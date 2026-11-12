import FV.E2E.RegLevelPush

/-!
# The prologue's result does not depend on the entry flags in the loop form (#581)

With Cranelift's stack-probe loop (`probeLoopBody`, a probed stack of 16 KiB or more) the
prologue sets the flags (the loop's `cmn x16, x17`) before anything reads them, and nothing in
the prologue reads the entry's flags. So two entries that differ at most in their flags
(`FlagTwin`) reach the same state after the prologue (`ProRun.flags_irrel`):

* the frame setup (`fplrLines`) and the loop's constants (`probeHead`) write the same values in
  both runs (`exec_stp_fplr`, `exec_mov_fp_sp`, `steps_loadConst64` give the states explicitly),
  so the states before the loop are again twins;
* `probeLoop_ok` gives the state after the loop completely (the flags are `loopFlag total`):
  the two states after the loop are equal (`Arm.state_eq_iff_components_eq`);
* the pushes and the `sp` adjustment run from the same state (`StepsOk.det`).

This is what the two-run theorems whose conclusions speak only of the states after the prologue
use to do without a premise on the entries' flags (`E2E.stEqOutX_prologueZ_entry`).

* `FlagTwin`, `FlagTwin.w`, `FlagTwin.write_mem`, `FlagTwin.eq_of_flags`;
* `flagsOf`, `flagsOf_flag`, `flagsOf_twin`;
* `ProbeRun.flags_irrel`, **`ProRun.flags_irrel`**;
* `proRun_flags_irrel_witness` (non-vacuity: a 16 KiB frame, two entries differing in `N`).
-/

open Backend E2E

namespace Backend.Proof

/-- Two states that differ at most in their flags. -/
def FlagTwin (s t : Arm.ArmState) : Prop :=
  (∀ f, (∀ fl, f ≠ .FLAG fl) → Arm.r f s = Arm.r f t) ∧ s.program = t.program ∧ s.mem = t.mem

theorem FlagTwin.refl (s : Arm.ArmState) : FlagTwin s s := ⟨fun _ _ => rfl, rfl, rfl⟩

theorem FlagTwin.symm {s t : Arm.ArmState} (h : FlagTwin s t) : FlagTwin t s :=
  ⟨fun f hf => (h.1 f hf).symm, h.2.1.symm, h.2.2.symm⟩

/-- Writing the same value to the same field keeps twins. -/
theorem FlagTwin.w {s t : Arm.ArmState} (h : FlagTwin s t) (g : Arm.StateField)
    (v : Arm.state_value g) : FlagTwin (Arm.w g v s) (Arm.w g v t) := by
  refine ⟨fun f hf => ?_, by rw [Arm.w_program, Arm.w_program]; exact h.2.1,
    by rw [Arm.ArmState.mem_w_eq_mem, Arm.ArmState.mem_w_eq_mem]; exact h.2.2⟩
  by_cases e : f = g
  · subst e; rw [Arm.r_of_w_same, Arm.r_of_w_same]
  · rw [Arm.r_of_w_different e, Arm.r_of_w_different e]; exact h.1 f hf

/-- Writing the same bytes at the same address keeps twins. -/
theorem FlagTwin.write_mem {s t : Arm.ArmState} (h : FlagTwin s t) (n : Nat) (a : BitVec 64)
    (v : BitVec (n * 8)) :
    FlagTwin (Arm.write_mem_bytes n a v s) (Arm.write_mem_bytes n a v t) :=
  ⟨fun f hf => by rw [Arm.r_of_write_mem_bytes, Arm.r_of_write_mem_bytes]; exact h.1 f hf,
    by rw [Arm.write_mem_bytes_program, Arm.write_mem_bytes_program]; exact h.2.1,
    Arm.mem_write_mem_bytes_of_mem_eq h.2.2 n a v⟩

/-- Twins with the same flags are equal. -/
theorem FlagTwin.eq_of_flags {s t : Arm.ArmState} (h : FlagTwin s t)
    (hfl : ∀ fl, Arm.r (.FLAG fl) s = Arm.r (.FLAG fl) t) : s = t := by
  refine Arm.state_eq_iff_components_eq.2 ⟨fun f => ?_, h.2.1, fun n a => ?_⟩
  · by_cases hf : ∃ fl, f = .FLAG fl
    · obtain ⟨fl, rfl⟩ := hf; exact hfl fl
    · exact h.1 f fun fl e => hf ⟨fl, e⟩
  · rw [Arm.Memory.State.read_mem_bytes_eq_mem_read_bytes,
      Arm.Memory.State.read_mem_bytes_eq_mem_read_bytes, h.2.2]

/-- `t` with the flags of `s`. -/
def flagsOf (s t : Arm.ArmState) : Arm.ArmState :=
  Arm.w (.FLAG .N) (Arm.r (.FLAG .N) s) (Arm.w (.FLAG .Z) (Arm.r (.FLAG .Z) s)
    (Arm.w (.FLAG .C) (Arm.r (.FLAG .C) s) (Arm.w (.FLAG .V) (Arm.r (.FLAG .V) s) t)))

theorem flagsOf_flag (s t : Arm.ArmState) (fl : Arm.PFlag) :
    Arm.r (.FLAG fl) (flagsOf s t) = Arm.r (.FLAG fl) s := by
  cases fl <;> simp [flagsOf, Arm.r_of_w_same, Arm.r_of_w_different]

theorem flagsOf_twin (s t : Arm.ArmState) : FlagTwin (flagsOf s t) t :=
  ⟨fun f hf => by
      simp only [flagsOf]
      rw [Arm.r_of_w_different (hf _), Arm.r_of_w_different (hf _), Arm.r_of_w_different (hf _),
        Arm.r_of_w_different (hf _)],
    by simp only [flagsOf, Arm.w_program], by simp only [flagsOf, Arm.ArmState.mem_w_eq_mem]⟩

/-- **The stack probes' result does not depend on the entry flags in the loop form**: the probe
runs of twins with an aligned `sp` end in the same state. -/
theorem ProbeRun.flags_irrel {env : Env} {total : Nat} (hl : probeLoop total = true)
    {s t s' t' : Arm.ArmState} (hal : (spOf s).toNat % 16 = 0) (htw : FlagTwin s t)
    (h1 : ProbeRun env total s s') (h2 : ProbeRun env total t t') : s' = t' := by
  obtain ⟨hlo, hhi, hcnt⟩ := probeLoop_facts hl
  have hH : probeHead total = loadConst64 (.x 16) 0 ++ loadConst64 (.x 17) total := by
    simp [probeHead, hl]
  have hI : loopIters total = probeCount total := by simp [loopIters, hl]
  -- the state after the loop's constants, and after the loop, from any start
  have key : ∀ u u', (spOf u).toNat % 16 = 0 → ProbeRun env total u u' →
      ∃ u1, u1 = pcx (pcx u 16 (Arm.r .PC u + BitVec.ofNat 64 (4 * (loadConst64 (.x 16) 0).length))
            (BitVec.ofNat 64 0)) 17
          (Arm.r .PC (pcx u 16 (Arm.r .PC u + BitVec.ofNat 64 (4 * (loadConst64 (.x 16) 0).length))
            (BitVec.ofNat 64 0)) + BitVec.ofNat 64 (4 * (loadConst64 (.x 17) total).length))
          (BitVec.ofNat 64 total) ∧
        u'.program = u1.program ∧
        xreg 16 u' = loopOff (0 + probeCount total) ∧
        (∀ fl, Arm.r (.FLAG fl) u' = loopFlag total fl) ∧
        Arm.r .PC u' = Arm.r .PC u1 + 16#64 ∧
        (∀ f, f ≠ .PC → f ≠ .GPR 16#5 → (∀ fl, f ≠ .FLAG fl) → Arm.r f u' = Arm.r f u1) ∧
        (∀ a, u'.mem a = if probeHitB (probeCount total)
          (spOf u1 - BitVec.ofNat 64 (4096 * 0)) a then 0#8 else u1.mem a) := by
    intro u u' halu hrun
    obtain ⟨v1, hHv, -, hLv, -⟩ := hrun
    have e1 := steps_loadConst64 env (n := 16) (by omega) 0 u
    generalize hs1 : pcx u 16 (Arm.r .PC u + BitVec.ofNat 64 (4 * (loadConst64 (.x 16) 0).length))
      (BitVec.ofNat 64 0) = u1 at e1
    have e2 := steps_loadConst64 { env with pc := env.pc + 4 * (loadConst64 (.x 16) 0).length }
      (n := 17) (by omega) total u1
    generalize hs2 : pcx u1 17 (Arm.r .PC u1 + BitVec.ofNat 64 (4 * (loadConst64 (.x 17) total).length))
      (BitVec.ofNat 64 total) = u2 at e2
    rw [hH] at hHv
    obtain rfl := StepsOk.det hHv (StepsOk.append e1 e2)
    have hf2 : ∀ f, f ≠ .PC → f ≠ .GPR 16#5 → f ≠ .GPR 17#5 → Arm.r f v1 = Arm.r f u := by
      intro f g1 g2 g3
      rw [← hs2, ← hs1]
      simp only [pcx]
      rw [Arm.r_of_w_different g1, Arm.r_of_w_different g3, Arm.r_of_w_different g1,
        Arm.r_of_w_different g2]
    have hsp2 : spOf v1 = spOf u := hf2 _ (by simp) (by simp) (by simp)
    have h16 : xreg 16 v1 = loopOff 0 := by
      show Arm.r _ v1 = _
      rw [← hs2, ← hs1]
      simp [pcx, Arm.r_of_w_different, Arm.r_of_w_same]
    have h17 : xreg 17 v1 = BitVec.ofNat 64 total := by
      show Arm.r _ v1 = _
      rw [← hs2]; simp [pcx, Arm.r_of_w_same]
    obtain ⟨w, hL, -, hx16, -, hfl, hpc, hf, hm⟩ :=
      probeLoop_ok { env with pc := env.pc + 4 * (probeHead total).length } hlo hhi (probeCount total) 0 v1
        (by omega) (by omega) (by rw [hsp2]; exact halu) h16 h17
    rw [hsp2] at hL
    rw [hI] at hLv
    obtain rfl := LoopRuns.det hLv hL
    exact ⟨v1, rfl, hL.err.2, hx16, hfl, hpc, hf, hm⟩
  obtain ⟨s1, hs1, hp, hx16, hfl, hpc, hf, hm⟩ := key s s' hal h1
  obtain ⟨t1, ht1, hp', hx16', hfl', hpc', hf', hm'⟩ := key t t'
    (by rw [show spOf t = spOf s from (htw.1 _ (by simp)).symm]; exact hal) h2
  -- the states before the loop are twins
  have htw1 : FlagTwin s1 t1 := by
    rw [hs1, ht1]
    simp only [pcx]
    have hpc0 : Arm.r .PC s = Arm.r .PC t := htw.1 _ (by simp)
    rw [hpc0]
    have hA := (htw.w (.GPR (BitVec.ofNat 5 16)) (BitVec.ofNat 64 0)).w .PC
      (Arm.r .PC t + BitVec.ofNat 64 (4 * (loadConst64 (.x 16) 0).length))
    have hpc1 := hA.1 .PC (by simp)
    rw [hpc1]
    exact (hA.w (.GPR (BitVec.ofNat 5 17)) (BitVec.ofNat 64 total)).w .PC _
  refine Arm.state_eq_iff_components_eq.2 ⟨fun f => ?_, ?_, fun n a => ?_⟩
  · by_cases g1 : f = .PC
    · subst g1; rw [hpc, hpc', htw1.1 _ (by simp)]
    · by_cases g2 : f = .GPR 16#5
      · subst g2; exact hx16.trans hx16'.symm
      · by_cases g3 : ∃ fl, f = .FLAG fl
        · obtain ⟨fl, rfl⟩ := g3; rw [hfl, hfl']
        · have g3' : ∀ fl, f ≠ .FLAG fl := fun fl e => g3 ⟨fl, e⟩
          rw [hf f g1 g2 g3', hf' f g1 g2 g3', htw1.1 f g3']
  · rw [hp, hp', htw1.2.1]
  · rw [Arm.Memory.State.read_mem_bytes_eq_mem_read_bytes,
      Arm.Memory.State.read_mem_bytes_eq_mem_read_bytes]
    congr 1
    funext b
    rw [hm b, hm' b, htw1.2.2, show spOf s1 = spOf t1 from htw1.1 _ (by simp)]

/-- **The prologue's result does not depend on the entry flags in the loop form** (module doc):
the prologue runs (`ProRun`) of two entries with an aligned `sp` that differ at most in their
flags end in the same state, when the stack probes are Cranelift's loop. -/
theorem ProRun.flags_irrel {env : Env} {saves : List Reg} {size : Nat} {calls : Bool}
    (hl : probeLoop (probeTotal size calls) = true) {s t s' t' : Arm.ArmState}
    (hal : (spOf s).toNat % 16 = 0) (htw : FlagTwin s t)
    (h1 : ProRun env saves size calls s s') (h2 : ProRun env saves size calls t t') : s' = t' := by
  obtain ⟨s2, sP, hA, hsp2, hP, hT⟩ := h1
  obtain ⟨t2, tP, hA', -, hP', hT'⟩ := h2
  -- the frame setup, explicitly, from any aligned start
  have key : ∀ u u2, (spOf u).toNat % 16 = 0 → StepsOk env fplrLines u u2 →
      u2 = Arm.w (.GPR 29#5) (spOf u - 16#64) (Arm.w .PC (Arm.r .PC u + 4#64 + 4#64)
        (Arm.w .PC (Arm.r .PC u + 4#64) (Arm.w (.GPR 31#5) (spOf u - 16#64)
          (Arm.write_mem_bytes 16 (spOf u - 16#64) (xreg 30 u ++ xreg 29 u) u)))) := by
    intro u u2 halu hsteps
    obtain ⟨a1, ha1, he1⟩ := exec_stp_fplr env u (checkSP_of halu)
    obtain ⟨a2, ha2, he2⟩ := exec_mov_fp_sp { env with pc := env.pc + 4 } (Arm.exec_inst a1 u)
    have hst : StepsOk env fplrLines u (Arm.exec_inst a2 (Arm.exec_inst a1 u)) := by
      show StepsOk env [.ins _ none, .ins _ none] u _
      refine steps_cons ha1 (by rw [he1]; simp [Arm.r_of_w_same])
        (by rw [he1]; simp [Arm.r_of_w_different, Arm.r_of_write_mem_bytes])
        (by rw [he1]; simp [Arm.w_program, Arm.write_mem_bytes_program]) ?_
      exact steps_one ha2 (by rw [he2]; simp [Arm.r_of_w_same, Arm.r_of_w_different])
        (by rw [he2]; simp [Arm.r_of_w_different]) (by rw [he2]; simp [Arm.w_program])
    rw [StepsOk.det hsteps hst, he2, he1]
    simp [spOf, Arm.r_of_w_same, Arm.r_of_w_different]
  have halt : (spOf t).toNat % 16 = 0 := by
    rw [show spOf t = spOf s from (htw.1 _ (by simp)).symm]; exact hal
  have htw2 : FlagTwin s2 t2 := by
    rw [key s s2 hal hA, key t t2 halt hA']
    rw [show spOf s = spOf t from htw.1 _ (by simp),
      show Arm.r .PC s = Arm.r .PC t from htw.1 _ (by simp),
      show xreg 30 s = xreg 30 t from htw.1 _ (by simp),
      show xreg 29 s = xreg 29 t from htw.1 _ (by simp)]
    exact ((((htw.write_mem 16 _ _).w _ _).w _ _).w _ _).w _ _
  have hal2 : (spOf s2).toNat % 16 = 0 := by
    rw [hsp2]; exact aligned_sub hal (by decide) (by decide)
  obtain rfl := ProbeRun.flags_irrel hl hal2 htw2 hP hP'
  exact StepsOk.det hT hT'

/-! ## Non-vacuity -/

/-- An entry with an aligned `sp` and the `N` flag clear. -/
def flagWitS : Arm.ArmState := Arm.w (.FLAG .N) 0#1 (Arm.w (.GPR 31#5) 0#64 Arm.ArmState.default)

/-- `flagWitS` with the `N` flag set. -/
def flagWitT : Arm.ArmState := Arm.w (.FLAG .N) 1#1 flagWitS

/-- **`ProRun.flags_irrel` is not vacuous**: a 16 KiB frame has the probe loop, the two entries
`flagWitS` and `flagWitT` are different twins, both prologue runs exist (`prologue_ok`), and they
end in the same state. -/
theorem proRun_flags_irrel_witness (env : Env) :
    probeLoop (probeTotal 16384 false) = true ∧ FlagTwin flagWitS flagWitT ∧ flagWitS ≠ flagWitT ∧
      ∃ s' t', ProRun env [] 16384 false flagWitS s' ∧ ProRun env [] 16384 false flagWitT t' ∧
        s' = t' := by
  have hal : (spOf flagWitS).toNat % 16 = 0 := by
    simp [spOf, flagWitS, Arm.r_of_w_same, Arm.r_of_w_different]
  have htw : FlagTwin flagWitS flagWitT :=
    ⟨fun f hf => by rw [flagWitT, Arm.r_of_w_different (hf _)],
      by rw [flagWitT, Arm.w_program], by rw [flagWitT, Arm.ArmState.mem_w_eq_mem]⟩
  have hal' : (spOf flagWitT).toNat % 16 = 0 := by
    rw [show spOf flagWitT = spOf flagWitS from (htw.1 _ (by simp)).symm]; exact hal
  have hl : probeLoop (probeTotal 16384 false) = true := by decide
  have hsv : SavesOk [] := ⟨fun _ h => (by cases h), List.nodup_nil⟩
  obtain ⟨s', h1, -⟩ := prologue_ok (calls := false) env (size := 16384) (by decide) hsv (by decide)
    flagWitS hal
  obtain ⟨t', h2, -⟩ := prologue_ok (calls := false) env (size := 16384) (by decide) hsv (by decide)
    flagWitT hal'
  refine ⟨hl, htw, fun e => ?_, s', t', h1, h2, ProRun.flags_irrel hl hal htw h1 h2⟩
  have := congrArg (Arm.r (.FLAG .N)) e
  simp [flagWitS, flagWitT, Arm.r_of_w_same] at this

end Backend.Proof
