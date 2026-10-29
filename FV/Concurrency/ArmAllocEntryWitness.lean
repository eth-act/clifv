import FV.Concurrency.ArmAllocEntry
import FV.Concurrency.RealizeWitnessLoad

/-!
# Layer 4b from the ABI entry on the compiled `atomic_load` (T2h, #311)

The CLIF `%ld(i64) -> i64 { v1 = atomic_load.i64 v0; return v1 }` as the pipeline compiles it
(`RealizeCompiled.WitnessL.RAL`), from its **ABI entry** `RAL.s0`:

* `entry_premises`: every premise of `ArmAllocThread.arm_alloc_refines_entry` (`R.Wf`,
  `MemScopeLS`, `AbiCall`, `BodyEntryW` with the body-entry world `w₀L`);
* `run_load_entry`: the precise run (reading the thread's own bytes, `OkPriv`) from the ABI entry
  through the prologue (its `stp` writing the fp/lr slot, `prun_fwd`), the 18 saves, the entry
  `args`, the spill of `x0` and back, and the `ldar`: one `acqR` event of 8 bytes at address 0,
  every earlier event private and plain; `Compiled` holds at the state after the prologue;
* `refines_load_entry`: `arm_alloc_refines_entry` on that run.

Checks by `native_decide` (witness only, through `RealizeWitnessLoad`).
-/

namespace Concurrency.RealizeCompiled.WitnessL

open Arm ArmFoot ArmThread Prog ClifThread ProgE2E Backend Backend.Proof Backend.Proof.Driver
  VCodeThread PrepThread AllocThread ThreadRefine ArmAllocThread E2E ArmInstFoot Code
  RealizeCompiled.Witness

theorem abiRL : AbiCall RAL.fb RAL.base 0x4000#64 RAL.s0 :=
  ArmAllocThread.Witness.abi_ofAt (by decide) (by decide) factsL.2.2.2.2.2.2.2.1 codeRL

theorem bodyRL : BodyEntryW RAL.F RAL.vc.EntryArg RAL.af RAL.s0 w₀L :=
  (E2E.Binary.bodyEntry_bodyOf RAL.af RAL.s0).w RAL.F entryArgRL

/-- `atomic_load`'s frame gets no stack probes (#581). -/
theorem probeF_RL : ProbeF RAL :=
  ProbeF.of_small (by have := factsL.2.2.2.2.2.2.1; omega)

/-- **Every premise of `arm_alloc_refines_entry`** for the compiled `atomic_load`. -/
theorem entry_premises : RAL.Wf ∧ MemScopeLS RAL ∧
    AbiCall RAL.fb RAL.base 0x4000#64 RAL.s0 ∧
    BodyEntryW RAL.F RAL.vc.EntryArg RAL.af RAL.s0 w₀L ∧ ProbeF RAL :=
  ⟨wfRL, memScopeLS_of_memScopeB (memScopeB_of_memScopeL (memScopeL_of_memScope scopeRL)), abiRL,
    bodyRL, probeF_RL⟩

/-- **The precise run from the ABI entry through the `ldar`** (module doc). -/
theorem run_load_entry : ∃ (lsP : List Lab) (e : Ev) (t' : ArmState × Mon),
    (∀ env p, Compiled env p RAL csL
      (iterN RAL.step (prologueLines RAL.af.saves RAL.af.frameSize RAL.af.isCaller).length RAL.s0)) ∧
    PRun Policy.arm RAL.step (OkPriv RAL) (RAL.s0, none) (lsP ++ [⟨[e], false⟩]) t' ∧
    e.k = .acqR ∧ e.n = 8 ∧ e.addr = 0 ∧
    (∀ l ∈ lsP, ∀ e' ∈ l.evs, PrivA RAL e'.addr.toNat ∧ (e'.k = .plainW ∨ e'.k = .plainR)) := by
  obtain ⟨hlat, hq, hA⟩ := q_init_lines wfRL abiRL bodyRL
  have hpe := prologue_evs wfRL abiRL probeF_RL hlat
  -- the prologue
  obtain ⟨t0, r0, ht0⟩ := prun_fwd wfRL hlat (fun i hi => (hpe i hi).2) none
  have hev0 : ∀ l ∈ (segEvs RAL.step (prologueLines RAL.af.saves RAL.af.frameSize RAL.af.isCaller).length RAL.s0).map
      (fun e => (⟨e, false⟩ : Lab)), ∀ e' ∈ l.evs, PrivA RAL e'.addr.toNat ∧ e'.k = .plainW := by
    intro l hl e' he'
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hl
    obtain ⟨i, hi, rfl⟩ := mem_segEvs hx
    obtain ⟨hF, hK⟩ := (hpe i hi).1 e' he'
    exact ⟨privA_addr.2 hF, hK⟩
  generalize iterN RAL.step (prologueLines RAL.af.saves RAL.af.frameSize RAL.af.isCaller).length RAL.s0 = s1 at hq hA ht0 ⊢
  obtain ⟨t0s, t0m⟩ := t0
  simp only at ht0
  subst ht0
  have hq0 := hq
  have hA0 := hA
  have e0 := checksRunL.1
  simp only [MConf.init] at hq0 hA0
  rw [show RAL.rf = rfL from rfl, e0] at hq0 hA0
  -- the saves
  obtain ⟨ls1, t1, r1, hq1, hA1, hev1⟩ := moves_fwdA wfRL (fun K => (K == .plainW) = true)
    savesL _ _ _ t0m hq0 hA0 (moves_kinds checksRunL.2.1) (by simp [savesL, Loc.isSave])
  -- the entry `args`
  obtain ⟨m', hst, hm'⟩ := args_step (spillL.map (fun p => RItem.move p.1 p.2) ++ rest2L) _ w₀L
  have hq2 := realizes_args wfRL hq1 hA1 vb0L argsL0.1 hst
  have hA2 := Backend.Proof.aInv_step wfRL hq1 hA1 hst
  -- the spill moves
  obtain ⟨ls2, t2, r2, hq3, -, hev2⟩ := moves_fwdA wfRL
    (fun K => (K == .plainW || K == .plainR) = true) spillL rest2L t1.1 m' t1.2 hq2 hA2
    (moves_kinds checksRunL.2.2.1) (by simp [spillL, Loc.isSave])
  -- the `ldar`
  obtain ⟨j, hj, hpc, hstr⟩ := q_head hq3 rfl head_ldarL
  obtain ⟨t3, ev, r3, -, hk, hn, ha⟩ := excl_step_fwd wfRL hj rfl hstr.prog hpc hstr.err
    (lb := 1) (p := 1) (q := 0) (.inr rfl) (by omega) (by omega) (fun _ => rfl) t2.2
  simp only [ite_true] at hk
  have hx0 : movesM spillL m' (.reg (.x 0)) = regVal w₀L (.x 0) := by
    simp [movesM, spillL, Backend.Proof.upd, hm']
  have hs3 := hstr.store (.reg (.x 0)) (fun r h => by cases h; rfl) trivial
  rw [hx0] at hs3
  have hz : regVal w₀L (.x 0) = 0 := by
    rw [E2E.regVal_bodyOf _ _ (by decide), shapeL.2.2.2.2.2.2.2]
  refine ⟨_ ++ (ls1 ++ ls2), ev, t3, fun env p => compiled_ofL hq hA env p,
    PRun.append (PRun.append r0 (PRun.append r1 r2)) r3, hk, hn, ha.trans (regVal_x0 hs3 hz), ?_⟩
  intro l hl e' he'
  rcases List.mem_append.mp hl with hl | hl
  · obtain ⟨hF, hK⟩ := hev0 l hl e' he'
    exact ⟨hF, .inl hK⟩
  rcases List.mem_append.mp hl with hl | hl
  · obtain ⟨hF, hK⟩ := hev1 l hl e' he'
    exact ⟨privA_addr.2 hF, .inl (by simpa using hK)⟩
  · obtain ⟨hF, hK⟩ := hev2 l hl e' he'
    exact ⟨privA_addr.2 hF, by simpa using hK⟩

/-- **Layer 4b from the ABI entry on the compiled `atomic_load`**: the run of `run_load_entry`
realizes, on a prefix, a run of the allocated code from its entry configuration. -/
theorem refines_load_entry : ∃ (lsP : List Lab) (e : Ev) (t' : ArmState × Mon),
    PRun Policy.arm RAL.step (OkPriv RAL) (RAL.s0, none) (lsP ++ [(⟨[e], false⟩ : Lab)]) t' ∧
    e.k = .acqR ∧ e.n = 8 ∧
    ∃ m₀ n trS cE ψ, n ≤ (lsP ++ [(⟨[e], false⟩ : Lab)]).length ∧
      MTRun RAL.vc RAL.rf RAL.sem ckeep (cEvs RAL.F RAL.ctx) (MConf.init RAL.rf m₀ w₀L) trS cE ∧
      Refines (· = ·) (PrivA RAL) (MonPair (evTr ((lsP ++ [(⟨[e], false⟩ : Lab)]).take n)))
        (PrepThread.conv trS) (PrepThread.conv (evTr ((lsP ++ [(⟨[e], false⟩ : Lab)]).take n))) ψ ∧
      (n = (lsP ++ [(⟨[e], false⟩ : Lab)]).length ∨ Done RAL cE) := by
  obtain ⟨lsP, e, t', -, hr, hk, hn, -, -⟩ := run_load_entry
  obtain ⟨hR, hsc, hent, hbe, hpf⟩ := entry_premises
  exact ⟨lsP, e, t', hr, hk, hn, arm_alloc_refines_entry hR hsc hent hpf hbe hr⟩

end Concurrency.RealizeCompiled.WitnessL
