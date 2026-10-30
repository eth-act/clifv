import FV.Concurrency.CallCalleeRet
import FV.Concurrency.LinkedMachine
import FV.E2E.LinkArm

/-!
# The return end of a callee's segment on the linked machine (#473, step (4))

At a callee's return end (`CallRetsEnd.RetEnd`: layer 4b at its `rets` item, the epilogue and
`ret` reaching the return address in `n` steps of the activation's machine), on the linked
machine with the return address in the caller's code:

* `stuck_outside`: from a state with the activation's program and the pc outside its code, every
  later step errs (`E2E.retStuck`);
* `retEnd_privP`: `RetEnd`'s `n` is `CallResume.rets_privP`'s (a state at the return address
  outside the callee's code is stuck, but both runs end without an error), so the epilogue's
  steps are private, at the callee's lines, the last one at a `ret` line;
* **`Link.ret_end`**: the return contract `RetC` of the activation at the state after its `ret`
  on the linked machine (the caller's program), and every precise run of the linked machine from
  the pause through the `n` steps is the single-core path but for the program switched by the
  `ret` (`LinkedMachine.Link.M_ret_x30`), its events the path's, private, no `relXW`.
-/

namespace Concurrency.LinkedMachine.Link

open Arm ArmFoot ArmThread ArmInstFoot Backend Backend.Proof ArmAllocThread E2E CallSeg
  CallRetsEnd

/-- **Outside its code, the activation's machine is stuck with an error.** -/
theorem stuck_outside {R : RL} (hR : R.Wf) {t : ArmState} (hprog : t.program = R.fb.program R.base)
    (hra : ∀ k < R.fb.words.size, Arm.r .PC t ≠ R.base + BitVec.ofNat 64 (4 * k)) (m : Nat) :
    Arm.r .ERR (iterN R.step (m + 1) t) ≠ .None := by
  have := retStuck (X := R.X) (H := R.H) (a := ⟨0, R.vc, R.vc, R.rf, R.af, R.fa, R.fb, R.base⟩)
    hR.layout hR.lm hprog hra m
  rwa [runX_eq] at this

/-- **`RetEnd` with the epilogue's steps** (module doc). -/
theorem retEnd_privP {R : RL} (hR : R.Wf) {ra : BitVec 64} (hent : AbiCall R.fb R.base ra R.s0)
    (hra : ∀ k < R.fb.words.size, ra ≠ R.base + BitVec.ofNat 64 (4 * k))
    {env : Clif.Env} {p : Clif.Program} {MR : MemRelT} {slots : List (Clif.SlotId × Nat)}
    {r₀ : Reg → CV} {x : ArmState} {s' : Clif.State} (hret : RetEnd R ra env p MR slots r₀ x s') :
    ∃ n, (∀ i < n, ((∀ e ∈ stepEvs (iterN R.step i x), R.F e.addr) ∧ NoStx (iterN R.step i x)) ∧
        (iterN R.step i x).program = R.fb.program R.base ∧ Arm.r .ERR (iterN R.step i x) = .None) ∧
      RetC R ra r₀ (iterN R.step n x) ∧ (iterN R.step n x).mem = x.mem ∧
      (iterN R.step n x).program = x.program ∧
      (∀ i, i + 1 < n → AtNonRet R (iterN R.step i x)) ∧ 0 < n ∧
      (∃ j t, R.fa.lines.toList[j]? = some (.ins .ret t) ∧
        Arm.r .PC (iterN R.step (n - 1) x) = R.pcOf j) ∧
      RetEnd R ra env p MR slots r₀ x s' := by
  have hret0 := hret
  obtain ⟨b, k, allocs, its, m, w, vb, us, ops, ρ, vals, cm, n1, hq, hvb, hi, -, -, -, -, -, hgood,
    hpc1, herr1, hsp1, hmem1, ⟨hprog1, hfp1⟩, hcs1, -⟩ := hret
  obtain ⟨mt, hqt⟩ := qa_q hq
  obtain ⟨n2, hpath, hpc2, herr2, -, hmem2, hprog2, -, hnr, hn0, hjret⟩ :=
    rets_privP hR hent hqt hvb hi
  have hxp : x.program = R.fb.program R.base := (q_stRel hqt).prog
  -- the two step counts agree
  have hn : n1 = n2 := by
    rcases Nat.lt_trichotomy n1 n2 with h | h | h
    · exfalso
      have hs := stuck_outside hR (t := iterN R.step n1 x) (by rw [hprog1, hxp])
        (by rw [hpc1]; exact hra) (n2 - n1 - 1)
      rw [← iterN_add, show n1 + (n2 - n1 - 1 + 1) = n2 by omega] at hs
      exact hs herr2
    · exact h
    · exfalso
      have hs := stuck_outside hR (t := iterN R.step n2 x) (by rw [hprog2, hxp])
        (by rw [hpc2]; exact hra) (n1 - n2 - 1)
      rw [← iterN_add, show n2 + (n1 - n2 - 1 + 1) = n1 by omega] at hs
      exact hs herr1
  subst hn
  exact ⟨n1, fun i hi => ⟨(hpath i hi).1, (hpath i hi).2.1, (hgood i hi).err⟩,
    ⟨hpc1, herr1, hsp1, fun a ha => by rw [hmem1]; exact gkeep_of_q hqt a ha, hfp1, hcs1⟩, hmem1,
    hprog1, hnr, hn0, hjret, hret0⟩

variable {L : Link} {FB : LFn} {s0 : ArmState} {K : Nat} {G : BitVec 64 → Prop}

local notation "RB" => Link.act L FB s0 K G

/-- **The return end on the linked machine** (module doc). -/
theorem ret_end (hL : L.Ok) {nB : String} (hB : (nB, FB) ∈ L.fns)
    (hRB : (L.act FB s0 K G).Wf) {ra : BitVec 64}
    (hent : AbiCall FB.fb FB.base ra s0)
    (hra : ∀ k < FB.fb.words.size, ra ≠ FB.base + BitVec.ofNat 64 (4 * k))
    {nA : String} {FA : LFn} (hA : (nA, FA) ∈ L.fns) (hrA : FA.InRange ra)
    {env : Clif.Env} {p : Clif.Program} {MR : MemRelT} {slots : List (Clif.SlotId × Nat)}
    {r₀ : Reg → CV} {x : ArmState} {s' : Clif.State}
    (hret : RetEnd (L.act FB s0 K G) ra env p MR slots r₀ x s') :
    ∃ n, 0 < n ∧ RetC (L.act FB s0 K G) ra r₀ (iterN (L.act FB s0 K G).step n x) ∧
      (iterN (L.act FB s0 K G).step n x).mem = x.mem ∧
      ∀ {mon : Mon} {ls : List Lab} {t' : ArmState × Mon},
        PRun Policy.arm L.M (OkPriv (L.act FB s0 K G)) (x, mon) ls t' →
        (ls.length < n → t'.1 = iterN (L.act FB s0 K G).step ls.length x ∧
          evTr ls = segEvs (L.act FB s0 K G).step ls.length x ∧
          PrivW (PrivA (L.act FB s0 K G)) (evTr ls) ∧ ∀ l ∈ ls, ∀ e ∈ l.evs, e.k ≠ .relXW) ∧
        (n ≤ ls.length → ∃ v, PRun Policy.arm L.M (OkPriv (L.act FB s0 K G)) (x, mon) (ls.take n) v ∧
          v.1 = set_program (iterN (L.act FB s0 K G).step n x) (FA.fb.program FA.base) ∧
          evTr (ls.take n) = segEvs (L.act FB s0 K G).step n x ∧
          PrivW (PrivA (L.act FB s0 K G)) (evTr (ls.take n)) ∧
          ∀ l ∈ ls.take n, ∀ e ∈ l.evs, e.k ≠ .relXW) := by
  obtain ⟨n, hpath, hRC, hmem, -, hnr, hn0, ⟨j, t, hj, hpcj⟩, -⟩ := retEnd_privP hRB hent hra hret
  have hag : ∀ i, i + 1 < n → L.M (iterN (RB).step i x) = (RB).step (iterN (RB).step i x) :=
    fun i hi => agreesAt_M hL hB s0 K G _ (hpath i (by omega)).2.1 (hnr i hi)
  refine ⟨n, hn0, hRC, hmem, fun {mon ls t'} hr => ⟨fun hlt => ?_, fun hle => ?_⟩⟩
  · obtain ⟨h1, hev, hk⟩ := prun_privF hr fun i hi =>
      ⟨(hpath i (by omega)).1.1, (hpath i (by omega)).1.2, hag i (by omega)⟩
    refine ⟨h1, hev, ?_, fun l hl => (hk l hl).2⟩
    rw [hev]; exact privW_segEvs (fun i hi => (hpath i (by omega)).1.1)
      fun i hi => stepEvs_noRelXW (hpath i (by omega)).1.2
  · -- the epilogue before the `ret`, then the `ret`
    obtain ⟨v1, hv1, hrest⟩ := CallCompose.take_prun hr (n - 1)
    have hl1 : (ls.take (n - 1)).length = n - 1 := by simp; omega
    obtain ⟨hv1e, hev1, hk1⟩ := prun_privF hv1 fun i hi =>
      ⟨(hpath i (by omega)).1.1, (hpath i (by omega)).1.2, hag i (by omega)⟩
    rw [hl1] at hv1e hev1
    obtain ⟨l, rest, hdrop⟩ : ∃ l rest, ls.drop (n - 1) = l :: rest := by
      cases h : ls.drop (n - 1) with
      | nil => simp at h; omega
      | cons l rest => exact ⟨l, rest, rfl⟩
    rw [hdrop] at hrest
    obtain ⟨z, mz⟩ := v1
    simp only at hv1e
    subst hv1e
    cases hrest with
    | cons hs hp ho _ =>
      rename_i t1 _
      have hz := hpath (n - 1) (by omega)
      obtain ⟨ht1, hlev, -, hlk⟩ := tstep_priv1 hs hp ho hz.1.1 hz.1.2
      -- the `ret` on the linked machine
      have hisRet : FB.IsRet (iterN (RB).step (n - 1) x) := ⟨j, t, hj, hpcj⟩
      have hstF := stepF_ret hL hB hz.2.1 hisRet hz.2.2
      have hn1 : iterN (RB).step n x = (RB).step (iterN (RB).step (n - 1) x) := by
        rw [show n = n - 1 + 1 by omega, iterN_add]; rfl
      have hstep : (RB).step (iterN (RB).step (n - 1) x) =
          w .PC (xreg 30 (iterN (RB).step (n - 1) x)) (iterN (RB).step (n - 1) x) := hstF
      have hx30 : xreg 30 (iterN (RB).step (n - 1) x) = ra := by
        have := hRC.1
        rw [hn1, hstep, r_of_w_same] at this
        exact this
      have hM := M_ret_x30 hL hB hA hz.2.1 hisRet hz.2.2 (by rw [hx30]; exact hrA)
      have htake : ls.take n = ls.take (n - 1) ++ [l] := by
        rw [show n = n - 1 + 1 by omega, List.take_add, hdrop]; simp
      refine ⟨t1, ?_, ?_, ?_, ?_, ?_⟩
      · rw [htake]; exact hv1.append (.cons hs hp ho .nil)
      · rw [ht1, hM, hn1, hstep]
      · rw [htake, evTr_append, hev1, show n = n - 1 + 1 by omega, segEvs_add]
        simp [evTr, hlev, segEvs, iterN]
      · rw [htake, evTr_append, hev1]
        intro q y hy hW
        rcases Nat.lt_or_ge q.1 (segEvs (RB).step (n - 1) x).length with hq | hq
        · rw [evAt_append_lt _ _ hq] at hy
          exact privW_segEvs (fun i hi => (hpath i (by omega)).1.1)
            (fun i hi => stepEvs_noRelXW (hpath i (by omega)).1.2) q y hy hW
        · rw [evAt_append_ge _ _ hq] at hy
          obtain ⟨e, he, hye⟩ := mem_of_evAt hy
          simp only [evTr, List.map_cons, List.map_nil, List.mem_singleton] at he
          subst he
          rw [hlev] at hye
          exact ⟨privA_addr.2 (hz.1.1 y hye), hlk y (by rw [hlev]; exact hye)⟩
      · rw [htake]
        intro l' hl'
        rcases List.mem_append.mp hl' with hl' | hl'
        · exact (hk1 l' hl').2
        · simp only [List.mem_singleton] at hl'; subst hl'; exact hlk

end Concurrency.LinkedMachine.Link
