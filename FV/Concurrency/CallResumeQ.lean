import FV.E2E.RegLevelCall
import FV.E2E.RegLevelNext
import FV.E2E.RegLevelGoto
import FV.E2E.RegLevelOp
import FV.E2E.RegLevelRelax
import FV.Concurrency.AllocThread
import FV.Concurrency.ArmAllocThread

/-!
# `Q` after a call's return (#473)

* **`resumeQW`**: layer 4b's relation `Q` at the item after a call, from `Q` at the call and the
  caller's state as the callee returns (the pc after the `bl`/`blr`, no error, `sp`, program and
  the activation's frame, code and kept addresses `R.FK` as at the call), for any store holding
  the state's live locations and any world agreeing with it outside the private addresses;
* `resumeQ`: the store and the world the state holds (`R.F` for `R.FK`).
-/

namespace Concurrency.CallSeg

open Arm ArmFoot ArmThread Prog ClifThread ProgE2E Backend Backend.Proof VCodeThread PrepThread
  AllocThread ThreadRefine ArmAllocThread E2E ArmInstFoot

/-- **`Q` at the item after a call, when the callee returned** (module doc): from `Q` at the call
item and a state `y` at the address after the call's `bl`/`blr`, without error, with the call's
`sp` and frame pointer x29 (`StRel.fp`: Cranelift's frame keeps x29 at entry `sp − 16`, the
callees restore it), its program, and the activation's addresses (`R.F`: its frame, its code, the
kept addresses) as at the call (`R.FK`: its frame, its code, the kept addresses); any store
holding `y`'s live locations, any world agreeing with `y` outside the private addresses
(`SameWorld R.F`). -/
theorem resumeQW {R : RL} (hR : R.Wf) {s y : ArmState} {b k : Nat} {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : ArmState}
    (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩)) {vb : VBlock} {info : CallInfo}
    (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some (.call info))
    (hpc : Arm.r .PC y = Arm.r .PC s + 4#64) (herr : Arm.r .ERR y = .None)
    (hsp : spOf y = spOf s) (hmem : ∀ a, R.FK a → y.mem a = s.mem a)
    (hprog : y.program = s.program) (hfp : xreg 29 y = xreg 29 s) {m' : Loc → CV} {w' : ArmState}
    (hst' : ∀ l, ValidLoc l → Live R.rf l → m' l = locVal R.fr y l)
    (hw' : SameWorld R.F y w') :
    Q R y (.run ⟨b, its, m', w'⟩) := by
  obtain ⟨j0, items, pre, regs, i', c1, c2, ls1, ls2, ps1, psm, ps2, T, cc, wh, ops, -, hit, hsplit,
    hasg, hc1', -, -, hchk', hc2, h1, h2, htr, hdrop, hpc0, hst⟩ := q_op hq hvb hi
  obtain ⟨ic, rfl⟩ := assign_call_form hasg
  obtain rfl : c1 = [.inst (.call ic)] := by
    rcases hc1' with ⟨h, -, -⟩ | ⟨_, h, -⟩ | ⟨_, h, -⟩
    · exact h
    · cases h
    · cases h
  obtain ⟨x, hl, hx⟩ : ∃ x, (∀ ps, (MInst.call ic).lines R.ctx ps = .ok ([.ins x none], ps)) ∧
      ((∃ n, x = .bl n) ∨ (∃ r, x = .blr r)) := by
    cases hd : ic.dest with
    | sym n => exact ⟨.bl n, fun ps => by simp [MInst.lines, hd, pure, Except.pure], .inl ⟨n, rfl⟩⟩
    | reg r => exact ⟨.blr r, fun ps => by simp [MInst.lines, hd, pure, Except.pure], .inr ⟨r, rfl⟩⟩
  have h1' := codeLinesE_single h1
  rw [hl ps1] at h1'
  simp only [Except.ok.injEq, Prod.mk.injEq] at h1'
  obtain ⟨rfl, -⟩ := h1'
  have hft : ftList ([Line.ins x none] ++ (ls2 ++ nxtOf R.af b)) =
      [Line.ins x none] ++ ftList (ls2 ++ nxtOf R.af b) := by
    rw [List.singleton_append, ftList_cons, ftStep_call hx]; rfl
  have hrl : relaxLines R.far [Line.ins x none] = [Line.ins x none] := by
    rw [relaxLines_cons, relaxLine_of_none (by rcases hx with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl)]; rfl
  have hj : R.L[j0]? = some (.ins x none) := by
    have hd := hdrop
    rw [hft, relaxLines_append, hrl] at hd
    exact drop_get (Z := []) (by rw [hd]; rfl)
  refine q_next hvb hit hsplit hchk' hc2 h2 htr hdrop hft ?_ ?_
  · rw [hrl, List.length_singleton, pcOf_succ hj, hpc, hpc0]; rfl
  · refine ⟨hst', hw', herr, hprog.trans hst.prog, hsp.trans hst.sp,
      align_of_sp hsp hst.align, fun hframe => ?_, ?_, fun a ha => ?_,
      fun hf => hfp.trans (hst.fp hf)⟩
    · rw [← hst.fplr hframe]
      exact read_mem_bytes_congr _ _ fun k hk => hmem _ (fplr_inF hR hframe k hk)
    · exact code_keep hR.prog0 hst.code fun a ha => hmem a (.inl (.inr (.inr ha)))
    · rw [hmem a (.inr ha)]; exact hst.gkeep a ha

/-- **`Q` at the item after a call, when the callee returned** (`resumeQW` with the store and
the world `y` holds). -/
theorem resumeQ {R : RL} (hR : R.Wf) {s y : ArmState} {b k : Nat} {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : ArmState}
    (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩)) {vb : VBlock} {info : CallInfo}
    (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some (.call info))
    (hpc : Arm.r .PC y = Arm.r .PC s + 4#64) (herr : Arm.r .ERR y = .None)
    (hsp : spOf y = spOf s) (hmem : ∀ a, R.F a → y.mem a = s.mem a)
    (hprog : y.program = s.program) (hfp : xreg 29 y = xreg 29 s) :
    Q R y (.run ⟨b, its, locVal R.fr y, y⟩) :=
  resumeQW hR hq hvb hi hpc herr hsp (fun a ha => hmem a (RL.FK_F ha)) hprog hfp
    (fun _ _ _ => rfl) (SameWorld.refl _ _)

end Concurrency.CallSeg
