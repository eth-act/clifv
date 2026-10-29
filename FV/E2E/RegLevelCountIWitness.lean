module

public import FV.E2E.RegLevelCountI
public import FV.E2E.RegLevelCorrectU
public import FV.E2E.LinkArmProphThmWitness

@[expose] public section

/-!
# Witnesses for the counter against the machine's calls (`FV/E2E/RegLevelCountI.lean`)

* `countIn`/`stepC`: counting every state of a run, and the one-line `bl f` machine of
  `LinkArmProphThmWitness` (whose `callsBefore` is `countIn` of its call states);
* `opCalls`: `1` at the `call f` of `RegLevelCorrectUWitness`'s function, `0` at a move; a counted
  move at counter `5` keeps the counter (`MStep.counted_ctr`); `MNext.world`;
* `RealizesC`: the identity machine counting every state realises every semantics with
  `opCalls` states per segment (`realizesC_any`); `RealizesC.toRealizes`; `RealizesC.counted` on
  it: the counted semantics is realised with the counter equal to the count.
-/

namespace Backend.Proof.RegLevelCountIWitness

open Backend Backend.Proof E2E

theorem ind_true : ind True = 1 := by simp [ind]

theorem countIn_true {S : Type} (step : S → S) (s : S) : ∀ n, countIn (fun _ => True) step s n = n
  | 0 => rfl
  | n + 1 => by
    show countIn (fun _ => True) step s n + ind True = n + 1
    rw [countIn_true step s n, ind_true]

theorem countIn_succ_id : countIn (fun _ => True) (id : Unit → Unit) () 3 =
    ind True + countIn (fun _ => True) id () 2 :=
  countIn_succ' _ _ 2 ()

theorem iterN_stepC_id : iterN (stepC (fun _ => True) (id : Unit → Unit)) 4 ((), 7) = ((), 11) := by
  rw [iterN_stepC, countIn_true]

theorem callsBefore_u0_countIn :
    callsBefore id LinkArmProphThmWitness.faC 0x1000#64 LinkArmProphThmWitness.u0 4 =
      countIn (fun u => CallPc LinkArmProphThmWitness.faC 0x1000#64 (Arm.r .PC u)) id
        LinkArmProphThmWitness.u0 4 :=
  callsBefore_eq_countIn _ _ _ _ 4

/-- The `call f` (instruction `1` of block `0`) of `RegLevelCorrectUWitness.vc` counts one call. -/
theorem opCalls_call (m : Loc → CV) (w : Arm.ArmState × Nat) :
    opCalls RegLevelCorrectUWitness.vc (.run ⟨0, [.op 1 #[]], m, w⟩ : MConf CV (Arm.ArmState × Nat)) = 1 := by
  rfl

theorem opCalls_move (vc : VCode) (src dst : Loc) (its : List RItem) (m : Loc → CV) (w : Arm.ArmState) :
    opCalls vc (.run ⟨0, .move src dst :: its, m, w⟩ : MConf CV Arm.ArmState) = 0 := rfl

theorem opCalls_mapW_call (m : Loc → CV) (w : Arm.ArmState) :
    opCalls RegLevelCorrectUWitness.vc
      ((MConf.run ⟨0, [.op 1 #[]], m, (w, 2)⟩ : MConf CV (Arm.ArmState × Nat)).mapW Prod.fst) = 1 := by
  rw [opCalls_mapW]; exact opCalls_call m (w, 2)

theorem mnext_world (vc : VCode) (rf : RFunc) (m : Loc → CV) (w : Arm.ArmState) :
    (MConf.run ⟨0, [], m, w⟩ : MConf CV Arm.ArmState).world = w :=
  MNext.world (vc := vc) (rf := rf) (b := 0) (k := 0) (n := 2) (i := .rets [])
    (uses := []) (its := []) (MNext.next (by omega))

/-- A counted move at counter `5` keeps the counter. -/
theorem move_ctr (vc : VCode) (rf : RFunc) (sem : Nat → ISem CV Arm.ArmState) (src dst : Loc)
    (its : List RItem) (m : Loc → CV) (w : Arm.ArmState) :
    (MConf.run ⟨0, its, upd m dst (m src), (w, 5)⟩ : MConf CV (Arm.ArmState × Nat)).world.2 =
      (MConf.run ⟨0, .move src dst :: its, m, (w, 5)⟩ : MConf CV (Arm.ArmState × Nat)).world.2 +
        opCalls vc (MConf.run ⟨0, .move src dst :: its, m, (w, 5)⟩ : MConf CV (Arm.ArmState × Nat)) :=
  MStep.counted_ctr (keep := ckeep) (rf := rf) (sem := sem) .move

/-- **The identity machine counting every state realises every semantics, `opCalls` states per
segment.** -/
theorem realizesC_any {V W : Type} (vc : VCode) (rf : RFunc) (sem : ISem V W) (keep : Reg → V → V) :
    RealizesC vc rf sem keep (id : Unit → Unit) (fun _ _ => True) (fun _ => True) (fun _ => True) :=
  fun _ c c' _ hs => ⟨opCalls vc c, c', hs, trivial, fun _ _ => trivial, countIn_true _ _ _⟩

theorem realizes_of_C (vc : VCode) (rf : RFunc) (sem : ISem CV Arm.ArmState) :
    Realizes vc rf sem ckeep (id : Unit → Unit) (fun _ _ => True) (fun _ => True) :=
  (realizesC_any vc rf sem ckeep).toRealizes

/-- **The counted semantics with the counter equal to the count** on it. -/
theorem counted_any (vc : VCode) (rf : RFunc) (sem : Nat → ISem CV Arm.ArmState) :
    Realizes vc rf (ISem.counted sem) ckeep (stepC (fun _ => True) (id : Unit → Unit))
      (fun p c => True ∧ p.2 = c.world.2) (fun _ => True) :=
  RealizesC.counted (Q := fun _ _ => True) (T := fun _ => True) fun n => realizesC_any vc rf (sem n) ckeep

end Backend.Proof.RegLevelCountIWitness
