import FV.Backend.Proof.StockProtectedSinkFrame
import FV.Backend.Proof.LowerSim
import FV.Backend.Proof.LowerDecide
import FV.Backend.Proof.StockNoLoadSource

namespace Backend.Stock.Proof.SinkRules.ProtectedWitness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
attribute [local irreducible] Isle.Aarch64.program

private def function (atomic signed : Bool) : Clif.Function := {
  name := "protected_store_with_load"
  sig := {params := List.replicate 2 ⟨.i64,.none,.normal⟩,returns := [⟨.i64,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(0,.i64),(1,.i64)],body := [
    ⟨[2],if atomic then .atomicLoad .i8 {} 0 else .load .load .i8 {} 0 0⟩,
    ⟨[3],.extend (if signed then .sextend else .uextend) .i64 2⟩,
    ⟨[],.store .store .i64 {} 1 0 0⟩],term := .jump ⟨1,[]⟩},
    {id := 1,term := .ret [3]}] }
private def built (atomic signed : Bool) :=
  (Stock.buildCtx (function atomic signed)).toOption.getD (sinkCtx,#[],sinkState)
private def input : State := {sinkState with
  demand := #[0,0,0,0],uses := #[.once,.once,.once,.once],
  sunk := #[false,false,false],entryColor := #[1,1,1],current := some 1}
private theorem scope (atomic signed : Bool) : LowerScope (function atomic signed) := by
  cases atomic <;> cases signed <;> exact lowerScope_of (by decide +kernel)
private theorem mapped (atomic signed : Bool) :
    MappedCtxInv (function atomic signed) (built atomic signed).1 :=
  buildCtx_mappedInv (scope atomic signed) (ranges := (built atomic signed).2.1) (st := (built atomic signed).2.2) (by cases atomic <;> cases signed <;> rfl)
private theorem safe (atomic signed : Bool) : NoLoadAt (built atomic signed).1 2 := by
  intro info found fmt fields load
  have clif : info.clif = some (.store .store .i64 {} 1 0 0) := by
    cases atomic <;> cases signed <;> cases found <;> rfl
  exact inst_data_no_load ((mapped atomic signed).instE 2 info _ found clif)
    (by constructor <;> decide +kernel)
    ((mapped atomic signed).data 2 info _ found clif) fmt fields load
private theorem empty (atomic signed : Bool) : (built atomic signed).1.insts[2]!.results = [] := by
  cases atomic <;> cases signed <;> rfl

private def patternOk (atomic : Bool) : Bool :=
  match (matchRule program (Stock.sem (built atomic false).1) {} 2
      (if atomic then rule_inst_3905 else rule_inst_4203)
      (if atomic then [.inst 0] else [.ty (.int 8),.inst 0])).run (input,#[]) with
  | .ok (some bound,matched,tr) =>
    match (evalExpr program (Stock.sem (built atomic false).1) {} 2005
        (if atomic then rule_inst_3905 else rule_inst_4203).rhs bound).run (matched,tr) with
    | .ok (some _,next,_) => next.sunk[0]! && !next.sunk[2]!
    | _ => false
  | _ => false
private theorem patternOk_true (atomic : Bool) : patternOk atomic = true := by
  cases atomic <;> decide +kernel

/-- Both actual load helpers sink a load beside an installed protected store. -/
theorem pattern_frame_witness (atomic : Bool) :
    ∃ bound matched next tr tr' out,
      NoLoadAt (built atomic false).1 2 ∧
      (built atomic false).1.insts[2]!.results = [] ∧
      2 < input.sunk.size ∧ input.sunk[2]! = false ∧
      (matchRule program (Stock.sem (built atomic false).1) {} 2
        (if atomic then rule_inst_3905 else rule_inst_4203)
        (if atomic then [.inst 0] else [.ty (.int 8),.inst 0])).run (input,#[]) =
          .ok (some bound,matched,tr) ∧
      (evalExpr program (Stock.sem (built atomic false).1) {} 2005
        (if atomic then rule_inst_3905 else rule_inst_4203).rhs bound).run (matched,tr) =
          .ok (some out,next,tr') ∧ next.sunk[0]! = true ∧ next.sunk[2]! = input.sunk[2]! := by
  have h := patternOk_true atomic
  unfold patternOk at h
  split at h
  · rename_i bound matched tr matchedRun
    split at h
    · rename_i out next tr' rhsRun
      have pair : next.sunk[0]! = true ∧ (!next.sunk[2]!) = true := by
        simpa only [Bool.and_eq_true] using h
      refine ⟨bound,matched,next,tr,tr',out,safe atomic false,empty atomic false,
        by decide,rfl,matchedRun,rhsRun,pair.1,?_⟩
      exact pattern_sink_rule_frame (safe atomic false)
        (fun m _ => protected_slot_frames (mapped atomic false) (safe atomic false) (empty atomic false) m)
        atomic matchedRun rhsRun
    · cases h
  · cases h

private def eligibilityOk (signed : Bool) : Bool :=
  match (matchRule program (Stock.sem (built false signed).1) {} 5
      (if signed then rule_lower_1359 else rule_lower_1300) [.inst 1]).run (input,#[]) with
  | .ok (some bound,matched,tr) =>
    match (evalExpr program (Stock.sem (built false signed).1) {} 2005
        (if signed then rule_lower_1359 else rule_lower_1300).rhs bound).run (matched,tr) with
    | .ok (some _,next,_) => next.sunk[0]! && !next.sunk[2]!
    | _ => false
  | _ => false
private theorem eligibilityOk_true (signed : Bool) : eligibilityOk signed = true := by
  cases signed <;> decide +kernel

/-- Both actual extension rules sink a load and preserve the installed store. -/
theorem eligibility_frame_witness (signed : Bool) :
    ∃ bound matched next tr tr' out,
      MappedCtxInv (function false signed) (built false signed).1 ∧
      NoLoadAt (built false signed).1 2 ∧
      (built false signed).1.insts[2]!.results = [] ∧
      2 < input.sunk.size ∧ input.sunk[2]! = false ∧
      (matchRule program (Stock.sem (built false signed).1) {} 5
        (if signed then rule_lower_1359 else rule_lower_1300) [.inst 1]).run (input,#[]) =
          .ok (some bound,matched,tr) ∧
      (evalExpr program (Stock.sem (built false signed).1) {} 2005
        (if signed then rule_lower_1359 else rule_lower_1300).rhs bound).run (matched,tr) =
          .ok (some out,next,tr') ∧ next.sunk[0]! = true ∧ next.sunk[2]! = input.sunk[2]! := by
  have h := eligibilityOk_true signed
  unfold eligibilityOk at h
  split at h
  · rename_i bound matched tr matchedRun
    split at h
    · rename_i out next tr' rhsRun
      have pair : next.sunk[0]! = true ∧ (!next.sunk[2]!) = true := by
        simpa only [Bool.and_eq_true] using h
      refine ⟨bound,matched,next,tr,tr',out,mapped false signed,safe false signed,empty false signed,
        by decide,rfl,matchedRun,rhsRun,pair.1,?_⟩
      exact eligibility_sink_rule_frame (mapped false signed) (empty false signed)
        (fun m _ => protected_slot_frames (mapped false signed) (safe false signed) (empty false signed) m)
        signed matchedRun rhsRun
    · cases h
  · cases h

private def namedCtx (branch : Bool) : Ctx :=
  if branch then termCtx (built false false).1 3
    ((termData (.jump ⟨1,[]⟩)).toOption.getD (.op .unit)) else (built false false).1
private theorem named_mapped (branch : Bool) : MappedCtxInv (function false false) (namedCtx branch) := by
  cases branch with
  | false => exact mapped false false
  | true => exact (mapped false false).termCtx (ti := 3) rfl _
private theorem named_safe (branch : Bool) : NoLoadAt (namedCtx branch) 2 := by
  cases branch with
  | false => exact safe false false
  | true =>
    intro info found fmt fields load decoded
    rw [show namedCtx true = termCtx (built false false).1 3
      ((termData (.jump ⟨1,[]⟩)).toOption.getD (.op .unit)) from rfl,
      termCtx_insts_ne (by decide)] at found
    exact safe false false info found fmt fields load decoded
private theorem named_empty (branch : Bool) : (namedCtx branch).insts[2]!.results = [] := by
  cases branch <;> rfl

private def namedOk (branch : Bool) : Bool :=
  match Stock.runTerm (namedCtx branch) (if branch then "lower_branch" else "lower")
      (if branch then [.inst 3,.labels [1]] else [.inst 1]) input with
  | .ok (some _,next,_) => !next.sunk[2]!
  | _ => false
private theorem namedOk_true (branch : Bool) : namedOk branch = true := by
  cases branch <;> native_decide

/-- Both named production helpers execute with a real protected store slot. -/
theorem named_frame_witness (branch : Bool) :
    ∃ out next trace,
      Stock.runTerm (namedCtx branch) (if branch then "lower_branch" else "lower")
        (if branch then [.inst 3,.labels [1]] else [.inst 1]) input =
          .ok (some out,next,trace) ∧
      2 < input.sunk.size ∧ next.sunk[2]! = input.sunk[2]! := by
  have h := namedOk_true branch
  unfold namedOk at h
  split at h
  · rename_i out next trace run
    refine ⟨out,next,trace,run,by decide,?_⟩
    cases branch with
    | false => exact protected_slot_lower (named_mapped false) (named_safe false) (named_empty false) run
    | true => exact protected_slot_branch (named_mapped true) (named_safe true) (named_empty true) run
  · cases h

end Backend.Stock.Proof.SinkRules.ProtectedWitness
