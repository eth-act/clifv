import FV.Backend.Lowering.Stock
import FV.Arm.MinTheory
import FV.Backend.Proof.PrepareCheck
import FV.Backend.Proof.IselInterp

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Stock.runTerm branchArgs collectOutgoing scanBlock

private theorem handler_labels (items : List (Option Nat)) (labels : List Label)
    (size : labels.length = items.length + 1) :
    ((items.zip labels).map (fun | (some n,l) => TryHandler.tag n l | (none,l) => .default l)).map
      (·.label) ++ [labels.getLastD 0] = labels := by
  induction items generalizing labels with
  | nil =>
    cases labels with
    | nil => simp at size
    | cons l ls =>
      have empty : ls = [] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons,List.length_nil] at size; omega)
      subst ls
      rfl
  | cons item items ih =>
    cases labels with
    | nil => simp at size
    | cons label labels =>
      have count : labels.length = items.length + 1 := by simp only [List.length_cons] at size; omega
      have nonempty : labels ≠ [] := by intro empty; simp [empty] at count
      have last : (label :: labels).getLastD 0 = labels.getLastD 0 := by
        cases labels with
        | nil => contradiction
        | cons next rest => rfl
      cases item <;> simpa only [List.zip_cons_cons,List.map_cons,TryHandler.label,List.cons_append,last]
        using congrArg (List.cons label) (ih labels count)

private theorem try_targets {sig : Clif.Signature} {items : List (Option Nat)}
    {labels : List Label} {info : TryInfo} (run : tryInfoOf sig items labels = some info) :
    info.handlers.map (·.label) ++ [info.continuation] = labels := by
  unfold tryInfoOf at run
  split at run
  · cases run
  · rename_i count
    simp only [bne_iff_ne,ne_eq,Decidable.not_not] at count
    cases run
    exact handler_labels items labels count

/-- The actual TryCall replacement gate returns a terminator whose targets
are exactly the computed successor labels, including all handlers followed by
the normal continuation. No property of the preceding call code is assumed. -/
theorem stock_branchCode_try_targets {f : Clif.Function} {term : Clif.Terminator}
    {labels : Array Nat} {before after : Array MInst}
    (isTry : term.isTry = true) (run : branchCode f term labels before = .ok after) :
    ∃ last,after.back? = some last ∧ last.isTerminator = true ∧ last.targets = labels.toList := by
  cases term <;> simp [Clif.Terminator.isTry] at isTry
  all_goals
    unfold branchCode at run
    dsimp only at run
    repeat' first
      | (solve | cases run)
      | simp only [bind,Except.bind,pure,Except.pure] at run
      | split at run
    all_goals
      cases run
      simp only [Array.back?_push]
      refine ⟨_,rfl,rfl,?_⟩
      rename_i _ pair _ _ info infoRun _ call _
      simpa only [MInst.targets] using try_targets infoRun

private theorem branch_targets {ctx : Ctx} {f : Clif.Function} {term : Clif.Terminator}
    {bi ti : Nat} {labels : Array Nat} {input : State} {out : BranchEmission}
    (isTry : term.isTry = true) (run : emitBranch ctx f term bi ti labels input = .ok out) :
    ∃ last,out.code.back? = some last ∧ last.isTerminator = true ∧ last.targets = labels.toList := by
  unfold emitBranch at run
  dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind,Except.bind,pure,Except.pure] at run
    | split at run
  all_goals
    cases run
    exact stock_branchCode_try_targets isTry (by assumption)

private theorem append_last {α : Type} {left right : Array α} {last : α}
    (atLast : right.back? = some last) : (left ++ right).back? = some last := by
  rw [Array.back?_append]
  simp only [atLast]
  rfl

private theorem map_some_inv {α : Type} {call : Except String α} {out : Option α}
    (run : (some <$> call) = .ok out) : ∃ value,call = .ok value ∧ out = some value := by
  cases call with
  | error err => cases run
  | ok value => cases run; exact ⟨value,rfl,rfl⟩

/-- Actual body scanning and outgoing-demand collection cannot change the
TryCall terminator or its computed handler/continuation successor ordering. -/
theorem stock_lowerBlockCore_try_targets {ctx : Ctx} {order : Order} {f : Clif.Function}
    {b : Clif.Block} {bi start stop : Nat} {data : Backend.V} {labels : Array Nat}
    {input : State} {out : LoweredBlockCore}
    (isTry : b.term.isTry = true)
    (run : lowerBlockCore ctx order f b bi start stop data labels input = .ok out) :
    ∃ last,out.code.back? = some last ∧ last.isTerminator = true ∧ last.targets = labels.toList := by
  cases term : b.term <;> simp only [term,Clif.Terminator.isTry] at isTry
  all_goals try contradiction
  all_goals
    unfold lowerBlockCore at run
    simp only [term] at run
    repeat' first
      | (solve | cases run)
      | simp only [bind,Except.bind,pure,Except.pure,Functor.map,Except.map] at run
      | split at run
    all_goals
      cases run
      rename_i _ branch branchRun _ outgoing outgoingRun _ scan scanRun
      obtain ⟨emission,emitted,wrapped⟩ := map_some_inv branchRun
      subst branch
      obtain ⟨last,atLast,terminal,targets⟩ := branch_targets (run := emitted) (by rfl)
      exact ⟨last,append_last atLast,terminal,targets⟩

end Backend.Stock.Proof
