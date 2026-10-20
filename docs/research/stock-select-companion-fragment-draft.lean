import FV.Backend.Proof.StockSelectBooleanCompanion
import FV.Backend.Proof.StockSelectReplacementResolved
namespace Backend.Stock.Proof.ScalarSelect
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
/-- Actual retained records start with an empty emission buffer. A boolean
companion fragment therefore identifies its final consumer without assuming
an arbitrary existential comparison fragment has the desired instruction shape. -/
theorem stock_select_companion_fragment_code {start middle : LState} {producer : MInst}
    {condition : Cond} {code : List MInst} (empty : start.emitted = #[])
    (fragment : Frag start (((middle.fresh .int).2.emit producer).emit
      (.cset (middle.fresh .int).1 condition)) code) :
    code = middle.emitted.toList ++ [producer,.cset (middle.fresh .int).1 condition] := by
  have emitted := congrArg Array.toList fragment.emitted
  simpa only [LState.emit,LState.fresh,Array.toList_push,Array.toList_append,empty,
    Array.toList_empty,List.nil_append,List.toList_toArray,List.append_assoc,List.cons_append,
    List.nil_append] using emitted.symm
/-- Replacing the companion consumer preserves the exact fresh-definition
fragment for the real csel, including the complete emitter prefix. -/
theorem stock_select_companion_fragment_replace {start middle : LState} {producer : MInst}
    {condition : Cond} {code : List MInst} (x y : Nat) (empty : start.emitted = #[])
    (fragment : Frag start (((middle.fresh .int).2.emit producer).emit
      (.cset (middle.fresh .int).1 condition)) code) :
    Frag start (((middle.fresh .int).2.emit producer).emit
      (.csel (middle.fresh .int).1 (.vreg x .int) (.vreg y .int) condition))
      (middle.emitted.toList ++ [producer,.csel (middle.fresh .int).1 (.vreg x .int) (.vreg y .int) condition]) := by
  have shape := stock_select_companion_fragment_code empty fragment
  constructor
  · apply Array.toList_inj.mp
    simp [LState.emit,LState.fresh,empty]
  · exact fragment.mono
  · intro inst member k defined
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with prior | rfl | rfl
    · exact fragment.defs inst (by rw [shape]; simp [prior]) k defined
    · exact fragment.defs inst (by rw [shape]; simp) k defined
    · apply fragment.defs (.cset (middle.fresh .int).1 condition) (by rw [shape]; simp) k
      change k ∈ vdefs (.csel (.vreg middle.nextVreg .int) (.vreg x .int) (.vreg y .int) condition) at defined
      change k ∈ vdefs (.cset (.vreg middle.nextVreg .int) condition)
      simpa only [vdefs_cset,vdefs_csel] using defined
end Backend.Stock.Proof.ScalarSelect
#print axioms Backend.Stock.Proof.ScalarSelect.stock_select_companion_fragment_code
#print axioms Backend.Stock.Proof.ScalarSelect.stock_select_companion_fragment_replace
