import FV.Backend.Proof.IselCmpSelect
import FV.Backend.Proof.StockPolicy
import FV.Backend.Proof.PrepareCheck
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
/-- A nonempty emitted prefix and two real flag instructions inhabit both
fragment-code extraction and consumer replacement at a fresh destination. -/
theorem stock_select_companion_fragment_witness (condition : Cond) :
    ∃ (start middle : LState) (producer : MInst) (code : List MInst),start.emitted = #[] ∧ middle.emitted.size = 1 ∧
      Frag start (((middle.fresh .int).2.emit producer).emit
        (.cset (middle.fresh .int).1 condition)) code ∧
      code = middle.emitted.toList ++ [producer,.cset (middle.fresh .int).1 condition] ∧
      Frag start (((middle.fresh .int).2.emit producer).emit
        (.csel (middle.fresh .int).1 (.vreg 1 .int) (.vreg 3 .int) condition))
        (middle.emitted.toList ++ [producer,.csel (middle.fresh .int).1 (.vreg 1 .int) (.vreg 3 .int) condition]) := by
  let start : LState := {sinkState.base with nextVreg := 4,emitted := #[]}
  let producer : MInst := .aluRRR .subS .size64 .xzr (.vreg 1 .int) (.vreg 3 .int)
  let middle := start.emit producer
  have noDefs : vdefs producer = [] := rfl
  have leading : Frag start middle [producer] := by
    refine ⟨rfl,Nat.le_refl _,?_⟩
    intro inst member k defined
    have same := List.mem_singleton.mp member
    subst inst
    rw [noDefs] at defined
    cases defined
  have tail : Frag middle (((middle.fresh .int).2.emit producer).emit
      (.cset (middle.fresh .int).1 condition)) [producer,.cset (middle.fresh .int).1 condition] :=
    Frag.fresh_emit2 middle noDefs (by rw [show (middle.fresh .int).1 = .vreg middle.nextVreg .int from rfl,vdefs_cset]; exact List.Subset.refl _)
  have full := leading.append tail
  exact ⟨start,middle,producer,_,rfl,rfl,full,stock_select_companion_fragment_code rfl full,
    stock_select_companion_fragment_replace 1 3 rfl full⟩
end Backend.Stock.Proof.ScalarSelect
