module

public import FV.Backend.Proof.StockNoLoadDriver
public import FV.Backend.Proof.LowerDecide
public import FV.E2E.StockDivFixtures

@[expose] public section

namespace Backend.Stock.Proof.SinkRules.DriverWitness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
attribute [local irreducible] Isle.Aarch64.program Stock.lower Stock.runTerm

/-- The first division is consumed by a second division whose result is unused.
All nine original arguments and the explicit stack slot remain. -/
def function : Clif.Function :=
  let original := E2E.StockDivNIWitness.function .defaultI64 .sdiv
  {original with name := "stock_two_divisions_unused", blocks := original.blocks.map fun b =>
    {b with body := [⟨[100],.div .sdiv .i64 1 8⟩,⟨[101],.div .udiv .i64 100 8⟩],term := .ret [1]}}

private theorem scope : LowerScope function := lowerScope_of (by decide +kernel)

private theorem family : ∀ b ∈ function.blocks, ∀ stm ∈ b.body,
    HighMulBody.Family stm.inst ∨ ∃ op ty x y, stm.inst = .div op ty x y := by
  intro b member stm statement
  have table : function.blocks = [function.blocks[0]!] := rfl
  have block : b = function.blocks[0]! := by
    rw [table] at member
    exact List.mem_singleton.mp member
  subst b
  change stm ∈ [⟨[100],.div .sdiv .i64 1 8⟩,⟨[101],.div .udiv .i64 100 8⟩] at statement
  simp only [List.mem_cons,List.not_mem_nil,or_false] at statement
  rcases statement with rfl | rfl
  · exact Or.inr ⟨.sdiv,.i64,1,8,rfl⟩
  · exact Or.inr ⟨.udiv,.i64,100,8,rfl⟩

private def observation (result : Except String Result) : Bool :=
  match result with
  | .error _ => false
  | .ok result => decide (result.blockScans.size = 1) &&
      decide (result.schedule.toList.countP (fun s => s.decision == .emitted) = 3) &&
      decide (result.initial.demand[101]! = 0)

private theorem observed : observation (Stock.lower function) = true := by native_decide

private theorem decode {result : Except String Result} (checked : observation result = true) :
    ∃ output, result = .ok output ∧ output.blockScans.size = 1 ∧
      output.schedule.toList.countP (fun s => s.decision == .emitted) = 3 ∧
      output.initial.demand[101]! = 0 := by
  cases result with
  | error message => cases checked
  | ok output =>
    simp only [observation,Bool.and_eq_true,decide_eq_true_eq] at checked
    exact ⟨output,rfl,checked.1.1,checked.1.2,checked.2⟩

/-- Actual whole lowering emits both original divisions and the return. The
universal source-derived driver theorem protects every retained boundary. -/
theorem two_division_driver_witness : ∃ output,
    Stock.lower function = .ok output ∧ LowerScope function ∧
    output.blockScans.size = 1 ∧
    output.schedule.toList.countP (fun s => s.decision == .emitted) = 3 ∧
    output.initial.demand[101]! = 0 ∧
    ∀ q : Nat, output.final.sunk[q]! = false ∧
      ∀ event ∈ output.blockScans.toList, event.input.sunk[q]! = false ∧
        ∀ record ∈ event.output.records,
          record.input.sunk[q]! = false ∧ record.output.state.sunk[q]! = false := by
  obtain ⟨output,run,blocks,emitted,demand⟩ := decode observed
  exact ⟨output,run,scope,blocks,emitted,demand,
    fun q => stock_lower_scalar_div_unsunk run scope family q⟩

end Backend.Stock.Proof.SinkRules.DriverWitness
