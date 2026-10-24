import FV.Backend.Proof.StockNoLoadDriverWitness

namespace Backend.Stock.Proof.SinkRules.BranchWitness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
attribute [local irreducible] Isle.Aarch64.program Stock.lower Stock.runTerm

/-- A genuine critical edge: entry branches to a join also reached by block one.
Both divisions, original arguments and the stack slot remain. -/
def function : Clif.Function :=
  let old := DriverWitness.function
  {old with name := "stock_no_load_critical_edge", blocks :=
    [{old.blocks[0]! with term := .brif 0 ⟨1,[1]⟩ ⟨2,[1]⟩},
      {id := 1,params := [(31,.i64)],term := .jump ⟨2,[31]⟩},
      {id := 2,params := [(47,.i64)],term := .ret [47]}]}

private theorem scope : LowerScope function := lowerScope_of (by decide +kernel)
private theorem formats : ∀ b ∈ function.blocks, ∀ stm ∈ b.body,
    CastComplete.MemoryFormat stm.inst := by
  intro b member stm statement
  change b ∈ [function.blocks[0]!,function.blocks[1]!,function.blocks[2]!] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · change stm ∈ [⟨[100],.div .sdiv .i64 1 8⟩,⟨[101],.div .udiv .i64 100 8⟩] at statement
    simp only [List.mem_cons,List.not_mem_nil,or_false] at statement
    rcases statement with rfl | rfl <;> simp [CastComplete.MemoryFormat,instNames]
  · cases statement
  · cases statement

private def observed (result : Except String Result) : Bool :=
  match result with
  | .error _ => false
  | .ok output => decide (output.blockScans.size = 3) &&
      output.order.nodes.any (fun node => match node with | .edge .. => true | _ => false)

private theorem checked : observed (Stock.lower function) = true := by native_decide

private theorem decode {result : Except String Result} (check : observed result = true) :
    ∃ output, result = .ok output ∧ output.blockScans.size = 3 ∧
      ∃ node ∈ output.order.nodes.toList, match node with | .edge .. => True | _ => False := by
  cases result with
  | error message => cases check
  | ok output =>
    simp only [observed,Bool.and_eq_true,decide_eq_true_eq] at check
    have any : output.order.nodes.toList.any (fun node => match node with
        | .edge .. => true | _ => false) = true := by
      simpa only [Array.any_toList] using check.2
    obtain ⟨node,member,edge⟩ := List.any_eq_true.mp any
    refine ⟨output,rfl,check.1,node,member,?_⟩
    cases node <;> simp_all

/-- Actual conditional/jump/return helpers and a critical-edge node inhabit
the universal block/node/traversal and retained-boundary invariant. -/
theorem critical_edge_driver_witness : ∃ output,
    Stock.lower function = .ok output ∧ LowerScope function ∧
    output.blockScans.size = 3 ∧
    (∃ node ∈ output.order.nodes.toList, match node with | .edge .. => True | _ => False) ∧
    SunkEq output.initial output.final ∧ RecordsSunkEq output.initial output.blockScans := by
  obtain ⟨output,run,blocks,edge⟩ := decode checked
  obtain ⟨final,records⟩ := stock_lower_no_load_sunk_eq scope formats run
  exact ⟨output,run,scope,blocks,edge,final,records⟩

private def callDataFunction : Clif.Function :=
  {name := "no_load_try_data",sig := {params := [],returns := []},
    sigDecls := [(0,{params := [],returns := []})],blocks := []}
private def callDataTerm : Clif.Terminator :=
  .tryCallIndirect 0 [] {sig := 0,normal := ⟨0,[]⟩}
private def callData : V := instDataV "TryCallIndirect"
  [opcodeV "TryCallIndirect",.values [0],.op (.exnTable {params := [],returns := []} [])]

/-- Actual successful exception-call data construction inhabits the generic
format theorem independently of the scalar activation's source class. -/
theorem try_call_format_witness (ctx : Ctx) :
    tryCallData callDataFunction callDataTerm = .ok callData ∧
    ∀ fmt fields, fmt = 16 ∨ fmt = 17 →
      (Backend.sem ctx).unData 152 callData ≠ some (fmt,fields) := by
  have encoded : tryCallData callDataFunction callDataTerm = .ok callData := rfl
  exact ⟨encoded,try_call_data_no_load encoded⟩

end Backend.Stock.Proof.SinkRules.BranchWitness
