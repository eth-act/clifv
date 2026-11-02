import FV.Backend.Proof.StockShiftRootReceipts
import FV.Backend.Proof.StockRootOpcodeMatch
namespace Backend.Stock.Proof.ShiftComplete
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.ScalarShift
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

def candidateIds : Kind → List Nat
  | .lsl => [874,873]
  | .lsr => [893,884,883]
  | .asr => [892,891,890]

/-- Current original-source closure has eight shift candidates. Historical
root counts include cases excluded by the existing scope/adapter proof. -/
theorem opcode_inventory (kind : Kind) : sourceOpcodeIds kind.opcode = candidateIds kind := by
  cases kind <;> unfold sourceOpcodeIds <;>
    rw [show TId.lower = 686 from rfl,data_program.r686] <;> decide +kernel

section Source
attribute [local semireducible] Isle.Aarch64.program
private theorem source_data {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    (kind : Kind) {i x y : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.binary kind.cop ty x y)) :
    info.data = .data 152 2 [.data 151 kind.opcode [],.values [x,y]] := by
  have accepted := inv.instE i info _ source clif
  have supported : eTy ty = true := by
    cases kind <;> simpa [Kind.cop,Compile.instE,Compile.binaryE,Compile.tyE,eTy] using accepted
  have raw := inv.data i info _ source clif
  have shape : instData f (.binary kind.cop ty x y) =
      .ok (.data 152 2 [.data 151 kind.opcode [],.values [x,y]]) := by
    cases kind <;> simp only [Kind.cop,Kind.opcode,instData,binaryOpcode,supported,ite_true] <;> rfl
  exact Except.ok.inj (raw.symm.trans shape)
end Source

/-- Actual first-match selection derives the complete shift root boundary
internally, retaining original mapped-context and source conditions. -/
theorem selected_rule_ids {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    (kind : Kind) {i x y : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.binary kind.cop ty x y))
    {st next : State} {out : V} {trace : List RuleId}
    (selected : LowerSelection ctx i st out next trace) : selected.rule.id ∈ candidateIds kind := by
  have member := stock_selected_source_opcode_ids inv source clif (source_data inv kind source clif) selected
  rwa [opcode_inventory] at member
end Backend.Stock.Proof.ShiftComplete
