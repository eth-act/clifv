import FV.Backend.Proof.StockRootOpcodeMatch
namespace Backend.Stock.Proof.ScalarDiv
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
def opcodeId : Clif.DivOp → Nat | .udiv => 82 | .sdiv => 83 | .urem => 84 | .srem => 85
def rootIds : Clif.DivOp → List RuleId
  | .udiv => [786,787]
  | .sdiv => [790,791,788,789]
  | .urem => [792,793]
  | .srem => [794,795]
section SourceData
attribute [local semireducible] Isle.Aarch64.program
/-- Original accepted high-multiply instructions determine their exact scalar
opcode, width and operand data; source IDs retain the original numbering. -/
theorem stock_div_source_data {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    (op : Clif.DivOp) {i x y : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info)
    (clif : info.clif = some (.div op ty x y)) :
    (ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64) ∧
      info.data = .data 152 2 [.data 151 (opcodeId op) [],.values [x,y]] ∧
      info.resTys.head? = some (.int ty.width) := by
  have accepted := inv.instE i info _ source clif
  have supported : eTy ty = true := by cases op <;> simpa [Compile.instE,Compile.tyE,eTy] using accepted
  have raw := inv.data i info _ source clif
  obtain ⟨types,result,typed,_⟩ := inv.resTys i info _ source clif
  simp only [Clif.Inst.resultTypes] at result
  cases result
  refine ⟨?_,?_,by rw [typed]; simp [ofClif_int_width (isInt_of_eTy supported)]⟩
  · cases ty <;> simp [eTy,Clif.Ty.width] at supported ⊢
  · have expected : instData f (.div op ty x y) =
        .ok (.data 152 2 [.data 151 (opcodeId op) [],.values [x,y]]) := by
      cases op <;> simp [instData,divOpcode,supported] <;> rfl
    exact Except.ok.inj (raw.symm.trans expected)
end SourceData
private theorem inventory (op : Clif.DivOp) : sourceOpcodeIds (opcodeId op) = rootIds op := by
  cases op <;> decide +kernel
/-- Actual original Stock source selection belongs to the complete division/
remainder inventory, including general and safe signed-divisor roots. -/
theorem stock_selected_div_roots {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    (op : Clif.DivOp) {i x y : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.div op ty x y))
    {st next : State} {out : V} {rules : List RuleId}
    (selected : LowerSelection ctx i st out next rules) : selected.rule.id ∈ rootIds op := by
  obtain ⟨_,data,_⟩ := stock_div_source_data inv op source clif
  have member := stock_selected_source_opcode_ids inv source clif data selected
  rw [inventory] at member
  exact member
end Backend.Stock.Proof.ScalarDiv
