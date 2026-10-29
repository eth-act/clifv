module

public import FV.Backend.Proof.StockRootOpcodeMatch
public import FV.Backend.Proof.IselCmpRoot

@[expose] public section

namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
section SourceData
attribute [local semireducible] Isle.Aarch64.program
/-- Original accepted comparisons determine their exact source data and boolean
result type. The scalar width follows from the unchanged original scope. -/
theorem stock_cmp_source_data {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {cc : Clif.IntCC} {i x y : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.icmp cc ty x y)) :
    (ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64) ∧
      info.data = .data 152 14 [.data 151 72 [],.values [x,y],.data 145 (ccIdx cc) []] ∧
      info.resTys.head? = some (.int 8) := by
  have accepted := inv.instE i info _ source clif
  have supported : eTy ty = true := by simpa [Compile.instE,Compile.tyE,eTy] using accepted
  have raw := inv.data i info _ source clif
  obtain ⟨types,result,typed,_⟩ := inv.resTys i info _ source clif
  simp only [Clif.Inst.resultTypes] at result
  cases result
  refine ⟨?_,?_,by rw [typed]; rfl⟩
  · cases ty <;> simp [eTy,Clif.Ty.width] at supported ⊢
  · have expected : instData f (.icmp cc ty x y) =
        .ok (.data 152 14 [.data 151 72 [],.values [x,y],.data 145 (ccIdx cc) []]) := by
      simp only [instData,supported,ite_true,mkVariant_intcc]
      rfl
    exact Except.ok.inj (raw.symm.trans expected)
end SourceData
private theorem inventory : sourceOpcodeIds 72 = [958] := by decide +kernel
/-- Actual original-source comparison selection must be the real comparison
root958; no caller-supplied match or rule-selection certificate is introduced. -/
theorem stock_selected_cmp_root {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {cc : Clif.IntCC} {i x y : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.icmp cc ty x y))
    {st next : State} {out : V} {rules : List RuleId}
    (selected : LowerSelection ctx i st out next rules) : selected.rule.id = 958 := by
  obtain ⟨_,data,_⟩ := stock_cmp_source_data inv source clif
  have member := stock_selected_source_opcode_ids inv source clif data selected
  rw [inventory] at member
  simpa only [List.mem_singleton] using member
end Backend.Stock.Proof.ScalarCmp
