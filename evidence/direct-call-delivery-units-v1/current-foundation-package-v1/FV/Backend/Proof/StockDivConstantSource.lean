import FV.Backend.Proof.StockSourceView
import FV.Backend.Proof.StockDFG
import FV.Backend.Proof.IselFamALUA

/-! The original constant a division's look-through data denotes
(`stock_div_constant_source_value`). Its own module, so that the comparison source values that use
it need not wait for the division requests (`StockDivConstant`). -/
namespace Backend.Stock.Proof.ScalarDiv
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
/-- A divisor's real look-through data denotes its original constant value.
Only the original mapped context, restricted DFG and source getter are needed. -/
theorem stock_div_constant_source_value {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {fr : Clif.Frame} (dfg : DFGCons ctx fr)
    {y j : Nat} {info : IInfo} {i : Int} {ty : Clif.Ty} {u : BitVec ty.width}
    (get : fr.getAs y ty = .ok u) (defined : ctx.defInst? y = some j)
    (found : ctx.insts[j]? = some info)
    (data : info.data = .data 152 35 [.data 151 57 [],.int i]) :
    info.clif = some (.iconst ty u) ∧ i = imm64OfIconst ty u := by
  obtain ⟨original,clif,raw⟩ := ctxInv_clif inv.identityView defined found
  rw [data] at raw
  obtain ⟨ty',c,rfl,equal⟩ := instData_iconst_inv raw
  have value := dfg_single dfg defined found clif rfl (getAs_ok get) (a := ⟨ty',c⟩)
    (fun vals cm cm' run => by rw [evalInst_iconst] at run; cases run; rfl)
  cases value
  exact ⟨clif,V.int.inj (List.cons.inj equal).1⟩
end Backend.Stock.Proof.ScalarDiv
