import FV.Backend.Proof.PrepareCheck
import FV.Backend.Proof.IselCmpRoot

namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false

/-- The original DFG invariant re-evaluates the looked-through comparison in
the same frame. In a restricted frame this derives operand availability as well
as the exact stored boolean, without demanding an unavailable old operand. -/
theorem stock_cast_cmp_source_operands {ctx : Ctx} {fr : Clif.Frame}
    (dfg : DFGCons ctx fr) {z j x y : Nat} {info : IInfo} {cc : Clif.IntCC} {ty : Clif.Ty}
    (defined : ctx.defInst? z = some j) (found : ctx.insts[j]? = some info)
    (clif : info.clif = some (.icmp cc ty x y)) {value : Clif.Val}
    (get : fr.regs z = some value) :
    ∃ u v,fr.getAs x ty = .ok u ∧ fr.getAs y ty = .ok v ∧
      value = ⟨.i8,Clif.Sem.bool8 (Clif.Sem.intcc cc u v)⟩ := by
  obtain ⟨vals,evaluated,lookup⟩ := dfg.1 z j info _ value defined found clif rfl get
  obtain ⟨u,v,getX,getY,rfl,_⟩ := evalInst_icmp_ok (evaluated default)
  have actual := lookup_zip_single lookup
  exact ⟨u,v,getX,getY,actual⟩

end Backend.Stock.Proof.ScalarCmp
