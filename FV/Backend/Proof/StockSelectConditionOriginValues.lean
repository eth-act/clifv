module

public import FV.Backend.Proof.StockSelectConditionCalls

@[expose] public section

namespace Backend.Stock.Proof.ScalarSelect
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
private theorem icmp_definition_values {ctx : Ctx} {fr : Clif.Frame} (dfg : DFGCons ctx fr)
    {c a b : Nat} {cc : Clif.IntCC} {ty : Clif.Ty} {value : Clif.Val}
    (definition : ctx.defClif? c = some (.icmp cc ty a b)) (read : fr.regs c = some value) :
    ∃ u v : BitVec ty.width,fr.getAs a ty = .ok u ∧ fr.getAs b ty = .ok v ∧
      value = ⟨.i8,Clif.Sem.bool8 (Clif.Sem.intcc cc u v)⟩ := by
  obtain ⟨i,info,defined,found,source⟩ := cmp_defClif_inv definition
  obtain ⟨vals,evaluated,written⟩ := dfg.1 c i info _ value defined found source rfl read
  obtain ⟨u,v,getA,getB,rfl,_⟩ := evalInst_icmp_ok (evaluated default)
  exact ⟨u,v,getA,getB,lookup_zip_single written⟩
/-- Actual650 comparison provenance and the original restricted DFG determine
both original comparison reads and condition truth, including zero-extended
comparison results whose machine value was never materialized. -/
theorem stock_select_comparison_origin_values {ctx : Ctx} {fr : Clif.Frame} (dfg : DFGCons ctx fr)
    {c a b : Nat} {cc : Clif.IntCC} {ty : Clif.Ty} {value : Clif.Val}
    (origin : SelectComparisonOrigin ctx c cc ty a b) (read : fr.regs c = some value) :
    ∃ u v : BitVec ty.width,fr.getAs a ty = .ok u ∧ fr.getAs b ty = .ok v ∧
      Clif.Sem.truthy value.bits = Clif.Sem.intcc cc u v := by
  rcases origin with direct | ⟨target,z,extension,comparison⟩
  · obtain ⟨u,v,getA,getB,same⟩ := icmp_definition_values dfg direct read
    refine ⟨u,v,getA,getB,?_⟩
    rw [same]
    exact truthy_bool8 _
  · obtain ⟨i,info,defined,found,source⟩ := cmp_defClif_inv extension
    obtain ⟨vals,evaluated,written⟩ := dfg.1 c i info _ value defined found source rfl read
    obtain ⟨test,readZ,grows,rfl,_⟩ := evalInst_uextend_ok (evaluated default)
    have same := lookup_zip_single written
    obtain ⟨u,v,getA,getB,testValue⟩ := icmp_definition_values dfg comparison readZ
    refine ⟨u,v,getA,getB,?_⟩
    rw [testValue] at same grows
    rw [same]
    change Clif.Sem.truthy (Clif.Sem.uextend target.width (Clif.Sem.bool8 (Clif.Sem.intcc cc u v))) = _
    rw [truthy_uextend8 (by change 8 ≤ target.width; change 8 < target.width at grows; omega),truthy_bool8]
end Backend.Stock.Proof.ScalarSelect
