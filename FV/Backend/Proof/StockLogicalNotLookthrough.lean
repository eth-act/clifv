import FV.Backend.Proof.IselFamALUALogicNot
import FV.Backend.Proof.StockSourceView
import FV.Backend.Proof.IselCovForm

namespace Backend.Stock.Proof.LogicalNot
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- A real nested NOT pattern exposes the source definition and complement
value, without assuming that its result has a separate machine register. -/
theorem stock_not_pattern_value {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {fr : Clif.Frame} (dfg : DFGCons ctx fr)
    {x slot : Nat} {ty : Clif.Ty} {v : BitVec ty.width} (source : fr.getAs x ty = .ok v)
    {st : State} {environment environment' : Isle.Interp.Env V}
    (matched : matchPat p (Stock.sem ctx) st
      (.term 15 1 [.term 18 209 [.wildcard 14,
        .term 152 2476 [.term 151 2384 [],.bind 15 slot (.wildcard 15)]]])
      (.value x) environment = .ok (some environment')) :
    ∃ (j y : Nat) (info : IInfo) (ty' : Clif.Ty) (u : BitVec ty.width),
      ctx.defInst? x = some j ∧ ctx.insts[j]? = some info ∧ info.clif = some (.unary .bnot ty' y) ∧
      fr.getAs y ty = .ok u ∧ v = ~~~u := by
  rw [stock_matchPat] at matched
  obtain ⟨j,info,fields,env0,defined,found,data,rest⟩ :=
    defInst_match_inv hp ctx hp.t2476 term_2476_kind hp.t2384 term_2384_kind matched
  obtain ⟨cl,original,raw⟩ := ctxInv_clif inv.identityView defined found
  rw [data] at raw
  obtain ⟨ty',y,rfl,rfl⟩ := instData_bnot_inv raw
  obtain ⟨u,get,value⟩ := bnot_value dfg defined found original source
  exact ⟨j,y,info,ty',u,defined,found,original,get,value⟩

end Backend.Stock.Proof.LogicalNot
