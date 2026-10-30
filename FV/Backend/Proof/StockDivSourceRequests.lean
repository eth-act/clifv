import FV.Backend.Proof.StockDivConstantSource
import FV.Backend.Proof.StockDivRequests
import FV.Backend.Proof.StockDivImmValues
namespace Backend.Stock.Proof.ScalarDiv
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
def SourceDivisorValues (F : BitVec 64 → Prop) (isem : Backend.Proof.Sem) (ctx : Ctx) (y e : Nat)
    (ty : Clif.Ty) (u : BitVec ty.width) (s s' : State × Array RuleId) (out : V) : Prop :=
  (∃ j info,ctx.defInst? y = some j ∧ ctx.insts[j]? = some info ∧
      info.clif = some (.iconst ty u) ∧ imm64OfIconst ty u ≠ 0 ∧
      s'.1 = {s.1 with base := s'.1.base} ∧
      ImmOut F isem ty.width e (u64 (imm64OfIconst ty u)) s.1.base s'.1.base out) ∨
    (ty.width = 64 ∧ DemandAllowed ctx s.1 y ∧ ∃ ry,ctx.valueReg? y = some ry ∧ out = .reg ry ∧
      s'.1 = {s.1.mark y with base := s.1.base.emit (.trapIf (.zero ry .size64) .intDivz)}) ∨
    (ty.width ≤ 32 ∧ ∃ r middle,ScalarShift.MappedExtOut ctx y (e == 0) 32 [.int 32,.int 64] s.1 middle (.reg r) ∧
      out = .reg r ∧ s'.1 = {middle with base := middle.base.emit (.trapIf (.zero r .size32) .intDivz)})
/-- Successful divisor requests expose machine-valued original constants or
original guarded register/widening paths. The materialization fuel bound is
proved from execution, rather than imposed on the source. -/
theorem stock_div_divisor_source_values {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {fr : Clif.Frame} (dfg : DFGCons ctx fr) {y e n : Nat}
    {ty : Clif.Ty} {u : BitVec ty.width} (get : fr.getAs y ty = .ok u)
    {cfg : Config} (hc : cfg.checkOverlap = false) (enough : 120 ≤ n)
    (width : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64) (extension : e = 0 ∨ e = 1)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {s s' : State × Array RuleId} {out : V}
    (run : ApplyInternal p (Stock.sem ctx) cfg n 27 698 [.value y,.data 125 e [],.ty (.int ty.width)] s out s') :
    SourceDivisorValues F isem ctx y e ty u s s' out := by
  have observed := stock_div_divisor_observed_with_fuel hp ctx hc enough width extension run
  rcases observed with ⟨j,info,i,defined,found,data,nonzero,fuel,trace,bound,materialized⟩ | guarded | widened
  · obtain ⟨original,equal⟩ := stock_div_constant_source_value inv dfg get defined found data
    subst i
    obtain ⟨k,fuelEq⟩ : ∃ k,fuel+1 = k+40 := ⟨fuel-39,by omega⟩
    unfold ApplyInternal at materialized
    rw [fuelEq] at materialized
    obtain ⟨frame,values⟩ := stock_div_imm_values hp ctx hc refines width extension materialized
    rw [u64_ofNat (u64_lt' _)] at values
    exact Or.inl ⟨j,info,defined,found,original,nonzero,frame,values⟩
  · exact Or.inr (Or.inl guarded)
  · exact Or.inr (Or.inr widened)
end Backend.Stock.Proof.ScalarDiv
