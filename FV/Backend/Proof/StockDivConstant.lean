import FV.Backend.Proof.StockDivConstantSource
import FV.Backend.Proof.StockDivImmFrame
import FV.Backend.Proof.StockDivRequests
namespace Backend.Stock.Proof.ScalarDiv
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
def SourceDivisorObserved (p : Program) (ctx : Ctx) (cfg : Config) (y e : Nat)
    (ty : Clif.Ty) (u : BitVec ty.width) (s s' : State × Array RuleId) (out : V) : Prop :=
  (∃ j info,ctx.defInst? y = some j ∧ ctx.insts[j]? = some info ∧
    info.clif = some (.iconst ty u) ∧ imm64OfIconst ty u ≠ 0 ∧
    s'.1 = {s.1 with base := s'.1.base} ∧ ∃ fuel trace,
      ApplyInternal p (Stock.sem ctx) cfg fuel 27 553 (immArgs ty.width e (u64 (imm64OfIconst ty u)))
        s out (s'.1,trace)) ∨
  (ty.width = 64 ∧ DemandAllowed ctx s.1 y ∧ ∃ ry,ctx.valueReg? y = some ry ∧ out = .reg ry ∧
    s'.1 = {s.1.mark y with base := s.1.base.emit (.trapIf (.zero ry .size64) .intDivz)}) ∨
  (ty.width ≤ 32 ∧ ∃ r middle,ScalarShift.MappedExtOut ctx y (e == 0) 32 [.int 32,.int 64] s.1 middle (.reg r) ∧
    out = .reg r ∧ s'.1 = {middle with base := middle.base.emit (.trapIf (.zero r .size32) .intDivz)})
/-- Actual successful divisor requests connect their literal path to the
original source constant through the original restricted DFG/getter. Register
paths retain their internally derived guarded mapping and full-state receipts. -/
theorem stock_div_divisor_source_observed {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {fr : Clif.Frame} (dfg : DFGCons ctx fr) {y e n : Nat}
    {ty : Clif.Ty} {u : BitVec ty.width} (get : fr.getAs y ty = .ok u)
    {cfg : Config} (hc : cfg.checkOverlap = false) (enough : 120 ≤ n)
    (width : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64) (extension : e = 0 ∨ e = 1)
    {s s' : State × Array RuleId} {out : V}
    (run : ApplyInternal p (Stock.sem ctx) cfg n 27 698 [.value y,.data 125 e [],.ty (.int ty.width)] s out s') :
    SourceDivisorObserved p ctx cfg y e ty u s s' out := by
  have observed := stock_div_divisor_observed hp ctx hc enough width extension run
  rcases observed with ⟨j,info,i,defined,found,data,nonzero,fuel,trace,materialized⟩ | guarded | widened
  · obtain ⟨original,equal⟩ := stock_div_constant_source_value inv dfg get defined found data
    subst i
    have frame := (stock_div_imm_observed hp ctx hc materialized).1
    exact Or.inl ⟨j,info,defined,found,original,nonzero,frame,fuel,trace,materialized⟩
  · exact Or.inr (Or.inl guarded)
  · exact Or.inr (Or.inr widened)
end Backend.Stock.Proof.ScalarDiv
