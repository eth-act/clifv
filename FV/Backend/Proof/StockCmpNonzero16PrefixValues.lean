import FV.Backend.Proof.StockExtendValues
import FV.Backend.Proof.StockCmpNonzeroNarrowCalls
namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
/-- Actual narrow nonzero RHS execution establishes the original16-bit value's
zero-extension, including its real temporary-write fragment and outside frame.
The original restricted DFG and demanded-value relation remain required. -/
theorem stock_cmp_nonzero16_rhs_prefix_values {p : Program} (hp : Data p)
    {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {fr : Clif.Frame} (dfg : DFGCons ctx fr) {x : Nat} {u : BitVec 16}
    (get : fr.getAs x .i16 = .ok u) {n : Nat}
    {st next : State} {tr trace : Array RuleId} {out : V}
    (rhs : (evalExpr p (Stock.sem ctx) {} (n+220) rule_inst_4977.rhs
      #[some (.ty (.int 16)),some (.value x)]).run (st,tr) = .ok (some out,next,trace))
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ z r,ctx.valueReg? z = some r → z < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun key => ρ (aliasNum aliases key))) :
    ∃ value,out = .data 123 1 [value,.data 93 0 []] ∧
      ScalarShift.ExtValueOut F isem false 32 .i16 u st next value aliases ρ := by
  obtain ⟨fuel,value,enough,extension,output⟩ := stock_cmp_nonzero_narrow_rhs_calls hp ctx x (.int 16) n rhs
  exact ⟨value,output,ScalarShift.stock_ext_helper_values hp inv refines false false enough
    dfg get bounded extent held extension⟩
end Backend.Stock.Proof.ScalarCmp
