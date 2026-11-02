import FV.Backend.Proof.StockCmpWideActualValues
import FV.Backend.Proof.StockSelectComparisonConditionShape
import FV.Backend.Proof.StockSelectConditionCompanion
namespace Backend.Stock.Proof.ScalarSelect
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.ScalarCmp
/-- Actual scalar comparison selection constructs its boolean proof companion
and proves its original source predicate. No helper-success certificate or
materialized condition-value premise is required. Retained callers discharge
scratch separation from original availability. -/
theorem stock_select_comparison_companion_source_values {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {ty : Clif.Ty}
    (width : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64)
    (cc : Clif.IntCC) {fr : Clif.Frame} (dfg : DFGCons ctx fr) {x y fuel : Nat}
    {u v : BitVec ty.width} (getX : fr.getAs x ty = .ok u) (getY : fr.getAs y ty = .ok v)
    (typeX : ctx.valueType? x = some (.int ty.width))
    (typeY : ctx.valueType? y = some (.int ty.width)) (enough : 300 ≤ fuel)
    {st middle : State} {tr trace : Array RuleId} {raw : V}
    (emitter : ApplyInternal program (Stock.sem ctx) {} fuel 123 652
      [.data 145 (ccIdx cc) [],.value x,.value y] (st,tr) raw (middle,trace))
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ z r,ctx.valueReg? z = some r → z < st.demand.size)
    (held : ValuesHeld (Demanded middle) ctx fr (fun key => ρ (aliasNum aliases key)))
    (separatedY : ∀ r,ctx.valueReg? y = some (.vreg r .int) → aliasNum aliases r ≠ st.base.nextVreg) :
    ∃ producer condition booleanTrace,
      CondFlag cmpImm0 raw producer condition ∧ vdefs producer = [] ∧
      condition ≠ .al ∧ condition ≠ .nv ∧
      ApplyInternal program (Stock.sem ctx) {} 119 27 715 [raw] (middle,trace)
        (.reg (middle.base.fresh .int).1)
        ({middle with base := (((middle.base.fresh .int).2.emit producer).emit
          (.cset (middle.base.fresh .int).1 condition))},booleanTrace) ∧
      CmpExecution F isem aliases cc ty u v st
        {middle with base := (((middle.base.fresh .int).2.emit producer).emit
          (.cset (middle.base.fresh .int).1 condition))}
        (.reg (middle.base.fresh .int).1) ρ := by
  have shape := stock_select_comparison_condition_shape inv width cc typeX typeY enough emitter
  obtain ⟨producer,condition,booleanTrace,flags,noDefs,notAl,notNv,companion⟩ :=
    stock_select_condition_boolean_companion ctx shape middle trace
  refine ⟨producer,condition,booleanTrace,flags,noDefs,notAl,notNv,companion,?_⟩
  cases ty
  · exact stock_cmp_narrow_actual_emitter_values inv false cc rfl dfg getX getY typeX typeY
      enough (by decide) emitter companion refines bounded extent held separatedY
  · exact stock_cmp_narrow_actual_emitter_values inv true cc rfl dfg getX getY typeX typeY
      enough (by decide) emitter companion refines bounded extent held separatedY
  · exact stock_cmp_wide_actual_emitter_values inv false cc rfl dfg getX getY typeX typeY
      enough (by decide) emitter companion refines bounded extent held
  · exact stock_cmp_wide_actual_emitter_values inv true cc rfl dfg getX getY typeX typeY
      enough (by decide) emitter companion refines bounded extent held
  · simp [Clif.Ty.width] at width
  all_goals cases getAs_typed dfg typeX getX
end Backend.Stock.Proof.ScalarSelect
