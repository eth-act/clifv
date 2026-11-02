import FV.Backend.Proof.StockCmpWideActualValues
import FV.Backend.Proof.StockSelectComparisonConditionShape
import FV.Backend.Proof.StockSelectConditionCompanion
import FV.Backend.Proof.StockSelectConditionOriginValues

namespace Backend.Stock.Proof.ConditionalValues
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open ScalarCmp ScalarSelect
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- Execution of an internally constructed boolean proof companion. Its source
predicate is known, without materializing that source condition in real code. -/
def BooleanExecution (F : BitVec 64 → Prop) (isem : Backend.Proof.Sem)
    (aliases : Array (Option Nat)) (truth : Bool) (before next : State) (out : V) (ρ : Nat → CV) : Prop :=
  ∃ d code,out = .reg (.vreg d .int) ∧ before.base.nextVreg ≤ d ∧ d < next.base.nextVreg ∧
    Frag before.base next.base code ∧
    ∀ world,Runs F isem (code.map (·.mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world (fun final _ =>
        VHolds ⟨.i8,Clif.Sem.bool8 truth⟩ (final d) ∧
        ∀ k,k < before.base.nextVreg ∨ next.base.nextVreg ≤ k → final k = ρ k)

/-- Reuse every already-proved original scalar nonzero condition, including
8-bit masking and the real16-bit scratch extension, for a boolean companion.
Widths are internal cases, and final aliases and demanded source values are
handled by the existing source theorems. -/
theorem nonzero_boolean_values {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {cty : Clif.Ty}
    (width : cty.width = 8 ∨ cty.width = 16 ∨ cty.width = 32 ∨ cty.width = 64)
    {fr : Clif.Frame} (dfg : DFGCons ctx fr) {c : Nat} {test : BitVec cty.width}
    (getC : fr.getAs c cty = .ok test) (typed : ctx.valueType? c = some (.int cty.width))
    {emitFuel conditionFuel : Nat} (enoughEmit : 220 ≤ emitFuel) (enoughCondition : 119 ≤ conditionFuel)
    {before middle next : State} {trace emitTrace conditionStart final : Array RuleId} {raw out : V}
    (emitter : ApplyInternal program (Stock.sem ctx) {} emitFuel 123 651 [.value c]
      (before,trace) raw (middle,emitTrace))
    (consumer : ApplyInternal program (Stock.sem ctx) {} conditionFuel 27 715 [raw]
      (middle,conditionStart) out (next,final))
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} (bounded : aliases.size ≤ before.base.nextVreg)
    (extent : ∀ value r,ctx.valueReg? value = some r → value < before.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun key => ρ (aliasNum aliases key))) :
    BooleanExecution F isem aliases (test != 0) before next out ρ := by
  unfold BooleanExecution
  cases cty
  case i8 =>
    obtain ⟨rhsTrace,rhs,_⟩ := stock_cmp_original_nonzero8_selected ctx inv (by omega) typed emitter
    obtain ⟨n,gas⟩ : ∃ n,emitFuel=n+100 := ⟨emitFuel-100,by omega⟩
    rw [gas] at rhs
    obtain ⟨key,d,_,output,lower,upper,fragment,execution⟩ := stock_cmp_nonzero8_rhs_source_values
      data_program inv getC typed enoughCondition rhs consumer refines bounded extent held
    refine ⟨d,_,output,lower,upper,fragment,fun world => (execution world).imp ?_⟩
    intro final _ _ pair
    exact ⟨pair.1,fun k outside => pair.2 k (by rcases outside with h | h <;> omega)⟩
  case i16 =>
    obtain ⟨rhsTrace,rhs,_⟩ := stock_cmp_original_nonzero16_selected ctx inv (by omega) typed emitter
    obtain ⟨n,gas⟩ : ∃ n,emitFuel=n+220 := ⟨emitFuel-220,by omega⟩
    rw [gas] at rhs
    obtain ⟨code,key,d,output,lower,upper,fragment,execution⟩ := stock_cmp_nonzero16_rhs_source_values
      data_program inv dfg getC enoughCondition rhs consumer refines bounded extent held
    exact ⟨d,_,output,lower,upper,fragment,execution⟩
  case i32 =>
    obtain ⟨key,d,_,output,lower,upper,fragment,execution⟩ := stock_cmp_original_nonzero32_values
      inv getC typed enoughEmit enoughCondition emitter consumer refines bounded extent held
    refine ⟨d,_,output,lower,upper,fragment,fun world => (execution world).imp ?_⟩
    intro final _ _ pair
    exact ⟨pair.1,fun k outside => pair.2 k (by rcases outside with h | h <;> omega)⟩
  case i64 =>
    obtain ⟨key,d,_,output,lower,upper,fragment,execution⟩ := stock_cmp_original_nonzero64_values
      inv getC typed (by omega) enoughCondition emitter consumer refines bounded extent held
    refine ⟨d,_,output,lower,upper,fragment,fun world => (execution world).imp ?_⟩
    intro final _ _ pair
    exact ⟨pair.1,fun k outside => pair.2 k (by rcases outside with h | h <;> omega)⟩
  case i128 => simp [Clif.Ty.width] at width
  case f32 | f64 => cases getAs_typed dfg typed getC


/-- Actual original650 constructs its boolean proof companion and establishes
original source truth, including direct/zero-extended comparison look-through.
No supplied flag/condition-value certificate or materialized comparison result
is required. Retained source availability will discharge scratch separation. -/
theorem original_boolean_companion {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {cty : Clif.Ty} {fr : Clif.Frame} (dfg : DFGCons ctx fr)
    {c : Nat} {test : BitVec cty.width} (getC : fr.getAs c cty = .ok test)
    (typedReads : ∀ {value : Nat} {ty : Clif.Ty} {bits : BitVec ty.width},
      fr.getAs value ty = .ok bits → ctx.valueType? value = some (.int ty.width))
    {fuel : Nat} (enough : 400 ≤ fuel) {before middle : State}
    {trace emitTrace : Array RuleId} {raw : V}
    (emitter : ApplyInternal program (Stock.sem ctx) {} fuel 123 650 [.value c]
      (before,trace) raw (middle,emitTrace))
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} (bounded : aliases.size ≤ before.base.nextVreg)
    (extent : ∀ value r,ctx.valueReg? value = some r → value < before.demand.size)
    (held : ValuesHeld (Demanded middle) ctx fr (fun key => ρ (aliasNum aliases key)))
    (separatedReads : ∀ {value : Nat} {ty : Clif.Ty} {bits : BitVec ty.width},
      fr.getAs value ty = .ok bits → ∀ key,ctx.valueReg? value = some (.vreg key .int) →
        aliasNum aliases key ≠ before.base.nextVreg) :
    ∃ producer condition booleanTrace,
      CondShape raw (fun _ => True) ∧ CondFlag cmpImm0 raw producer condition ∧
      vdefs producer = [] ∧ condition ≠ .al ∧ condition ≠ .nv ∧
      ApplyInternal program (Stock.sem ctx) {} 119 27 715 [raw] (middle,emitTrace)
        (.reg (middle.base.fresh .int).1)
        ({middle with base := (((middle.base.fresh .int).2.emit producer).emit
          (.cset (middle.base.fresh .int).1 condition))},booleanTrace) ∧
      BooleanExecution F isem aliases (test != 0) before
        {middle with base := (((middle.base.fresh .int).2.emit producer).emit
          (.cset (middle.base.fresh .int).1 condition))}
        (.reg (middle.base.fresh .int).1) ρ := by
  have supported : ∀ {value : Nat} {ty : Clif.Ty} {bits : BitVec ty.width},
      fr.getAs value ty = .ok bits →
      ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64 := by
    intro value ty bits read
    have type := typedReads read
    have valid := inv.valTyE value (.int ty.width) type
    cases ty <;> simp [eCTys,Clif.Ty.width] at valid ⊢
  rcases stock_original_select_condition_calls inv enough emitter with
    ⟨helperFuel,helperTrace,enoughHelper,nonzero⟩ |
    ⟨cc,ty,a,b,origin,helperFuel,helperTrace,enoughHelper,comparison⟩
  · have shape := stock_select_nonzero_actual_condition_shape inv (supported getC) (by omega) (typedReads getC) nonzero
    obtain ⟨producer,condition,booleanTrace,flags,noDefs,notAl,notNv,companion⟩ :=
      stock_select_condition_boolean_companion ctx shape middle emitTrace
    have execution := nonzero_boolean_values inv (supported getC) dfg getC (typedReads getC)
      (by omega) (by decide) nonzero companion refines bounded extent held
    exact ⟨producer,condition,booleanTrace,shape,flags,noDefs,notAl,notNv,companion,execution⟩
  · obtain ⟨av,bv,getA,getB,truth⟩ := stock_select_comparison_origin_values dfg origin (getAs_ok getC)
    have shape := stock_select_comparison_condition_shape inv (supported getA) cc
      (typedReads getA) (typedReads getB) enoughHelper comparison
    obtain ⟨producer,condition,booleanTrace,flags,noDefs,notAl,notNv,companion⟩ :=
      stock_select_condition_boolean_companion ctx shape middle emitTrace
    have execution : ScalarCmp.CmpExecution F isem aliases cc ty av bv before
        {middle with base := (((middle.base.fresh .int).2.emit producer).emit
          (.cset (middle.base.fresh .int).1 condition))}
        (.reg (middle.base.fresh .int).1) ρ := by
      cases ty
      · exact stock_cmp_narrow_actual_emitter_values inv false cc rfl dfg getA getB
          (typedReads getA) (typedReads getB) enoughHelper (by decide) comparison companion
          refines bounded extent held (separatedReads getB)
      · exact stock_cmp_narrow_actual_emitter_values inv true cc rfl dfg getA getB
          (typedReads getA) (typedReads getB) enoughHelper (by decide) comparison companion
          refines bounded extent held (separatedReads getB)
      · exact stock_cmp_wide_actual_emitter_values inv false cc rfl dfg getA getB
          (typedReads getA) (typedReads getB) enoughHelper (by decide) comparison companion
          refines bounded extent held
      · exact stock_cmp_wide_actual_emitter_values inv true cc rfl dfg getA getB
          (typedReads getA) (typedReads getB) enoughHelper (by decide) comparison companion
          refines bounded extent held
      · have impossible := supported getA
        simp [Clif.Ty.width] at impossible
      all_goals cases getAs_typed dfg (typedReads getA) getA
    refine ⟨producer,condition,booleanTrace,shape,flags,noDefs,notAl,notNv,companion,?_⟩
    change (test != 0) = Clif.Sem.intcc cc av bv at truth
    rw [truth]
    exact execution

end Backend.Stock.Proof.ConditionalValues
