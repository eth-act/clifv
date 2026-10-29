module

public import FV.Backend.Proof.StockConditionalCallValues
public import FV.Backend.Proof.StockSelectNonzeroWideShape

@[expose] public section

namespace Backend.Stock.Proof.ConditionalValues
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

private theorem branch_no_defs {yes no : Label} {raw : V} {code : List MInst}
    (compiled : BranchCode yes no raw code) : ∀ inst ∈ code,vdefs inst = [] := by
  cases compiled with
  | zero key index size decoded | nonzero key index size decoded =>
    intro inst member
    simp only [List.mem_singleton] at member
    subst inst
    rfl
  | flags raw producer condition decoded notAl notNv noDefs =>
    intro inst member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact noDefs
    · rfl

/-- Actual wide scalar nonzero lowering has no real scratch prefix and its
entire branch fragment defines no virtual registers. Alias endpoints and held
source values therefore need no allocation-interval side condition. -/
theorem nonzero_wide_no_defs {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) (wide : Bool) {c : Nat}
    (typed : ctx.valueType? c = some (.int (if wide then 64 else 32)))
    {conditionFuel constructFuel emitFuel : Nat}
    (enoughCondition : 220 ≤ conditionFuel) (enoughConstruct : 100 ≤ constructFuel) (enoughEmit : 30 ≤ emitFuel)
    {before middle constructed next : State} {trace helperTrace conditionTrace constructTrace final : Array RuleId}
    {raw descriptor out : V} {yes no : Label}
    (conditionRun : ApplyInternal program (Stock.sem ctx) {} conditionFuel 123 651 [.value c]
      (before,trace) raw (middle,helperTrace))
    (constructRun : ApplyInternal program (Stock.sem ctx) {} constructFuel 46 722
      [raw,.label yes,.label no] (middle,conditionTrace) descriptor (constructed,constructTrace))
    (emitRun : ApplyInternal program (Stock.sem ctx) {} emitFuel 13 242
      [descriptor] (constructed,constructTrace) out (next,final)) :
    ∃ code,Frag before.base next.base code ∧ ∀ inst ∈ code,vdefs inst = [] := by
  obtain ⟨allowed,key,mapped,rawEq,finish⟩ :=
    ScalarSelect.stock_select_nonzero_wide_emitter_observed inv wide enoughCondition typed conditionRun
  let size : OperandSize := if wide then .size64 else .size32
  have decoded : OperandSize.ofIdx? (if wide then 1 else 0) = some size := by cases wide <;> rfl
  have shape : CondShape raw (fun _ => True) := .inr (.inl ⟨key,_,size,rawEq,decoded,trivial⟩)
  obtain ⟨code,compiled,fragment⟩ := descriptor_emits rfl enoughConstruct enoughEmit shape constructRun emitRun
  have initial : Frag before.base middle.base [] := by rw [finish]; exact Frag.nil _
  exact ⟨code,by simpa only [List.nil_append] using initial.append fragment,branch_no_defs compiled⟩

end Backend.Stock.Proof.ConditionalValues

namespace Backend.Stock.Proof.ConditionalCalls
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64 ConditionalValues
set_option autoImplicit false
set_option Elab.async false

/-- The selected actual parameter-branch calls derive a complete no-definition
fragment. Original source provenance and parameter typing identify this class;
no emitted-code or scratch-separation certificate is required. -/
theorem Calls.parameter_wide_no_defs {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {i : Nat} {labels : List Label}
    {before next : State} {out : V} (calls : Calls ctx i labels before out next)
    {c : Nat} (source : calls.source = .value c) (wide : Bool)
    (typed : ctx.valueType? c = some (.int (if wide then 64 else 32)))
    (parameter : ctx.defInst? c = none) :
    ∃ code,Frag before.base next.base code ∧ ∀ inst ∈ code,vdefs inst = [] := by
  have conditionRun := calls.conditionRun
  rw [source] at conditionRun
  rcases ScalarSelect.stock_original_select_condition_calls inv calls.conditionEnough conditionRun with
    ⟨helperFuel,helperTrace,enough,nonzero⟩ |
    ⟨cc,ty,a,b,origin,helperFuel,helperTrace,enough,comparison⟩
  · exact nonzero_wide_no_defs inv wide typed (by omega) calls.constructEnough calls.emitEnough
      nonzero calls.constructRun calls.emitRun
  · simp [ScalarSelect.SelectComparisonOrigin,Ctx.defClif?,parameter] at origin

/-- Wide original parameter branches combine source truth, real fragment and
no virtual definitions. The later stopped-run frame therefore preserves every
held value under the actual final resolver, without interval side conditions. -/
theorem Calls.parameter_wide_source_values {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {i : Nat} {labels : List Label}
    {before next : State} {out : V} (calls : Calls ctx i labels before out next)
    {c : Nat} (source : calls.source = .value c)
    {cty : Clif.Ty} {fr : Clif.Frame} (dfg : DFGCons ctx fr)
    {test : BitVec cty.width} (getC : fr.getAs c cty = .ok test)
    (width : cty.width = 32 ∨ cty.width = 64)
    (typed : ctx.valueType? c = some (.int cty.width)) (parameter : ctx.defInst? c = none)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} (bounded : aliases.size ≤ before.base.nextVreg)
    (extent : ∀ value r,ctx.valueReg? value = some r → value < before.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun key => ρ (aliasNum aliases key))) :
    ∃ yes no code,labels = [yes,no] ∧ Frag before.base next.base code ∧
      (∀ inst ∈ code,vdefs inst = []) ∧
      ∀ world,BranchExecution F isem yes no (code.map
        (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1))))
        (test != 0) before.base next.base ρ world := by
  obtain ⟨yes,no,code,labelsEq,fragment,execution⟩ := calls.parameter_source_values inv source
    dfg getC typed parameter refines bounded extent held
  have noDefs : ∃ other,Frag before.base next.base other ∧ ∀ inst ∈ other,vdefs inst = [] := by
    rcases width with narrow | wide
    · exact calls.parameter_wide_no_defs inv source false (by simpa [narrow] using typed) parameter
    · exact calls.parameter_wide_no_defs inv source true (by simpa [wide] using typed) parameter
  obtain ⟨other,otherFragment,noDefs⟩ := noDefs
  have buffers := congrArg Array.toList (fragment.emitted.symm.trans otherFragment.emitted)
  simp only [Array.toList_append,List.toList_toArray] at buffers
  have same : code = other := List.append_cancel_left buffers
  rw [← same] at noDefs
  exact ⟨yes,no,code,labelsEq,fragment,noDefs,execution⟩

end Backend.Stock.Proof.ConditionalCalls
