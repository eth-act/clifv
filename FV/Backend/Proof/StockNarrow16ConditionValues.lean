import FV.Backend.Proof.StockNarrowConditionValues
import FV.Backend.Proof.StockCmpNonzero16OriginalSelection
import FV.Backend.Proof.StockCmpNonzeroNarrowCalls
import FV.Backend.Proof.StockBranchFreshDefs

/-! Branches on a plain `i16` condition: source branch values (#140, CB-12b).

A `brif c` whose condition `c` has type `i16` selects `lower_brif` (3231) and `is_nonzero_cmp c`
(650) as a wide condition does when no rule looks through the definition of `c` (`PlainSource`).
`is_nonzero c` (651) then selects rule 4977 (`aarch64/inst.isle`): `put_in_reg_zext32 c` (556,
rules 3809 and 2991) emits `uxth t, w` into a fresh temporary `t`, and the condition is
`t != 0` at 32 bits. So `br_cond_result` (3240) appends `uxth t, w` and `cbnz t`
(`nonzero16_code`). The temporary is the one register that the emission allocates.

Unlike the `i8` case, the emission defines a register. Its definition is in the branch interval
(`narrow16_fresh_defs`), and every emission run of the terminator allocates exactly one register
(`narrow16_fixed`). So `branch_alias_outside` applies: the resolved registers of the available
values are outside the branch interval, and the guarded post-frame survives the branch
(`narrow16_branch_values_last`). -/

namespace Backend.Stock.Proof.ConditionalValues
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] Isle.Aarch64.program

/-- `uxth t, w`: the zero extension of the `i16` condition in register `key` into the temporary
`t`. -/
def uxth16 (t key : Nat) : MInst := .extend (.vreg t .int) (.vreg key .int) false 16 32

/-- The actual `i16` nonzero branch appends exactly `uxth16 t key` and `cbnz t`, where `t` is the
next register. -/
private theorem nonzero16_emission {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {c : Nat} (typed : ctx.valueType? c = some (.int 16))
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
    ∃ key,next.base = ((before.base.fresh .int).2.emit (uxth16 before.base.nextVreg key)).emit
      (.condBr yes no (.notZero (.vreg before.base.nextVreg .int) .size32)) := by
  obtain ⟨rhsTrace,rhs,_⟩ := ScalarCmp.stock_cmp_original_nonzero16_selected ctx inv (by omega) typed conditionRun
  obtain ⟨n,gas⟩ : ∃ n,conditionFuel = n+220 := ⟨conditionFuel-220,by omega⟩
  rw [gas] at rhs
  obtain ⟨fuel,value,enough,extension,output⟩ :=
    ScalarCmp.stock_cmp_nonzero_narrow_rhs_calls data_program ctx c (.int 16) n rhs
  obtain ⟨t,typedT,_,rx,mapped,form⟩ := ScalarShift.stock_zext32_out data_program rfl enough extension
  rw [typed] at typedT
  cases Option.some.inj typedT
  obtain ⟨key,rfl⟩ := inv.valueReg c rx mapped
  rcases form with ⟨pass,_,_⟩ | ⟨_,_,valueEq,middleEq⟩
  · simp at pass
  · have rawEq : raw = .data 123 1 [.reg (.vreg before.base.nextVreg .int),.data 93 0 []] := by
      rw [output,valueEq]
      rfl
    have shape : CondShape raw (fun _ => True) := .inr (.inl ⟨_,0,.size32,rawEq,rfl,trivial⟩)
    obtain ⟨base,descriptorEq⟩ := descriptor_shape rfl enoughConstruct shape constructRun
    have projected := BranchHelpers.stock_emit_side_effect_projects ctx {} rfl (emitFuel+1)
      [descriptor] constructed constructTrace
    have legacy : ApplyInternal program (Backend.sem ctx) {} emitFuel 13 242
        [descriptor] (constructed.base,constructTrace) out (next.base,final) := by
      unfold ApplyInternal at emitRun ⊢
      rw [emitRun] at projected
      exact projected.symm
    rw [base,descriptorEq,rawEq] at legacy
    dsimp only [brCondV] at legacy
    obtain ⟨inst,decodedInst,finish,_⟩ := emit_side_effect_inst_ok data_program rfl enoughEmit legacy
    rw [ofV_condBr_notZero (show OperandSize.ofIdx? 0 = some .size32 from rfl)] at decodedInst
    cases decodedInst
    dsimp only at finish
    have middleBase : middle.base = (before.base.fresh .int).2.emit (uxth16 before.base.nextVreg key) :=
      congrArg State.base middleEq
    rw [finish,middleBase]
    exact ⟨key,rfl⟩

/-- The actual `i16` nonzero branch is the fragment `[uxth16 t key, cbnz t]` with `t` the next
register, and it allocates exactly `t`. -/
theorem nonzero16_code {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {c : Nat} (typed : ctx.valueType? c = some (.int 16))
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
    ∃ key,Frag before.base next.base
        [uxth16 before.base.nextVreg key,.condBr yes no (.notZero (.vreg before.base.nextVreg .int) .size32)] ∧
      next.base.nextVreg = before.base.nextVreg+1 := by
  obtain ⟨key,finish⟩ := nonzero16_emission inv typed enoughCondition enoughConstruct enoughEmit
    conditionRun constructRun emitRun
  rw [finish]
  refine ⟨key,(Frag.fresh_emit _ ?_).append (Frag.emit_nodef _ rfl),rfl⟩
  intro d defined
  have defs : vdefs (uxth16 before.base.nextVreg key) = [before.base.nextVreg] := rfl
  rw [defs] at defined
  exact defined

end Backend.Stock.Proof.ConditionalValues

namespace Backend.Stock.Proof.ConditionalCalls
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64 ConditionalValues
open Backend.Stock.Proof.PlainBranch
set_option autoImplicit false
set_option Elab.async false

/-- The actual branch of a plain `i16` condition is the fragment `[uxth16 t key, cbnz t]` on the
packet's labels, with `t` the next register, and it allocates exactly `t`. -/
theorem Calls.narrow16_code {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {i : Nat} {labels : List Label}
    {before next : State} {out : V} (calls : Calls ctx i labels before out next)
    {c : Nat} (source : calls.source = .value c)
    (typed : ctx.valueType? c = some (.int 16)) (plain : PlainSource ctx c) :
    ∃ key,Frag before.base next.base
        [uxth16 before.base.nextVreg key,
          .condBr calls.yes calls.no (.notZero (.vreg before.base.nextVreg .int) .size32)] ∧
      next.base.nextVreg = before.base.nextVreg+1 := by
  have conditionRun := calls.conditionRun
  rw [source] at conditionRun
  rcases ScalarSelect.stock_original_select_condition_calls inv calls.conditionEnough conditionRun with
    ⟨helperFuel,helperTrace,enough,nonzero⟩ |
    ⟨cc,ty,a,b,origin,helperFuel,helperTrace,enough,comparison⟩
  · exact nonzero16_code inv typed (by omega) calls.constructEnough calls.emitEnough
      nonzero calls.constructRun calls.emitRun
  · exact False.elim (plain.2 cc ty a b origin)

/-- The call packet keeps the extent of the demand array. -/
theorem Calls.demand_size {ctx : Ctx} {i : Nat} {labels : List Label}
    {before next : State} {out : V} (calls : Calls ctx i labels before out next) :
    next.demand.size = before.demand.size :=
  (Extent.apply_demand_size calls.emitRun).trans
    ((Extent.apply_demand_size calls.constructRun).trans (Extent.apply_demand_size calls.conditionRun))

end Backend.Stock.Proof.ConditionalCalls

namespace Backend.Stock.Proof.ConditionalValues
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.PlainBranch Backend.Stock.Proof.ComparisonBranch
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

private theorem emission_origin {ctx : Ctx} {f : Clif.Function} {c : Nat}
    {yes no : Clif.BlockCall} {bi ti : Nat} {targets : Array Nat}
    {input : State} {emission : BranchEmission}
    (run : emitBranch ctx f (.brif c yes no) bi ti targets input = .ok emission) :
    ∃ out trace,Stock.runTerm ctx "lower_branch" [.inst ti,.labels targets.toList]
        {input with current := some ti,color := none,base.emitted := #[]} =
        .ok (some out,emission.state,trace) ∧
      emission.code = emission.state.base.emitted := by
  unfold emitBranch at run
  dsimp only at run
  cases call : Stock.runTerm ctx "lower_branch" [.inst ti,.labels targets.toList]
      {input with current := some ti,color := none,base.emitted := #[]} with
  | error message => simp only [call,bind,Except.bind] at run; cases run
  | ok q =>
    obtain ⟨out,next,trace⟩ := q
    simp only [call,bind,Except.bind] at run
    cases out with
    | none => simp at run
    | some out =>
      simp only [Option.isNone_some,Bool.false_eq_true,ite_false,branchCode,
        pure,Except.pure,bind,Except.bind] at run
      cases run
      exact ⟨out,trace,rfl,rfl⟩

/-- The actual terminator slot of the core of `spec` holds the `brif` data of the source. -/
theorem ConditionalBodySpec.terminator_slot {f : Clif.Function} {result : Result}
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (block : f.blocks[bi]? = some b) (termShape : b.term = .brif c yes no) :
    spec.core.scan.termInst = spec.ranges[bi]!.2-1 ∧
      spec.core.scan.ctx.insts[spec.ranges[bi]!.2-1]? =
        some ⟨.data 152 5 [.data 151 1 [],.value c,.blockCalls [0,1]],[],[],none⟩ := by
  have origin := stock_lowerBlockCore_scanOrigin spec.coreRun
  have ctxEq := origin.2.1
  have expected : Coverage.blockData f b.term =
      .ok (.data 152 5 [.data 151 1 [],.value c,.blockCalls [0,1]]) := by
    rw [termShape]
    with_unfolding_all rfl
  have dataEq := Except.ok.inj (spec.prepared.symm.trans expected)
  obtain ⟨original,st0,oldBuild,ctxSpec,view⟩ := buildCtx_source spec.build
  have range : spec.ranges[bi]! = (blockStart f bi,blockStart f bi+b.body.length+1) := by
    simp only [getElem!_def,ctxSpec.ranges bi b block]
  have placeholder : result.ctx.insts[blockStart f bi+b.body.length]? = some ⟨.op .unit,[],[],none⟩ := by
    rw [view.insts]
    exact ctxSpec.facts.term bi b block
  have bound : spec.ranges[bi]!.2-1 < result.ctx.insts.size := by
    have inside := (Array.getElem?_eq_some_iff.mp placeholder).1
    rw [range]
    dsimp only
    omega
  refine ⟨origin.2.2.2.1,?_⟩
  rw [ctxEq]
  change (result.ctx.insts.set! (spec.ranges[bi]!.2-1) ⟨spec.data,[],[],none⟩)[spec.ranges[bi]!.2-1]? = _
  simp only [dataEq,Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds_self_of_lt bound]

/-- **Every emission run of a branch on a plain `i16` condition allocates one register.** In the
actual context of the core, `lower_branch` at the terminator slot allocates exactly the
temporary of `uxth`, from any input and for any targets. -/
theorem ConditionalBodySpec.narrow16_fixed {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (block : f.blocks[bi]? = some b) (termShape : b.term = .brif c yes no)
    (plain : PlainSource result.ctx c) (narrow : result.ctx.valueType? c = some (.int 16)) :
    spec.FixedAllocation := by
  have inv := (stock_lower_record_context run scope spec.events).1
  have ctxEq := (stock_lowerBlockCore_scanOrigin spec.coreRun).2.1
  have plainHere := spec.plain_here plain
  have narrowHere : spec.core.scan.ctx.valueType? c = some (.int 16) := by rw [ctxEq]; exact narrow
  obtain ⟨slotInst,slot⟩ := spec.terminator_slot block termShape
  obtain ⟨calls,source⟩ := spec.plain_calls run scope block termShape plain
  obtain ⟨_,_,retained⟩ := calls.narrow16_code inv source narrowHere plainHere
  intro targets input emission emitted
  rw [slotInst] at emitted
  obtain ⟨out,trace,named,_⟩ := emission_origin emitted
  obtain ⟨other,otherSource⟩ := PlainBranch.plain_named_calls inv slot plainHere named
  obtain ⟨_,_,allocated⟩ := other.narrow16_code inv otherSource narrowHere plainHere
  change emission.state.base.nextVreg = input.base.nextVreg+1 at allocated
  change spec.origin.emission.state.base.nextVreg = spec.input.base.nextVreg+1 at retained
  omega

/-- The real emission of a branch on a plain `i16` condition is `[uxth16 t key, cbnz t]`, with `t`
the next register at the core input, and it allocates exactly `t`. -/
theorem ConditionalBodySpec.narrow16_code {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (block : f.blocks[bi]? = some b) (termShape : b.term = .brif c yes no)
    (plain : PlainSource result.ctx c) (narrow : result.ctx.valueType? c = some (.int 16)) :
    ∃ key yesLabel noLabel,spec.origin.emission.code.toList =
        [uxth16 spec.input.base.nextVreg key,
          .condBr yesLabel noLabel (.notZero (.vreg spec.input.base.nextVreg .int) .size32)] ∧
      (∀ m ∈ spec.origin.emission.code.toList,∀ d ∈ vdefs m,
        spec.input.base.nextVreg ≤ d ∧ d < spec.origin.emission.state.base.nextVreg) ∧
      spec.origin.emission.state.base.nextVreg = spec.input.base.nextVreg+1 := by
  have inv := (stock_lower_record_context run scope spec.events).1
  have ctxEq := (stock_lowerBlockCore_scanOrigin spec.coreRun).2.1
  have plainHere := spec.plain_here plain
  obtain ⟨calls,source⟩ := spec.plain_calls run scope block termShape plain
  obtain ⟨key,fragment,allocated⟩ := calls.narrow16_code inv source (by rw [ctxEq]; exact narrow) plainHere
  have actualCode : spec.origin.emission.code.toList =
      [uxth16 spec.input.base.nextVreg key,
        .condBr calls.yes calls.no (.notZero (.vreg spec.input.base.nextVreg .int) .size32)] := by
    rw [spec.origin.emitted]
    have buffers := congrArg Array.toList fragment.emitted
    simpa only [Array.toList_append,Array.toList_empty,List.toList_toArray,List.nil_append] using buffers
  refine ⟨key,calls.yes,calls.no,actualCode,?_,allocated⟩
  rw [actualCode]
  exact fragment.defs

/-- The definitions of the real emission of a branch on a plain `i16` condition are in its branch
interval. -/
theorem ConditionalBodySpec.narrow16_fresh_defs {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (block : f.blocks[bi]? = some b) (termShape : b.term = .brif c yes no)
    (plain : PlainSource result.ctx c) (narrow : result.ctx.valueType? c = some (.int 16)) :
    ∀ m ∈ spec.origin.emission.code.toList,∀ d ∈ vdefs m,
      spec.input.base.nextVreg ≤ d ∧ d < spec.origin.emission.state.base.nextVreg := by
  obtain ⟨key,yesLabel,noLabel,actualCode,fresh,allocated⟩ :=
    spec.narrow16_code run scope block termShape plain narrow
  exact fresh

/-- The real emission of a branch on a plain `i16` condition is exactly two instructions. -/
theorem ConditionalBodySpec.narrow16_emission_size {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (block : f.blocks[bi]? = some b) (termShape : b.term = .brif c yes no)
    (plain : PlainSource result.ctx c) (narrow : result.ctx.valueType? c = some (.int 16)) :
    spec.origin.emission.code.size = 2 := by
  obtain ⟨key,yesLabel,noLabel,actualCode,fresh,allocated⟩ :=
    spec.narrow16_code run scope block termShape plain narrow
  rw [← Array.length_toList,actualCode]
  rfl

/-- `narrow8_branch_values_last` for a plain `i16` condition: the actual retained `uxth` and
`cbnz` stop at the last instruction of their real buffer on the edge of the source truth, with
the guarded post-frame. The `uxth` writes only its temporary, which is outside the resolved
registers of the available values (`branch_alias_outside`). -/
theorem ConditionalBodySpec.narrow16_branch_values_last {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {MR : MemRelT} (stable : MRStable F MR) {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (block : f.blocks[bi]? = some b) (termShape : b.term = .brif c yes no)
    (plain : PlainSource result.ctx c) (narrow : result.ctx.valueType? c = some (.int 16))
    {fr : Clif.Frame} {cm : Clif.Mem} {cty : Clif.Ty} {test : BitVec cty.width}
    (getC : (restrict fr (availOf f (availIn f result.ctx) spec.core.scan.block b.body.length)).getAs c cty = .ok test)
    {ρ : Nat → CV} {world : Arm.ArmState}
    (post : GuardedScanRel f result spec.core.scan.ctx spec.core.scan.block MR spec.term.output.state
      (b.body.length,fr,cm) ρ world) :
    ∃ index inst ops regs prefixWorld endWorld,
      seqRun isem (spec.origin.emission.code.toList.map
        (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ world =
        some (.stop index inst ops regs prefixWorld [] endWorld (.goto (if test != 0 then 0 else 1))) ∧
      index+1 = spec.origin.emission.code.size ∧
      GuardedScanRel f result spec.core.scan.ctx spec.core.scan.block MR spec.term.output.state
        (b.body.length,fr,cm) regs endWorld ∧
      inst.targets = result.order.successors[label]!.toList ∧ inst.isTerminator = true := by
  have inv := (stock_lower_record_context run scope spec.events).1
  have ctxEq := (stock_lowerBlockCore_scanOrigin spec.coreRun).2.1
  have plainHere := spec.plain_here plain
  have narrowHere : spec.core.scan.ctx.valueType? c = some (.int 16) := by rw [ctxEq]; exact narrow
  have fixed := spec.narrow16_fixed run scope block termShape plain narrow
  obtain ⟨calls,source⟩ := spec.plain_calls run scope block termShape plain
  have available := restrict_regs_isSome (by rw [getAs_ok getC]; rfl)
  have typed := stock_lower_available_getAs_type run spec.events available post.2.1 getC
  obtain ⟨emission,afterEdges,retained,branchCall,outgoing,scanInput,scanCtx,branchScan,combined⟩ :=
    conditional_core_calls termShape spec.coreRun
  have same : emission = spec.origin.emission := Option.some.inj (retained.symm.trans spec.origin.retained)
  rw [same] at outgoing
  obtain ⟨edgeBase,edgeExtent⟩ := outgoing_base_extent outgoing
  have scanExtent : spec.core.scan.input.demand.size = spec.origin.emission.state.demand.size := by
    rw [scanInput]; exact edgeExtent
  have demandSize : spec.origin.emission.state.demand.size = spec.input.demand.size := calls.demand_size
  have termRecorded : spec.term ∈ spec.core.scan.output.records := by rw [spec.split.records]; simp
  have bounded : result.final.alias.size ≤ spec.input.base.nextVreg :=
    Nat.le_trans (stock_lower_allocationBounds run).1 (spec.branch_alias_outside run scope dominated termShape fixed).1
  have extent : ∀ value r,spec.core.scan.ctx.valueReg? value = some r → value < spec.input.demand.size := by
    intro value r mapped
    have actual := (Extent.lower_mapped_demand_bounds run scope spec.events termRecorded mapped).1
    rw [spec.split.termInput,scanExtent,demandSize] at actual
    exact actual
  have termDemand := (Control.stock_branch_scan_body_code spec.split spec.origin.branchScan).2
  have held : ValuesHeld (Demanded spec.origin.emission.state) spec.core.scan.ctx
      (restrict fr (availOf f (availIn f result.ctx) spec.core.scan.block b.body.length))
      (fun key => ρ (aliasNum result.final.alias key)) := by
    intro value needed val read
    have av := restrict_regs_isSome (by rw [read]; rfl)
    rw [restrict_regs_of_mem av] at read
    have mono := conditional_core_emission_demand termShape spec.coreRun spec.origin value
    have demanded : Demanded spec.term.output.state value := by
      unfold Demanded at needed ⊢
      rw [termDemand,spec.split.termInput]
      omega
    exact post.2.2.2 value ⟨demanded,av⟩ val read
  obtain ⟨yesLabel,noLabel,code,labels,fragment,execution⟩ := calls.plain_source_values inv source
    post.2.1 getC typed plainHere refines bounded extent held
  obtain ⟨key,otherFragment,_⟩ := calls.narrow16_code inv source narrowHere plainHere
  have buffers := congrArg Array.toList (fragment.emitted.symm.trans otherFragment.emitted)
  simp only [Array.toList_append] at buffers
  have sameCode := List.append_cancel_left buffers
  have actualCode : spec.origin.emission.code.toList = code := by
    rw [spec.origin.emitted]
    have emitted := congrArg Array.toList fragment.emitted
    simpa only [Array.toList_append,Array.toList_empty,List.toList_toArray,List.nil_append] using emitted
  obtain ⟨index,inst,ops,regs,prefixWorld,endWorld,machine,nf,outside,targets,terminal⟩ := execution world
  have machine' : seqRun isem (spec.origin.emission.code.toList.map
      (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ world =
      some (.stop index inst ops regs prefixWorld [] endWorld (.goto (if test != 0 then 0 else 1))) := by
    rw [actualCode]
    exact machine
  have count : spec.origin.emission.code.size = 2 := by
    rw [← Array.length_toList,actualCode,sameCode]
    rfl
  have stopIndex : index+1 = spec.origin.emission.code.size := by
    have member := (seqRun_stop_mem machine').1
    rw [count]
    rw [actualCode,sameCode] at member
    match index,member with
    | 0,first =>
      simp only [List.map_cons,List.getElem?_cons_zero,Option.some.injEq] at first
      have quiet : ((uxth16 spec.input.base.nextVreg key).mapRegs
          (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))).isTerminator = false := rfl
      rw [← first,quiet] at terminal
      cases terminal
    | 1,_ => rfl
    | n+2,beyond => simp at beyond
  refine ⟨index,inst,ops,regs,prefixWorld,endWorld,machine',stopIndex,?_,targets.trans labels.symm,terminal⟩
  exact spec.guarded_of_branch_frame run scope dominated stable termShape fixed post outside nf

end Backend.Stock.Proof.ConditionalValues
