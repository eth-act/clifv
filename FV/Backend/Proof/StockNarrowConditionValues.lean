import FV.Backend.Proof.StockPlainConditionValues
import FV.Backend.Proof.StockConditionalWideAllocation
import FV.Backend.Proof.StockConditionalNoDefs

/-! Branches on a plain `i8` condition: source branch values (#140, CB-12).

A `brif c` whose condition `c` has type `i8` selects `lower_brif` (3231) and `is_nonzero_cmp c`
(650) as a wide condition does when no rule looks through the definition of `c` (`PlainSource`).
`is_nonzero c` (651) then selects rule 4988 (`aarch64/inst.isle`): the flag producer
`tst w, #0xff` (`ands wzr, w, #255`) and `Cond.ne`. The overflow-flag rules 4993-5094 are
unreachable in the source subset (`stock_overflow_flags_rule_unreachable`). So `br_cond_result`
(3240) appends two instructions: the `tst` and a `b.ne`. Neither defines a virtual register and
neither allocates one (`nonzero8_no_defs`, `nonzero8_allocation`, `nonzero8_emitted_size`).

The source branch values of a plain condition (`plain_source_branch_values`) hold for every
scalar width. With the three facts above, the plain-condition proofs carry over with a
two-instruction emission in place of the one `cbnz`: `narrow8_branch_values_last`,
`narrow8_emission_size` and `narrow8_branch_no_defs`. -/

namespace Backend.Stock.Proof.ConditionalValues
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] Isle.Aarch64.program

/-- The `tst w, #0xff` flag producer of an `i8` condition in register `key`. -/
def tst8 (key : Nat) : MInst := .aluRRImmLogic .andS .size32 .xzr (.vreg key .int) ⟨255,.size32⟩

/-- The actual `i8` nonzero helper keeps the compiler base state and returns the `tst` flag
producer with `Cond.ne`. -/
private theorem nonzero8_observed {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {c : Nat} (typed : ctx.valueType? c = some (.int 8))
    {conditionFuel : Nat} (enoughCondition : 220 ≤ conditionFuel)
    {before middle : State} {trace helperTrace : Array RuleId} {raw : V}
    (conditionRun : ApplyInternal program (Stock.sem ctx) {} conditionFuel 123 651 [.value c]
      (before,trace) raw (middle,helperTrace)) :
    middle.base = before.base ∧ ∃ key,
      raw = .data 123 2 [.data 47 1 [.data 58 5 [.data 59 5 [],.data 93 0 [],.reg .xzr,
        .reg (.vreg key .int),.op (.immLogic ⟨255,.size32⟩)]],.data 96 1 []] := by
  obtain ⟨_,rhs,_⟩ := ScalarCmp.stock_cmp_original_nonzero8_selected ctx inv (by omega) typed conditionRun
  obtain ⟨n,gas⟩ : ∃ n,conditionFuel = n+100 := ⟨conditionFuel-100,by omega⟩
  rw [gas] at rhs
  obtain ⟨_,rx,mapped,rawEq,middleEq⟩ := ScalarCmp.stock_cmp_nonzero8_rhs_observed data_program ctx rfl rhs
  obtain ⟨key,rfl⟩ := inv.valueReg c rx mapped
  exact ⟨by rw [middleEq]; rfl,key,rawEq⟩

/-- The actual `i8` nonzero branch appends exactly `tst8 key` and `b.ne`. -/
private theorem nonzero8_emission {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {c : Nat} (typed : ctx.valueType? c = some (.int 8))
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
    ∃ key,next.base = (before.base.emit (tst8 key)).emit (.condBr yes no (.cond .ne)) := by
  obtain ⟨middleBase,key,rawEq⟩ := nonzero8_observed inv typed enoughCondition conditionRun
  have shape : CondShape raw (fun _ => True) := by
    rw [rawEq]
    exact Or.inr (Or.inr ⟨_,_,Cond.ne,rfl,ofV_tst .xzr (.vreg key .int) ⟨255,.size32⟩,
      by decide,by decide,rfl,fun _ _ => trivial⟩)
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
  obtain ⟨first,last,finish,decodedFirst,decodedLast⟩ := emit_side_effect_inst2_ok data_program rfl enoughEmit legacy
  rw [ofV_tst] at decodedFirst
  cases decodedFirst
  have branch : MInst.ofV (.data 58 118 [.label yes,.label no,.data 83 2 [.data 96 1 []]]) =
      some (.condBr yes no (.cond .ne)) := ofV_condBr_cond yes no .ne
  rw [branch] at decodedLast
  cases decodedLast
  dsimp only at finish
  rw [middleBase] at finish
  exact ⟨key,finish⟩

/-- The actual `i8` nonzero branch is the fragment `[tst8 key, b.ne]`. -/
theorem nonzero8_code {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {c : Nat} (typed : ctx.valueType? c = some (.int 8))
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
    ∃ key,Frag before.base next.base [tst8 key,.condBr yes no (.cond .ne)] := by
  obtain ⟨key,finish⟩ := nonzero8_emission inv typed enoughCondition enoughConstruct enoughEmit
    conditionRun constructRun emitRun
  rw [finish]
  exact ⟨key,(Frag.emit_nodef _ rfl).append (Frag.emit_nodef _ rfl)⟩

/-- The actual `i8` nonzero branch fragment defines no virtual registers. -/
theorem nonzero8_no_defs {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {c : Nat} (typed : ctx.valueType? c = some (.int 8))
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
  obtain ⟨key,fragment⟩ := nonzero8_code inv typed enoughCondition enoughConstruct enoughEmit
    conditionRun constructRun emitRun
  refine ⟨_,fragment,?_⟩
  intro inst member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl <;> rfl

/-- The actual `i8` nonzero helpers allocate no virtual registers. -/
theorem nonzero8_allocation {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {c : Nat} (typed : ctx.valueType? c = some (.int 8))
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
    next.base.nextVreg = before.base.nextVreg := by
  obtain ⟨key,finish⟩ := nonzero8_emission inv typed enoughCondition enoughConstruct enoughEmit
    conditionRun constructRun emitRun
  rw [finish]
  rfl

/-- The real `i8` branch emitter appends exactly two instructions. -/
theorem nonzero8_emitted_size {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {c : Nat} (typed : ctx.valueType? c = some (.int 8))
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
    next.base.emitted.size = before.base.emitted.size+2 := by
  obtain ⟨key,finish⟩ := nonzero8_emission inv typed enoughCondition enoughConstruct enoughEmit
    conditionRun constructRun emitRun
  rw [finish]
  simp only [LState.emit,Array.size_push]

end Backend.Stock.Proof.ConditionalValues

namespace Backend.Stock.Proof.ConditionalCalls
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64 ConditionalValues
open Backend.Stock.Proof.PlainBranch
set_option autoImplicit false
set_option Elab.async false

/-- `Calls.plain_wide_no_defs` for a plain `i8` condition. -/
theorem Calls.narrow8_no_defs {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {i : Nat} {labels : List Label}
    {before next : State} {out : V} (calls : Calls ctx i labels before out next)
    {c : Nat} (source : calls.source = .value c)
    (typed : ctx.valueType? c = some (.int 8)) (plain : PlainSource ctx c) :
    ∃ code,Frag before.base next.base code ∧ ∀ inst ∈ code,vdefs inst = [] := by
  have conditionRun := calls.conditionRun
  rw [source] at conditionRun
  rcases ScalarSelect.stock_original_select_condition_calls inv calls.conditionEnough conditionRun with
    ⟨helperFuel,helperTrace,enough,nonzero⟩ |
    ⟨cc,ty,a,b,origin,helperFuel,helperTrace,enough,comparison⟩
  · exact nonzero8_no_defs inv typed (by omega) calls.constructEnough calls.emitEnough
      nonzero calls.constructRun calls.emitRun
  · exact False.elim (plain.2 cc ty a b origin)

/-- The actual branch of a plain `i8` condition is the fragment `[tst8 key, b.ne]` on the
packet's labels. -/
theorem Calls.narrow8_code {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {i : Nat} {labels : List Label}
    {before next : State} {out : V} (calls : Calls ctx i labels before out next)
    {c : Nat} (source : calls.source = .value c)
    (typed : ctx.valueType? c = some (.int 8)) (plain : PlainSource ctx c) :
    ∃ key,Frag before.base next.base [tst8 key,.condBr calls.yes calls.no (.cond .ne)] := by
  have conditionRun := calls.conditionRun
  rw [source] at conditionRun
  rcases ScalarSelect.stock_original_select_condition_calls inv calls.conditionEnough conditionRun with
    ⟨helperFuel,helperTrace,enough,nonzero⟩ |
    ⟨cc,ty,a,b,origin,helperFuel,helperTrace,enough,comparison⟩
  · exact nonzero8_code inv typed (by omega) calls.constructEnough calls.emitEnough
      nonzero calls.constructRun calls.emitRun
  · exact False.elim (plain.2 cc ty a b origin)

/-- `Calls.plain_wide_bounds` for a plain `i8` condition. -/
theorem Calls.narrow8_bounds {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {i : Nat} {labels : List Label}
    {before next : State} {out : V} (calls : Calls ctx i labels before out next)
    {c : Nat} (source : calls.source = .value c)
    (typed : ctx.valueType? c = some (.int 8)) (plain : PlainSource ctx c) :
    next.base.nextVreg = before.base.nextVreg ∧ next.demand.size = before.demand.size := by
  have size := (Extent.apply_demand_size calls.emitRun).trans
    ((Extent.apply_demand_size calls.constructRun).trans (Extent.apply_demand_size calls.conditionRun))
  have conditionRun := calls.conditionRun
  rw [source] at conditionRun
  rcases ScalarSelect.stock_original_select_condition_calls inv calls.conditionEnough conditionRun with
    ⟨helperFuel,helperTrace,enough,nonzero⟩ |
    ⟨cc,ty,a,b,origin,helperFuel,helperTrace,enough,comparison⟩
  · exact ⟨nonzero8_allocation inv typed (by omega) calls.constructEnough calls.emitEnough
      nonzero calls.constructRun calls.emitRun,size⟩
  · exact False.elim (plain.2 cc ty a b origin)

/-- `Calls.plain_wide_emitted_size` for a plain `i8` condition: two instructions. -/
theorem Calls.narrow8_emitted_size {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {i : Nat} {labels : List Label}
    {before next : State} {out : V} (calls : Calls ctx i labels before out next)
    {c : Nat} (source : calls.source = .value c)
    (typed : ctx.valueType? c = some (.int 8)) (plain : PlainSource ctx c) :
    next.base.emitted.size = before.base.emitted.size+2 := by
  have conditionRun := calls.conditionRun
  rw [source] at conditionRun
  rcases ScalarSelect.stock_original_select_condition_calls inv calls.conditionEnough conditionRun with
    ⟨helperFuel,helperTrace,enough,nonzero⟩ |
    ⟨cc,ty,a,b,origin,helperFuel,helperTrace,enough,comparison⟩
  · exact nonzero8_emitted_size inv typed (by omega) calls.constructEnough calls.emitEnough
      nonzero calls.constructRun calls.emitRun
  · exact False.elim (plain.2 cc ty a b origin)

/-- `Calls.plain_wide_source_values` for a plain `i8` condition: source truth on the real
fragment `[tst8 key, b.ne]`. -/
theorem Calls.narrow8_source_values {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {i : Nat} {labels : List Label}
    {before next : State} {out : V} (calls : Calls ctx i labels before out next)
    {c : Nat} (source : calls.source = .value c)
    {cty : Clif.Ty} {fr : Clif.Frame} (dfg : DFGCons ctx fr)
    {test : BitVec cty.width} (getC : fr.getAs c cty = .ok test)
    (typed : ctx.valueType? c = some (.int cty.width)) (narrow : cty.width = 8)
    (plain : PlainSource ctx c)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} (bounded : aliases.size ≤ before.base.nextVreg)
    (extent : ∀ value r,ctx.valueReg? value = some r → value < before.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun key => ρ (aliasNum aliases key))) :
    ∃ yes no key,labels = [yes,no] ∧
      Frag before.base next.base [tst8 key,.condBr yes no (.cond .ne)] ∧
      ∀ world,BranchExecution F isem yes no ([tst8 key,.condBr yes no (.cond .ne)].map
        (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1))))
        (test != 0) before.base next.base ρ world := by
  obtain ⟨yes,no,code,labelsEq,fragment,execution⟩ := calls.plain_source_values inv source
    dfg getC typed plain refines bounded extent held
  obtain ⟨key,otherFragment⟩ := calls.narrow8_code inv source (by simpa [narrow] using typed) plain
  have buffers := congrArg Array.toList (fragment.emitted.symm.trans otherFragment.emitted)
  simp only [Array.toList_append] at buffers
  have same := List.append_cancel_left buffers
  subst same
  have pair := labelsEq.symm.trans calls.labels_eq
  simp only [List.cons.injEq,and_true] at pair
  obtain ⟨rfl,rfl⟩ := pair
  exact ⟨_,_,key,labelsEq,otherFragment,execution⟩

end Backend.Stock.Proof.ConditionalCalls

namespace Backend.Stock.Proof.ConditionalValues
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.PlainBranch Backend.Stock.Proof.ComparisonBranch
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- `plain_branch_values_last` for a plain `i8` condition: the actual retained `tst` and `b.ne`
stop at the last instruction of their real buffer on the edge of the source truth, with the
guarded post-frame. -/
theorem ConditionalBodySpec.narrow8_branch_values_last {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {MR : MemRelT} (stable : MRStable F MR) {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (block : f.blocks[bi]? = some b) (termShape : b.term = .brif c yes no)
    (plain : PlainSource result.ctx c) (narrow : result.ctx.valueType? c = some (.int 8))
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
  have narrowHere : spec.core.scan.ctx.valueType? c = some (.int 8) := by rw [ctxEq]; exact narrow
  obtain ⟨calls,source⟩ := spec.plain_calls run scope block termShape plain
  have available := restrict_regs_isSome (by rw [getAs_ok getC]; rfl)
  have typed := stock_lower_available_getAs_type run spec.events available post.2.1 getC
  have width : cty.width = 8 := by
    rw [narrowHere] at typed
    exact (CTy.int.inj (Option.some.inj typed)).symm
  obtain ⟨emission,afterEdges,retained,branchCall,outgoing,scanInput,scanCtx,branchScan,combined⟩ :=
    conditional_core_calls termShape spec.coreRun
  have same : emission = spec.origin.emission := Option.some.inj (retained.symm.trans spec.origin.retained)
  rw [same] at outgoing
  obtain ⟨edgeBase,edgeExtent⟩ := outgoing_base_extent outgoing
  have scanBase : spec.core.scan.input.base = spec.origin.emission.state.base := by rw [scanInput]; exact edgeBase
  have scanExtent : spec.core.scan.input.demand.size = spec.origin.emission.state.demand.size := by rw [scanInput]; exact edgeExtent
  have sizes : spec.origin.emission.state.base.nextVreg = spec.input.base.nextVreg ∧
      spec.origin.emission.state.demand.size = spec.input.demand.size :=
    calls.narrow8_bounds inv source narrowHere plainHere
  have termRecorded : spec.term ∈ spec.core.scan.output.records := by rw [spec.split.records]; simp
  have bounded : result.final.alias.size ≤ spec.input.base.nextVreg := by
    have actual := stock_lower_blockScanAliasBounds run spec.core.scan spec.events spec.term termRecorded
    have fresh : (scanState spec.term.input spec.term.inst).base.nextVreg = spec.term.input.base.nextVreg := by
      unfold scanState
      dsimp only
      split <;> rfl
    rw [fresh] at actual
    rw [spec.split.termInput,scanBase,sizes.1] at actual
    exact actual
  have extent : ∀ value r,spec.core.scan.ctx.valueReg? value = some r → value < spec.input.demand.size := by
    intro value r mapped
    have actual := (Extent.lower_mapped_demand_bounds run scope spec.events termRecorded mapped).1
    rw [spec.split.termInput,scanExtent,sizes.2] at actual
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
  obtain ⟨yesLabel,noLabel,key,labels,fragment,execution⟩ := calls.narrow8_source_values
    inv source post.2.1 getC typed width plainHere refines bounded extent held
  have actualCode : spec.origin.emission.code.toList = [tst8 key,.condBr yesLabel noLabel (.cond .ne)] := by
    rw [spec.origin.emitted]
    have buffers := congrArg Array.toList fragment.emitted
    simpa only [Array.toList_append,Array.toList_empty,List.toList_toArray,List.nil_append] using buffers
  obtain ⟨index,inst,ops,regs,prefixWorld,endWorld,machine,nf,outside,targets,terminal⟩ := execution world
  have frame : ∀ k,regs k = ρ k := by
    intro k
    apply Sequence.stop_frame isem machine k
    intro selected member defined
    obtain ⟨raw,inside,rfl⟩ := List.mem_map.mp member
    have noDefs : vdefs raw = [] := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at inside
      rcases inside with rfl | rfl <;> rfl
    rw [Resolved.renamed_defs,noDefs,List.map_nil] at defined
    exact List.not_mem_nil defined
  have registerEq : regs = ρ := funext frame
  have machine' : seqRun isem (spec.origin.emission.code.toList.map
      (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ world =
      some (.stop index inst ops regs prefixWorld [] endWorld (.goto (if test != 0 then 0 else 1))) := by
    rw [actualCode]
    exact machine
  have count : spec.origin.emission.code.size = 2 := by
    rw [← Array.length_toList,actualCode]
    rfl
  have stopIndex : index+1 = spec.origin.emission.code.size := by
    have member := (seqRun_stop_mem machine).1
    rw [count]
    match index,member with
    | 0,first =>
      simp only [List.map_cons,List.getElem?_cons_zero,Option.some.injEq] at first
      have quiet : ((tst8 key).mapRegs
          (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))).isTerminator = false := rfl
      rw [← first,quiet] at terminal
      cases terminal
    | 1,_ => rfl
    | n+2,beyond => simp at beyond
  refine ⟨index,inst,ops,regs,prefixWorld,endWorld,machine',stopIndex,?_,targets.trans labels.symm,terminal⟩
  refine ⟨post.1,post.2.1,stable _ _ _ _ nf post.2.2.1,?_⟩
  simpa only [registerEq] using post.2.2.2

/-- The real emission of a branch on a plain `i8` condition is exactly two instructions. -/
theorem ConditionalBodySpec.narrow8_emission_size {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (block : f.blocks[bi]? = some b) (termShape : b.term = .brif c yes no)
    (plain : PlainSource result.ctx c) (narrow : result.ctx.valueType? c = some (.int 8)) :
    spec.origin.emission.code.size = 2 := by
  have inv := (stock_lower_record_context run scope spec.events).1
  have ctxEq := (stock_lowerBlockCore_scanOrigin spec.coreRun).2.1
  have plainHere := spec.plain_here plain
  obtain ⟨calls,source⟩ := spec.plain_calls run scope block termShape plain
  rw [spec.origin.emitted]
  have actual := calls.narrow8_emitted_size inv source (by rw [ctxEq]; exact narrow) plainHere
  simpa only [Array.size_empty,Nat.zero_add] using actual

/-- The actual `tst` and `b.ne` of a branch on a plain `i8` condition define no virtual
registers. -/
theorem ConditionalBodySpec.narrow8_branch_no_defs {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (block : f.blocks[bi]? = some b) (termShape : b.term = .brif c yes no)
    (plain : PlainSource result.ctx c) (narrow : result.ctx.valueType? c = some (.int 8)) :
    ∀ m ∈ spec.origin.emission.code.toList,vdefs m = [] := by
  have inv := (stock_lower_record_context run scope spec.events).1
  have ctxEq := (stock_lowerBlockCore_scanOrigin spec.coreRun).2.1
  have plainHere := spec.plain_here plain
  obtain ⟨calls,source⟩ := spec.plain_calls run scope block termShape plain
  obtain ⟨code,fragment,noDefs⟩ := calls.narrow8_no_defs inv source (by rw [ctxEq]; exact narrow) plainHere
  have actualCode : spec.origin.emission.code.toList = code := by
    rw [spec.origin.emitted]
    have buffers := congrArg Array.toList fragment.emitted
    simpa only [Array.toList_append,Array.toList_empty,List.toList_toArray,List.nil_append] using buffers
  intro m member
  rw [actualCode] at member
  exact noDefs m member

end Backend.Stock.Proof.ConditionalValues
