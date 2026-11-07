import FV.Backend.Proof.StockMemorySinkExtSelection
import FV.Backend.Proof.StockMemorySinkExtSource
import FV.Backend.Proof.StockReturnedSourceRetention
import FV.Backend.Proof.StockReturnRecordCalls
import FV.Backend.Proof.StockTerminalEmission
import FV.Backend.Proof.StockArithmeticBodyRefines
import FV.Backend.Proof.StockMemoryReturnSpec
import FV.Backend.Proof.DriverCheckSound

/-! The sink step inside the actual whole-driver run on the original source class
`[y = load x; z = extend y]; return z`. The return leaves the memory color of the
load's barrier, so Stock's sinking test accepts the loaded value at the extension;
the extension's record selects the sinking root, sinks the load and emits one
extending load, and the load's own record is skipped as sunk. The same holds for
`[y = atomic_load x; z = uextend y]; return z` (`SourceShape .acquire`), where rule 810
emits one acquiring load. -/
namespace Backend.Stock.Memory.SinkExtend
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Memory.ExtendedRoots (Kind)
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

/-- Original source syntax of the sinking-extension class. -/
structure Shape (kind : Kind) (f : Clif.Function) (b : Clif.Block) (x y z : Nat) (ty : Clif.Ty)
    (flags : Clif.MemFlags) : Prop where
  blocks : f.blocks = [b]
  body : b.body = [⟨[y],.load .load (loadTy kind) flags x 0⟩,⟨[z],.extend (extendOp kind) ty y⟩]
  ret : b.term = .ret [z]
  small : narrow ty = true
  parameter : x ∈ b.params.map (·.1)
  ordinary : (sigRets f.sig).any (·.purpose == .sret) = false

/-- A source load of either kind uses the pointer `x`. -/
theorem Source.loads (src : Source) (ty : Clif.Ty) (flags : Clif.MemFlags) (x : Nat) :
    (∃ ty' flags',src.load ty flags x = .load .load ty' flags' x 0) ∨
      ∃ ty' flags',src.load ty flags x = .atomicLoad ty' flags' x := by
  cases src
  · exact Or.inl ⟨ty,flags,rfl⟩
  · exact Or.inr ⟨ty,flags,rfl⟩

/-- Original source syntax of the sinking-extension class, for a plain or atomic load. -/
structure SourceShape (src : Source) (kind : Kind) (f : Clif.Function) (b : Clif.Block)
    (x y z : Nat) (ty : Clif.Ty) (flags : Clif.MemFlags) : Prop where
  blocks : f.blocks = [b]
  body : b.body = [⟨[y],src.load (loadTy kind) flags x⟩,⟨[z],.extend (extendOp kind) ty y⟩]
  ret : b.term = .ret [z]
  small : narrow ty = true
  parameter : x ∈ b.params.map (·.1)
  ordinary : (sigRets f.sig).any (·.purpose == .sret) = false
  admits : src.admits kind = true

/-- The plain-load class is the plain source of the general class. -/
theorem Shape.source {kind : Kind} {f : Clif.Function} {b : Clif.Block} {x y z : Nat}
    {ty : Clif.Ty} {flags : Clif.MemFlags} (shape : Shape kind f b x y z ty flags) :
    SourceShape .plain kind f b x y z ty flags :=
  ⟨shape.blocks,shape.body,shape.ret,shape.small,shape.parameter,shape.ordinary,rfl⟩

/-- A single-result source statement's result has its CLIF type in the actual scan context. -/
theorem stock_lower_statement_result_type {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {bi k y : Nat} {b : Clif.Block} {inst : Clif.Inst} {ty : Clif.Ty}
    (block : f.blocks[bi]? = some b) (statement : b.body[k]? = some ⟨[y],inst⟩)
    (types : inst.resultTypes (fun r => (f.extern? r).map (·.sig)) (f.sigDecls.lookup ·) = some [ty]) :
    event.ctx.valueType? y = some (CTy.ofClif ty) := by
  obtain ⟨ranges,params,earlier,suffix,starting,finishing,before,after,label,bi',data,core,
    build,ordered,initial,empty,parts,folded,final,prefixRun,nodeRun,suffixRun,node,coreRun,
    eventEq,stateEq⟩ := stock_lower_blockScanOrigin run events
  obtain ⟨original,st0,oldBuild,spec,view⟩ := buildCtx_source build
  have valTys : event.ctx.valTy = original.valTy := by
    rw [eventEq,(stock_lowerBlockCore_scanOrigin coreRun).2.1]
    exact view.valTy
  obtain ⟨info,originalFound,clif,results⟩ := spec.facts.stmt bi b k ⟨[y],inst⟩ block statement
  have inv := buildCtx_mappedInv scope build
  obtain ⟨tys,typesEq,resTys,_⟩ := inv.resTys _ info inst (by rw [view.insts]; exact originalFound) clif
  rw [types] at typesEq
  cases typesEq
  have typed := (spec.facts.types dominated.ssa).1 _ info originalFound 0 y (CTy.ofClif ty)
    (by rw [results]; rfl) (by rw [resTys]; rfl)
  simpa only [Ctx.valueType?,valTys] using typed

private theorem scan_emitted (st : State) (i : Nat) : (scanState st i).base.emitted = #[] := by
  unfold scanState; dsimp only; split <;> rfl

/-- Binding one virtual result installs an alias: no copy, and the lowering base and
sunk table are unchanged. -/
theorem bind_single_vreg {ctx : Ctx} {z n : Nat} {cls : RegClass} {st bound : State}
    {copies : Array MInst} (h : bindResults ctx [(z,[.vreg n cls])] st = .ok (bound,copies)) :
    copies = #[] ∧ bound.base = st.base ∧ bound.sunk = st.sunk := by
  unfold bindResults at h
  simp only [List.foldlM_cons,List.foldlM_nil,bind,Except.bind,pure,Except.pure] at h
  cases mapped : ctx.valueReg? z with
  | none => simp [mapped,throw,throwThe,MonadExceptOf.throw] at h
  | some r =>
    simp only [mapped] at h
    cases alias : st.setAlias r (.vreg n cls) with
    | error e => simp [alias] at h
    | ok q =>
      simp only [alias,Except.ok.injEq,Prod.mk.injEq] at h
      obtain ⟨rfl,rfl⟩ := h
      refine ⟨rfl,?_⟩
      cases r <;> simp only [State.setAlias,bind,Except.bind,pure,Except.pure,throw,throwThe,
        MonadExceptOf.throw] at alias
      all_goals repeat' first | (solve | cases alias) | (solve | cases alias; exact ⟨rfl,rfl⟩) | split at alias

/-- In the actual run, the extension's scan state accepts the loaded value for sinking,
for a plain or an atomic load. -/
theorem stock_lower_source_extend_eligible (src : Source) (kind : Kind) {f : Clif.Function}
    {result : Result} (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} {x y z : Nat} {ty : Clif.Ty} {flags : Clif.MemFlags}
    (shape : SourceShape src kind f b x y z ty flags)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList) :
    ∃ (term extend load : ScanRecord) (scanned : BlockScan) (step : Step),
      SourceBodySplit f event b term scanned ∧ scanned.records = [extend,load] ∧
      event.block = 0 ∧ extend.inst = 1 ∧ load.inst = 0 ∧ extend.input = term.output.state ∧
      load.input = extend.output.state ∧
      scanInstruction event.ctx event.block 0 event.termInst event.isBranch load.input = .ok load.output ∧
      extend ∈ event.output.records ∧ extend.output.step = some step ∧ step.decision = .emitted ∧
      (scanState extend.input 1).sunk = #[false,false,false] ∧
      Stock.source event.ctx (scanState extend.input 1) y = some (0,true) := by
  obtain ⟨b',term0,body0,split0⟩ := stock_lower_body_scan_split run scope events
  have bound : event.block < 1 := by
    have h := lt_of_getElem? split0.block
    simpa [shape.blocks] using h
  have zero : event.block = 0 := by omega
  have block : f.blocks[event.block]? = some b := by rw [zero,shape.blocks]; rfl
  have statement0 : b.body[0]? = some ⟨[y],src.load (loadTy kind) flags x⟩ := by
    simp [shape.body]
  have statement1 : b.body[1]? = some ⟨[z],.extend (extendOp kind) ty y⟩ := by simp [shape.body]
  obtain ⟨term,extend,scanned,step,split,member,current,_,_,retained,recorded,emitted⟩ :=
    stock_lower_returned_definition_emitted run scope dominated events block statement1 (z := z)
      (by simp) shape.ret (by simp)
  have termMember : term ∈ event.output.records := by rw [split.records]; exact List.mem_cons_self
  obtain ⟨termStep,termRecorded,termEmitted⟩ := stock_lower_retTrap_record_emitted run scope events
    block (by rw [shape.ret]; rfl) termMember split.termInst
  obtain ⟨_,_,_,_,_,_,_,_,_,termState,_⟩ := stock_lower_return_record_helper run scope events block
    shape.ret termMember split.termInst termRecorded termEmitted
  have start : blockStart f event.block = 0 := by rw [zero]; simp [blockStart]
  have terminal : event.termInst = 2 := by rw [split.termIndex,start,shape.body]; rfl
  have indices : sourceBodyIndices f event.block b = [1,0] := by
    simp [sourceBodyIndices,start,shape.body,List.range_succ]
  obtain ⟨ranges,_,_,_,_,_,_,_,_,_,_,_,build,_⟩ := stock_lower_blockScanOrigin run events
  obtain ⟨colors,uses,sunks⟩ := initial_chain_of build dominated shape.blocks
    (Source.loads src (loadTy kind) flags x) shape.body shape.ret shape.parameter
    (sretRet_ordinary shape.ordinary)
  have input := single_event_input run shape.blocks shape.ret events
  have defined : event.ctx.defInst? y = some 0 := by
    have h := stock_lower_source_result_definition run dominated events block statement0
      (x := y) (by simp)
    rwa [start] at h
  have scans := split.scanned
  rw [indices] at scans
  cases scans with
  | cons head rest =>
    rename_i scan1 tail
    cases rest with
    | cons head' rest' =>
      rename_i scan0 tail'
      cases rest'
      have extendEq : extend = ⟨1,term.output.state,scan1⟩ := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with same | same
        · exact same
        · rw [same] at current; simp [start] at current
      subst extendEq
      obtain ⟨info0,source0,_,results0⟩ := ArithmeticBody.body_source_info run events split statement0
        (record := ⟨0,scan1.state,scan0⟩) (by simp [start])
      have source0' : event.ctx.insts[0]? = some info0 := source0
      have resultsLen : event.ctx.insts[0]!.results.length = 1 := by
        simp only [getElem!_def,source0',results0,List.length_singleton]
      have termInput : term.input = event.input := split.termInput
      have termInst : term.inst = 2 := split.termInst.trans terminal
      rw [sretRet_ordinary shape.ordinary] at termState
      simp only [List.append_nil,List.foldl_cons,List.foldl_nil] at termState
      have fields : (scanState term.output.state 1).entryColor = #[1,0,2] ∧
          (scanState term.output.state 1).uses = result.initial.uses ∧
          (scanState term.output.state 1).color = some 2 ∧
          (scanState term.output.state 1).sunk = #[false,false,false] := by
        rw [termState,termInput,input,termInst]
        simp [scanState,State.mark,colors,sunks]
      refine ⟨term,⟨1,term.output.state,scan1⟩,⟨0,scan1.state,scan0⟩,_,step,split,rfl,zero,rfl,rfl,
        rfl,rfl,?_,retained,recorded,emitted,fields.2.2.2,?_⟩
      · exact head'
      · obtain ⟨entry,usesAt,color,_⟩ := fields
        simp only [Stock.source,defined,entry,usesAt,color,uses]
        simp
        exact resultsLen

/-- In the actual run, the extension's scan state accepts the loaded value for sinking.
The single block, its two records and their chained states are derived from the run. -/
theorem stock_lower_sink_extend_eligible (kind : Kind) {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} {x y z : Nat} {ty : Clif.Ty} {flags : Clif.MemFlags}
    (shape : Shape kind f b x y z ty flags)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList) :
    ∃ (term extend load : ScanRecord) (scanned : BlockScan) (step : Step),
      SourceBodySplit f event b term scanned ∧ scanned.records = [extend,load] ∧
      event.block = 0 ∧ extend.inst = 1 ∧ load.inst = 0 ∧ extend.input = term.output.state ∧
      load.input = extend.output.state ∧
      scanInstruction event.ctx event.block 0 event.termInst event.isBranch load.input = .ok load.output ∧
      extend ∈ event.output.records ∧ extend.output.step = some step ∧ step.decision = .emitted ∧
      (scanState extend.input 1).sunk = #[false,false,false] ∧
      Stock.source event.ctx (scanState extend.input 1) y = some (0,true) :=
  stock_lower_source_extend_eligible .plain kind run scope dominated shape.source events

/-- The whole-driver sink step for a plain or an atomic load. The extension's record
selects the sinking root and emits exactly one load (an extending load or an acquiring
load) from the load's pointer into a fresh register; the load becomes sunk, and the
load's own record is skipped as sunk with no code. -/
theorem stock_lower_source_extend_record (src : Source) (kind : Kind) {f : Clif.Function}
    {result : Result} (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} {x y z : Nat} {ty : Clif.Ty} {flags : Clif.MemFlags}
    (shape : SourceShape src kind f b x y z ty flags)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList) :
    ∃ (term extend load : ScanRecord) (scanned : BlockScan) (step : Step) (nreg : Nat),
      SourceBodySplit f event b term scanned ∧ scanned.records = [extend,load] ∧
      event.block = 0 ∧ extend.inst = 1 ∧ load.inst = 0 ∧ extend.input = term.output.state ∧
      load.input = extend.output.state ∧ event.ctx.valueReg? x = some (.vreg nreg .int) ∧
      extend.output.step = some step ∧ step.decision = .emitted ∧
      step.rules.getLast? = some (src.root kind).id ∧
      extend.output.emitted = #[src.emitted kind ((scanState extend.input 1).base.fresh .int).1 nreg flags] ∧
      extend.output.state.sunk = #[true,false,false] ∧
      load.output = ⟨load.input,some ⟨0,0,.sunk,load.input,load.input,[],[],#[]⟩,#[]⟩ := by
  obtain ⟨term,extend,load,scanned,step,split,records,zero,extendInst,loadInst,extendInput,loadInput,
    loadRun,retained,recorded,emitted,sunks,eligible⟩ :=
    stock_lower_source_extend_eligible src kind run scope dominated shape events
  obtain ⟨receipt⟩ := stock_lower_record_selection run events retained recorded emitted
  have inv := (stock_lower_record_context run scope events).1
  have block : f.blocks[event.block]? = some b := by rw [zero,shape.blocks]; rfl
  have start : blockStart f event.block = 0 := by rw [zero]; simp [blockStart]
  have statement0 : b.body[0]? = some ⟨[y],src.load (loadTy kind) flags x⟩ := by
    simp [shape.body]
  have statement1 : b.body[1]? = some ⟨[z],.extend (extendOp kind) ty y⟩ := by simp [shape.body]
  obtain ⟨info1,source1,clif1,results1⟩ := ArithmeticBody.body_source_info run events split statement1
    (record := extend) (by rw [extendInst,start])
  obtain ⟨info0,source0,clif0,_⟩ := ArithmeticBody.body_source_info run events split statement0
    (record := load) (by rw [loadInst,start])
  rw [extendInst] at source1
  rw [loadInst] at source0
  have defined : event.ctx.defInst? y = some 0 := by
    have h := stock_lower_source_result_definition run dominated events block statement0
      (x := y) (by simp)
    rwa [start] at h
  have typed : event.ctx.valueType? y = some (.int (loadTy kind).width) := by
    have h := stock_lower_statement_result_type run scope dominated events block statement0
      (ty := loadTy kind) (by cases src <;> rfl)
    rw [h]
    cases kind <;> rfl
  have parameter := stock_lower_source_parameter_definition run dominated events block shape.parameter
  obtain ⟨nreg,mapped⟩ := inv.typedReg x _ (inv.addr64 _ _ _ x source0 clif0 (by cases src <;> rfl))
  have rootRun := receipt.rootRun
  rw [extendInst] at rootRun
  obtain ⟨_,outEq,nextEq,last⟩ := stock_lower_source_extend src kind inv shape.admits source1 clif1
    shape.small typed defined source0 clif0 parameter mapped eligible rootRun
  have output := receipt.output
  rw [outEq] at output
  simp only [V.regsVec.injEq] at output
  have binding := receipt.binding
  have resultsAt : event.ctx.insts[extend.inst]!.results = [z] := by
    rw [extendInst]
    simp only [getElem!_def,source1,results1]
  rw [resultsAt,← output] at binding
  obtain ⟨copiesEq,baseEq,sunkEq⟩ := bind_single_vreg binding
  refine ⟨term,extend,load,scanned,step,nreg,split,records,zero,extendInst,loadInst,extendInput,
    loadInput,mapped,recorded,emitted,?_,?_,?_,?_⟩
  · rw [receipt.rules,last]
  · rw [receipt.code,copiesEq,baseEq,nextEq]
    simp [LState.emit,LState.fresh,scan_emitted]
  · rw [receipt.state,sunkEq,nextEq]
    simp only [State.mark]
    rw [sunks]
    rfl
  · have sunk : load.input.sunk[0]! = true := by
      rw [loadInput,receipt.state,sunkEq,nextEq]
      simp only [State.mark]
      rw [sunks]
      rfl
    simp only [scanInstruction,sunk,ite_true,zero,pure,Except.pure] at loadRun
    exact (Except.ok.inj loadRun).symm

/-- The whole-driver sink step. The extension's record selects the sinking root and
emits exactly one extending load from the load's address into a fresh register; the
load becomes sunk, and the load's own record is skipped as sunk with no code. -/
theorem stock_lower_sink_extend_record (kind : Kind) {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} {x y z : Nat} {ty : Clif.Ty} {flags : Clif.MemFlags}
    (shape : Shape kind f b x y z ty flags)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList) :
    ∃ (term extend load : ScanRecord) (scanned : BlockScan) (step : Step) (nreg : Nat),
      SourceBodySplit f event b term scanned ∧ scanned.records = [extend,load] ∧
      event.block = 0 ∧ extend.inst = 1 ∧ load.inst = 0 ∧ extend.input = term.output.state ∧
      load.input = extend.output.state ∧ event.ctx.valueReg? x = some (.vreg nreg .int) ∧
      extend.output.step = some step ∧ step.decision = .emitted ∧
      step.rules.getLast? = some (root kind).id ∧
      extend.output.emitted = #[.load kind.loadOp ((scanState extend.input 1).base.fresh .int).1
        (.unsignedOffset (.vreg nreg .int) 0) flags] ∧
      extend.output.state.sunk = #[true,false,false] ∧
      load.output = ⟨load.input,some ⟨0,0,.sunk,load.input,load.input,[],[],#[]⟩,#[]⟩ :=
  stock_lower_source_extend_record .plain kind run scope dominated shape.source events

end Backend.Stock.Memory.SinkExtend
