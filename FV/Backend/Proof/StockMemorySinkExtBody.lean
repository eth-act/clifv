import FV.Backend.Proof.StockMemorySinkExtRecord
import FV.Backend.Proof.IselMemSem
import FV.Backend.Proof.StockMemoryLoad
import FV.Backend.Proof.StockGuardedRecordValues
import FV.Backend.Proof.StockSourceDFG
import FV.Backend.Proof.StockSelectScanRefines
import FV.Backend.Proof.StockAluOperandCoverage
import FV.Backend.Proof.StockDemandExtent
import FV.Backend.Proof.StockDriverBounds
import FV.Backend.Proof.StockMemoryReturnRefines

/-! Body simulation for `[y = load x; z = extend y]; return z` with the load sunk.
The two source steps (a plain load, then its extension) run against one machine
extending load. The loaded value is never demanded, so the guarded relation holds
across the load step without a register for `y`; the extension step reads memory
through the same pointer. A source-level lemma identifies the two steps with one
extending source load, whose machine refinement is the existing load contract. -/
namespace Backend.Stock.Memory.SinkExtend
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Memory.ExtendedRoots (Kind)
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

/-! ## Source values -/

/-- A load whose access size is `n` evaluates to the extension of the `n`-byte read. -/
theorem evalInst_load_of {fr : Clif.Frame} {cm : Clif.Mem} {op : Clif.LoadOp} {ty : Clif.Ty}
    {flags : Clif.MemFlags} {x : Nat} {pv : Clif.Val} {n : Nat} {raw : BitVec (8 * n)}
    (hp : fr.get x = .ok pv) (size : op.size ty = n) (room : n ≤ ty.bytes)
    (hl : cm.load flags (Clif.effAddr pv 0) n (8 * n) = .ok raw) :
    Clif.evalInst fr cm (.load op ty flags x 0) =
      .ok ([⟨ty,if op.signed then raw.signExtend ty.width else raw.zeroExtend ty.width⟩],cm) := by
  subst size
  simp [Clif.evalInst,hp,room,hl]

private theorem zext_same {n m w : Nat} (h : n = m) (raw : BitVec n) :
    (raw.zeroExtend m).zeroExtend w = raw.zeroExtend w := by
  subst h; simp [BitVec.setWidth_eq]

private theorem sext_same {n m w : Nat} (h : n = m) (raw : BitVec n) :
    (raw.zeroExtend m).signExtend w = raw.signExtend w := by
  subst h; simp [BitVec.setWidth_eq]

/-- A plain load followed by its extension computes the same value as one extending
load from the same pointer, and neither step changes memory. -/
theorem extend_load_eval (kind : Kind) {fr fr1 : Clif.Frame} {cm cm1 cm2 : Clif.Mem}
    {flags : Clif.MemFlags} {x y : Nat} {ty : Clif.Ty} {v1 v2 : Clif.Val}
    (loaded : Clif.evalInst fr cm (.load .load (loadTy kind) flags x 0) = .ok ([v1],cm1))
    (bound : fr1.get y = .ok v1)
    (extended : Clif.evalInst fr1 cm1 (.extend (extendOp kind) ty y) = .ok ([v2],cm2)) :
    cm2 = cm1 ∧ Clif.evalInst fr cm (.load kind.sourceOp ty flags x 0) = .ok ([v2],cm1) := by
  simp only [Clif.evalInst] at loaded extended
  obtain ⟨pv,hp,loaded⟩ := res_bind_eq_ok loaded
  obtain ⟨_,_,loaded⟩ := res_bind_eq_ok loaded
  obtain ⟨raw,hl,loaded⟩ := res_bind_eq_ok loaded
  simp only [Clif.Res.pure_eq,Clif.Res.ok.injEq,Prod.mk.injEq,List.cons.injEq,and_true] at loaded
  obtain ⟨rfl,rfl⟩ := loaded
  rw [bound] at extended
  simp only [Clif.Res.ok_bind] at extended
  obtain ⟨_,widen,extended⟩ := res_bind_eq_ok extended
  have widen := of_decide_eq_true (res_check_ok widen)
  have bytes : ty.bytes = ty.width / 8 := rfl
  have size : Clif.LoadOp.size ty kind.sourceOp = Clif.LoadOp.size (loadTy kind) .load := by
    cases kind <;> rfl
  have room : Clif.LoadOp.size (loadTy kind) .load ≤ ty.bytes := by
    rw [bytes]
    cases kind <;> simp only [loadTy,show Clif.Ty.i8.width = 8 from rfl,
      show Clif.Ty.i16.width = 16 from rfl,show Clif.Ty.i32.width = 32 from rfl,Clif.LoadOp.size,
      show Clif.Ty.i8.bytes = 1 from rfl,show Clif.Ty.i16.bytes = 2 from rfl,
      show Clif.Ty.i32.bytes = 4 from rfl] at widen ⊢ <;> omega
  have same : 8 * Clif.LoadOp.size (loadTy kind) .load = (loadTy kind).width := by cases kind <;> rfl
  rw [evalInst_load_of hp size room hl]
  cases kind
  all_goals
    simp only [extendOp,Stock.Proof.ScalarCast.extendOp,signed,Bool.false_eq_true,ite_true,
      ite_false,Clif.Res.pure_eq,Clif.Res.ok.injEq,Prod.mk.injEq,List.cons.injEq,and_true] at extended
    obtain ⟨rfl,rfl⟩ := extended
    refine ⟨rfl,?_⟩
    simp only [Stock.Memory.ExtendedRoots.Kind.sourceOp,Clif.LoadOp.signed,Bool.false_eq_true,
      ite_true,ite_false,Clif.Sem.uextend,Clif.Sem.sextend]
    first | rw [zext_same same] | rw [sext_same same]

/-- An extension has exactly one result and keeps memory. -/
theorem extend_single {fr : Clif.Frame} {cm cm' : Clif.Mem} {op : Clif.ExtendOp} {ty : Clif.Ty}
    {y : Nat} {vals : List Clif.Val}
    (h : Clif.evalInst fr cm (.extend op ty y) = .ok (vals,cm')) : ∃ v,vals = [v] := by
  simp only [Clif.evalInst] at h
  obtain ⟨a,_,h⟩ := res_bind_eq_ok h
  obtain ⟨_,_,h⟩ := res_bind_eq_ok h
  cases op <;> simp only [Clif.Res.pure_eq,Clif.Res.ok.injEq,Prod.mk.injEq] at h <;> exact ⟨_,h.1.symm⟩

/-! ## The extension record -/

private theorem scan_fields (st : State) (i : Nat) :
    (scanState st i).base.nextVreg = st.base.nextVreg ∧ (scanState st i).demand = st.demand ∧
      (scanState st i).base.emitted = #[] := by
  unfold scanState; dsimp only; split <;> exact ⟨rfl,rfl,rfl⟩

/-- Binding one virtual result keeps the demand table and needs a mapped result. -/
theorem bind_single_vreg_demand {ctx : Ctx} {z n : Nat} {cls : RegClass} {st bound : State}
    {copies : Array MInst} (h : bindResults ctx [(z,[.vreg n cls])] st = .ok (bound,copies)) :
    bound.demand = st.demand ∧ (ctx.valueReg? z).isSome = true := by
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
      refine ⟨?_,rfl⟩
      cases r <;> simp only [State.setAlias,bind,Except.bind,pure,Except.pure,throw,throwThe,
        MonadExceptOf.throw] at alias
      all_goals repeat' first | (solve | cases alias) | (solve | cases alias; rfl) | split at alias

/-- The extension record of the actual run: one fresh extending load, the pointer
demanded and the loaded value not demanded, and the body code is this record's code. -/
theorem stock_lower_sink_extend_body_facts (kind : Kind) {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} {x y z : Nat} {ty : Clif.Ty} {flags : Clif.MemFlags}
    (shape : Shape kind f b x y z ty flags)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList) :
    ∃ (term extend load : ScanRecord) (scanned : BlockScan) (step : Step) (nreg a : Nat),
      SourceBodySplit f event b term scanned ∧ event.block = 0 ∧
      extend.inst = 1 ∧ load.inst = 0 ∧ extend.input = term.output.state ∧
      extend ∈ event.output.records ∧ load ∈ event.output.records ∧
      extend.output.step = some step ∧ step.decision = .emitted ∧
      step.results = [[.vreg extend.input.base.nextVreg .int]] ∧
      event.ctx.valueReg? x = some (.vreg nreg .int) ∧ event.ctx.valueReg? z = some (.vreg a .int) ∧
      scanned.state = extend.output.state ∧ scanned.code = extend.output.emitted ∧
      extend.output.emitted = #[.load kind.loadOp (.vreg extend.input.base.nextVreg .int)
        (.unsignedOffset (.vreg nreg .int) 0) flags] ∧
      extend.output.state.base.nextVreg = extend.input.base.nextVreg + 1 ∧
      Demanded extend.output.state x ∧ ¬ Demanded extend.output.state y := by
  obtain ⟨term,extend,load,scanned,step,split,records,zero,extendInst,loadInst,extendInput,loadInput,
    loadRun,retained,recorded,emitted,sunks,eligible⟩ :=
    stock_lower_sink_extend_eligible kind run scope dominated shape events
  have inv := (stock_lower_record_context run scope events).1
  have block : f.blocks[event.block]? = some b := by rw [zero,shape.blocks]; rfl
  have start : blockStart f event.block = 0 := by rw [zero]; simp [blockStart]
  have statement0 : b.body[0]? = some ⟨[y],.load .load (loadTy kind) flags x 0⟩ := by
    simp [shape.body]
  have statement1 : b.body[1]? = some ⟨[z],.extend (extendOp kind) ty y⟩ := by simp [shape.body]
  obtain ⟨info1,source1,clif1,results1⟩ := ArithmeticBody.body_source_info run events split statement1
    (record := extend) (by rw [extendInst,start])
  obtain ⟨info0,source0,clif0,results0⟩ := ArithmeticBody.body_source_info run events split statement0
    (record := load) (by rw [loadInst,start])
  rw [extendInst] at source1
  rw [loadInst] at source0
  have defined : event.ctx.defInst? y = some 0 := by
    have h := stock_lower_source_result_definition run dominated events block statement0
      (x := y) (by simp)
    rwa [start] at h
  have parameter := stock_lower_source_parameter_definition run dominated events block shape.parameter
  obtain ⟨nreg,mapped⟩ := inv.typedReg x _ (inv.addr64 _ _ _ x source0 clif0 rfl)
  have rootEligible := eligible
  obtain ⟨receipt⟩ := stock_lower_record_selection run events retained recorded emitted
  have rootRun := receipt.rootRun
  rw [extendInst] at rootRun
  obtain ⟨sink,outEq,nextEq,_⟩ := stock_lower_sink_extend kind inv source1 clif1 shape.small defined
    source0 clif0 parameter mapped rootEligible rootRun
  have output := receipt.output
  rw [outEq] at output
  simp only [V.regsVec.injEq] at output
  have binding := receipt.binding
  have resultsAt : event.ctx.insts[extend.inst]!.results = [z] := by
    rw [extendInst]
    simp only [getElem!_def,source1,results1]
  rw [resultsAt,← output] at binding
  obtain ⟨copiesEq,baseEq,sunkEq⟩ := bind_single_vreg binding
  obtain ⟨demandEq,zMapped⟩ := bind_single_vreg_demand binding
  obtain ⟨zr,zSome⟩ := Option.isSome_iff_exists.mp zMapped
  obtain ⟨a,rfl⟩ := inv.valueReg z zr zSome
  obtain ⟨scanNext,scanDemand,scanEmitted⟩ := scan_fields extend.input 1
  have emittedEq : extend.output.emitted = #[.load kind.loadOp (.vreg extend.input.base.nextVreg .int)
      (.unsignedOffset (.vreg nreg .int) 0) flags] := by
    rw [receipt.code,copiesEq,baseEq,nextEq]
    simp [LState.emit,LState.fresh,scanEmitted,scanNext]
  have stateDemand : extend.output.state.demand = ((scanState extend.input 1).mark x).demand := by
    rw [receipt.state,demandEq,nextEq]
    rfl
  have nextVreg : extend.output.state.base.nextVreg = extend.input.base.nextVreg + 1 := by
    rw [receipt.state,baseEq,nextEq]
    simp [LState.emit,LState.fresh,scanNext]
  have stateSunk : extend.output.state.sunk[0]! = true := by
    rw [receipt.state,sunkEq,nextEq]
    simp only [State.mark]
    rw [sunks]
    rfl
  have xBound := (Extent.lower_mapped_demand_bounds run scope events retained mapped).1
  have xy : x ≠ y := by
    intro same
    subst same
    rw [parameter] at defined
    cases defined
  have demandedX : Demanded extend.output.state x := by
    change extend.output.state.demand[x]! ≠ 0
    rw [stateDemand]
    exact (demanded_mark_iff (scanState extend.input 1) x x (by rw [scanDemand]; exact xBound)).mpr
      (Or.inl rfl)
  have quietY : ¬ Demanded extend.output.state y := by
    have zeroY : (scanState extend.input 1).demand[y]! = 0 := by
      have accepted := (sink_accepted sink).2.2.1
      apply accepted y
      simp only [getElem!_def,source0,results0,List.mem_singleton]
    intro wanted
    change extend.output.state.demand[y]! ≠ 0 at wanted
    rw [stateDemand] at wanted
    exact wanted (by rw [mark_other _ x y (Ne.symm xy)]; exact zeroY)
  have loadOutput : load.output = ⟨load.input,some ⟨0,0,.sunk,load.input,load.input,[],[],#[]⟩,#[]⟩ := by
    have sunk : load.input.sunk[0]! = true := by rw [loadInput]; exact stateSunk
    simp only [scanInstruction,sunk,ite_true,zero,pure,Except.pure] at loadRun
    exact (Except.ok.inj loadRun).symm
  have indices : sourceBodyIndices f event.block b = [1,0] := by
    simp [sourceBodyIndices,start,shape.body,List.range_succ]
  have scans := split.scanned
  rw [indices] at scans
  have loadMember : load ∈ event.output.records := by
    rw [split.records,records]; simp
  have bodyFacts : scanned.state = extend.output.state ∧ scanned.code = extend.output.emitted := by
    cases scans with
    | cons head rest =>
      rename_i scan1 tail
      cases rest with
      | cons head' rest' =>
        rename_i scan0 tail'
        cases rest'
        simp only [List.cons.injEq,and_true] at records
        obtain ⟨rfl,rfl⟩ := records
        simp only at loadOutput
        subst loadOutput
        simp
  refine ⟨term,extend,load,scanned,step,nreg,a,split,zero,extendInst,loadInst,extendInput,retained,
    loadMember,recorded,emitted,?_,mapped,zSome,bodyFacts.1,bodyFacts.2,emittedEq,nextVreg,demandedX,quietY⟩
  rw [receipt.resultRegs,← output]
  simp [LState.fresh,scanNext]

/-! ## Body simulation -/

/-- Two original source steps, the plain load and its extension, against the body's one
machine extending load. The guarded relation at the body's final scan state holds
before both steps; after them it holds at the return's scan state. The loaded value has
no register; the extension reads the same memory through the same pointer. -/
theorem stock_sink_extend_return_body (kind : Kind) {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} {x y z : Nat} {ty : Clif.Ty} {flags : Clif.MemFlags}
    (shape : Shape kind f b x y z ty flags)
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat} {isem : Backend.Proof.Sem}
    {MR : MemRelT} (stable : MRStable F MR) (memorySem : MemRefines F sb syms isem)
    (memoryOk : MemRelOk F sb syms f MR) {env : Clif.Env} {cp : Clif.Program}
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList) :
    ∃ (term : ScanRecord) (body : BlockScan), SourceBodySplit f event b term body ∧
      ∀ s s',SourceSteps (IndexedSourceInst env cp f event.ctx event.block)
        ((List.range b.body.length).map (blockStart f event.block + ·)) s s' →
      ∀ ρ w,GuardedScanRel f result event.ctx event.block MR event.output.state s ρ w → ∃ ρ' w',
        seqRun isem (body.code.toList.map (·.mapRegs
          (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) ρ w =
          some (.fall ρ' w') ∧
        GuardedScanRel f result event.ctx event.block MR term.output.state s' ρ' w' := by
  obtain ⟨term,extend,load,scanned,step,nreg,a,split,zero,extendInst,loadInst,extendInput,retained,
    _,recorded,emitted,results,mapped,zMapped,stateEq,codeEq,emittedEq,nextVreg,demandedX,quietY⟩ :=
    stock_lower_sink_extend_body_facts kind run scope dominated shape events
  refine ⟨term,scanned,split,?_⟩
  intro s s' steps ρ w held
  have inv := (stock_lower_record_context run scope events).1
  have block : f.blocks[event.block]? = some b := by rw [zero,shape.blocks]; rfl
  have start : blockStart f event.block = 0 := by rw [zero]; simp [blockStart]
  have statement0 : b.body[0]? = some ⟨[y],.load .load (loadTy kind) flags x 0⟩ := by
    simp [shape.body]
  have statement1 : b.body[1]? = some ⟨[z],.extend (extendOp kind) ty y⟩ := by simp [shape.body]
  have current0 : load.inst = blockStart f event.block + 0 := by rw [loadInst,start]
  have current1 : extend.inst = blockStart f event.block + 1 := by rw [extendInst,start]
  obtain ⟨info1,source1,clif1,results1⟩ := ArithmeticBody.body_source_info run events split statement1
    current1
  obtain ⟨info0,source0,clif0,results0⟩ := ArithmeticBody.body_source_info run events split statement0
    current0
  obtain ⟨little,_,_⟩ := load_source_data kind inv source0 clif0
  have finalState : event.output.state = extend.output.state := split.state.symm.trans stateEq
  have range : (List.range b.body.length).map (blockStart f event.block + ·) = [0,1] := by
    simp [shape.body,start,List.range_succ]
  rw [range] at steps
  obtain ⟨p,fr,cm⟩ := s
  obtain ⟨p',fr',cm'⟩ := s'
  cases steps with
  | cons head0 tail =>
    rename_i s1
    cases tail with
    | cons head1 done =>
      cases done
      obtain ⟨p1,fr1,cm1⟩ := s1
      obtain ⟨at0,adv0,step0⟩ := head0
      obtain ⟨at1,adv1,step1⟩ := head1
      dsimp only at at0 adv0 at1 adv1
      rw [start] at at0 at1
      have p0 : p = 0 := by omega
      have pOne : p1 = 1 := by omega
      have pTwo : p' = 2 := by omega
      subst p0 pOne pTwo
      obtain ⟨func,dfg,memory,values⟩ := held
      dsimp only at func dfg memory values
      have loadStep : SourceInstResult env cp event.ctx load.inst (fr,cm) (fr1,cm1) := by
        rw [loadInst]; exact step0
      have extendStep : SourceInstResult env cp event.ctx extend.inst (fr1,cm1) (fr',cm') := by
        rw [extendInst]; exact step1
      -- the load step: one value, unchanged memory, and the loaded value in the next frame
      have loadParts := loadStep
      obtain ⟨info0',inst0,vals1,regs1,rest0,found0,original0,_,outcome0,written0,frame0⟩ := loadParts
      cases Option.some.inj (found0.symm.trans source0)
      cases Option.some.inj (original0.symm.trans clif0)
      have plain0 : Clif.evalInst fr cm (.load .load (loadTy kind) flags x 0) = .ok (vals1,cm1) := by
        simpa only [instOutcome] using outcome0
      obtain ⟨_,_,_,_,_,_,valsEq,memEq⟩ := evalInst_load_inv little plain0
      obtain ⟨v1,rfl⟩ : ∃ v1,vals1 = [v1] := ⟨_,valsEq⟩
      subst cm1
      rw [results0] at written0
      simp only [Clif.Regs.setMany_cons,Clif.Regs.setMany_nil,Option.some.injEq] at written0
      subst regs1
      change fr1 = _ at frame0
      have getY : fr1.get y = .ok v1 := by
        rw [frame0]; simp [Clif.Frame.get,Clif.Regs.set_same]
      have func1 : fr1.func = f := by rw [frame0]; exact func
      -- the extension step and the single extending source load it equals
      have extendParts := extendStep
      obtain ⟨info1',inst1,vals2,regs2,rest1,found1,original1,_,outcome1,_,frame1⟩ := extendParts
      cases Option.some.inj (found1.symm.trans source1)
      cases Option.some.inj (original1.symm.trans clif1)
      have plain1 : Clif.evalInst fr1 cm (.extend (extendOp kind) ty y) = .ok (vals2,cm') := by
        simpa only [instOutcome] using outcome1
      obtain ⟨v2,rfl⟩ := extend_single plain1
      obtain ⟨memSame,oneLoad⟩ := extend_load_eval kind plain0 getY plain1
      subst cm'
      change fr' = _ at frame1
      have func2 : fr'.func = f := by rw [frame1]; exact func1
      -- the machine load reads the same memory through the demanded pointer
      have required : Demanded event.output.state x ∧
          x ∈ availOf f (availIn f result.ctx) event.block 0 :=
        ⟨by rw [finalState]; exact demandedX,
          stock_lower_record_args_available run scope dominated events block statement0 current0
            source0 clif0 x (by simp [Driver.instArgs])⟩
      have restrictedGet : (restrict fr (availOf f (availIn f result.ctx) event.block 0)).get x =
          fr.get x := by
        simp only [Clif.Frame.get,restrict_regs_of_mem required.2]
      have restrictedEval : Clif.evalInst (restrict fr (availOf f (availIn f result.ctx) event.block 0)) cm
          (.load kind.sourceOp ty flags x 0) = .ok ([v2],cm) := by
        simpa only [Clif.evalInst,restrictedGet] using oneLoad
      have restrictedHeld : ValuesHeld (fun v => Demanded event.output.state v ∧
          v ∈ availOf f (availIn f result.ctx) event.block 0) event.ctx
          (restrict fr (availOf f (availIn f result.ctx) event.block 0))
          (fun k => ρ (aliasNum result.final.alias k)) := by
        intro v needed value lookup
        rw [restrict_regs_of_mem needed.2] at lookup
        exact values v needed value lookup
      have operands := restrictedHeld x required
      have pointerTy := inv.addr64 _ _ _ x source0 clif0 rfl
      have address := mapped_unsigned_address (sb := sb) (bytes := kind.loadOp.bytes) (w := w)
        operands mapped dfg pointerTy (off := 0) (by cases kind <;> decide)
      have width : ty.width ≤ 64 := by
        have small := shape.small
        cases ty <;> simp [narrow] at small <;> decide
      obtain ⟨ρ',w',executed,_,memory',loaded,_⟩ := load_source_seqRun stable memorySem memoryOk memory
        (fr := restrict fr (availOf f (availIn f result.ctx) event.block 0))
        (ρ := ρ) (d := extend.input.base.nextVreg)
        (am := .unsignedOffset (.vreg (aliasNum result.final.alias nreg) .int) 0)
        (by intro r member; exact ⟨_,List.mem_singleton.mp member⟩)
        (aop := kind.loadOp) (by cases kind <;> decide)
        (by cases kind <;> rfl) (by cases kind <;> rfl) width little
        (fun pv hpv => by simpa [amUses,amVregs,AMode.regs,amodeAddr,LoadOp.bytes] using address pv hpv)
        restrictedEval
      have value := loaded v2 (by simp)
      -- the body code is the record's one load; its destination has no alias
      have aliasBound : result.final.alias.size ≤ extend.input.base.nextVreg := by
        simpa only [(scan_fields extend.input extend.inst).1] using
          stock_lower_blockScanAliasBounds run event events extend retained
      have fixed : aliasNum result.final.alias extend.input.base.nextVreg = extend.input.base.nextVreg := by
        apply chaseF_none
        rw [Array.getElem?_eq_none aliasBound]
        rfl
      have resolved : extend.output.emitted.toList.map (·.mapRegs
          (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))) =
          [.load kind.loadOp (.vreg extend.input.base.nextVreg .int)
            (.unsignedOffset (.vreg (aliasNum result.final.alias nreg) .int) 0) flags] := by
        rw [emittedEq]
        change [MInst.load kind.loadOp
          (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)
            (.vreg extend.input.base.nextVreg .int))
          (.unsignedOffset (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)
            (.vreg nreg .int)) 0) flags] = _
        rw [resolve_vreg,resolve_vreg]
        change [MInst.load kind.loadOp (.vreg (aliasNum result.final.alias extend.input.base.nextVreg) .int)
          (.unsignedOffset (.vreg (aliasNum result.final.alias nreg) .int) 0) flags] = _
        rw [fixed]
      have executedRecord : seqRun isem (extend.output.emitted.toList.map (·.mapRegs
          (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w =
          some (.fall ρ' w') := by
        rw [resolved]; exact executed
      refine ⟨ρ',w',by rw [codeEq]; exact executedRecord,func2,?_,?_,?_⟩
      · -- the post-step restricted frames keep their dataflow facts
        have dfg1 := stock_lower_source_step_dfg run scope dominated events block statement0 current0
          func dfg loadStep
        exact stock_lower_source_step_dfg run scope dominated events block statement1 current1
          func1 dfg1 extendStep
      · rw [frame1,frame0]
        exact memory'
      · -- the loaded value is undemanded, so the guarded values survive the load step
        have before : ValuesHeld (fun v => Demanded extend.output.state v ∧
            v ∈ availOf f (availIn f result.ctx) event.block (0 + 1)) event.ctx (withValue fr y v1)
            (fun k => ρ (aliasNum result.final.alias k)) := by
          intro v needed val lookup
          by_cases same : v = y
          · subst v
            exact absurd needed.1 quietY
          · have earlier := available_before_of_after_not_result block statement0 needed.2
              (by simpa only [List.mem_singleton] using same)
            have lookup' : fr.regs v = some val := by
              simpa only [withValue,same,ite_false] using lookup
            exact values v ⟨by rw [finalState]; exact needed.1,earlier⟩ val lookup'
        have afterLoad := source_single_result_values source0 clif0 results0 loadStep
          (by simpa only [instOutcome] using plain0) before
        have defs : ∀ m ∈ extend.output.emitted.toList.map (·.mapRegs
            (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1))),
            ∀ key ∈ vdefs m,
            extend.input.base.nextVreg ≤ key ∧ key < extend.output.state.base.nextVreg := by
          rw [resolved]
          intro m member key defined
          have equal := List.mem_singleton.mp member
          subst m
          change key ∈ [extend.input.base.nextVreg] at defined
          have equal := List.mem_singleton.mp defined
          subst key
          rw [nextVreg]
          exact ⟨Nat.le_refl _,Nat.lt_succ_self _⟩
        have afterWith := stock_lower_fresh_record_values_auto_demand run scope dominated events retained
          block statement1 current1 source1 clif1 results1 rfl zMapped recorded emitted results
          (Nat.le_refl _) afterLoad defs executedRecord value
        have afterExtend := source_single_result_values source1 clif1 results1 extendStep
          (by simpa only [instOutcome] using plain1) afterWith
        rw [extendInput] at afterExtend
        exact afterExtend

/-- The return half of the memory contract: an original source return refines the
actual Stock code, with the sinking body supplied by `stock_sink_extend_return_body`.
The load's trap behavior is not involved, since the source run returned. -/
theorem stock_sink_extend_returns (kind : Kind) {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) {b : Clif.Block} {x y z : Nat} {ty : Clif.Ty} {flags : Clif.MemFlags}
    (shape : Shape kind f b x y z ty flags)
    {args : List Clif.Val} {cm : Clif.Mem} {fr : Clif.Frame} (entered : SourceEntry f args fr)
    {env : Clif.Env} {cp : Clif.Program} {fuel : Nat} {vals : List Clif.Val} {mem : Clif.Mem}
    (returned : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .returned vals mem)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms isem) {MR : MemRelT} (stable : MRStable F MR)
    (memoryOk : MemRelOk F sb syms f MR) {w : Arm.ArmState} (memory : MR fr.slots cm w)
    (arguments : ArgsAtEntry F f.sig args w) :
    ∃ ρ,RunOkABI f result.code isem MR fr.slots ⟨0,0,ρ,w⟩ (.returned vals mem) := by
  have family : ∀ stm ∈ b.body,OrdinaryBody.OrdinaryInst stm.inst := by
    intro stm member
    rw [shape.body] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    all_goals
      constructor
      · intro fn args impossible; cases impossible
      · intro sig callee args impossible; cases impossible
  exact OrdinaryBody.actual_ordinary_entry_return_refines_frame run scope dominated abi shape.blocks
    family shape.ret entered returned refines driver memorySem stable
    (fun event events => stock_sink_extend_return_body kind run scope dominated shape stable memorySem
      memoryOk events) memory arguments

end Backend.Stock.Memory.SinkExtend
