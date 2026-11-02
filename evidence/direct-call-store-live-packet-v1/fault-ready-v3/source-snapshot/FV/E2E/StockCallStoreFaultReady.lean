import FV.E2E.StockCallStoreSourceFault
import FV.E2E.StockLiveCallPrelude
import FV.E2E.ABIReadOnlyMachine

namespace Backend.Stock.CallStore
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof E2E
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- Internal call-entry facts come from the original source and actual compiler records. -/
structure FaultReady (f : Clif.Function) (result : Stock.Result) (env : Clif.Env) (cp : Clif.Program)
    (fr : Clif.Frame) (cm : Clif.Mem) (Γ : Rel) (fc : FnCtx) (X : ExtSem)
    (initial : Arm.ArmState) (trap : Clif.TrapCode) where
  block : VBlock
  placed : result.code.blocks[0]? = some block
  prelude : List MInst
  suffix : List MInst
  seed : Nat → CV
  values : Nat → CV
  pointer : Nat
  argument : Nat
  called : Nat
  separate : pointer ≠ called
  ext : Clif.ExtFunc
  member : ext ∈ f.externs.map (·.2)
  returned : Clif.AbiParam
  returns : ext.sig.returns = [returned]
  callee : List Clif.Val → Clif.Mem → Clif.Outcome
  found : env.extern ext.name = some callee
  liveWord : BitVec 64
  returnedWord : BitVec 64
  after : Clif.Mem
  sourceReturned : callee [⟨.i64,liveWord⟩] cm = .returned [⟨.i64,returnedWord⟩] after
  flags : Clif.MemFlags
  pointerValue : Clif.Val
  pointerType : pointerValue.ty = .i64
  pointerHeld : VHolds pointerValue (values pointer)
  invalid : after.valid (Clif.effAddr pointerValue 8) 8 = false
  flag : flags.trapCode = some trap
  sourceState : Clif.State
  sourceReached : Reach env cp ⟨fr,[],cm⟩ sourceState
  sourceTrap : Clif.MemTrapAt env cp sourceState trap (Clif.effAddr pointerValue 8) 8
  liveHeld : VHolds ⟨.i64,liveWord⟩ (values argument)
  arguments : ∀ world,ArgsAt ext.sig [⟨.i64,liveWord⟩] [values argument] world
  preRun : seqRun (ABIReadOnly.sem Γ.F fc X) prelude seed initial = some (.fall values initial)
  reads : ∀ j inst,prelude[j]? = some inst → Backend.ABIReadOnly.instruction f.sig 0 j inst = true
  code : block.insts.toList = (prelude ++
    [.call ⟨.sym ext.name,retPairs [(argument,.x 0)],callDefs [(.x 0,called)]⟩,
     .store .store64 (.vreg called .int) (.unsignedOffset (.vreg pointer .int) 8) flags,
     .rets (retPairs [(called,.x 0)])]) ++ suffix
  retABI : ReturnABI f (retPairs [(called,.x 0)])

/-- The original entry and complete source run derive every internal call-entry fact. -/
theorem Layout.fault_ready {f : Clif.Function} {result : Stock.Result}
    (layout : Layout f result) (run : Stock.lower f = .ok result)
    (scope : LowerScope f) (dominated : Dominated f) {env : Clif.Env} {cp : Clif.Program}
    (subset : InSubset cp f) {args : List Clif.Val} {fr : Clif.Frame} {cm : Clif.Mem}
    (entered : SourceEntry f args fr) {fuel : Nat} {trap : Clif.TrapCode}
    (trapped : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .trapped trap)
    {Γ : Rel} {fc : FnCtx} {X : ExtSem} {c : BitVec 64}
    (slot : fc.slotBase = Γ.slotOff)
    (symbols : ∀ n b,Γ.syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    {w : Arm.ArmState} (memory : RelW Γ f c fr.slots cm w)
    (arguments : ArgsAtEntry Γ.F f.sig args w) :
    instOutcome env cp fr cm (.call layout.data.fn [layout.data.argument]) = .trap trap ∨
      Nonempty (FaultReady f result env cp fr cm Γ fc X w trap) := by
  obtain ⟨blocks,parameters,body,term,params,returns,calleeParams,calleeReturns,integer,lookup,pins,
    sourceSeparate,argumentCalled,pointerArgument,flags,parameterBytes⟩ := layout.source_fields
  rcases layout.source_fault subset entered trapped with callTrap |
      ⟨g,liveWord,returnedWord,after,pointerValue,callee,read,called,pointerRead,pointerType,invalid,flag⟩
  · exact .inl callTrap
  apply Or.inr
  obtain ⟨event,block,prelude,tail,ρ,w1,events,entryBlock,placed,parts,preRun,mem1,values,same,noCalls,suffix,tailEq⟩ :=
    stock_lower_entry_prelude_refines_nocall_frame run scope dominated entered
      (ABIReadOnly.driver Γ.F fc X) (ABIReadOnly.memory Γ.F fc X slot symbols)
      (mrStable_relW Γ f c) memory arguments
  have reads := prelude_read_checks layout.reads placed parts noCalls
  have sourceEntry := entered
  obtain ⟨b,regs,found,types,paramTypes,set,frame⟩ := sourceEntry
  have inputTypes : args.map (·.ty) = f.sig.params.map (·.ty) := by
    simpa only [Clif.AbiParam.tys] using types
  have fixed := (ABIReadOnly.seqRun_fall_transport inputTypes (SameWorld.refl Γ.F w)
    (fun _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
    (b := 0) (start := 0) (by simpa only [Nat.zero_add] using reads) preRun).1
  subst w1
  obtain ⟨scan,mappedPointer,mappedLive,mappedCall,code,callAlias,separate⟩ :=
    layout.scan_fields events entryBlock
  have held := VoidCall.entry_values_resolved run scope dominated events entered values
  let liveKey := aliasNum result.final.alias scan.argument
  let callKey := aliasNum result.final.alias scan.calledDestination
  let pointerKey := aliasNum result.final.alias scan.pointer
  have liveHeld : VHolds ⟨.i64,liveWord⟩ (ρ liveKey) := by
    have actual : AllHold [⟨.i64,liveWord⟩] [ρ liveKey] := by
      simpa only [List.map_cons,List.map_nil,VoidCall.sourceKey,mappedLive,liveKey] using
        VoidCall.call_values_hold held read
    exact actual.2 0 _ _ rfl rfl
  have pointerHeld : VHolds pointerValue (ρ pointerKey) := by
    obtain ⟨key,mapped,value⟩ := held layout.data.pointer trivial pointerValue pointerRead
    have same : key = scan.pointer := by simpa using mapped.symm.trans mappedPointer
    subst key
    exact value
  have sizes : sigParamBytes layout.data.ext.sig = .ok [8] := by
    cases decoded : sigParamBytes layout.data.ext.sig with
    | error message => rw [decoded] at parameterBytes; cases parameterBytes
    | ok bytes =>
      rw [decoded] at parameterBytes
      have exactBytes : bytes = [8] := Option.some.inj parameterBytes
      subst bytes
      rfl
  have arity : ([⟨.i64,liveWord⟩] : List Clif.Val).length = layout.data.ext.sig.params.length := by
    have count := congrArg List.length calleeParams
    simpa only [List.length_map,List.length_cons,List.length_nil] using count.symm
  have argsAt : ∀ world,ArgsAt layout.data.ext.sig [⟨.i64,liveWord⟩] [ρ liveKey] world := by
    intro world
    apply (argsAt_iff_of_regs sizes (by decide) arity).mpr
    refine ⟨rfl,?_⟩
    intro j val actual found atOutput
    cases j with
    | zero => cases found; cases atOutput; exact liveHeld
    | succ j => simp at found
  let resolve := Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)
  have codeEq : event.output.code.map (·.mapRegs resolve) = #[
      .call ⟨.sym layout.data.ext.name,retPairs [(liveKey,.x 0)],callDefs [(.x 0,callKey)]⟩,
      .store .store64 (.vreg callKey .int) (.unsignedOffset (.vreg pointerKey .int) 8) layout.data.flags,
      .rets (retPairs [(callKey,.x 0)])] := by
    rw [code]
    unfold aliasNum at callAlias
    simp [MInst.mapRegs,AMode.mapRegs,retPairs,callDefs,resolve,resolve_vreg,liveKey,callKey,pointerKey,aliasNum,callAlias]
  have blockList : block.insts.toList = (prelude.toList ++
      [.call ⟨.sym layout.data.ext.name,retPairs [(liveKey,.x 0)],callDefs [(.x 0,callKey)]⟩,
       .store .store64 (.vreg callKey .int) (.unsignedOffset (.vreg pointerKey .int) 8) layout.data.flags,
       .rets (retPairs [(callKey,.x 0)])]) ++ suffix.toList := by
    rw [parts,tailEq]
    change (prelude ++ (event.output.code.map (·.mapRegs resolve) ++ suffix)).toList = _
    rw [codeEq]
    simp only [Array.toList_append,Array.toList_push,Array.toList_empty,List.append_assoc]
  have first : f.entry? = some layout.data.block := by
    simp only [Clif.Function.entry?,blocks,List.head?_cons]
  cases Option.some.inj (found.symm.trans first)
  have func : fr.func = f := congrArg Clif.Frame.func frame
  have body' : fr.body = [⟨[layout.data.called],.call layout.data.fn [layout.data.argument]⟩,
      ⟨[],.store .store .i64 layout.data.flags layout.data.called layout.data.pointer 8⟩] :=
    (congrArg Clif.Frame.body frame).trans body
  have external : cp.func? layout.data.ext.name = none :=
    subset.externCalls layout.data.block (by simp [blocks])
      ⟨[layout.data.called],.call layout.data.fn [layout.data.argument]⟩ (by simp [body])
      layout.data.fn [layout.data.argument] rfl layout.data.ext lookup
  have callOk : instOutcome env cp fr cm (.call layout.data.fn [layout.data.argument]) =
      .ok ([⟨.i64,returnedWord⟩],after) := by
    simp [instOutcome,func,lookup,read,calleeParams,Clif.AbiParam.tys,Clif.checkTys,
      Clif.Res.ofOption,Clif.Res.bind,Clif.Res.check,external,callee,called,calleeReturns,integer]
  let frStore : Clif.Frame := {fr with regs := fr.regs.set layout.data.called ⟨.i64,returnedWord⟩,body := [⟨[],.store .store .i64 layout.data.flags layout.data.called layout.data.pointer 8⟩]}
  have step : Clif.step env cp ⟨fr,[],cm⟩ = .next ⟨frStore,[],after⟩ := by
    have actual := stepCall_eq env cp ⟨fr,[],cm⟩
      [⟨[],.store .store .i64 layout.data.flags layout.data.called layout.data.pointer 8⟩]
      [layout.data.called] layout.data.fn [layout.data.argument]
      (by intro ext found; rw [func,lookup] at found; cases found; exact external)
    rw [Clif.step,body']
    change Clif.stepCall env cp _ _ _ _ _ = _
    rw [actual,callOk]
    rfl
  have evaluated : Clif.evalInst frStore after
      (.store .store .i64 layout.data.flags layout.data.called layout.data.pointer 8) = .trap trap := by
    simp [Clif.evalInst,frStore,Clif.Frame.getAs,Clif.Frame.get,Clif.Regs.set,sourceSeparate,
      pointerRead,Clif.Res.ofOption,Clif.Val.as?,Clif.StoreOp.size,Clif.Ty.bytes,Clif.Ty.width,
      Clif.Res.check,Clif.Mem.store,Clif.Mem.checkAccess,invalid,flag]
  have memoryTrap : Clif.MemTrapAt env cp ⟨frStore,[],after⟩ trap (Clif.effAddr pointerValue 8) 8 := by
    refine ⟨?_,invalid,⟨⟨[],.store .store .i64 layout.data.flags layout.data.called layout.data.pointer 8⟩,[],rfl,?_⟩⟩
    · have actual := Clif.step_inst env cp ⟨frStore,[],after⟩
        ⟨[],.store .store .i64 layout.data.flags layout.data.called layout.data.pointer 8⟩ [] rfl
        (by intro fn args impossible; cases impossible) (by intro sig fn args impossible; cases impossible)
      rw [actual]
      change Clif.StepResult.ofRes (Clif.evalInst _ _ _) _ = _
      rw [evaluated]
      rfl
    · apply Clif.Access.store
      simp [frStore,Clif.Frame.get,Clif.Regs.set,sourceSeparate,pointerRead,Clif.Res.ofOption]
  refine ⟨{
    block := block
    placed := placed
    prelude := prelude.toList
    suffix := suffix.toList
    seed := entrySeed event.ctx fr
    values := ρ
    pointer := pointerKey
    argument := liveKey
    called := callKey
    separate := separate
    ext := layout.data.ext
    member := externsIn_self f layout.data.fn layout.data.ext lookup
    returned := layout.data.returned
    returns := calleeReturns
    callee := g
    found := callee
    liveWord := liveWord
    returnedWord := returnedWord
    after := after
    sourceReturned := called
    flags := layout.data.flags
    pointerValue := pointerValue
    pointerType := pointerType
    pointerHeld := pointerHeld
    invalid := invalid
    flag := flag
    sourceState := ⟨frStore,[],after⟩
    sourceReached := .step step (.refl _)
    sourceTrap := memoryTrap
    liveHeld := liveHeld
    arguments := argsAt
    preRun := preRun
    reads := reads
    code := blockList
    retABI := ?_ }⟩
  simpa only [ReturnABI,retPairs,List.map_cons,List.map_nil,List.length_cons,List.length_nil] using pins

end Backend.Stock.CallStore
