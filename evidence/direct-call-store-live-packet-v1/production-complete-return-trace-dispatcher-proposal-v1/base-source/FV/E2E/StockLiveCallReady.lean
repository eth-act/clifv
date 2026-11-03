import FV.E2E.StockLiveCallSourceResult
import FV.E2E.StockLiveCallPrelude
import FV.E2E.ABIReadOnlyMachine

namespace Backend.Stock.LiveCall
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof E2E
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- Internal call-entry facts come from the original source and actual compiler records. -/
structure Ready (f : Clif.Function) (result : Stock.Result) (env : Clif.Env)
    (fr : Clif.Frame) (cm outMem : Clif.Mem) (Γ : Rel) (fc : FnCtx) (X : ExtSem)
    (initial : Arm.ArmState) where
  block : VBlock
  placed : result.code.blocks[0]? = some block
  prelude : List MInst
  suffix : List MInst
  seed : Nat → CV
  values : Nat → CV
  live : Nat
  called : Nat
  sum : Nat
  separate : live ≠ called
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
  freed : outMem = (after.free (fr.slots.map (·.2))).leave
  liveHeld : VHolds ⟨.i64,liveWord⟩ (values live)
  arguments : ∀ world,ArgsAt ext.sig [⟨.i64,liveWord⟩] [values live] world
  preRun : seqRun (ABIReadOnly.sem Γ.F fc X) prelude seed initial = some (.fall values initial)
  reads : ∀ j inst,prelude[j]? = some inst → Backend.ABIReadOnly.instruction f.sig 0 j inst = true
  code : block.insts.toList = (prelude ++
    [.call ⟨.sym ext.name,retPairs [(live,.x 0)],callDefs [(.x 0,called)]⟩,
     .aluRRR .add .size64 (.vreg sum .int) (.vreg called .int) (.vreg live .int),
     .rets (retPairs [(sum,.x 0)])]) ++ suffix
  retABI : ReturnABI f (retPairs [(sum,.x 0)])

/-- The original entry and complete source run derive every internal call-entry fact. -/
theorem Layout.ready {f : Clif.Function} {result : Stock.Result}
    (layout : Layout f result) (run : Stock.lower f = .ok result)
    (scope : LowerScope f) (dominated : Dominated f) {env : Clif.Env} {cp : Clif.Program}
    (subset : InSubset cp f) {args : List Clif.Val} {fr : Clif.Frame} {cm outMem : Clif.Mem}
    (entered : SourceEntry f args fr) {fuel : Nat} {vals : List Clif.Val}
    (returned : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .returned vals outMem)
    {Γ : Rel} {fc : FnCtx} {X : ExtSem} {c : BitVec 64}
    (slot : fc.slotBase = Γ.slotOff)
    (symbols : ∀ n b,Γ.syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    {w : Arm.ArmState} (memory : RelW Γ f c fr.slots cm w)
    (arguments : ArgsAtEntry Γ.F f.sig args w) :
    ∃ ready : Ready f result env fr cm outMem Γ fc X w,
      vals = [⟨.i64,ready.returnedWord+ready.liveWord⟩] := by
  obtain ⟨blocks,parameters,body,term,params,returns,calleeParams,calleeReturns,integer,lookup,pins,
    sourceSeparate,sumCalled,sumLive,parameterBytes⟩ := layout.source_fields
  obtain ⟨g,liveWord,returnedWord,after,callee,read,called,equal,freed⟩ := layout.source_result subset entered returned
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
  obtain ⟨scan,mappedLive,mappedCall,mappedSum,code,callAlias,sumAlias,separate⟩ :=
    layout.scan_fields events entryBlock
  have held := VoidCall.entry_values_resolved run scope dominated events entered values
  let liveKey := aliasNum result.final.alias scan.live
  let callKey := aliasNum result.final.alias scan.calledDestination
  let sumKey := aliasNum result.final.alias scan.sumDestination
  have liveHeld : VHolds ⟨.i64,liveWord⟩ (ρ liveKey) := by
    have actual : AllHold [⟨.i64,liveWord⟩] [ρ liveKey] := by
      simpa only [List.map_cons,List.map_nil,VoidCall.sourceKey,mappedLive,liveKey] using
        VoidCall.call_values_hold held read
    exact actual.2 0 _ _ rfl rfl
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
      .aluRRR .add .size64 (.vreg sumKey .int) (.vreg callKey .int) (.vreg liveKey .int),
      .rets (retPairs [(sumKey,.x 0)])] := by
    rw [code]
    unfold aliasNum at callAlias sumAlias
    simp [MInst.mapRegs,retPairs,callDefs,resolve,resolve_vreg,liveKey,callKey,sumKey,aliasNum,callAlias,sumAlias]
  have blockList : block.insts.toList = (prelude.toList ++
      [.call ⟨.sym layout.data.ext.name,retPairs [(liveKey,.x 0)],callDefs [(.x 0,callKey)]⟩,
       .aluRRR .add .size64 (.vreg sumKey .int) (.vreg callKey .int) (.vreg liveKey .int),
       .rets (retPairs [(sumKey,.x 0)])]) ++ suffix.toList := by
    rw [parts,tailEq]
    change (prelude ++ (event.output.code.map (·.mapRegs resolve) ++ suffix)).toList = _
    rw [codeEq]
    simp only [Array.toList_append,Array.toList_push,Array.toList_empty,List.append_assoc]
  refine ⟨{
    block := block
    placed := placed
    prelude := prelude.toList
    suffix := suffix.toList
    seed := entrySeed event.ctx fr
    values := ρ
    live := liveKey
    called := callKey
    sum := sumKey
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
    freed := freed
    liveHeld := liveHeld
    arguments := argsAt
    preRun := preRun
    reads := reads
    code := blockList
    retABI := ?_ },equal⟩
  simpa only [ReturnABI,retPairs,List.map_cons,List.map_nil,List.length_cons,List.length_nil] using pins

end Backend.Stock.LiveCall
