import FV.E2E.StockLiveCallSourceResult
import FV.E2E.StockLiveCallPrelude
import FV.Backend.Proof.RefinesCSem

namespace Backend.Stock.LiveCall
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof E2E
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- Original source, retained binders, call contracts, and existing addition semantics compose with arbitrary callee effects. -/
theorem Layout.return_function_for {f : Clif.Function} {result : Stock.Result}
    (layout : Layout f result) (run : Stock.lower f = .ok result)
    (scope : LowerScope f) (dominated : Dominated f) {env : Clif.Env} {cp : Clif.Program}
    (subset : InSubset cp f) {args : List Clif.Val} {fr : Clif.Frame} {cm outMem : Clif.Mem}
    (entered : SourceEntry f args fr) {fuel : Nat} {vals : List Clif.Val}
    (returned : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .returned vals outMem)
    {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {MR : MemRelT}
    {isem : Sem} (refines : Refines F isem) (driver : DriverSem isem)
    (callSem : ∀ (name : String) (pairs : List (Nat × Reg)) (defs : List (Reg × Nat)) uses world,
      isem (.call ⟨.sym name,retPairs pairs,callDefs defs⟩) uses world =
        (X.call (some name) uses world).map (fun pair => (pair.1,pair.2,Ctl.next)))
    (retSem : ∀ (us : List (Reg × Reg)) uses world,isem (.rets us) uses world = some ([],world,.ret))
    (calls : XCallsOk env (f.externs.map (·.2)) MR X)
    (stable : MRStable F MR) {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms isem)
    {w : Arm.ArmState} (memory : MR fr.slots cm w) (arguments : ArgsAtEntry F f.sig args w) :
    ∃ ρ,RunOkABI f result.code isem MR fr.slots ⟨0,0,ρ,w⟩ (.returned vals outMem) := by
  obtain ⟨blocks,parameters,body,term,params,returns,calleeParams,calleeReturns,integer,lookup,pins,
    sourceSeparate,sumCalled,sumLive,parameterBytes⟩ := layout.source_fields
  obtain ⟨g,live,returnedWord,after,callee,read,called,equal,freed⟩ := layout.source_result subset entered returned
  subst vals
  obtain ⟨event,block,prelude,tail,ρ,w1,events,entryBlock,placed,parts,preRun,mem1,values,same,suffix,tailEq⟩ :=
    stock_lower_entry_prelude_refines_frame run scope dominated entered
      driver memorySem stable memory arguments
  obtain ⟨scan,mappedLive,mappedCall,mappedSum,code,callAlias,sumAlias,separate⟩ :=
    layout.scan_fields events entryBlock
  have held := VoidCall.entry_values_resolved run scope dominated events entered values
  let liveKey := aliasNum result.final.alias scan.live
  let callKey := aliasNum result.final.alias scan.calledDestination
  let sumKey := aliasNum result.final.alias scan.sumDestination
  have liveHeld : VHolds ⟨.i64,live⟩ (ρ liveKey) := by
    have actual : AllHold [⟨.i64,live⟩] [ρ liveKey] := by
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
  have arity : ([⟨.i64,live⟩] : List Clif.Val).length = layout.data.ext.sig.params.length := by
    have count := congrArg List.length calleeParams
    simpa only [List.length_map,List.length_cons,List.length_nil] using count.symm
  have argsAt : ArgsAt layout.data.ext.sig [⟨.i64,live⟩] [ρ liveKey] w1 := by
    apply (argsAt_iff_of_regs sizes (by decide) arity).mpr
    refine ⟨rfl,?_⟩
    intro j val actual found atOutput
    cases j with
    | zero => cases found; cases atOutput; exact liveHeld
    | succ j => simp at found
  have member : layout.data.ext ∈ f.externs.map (·.2) :=
    externsIn_self f layout.data.fn layout.data.ext lookup
  obtain ⟨actual,w2,callRun,resultCount,resultHeld,mem2⟩ := calls layout.data.ext member g fr.slots cm w1
    (some layout.data.ext.name) [ρ liveKey] [ρ liveKey] [⟨.i64,live⟩] [⟨.i64,returnedWord⟩] after callee
    (Or.inl ⟨rfl,rfl⟩) argsAt mem1 called (by rw [calleeReturns]; rfl)
  have abi : sigRets layout.data.ext.sig = [layout.data.returned] := by
    unfold sigRets
    split <;> simp [calleeReturns]
  rw [abi] at resultCount
  cases actual with
  | nil => cases resultCount
  | cons output rest =>
    have empty : rest = [] := by simpa using resultCount
    subst rest
    have resultValue : VHolds ⟨.i64,returnedWord⟩ output := resultHeld.2 0 _ _ rfl rfl
    have step : csem F ctx X
        (.call ⟨.sym layout.data.ext.name,retPairs [(liveKey,.x 0)],callDefs [(.x 0,callKey)]⟩)
        ([(liveKey,Reg.x 0)].map (ρ ·.1)) w1 = some ([output],w2,.next) := by
      rw [callSem]
      change (X.call (some layout.data.ext.name) [ρ liveKey] w1).map
        (fun pair => (pair.1,pair.2,Ctl.next)) = _
      rw [callRun]
      rfl
    obtain ⟨w3,callAdd,world⟩ := LiveCallArithmetic.call_then_add refines
      (by exact separate) (sum := sumKey) step
    let sumValue := resX .size64 (opnd .size64 output + opnd .size64 (ρ liveKey))
    let updated := upd (fun key => if key = callKey then output else ρ key) sumKey sumValue
    have mem3 : MR fr.slots after w3 := stable _ _ _ _ world.nf mem2
    have sumHeld : VHolds ⟨.i64,returnedWord+live⟩ sumValue :=
      LiveCallArithmetic.sum_holds resultValue liveHeld
    have machineReturn : seqRun isem [.rets (retPairs [(sumKey,.x 0)])] updated w3 =
        some (.stop 0 (.rets (retPairs [(sumKey,.x 0)]))
          (retOps [(sumKey,.x 0)]).toArray updated w3 [] w3 .ret) := by
      simp [seqRun,operands_rets,retSem,retOps,Operand.isDef]
    have bodyRun := seqRun_append_fall_stop isem callAdd machineReturn
    have complete := seqRun_append_fall_stop isem preRun bodyRun
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
    have segment : SegAt block 0 (prelude.toList ++
        [.call ⟨.sym layout.data.ext.name,retPairs [(liveKey,.x 0)],callDefs [(.x 0,callKey)]⟩,
         .aluRRR .add .size64 (.vreg sumKey .int) (.vreg callKey .int) (.vreg liveKey .int),
         .rets (retPairs [(sumKey,.x 0)])]) :=
      segAt_of_toList (L₁ := []) (by simpa only [List.nil_append] using blockList)
    obtain ⟨path,_,instruction,operands,ran,_,_⟩ := seqRun_stop_star placed segment complete
    refine ⟨entrySeed event.ctx fr,retPairs [(sumKey,.x 0)],[sumValue],w3,after,?_,?_,rfl,?_,mem3,freed⟩
    · refine ⟨0,_,updated,w3,block,(retOps [(sumKey,.x 0)]).toArray,[],path,placed,instruction,rfl,?_,rfl⟩
      simp [vuses_retOps,updated,upd]
    · simpa only [ReturnABI,retPairs,List.map_cons,List.map_nil,List.length_cons,List.length_nil] using pins
    · refine ⟨Nat.le_refl _,?_⟩
      intro j val actual found atOutput
      cases j with
      | zero => cases found; cases atOutput; exact sumHeld
      | succ j => simp at found


theorem Layout.return_function {f : Clif.Function} {result : Stock.Result}
    (layout : Layout f result) (run : Stock.lower f = .ok result)
    (scope : LowerScope f) (dominated : Dominated f) {env : Clif.Env} {cp : Clif.Program}
    (subset : InSubset cp f) {args : List Clif.Val} {fr : Clif.Frame} {cm outMem : Clif.Mem}
    (entered : SourceEntry f args fr) {fuel : Nat} {vals : List Clif.Val}
    (returned : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .returned vals outMem)
    {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {MR : MemRelT}
    (calls : XCallsOk env (f.externs.map (·.2)) MR X)
    (stable : MRStable F MR) {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms (csem F ctx X))
    {w : Arm.ArmState} (memory : MR fr.slots cm w) (arguments : ArgsAtEntry F f.sig args w) :
    ∃ ρ,RunOkABI f result.code (csem F ctx X) MR fr.slots ⟨0,0,ρ,w⟩ (.returned vals outMem) := by
  exact layout.return_function_for run scope dominated subset entered returned
    (refines_csem F ctx X) (driverSem_csem F ctx X)
    (fun _ _ _ _ _ => rfl) (fun _ _ _ => rfl) calls stable memorySem memory arguments

end Backend.Stock.LiveCall
