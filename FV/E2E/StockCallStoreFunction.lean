import FV.E2E.StockCallStoreSourceResult
import FV.E2E.StockCallStoreTail
import FV.Backend.Proof.StockCallStoreAddress
import FV.Backend.Proof.RefinesCSem

namespace Backend.Stock.CallStore
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof E2E
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- The return/store contract keeps arbitrary callee effects and derives the store from the source run. -/
theorem Layout.return_function_for {f : Clif.Function} {result : Stock.Result}
    (layout : Layout f result) (run : Stock.lower f = .ok result)
    (scope : LowerScope f) (dominated : Dominated f) {env : Clif.Env} {cp : Clif.Program}
    (subset : InSubset cp f) {args : List Clif.Val} {fr : Clif.Frame} {cm outMem : Clif.Mem}
    (entered : SourceEntry f args fr) {fuel : Nat} {vals : List Clif.Val}
    (returned : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .returned vals outMem)
    {F : BitVec 64 → Prop} {X : ExtSem} {MR : MemRelT}
    {isem : Sem} (refines : Refines F isem) (driver : DriverSem isem)
    (callSem : ∀ (name : String) (pairs : List (Nat × Reg)) (defs : List (Reg × Nat)) uses world,
      isem (.call ⟨.sym name,retPairs pairs,callDefs defs⟩) uses world =
        (X.call (some name) uses world).map (fun pair => (pair.1.take (callDefs defs).length,pair.2,Ctl.next)))
    (retSem : ∀ (us : List (Reg × Reg)) uses world,isem (.rets us) uses world = some ([],world,.ret))
    (calls : XCallsOk env (f.externs.map (·.2)) MR X)
    (stable : MRStable F MR) {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms isem) (memoryOk : MemRelOk F sb syms f MR)
    {w : Arm.ArmState} (memory : MR fr.slots cm w) (arguments : ArgsAtEntry F f.sig args w) :
    ∃ ρ,RunOkABI f result.code isem MR fr.slots ⟨0,0,ρ,w⟩ (.returned vals outMem) := by
  obtain ⟨blocks,parameters,body,term,params,returns,calleeParams,calleeReturns,integer,lookup,pins,
    pointerCalled,argumentCalled,pointerArgument,flags,parameterBytes⟩ := layout.source_fields
  obtain ⟨g,argumentWord,returnedWord,after,stored,pointer,callee,read,called,pointerRead,
    pointerType,evaluated,equal,freed⟩ := layout.source_result subset entered returned
  subst vals
  obtain ⟨event,block,prelude,tail,ρ,w1,events,entryBlock,placed,parts,preRun,mem1,values,same,suffix,tailEq⟩ :=
    stock_lower_entry_prelude_refines_frame run scope dominated entered driver memorySem stable memory arguments
  obtain ⟨scan,mappedPointer,mappedArgument,mappedCall,code,callAlias,separate⟩ :=
    layout.scan_fields events entryBlock
  have held := VoidCall.entry_values_resolved run scope dominated events entered values
  let pointerKey := aliasNum result.final.alias scan.pointer
  let argumentKey := aliasNum result.final.alias scan.argument
  let callKey := aliasNum result.final.alias scan.calledDestination
  have pointerHeld : VHolds pointer (ρ pointerKey) := by
    obtain ⟨key,mapped,value⟩ := held layout.data.pointer trivial pointer pointerRead
    have same : key = scan.pointer := by simpa using mapped.symm.trans mappedPointer
    subst key
    exact value
  have argumentHeld : VHolds ⟨.i64,argumentWord⟩ (ρ argumentKey) := by
    have actual : AllHold [⟨.i64,argumentWord⟩] [ρ argumentKey] := by
      simpa only [List.map_cons,List.map_nil,VoidCall.sourceKey,mappedArgument,argumentKey] using
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
  have arity : ([⟨.i64,argumentWord⟩] : List Clif.Val).length = layout.data.ext.sig.params.length := by
    have count := congrArg List.length calleeParams
    simpa only [List.length_map,List.length_cons,List.length_nil] using count.symm
  have argsAt : ArgsAt layout.data.ext.sig [⟨.i64,argumentWord⟩] [ρ argumentKey] w1 := by
    apply (argsAt_iff_of_regs sizes (by decide) arity).mpr
    refine ⟨rfl,?_⟩
    intro j val actual found atOutput
    cases j with
    | zero => cases found; cases atOutput; exact argumentHeld
    | succ j => simp at found
  have member : layout.data.ext ∈ f.externs.map (·.2) :=
    externsIn_self f layout.data.fn layout.data.ext lookup
  obtain ⟨actual,w2,callRun,resultCount,resultHeld,mem2⟩ := calls layout.data.ext member g fr.slots cm w1
    (some layout.data.ext.name) [ρ argumentKey] [ρ argumentKey] [⟨.i64,argumentWord⟩]
    [⟨.i64,returnedWord⟩] after callee (Or.inl ⟨rfl,rfl⟩) argsAt mem1 called
    (by rw [calleeReturns]; rfl)
  rw [calleeReturns] at resultCount
  cases actual with
  | nil => cases resultCount
  | cons output rest =>
    have empty : rest = [] := by simpa using resultCount
    subst rest
    have resultValue : VHolds ⟨.i64,returnedWord⟩ output := resultHeld.2 0 _ _ rfl rfl
    have step : isem
        (.call ⟨.sym layout.data.ext.name,retPairs [(argumentKey,.x 0)],callDefs [(.x 0,callKey)]⟩)
        ([(argumentKey,Reg.x 0)].map (ρ ·.1)) w1 = some ([output],w2,.next) := by
      rw [callSem]
      change (X.call (some layout.data.ext.name) [ρ argumentKey] w1).map
        (fun pair => (pair.1.take 1,pair.2,Ctl.next)) = _
      rw [callRun]
      rfl
    let resolve := Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)
    have codeEq : event.output.code.map (·.mapRegs resolve) = #[
        .call ⟨.sym layout.data.ext.name,retPairs [(argumentKey,.x 0)],callDefs [(.x 0,callKey)]⟩,
        .store .store64 (.vreg callKey .int) (.unsignedOffset (.vreg pointerKey .int) 8) layout.data.flags,
        .rets (retPairs [(callKey,.x 0)])] := by
      rw [code]
      unfold aliasNum at callAlias
      simp [MInst.mapRegs,AMode.mapRegs,retPairs,callDefs,resolve,resolve_vreg,
        pointerKey,argumentKey,callKey,aliasNum,callAlias]
    have blockList : block.insts.toList = (prelude.toList ++
        [.call ⟨.sym layout.data.ext.name,retPairs [(argumentKey,.x 0)],callDefs [(.x 0,callKey)]⟩,
         .store .store64 (.vreg callKey .int) (.unsignedOffset (.vreg pointerKey .int) 8) layout.data.flags,
         .rets (retPairs [(callKey,.x 0)])]) ++ suffix.toList := by
      rw [parts,tailEq]
      change (prelude ++ (event.output.code.map (·.mapRegs resolve) ++ suffix)).toList = _
      rw [codeEq]
      simp only [Array.toList_append,Array.toList_push,Array.toList_empty,List.append_assoc]
    let sourceAfter : Clif.Frame := {fr with regs := fr.regs.set layout.data.called ⟨.i64,returnedWord⟩,body := [⟨[],.store .store .i64 layout.data.flags layout.data.called layout.data.pointer 8⟩]}
    have valueHeld : ∀ bits,sourceAfter.getAs layout.data.called .i64 = .ok bits →
        VHolds ⟨.i64,bits⟩ output := by
      intro bits found
      have actual : sourceAfter.getAs layout.data.called .i64 = .ok returnedWord := by
        simp [sourceAfter,Clif.Frame.getAs,Clif.Frame.get,Clif.Regs.set,
          Clif.Res.ofOption,Clif.Val.as?]
      have equal := Clif.Res.ok.inj (actual.symm.trans found)
      subst bits
      exact resultValue
    have address : ∀ pv,sourceAfter.regs layout.data.pointer = some pv →
        amodeAddr sb (.unsignedOffset (.vreg pointerKey .int) 8) 8 [ρ pointerKey] w2 =
          some (BitVec.ofNat 64 (Clif.effAddr pv 8)) := by
      intro pv found
      have expected : sourceAfter.regs layout.data.pointer = some pointer := by
        simpa only [sourceAfter,Clif.Regs.set,pointerCalled,↓reduceIte] using pointerRead
      have equal : pv = pointer := Option.some.inj (found.symm.trans expected)
      subst pv
      exact CallStoreResult.pointer_address pointerHeld pointerType w2
    have little : layout.data.flags.endianness ≠ some .big := by rw [flags]; decide
    obtain ⟨pv,w3,pointerFound,reached,world,mem3⟩ := execute_tail stable
      (Stock.Memory.store_refines_of_mem memorySem) memoryOk retSem placed separate blockList preRun step
      (fr := sourceAfter) mem2 little valueHeld address evaluated
    refine ⟨entrySeed event.ctx fr,retPairs [(callKey,.x 0)],[output],w3,stored,reached,?_,rfl,?_,mem3,freed⟩
    · have ordinary : (sigRets f.sig).any (·.purpose == .sret) = false := by
        cases sret : (sigRets f.sig).any (·.purpose == .sret) with
        | false => rfl
        | true => simp [returnPins,sret] at pins
      refine ⟨?_,by simp [retPairs,sretRet_nil_of_ordinary ordinary]⟩
      simpa only [ReturnABI,retPairs,List.map_cons,List.map_nil,List.length_cons,List.length_nil] using pins
    · refine ⟨Nat.le_refl _,?_⟩
      intro j val actual found atOutput
      cases j with
      | zero => cases found; cases atOutput; exact resultValue
      | succ j => simp at found

/-- This wrapper keeps the existing call and memory premises and claims only returned executions. -/
theorem Layout.return_function {f : Clif.Function} {result : Stock.Result}
    (layout : Layout f result) (run : Stock.lower f = .ok result)
    (scope : LowerScope f) (dominated : Dominated f) {env : Clif.Env} {cp : Clif.Program}
    (subset : InSubset cp f) {args : List Clif.Val} {fr : Clif.Frame} {cm outMem : Clif.Mem}
    (entered : SourceEntry f args fr) {fuel : Nat} {vals : List Clif.Val}
    (returned : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .returned vals outMem)
    {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {MR : MemRelT}
    (calls : XCallsOk env (f.externs.map (·.2)) MR X) (stable : MRStable F MR)
    {sb : Nat} {syms : String → Option Nat} (memorySem : MemRefines F sb syms (csem F ctx X))
    (memoryOk : MemRelOk F sb syms f MR)
    {w : Arm.ArmState} (memory : MR fr.slots cm w) (arguments : ArgsAtEntry F f.sig args w) :
    ∃ ρ,RunOkABI f result.code (csem F ctx X) MR fr.slots ⟨0,0,ρ,w⟩ (.returned vals outMem) := by
  exact layout.return_function_for run scope dominated subset entered returned
    (refines_csem F ctx X) (driverSem_csem F ctx X) (fun _ _ _ _ _ => rfl)
    (fun _ _ _ => rfl) calls stable memorySem memoryOk memory arguments

end Backend.Stock.CallStore
