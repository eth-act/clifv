import FV.E2E.StockResultCallRun

namespace Backend.Stock.ResultCall
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof E2E
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- The original explicit-trap condition excludes hidden callee traps in this call class. -/
theorem source_call_notrap {env : Clif.Env} {cp : Clif.Program} {fr : Clif.Frame}
    {cm : Clif.Mem} {fn : Clif.FnRef} {args : List Nat} {source : Nat}
    (body : fr.body = [⟨[source],.call fn args⟩]) (term : fr.term = .ret [source])
    (external : ∀ e,fr.func.extern? fn = some e → cp.func? e.name = none)
    (explicit : TrapsExplicit env cp ⟨fr,[],cm⟩) (fuel : Nat) (code : Clif.TrapCode) :
    Clif.runLoop env cp fuel ⟨fr,[],cm⟩ ≠ .trapped code := by
  intro trapped
  cases fuel with
  | zero => cases trapped
  | succ fuel =>
    have step : Clif.step env cp ⟨fr,[],cm⟩ =
        Clif.StepResult.ofRes (instOutcome env cp fr cm (.call fn args))
          (fun pair => Clif.continueWith ⟨fr,[],cm⟩ [] [source] pair.1 pair.2) := by
      simp only [Clif.step,body]
      exact stepCall_eq env cp ⟨fr,[],cm⟩ [] [source] fn args external
    rw [Clif.runLoop_succ,step] at trapped
    cases outcome : instOutcome env cp fr cm (.call fn args) with
    | trap c =>
      have halted : Clif.step env cp ⟨fr,[],cm⟩ = .trapped c := by rw [step,outcome]; rfl
      have impossible := explicit.stmt ⟨fr,[],cm⟩ c ⟨[source],.call fn args⟩ [] (.refl _) halted body
      cases impossible
    | stuck message => simp only [outcome,Clif.StepResult.ofRes] at trapped; cases trapped
    | ok pair =>
      obtain ⟨results,after⟩ := pair
      cases results with
      | nil =>
        simp only [outcome,Clif.StepResult.ofRes,Clif.continueWith,Clif.Regs.setMany] at trapped
        cases trapped
      | cons value rest =>
        cases rest with
        | nil =>
          simp only [outcome,Clif.StepResult.ofRes,Clif.continueWith,Clif.Regs.setMany] at trapped
          exact OrdinaryBody.ordinary_source_notrap fuel
            ⟨{fr with body := [],regs := fr.regs.set source value},[],after⟩ rfl
            (by intro statement member; cases member) term code trapped
        | cons next tail =>
          simp only [outcome,Clif.StepResult.ofRes,Clif.continueWith,Clif.Regs.setMany] at trapped
          cases trapped

/-- The generic memory relation can describe any actual callee effect. -/
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
  obtain ⟨blocks,body,term,returns,calleeReturns,integer,lookup,sizes,registers,pins⟩ := layout.source_fields
  obtain ⟨g,sourceArgs,after,value,callee,read,argTypes,called,valueType,equal,freed⟩ :=
    layout.source_result subset entered returned
  subst vals
  obtain ⟨event,block,prelude,tail,ρ,w1,events,entryBlock,placed,parts,preRun,mem1,values,same,suffix,tailEq⟩ :=
    stock_lower_entry_prelude_refines_frame run scope dominated entered
      (driverSem_csem F ctx X) memorySem stable memory arguments
  have held := VoidCall.entry_values_resolved run scope dominated events entered values
  let inputValues := layout.data.args.map
    (fun x => ρ (aliasNum result.final.alias (VoidCall.sourceKey event.ctx x)))
  have holds : AllHold sourceArgs inputValues := VoidCall.call_values_hold held read
  have arity : sourceArgs.length = layout.data.ext.sig.params.length := by
    have count := congrArg List.length argTypes
    simpa only [Clif.AbiParam.tys,List.length_map] using count
  have argsAt : ArgsAt layout.data.ext.sig sourceArgs inputValues w1 :=
    (argsAt_iff_of_regs sizes registers arity).mpr holds
  have member : layout.data.ext ∈ f.externs.map (·.2) :=
    externsIn_self f layout.data.fn layout.data.ext lookup
  obtain ⟨actual,w2,callRun,resultCount,resultHeld,mem2⟩ := calls layout.data.ext member g fr.slots cm w1
    (some layout.data.ext.name) inputValues inputValues sourceArgs [value] after callee
    (Or.inl ⟨rfl,rfl⟩) argsAt mem1 called (by rw [calleeReturns]; rfl)
  rw [calleeReturns] at resultCount
  cases actual with
  | nil => cases resultCount
  | cons output rest =>
    have empty : rest = [] := by simpa using resultCount
    subst rest
    obtain ⟨root,destination,pairs,mapped,code,aliases,keys⟩ := layout.scan_fields events entryBlock
    let resolve := Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)
    let resolvedPairs := pairs.map (fun p => (aliasNum result.final.alias p.1,p.2))
    let resolvedDestination := aliasNum result.final.alias destination
    let updated := fun key => if key = resolvedDestination then output else ρ key
    have actualArgs : resolvedPairs.map (ρ ·.1) = inputValues := by
      simp only [resolvedPairs,List.map_map,Function.comp_def]
      calc
        pairs.map (fun p => ρ (aliasNum result.final.alias p.1)) =
            (pairs.map (·.1)).map (fun key => ρ (aliasNum result.final.alias key)) := by
              simp only [List.map_map,Function.comp_def]
        _ = inputValues := by rw [keys]; simp only [inputValues,List.map_map,Function.comp_def]
    have step : csem F ctx X
        (.call ⟨.sym layout.data.ext.name,retPairs resolvedPairs,callDefs [(.x 0,resolvedDestination)]⟩)
        (resolvedPairs.map (ρ ·.1)) w1 = some ([output],w2,.next) := by
      change (X.call (some layout.data.ext.name) (resolvedPairs.map (ρ ·.1)) w1).map
        (fun pair => (pair.1.take 1,pair.2,Ctl.next)) = _
      rw [actualArgs,callRun]
      rfl
    have machineCall : seqRun (csem F ctx X)
        [.call ⟨.sym layout.data.ext.name,retPairs resolvedPairs,callDefs [(.x 0,resolvedDestination)]⟩]
        ρ w1 = some (.fall updated w2) := by
      have execution := seqRun_call_sym step (show [output].length = [(.x 0,resolvedDestination)].length from rfl)
      have bound := DirectCallResult.virtual_result resolvedPairs resolvedDestination output ρ
      rw [vdefUpd_call] at bound
      rw [bound] at execution
      exact execution
    have machineReturn : seqRun (csem F ctx X) [.rets (retPairs [(resolvedDestination,.x 0)])] updated w2 =
        some (.stop 0 (.rets (retPairs [(resolvedDestination,.x 0)]))
          (retOps [(resolvedDestination,.x 0)]).toArray updated w2 [] w2 .ret) := by
      simp [seqRun,operands_rets,csem,retOps,Operand.isDef]
    have bodyRun := seqRun_append_fall_stop (csem F ctx X) machineCall machineReturn
    have complete := seqRun_append_fall_stop (csem F ctx X) preRun bodyRun
    have codeEq : event.output.code.map (·.mapRegs resolve) =
        #[.call ⟨.sym layout.data.ext.name,retPairs resolvedPairs,callDefs [(.x 0,resolvedDestination)]⟩,
          .rets (retPairs [(resolvedDestination,.x 0)])] := by
      rw [code]
      apply Array.toList_inj.mp
      have resolvedAliases := aliases
      unfold aliasNum at resolvedAliases
      simp [MInst.mapRegs,retPairs,callDefs,resolve,resolve_vreg,resolvedPairs,resolvedDestination,
        aliasNum,resolvedAliases]
    have blockList : block.insts.toList = (prelude.toList ++
        [.call ⟨.sym layout.data.ext.name,retPairs resolvedPairs,callDefs [(.x 0,resolvedDestination)]⟩,
          .rets (retPairs [(resolvedDestination,.x 0)])]) ++ suffix.toList := by
      rw [parts,tailEq]
      change (prelude ++ (event.output.code.map (·.mapRegs resolve) ++ suffix)).toList = _
      rw [codeEq]
      simp only [Array.toList_append,Array.toList_push,Array.toList_empty,List.append_assoc]
    have segment : SegAt block 0 (prelude.toList ++
        [.call ⟨.sym layout.data.ext.name,retPairs resolvedPairs,callDefs [(.x 0,resolvedDestination)]⟩,
          .rets (retPairs [(resolvedDestination,.x 0)])]) :=
      segAt_of_toList (L₁ := []) (by simpa only [List.nil_append] using blockList)
    obtain ⟨path,_,instruction,operands,ran,_,_⟩ := seqRun_stop_star placed segment complete
    refine ⟨entrySeed event.ctx fr,retPairs [(resolvedDestination,.x 0)],[output],w2,after,?_,?_,rfl,
      resultHeld,mem2,freed⟩
    · refine ⟨0,0+(0+1+prelude.toList.length),updated,w2,block,
        (retOps [(resolvedDestination,.x 0)]).toArray,[],path,placed,instruction,rfl,?_,rfl⟩
      simp [vuses_retOps,updated]
    · have ordinary : (sigRets f.sig).any (·.purpose == .sret) = false := by
        cases sret : (sigRets f.sig).any (·.purpose == .sret) with
        | false => rfl
        | true => simp [returnPins,sret] at pins
      refine ⟨?_,by simp [retPairs,sretRet_nil_of_ordinary ordinary]⟩
      simpa only [ReturnABI,retPairs,List.map_cons,List.map_nil,List.length_cons,List.length_nil] using pins

/-- This function contract retains the original source execution and general callee memory relation. -/
structure Domain (f : Clif.Function) (vc : VCode) : Prop where
  scope : LowerScope f
  dominated : Dominated f
  abi : sigAbiOk f.sig = true
  lower : ∃ result,Stock.lower f = .ok result ∧ result.code = vc
  returns : ∀ {env : Clif.Env} {cp : Clif.Program},InSubset cp f →
    ∀ {args : List Clif.Val} {fr : Clif.Frame} {cm outMem : Clif.Mem},SourceEntry f args fr →
    ∀ {fuel : Nat} {vals : List Clif.Val},
      Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .returned vals outMem →
    ∀ {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {MR : MemRelT},
      XCallsOk env (f.externs.map (·.2)) MR X → MRStable F MR →
    ∀ {sb : Nat} {syms : String → Option Nat},MemRefines F sb syms (csem F ctx X) →
    ∀ {w : Arm.ArmState},MR fr.slots cm w → ArgsAtEntry F f.sig args w →
      ∃ ρ,RunOkABI f vc (csem F ctx X) MR fr.slots ⟨0,0,ρ,w⟩ (.returned vals outMem)
  notrap : ∀ {env : Clif.Env} {cp : Clif.Program},InSubset cp f →
    ∀ {args : List Clif.Val} {fr : Clif.Frame} {cm : Clif.Mem},SourceEntry f args fr →
      TrapsExplicit env cp ⟨fr,[],cm⟩ → ∀ fuel code,Clif.runLoop env cp fuel ⟨fr,[],cm⟩ ≠ .trapped code

/-- The runtime checker derives every source contract premise from actual artifacts. -/
theorem check_domain {f : Clif.Function} {vc : VCode} (checked : check f vc = true) : Domain f vc := by
  obtain ⟨result,lowered,equal,scope,dominated,abi,⟨layout⟩,_⟩ := check_sound checked
  refine ⟨scope,dominated,abi,⟨result,lowered,equal⟩,?_,?_⟩
  · intro env cp subset args fr cm outMem entered fuel vals returned F ctx X MR calls stable sb syms
      memorySem w memory arguments
    rw [← equal]
    exact layout.return_function lowered scope dominated subset entered returned calls stable memorySem memory arguments
  · intro env cp subset args fr cm entered explicit fuel code
    obtain ⟨blocks,body,term,returns,calleeReturns,integer,lookup,sizes,registers,pins⟩ := layout.source_fields
    obtain ⟨b,regs,found,types,paramTypes,set,frame⟩ := entered
    have first : f.entry? = some layout.data.block := by
      simp only [Clif.Function.entry?,blocks,List.head?_cons]
    cases Option.some.inj (found.symm.trans first)
    have func : fr.func = f := congrArg Clif.Frame.func frame
    have sourceBody : fr.body = [⟨[layout.data.result],.call layout.data.fn layout.data.args⟩] :=
      (congrArg Clif.Frame.body frame).trans body
    have sourceTerm : fr.term = .ret [layout.data.result] := (congrArg Clif.Frame.term frame).trans term
    apply source_call_notrap sourceBody sourceTerm ?_ explicit fuel code
    intro ext found
    have same : ext = layout.data.ext := by
      rw [func,lookup] at found
      exact Option.some.inj found.symm
    subst ext
    exact subset.externCalls layout.data.block (by simp [blocks])
      ⟨[layout.data.result],.call layout.data.fn layout.data.args⟩ (by simp [body])
      layout.data.fn layout.data.args rfl layout.data.ext lookup

end Backend.Stock.ResultCall
