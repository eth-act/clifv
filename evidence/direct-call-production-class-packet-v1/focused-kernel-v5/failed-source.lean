import FV.E2E.StockResultCallPair
import FV.E2E.StockResultCallLayout
import FV.E2E.ABIReadOnlyMachine

namespace Backend.Stock.ResultCall
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof E2E Backend.DeadCleanup
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- This record is internal. The layout theorem must derive every field from the original execution. -/
structure SourceRun (f : Clif.Function) (result : Stock.Result) (env : Clif.Env)
    (fr : Clif.Frame) (cm outMem : Clif.Mem) (Γ : Rel) (fc : FnCtx) (X : ExtSem)
    (initial : Arm.ArmState) where
  block : VBlock
  placed : result.code.blocks[0]? = some block
  prelude : List MInst
  suffix : List MInst
  seed : Nat → CV
  values : Nat → CV
  pairs : List (Nat × Reg)
  destination : Nat
  ext : Clif.ExtFunc
  member : ext ∈ f.externs.map (·.2)
  returned : Clif.AbiParam
  returns : ext.sig.returns = [returned]
  callee : List Clif.Val → Clif.Mem → Clif.Outcome
  found : env.extern ext.name = some callee
  sourceArgs : List Clif.Val
  sourceValue : Clif.Val
  after : Clif.Mem
  sourceReturned : callee sourceArgs cm = .returned [sourceValue] after
  freed : outMem = (after.free (fr.slots.map (·.2))).leave
  arguments : ∀ w,ArgsAt ext.sig sourceArgs (pairs.map (values ·.1)) w
  preRun : seqRun (ABIReadOnly.sem Γ.F fc X) prelude seed initial = some (.fall values initial)
  reads : ∀ j i,prelude[j]? = some i → Backend.ABIReadOnly.instruction f.sig 0 j i = true
  code : block.insts.toList = (prelude ++
    [.call ⟨.sym ext.name,retPairs pairs,callDefs [(.x 0,destination)]⟩,
      .rets (retPairs [(destination,.x 0)])]) ++ suffix
  retABI : ReturnABI f (retPairs [(destination,.x 0)])

/-- Original entry, execution, and actual retained records construct the entire internal call path. -/
theorem Layout.source_run {f : Clif.Function} {result : Stock.Result}
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
    ∃ source : SourceRun f result env fr cm outMem Γ fc X w,vals = [source.sourceValue] := by
  obtain ⟨blocks,body,term,returns,calleeReturns,integer,lookup,sizes,registers,pins⟩ := layout.source_fields
  obtain ⟨g,sourceArgs,after,value,callee,read,argTypes,called,valueType,equal,freed⟩ :=
    layout.source_result subset entered returned
  obtain ⟨event,block,prelude,tail,ρ,w1,events,entryBlock,placed,parts,preRun,mem1,values,same,noCalls,suffix,tailEq⟩ :=
    stock_lower_entry_prelude_refines_nocall_frame run scope dominated entered
      (ABIReadOnly.driver Γ.F fc X) (ABIReadOnly.memory Γ.F fc X slot symbols)
      (mrStable_relW Γ f c) memory arguments
  have readChecks : VoidCall.NI.codeCheck f.sig result.code = true := layout.reads
  have reads := VoidCall.NI.prelude_read_checks readChecks placed parts noCalls
  obtain ⟨b,regs,found,types,paramTypes,set,frame⟩ := entered
  have inputTypes : args.map (·.ty) = f.sig.params.map (·.ty) := by
    simpa only [Clif.AbiParam.tys] using types
  have fixed := (ABIReadOnly.seqRun_fall_transport inputTypes (SameWorld.refl Γ.F w)
    (fun _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
    (b := 0) (start := 0) (by simpa only [Nat.zero_add] using reads) preRun).1
  subst w1
  have held := VoidCall.entry_values_resolved run scope dominated events entered values
  let inputValues := layout.data.args.map
    (fun x => ρ (aliasNum result.final.alias (VoidCall.sourceKey event.ctx x)))
  have holds : AllHold sourceArgs inputValues := VoidCall.call_values_hold held read
  have arity : sourceArgs.length = layout.data.ext.sig.params.length := by
    have count := congrArg List.length argTypes
    simpa only [Clif.AbiParam.tys,List.length_map] using count
  have argsAt : ∀ world,ArgsAt layout.data.ext.sig sourceArgs inputValues world := fun world =>
    (argsAt_iff_of_regs sizes registers arity).mpr holds
  have member : layout.data.ext ∈ f.externs.map (·.2) :=
    externsIn_self f layout.data.fn layout.data.ext lookup
  obtain ⟨root,destination,pairs,mapped,code,aliases,keys⟩ := layout.scan_fields events entryBlock
  let resolve := Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)
  let resolvedPairs := pairs.map (fun p => (aliasNum result.final.alias p.1,p.2))
  let resolvedDestination := aliasNum result.final.alias destination
  have actualArgs : resolvedPairs.map (ρ ·.1) = inputValues := by
    simp only [resolvedPairs,List.map_map,Function.comp_def]
    calc
      pairs.map (fun p => ρ (aliasNum result.final.alias p.1)) =
          (pairs.map (·.1)).map (fun key => ρ (aliasNum result.final.alias key)) := by
            simp only [List.map_map,Function.comp_def]
      _ = inputValues := by rw [keys]; simp only [inputValues,List.map_map,Function.comp_def]
  have codeEq : event.output.code.map (·.mapRegs resolve) =
      #[.call ⟨.sym layout.data.ext.name,retPairs resolvedPairs,callDefs [(.x 0,resolvedDestination)]⟩,
        .rets (retPairs [(resolvedDestination,.x 0)])] := by
    rw [code]
    apply Array.toList_inj.mp
    simp [MInst.mapRegs,retPairs,callDefs,resolve,resolve_vreg,resolvedPairs,resolvedDestination,aliases]
  have blockList : block.insts.toList = (prelude.toList ++
      [.call ⟨.sym layout.data.ext.name,retPairs resolvedPairs,callDefs [(.x 0,resolvedDestination)]⟩,
        .rets (retPairs [(resolvedDestination,.x 0)])]) ++ suffix.toList := by
    rw [parts,tailEq]
    change (prelude ++ (event.output.code.map (·.mapRegs resolve) ++ suffix)).toList = _
    rw [codeEq]
    simp only [Array.toList_append,Array.toList_push,Array.toList_empty,List.append_assoc]
  have retABI : ReturnABI f (retPairs [(resolvedDestination,.x 0)]) := by
    simpa only [ReturnABI,retPairs,List.map_cons,List.map_nil,List.length_cons,List.length_nil] using pins
  refine ⟨⟨block,placed,prelude.toList,suffix.toList,entrySeed event.ctx fr,ρ,resolvedPairs,
    resolvedDestination,layout.data.ext,member,layout.data.returned,calleeReturns,g,callee,
    sourceArgs,value,after,called,freed,?_,preRun,reads,blockList,retABI⟩,equal⟩
  intro world
  rw [actualArgs]
  exact argsAt world

/-- The actual call operand binder keeps the complete scalar value and the actual callee world. -/
theorem seqRun_call_result {F : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem}
    {name : String} {pairs : List (Nat × Reg)} {destination : Nat} {values : Nat → CV}
    {before after : Arm.ArmState} {output : CV}
    (called : X.call (some name) (pairs.map (values ·.1)) before = some ([output],after)) :
    seqRun (valueSem F fc X)
      [.call ⟨.sym name,retPairs pairs,callDefs [(.x 0,destination)]⟩] values before =
      some (.fall (fun key => if key = destination then output else values key) after) := by
  have step : valueSem F fc X
      (.call ⟨.sym name,retPairs pairs,callDefs [(.x 0,destination)]⟩)
      (pairs.map (values ·.1)) before = some ([output],after,.next) := by
    change (X.call (some name) (pairs.map (values ·.1)) before).map
      (fun p => (p.1,p.2,Ctl.next)) = _
    rw [called]
    rfl
  have execution := seqRun_call_sym step (show [output].length = [(.x 0,destination)].length from rfl)
  have bound := DirectCallResult.virtual_result pairs destination output values
  rw [vdefUpd_call] at bound
  rw [bound] at execution
  exact execution

/-- The placed return reads the same virtual destination that the actual call defined. -/
theorem SourceRun.virtual_return {f : Clif.Function} {result : Stock.Result} {env : Clif.Env}
    {fr : Clif.Frame} {cm outMem : Clif.Mem} {Γ : Rel} {fc : FnCtx} {X : ExtSem}
    {initial w before after : Arm.ArmState} {output : CV}
    (source : SourceRun f result env fr cm outMem Γ fc X initial)
    (preRun : seqRun (valueSem Γ.F fc X) source.prelude source.seed w = some (.fall source.values before))
    (called : X.call (some source.ext.name) (source.pairs.map (source.values ·.1)) before = some ([output],after)) :
    VReturns result.code (valueSem Γ.F fc X) source.seed w
      (retPairs [(source.destination,.x 0)]) [output] after := by
  let updated := fun key => if key = source.destination then output else source.values key
  have callRun : seqRun (valueSem Γ.F fc X)
      [.call ⟨.sym source.ext.name,retPairs source.pairs,callDefs [(.x 0,source.destination)]⟩]
      source.values before = some (.fall updated after) := seqRun_call_result called
  have retRun : seqRun (valueSem Γ.F fc X) [.rets (retPairs [(source.destination,.x 0)])] updated after =
      some (.stop 0 (.rets (retPairs [(source.destination,.x 0)]))
        (retOps [(source.destination,.x 0)]).toArray updated after [] after .ret) := by
    simp [seqRun,operands_rets,valueSem,specForm,pureForm,cmpForm,csem,retOps,Operand.isDef]
  have body := seqRun_append_fall_stop (valueSem Γ.F fc X) callRun retRun
  have complete := seqRun_append_fall_stop (valueSem Γ.F fc X) preRun body
  have segment : SegAt source.block 0 (source.prelude ++
      [.call ⟨.sym source.ext.name,retPairs source.pairs,callDefs [(.x 0,source.destination)]⟩,
        .rets (retPairs [(source.destination,.x 0)])]) :=
    segAt_of_toList (L₁ := []) (by simpa only [List.nil_append] using source.code)
  obtain ⟨path,_,instruction,operands,ran,_,_⟩ := seqRun_stop_star source.placed segment complete
  refine ⟨0,0+(0+1+source.prelude.length),updated,after,source.block,
    (retOps [(source.destination,.x 0)]).toArray,[],path,source.placed,instruction,rfl,?_,rfl⟩
  simp [vuses_retOps,updated]

/-- Original call correctness supplies the returned value and the actual callback memory. -/
theorem SourceRun.execute {f : Clif.Function} {result : Stock.Result} {env : Clif.Env}
    {fr : Clif.Frame} {cm outMem : Clif.Mem} {Γ : Rel} {fc : FnCtx} {X : ExtSem}
    {c : BitVec 64} {initial : Arm.ArmState}
    (source : SourceRun f result env fr cm outMem Γ fc X initial)
    {args : List Clif.Val} (types : args.map (·.ty) = f.sig.params.map (·.ty))
    (arguments : ArgsAtEntry Γ.F f.sig args initial)
    (memory : RelW Γ f c fr.slots cm initial)
    (calls : XCallsOk env (f.externs.map (·.2)) (RelW Γ f c) X) :
    ∃ before output after,
      seqRun (valueSem Γ.F fc X) source.prelude source.seed initial = some (.fall source.values before) ∧
      SameWorld Γ.F before initial ∧ RelW Γ f c fr.slots cm before ∧
      X.call (some source.ext.name) (source.pairs.map (source.values ·.1)) before = some ([output],after) ∧
      VHolds source.sourceValue output ∧ RelW Γ f c fr.slots source.after after ∧
      VReturns result.code (valueSem Γ.F fc X) source.seed initial
        (retPairs [(source.destination,.x 0)]) [output] after := by
  obtain ⟨_,before,preRun,related⟩ := ABIReadOnly.seqRun_fall_realize types arguments (SameWorld.refl Γ.F initial)
    (b := 0) (start := 0) (by simpa only [Nat.zero_add] using source.reads) (fun _ => rfl) source.preRun
  have beforeMemory := mrStable_relW Γ f c fr.slots cm initial before (SameWorld.nf related) memory
  obtain ⟨actual,after,called,arity,held,mem⟩ := calls source.ext source.member source.callee fr.slots cm before
    (some source.ext.name) (source.pairs.map (source.values ·.1)) (source.pairs.map (source.values ·.1))
    source.sourceArgs [source.sourceValue] source.after source.found (Or.inl ⟨rfl,rfl⟩)
    (source.arguments before) beforeMemory source.sourceReturned (by rw [source.returns]; rfl)
  have abi : sigRets source.ext.sig = [source.returned] := by
    unfold sigRets
    split <;> simp [source.returns]
  rw [abi] at arity
  cases actual with
  | nil => cases arity
  | cons output tail =>
    have empty : tail = [] := by simpa using arity
    subst tail
    exact ⟨before,output,after,preRun,related,beforeMemory,called,
      held.2 0 source.sourceValue output rfl rfl,mem,source.virtual_return preRun called⟩

/-- Original XNI keeps the result equal and pairs the actual returned memory worlds. -/
theorem SourceRun.execute_other {f : Clif.Function} {result : Stock.Result} {env : Clif.Env}
    {fr : Clif.Frame} {cm outMem : Clif.Mem} {Γ : Rel} {fc : FnCtx} {X : ExtSem}
    {c : BitVec 64} {initial before after : Arm.ArmState} {output : CV}
    (source : SourceRun f result env fr cm outMem Γ fc X initial)
    {args : List Clif.Val} (types : args.map (·.ty) = f.sig.params.map (·.ty))
    (arguments : ArgsAtEntry Γ.F f.sig args initial)
    (related : SameWorld Γ.F before initial) (memory : RelW Γ f c fr.slots cm before)
    (called : X.call (some source.ext.name) (source.pairs.map (source.values ·.1)) before = some ([output],after))
    (calls : XCallsOk env (f.externs.map (·.2)) (RelW Γ f c) X)
    (ni : XNI Γ.F Γ.syms (f.externs.map (·.2)) (indSigs f) c
      (CallLg env (f.externs.map (·.2)) (indSigs f)) X)
    {Z : BitVec 64 → Prop} (covers : ∀ a,Γ.F a → Z a) {other : Arm.ArmState}
    (otherMemory : RelW Γ f c fr.slots cm other) (worlds : SameWorld Z initial other)
    (registers : ∀ r v,(.reg r,v) ∈ (locsOf f.sig).zip args → regVal other r = regVal initial r)
    (stack : ∀ (off : Nat) (v : Clif.Val),(.stack off,v) ∈ (locsOf f.sig).zip args → ∀ j < v.ty.bytes,
      other.mem (Arm.r (.GPR 29#5) initial + BitVec.ofInt 64 (16+(off : Int)) + BitVec.ofNat 64 j) =
      initial.mem (Arm.r (.GPR 29#5) initial + BitVec.ofInt 64 (16+(off : Int)) + BitVec.ofNat 64 j)) :
    ∃ final,SameWorld Z final after ∧ RelW Γ f c fr.slots source.after final ∧
      VReturns result.code (valueSem Γ.F fc X) source.seed other
        (retPairs [(source.destination,.x 0)]) [output] final := by
  have otherArguments := ABIReadOnly.arguments_transport arguments worlds registers stack
  have transferred := (ABIReadOnly.seqRun_fall_transport types worlds registers stack
    (b := 0) (start := 0) (by simpa only [Nat.zero_add] using source.reads) source.preRun).2
  obtain ⟨_,otherBefore,otherRun,otherRelated⟩ := ABIReadOnly.seqRun_fall_realize types otherArguments
    (SameWorld.refl Γ.F other) (b := 0) (start := 0)
    (by simpa only [Nat.zero_add] using source.reads) (fun _ => rfl) transferred
  have beforeMemory := mrStable_relW Γ f c fr.slots cm other otherBefore (SameWorld.nf otherRelated) otherMemory
  have beforeWorlds : SameWorld Z before otherBefore :=
    (SameWorld.mono covers related).trans (worlds.trans (SameWorld.mono covers otherRelated).symm)
  obtain ⟨paired,firstOut,otherOut,firstCall,otherCall,held,firstMemory,finalMemory,finalWorlds⟩ :=
    result_call_pair calls ni source.member source.returns source.found source.sourceReturned memory beforeMemory
      (source.arguments before) (source.arguments otherBefore) covers beforeWorlds
  have equal := Prod.mk.inj (Option.some.inj (firstCall.symm.trans called))
  have sameOutput : paired = output := List.cons.inj equal.1 |>.1
  have sameWorld : firstOut = after := equal.2
  subst paired
  subst firstOut
  exact ⟨otherOut,finalWorlds.symm,finalMemory,source.virtual_return otherRun otherCall⟩

end Backend.Stock.ResultCall
