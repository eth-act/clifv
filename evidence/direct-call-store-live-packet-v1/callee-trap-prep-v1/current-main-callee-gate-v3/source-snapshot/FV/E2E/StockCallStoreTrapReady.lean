import FV.E2E.StockCallStoreSourceResult
import FV.Backend.Proof.StockCallStoreCalleeTrap
import FV.E2E.StockLiveCallPrelude
import FV.E2E.ABIReadOnlyMachine

namespace Backend.Stock.CallStore
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof E2E
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- Internal call-entry facts come from the original source and actual compiler records. -/
structure TrapReady (f : Clif.Function) (result : Stock.Result) (env : Clif.Env) (cp : Clif.Program)
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
  callee : List Clif.Val → Clif.Mem → Clif.Outcome
  found : env.extern ext.name = some callee
  liveWord : BitVec 64
  sourceTrapped : callee [⟨.i64,liveWord⟩] cm = .trapped trap
  flags : Clif.MemFlags
  liveHeld : VHolds ⟨.i64,liveWord⟩ (values argument)
  arguments : ∀ world,ArgsAt ext.sig [⟨.i64,liveWord⟩] [values argument] world
  preRun : seqRun (ABIReadOnly.sem Γ.F fc X) prelude seed initial = some (.fall values initial)
  reads : ∀ j inst,prelude[j]? = some inst → Backend.ABIReadOnly.instruction f.sig 0 j inst = true
  code : block.insts.toList = (prelude ++
    [.call ⟨.sym ext.name,retPairs [(argument,.x 0)],callDefs [(.x 0,called)]⟩,
     .store .store64 (.vreg called .int) (.unsignedOffset (.vreg pointer .int) 8) flags,
     .rets (retPairs [(called,.x 0)])]) ++ suffix

/-- The original entry and complete source run derive every internal call-entry fact. -/
theorem Layout.trap_ready {f : Clif.Function} {result : Stock.Result}
    (layout : Layout f result) (run : Stock.lower f = .ok result)
    (scope : LowerScope f) (dominated : Dominated f) {env : Clif.Env} {cp : Clif.Program}
    (subset : InSubset cp f) {args : List Clif.Val} {fr : Clif.Frame} {cm : Clif.Mem}
    (entered : SourceEntry f args fr) {trap : Clif.TrapCode}
    (trapped : instOutcome env cp fr cm (.call layout.data.fn [layout.data.argument]) = .trap trap)
    {Γ : Rel} {fc : FnCtx} {X : ExtSem} {c : BitVec 64}
    (slot : fc.slotBase = Γ.slotOff)
    (symbols : ∀ n b,Γ.syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    {w : Arm.ArmState} (memory : RelW Γ f c fr.slots cm w)
    (arguments : ArgsAtEntry Γ.F f.sig args w) :
    Nonempty (TrapReady f result env cp fr cm Γ fc X w trap) := by
  obtain ⟨blocks,parameters,body,term,params,returns,calleeParams,calleeReturns,integer,lookup,pins,
    sourceSeparate,argumentCalled,pointerArgument,flags,parameterBytes⟩ := layout.source_fields
  have func : fr.func = f := by
    obtain ⟨b,regs,entry,types,paramTypes,set,frame⟩ := entered
    exact congrArg Clif.Frame.func frame
  obtain ⟨ext,arguments,g,extFound,read,argTypes,external,callee,called⟩ :=
    CallStoreResult.source_callee_trap trapped
  have same : ext = layout.data.ext := by
    rw [func,lookup] at extFound
    exact Option.some.inj extFound.symm
  subst ext
  have count : arguments.length = 1 := by simpa using (getMany_ok read).1
  cases arguments with
  | nil => cases count
  | cons original rest =>
    have empty : rest = [] := by simpa using count
    subst rest
    have originalType : original.ty = .i64 := by
      simpa only [Clif.AbiParam.tys,calleeParams,List.map_cons,List.map_nil,List.cons.injEq,and_true] using argTypes
    obtain ⟨argumentTy,liveWord⟩ := original
    dsimp only at originalType
    subst argumentTy
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
      callee := g
      found := callee
      liveWord := liveWord
      sourceTrapped := called
      flags := layout.data.flags
      liveHeld := liveHeld
      arguments := argsAt
      preRun := preRun
      reads := reads
      code := blockList
      }⟩

end Backend.Stock.CallStore
