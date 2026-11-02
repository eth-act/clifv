import FV.E2E.StockVoidCallEntry
import FV.E2E.ABIReadOnlyMachine
import FV.E2E.StockArithmeticStageContract
import FV.E2E.StockArithmeticStage
import FV.E2E.DeadCleanupRegLevelX
import FV.E2E.DeadCleanupGot

namespace Backend.Stock.VoidCall
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof E2E
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Proof-internal source and actual-code facts. The source theorem constructs this record. -/
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
  ext : Clif.ExtFunc
  member : ext ∈ f.externs.map (·.2)
  void : ext.sig.returns = []
  callee : List Clif.Val → Clif.Mem → Clif.Outcome
  found : env.extern ext.name = some callee
  sourceArgs : List Clif.Val
  after : Clif.Mem
  sourceReturned : callee sourceArgs cm = .returned [] after
  freed : outMem = (after.free (fr.slots.map (·.2))).leave
  arguments : ∀ w,ArgsAt ext.sig sourceArgs (pairs.map (values ·.1)) w
  preRun : seqRun (ABIReadOnly.sem Γ.F fc X.voidCalls) prelude seed initial = some (.fall values initial)
  reads : ∀ j i,prelude[j]? = some i → Backend.ABIReadOnly.instruction f.sig 0 j i = true
  code : block.insts.toList =
    (prelude ++ [.call ⟨.sym ext.name,retPairs pairs,[]⟩,.rets []]) ++ suffix
  retABI : ReturnABI f []

/-- Original source execution and checked actual code derive the internal call path. -/
theorem Layout.source_run {f : Clif.Function} {result : Stock.Result}
    (layout : Layout f result) (run : Stock.lower f = .ok result)
    (scope : LowerScope f) (dominated : Dominated f) {env : Clif.Env} {cp : Clif.Program}
    (subset : InSubset cp f) {args : List Clif.Val} {fr : Clif.Frame} {cm outMem : Clif.Mem}
    (entered : SourceEntry f args fr) {fuel : Nat} {vals : List Clif.Val}
    (returned : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .returned vals outMem)
    {Γ : Rel} {fc : FnCtx} {X : ExtSem} {c : BitVec 64}
    (slot : fc.slotBase = Γ.slotOff)
    (symbols : ∀ n b,Γ.syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (checked : NI.codeCheck f.sig result.code = true)
    {w : Arm.ArmState} (memory : RelW Γ f c fr.slots cm w)
    (arguments : ArgsAtEntry Γ.F f.sig args w) :
    vals = [] ∧ Nonempty (SourceRun f result env fr cm outMem Γ fc X w) := by
  have source := entered
  obtain ⟨b,regs,found,types,paramTypes,set,frame⟩ := source
  have first : f.entry? = some layout.block := by simp only [Clif.Function.entry?,layout.blocks,List.head?_cons]
  cases Option.some.inj (found.symm.trans first)
  have func : fr.func = f := congrArg Clif.Frame.func frame
  have body : fr.body = [⟨[],.call layout.fn layout.args⟩] :=
    (congrArg Clif.Frame.body frame).trans layout.body
  have term : fr.term = .ret [] := (congrArg Clif.Frame.term frame).trans layout.term
  have lookup : fr.func.extern? layout.fn = some layout.ext := by rw [func]; exact layout.lookup
  have external : cp.func? layout.ext.name = none :=
    subset.externCalls layout.block (by simp [layout.blocks]) ⟨[],.call layout.fn layout.args⟩
      (by simp [layout.body]) layout.fn layout.args rfl layout.ext layout.lookup
  obtain ⟨g,sourceArgs,after,callee,read,argTypes,called,empty,freed⟩ :=
    source_return_call body term (by rw [func]; exact layout.noReturns) lookup external layout.void returned
  refine ⟨empty,?_⟩
  obtain ⟨event,block,prelude,tail,ρ,w1,events,entryBlock,placed,parts,preRun,mem1,values,same,noCalls,suffix,tailEq⟩ :=
    stock_lower_entry_prelude_refines_nocall_frame run scope dominated entered
      (ABIReadOnly.driver Γ.F fc X.voidCalls) (ABIReadOnly.memory Γ.F fc X.voidCalls slot symbols)
      (mrStable_relW Γ f c) memory arguments
  have reads := NI.prelude_read_checks checked placed parts noCalls
  have inputTypes : args.map (·.ty) = f.sig.params.map (·.ty) := by
    simpa only [Clif.AbiParam.tys] using types
  have fixed := (ABIReadOnly.seqRun_fall_transport inputTypes (SameWorld.refl Γ.F w)
    (fun _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
    (b := 0) (start := 0) (by simpa only [Nat.zero_add] using reads) preRun).1
  subst w1
  have held := entry_values_resolved run scope dominated events entered values
  let inputValues := layout.args.map (fun x => ρ (aliasNum result.final.alias (sourceKey event.ctx x)))
  have holds : AllHold sourceArgs inputValues := call_values_hold held read
  have arity : sourceArgs.length = layout.ext.sig.params.length := by
    have count := congrArg List.length argTypes
    simpa only [Clif.AbiParam.tys,List.length_map] using count
  have argsAt : ∀ world,ArgsAt layout.ext.sig sourceArgs inputValues world := fun world =>
    (argsAt_iff_of_regs layout.sizes layout.registers arity).mpr holds
  have member : layout.ext ∈ f.externs.map (·.2) := externsIn_self f layout.fn layout.ext layout.lookup
  obtain ⟨pairs,code,keys⟩ := layout.code event events entryBlock
  let resolve := Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)
  let resolvedPairs := pairs.map (fun p => (aliasNum result.final.alias p.1,p.2))
  have actualArgs : resolvedPairs.map (ρ ·.1) = inputValues := by
    simp only [resolvedPairs,List.map_map,Function.comp_def]
    calc
      pairs.map (fun p => ρ (aliasNum result.final.alias p.1)) =
          (pairs.map (·.1)).map (fun key => ρ (aliasNum result.final.alias key)) := by
            simp only [List.map_map,Function.comp_def]
      _ = inputValues := by
        rw [keys]
        simp only [inputValues,List.map_map,Function.comp_def]
  have codeEq : event.output.code.map (·.mapRegs resolve) =
      #[.call ⟨.sym layout.ext.name,retPairs resolvedPairs,[]⟩,.rets []] := by
    rw [code]
    apply Array.toList_inj.mp
    simp only [Array.toList_map,Array.toList_push,Array.toList_empty,List.map_cons,List.map_nil,
      MInst.mapRegs,retPairs,List.map_map,Function.comp_def,List.map_nil]
    simp only [resolve,resolve_vreg,resolvedPairs,List.map_map,Function.comp_def]
    rfl
  have blockList : block.insts.toList =
      (prelude.toList ++ [.call ⟨.sym layout.ext.name,retPairs resolvedPairs,[]⟩,.rets []]) ++ suffix.toList := by
    rw [parts,tailEq]
    change (prelude ++ (event.output.code.map (·.mapRegs resolve) ++ suffix)).toList = _
    rw [codeEq]
    simp only [Array.toList_append,Array.toList_push,Array.toList_empty,List.append_assoc]
  refine ⟨⟨block,placed,prelude.toList,suffix.toList,entrySeed event.ctx fr,ρ,resolvedPairs,
    layout.ext,member,layout.void,g,callee,sourceArgs,after,called,freed,?_,preRun,reads,blockList,layout.retABI⟩⟩
  intro world
  rw [actualArgs]
  exact argsAt world

end Backend.Stock.VoidCall

namespace Backend.Stock.VoidCall
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof E2E Backend.DeadCleanup
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- Compose the actual ABI prelude, direct void call, and placed return. -/
theorem SourceRun.virtual_return {f : Clif.Function} {result : Stock.Result} {env : Clif.Env}
    {fr : Clif.Frame} {cm outMem : Clif.Mem} {Γ : Rel} {fc : FnCtx} {X : ExtSem}
    {initial w t out : Arm.ArmState}
    (source : SourceRun f result env fr cm outMem Γ fc X initial)
    (preRun : seqRun (valueSem Γ.F fc X.voidCalls) source.prelude source.seed w = some (.fall source.values t))
    (called : X.voidCalls.call (some source.ext.name) (source.pairs.map (source.values ·.1)) t = some ([],out)) :
    VReturns result.code (valueSem Γ.F fc X.voidCalls) source.seed w [] [] out := by
  obtain ⟨actual,oldRun,_⟩ := ExtSem.voidCalls_call_inv called
  have callRun : seqRun (valueSem Γ.F fc X.voidCalls)
      [.call ⟨.sym source.ext.name,retPairs source.pairs,[]⟩] source.values t =
      some (.fall source.values out) := seqRun_call_voidCalls_int (F := Γ.F) (ctx := fc) oldRun
  have retRun : seqRun (valueSem Γ.F fc X.voidCalls) [.rets []] source.values out =
      some (.stop 0 (.rets []) #[] source.values out [] out .ret) := rfl
  have body := seqRun_append_fall_stop (valueSem Γ.F fc X.voidCalls) callRun retRun
  have complete := seqRun_append_fall_stop (valueSem Γ.F fc X.voidCalls) preRun body
  have segment : SegAt source.block 0
      (source.prelude ++ [.call ⟨.sym source.ext.name,retPairs source.pairs,[]⟩,.rets []]) :=
    segAt_of_toList (L₁ := []) (by simpa only [List.nil_append] using source.code)
  obtain ⟨path,_,instruction,operands,ran,_,_⟩ := seqRun_stop_star source.placed segment complete
  exact ⟨0,0+(0+1+source.prelude.length),source.values,out,source.block,#[],[],path,
    source.placed,instruction,rfl,rfl,rfl⟩

/-- The original source-call contract realizes this internally derived path. -/
theorem SourceRun.execute {f : Clif.Function} {result : Stock.Result} {env : Clif.Env}
    {fr : Clif.Frame} {cm outMem : Clif.Mem} {Γ : Rel} {fc : FnCtx} {X : ExtSem}
    {c : BitVec 64} {initial : Arm.ArmState}
    (source : SourceRun f result env fr cm outMem Γ fc X initial)
    {args : List Clif.Val} (types : args.map (·.ty) = f.sig.params.map (·.ty))
    (arguments : ArgsAtEntry Γ.F f.sig args initial)
    (memory : RelW Γ f c fr.slots cm initial)
    (calls : XCallsOk env (f.externs.map (·.2)) (RelW Γ f c) X) :
    ∃ before out,
      seqRun (valueSem Γ.F fc X.voidCalls) source.prelude source.seed initial = some (.fall source.values before) ∧
      SameWorld Γ.F before initial ∧ RelW Γ f c fr.slots cm before ∧
      X.voidCalls.call (some source.ext.name) (source.pairs.map (source.values ·.1)) before = some ([],out) ∧
      RelW Γ f c fr.slots source.after out ∧
      VReturns result.code (valueSem Γ.F fc X.voidCalls) source.seed initial [] [] out := by
  obtain ⟨_,before,preRun,related⟩ := ABIReadOnly.seqRun_fall_realize types arguments (SameWorld.refl Γ.F initial)
    (b := 0) (start := 0) (by simpa only [Nat.zero_add] using source.reads) (fun _ => rfl) source.preRun
  have beforeMemory := mrStable_relW Γ f c fr.slots cm initial before (SameWorld.nf related) memory
  obtain ⟨actual,out,called,_,_,mem⟩ := calls source.ext source.member source.callee fr.slots cm before
    (some source.ext.name) (source.pairs.map (source.values ·.1)) (source.pairs.map (source.values ·.1))
    source.sourceArgs [] source.after source.found (Or.inl ⟨rfl,rfl⟩) (source.arguments before)
    beforeMemory source.sourceReturned (by rw [source.void]; rfl)
  have internal := ExtSem.voidCalls_call called
  exact ⟨before,out,preRun,related,beforeMemory,internal,mem,source.virtual_return preRun internal⟩

end Backend.Stock.VoidCall

namespace Backend.Stock.VoidCall
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof E2E Backend.DeadCleanup
set_option autoImplicit false
set_option Elab.async false

/-- Original NI and ABI agreement pair the complete actual caller execution. -/
theorem SourceRun.execute_other {f : Clif.Function} {result : Stock.Result} {env : Clif.Env}
    {fr : Clif.Frame} {cm outMem : Clif.Mem} {Γ : Rel} {fc : FnCtx} {X : ExtSem}
    {c : BitVec 64} {initial before out : Arm.ArmState}
    (source : SourceRun f result env fr cm outMem Γ fc X initial)
    {args : List Clif.Val} (types : args.map (·.ty) = f.sig.params.map (·.ty))
    (arguments : ArgsAtEntry Γ.F f.sig args initial)
    (related : SameWorld Γ.F before initial) (memory : RelW Γ f c fr.slots cm before)
    (called : X.voidCalls.call (some source.ext.name) (source.pairs.map (source.values ·.1)) before = some ([],out))
    (calls : XCallsOk env (f.externs.map (·.2)) (RelW Γ f c) X)
    (ni : XNI Γ.F Γ.syms (f.externs.map (·.2)) (indSigs f) c
      (CallLg env (f.externs.map (·.2)) (indSigs f)) X)
    {Z : BitVec 64 → Prop} (covers : ∀ a,Γ.F a → Z a) {other : Arm.ArmState}
    (otherMemory : RelW Γ f c fr.slots cm other) (worlds : SameWorld Z initial other)
    (registers : ∀ r v,(.reg r,v) ∈ (locsOf f.sig).zip args → regVal other r = regVal initial r)
    (stack : ∀ (off : Nat) (v : Clif.Val),(.stack off,v) ∈ (locsOf f.sig).zip args → ∀ j < v.ty.bytes,
      other.mem (Arm.r (.GPR 29#5) initial + BitVec.ofInt 64 (16+(off : Int)) + BitVec.ofNat 64 j) =
      initial.mem (Arm.r (.GPR 29#5) initial + BitVec.ofInt 64 (16+(off : Int)) + BitVec.ofNat 64 j)) :
    ∃ final,SameWorld Z final out ∧ RelW Γ f c fr.slots source.after final ∧
      VReturns result.code (valueSem Γ.F fc X.voidCalls) source.seed other [] [] final := by
  have otherArguments := ABIReadOnly.arguments_transport arguments worlds registers stack
  have transferred := (ABIReadOnly.seqRun_fall_transport types worlds registers stack
    (b := 0) (start := 0) (by simpa only [Nat.zero_add] using source.reads) source.preRun).2
  obtain ⟨_,otherBefore,otherRun,otherRelated⟩ := ABIReadOnly.seqRun_fall_realize types otherArguments
    (SameWorld.refl Γ.F other) (b := 0) (start := 0)
    (by simpa only [Nat.zero_add] using source.reads) (fun _ => rfl) transferred
  have beforeMemory := mrStable_relW Γ f c fr.slots cm other otherBefore (SameWorld.nf otherRelated) otherMemory
  have beforeWorlds : SameWorld Z before otherBefore :=
    (SameWorld.mono covers related).trans (worlds.trans (SameWorld.mono covers otherRelated).symm)
  obtain ⟨firstOut,otherOut,firstCall,otherCall,firstMemory,finalMemory,finalWorlds⟩ :=
    void_call_pair calls ni source.member source.void source.found source.sourceReturned memory beforeMemory
      (source.arguments before) (source.arguments otherBefore) covers beforeWorlds
  have equal : firstOut = out := (Prod.mk.inj (Option.some.inj (firstCall.symm.trans called))).2
  subst firstOut
  exact ⟨otherOut,finalWorlds.symm,finalMemory,source.virtual_return otherRun otherCall⟩

end Backend.Stock.VoidCall

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.DeadCleanup
set_option autoImplicit false
set_option Elab.async false

/-- Realize the same actual caller artifact with the original complete entry and per-state facts. -/
theorem stock_void_call_machine_return {f : Clif.Function} {k : Nat} {result : Stock.Result}
    {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin} {cleanup : Bool}
    (hc : CompiledStockArithmeticStage f cleanup k result vcp rf af fa fb)
    (noTry : result.code.hasTryCall = false)
    {X : ExtSem} {K : Nat} {F Z : BitVec 64 → Prop}
    (covers : ∀ a,F a → Z a) (covered : FormsCovered ⟨fa.k,af.slotBase⟩ vcp)
    {initial final reference : Arm.ArmState} (worlds : SameWorld Z final reference)
    {ρ : Nat → CV} {us : List (Reg × Reg)} {outs : List CV}
    (returned : VReturns result.code (valueSem F ⟨fa.k,af.slotBase⟩ X.voidCalls) ρ initial us outs final)
    (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState)
    (entry : ActEntry vcp rf af fa fb K F G X H base ra s initial) :
    ∃ n,ActRet ra Z G us outs reference s (runX (ArmStepX X H fa) n s) ∧
      PostTrace fa af base (ArmStepX X H fa) s n ∧
      ∀ i < n,actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
        (runX (ArmStepX X H fa) i s) := by
  have preparedNoTry : vcp.hasTryCall = false := noTryCall_of_prepCheck hc.prepOk (by
    cases cleanup with
    | false => exact noTry
    | true => exact Backend.DeadCleanup.prune_noTryCall noTry)
  have internal := entry.voidCalls preparedNoTry
  have staged := StockArithmeticStage_returns hc.prepOk returned
  have machine := regLevelCorrect_worldX_value hc.check hc.alloc hc.emit hc.layout
    (X := X.voidCalls) (H := H) (K := K) (G := G) (gv := GotV vcp)
    covered internal.abi internal.stack internal.gfree (by rw [internal.hF]; exact internal.calls)
    (by rw [internal.hF]; exact internal.tries) (by rw [internal.hF]; exact internal.tls)
    (by rw [internal.hF]; exact internal.body) ρ
  rw [internal.hF] at machine
  obtain ⟨n,⟨ret,regs,world,frame,kept,program,trace⟩,good⟩ :=
    machine.1 us outs final (vReturns_gotV_value staged)
  refine ⟨n,⟨ret,regs,?_,?_,kept,program⟩,trace,fun i before => actGoodX_of_voidCalls (good i before)⟩
  · intro a outside
    exact (world a (fun hf => outside (covers a hf))).trans (worlds.2.1 a outside)
  · intro field unmasked fp sp
    exact (frame field unmasked fp sp).trans (worlds.1 field unmasked)

end E2E

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false

/-- Complete caller NI retains all original inputs, machine facts, and return guarantees. -/
theorem backend_correct_world_niX_stock_void_call {p : Clif.Program} {f : Clif.Function} {k : Nat} {result : Stock.Result} {vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (checked : Stock.VoidCall.NI.check f result.code = true) {cleanup : Bool}
    (hc : CompiledStockArithmeticStage f cleanup k result vcp rf af fa fb)
    {X : ExtSem} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        ReturnABI f us ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧ result.code.RetsSite us ∧
        (∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
          ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (ArmStepX X H fa) n s) ∧
            PostTrace fa af base (ArmStepX X H fa) s n ∧
            ∀ i < n, actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
              (runX (ArmStepX X H fa) i s)) ∧
        (XNI F syms (f.externs.map (·.2)) (indSigs f) c
          (CallLg env (f.externs.map (·.2)) (indSigs f)) X → XTls F X →
        ∀ (D : BitVec 64 → Prop) (w₀' : Arm.ArmState),
          RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀' →
          SameWorld (fun b => F b ∨ D b) w₀ w₀' →
          (∀ r v, (ArgLoc.reg r, v) ∈ (locsOf f.sig).zip args → regVal w₀' r = regVal w₀ r) →
          (∀ off v, (ArgLoc.stack off, v) ∈ (locsOf f.sig).zip args → ∀ k < v.ty.bytes,
            w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
              w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k)) →
          ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
            ActEntry vcp rf af fa fb K F G X H base ra s w₀' →
            ∃ n, ActRet ra (fun a => F a ∨ D a) G us outs w s (runX (ArmStepX X H fa) n s) ∧
              PostTrace fa af base (ArmStepX X H fa) s n ∧
              ∀ i < n, actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
                (runX (ArmStepX X H fa) i s)) := by
  intro vals cm returned
  have checks := Bool.and_eq_true_iff.mp checked
  obtain ⟨actual,lowered,equal,scope,dominated,abi,⟨layout⟩,_⟩ := Stock.VoidCall.check_sound checks.1
  have sameResult : actual = result := Except.ok.inj (lowered.symm.trans hc.lower)
  subst actual
  have state : (⟨cs.frame,[],cs.mem⟩ : Clif.State) = cs := by
    have callers := hcs.callers
    cases cs
    cases callers
    rfl
  obtain ⟨empty,⟨path⟩⟩ := layout.source_run (fc := ⟨fa.k,af.slotBase⟩) hc.lower scope dominated hsub hcs.stockSourceEntry
    (by rwa [state]) hslot hsym checks.2 hrel hargs
  subst vals
  obtain ⟨before,out,preRun,related,beforeMemory,called,mem,reached⟩ := path.execute hcs.sig hargs hrel hX
  have noTry := Stock.VoidCall.NI.noTryCall_of_codeCheck checks.2
  have site : result.code.RetsSite [] := by
    obtain ⟨b,j,ρ,w₁,vb,ops,vs,_,atBlock,atInst,_⟩ := reached
    exact ⟨b,vb,j,atBlock,atInst⟩
  have finalMemory : MemRel F syms cm out := by
    rw [path.freed]
    exact memRel_leave (memRel_free mem.1.1 _)
  refine ⟨[],[],out,path.retABI,rfl,?_,finalMemory,site,?_,?_⟩
  · simp [PrefixHold]
  · intro H G base ra s entry
    exact stock_void_call_machine_return hc noTry (fun _ h => h) hcov (SameWorld.refl F out)
      reached H G base ra s entry
  · intro ni tls D other otherMemory worlds registers stack H G base ra s entry
    obtain ⟨final,finalWorlds,_,otherRun⟩ := path.execute_other hcs.sig hargs related beforeMemory called hX ni
      (fun _ h => Or.inl h) otherMemory worlds registers stack
    exact stock_void_call_machine_return hc noTry (fun _ h => Or.inl h) hcov finalWorlds
      otherRun H G base ra s entry

end E2E

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false

/-- Every original source outcome retains the actual caller machine contract. -/
theorem backend_correct_worldX_stock_void_call {p : Clif.Program} {f : Clif.Function} {k : Nat} {result : Stock.Result} {vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (checked : Stock.VoidCall.NI.check f result.code = true) {cleanup : Bool}
    (hc : CompiledStockArithmeticStage f cleanup k result vcp rf af fa fb)
    {X : ExtSem} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    (∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        ReturnABI f us ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧ result.code.RetsSite us ∧
        ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
          ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (ArmStepX X H fa) n s) ∧
            PostTrace fa af base (ArmStepX X H fa) s n) ∧
    (∀ c', Clif.runLoop env p fuel cs = .trapped c' →
      ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
        ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
        ∃ n, TrapAt fb base c' (runX (ArmStepX X H fa) n s)) := by
  refine ⟨fun vals cm returned => ?_,fun code trapped H G base ra s entry => ?_⟩
  · obtain ⟨us,outs,w,pins,arity,values,memory,site,run,_⟩ :=
      backend_correct_world_niX_stock_void_call hsub checked hc hcov hX hXI hsym hslot hcs hrel hargs htr
        fuel vals cm returned
    refine ⟨us,outs,w,pins,arity,values,memory,site,?_⟩
    intro H G base ra s entry
    obtain ⟨n,ret,trace,_⟩ := run H G base ra s entry
    exact ⟨n,ret,trace⟩
  · have state : (⟨cs.frame,[],cs.mem⟩ : Clif.State) = cs := by
      have callers := hcs.callers
      cases cs
      cases callers
      rfl
    have noTrap := (Stock.VoidCall.check_domain (Bool.and_eq_true_iff.mp checked).1).notrap
      hsub hcs.stockSourceEntry (by rwa [state]) fuel code
    exact False.elim (noTrap (by rwa [state]))

end E2E
