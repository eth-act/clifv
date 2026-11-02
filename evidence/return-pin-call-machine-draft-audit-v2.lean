import FV.E2E.StockVoidCallDomain
import FV.E2E.StockVoidCallWitness
import FV.E2E.ABIReadOnlySem
import FV.Backend.LinearScan
import FV.E2E.PairDriverF
import FV.E2E.StockArithmeticStage
import FV.E2E.StockArithmeticStageContract
import FV.E2E.DeadCleanupRegLevelX
import FV.E2E.DeadCleanupGot

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false

/-- The original NI premise supplies the internal view without a new program condition. -/
theorem XNI.voidCalls {F : BitVec 64 → Prop} {syms : String → Option Nat}
    {exts : List Clif.ExtFunc} {sigs : List Clif.Signature} {sp0 : BitVec 64}
    {Lg : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop} {X : ExtSem}
    (ni : XNI F syms exts sigs sp0 Lg X) : XNI F syms exts sigs sp0 Lg X.voidCalls := by
  intro n sig vals cm args d uses Z w w' o x o' x' legitimate destination covers same
    memory memory' stack stack' arguments run run'
  obtain ⟨actual,oldRun,empty⟩ := ExtSem.voidCalls_call_inv run
  obtain ⟨actual',oldRun',empty'⟩ := ExtSem.voidCalls_call_inv run'
  have pair := ni n sig vals cm args d uses Z w w' actual x actual' x' legitimate destination
    covers same memory memory' stack stack' arguments oldRun oldRun'
  exact ⟨empty.trans empty'.symm,pair.2⟩

/-- The internal view keeps the original TLS flags and NI premise. -/
theorem XTls.voidCalls {F : BitVec 64 → Prop} {X : ExtSem} (tls : XTls F X) :
    XTls F X.voidCalls := tls

end E2E

namespace Backend.Stock.VoidCall
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof E2E
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- The complete source return uses the existing cleanup value semantics. -/
private theorem seqRun_eq_on {sem sem' : Sem} :
    ∀ ms : List MInst,(∀ i ∈ ms,sem i = sem' i) → ∀ ρ world,seqRun sem ms ρ world = seqRun sem' ms ρ world := by
  intro ms
  induction ms with
  | nil => intro _ _ _; rfl
  | cons i ms ih =>
    intro same ρ world
    have head := same i (List.mem_cons_self)
    have tail := ih (fun j hj => same j (List.mem_cons_of_mem i hj))
    simp only [seqRun,head,tail]

theorem Layout.return_function_with {f : Clif.Function} {result : Stock.Result}
    (layout : Layout f result) (run : Stock.lower f = .ok result)
    (scope : LowerScope f) (dominated : Dominated f) {env : Clif.Env} {cp : Clif.Program}
    (subset : InSubset cp f) {args : List Clif.Val} {fr : Clif.Frame} {cm outMem : Clif.Mem}
    (entered : SourceEntry f args fr) {fuel : Nat} {vals : List Clif.Val}
    (returned : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .returned vals outMem)
    {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {MR : MemRelT}
    (calls : XCallsOk env (f.externs.map (·.2)) MR X)
    {isem : Sem} (driver : DriverSem isem)
    (callSem : ∀ info,isem (.call info) = csem F ctx X.voidCalls (.call info))
    (returnSem : isem (.rets []) = csem F ctx X.voidCalls (.rets []))
    (stable : MRStable F MR) {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms isem)
    {w : Arm.ArmState} (memory : MR fr.slots cm w) (arguments : ArgsAtEntry F f.sig args w) :
    ∃ ρ,RunOkABI f result.code isem MR fr.slots ⟨0,0,ρ,w⟩ (.returned vals outMem) := by
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
  subst vals
  obtain ⟨event,block,prelude,tail,ρ,w1,events,entryBlock,placed,parts,preRun,mem1,values,same,suffix,tailEq⟩ :=
    stock_lower_entry_prelude_refines_frame run scope dominated entered
      driver memorySem stable memory arguments
  have held := entry_values_resolved run scope dominated events entered values
  let inputValues := layout.args.map (fun x => ρ (aliasNum result.final.alias (sourceKey event.ctx x)))
  have holds : AllHold sourceArgs inputValues := call_values_hold held read
  have arity : sourceArgs.length = layout.ext.sig.params.length := by
    have count := congrArg List.length argTypes
    simpa only [Clif.AbiParam.tys,List.length_map] using count
  have argsAt : ArgsAt layout.ext.sig sourceArgs inputValues w1 :=
    (argsAt_iff_of_regs layout.sizes layout.registers arity).mpr holds
  have member : layout.ext ∈ f.externs.map (·.2) := externsIn_self f layout.fn layout.ext layout.lookup
  obtain ⟨actual,w2,callRun,_,_,mem2⟩ := calls layout.ext member g fr.slots cm w1
    (some layout.ext.name) inputValues inputValues sourceArgs [] after callee (Or.inl ⟨rfl,rfl⟩)
    argsAt mem1 called (by rw [layout.void]; rfl)
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
  have machineCall : seqRun isem
      [.call ⟨.sym layout.ext.name,retPairs resolvedPairs,[]⟩] ρ w1 = some (.fall ρ w2) := by
    rw [seqRun_eq_on (sem' := csem F ctx X.voidCalls) _ (by
      intro i member
      have equal : i = .call ⟨.sym layout.ext.name,retPairs resolvedPairs,[]⟩ := by simpa using member
      subst i
      exact callSem _) ρ w1]
    exact seqRun_call_voidCalls_int (F := F) (ctx := ctx) (actualArgs.symm ▸ callRun)
  have machineReturn : seqRun isem [.rets []] ρ w2 =
      some (.stop 0 (.rets []) #[] ρ w2 [] w2 .ret) := by
    rw [seqRun_eq_on (sem' := csem F ctx X.voidCalls) _ (by
      intro i member
      have equal : i = .rets [] := by simpa using member
      subst i
      exact returnSem) ρ w2]
    rfl
  have bodyRun := seqRun_append_fall_stop isem machineCall machineReturn
  have complete := seqRun_append_fall_stop isem preRun bodyRun
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
  have segment : SegAt block 0
      (prelude.toList ++ [.call ⟨.sym layout.ext.name,retPairs resolvedPairs,[]⟩,.rets []]) :=
    segAt_of_toList (L₁ := []) (by simpa only [List.nil_append] using blockList)
  obtain ⟨path,_,instruction,operands,ran,_,_⟩ := seqRun_stop_star placed segment complete
  refine ⟨entrySeed event.ctx fr,[],[],w2,after,?_,layout.retABI,rfl,?_,mem2,freed⟩
  · exact ⟨0,0+(0+1+prelude.toList.length),ρ,w2,block,#[],[],path,placed,instruction,rfl,rfl,(by rw [returnSem]; rfl)⟩
  · simp [PrefixHold]

theorem Layout.return_function_value {f : Clif.Function} {result : Stock.Result}
    (layout : Layout f result) (run : Stock.lower f = .ok result)
    (scope : LowerScope f) (dominated : Dominated f) {env : Clif.Env} {cp : Clif.Program}
    (subset : InSubset cp f) {args : List Clif.Val} {fr : Clif.Frame} {cm outMem : Clif.Mem}
    (entered : SourceEntry f args fr) {fuel : Nat} {vals : List Clif.Val}
    (returned : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .returned vals outMem)
    {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {MR : MemRelT}
    (calls : XCallsOk env (f.externs.map (·.2)) MR X)
    (stable : MRStable F MR) {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms (Backend.DeadCleanup.valueSem F ctx X.voidCalls))
    {w : Arm.ArmState} (memory : MR fr.slots cm w) (arguments : ArgsAtEntry F f.sig args w) :
    ∃ ρ,RunOkABI f result.code (Backend.DeadCleanup.valueSem F ctx X.voidCalls) MR fr.slots ⟨0,0,ρ,w⟩ (.returned vals outMem) := by
  exact layout.return_function_with (ctx := ctx) run scope dominated subset entered returned calls
    (Backend.DeadCleanup.driverSem_valueSem F ctx X.voidCalls) (by intro info; rfl) rfl
    stable memorySem memory arguments

theorem Layout.return_function_abi_read {f : Clif.Function} {result : Stock.Result}
    (layout : Layout f result) (run : Stock.lower f = .ok result)
    (scope : LowerScope f) (dominated : Dominated f) {env : Clif.Env} {cp : Clif.Program}
    (subset : InSubset cp f) {args : List Clif.Val} {fr : Clif.Frame} {cm outMem : Clif.Mem}
    (entered : SourceEntry f args fr) {fuel : Nat} {vals : List Clif.Val}
    (returned : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .returned vals outMem)
    {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {MR : MemRelT}
    (calls : XCallsOk env (f.externs.map (·.2)) MR X)
    (stable : MRStable F MR) {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms (E2E.ABIReadOnly.sem F ctx X.voidCalls))
    {w : Arm.ArmState} (memory : MR fr.slots cm w) (arguments : ArgsAtEntry F f.sig args w) :
    ∃ ρ,RunOkABI f result.code (E2E.ABIReadOnly.sem F ctx X.voidCalls) MR fr.slots ⟨0,0,ρ,w⟩ (.returned vals outMem) := by
  exact layout.return_function_with (ctx := ctx) run scope dominated subset entered returned calls
    (E2E.ABIReadOnly.driver F ctx X.voidCalls) (by intro info; rfl) rfl
    stable memorySem memory arguments

end Backend.Stock.VoidCall

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.DeadCleanup
set_option autoImplicit false
set_option Elab.async false

/-- Original source contracts reach the actual checked machine and retain every per-state fact. -/
theorem backend_correct_worldX_stock_void_call {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {result : Stock.Result} {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (checked : Stock.VoidCall.check f result.code = true) {cleanup : Bool}
    (hc : CompiledStockArithmeticStage f cleanup k result vcp rf af fa fb)
    (noTry : result.code.hasTryCall = false) (subset : InSubset p f)
    {X : ExtSem} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (covered : FormsCovered ⟨fa.k,af.slotBase⟩ vcp)
    (calls : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F,syms,slotOff,(RAFrame.compute vcp rf).intBase⟩ f c) X)
    (symbols : ∀ n b,syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (slot : af.slotBase = slotOff)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (entered : ClifEntry f args cs)
    (memory : RelW ⟨F,syms,slotOff,(RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (arguments : ArgsAtEntry F f.sig args w₀) (fuel : Nat) :
    ∀ vals cm,Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        ReturnABI f us ∧ us.length = outs.length ∧ PrefixHold vals outs ∧
        MemRel F syms cm w ∧ result.code.RetsSite us ∧
        ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
          ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
          ∃ n,ActRet ra F G us outs w s (runX (ArmStepX X H fa) n s) ∧
            PostTrace fa af base (ArmStepX X H fa) s n ∧
            ∀ i < n,actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
              (runX (ArmStepX X H fa) i s) := by
  intro vals cm returned
  obtain ⟨actual,lowered,equal,scope,dominated,abi,⟨layout⟩,edges⟩ := Stock.VoidCall.check_sound checked
  have sameResult : actual = result := Except.ok.inj (lowered.symm.trans hc.lower)
  subst actual
  have state : (⟨cs.frame,[],cs.mem⟩ : Clif.State) = cs := by
    have callers := entered.callers
    cases cs
    cases callers
    rfl
  obtain ⟨ρ,source⟩ := layout.return_function_value hc.lower scope dominated subset entered.stockSourceEntry
    (by rwa [state]) calls
    (mrStable_relW ⟨F,syms,slotOff,(RAFrame.compute vcp rf).intBase⟩ f c)
    (memRefines_valueSem F ⟨fa.k,af.slotBase⟩ X.voidCalls slot symbols) memory arguments
  obtain ⟨us,outs,w,cm0,reached,pins,arity,values,mem,freed⟩ := source
  have staged := StockArithmeticStage_returns hc.prepOk reached
  have site : result.code.RetsSite us := by
    obtain ⟨b,j,ρ,w₁,vb,ops,vs,_,atBlock,atInst,_⟩ := reached
    exact ⟨b,vb,j,atBlock,atInst⟩
  have finalMemory : MemRel F syms cm w := by
    rw [freed]
    exact memRel_leave (memRel_free mem.1.1 _)
  have preparedNoTry : vcp.hasTryCall = false := noTryCall_of_prepCheck hc.prepOk (by
    cases cleanup with
    | false => exact noTry
    | true => exact Backend.DeadCleanup.prune_noTryCall noTry)
  refine ⟨us,outs,w,pins,arity,values,finalMemory,site,?_⟩
  intro H G base ra s entry
  have internal := entry.voidCalls preparedNoTry
  have machine := regLevelCorrect_worldX_value hc.check hc.alloc hc.emit hc.layout
    (X := X.voidCalls) (H := H) (K := K) (G := G) (gv := GotV vcp)
    covered internal.abi internal.stack internal.gfree (by rw [internal.hF]; exact internal.calls)
    (by rw [internal.hF]; exact internal.tries) (by rw [internal.hF]; exact internal.tls)
    (by rw [internal.hF]; exact internal.body) ρ
  rw [internal.hF] at machine
  obtain ⟨n,⟨ret,regs,world,frame,kept,program,trace⟩,good⟩ :=
    machine.1 us outs w (vReturns_gotV_value staged)
  exact ⟨n,⟨ret,regs,world,frame,kept,program⟩,trace,fun i before => actGoodX_of_voidCalls (good i before)⟩

end E2E

namespace E2E.VoidCallMachineWitness
open Backend Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private structure Data (cleanup : Bool) where
  result : Stock.Result
  prepared : VCode
  allocated : RFunc
  frame : AFunc
  assembly : FnAsm
  binary : FnBin
  lowered : Stock.lower VoidCallViewWitness.caller = .ok result
  source : Stock.VoidCall.check VoidCallViewWitness.caller result.code = true
  preparedRun : Backend.prepare (Stock.Arithmetic.stage cleanup result.code) = .ok prepared
  prepOk : prepCheck (Stock.Arithmetic.stage cleanup result.code) prepared = true
  checkRun : checkAlloc prepared allocated = .ok ()
  allocRun : lowerRFunc prepared allocated = .ok frame
  emitRun : emitFunc 0 frame = .ok assembly
  layoutRun : assembly.layout = .ok binary
  covered : FormsCovered ⟨assembly.k,frame.slotBase⟩ prepared
  noTry : result.code.hasTryCall = false

private def candidate (cleanup : Bool) : Except String (Data cleanup) :=
  match lowered : Stock.lower VoidCallViewWitness.caller with
  | .error message => .error message
  | .ok result =>
    if source : Stock.VoidCall.check VoidCallViewWitness.caller result.code = true then
      match preparedRun : Backend.prepare (Stock.Arithmetic.stage cleanup result.code) with
      | .error message => .error message
      | .ok prepared =>
        if prepOk : prepCheck (Stock.Arithmetic.stage cleanup result.code) prepared = true then
          match allocatedRun : leanAlloc prepared with
          | .error message => .error message
          | .ok allocated =>
            match checkRun : checkAlloc prepared allocated with
            | .error message => .error message
            | .ok () =>
              match allocRun : lowerRFunc prepared allocated with
              | .error message => .error message
              | .ok frame =>
                match emitRun : emitFunc 0 frame with
                | .error message => .error message
                | .ok assembly =>
                  match layoutRun : assembly.layout with
                  | .error message => .error message
                  | .ok binary =>
                    if covered : formsCoveredB ⟨assembly.k,frame.slotBase⟩ prepared = true then
                      if noTry : result.code.hasTryCall = false then
                        .ok ⟨result,prepared,allocated,frame,assembly,binary,lowered,source,
                          preparedRun,prepOk,checkRun,allocRun,emitRun,layoutRun,
                          (formsCoveredB_iff _ _).mp covered,noTry⟩
                      else .error "unexpected try-call"
                    else .error "forms are not covered"
        else .error "prepare check rejected"
    else .error "source admission rejected"

private theorem candidates_ok : ((candidate false).isOk && (candidate true).isOk) = true := by
  native_decide

/-- Both real cleanup modes inhabit every static premise of the complete machine theorem. -/
theorem compiled_caller (cleanup : Bool) :
    ∃ (result : Stock.Result) (prepared : VCode) (allocated : RFunc) (frame : AFunc)
      (assembly : FnAsm) (binary : FnBin),
      Stock.VoidCall.check VoidCallViewWitness.caller result.code = true ∧
      CompiledStockArithmeticStage VoidCallViewWitness.caller cleanup 0 result prepared allocated frame assembly binary ∧
      result.code.hasTryCall = false ∧ FormsCovered ⟨assembly.k,frame.slotBase⟩ prepared := by
  have available : (candidate cleanup).isOk = true := by
    have both := Bool.and_eq_true_iff.mp candidates_ok
    cases cleanup with
    | false => exact both.1
    | true => exact both.2
  cases found : candidate cleanup with
  | error message => rw [found] at available; cases available
  | ok d =>
    exact ⟨d.result,d.prepared,d.allocated,d.frame,d.assembly,d.binary,d.source,
      ⟨d.lowered,d.preparedRun,d.prepOk,d.checkRun,d.allocRun,d.emitRun,d.layoutRun⟩,d.noTry,d.covered⟩

end E2E.VoidCallMachineWitness

#print axioms E2E.XNI.voidCalls
#print axioms E2E.XTls.voidCalls
#print axioms Backend.Stock.VoidCall.Layout.return_function_with
#print axioms Backend.Stock.VoidCall.Layout.return_function_value
#print axioms Backend.Stock.VoidCall.Layout.return_function_abi_read
#print axioms E2E.backend_correct_worldX_stock_void_call
#print axioms E2E.VoidCallMachineWitness.compiled_caller -- witness: native_decide
