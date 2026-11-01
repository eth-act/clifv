import FV.Backend.StockVoidCallCheck
import FV.Backend.Proof.StockTermContract
import FV.E2E.StockVoidCallView
import FV.Backend.Proof.StockSourceEntry
import FV.Backend.Proof.StockMemoryNotrap
import FV.Backend.Proof.StockEntryPrelude

namespace Backend.Stock.VoidCall
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

private theorem empty_return_run {env : Clif.Env} {cp : Clif.Program} {fr : Clif.Frame}
    {cm outMem : Clif.Mem} {fuel : Nat} {vals : List Clif.Val}
    (body : fr.body = []) (term : fr.term = .ret []) (noReturns : fr.func.sig.returns = [])
    (returned : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .returned vals outMem) :
    vals = [] ∧ outMem = (cm.free (fr.slots.map (·.2))).leave := by
  have step : Clif.step env cp ⟨fr,[],cm⟩ = .done [] (cm.free (fr.slots.map (·.2))).leave := by
    simp [Clif.step,body,term,Clif.stepTerm,Clif.Frame.getMany,Clif.returnValues,noReturns,
      Clif.AbiParam.tys,Clif.checkTys,Clif.Res.check,Clif.StepResult.ofRes]
  cases fuel with
  | zero => cases returned
  | succ fuel =>
    rw [Clif.runLoop_succ,step] at returned
    cases returned
    exact ⟨rfl,rfl⟩

/-- Original source execution supplies the real external call, typed arguments, and final memory. -/
theorem source_return_call {env : Clif.Env} {cp : Clif.Program} {fr : Clif.Frame}
    {cm outMem : Clif.Mem} {fuel : Nat} {vals : List Clif.Val}
    {fn : Clif.FnRef} {args : List Nat} {ext : Clif.ExtFunc}
    (body : fr.body = [⟨[],.call fn args⟩]) (term : fr.term = .ret [])
    (noReturns : fr.func.sig.returns = []) (lookup : fr.func.extern? fn = some ext)
    (external : cp.func? ext.name = none) (void : ext.sig.returns = [])
    (returned : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .returned vals outMem) :
    ∃ (g : List Clif.Val → Clif.Mem → Clif.Outcome) (arguments : List Clif.Val) (after : Clif.Mem),
      env.extern ext.name = some g ∧ fr.getMany args = .ok arguments ∧
      arguments.map (·.ty) = Clif.AbiParam.tys ext.sig.params ∧
      g arguments cm = .returned [] after ∧ vals = [] ∧
      outMem = (after.free (fr.slots.map (·.2))).leave := by
  cases fuel with
  | zero => cases returned
  | succ fuel =>
    have step : Clif.step env cp ⟨fr,[],cm⟩ =
        Clif.StepResult.ofRes (instOutcome env cp fr cm (.call fn args))
          (fun pair => Clif.continueWith ⟨fr,[],cm⟩ [] [] pair.1 pair.2) := by
      simp only [Clif.step,body]
      apply stepCall_eq
      intro e found
      have same : e = ext := Option.some.inj (found.symm.trans lookup)
      subst e
      exact external
    rw [Clif.runLoop_succ,step] at returned
    cases outcome : instOutcome env cp fr cm (.call fn args) with
    | trap code => simp only [outcome,Clif.StepResult.ofRes] at returned; cases returned
    | stuck message => simp only [outcome,Clif.StepResult.ofRes] at returned; cases returned
    | ok pair =>
      obtain ⟨results,after⟩ := pair
      obtain ⟨e,arguments,g,found,read,types,called,run,retTypes⟩ := instOutcome_call_ok outcome
      have same : e = ext := Option.some.inj (found.symm.trans lookup)
      subst e
      have empty : results = [] := by
        have sizes := congrArg List.length retTypes
        simpa only [void,Clif.AbiParam.tys,List.map_nil,List.length_nil,List.length_map,
          List.length_eq_zero_iff] using sizes
      subst results
      simp only [outcome,Clif.StepResult.ofRes,Clif.continueWith,Clif.Regs.setMany] at returned
      obtain ⟨empty,memory⟩ := empty_return_run (fr := {fr with body := []}) rfl term noReturns returned
      exact ⟨g,arguments,after,called,read,types,run,empty,memory⟩


/-- The original explicit-trap premise excludes a hidden callee trap for this source class. -/
theorem source_call_notrap {env : Clif.Env} {cp : Clif.Program} {fr : Clif.Frame}
    {cm : Clif.Mem} {fn : Clif.FnRef} {args : List Nat}
    (body : fr.body = [⟨[],.call fn args⟩]) (term : fr.term = .ret [])
    (external : ∀ e,fr.func.extern? fn = some e → cp.func? e.name = none)
    (explicit : E2E.TrapsExplicit env cp ⟨fr,[],cm⟩) (fuel : Nat) (code : Clif.TrapCode) :
    Clif.runLoop env cp fuel ⟨fr,[],cm⟩ ≠ .trapped code := by
  intro trapped
  cases fuel with
  | zero => cases trapped
  | succ fuel =>
    have step : Clif.step env cp ⟨fr,[],cm⟩ =
        Clif.StepResult.ofRes (instOutcome env cp fr cm (.call fn args))
          (fun pair => Clif.continueWith ⟨fr,[],cm⟩ [] [] pair.1 pair.2) := by
      simp only [Clif.step,body]
      exact stepCall_eq env cp ⟨fr,[],cm⟩ [] [] fn args external
    rw [Clif.runLoop_succ,step] at trapped
    cases outcome : instOutcome env cp fr cm (.call fn args) with
    | trap c =>
      have halted : Clif.step env cp ⟨fr,[],cm⟩ = .trapped c := by
        rw [step,outcome]
        rfl
      have impossible := explicit.stmt ⟨fr,[],cm⟩ c ⟨[],.call fn args⟩ [] (.refl _) halted body
      cases impossible
    | stuck message => simp only [outcome,Clif.StepResult.ofRes] at trapped; cases trapped
    | ok pair =>
      obtain ⟨results,after⟩ := pair
      cases results with
      | nil =>
        simp only [outcome,Clif.StepResult.ofRes,Clif.continueWith,Clif.Regs.setMany] at trapped
        exact Stock.Proof.OrdinaryBody.ordinary_source_notrap fuel
          ⟨{fr with body := []},[],after⟩ rfl
          (by intro stm member; cases member) term code trapped
      | cons value rest =>
        simp only [outcome,Clif.StepResult.ofRes,Clif.continueWith,Clif.Regs.setMany] at trapped
        cases trapped

/-- Existing held-value facts derive all call arguments from original source reads. -/
theorem call_values_hold {ctx : Ctx} {fr : Clif.Frame} {ρ : Nat → CV}
    (held : Stock.Proof.ValuesHeld (fun _ => True) ctx fr ρ)
    {args : List Nat} {vals : List Clif.Val} (read : fr.getMany args = .ok vals) :
    AllHold vals (args.map (fun x => ρ (sourceKey ctx x))) := by
  obtain ⟨length,values⟩ := getMany_ok read
  constructor
  · simp only [List.length_map]
    exact length
  · intro j v actual value atValue
    simp only [List.getElem?_map,Option.map_eq_some_iff] at atValue
    obtain ⟨x,atArg,rfl⟩ := atValue
    have found := values j x v atArg value
    obtain ⟨key,mapped,hold⟩ := held x trivial v found
    simpa only [sourceKey,mapped] using hold

/-- Original entry bindings retain every value after final Stock aliases resolve. -/
theorem entry_values_resolved {f : Clif.Function} {result : Stock.Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : Stock.BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {args : List Clif.Val} {fr : Clif.Frame} (entered : Stock.Proof.SourceEntry f args fr)
    {ρ : Nat → CV} (held : Stock.Proof.ValuesHeld (fun _ => True) event.ctx fr ρ) :
    Stock.Proof.ValuesHeld (fun _ => True) event.ctx fr
      (fun key => ρ (Stock.Proof.aliasNum result.final.alias key)) := by
  obtain ⟨b,regs,entry,types,paramTypes,set,frame⟩ := entered
  have atBlock : f.blocks[0]? = some b := by
    simpa only [Clif.Function.entry?,List.head?_eq_getElem?] using entry
  have maps := (Stock.Proof.stock_lower_record_context run scope events).2.1
  intro x needed v found
  obtain ⟨key,mapped,value⟩ := held x needed v found
  have parameter : x ∈ b.params.map (·.1) := by
    by_cases member : x ∈ b.params.map (·.1)
    · exact member
    · have frameRegs : fr.regs = regs := congrArg Clif.Frame.regs frame
      have original : regs x = some v := by simpa only [frameRegs] using found
      rw [setMany_other set member] at original
      cases original
  have resultMap : result.ctx.valueReg? x = some (.vreg key .int) := by rwa [← maps]
  have alias := Stock.Proof.stock_lower_parameter_resolves run dominated.ssa atBlock parameter resultMap
  exact ⟨key,mapped,by simpa only [alias] using value⟩

end Backend.Stock.VoidCall
namespace Backend.Stock.VoidCall
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof E2E
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Internal source and actual scan facts. A class checker derives these facts from data. -/
structure Layout (f : Clif.Function) (result : Stock.Result) where
  block : Clif.Block
  fn : Clif.FnRef
  args : List Nat
  ext : Clif.ExtFunc
  blocks : f.blocks = [block]
  body : block.body = [⟨[],.call fn args⟩]
  term : block.term = .ret []
  noReturns : f.sig.returns = []
  void : ext.sig.returns = []
  lookup : f.extern? fn = some ext
  bytes : List Nat
  sizes : sigParamBytes ext.sig = .ok bytes
  registers : bytes.length ≤ 8
  retABI : ReturnABI f []
  code : ∀ event ∈ result.blockScans.toList,event.block = 0 → ∃ pairs : List (Nat × Reg),
    event.output.code = #[.call ⟨.sym ext.name,retPairs pairs,[]⟩,.rets []] ∧
    pairs.map (·.1) = args.map (sourceKey event.ctx)

/-- Original source execution and actual Stock records give the complete virtual return run. -/
theorem Layout.return_function {f : Clif.Function} {result : Stock.Result}
    (layout : Layout f result) (run : Stock.lower f = .ok result)
    (scope : LowerScope f) (dominated : Dominated f) {env : Clif.Env} {cp : Clif.Program}
    (subset : InSubset cp f) {args : List Clif.Val} {fr : Clif.Frame} {cm outMem : Clif.Mem}
    (entered : SourceEntry f args fr) {fuel : Nat} {vals : List Clif.Val}
    (returned : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .returned vals outMem)
    {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {MR : MemRelT}
    (calls : XCallsOk env (f.externs.map (·.2)) MR X)
    (stable : MRStable F MR) {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms (csem F ctx X.voidCalls))
    {w : Arm.ArmState} (memory : MR fr.slots cm w) (arguments : ArgsAtEntry F f.sig args w) :
    ∃ ρ,RunOkABI f result.code (csem F ctx X.voidCalls) MR fr.slots ⟨0,0,ρ,w⟩ (.returned vals outMem) := by
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
      (driverSem_csem F ctx X.voidCalls) memorySem stable memory arguments
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
  have machineCall := seqRun_call_voidCalls_int (F := F) (ctx := ctx) (actualArgs.symm ▸ callRun)
  have machineReturn : seqRun (csem F ctx X.voidCalls) [.rets []] ρ w2 =
      some (.stop 0 (.rets []) #[] ρ w2 [] w2 .ret) := rfl
  have bodyRun := seqRun_append_fall_stop (csem F ctx X.voidCalls) machineCall machineReturn
  have complete := seqRun_append_fall_stop (csem F ctx X.voidCalls) preRun bodyRun
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
  · exact ⟨0,0+(0+1+prelude.toList.length),ρ,w2,block,#[],[],path,placed,instruction,rfl,rfl,rfl⟩
  · simp [PrefixHold]

end Backend.Stock.VoidCall

namespace Backend.Stock.VoidCall
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false

/-- Data checks derive the complete internal layout; callers supply no run premise. -/
def Layout.of_checks {f : Clif.Function} {result : Stock.Result} {data : SourceData}
    (source : sourceB f data = true) (code : codeB data result = true) : Layout f result := by
  simp only [sourceB,Bool.and_eq_true,decide_eq_true_eq,and_assoc] at source
  obtain ⟨blocks,body,term,noReturns,void,lookup,sizes,registers,pins⟩ := source
  refine ⟨data.block,data.fn,data.args,data.ext,blocks,body,term,noReturns,void,lookup,
    data.bytes,sizes,registers,?_,?_⟩
  · simpa only [ReturnABI,List.length_nil,List.map_nil] using pins
  · intro event member atEntry
    have checked := List.all_eq_true.mp code event member
    simp only [scanB,atEntry,beq_self_eq_true,↓reduceIte] at checked
    split at checked
    · rename_i info shape
      simp only [Bool.and_eq_true,decide_eq_true_eq,List.isEmpty_iff,and_assoc] at checked
      obtain ⟨dest,defs,uses,keys⟩ := checked
      have same : info = ⟨.sym data.ext.name,retPairs (callUses info.uses),[]⟩ := by
        cases info
        simp only [CallInfo.mk.injEq]
        exact ⟨dest,uses,defs⟩
      refine ⟨callUses info.uses,?_,keys⟩
      apply Array.toList_inj.mp
      rw [shape]
      exact congrArg (fun c : CallInfo => [MInst.call c,MInst.rets []]) same
    · cases checked

end Backend.Stock.VoidCall

namespace Backend.Stock.VoidCall
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false

/-- The executable check derives actual provenance, original source conditions, and the layout. -/
theorem check_sound {f : Clif.Function} {vc : VCode} (checked : check f vc = true) :
    ∃ result,Stock.lower f = .ok result ∧ result.code = vc ∧ LowerScope f ∧ Dominated f ∧
      sigAbiOk f.sig = true ∧ Nonempty (Layout f result) ∧
      result.edgeArgs.all (fun row => row.all (·.isEmpty)) = true := by
  unfold check at checked
  cases data : sourceData? f with
  | none => simp only [data,Bool.false_eq_true] at checked
  | some source =>
    simp only [data] at checked
    cases lowered : Stock.lower f with
    | error message => simp only [lowered,Bool.and_false,Bool.false_eq_true] at checked
    | ok result =>
      simp only [lowered,Bool.and_eq_true,decide_eq_true_eq,and_assoc] at checked
      obtain ⟨sourceOk,scope,dominated,abi,equal,code,edges⟩ := checked
      exact ⟨result,rfl,equal,lowerScope_of scope,dominated_of dominated,abi,
        ⟨Layout.of_checks sourceOk code⟩,edges⟩

end Backend.Stock.VoidCall

namespace Backend.Stock.VoidCall
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof E2E
set_option autoImplicit false
set_option Elab.async false

/-- Call-aware source contract. The original call model supplies its callee facts internally. -/
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
    ∀ {sb : Nat} {syms : String → Option Nat},MemRefines F sb syms (csem F ctx X.voidCalls) →
    ∀ {w : Arm.ArmState},MR fr.slots cm w → ArgsAtEntry F f.sig args w →
      ∃ ρ,RunOkABI f vc (csem F ctx X.voidCalls) MR fr.slots ⟨0,0,ρ,w⟩ (.returned vals outMem)
  notrap : ∀ {env : Clif.Env} {cp : Clif.Program},InSubset cp f →
    ∀ {args : List Clif.Val} {fr : Clif.Frame} {cm : Clif.Mem},SourceEntry f args fr →
      TrapsExplicit env cp ⟨fr,[],cm⟩ → ∀ fuel code,Clif.runLoop env cp fuel ⟨fr,[],cm⟩ ≠ .trapped code

/-- Executable source and actual-record checks supply both complete source obligations. -/
theorem check_domain {f : Clif.Function} {vc : VCode} (checked : check f vc = true) : Domain f vc := by
  obtain ⟨result,lowered,equal,scope,dominated,abi,⟨layout⟩,_⟩ := check_sound checked
  refine ⟨scope,dominated,abi,⟨result,lowered,equal⟩,?_,?_⟩
  · intro env cp subset args fr cm outMem entered fuel vals returned F ctx X MR calls stable sb syms
      memorySem w memory arguments
    rw [← equal]
    exact layout.return_function lowered scope dominated subset entered returned calls stable
      memorySem memory arguments
  · intro env cp subset args fr cm entered explicit fuel code
    obtain ⟨b,regs,found,types,paramTypes,set,frame⟩ := entered
    have first : f.entry? = some layout.block := by simp only [Clif.Function.entry?,layout.blocks,List.head?_cons]
    cases Option.some.inj (found.symm.trans first)
    have func : fr.func = f := congrArg Clif.Frame.func frame
    have body : fr.body = [⟨[],.call layout.fn layout.args⟩] :=
      (congrArg Clif.Frame.body frame).trans layout.body
    have term : fr.term = .ret [] := (congrArg Clif.Frame.term frame).trans layout.term
    apply source_call_notrap body term ?_ explicit fuel code
    intro e lookup
    have same : e = layout.ext := by
      rw [func,layout.lookup] at lookup
      exact Option.some.inj lookup.symm
    subst e
    exact subset.externCalls layout.block (by simp [layout.blocks]) ⟨[],.call layout.fn layout.args⟩
      (by simp [layout.body]) layout.fn layout.args rfl layout.ext layout.lookup

end Backend.Stock.VoidCall
