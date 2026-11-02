import FV.Backend.Proof.LowerSim
import FV.Backend.Proof.IselCtlCallF
import FV.Backend.Proof.StockSourceEntry
import FV.Backend.Proof.StockMemoryNotrap
import FV.E2E.Statement
import FV.Backend.Proof.StockEntryPrelude
import FV.E2E.LinkWorld
import FV.Backend.Proof.IselCtlCallF
import FV.E2E.PreparedReturnPinCallerBoundaryWitness

namespace Backend.Proof
open Backend E2E Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Internal call view for a source caller that consumes no explicit results. -/
def ExtSem.voidCalls (X : ExtSem) : ExtSem :=
  {X with call := fun d uses w => (X.call d uses w).map fun p => ([],p.2)}

theorem ExtSem.voidCalls_call {X : ExtSem} {d : Option String} {uses outs : List CV}
    {w w' : Arm.ArmState} (run : X.call d uses w = some (outs,w')) :
    X.voidCalls.call d uses w = some ([],w') := by
  simp only [ExtSem.voidCalls,run,Option.map_some]

theorem ExtSem.voidCalls_call_inv {X : ExtSem} {d : Option String} {uses outs : List CV}
    {w w' : Arm.ArmState} (run : X.voidCalls.call d uses w = some (outs,w')) :
    ∃ actual,X.call d uses w = some (actual,w') ∧ outs = [] := by
  cases actual : X.call d uses w with
  | none => simp [ExtSem.voidCalls,actual] at run
  | some pair =>
    obtain ⟨values,world⟩ := pair
    simp only [ExtSem.voidCalls,actual,Option.map_some,Option.some.injEq,Prod.mk.injEq] at run
    obtain ⟨rfl,rfl⟩ := run
    exact ⟨values,rfl,rfl⟩

/-- The executable machine keeps the complete original hooks, symbols, and state transition. -/
theorem ArmStepX_voidCalls (X : ExtSem) (H : ArmHooks) (fa : FnAsm) :
    ArmStepX X.voidCalls H fa = ArmStepX X H fa := rfl

theorem csem_call_voidCalls_inv {X : ExtSem} {F : BitVec 64 → Prop} {ctx : FnCtx}
    {info : CallInfo} {uses outs : List CV} {w w' : Arm.ArmState} {ctl : Ctl}
    (run : csem F ctx X.voidCalls (.call info) uses w = some (outs,w',ctl)) :
    ∃ actual,csem F ctx X (.call info) uses w = some (actual,w',ctl) ∧ outs = [] := by
  change (X.voidCalls.call (match info.dest with | .sym n => some n | .reg _ => none) uses w).map
    (fun p => (p.1,p.2,Ctl.next)) = some (outs,w',ctl) at run
  cases actual : X.voidCalls.call (match info.dest with | .sym n => some n | .reg _ => none) uses w with
  | none => simp only [actual,Option.map_none] at run; cases run
  | some pair =>
    obtain ⟨values,world⟩ := pair
    simp only [actual,Option.map_some,Option.some.injEq,Prod.mk.injEq] at run
    obtain ⟨rfl,rfl,rfl⟩ := run
    obtain ⟨old,oldRun,empty⟩ := ExtSem.voidCalls_call_inv actual
    refine ⟨old,?_,empty⟩
    change (X.call (match info.dest with | .sym n => some n | .reg _ => none) uses w).map
      (fun p => (p.1,p.2,Ctl.next)) = _
    rw [oldRun]
    rfl

/-- A successful try-call in the void view also supplies the original call premise. -/
theorem csem_tryCall_voidCalls_inv {X : ExtSem} {F : BitVec 64 → Prop} {ctx : FnCtx}
    {info : CallInfo} {ti : TryInfo} {uses outs : List CV} {w w' : Arm.ArmState} {ctl : Ctl}
    (run : csem F ctx X.voidCalls (.tryCall info ti) uses w = some (outs,w',ctl)) :
    ∃ actual,csem F ctx X (.tryCall info ti) uses w = some (actual,w',ctl) := by
  change (((X.call (match info.dest with | .sym n => some n | .reg _ => none) uses w).map
    (fun p => ([],p.2))).filter fun p => decide (ti.rets ≤ p.1.length)).map
    (fun p => (p.1 ++ (info.defs.drop p.1.length).map (fun _ => ofX 0),p.2,Ctl.goto ti.handlers.length))
      = some (outs,w',ctl) at run
  cases actual : X.call (match info.dest with | .sym n => some n | .reg _ => none) uses w with
  | none => simp [actual] at run
  | some pair =>
    obtain ⟨values,world⟩ := pair
    simp only [actual,Option.map_some] at run
    by_cases arity : ti.rets ≤ 0
    · simp [Option.filter,arity] at run
      obtain ⟨rfl,rfl,rfl⟩ := run
      refine ⟨values ++ (info.defs.drop values.length).map (fun _ => ofX 0),?_⟩
      have enough : ti.rets ≤ values.length := Nat.le_trans arity (Nat.zero_le _)
      change ((X.call (match info.dest with | .sym n => some n | .reg _ => none) uses w).filter
        (fun p => decide (ti.rets ≤ p.1.length))).map
        (fun p => (p.1 ++ (info.defs.drop p.1.length).map (fun _ => ofX 0),p.2,Ctl.goto ti.handlers.length)) = _
      rw [actual]
      simp [Option.filter,enough]
    · simp [Option.filter,arity] at run


/-- The original physical callee contract supplies the internal void view without a new premise. -/
theorem CalleeOk.voidCalls {F : BitVec 64 → Prop} {K : Nat} {X : ExtSem} {H : ArmHooks}
    {S : CallInfo → Prop} (callee : CalleeOk F K X H S) : CalleeOk F K X.voidCalls H S := by
  constructor
  · intro ctx info site s room stack c wh ops regs i' w outs w' operands checked assigned world aligned err run
    obtain ⟨actual,oldRun,empty⟩ := csem_call_voidCalls_inv run
    obtain ⟨s',executed,same,frame,_,kept,saved⟩ :=
      callee.os ctx info site s room stack c wh ops regs i' w actual w'
        operands checked assigned world aligned err oldRun
    refine ⟨s',executed,same,frame,?_,kept,saved⟩
    rw [empty]
    simp [defRegs]
  · exact callee.pc
  · intro d uses w outs w' run err
    obtain ⟨actual,oldRun,_⟩ := ExtSem.voidCalls_call_inv run
    exact callee.ext d uses w actual w' oldRun err


/-- Successful guarded calls in the internal view retain an original call with the same world. -/
theorem csemV_voidCalls_inv {X : ExtSem} {F : BitVec 64 → Prop} {ctx : FnCtx}
    {gv : Nat → String → Prop} {info : CallInfo} {i : MInst}
    (kind : i = .call info ∨ ∃ ti,i = .tryCall info ti)
    {uses outs : List CV} {w w' : Arm.ArmState} {ctl : Ctl}
    (run : csemV gv F ctx X.voidCalls i uses w = some (outs,w',ctl)) :
    ∃ actual,csemV gv F ctx X i uses w = some (actual,w',ctl) := by
  classical
  rcases kind with rfl | ⟨ti,rfl⟩
  · change (if gotGuard gv X.voidCalls info uses then csem F ctx X.voidCalls (.call info) uses w
      else none) = some (outs,w',ctl) at run
    split at run
    · rename_i guard
      obtain ⟨actual,oldRun,_⟩ := csem_call_voidCalls_inv run
      refine ⟨actual,?_⟩
      change (if gotGuard gv X info uses then csem F ctx X (.call info) uses w else none) = _
      have oldGuard : gotGuard gv X info uses := guard
      simp only [oldGuard,↓reduceIte,oldRun]
    · cases run
  · change (if gotGuard gv X.voidCalls info uses then csem F ctx X.voidCalls (.tryCall info ti) uses w
      else none) = some (outs,w',ctl) at run
    split at run
    · rename_i guard
      obtain ⟨actual,oldRun⟩ := csem_tryCall_voidCalls_inv run
      refine ⟨actual,?_⟩
      change (if gotGuard gv X info uses then csem F ctx X (.tryCall info ti) uses w else none) = _
      have oldGuard : gotGuard gv X info uses := guard
      simp only [oldGuard,↓reduceIte,oldRun]
    · cases run

/-- The original world-relative physical contract supplies the internal call view. -/
theorem CalleeOkG.voidCalls {F G : BitVec 64 → Prop} {K : Nat} {s0 : Arm.ArmState}
    {Pc : BitVec 64 → MInst → Prop} {X : ExtSem} {H : ArmHooks}
    {S : CallInfo → Prop} {gv : Nat → String → Prop}
    (callee : CalleeOkG F K G s0 Pc X H S gv) : CalleeOkG F K G s0 Pc X.voidCalls H S gv := by
  constructor
  · intro ctx info site s room stack keep c wh ops regs i' w outs w' operands checked assigned position
      world aligned err run
    obtain ⟨actual,oldRun⟩ := csemV_voidCalls_inv (Or.inl rfl) run
    obtain ⟨_,_,empty⟩ := csem_call_voidCalls_inv (csemV_sub run)
    obtain ⟨s',executed,same,frame,_,kept,saved⟩ :=
      callee.os ctx info site s room stack keep c wh ops regs i' w actual w'
        operands checked assigned position world aligned err oldRun
    refine ⟨s',executed,same,frame,?_,kept,saved⟩
    rw [empty]
    simp [defRegs]
  · exact callee.pc
  · intro d uses w outs w' run err
    obtain ⟨actual,oldRun,_⟩ := ExtSem.voidCalls_call_inv run
    exact callee.ext d uses w actual w' oldRun err

def RL.voidCalls (R : RL) : RL := {R with X := R.X.voidCalls}

/-- The original call premise follows from the internal one, including successful try-calls. -/
theorem RL.CallPre.of_voidCalls {R : RL} {u : Arm.ArmState} (pre : R.voidCalls.CallPre u) :
    R.CallPre u := by
  obtain ⟨ctx,i,ctl,present,room,stack,keep,c,wh,ops,regs,i',w,outs,w',operands,checked,assigned,
    position,world,aligned,err,run⟩ := pre
  obtain ⟨info,site,kind⟩ := present
  obtain ⟨actual,oldRun⟩ := csemV_voidCalls_inv kind run
  exact ⟨ctx,i,ctl,⟨info,site,kind⟩,room,stack,keep,c,wh,ops,regs,i',w,actual,w',operands,checked,assigned,
    position,world,aligned,err,oldRun⟩

/-- The complete original per-state guarantee survives the internal view. -/
theorem RL.GoodX.of_voidCalls {R : RL} {u : Arm.ArmState} (good : R.voidCalls.GoodX u) :
    R.GoodX u :=
  ⟨good.good,good.err,good.prog,good.line,good.next,good.got,good.blr,
    fun x line call => (good.call x line call).of_voidCalls,good.reads⟩


/-- A call-only source class derives the internal entry from the original complete entry. -/
theorem _root_.E2E.ActEntry.voidCalls {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin} {K : Nat} {F G : BitVec 64 → Prop} {X : ExtSem} {H : ArmHooks}
    {base ra : BitVec 64} {s w : Arm.ArmState}
    (noTry : vcp.hasTryCall = false) (entry : ActEntry vcp rf af fa fb K F G X H base ra s w) :
    ActEntry vcp rf af fa fb K F G X.voidCalls H base ra s w := by
  refine ⟨entry.abi,entry.stack,entry.gfree,entry.hF,entry.calls.voidCalls,?_,?_,entry.body⟩
  · intro impossible
    rw [noTry] at impossible
    cases impossible
  · intro tls
    exact ⟨(entry.tls tls).pc,(entry.tls tls).seq,(entry.tls tls).flags⟩

/-- The complete public per-state guarantee keeps the original external semantics. -/
theorem actGoodX_of_voidCalls {vc : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    {base : BitVec 64} {s u : Arm.ArmState} {X : ExtSem} {H : ArmHooks} {K : Nat}
    {G : BitVec 64 → Prop} {gv : Nat → String → Prop}
    (good : actGoodX vc rf af fa fb base s X.voidCalls H K G gv u) :
    actGoodX vc rf af fa fb base s X H K G gv u := by
  exact RL.GoodX.of_voidCalls good


/-- A real zero-def call executes with the original callee world, regardless of implicit ABI results. -/
theorem seqRun_call_voidCalls {X : ExtSem} {F : BitVec 64 → Prop} {ctx : FnCtx}
    {name : String} {uses : List (Nat × RegClass × Reg)} {ρ : Nat → CV}
    {w w' : Arm.ArmState} {actual : List CV}
    (run : X.call (some name) (uses.map (ρ ·.1)) w = some (actual,w')) :
    seqRun (csem F ctx X.voidCalls) [.call ⟨.sym name,argPairsC uses,[]⟩] ρ w =
      some (.fall ρ w') := by
  have view : csem F ctx X.voidCalls (.call ⟨.sym name,argPairsC uses,callDefsC []⟩)
      (uses.map (ρ ·.1)) w = some ([],w',.next) := by
    change (X.voidCalls.call (some name) (uses.map (ρ ·.1)) w).map
      (fun p => (p.1,p.2,Ctl.next)) = _
    rw [ExtSem.voidCalls_call run]
    rfl
  have execution := seqRun_call_symC view (show ([] : List CV).length = ([] : List (Reg × Nat × RegClass)).length from rfl)
  simpa [callDefOpsC,callDefsC,writeV] using execution


/-- The same internal execution applies to the integer call metadata used by the captured caller. -/
theorem seqRun_call_voidCalls_int {X : ExtSem} {F : BitVec 64 → Prop} {ctx : FnCtx}
    {name : String} {uses : List (Nat × Reg)} {ρ : Nat → CV}
    {w w' : Arm.ArmState} {actual : List CV}
    (run : X.call (some name) (uses.map (ρ ·.1)) w = some (actual,w')) :
    seqRun (csem F ctx X.voidCalls) [.call ⟨.sym name,retPairs uses,[]⟩] ρ w =
      some (.fall ρ w') := by
  have typedRun : X.call (some name) ((uses.map (fun p => (p.1,RegClass.int,p.2))).map (ρ ·.1)) w =
      some (actual,w') := by simpa only [List.map_map,Function.comp_def] using run
  have execution := seqRun_call_voidCalls (F := F) (ctx := ctx) typedRun
  simpa only [argPairsC,retPairs,List.map_map,Function.comp_def] using execution

/-- The original source-call contract supplies every value and memory premise for a void call. -/
theorem XCallsOk.voidCalls_return {env : Clif.Env} {exts : List Clif.ExtFunc} {MR : MemRelT}
    {X : ExtSem} (calls : XCallsOk env exts MR X) {ext : Clif.ExtFunc} (member : ext ∈ exts)
    (noResults : ext.sig.returns = []) {g : List Clif.Val → Clif.Mem → Clif.Outcome} {slots : List (Clif.SlotId × Nat)}
    {cm cm' : Clif.Mem} {w : Arm.ArmState} {d : Option String} {uses args : List CV}
    {vals rvals : List Clif.Val} (found : env.extern ext.name = some g)
    (destination : d = some ext.name ∧ uses = args ∨
      d = none ∧ ext.colocated = false ∧ uses = ofX (X.sym ext.name 0) :: args)
    (arguments : ArgsAt ext.sig vals args w) (memory : MR slots cm w)
    (returned : g vals cm = .returned rvals cm') (arity : rvals.length = ext.sig.returns.length) :
    ∃ w',X.voidCalls.call d uses w = some ([],w') ∧ PrefixHold rvals [] ∧ MR slots cm' w' := by
  obtain ⟨actual,w',run,_,_,mem⟩ :=
    calls ext member g slots cm w d uses args vals rvals cm' found destination arguments memory returned arity
  refine ⟨w',ExtSem.voidCalls_call run,?_,mem⟩
  have empty : rvals = [] := by simpa only [noResults,List.length_nil,List.length_eq_zero_iff] using arity
  rw [empty]
  simp [PrefixHold]

end Backend.Proof

namespace E2E.VoidCallViewWitness
open Backend Backend.Proof Backend.Proof.Driver LinkCheck
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def caller : Clif.Function := PreparedReturnPinCallerBoundaryWitness.input.funcs[1]!.func
private def target : String := PreparedReturnPinCallerBoundaryWitness.input.funcs[0]!.func.name
private def callB (i : MInst) : Bool := match i with
  | .call info => decide (info.dest = .sym target) && info.defs.isEmpty &&
      decide (info.uses = retPairs (decU info.uses))
  | _ => false
private def observed : Bool := match Stock.lower caller with
  | .error _ => false
  | .ok result => !result.code.hasTryCall && result.code.blocks.toList.any fun b => b.insts.toList.any callB
attribute [local irreducible] observed
-- witness: native_decide (the unchanged real mixed-program caller only)
private theorem observed_true : observed = true := by native_decide

/-- The real Stock caller's zero-def call executes for every original callee result and world. -/
theorem actual_stock_call_witness :
    ∃ (result : Stock.Result) (block : VBlock) (uses : List (Nat × Reg)),
      Stock.lower caller = .ok result ∧ result.code.hasTryCall = false ∧
      block ∈ result.code.blocks.toList ∧ .call ⟨.sym target,retPairs uses,[]⟩ ∈ block.insts.toList ∧
      ∀ (X : ExtSem) (F : BitVec 64 → Prop) (ctx : FnCtx) (ρ : Nat → CV)
        (w w' : Arm.ArmState) (actual : List CV),
        X.call (some target) (uses.map (ρ ·.1)) w = some (actual,w') →
        seqRun (csem F ctx X.voidCalls) [.call ⟨.sym target,retPairs uses,[]⟩] ρ w = some (.fall ρ w') := by
  have checked := observed_true
  unfold observed at checked
  cases lowered : Stock.lower caller with
  | error message => simp only [lowered,Bool.false_eq_true] at checked
  | ok result =>
    simp only [lowered,Bool.and_eq_true,Bool.not_eq_true',List.any_eq_true] at checked
    obtain ⟨noTry,block,member,i,present,selected⟩ := checked
    cases i <;> simp only [callB,Bool.false_eq_true] at selected
    rename_i info
    simp only [Bool.and_eq_true,decide_eq_true_eq,List.isEmpty_iff] at selected
    obtain ⟨⟨dest,defs⟩,uses⟩ := selected
    have same : info = ⟨.sym target,retPairs (decU info.uses),[]⟩ := by
      cases info
      simp only [CallInfo.mk.injEq]
      exact ⟨dest,uses,defs⟩
    rw [same] at present
    refine ⟨result,block,decU info.uses,rfl,noTry,member,present,?_⟩
    intro X F ctx ρ w w' actual run
    exact seqRun_call_voidCalls_int run

end E2E.VoidCallViewWitness


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


/-- Read a source register through the actual context map, never its numeric source identifier. -/
def sourceKey (ctx : Ctx) (x : Nat) : Nat :=
  match ctx.valueReg? x with
  | some (.vreg key .int) => key
  | _ => 0

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

structure SourceData where
  block : Clif.Block
  fn : Clif.FnRef
  args : List Nat
  ext : Clif.ExtFunc
  bytes : List Nat

def sourceData? (f : Clif.Function) : Option SourceData :=
  match f.blocks with
  | [block] => match block.body with
    | [⟨[],.call fn args⟩] => do
      let ext ← f.extern? fn
      let bytes ← (sigParamBytes ext.sig).toOption
      pure ⟨block,fn,args,ext,bytes⟩
    | _ => none
  | _ => none

/-- Check the original source and ABI. No execution certificate is an input. -/
def sourceB (f : Clif.Function) (data : SourceData) : Bool :=
  decide (f.blocks = [data.block]) && decide (data.block.body = [⟨[],.call data.fn data.args⟩]) &&
  decide (data.block.term = .ret []) && decide (f.sig.returns = []) &&
  decide (data.ext.sig.returns = []) && decide (f.extern? data.fn = some data.ext) &&
  decide (sigParamBytes data.ext.sig = .ok data.bytes) && decide (data.bytes.length ≤ 8) &&
  decide (returnPins f 0 = some [])

def callUses (uses : List (Reg × Reg)) : List (Nat × Reg) :=
  uses.map fun pair => ((match pair.1 with | .vreg key .int => key | _ => 0),pair.2)

/-- Check actual retained call metadata against original source argument mappings. -/
def scanB (data : SourceData) (event : Stock.BlockScanEvent) : Bool :=
  if event.block == 0 then
    match event.output.code.toList with
    | [.call info,.rets []] =>
      decide (info.dest = .sym data.ext.name) && info.defs.isEmpty &&
        decide (info.uses = retPairs (callUses info.uses)) &&
        decide ((callUses info.uses).map (·.1) = data.args.map (sourceKey event.ctx))
    | _ => false
  else true

def codeB (data : SourceData) (result : Stock.Result) : Bool := result.blockScans.toList.all (scanB data)

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

/-- Bind the source and record checks to the actual unchanged Stock output. -/
def check (f : Clif.Function) (vc : VCode) : Bool :=
  match sourceData? f with
  | none => false
  | some data => sourceB f data && lowerScopeB f && dominatedB f && sigAbiOk f.sig &&
      match Stock.lower f with
      | .error _ => false
      | .ok result => decide (result.code = vc) && codeB data result &&
          result.edgeArgs.all (fun row => row.all (·.isEmpty))

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

namespace E2E.VoidCallViewWitness
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.VoidCall
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
private def fullCheck : Bool := match Stock.lower caller with
  | .error _ => false
  | .ok result => Stock.VoidCall.check caller result.code
attribute [local irreducible] fullCheck
-- witness: native_decide (the original caller, signature, and actual Stock records only)
private theorem fullCheck_true : fullCheck = true := by native_decide

/-- The unchanged real mixed-program caller inhabits the complete call-aware source contract. -/
theorem actual_stock_source_domain_witness :
    ∃ result,Stock.lower caller = .ok result ∧ Domain caller result.code := by
  have checked := fullCheck_true
  unfold fullCheck at checked
  cases lowered : Stock.lower caller with
  | error message => simp only [lowered,Bool.false_eq_true] at checked
  | ok result =>
    rw [lowered] at checked
    exact ⟨result,rfl,check_domain checked⟩

end E2E.VoidCallViewWitness

#print axioms Backend.Proof.ExtSem.voidCalls_call
#print axioms Backend.Proof.ExtSem.voidCalls_call_inv
#print axioms Backend.Proof.ArmStepX_voidCalls
#print axioms Backend.Proof.csem_call_voidCalls_inv
#print axioms Backend.Proof.csem_tryCall_voidCalls_inv
#print axioms Backend.Proof.CalleeOk.voidCalls
#print axioms Backend.Proof.csemV_voidCalls_inv
#print axioms Backend.Proof.CalleeOkG.voidCalls
#print axioms Backend.Proof.RL.CallPre.of_voidCalls
#print axioms Backend.Proof.RL.GoodX.of_voidCalls
#print axioms E2E.ActEntry.voidCalls
#print axioms Backend.Proof.actGoodX_of_voidCalls
#print axioms Backend.Proof.seqRun_call_voidCalls
#print axioms Backend.Proof.seqRun_call_voidCalls_int
#print axioms E2E.VoidCallViewWitness.actual_stock_call_witness -- witness: native_decide

#print axioms Backend.Proof.XCallsOk.voidCalls_return

#print axioms Backend.Stock.VoidCall.source_return_call
#print axioms Backend.Stock.VoidCall.source_call_notrap
#print axioms Backend.Stock.VoidCall.call_values_hold
#print axioms Backend.Stock.VoidCall.entry_values_resolved
#print axioms Backend.Stock.VoidCall.Layout.return_function
#print axioms Backend.Stock.VoidCall.Layout.of_checks
#print axioms Backend.Stock.VoidCall.check_sound
#print axioms Backend.Stock.VoidCall.check_domain
#print axioms E2E.VoidCallViewWitness.actual_stock_source_domain_witness -- witness: native_decide
