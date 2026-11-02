import FV.E2E.LinkWorld
import FV.Backend.Proof.IselCtlCallF

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
