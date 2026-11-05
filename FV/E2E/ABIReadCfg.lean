import FV.Backend.ABIReadCfg
import FV.E2E.ABIReadDiv
import FV.E2E.ABIReadCfgBoundary

namespace E2E.CfgBoundary
open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup E2E.MixedFlagBoundary
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

noncomputable abbrev sem := DivBoundary.sem

theorem refines (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) : Refines F (sem F ctx X) :=
  DivBoundary.refines F ctx X

theorem driver (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) : DriverSem (sem F ctx X) :=
  DivBoundary.driver F ctx X

theorem memory (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem)
    {sb : Nat} {syms : String → Option Nat} (base : ctx.slotBase = sb)
    (symbols : ∀ n b,syms n = some b → X.sym n 0 = BitVec.ofNat 64 b) :
    MemRefines F sb syms (sem F ctx X) := DivBoundary.memory F ctx X base symbols

/-- Outputs and control of a checked CFG form. They read only the uses and the
unmasked NZCV flags; the outputs (the jump table's dead temporaries) are constants. -/
private def branchStep (i : MInst) (us : List CV) (w : Arm.ArmState) : Option (List CV × Ctl) :=
  match i with
  | .condBr _ _ kind => some ([],.goto (if kind.holds us w then 0 else 1))
  | .testBitAndBranch k _ _ _ bit =>
    match us with
    | [a] => some ([],.goto (if ((lo64 a).getLsbD bit == (k == .nz)) then 0 else 1))
    | _ => none
  | .emitIsland _ => some ([],.next)
  | .jtSequence _ ts _ _ _ =>
    match us with
    | [a] =>
      if Arm.ConditionHolds Cond.hs.bits w then some ([ofX 0,ofX 0],.goto 0)
      else
        let j := ((lo64 a).setWidth 32).toNat
        if j < ts.length then some ([ofX 0,ofX 0],.goto (j+1)) else none
    | _ => none
  | _ => some ([],.goto 0)

/-- Branch control reads only the uses and the unmasked NZCV flags. -/
private theorem branchStep_world {i : MInst} {us : List CV} {Z : BitVec 64 → Prop}
    {w w' : Arm.ArmState} (worlds : SameWorld Z w w') : branchStep i us w = branchStep i us w' := by
  have flags : ∀ fl,Arm.r (.FLAG fl) w = Arm.r (.FLAG fl) w' :=
    fun fl => worlds.1 (.FLAG fl) (by simp [Masked])
  have same : ∀ c : Cond,Arm.ConditionHolds c.bits w = Arm.ConditionHolds c.bits w' := by
    intro c
    have read : ∀ fl,Arm.read_flag fl w = Arm.read_flag fl w' := flags
    unfold Arm.ConditionHolds
    rw [read .N,read .Z,read .C,read .V]
  cases i <;> try rfl
  case condBr taken notTaken kind =>
    cases kind
    case cond c =>
      have holds : (CondBrKind.cond c).holds us w = (CondBrKind.cond c).holds us w' := same c
      show some ([],Ctl.goto (if (CondBrKind.cond c).holds us w = true then 0 else 1)) =
        some ([],Ctl.goto (if (CondBrKind.cond c).holds us w' = true then 0 else 1))
      rw [holds]
    all_goals
      cases us with
      | nil => rfl
      | cons a rest => cases rest <;> rfl
  case jtSequence d ts ridx t1 t2 =>
    cases us with
    | nil => rfl
    | cons a rest =>
      cases rest with
      | cons => rfl
      | nil =>
        show (if Arm.ConditionHolds Cond.hs.bits w = true then _ else _) =
          (if Arm.ConditionHolds Cond.hs.bits w' = true then _ else _)
        rw [same Cond.hs]

/-- The jump table's step: the bounds-check flag, else the index's table entry. -/
private theorem table_map (w : Arm.ArmState) (ts : List Label) (c : Bool) (j : Nat) :
    (if c = true then some ([ofX 0,ofX 0],w,Ctl.goto 0)
      else if j < ts.length then some ([ofX 0,ofX 0],w,Ctl.goto (j+1)) else none) =
    (if c = true then some ([ofX 0,ofX 0],Ctl.goto 0)
      else if j < ts.length then some ([ofX 0,ofX 0],Ctl.goto (j+1)) else none).map
      (fun p => (p.1,w,p.2)) := by
  cases c
  · by_cases found : j < ts.length <;> simp [found]
  · rfl

private theorem branch_sem (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem)
    {i : MInst} (checked : Backend.ABIReadCfg.additional i = true) (us : List CV) (w : Arm.ArmState) :
    sem F ctx X i us w = (branchStep i us w).map (fun p => (p.1,w,p.2)) ∧
      valueSem F ctx X i us w = (branchStep i us w).map (fun p => (p.1,w,p.2)) := by
  cases i <;> try cases checked
  case jump label => exact ⟨rfl,rfl⟩
  case condBr taken notTaken kind =>
    cases kind <;> try cases checked
    case cond c =>
      cases us with
      | nil => exact ⟨rfl,rfl⟩
      | cons a rest => cases rest <;> exact ⟨rfl,rfl⟩
    all_goals rename_i r size
    all_goals cases r <;> try cases checked
    all_goals rename_i key cls
    all_goals cases cls <;> try cases checked
    all_goals
      cases us with
      | nil => exact ⟨rfl,rfl⟩
      | cons a rest => cases rest <;> exact ⟨rfl,rfl⟩
  case testBitAndBranch k taken notTaken r bit =>
    cases us with
    | nil => exact ⟨rfl,rfl⟩
    | cons a rest => cases rest <;> exact ⟨rfl,rfl⟩
  case emitIsland n => exact ⟨rfl,rfl⟩
  case jtSequence d ts ridx t1 t2 =>
    cases us with
    | nil => exact ⟨rfl,rfl⟩
    | cons a rest =>
      cases rest with
      | cons => exact ⟨rfl,rfl⟩
      | nil =>
        exact ⟨table_map w ts (Arm.ConditionHolds Cond.hs.bits w) ((lo64 a).setWidth 32).toNat,
          table_map w ts (Arm.ConditionHolds Cond.hs.bits w) ((lo64 a).setWidth 32).toNat⟩

/-- A checked CFG step keeps its world and runs alike from every world with the
same unmasked fields, in the boundary and the value semantics. -/
private theorem branch_run (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem)
    {i : MInst} (checked : Backend.ABIReadCfg.additional i = true) {Z : BitVec 64 → Prop}
    {us outs : List CV} {w w' t : Arm.ArmState} {ctl : Ctl} (worlds : SameWorld Z w w')
    (run : sem F ctx X i us w = some (outs,t,ctl)) :
    t = w ∧ sem F ctx X i us w' = some (outs,w',ctl) ∧
      valueSem F ctx X i us w' = some (outs,w',ctl) := by
  rw [(branch_sem F ctx X checked us w).1] at run
  obtain ⟨p,found,result⟩ := Option.map_eq_some_iff.mp run
  simp only [Prod.mk.injEq] at result
  obtain ⟨rfl,rfl,rfl⟩ := result
  rw [(branch_sem F ctx X checked us w').1,(branch_sem F ctx X checked us w').2,
    ← branchStep_world worlds,found]
  exact ⟨rfl,rfl,rfl⟩

private theorem reindex_nonentry {sig : Clif.Signature} {b k : Nat} {i : MInst}
    (nonentry : ¬ (b = 0 ∧ k = 0))
    (checked : Backend.ABIReadDiv.instruction sig b k i = true) :
    Backend.ABIReadDiv.instruction sig b (k+1) i = true := by
  have base : Backend.ABIReadOnly.instruction sig b (k+1) i =
      Backend.ABIReadOnly.instruction sig b k i := by
    cases i <;> try rfl
    case load op rd mem flags =>
      cases rd <;> try rfl
      case vreg key cls => cases cls <;> cases mem <;> rfl
    case args pairs =>
      cases b <;> cases k <;> simp_all [Backend.ABIReadOnly.instruction,DeadCleanup.pureForm]
  simpa only [Backend.ABIReadDiv.instruction,Backend.ABIReadScalar.instruction,
    Backend.ABIReadFlags.instruction,base] using checked

theorem checked_step_frame {sig : Clif.Signature} {b k : Nat} {i : MInst}
    (checked : Backend.ABIReadCfg.instruction sig b k i = true)
    {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem}
    {us outs : List CV} {w t : Arm.ArmState} {ctl : Ctl}
    (run : sem F ctx X i us w = some (outs,t,ctl)) :
    FlagFrame w t := by
  simp only [Backend.ABIReadCfg.instruction,Bool.or_eq_true] at checked
  rcases checked with old | jumped
  · exact (DivBoundary.checked_step_frame old run).1
  · obtain ⟨rfl,-,-⟩ := branch_run F ctx X jumped (SameWorld.refl F w) run
    exact FlagFrame.refl _

theorem checked_step_transport {sig : Clif.Signature} {args : List Clif.Val}
    (types : args.map (·.ty) = sig.params.map (·.ty))
    {b k : Nat} {i : MInst}
    (checked : Backend.ABIReadCfg.instruction sig b k i = true)
    {F Z : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem}
    {initial initial' w w' : Arm.ArmState}
    (current : FlagFrame initial w) (other : FlagFrame initial' w')
    (worlds : SameWorld Z w w')
    (registers : ∀ r v, (.reg r,v) ∈ (locsOf sig).zip args →
      regVal initial' r = regVal initial r)
    (stack : ∀ (off : Nat) (v : Clif.Val), (.stack off,v) ∈ (locsOf sig).zip args →
      ∀ j < v.ty.bytes,
      initial'.mem (Arm.r (.GPR 29#5) initial + BitVec.ofInt 64 (16+(off : Int)) + BitVec.ofNat 64 j) =
      initial.mem (Arm.r (.GPR 29#5) initial + BitVec.ofInt 64 (16+(off : Int)) + BitVec.ofNat 64 j))
    {us outs : List CV} {t : Arm.ArmState} {ctl : Ctl}
    (run : sem F ctx X i us w = some (outs,t,ctl)) :
    ∃ t', sem F ctx X i us w' = some (outs,t',ctl) ∧ SameWorld Z t t' := by
  simp only [Backend.ABIReadCfg.instruction,Bool.or_eq_true] at checked
  rcases checked with old | jumped
  · exact DivBoundary.checked_step_transport types old current other worlds registers stack run
  · obtain ⟨rfl,moved,-⟩ := branch_run F ctx X jumped worlds run
    exact ⟨w',moved,worlds⟩

namespace Realize
theorem step_realize {sig : Clif.Signature} {args : List Clif.Val}
    (types : args.map (·.ty) = sig.params.map (·.ty))
    {b k : Nat} {i : MInst}
    (checked : Backend.ABIReadCfg.instruction sig b k i = true)
    {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem}
    {initial w t final : Arm.ArmState} (frame : FlagFrame initial w)
    (arguments : ArgsAtEntry F sig args initial) (worlds : SameWorld F t w)
    (entry : b = 0 → k = 0 → t = w) {us outs : List CV} {ctl : Ctl}
    (executed : sem F ctx X i us w = some (outs,final,ctl)) :
    ∃ actual, valueSem F ctx X i us t = some (outs,actual,ctl) ∧ SameWorld F actual final := by
  simp only [Backend.ABIReadCfg.instruction,Bool.or_eq_true] at checked
  rcases checked with old | jumped
  · by_cases initialPosition : b = 0 ∧ k = 0
    · exact DivBoundary.Realize.step_realize types old frame arguments worlds
        (fun _ => entry initialPosition.1 initialPosition.2) executed
    · exact DivBoundary.Realize.step_realize types (reindex_nonentry initialPosition old)
        frame arguments worlds (by omega) executed
  · obtain ⟨rfl,-,realized⟩ := branch_run F ctx X jumped worlds.symm executed
    exact ⟨t,realized,worlds⟩

end Realize

private noncomputable def boundaryModel : ABIReadCfgBoundary.Model where
  instruction := Backend.ABIReadCfg.instruction
  eval := sem
  frame := checked_step_frame
  transport := checked_step_transport
  realize := Realize.step_realize

abbrev check := Backend.ABIReadCfg.check

private theorem no_entry {vc : VCode} (checked : Backend.ABIReadCfg.noEntryEdges vc = true) :
    ∀ b index,succOf vc b index ≠ some 0 := by
  intro b index successor
  unfold Backend.ABIReadCfg.noEntryEdges at checked
  cases cfg : vc.cfg with
  | error message => simp [cfg] at checked
  | ok pair =>
    obtain ⟨ss,ps⟩ := pair
    simp only [cfg] at checked
    simp only [succOf,cfg] at successor
    obtain ⟨row,found,target⟩ := Option.bind_eq_some_iff.mp successor
    have absent := Array.all_eq_true_iff_forall_mem.mp checked row (Array.mem_of_getElem? found)
    have no : 0 ∉ row := by simpa using absent
    exact no (Array.mem_of_getElem? target)

theorem return_transport {sig : Clif.Signature} {args : List Clif.Val}
    (types : args.map (·.ty) = sig.params.map (·.ty))
    {vc : VCode} (checked : check sig vc = true)
    {F Z : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem}
    {initial initial' : Arm.ArmState} (worlds : SameWorld Z initial initial')
    (registers : ∀ r v, (.reg r,v) ∈ (locsOf sig).zip args →
      regVal initial' r = regVal initial r)
    (stack : ∀ (off : Nat) (v : Clif.Val), (.stack off,v) ∈ (locsOf sig).zip args →
      ∀ j < v.ty.bytes,
      initial'.mem (Arm.r (.GPR 29#5) initial + BitVec.ofInt 64 (16+(off : Int)) + BitVec.ofNat 64 j) =
      initial.mem (Arm.r (.GPR 29#5) initial + BitVec.ofInt 64 (16+(off : Int)) + BitVec.ofNat 64 j))
    {ρ : Nat → CV} {us : List (Reg × Reg)} {outs : List CV} {world : Arm.ArmState}
    (returned : VReturns vc (sem F ctx X) ρ initial us outs world) :
    ∃ world', VReturns vc (sem F ctx X) ρ initial' us outs world' ∧ SameWorld Z world world' := by
  exact ABIReadCfgBoundary.return_transport (model := boundaryModel) types (Bool.and_eq_true_iff.mp checked).1 worlds registers stack returned

theorem return_realize {sig : Clif.Signature} {args : List Clif.Val}
    (types : args.map (·.ty) = sig.params.map (·.ty))
    {vc : VCode} (checked : check sig vc = true)
    {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {initial : Arm.ArmState}
    (arguments : ArgsAtEntry F sig args initial)
    {ρ : Nat → CV} {us : List (Reg × Reg)} {outs : List CV} {world : Arm.ArmState}
    (returned : VReturns vc (sem F ctx X) ρ initial us outs world) :
    ∃ t, VReturns vc (valueSem F ctx X) ρ initial us outs t ∧ SameWorld F t world := by
  exact ABIReadCfgBoundary.Realize.return_realize (model := boundaryModel) types
    (Bool.and_eq_true_iff.mp checked).1 (no_entry (Bool.and_eq_true_iff.mp checked).2) arguments returned

theorem machine_return {f : Clif.Function} {args : List Clif.Val}
    (types : args.map (·.ty) = f.sig.params.map (·.ty))
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin} {k : Nat}
    {cleanup : Bool} (readOnly : check f.sig vc = true)
    (prep : prepCheck (Stock.Arithmetic.stage cleanup vc) vcp = true)
    (check : checkAlloc vcp rf = .ok ()) (alloc : lowerRFunc vcp rf = .ok af)
    (emit : emitFunc k af = .ok fa) (layout : fa.layout = .ok fb)
    {X : ExtSem} {K : Nat} {F Z : BitVec 64 → Prop}
    (frame : ∀ a, F a → Z a) (covered : FormsCovered ⟨fa.k,af.slotBase⟩ vcp)
    {w final reference : Arm.ArmState} (arguments : ArgsAtEntry F f.sig args w)
    (worlds : SameWorld Z final reference)
    {ρ : Nat → CV} {us : List (Reg × Reg)} {outs : List CV}
    (returned : VReturns vc (sem F ⟨fa.k,af.slotBase⟩ X) ρ w us outs final)
    (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState)
    (entry : ActEntry vcp rf af fa fb K F G X H base ra s w) :
    ∃ n, ActRet ra Z G us outs reference s (runX (ArmStepX X H fa) n s) ∧
      PostTrace fa af base (ArmStepX X H fa) s n ∧
      ∀ i < n, actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
        (runX (ArmStepX X H fa) i s) := by
  exact ABIReadCfgBoundary.machine_return (model := boundaryModel) types (Bool.and_eq_true_iff.mp readOnly).1
    (no_entry (Bool.and_eq_true_iff.mp readOnly).2) prep check alloc emit layout frame covered arguments worlds returned H G base ra s entry

theorem checked_instruction {sig : Clif.Signature} {vc : VCode}
    (checked : check sig vc = true) {b k : Nat} {vb : VBlock} {i : MInst}
    (block : vc.blocks[b]? = some vb) (inst : vb.insts[k]? = some i) :
    Backend.ABIReadCfg.instruction sig b k i = true :=
  ABIReadCfgBoundary.checked_instruction (model := boundaryModel) (Bool.and_eq_true_iff.mp checked).1 block inst

end E2E.CfgBoundary
