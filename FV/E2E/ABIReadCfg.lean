module

public import FV.Backend.ABIReadCfg
public import FV.E2E.ABIReadDiv
public import FV.E2E.ABIReadCfgBoundary

@[expose] public section

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

private def branchControl (i : MInst) (us : List CV) : Ctl :=
  match i with
  | .condBr _ _ kind => .goto (if kind.holds us Arm.ArmState.default then 0 else 1)
  | _ => .goto 0

private theorem branch_sem (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem)
    {i : MInst} (checked : Backend.ABIReadCfg.additional i = true) (us : List CV) (w : Arm.ArmState) :
    sem F ctx X i us w = some ([],w,branchControl i us) ∧
      valueSem F ctx X i us w = some ([],w,branchControl i us) := by
  cases i <;> try cases checked
  case jump label => exact ⟨rfl,rfl⟩
  case condBr taken notTaken kind =>
    cases kind <;> try cases checked
    all_goals rename_i r size
    all_goals cases r <;> try cases checked
    all_goals rename_i key cls
    all_goals cases cls <;> try cases checked
    all_goals
      cases us with
      | nil => exact ⟨rfl,rfl⟩
      | cons a rest => cases rest <;> exact ⟨rfl,rfl⟩

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
  · rw [(branch_sem F ctx X jumped us w).1] at run
    simp only [Option.some.injEq,Prod.mk.injEq] at run
    obtain ⟨rfl,rfl,rfl⟩ := run
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
  · rw [(branch_sem F ctx X jumped us w).1] at run
    simp only [Option.some.injEq,Prod.mk.injEq] at run
    obtain ⟨rfl,rfl,rfl⟩ := run
    exact ⟨w',(branch_sem F ctx X jumped us w').1,worlds⟩

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
  · rw [(branch_sem F ctx X jumped us w).1] at executed
    simp only [Option.some.injEq,Prod.mk.injEq] at executed
    obtain ⟨rfl,rfl,rfl⟩ := executed
    exact ⟨t,(branch_sem F ctx X jumped us t).2,worlds⟩

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
