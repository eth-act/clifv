import FV.E2E.DivBoundaryCheck
import FV.Backend.ABIReadDiv
import FV.E2E.ABIReadTrapBoundary
import FV.E2E.ABIReadDivSteps
import FV.E2E.ABIReadScalar
namespace E2E.DivBoundary
open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup E2E.MixedFlagBoundary
set_option autoImplicit false
set_option Elab.async false

private def special : MInst → Bool
  | .aluRRR op .. => op == .sDiv || op == .uDiv
  | .aluRRImm12 op .. => op == .addS
  | .ccmpImm .. | .trapIf .. | .udf .. => true
  | _ => false

noncomputable def sem (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) : Sem :=
  fun i us w => if special i then mspec ctx.slotBase i us w else ScalarBoundary.sem F ctx X i us w

theorem refines (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) : Refines F (sem F ctx X) := by
  intro i us w outs w' ctl executed
  by_cases hs : special i = true
  · exact ⟨w',by simp only [sem,hs,↓reduceIte]; exact mspec_of_ispec executed,SameWorld.refl F w'⟩
  · simpa only [sem,show special i = false from Bool.eq_false_iff.mpr hs,Bool.false_eq_true,↓reduceIte] using
      ScalarBoundary.refines F ctx X i us w outs w' executed

theorem memory (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem)
    {sb : Nat} {syms : String → Option Nat} (base : ctx.slotBase = sb)
    (symbols : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b) :
    MemRefines F sb syms (sem F ctx X) := by
  simpa only [MemRefines,sem,special,Bool.false_eq_true,↓reduceIte] using
    ScalarBoundary.memory F ctx X base symbols

theorem driver (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) : DriverSem (sem F ctx X) := by
  have hd := ScalarBoundary.driver F ctx X
  refine ⟨⟨?_,?_,?_⟩,?_⟩
  · intro l w; exact hd.jump l w
  · intro g gn hg i
    funext us w
    have old := congrFun (congrFun (hd.rename g gn hg i) us) w
    have same : special (i.mapRegs g) = special i := by cases i <;> rfl
    simp only [sem,same]
    split
    · exact mspec_mapRegs hg ctx.slotBase i us w
    · exact old
  · intro i ls i' targets
    have old := hd.retarget i ls i' targets
    unfold MInst.setTargets at targets
    split at targets
    all_goals repeat' first | cases targets | split at targets
    all_goals
      funext us w
      simpa only [sem,special,Bool.false_eq_true,↓reduceIte] using congrFun (congrFun old us) w
  · intro ds w; exact hd.args ds w

private theorem old_not_special {sig : Clif.Signature} {b k : Nat} {i : MInst}
    (checked : Backend.ABIReadScalar.instruction sig b k i = true) : special i = false := by
  cases i with
  | aluRRR op sz rd rn rm => cases op <;> first | rfl | cases checked
  | aluRRImm12 op sz rd rn imm => cases op <;> first | rfl | cases checked
  | ccmpImm sz rn imm nzcv c => cases checked
  | trapIf kind code => cases checked
  | udf code => cases checked
  | _ => rfl

private theorem additional_special {i : MInst} (checked : Backend.ABIReadDiv.additional i = true) :
    special i = true := by
  cases i with
  | aluRRR op sz rd rn rm => cases op <;> first | rfl | cases checked
  | aluRRImm12 op sz rd rn imm => cases op <;> first | rfl | cases checked
  | ccmpImm sz rn imm nzcv c => rfl
  | trapIf kind code => rfl
  | udf code => rfl
  | _ => cases checked

theorem checked_step_frame {sig : Clif.Signature} {b k : Nat} {i : MInst}
    (checked : Backend.ABIReadDiv.instruction sig b k i = true)
    {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem}
    {us outs : List CV} {w t : Arm.ArmState} {ctl : Ctl}
    (run : sem F ctx X i us w = some (outs,t,ctl)) :
    FlagFrame w t ∧ (ctl = .next ∨ ctl = .ret ∨ ctl = .halt) := by
  simp only [Backend.ABIReadDiv.instruction,Bool.or_eq_true] at checked
  rcases checked with old | added
  · simp only [sem,old_not_special old,Bool.false_eq_true,↓reduceIte] at run
    obtain ⟨frame,control⟩ := ScalarBoundary.checked_step_frame old run
    refine ⟨frame,?_⟩
    rcases control with next | ret
    · exact Or.inl next
    · exact Or.inr (Or.inl ret)
  · simp only [sem,additional_special added,↓reduceIte] at run
    exact DivRead.step_frame added run

theorem checked_step_transport {sig : Clif.Signature} {args : List Clif.Val}
    (types : args.map (·.ty) = sig.params.map (·.ty))
    {b k : Nat} {i : MInst}
    (checked : Backend.ABIReadDiv.instruction sig b k i = true)
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
  simp only [Backend.ABIReadDiv.instruction,Bool.or_eq_true] at checked
  rcases checked with old | added
  · simp only [sem,old_not_special old,Bool.false_eq_true,↓reduceIte] at run ⊢
    exact ScalarBoundary.checked_step_transport types old current other worlds registers stack run
  · simp only [sem,additional_special added,↓reduceIte] at run ⊢
    exact mspec_lockstep (DivRead.no_mem added) worlds run

namespace Realize
theorem step_realize {sig : Clif.Signature} {args : List Clif.Val}
    (types : args.map (·.ty) = sig.params.map (·.ty))
    {b k : Nat} {i : MInst}
    (checked : Backend.ABIReadDiv.instruction sig b k i = true)
    {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem}
    {initial w t final : Arm.ArmState} (frame : FlagFrame initial w)
    (arguments : ArgsAtEntry F sig args initial) (worlds : SameWorld F t w)
    (entry : k = 0 → t = w) {us outs : List CV} {ctl : Ctl}
    (executed : sem F ctx X i us w = some (outs,final,ctl)) :
    ∃ actual, valueSem F ctx X i us t = some (outs,actual,ctl) ∧ SameWorld F actual final := by
  simp only [Backend.ABIReadDiv.instruction,Bool.or_eq_true] at checked
  rcases checked with old | added
  · simp only [sem,old_not_special old,Bool.false_eq_true,↓reduceIte] at executed ⊢
    exact ScalarBoundary.Realize.step_realize types old frame arguments worlds entry executed
  · simp only [sem,additional_special added,↓reduceIte] at executed
    obtain ⟨spec,run,related⟩ := mspec_lockstep (DivRead.no_mem added) worlds.symm executed
    rw [DivRead.spec_eq added] at run
    obtain ⟨actual,realized,related'⟩ := refines_valueSem F ctx X _ us t outs spec run
    exact ⟨actual,realized,related'.trans related.symm⟩

end Realize

private noncomputable def boundaryModel : ABIReadTrapBoundary.Model where
  instruction := Backend.ABIReadDiv.instruction
  eval := sem
  frame := checked_step_frame
  transport := checked_step_transport
  realize := Realize.step_realize

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
  exact ABIReadTrapBoundary.return_transport (model := boundaryModel) types checked worlds registers stack returned

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
  exact ABIReadTrapBoundary.machine_return (model := boundaryModel) types readOnly prep check alloc emit layout frame covered arguments worlds returned H G base ra s entry

theorem checked_instruction {sig : Clif.Signature} {vc : VCode}
    (checked : check sig vc = true) {b k : Nat} {vb : VBlock} {i : MInst}
    (block : vc.blocks[b]? = some vb) (inst : vb.insts[k]? = some i) :
    Backend.ABIReadDiv.instruction sig b k i = true :=
  ABIReadTrapBoundary.checked_instruction (model := boundaryModel) checked block inst

/-- A real checked zero guard inhabits terminal control in the new model for
any original world. No nonzero-divisor or no-trap assumption is supplied. -/
theorem zero_guard_halts (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem)
    (w : Arm.ArmState) :
    Backend.ABIReadDiv.additional (.trapIf (.zero (.vreg 0 .int) .size64) .intDivz) = true ∧
    trapCode? (.trapIf (.zero (.vreg 0 .int) .size64) .intDivz) = some .intDivz ∧
    sem F ctx X (.trapIf (.zero (.vreg 0 .int) .size64) .intDivz) [ofX 0] w =
      some ([],w,.halt) := by
  exact ⟨rfl,rfl,rfl⟩

/-- A false zero guard retains the exact same instruction and source conditions,
continuing with the original world. -/
theorem nonzero_guard_continues (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem)
    (w : Arm.ArmState) :
    sem F ctx X (.trapIf (.zero (.vreg 0 .int) .size64) .intDivz) [ofX 1] w =
      some ([],w,.next) := by
  rfl

end E2E.DivBoundary
