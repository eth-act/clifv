import FV.Backend.ABIReadScalar
import FV.E2E.ABIReadBoundary
import FV.E2E.ABIReadShiftSteps
import FV.E2E.ABIReadCastSteps
import FV.E2E.ABIReadBitSteps
import FV.E2E.ABIReadPopcountSteps
import FV.E2E.ABIReadComparisonSteps
import FV.E2E.ABIReadBooleanSteps
import FV.E2E.ABIReadHighMulSteps
import FV.E2E.ABIReadExtendedComparisonSteps
import FV.E2E.ABIReadMaskSteps

namespace E2E.ScalarBoundary
open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup E2E.MixedFlagBoundary
set_option autoImplicit false
set_option Elab.async false

private def special : MInst → Bool
  | .cset .. | .csetm .. | .movK .. | .bitfieldMove .. | .extend .. | .bitRR ..
  | .movToFpu .. | .movFromVec .. | .vecMisc .. | .vecLanes .. | .vecRRR .. => true
  | .aluRRImm12 op .. | .aluRRRExtend op .. => op == .subS
  | .aluRRImmLogic op .. => op == .andS
  | .aluRRR op .. | .aluRRImmShift op .. => Backend.ABIReadScalar.shiftOp op || op == .extr || op == .sMulH || op == .uMulH
  | .aluRRRShift op .. => op == .extr
  | _ => false

/-- Proof-only scalar producer specification frames original ABI reads while actual value
semantics is recovered by the shared machine realization proof. -/
noncomputable def sem (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) : Sem :=
  fun i us w => if special i then mspec ctx.slotBase i us w else MixedFlagBoundary.sem F ctx X i us w

theorem refines (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) : Refines F (sem F ctx X) := by
  intro i us w outs w' ctl executed
  by_cases hs : special i = true
  · exact ⟨w',by simp only [sem,hs,↓reduceIte]; exact mspec_of_ispec executed,SameWorld.refl F w'⟩
  · simpa only [sem,show special i = false from Bool.eq_false_iff.mpr hs,Bool.false_eq_true,↓reduceIte] using
      MixedFlagBoundary.refines F ctx X i us w outs w' executed

theorem memory (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem)
    {sb : Nat} {syms : String → Option Nat} (base : ctx.slotBase = sb)
    (symbols : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b) :
    MemRefines F sb syms (sem F ctx X) := by
  simpa only [MemRefines,sem,special,Bool.false_eq_true,↓reduceIte] using
    MixedFlagBoundary.memory F ctx X base symbols

theorem driver (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) : DriverSem (sem F ctx X) := by
  have hd := MixedFlagBoundary.driver F ctx X
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

private theorem constant_cases {i : MInst} (checked : Backend.ABIReadScalar.constant i = true) :
    ∃ d n imm sz, i = .movK (.vreg d .int) (.vreg n .int) imm sz := by
  cases i with
  | movK rd rn imm sz =>
    cases rd <;> try cases checked
    case vreg d cls =>
      cases cls <;> try cases checked
      cases rn <;> try cases checked
      case vreg n cls =>
        cases cls <;> try cases checked
        exact ⟨d,n,imm,sz,rfl⟩
  | _ => cases checked

private theorem old_not_special {sig : Clif.Signature} {b k : Nat} {i : MInst}
    (checked : Backend.ABIReadFlags.instruction sig b k i = true) : special i = false := by
  cases i with
  | cset rd c => cases checked
  | csetm rd c => cases checked
  | movK rd rn imm sz => cases checked
  | bitfieldMove sz op rd rn a b => cases checked
  | extend rd rn sg fromB toB => cases checked
  | bitRR op sz rd rn => cases checked
  | movToFpu rd rn sz => cases checked
  | movFromVec rd rn idx sz => cases checked
  | vecMisc op rd rn sz => cases checked
  | vecLanes op rd rn sz => cases checked
  | vecRRR op rd rn rm sz => cases checked
  | aluRRImm12 op sz rd rn imm => cases op <;> first | rfl | cases checked
  | aluRRR op sz rd rn rm => cases op <;> first | rfl | cases checked
  | aluRRImmShift op sz rd rn imm => cases op <;> first | rfl | cases checked
  | aluRRRExtend op sz rd rn rm e => cases op <;> first | rfl | cases checked
  | aluRRImmLogic op sz rd rn imm => cases op <;> first | rfl | cases checked
  | aluRRRShift op sz rd rn rm sh => cases op <;> first | rfl | cases checked
  | _ => rfl

private theorem shift_special {i : MInst} (checked : Backend.ABIReadScalar.shift i = true) : special i = true := by
  cases i <;> simp_all [special,Backend.ABIReadScalar.shift]

private theorem bit_special {i : MInst} (checked : Backend.ABIReadScalar.bitProducer i = true) : special i = true := by
  cases i with
  | bitRR op sz rd rn => rfl
  | aluRRR op sz rd rn rm => cases op <;> first | rfl | cases checked
  | aluRRImmShift op sz rd rn imm => cases op <;> first | rfl | cases checked
  | aluRRRShift op sz rd rn rm sh => cases op <;> first | rfl | cases checked
  | _ => cases checked

private theorem popcount_special {i : MInst} (checked : Backend.ABIReadScalar.popcountProducer i = true) : special i = true := by
  cases i <;> first | rfl | cases checked

private theorem boolean_special {i : MInst} (checked : Backend.ABIReadScalar.booleanProducer i = true) : special i = true := by
  cases i <;> first | rfl | cases checked

private theorem highmul_special {i : MInst} (checked : Backend.ABIReadScalar.highmulProducer i = true) : special i = true := by
  cases i with
  | aluRRR op sz rd rn rm => cases op <;> first | rfl | cases checked
  | _ => cases checked

private theorem extended_comparison_special {i : MInst}
    (checked : Backend.ABIReadScalar.extendedComparisonProducer i = true) : special i = true := by
  rcases ExtendedComparisonRead.cases_of_check checked with ⟨sz,n,m,e,rfl⟩ | ⟨sz,n,imm,rfl⟩ <;> rfl

private theorem mask_special {i : MInst}
    (checked : Backend.ABIReadScalar.maskProducer i = true) : special i = true := by
  cases i <;> first | rfl | cases checked

private theorem comparison_sem_eq {i : MInst}
    (checked : Backend.ABIReadScalar.comparisonProducer i = true)
    (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) (us : List CV) (w : Arm.ArmState) :
    sem F ctx X i us w = mspec ctx.slotBase i us w := by
  cases i with
  | aluRRR op sz rd rn rm => cases op <;> first | rfl | cases checked
  | aluRRImm12 op sz rd rn imm => cases op <;> first | rfl | cases checked
  | _ => cases checked

private theorem extension_special {i : MInst} (checked : Backend.ABIReadScalar.extension i = true) : special i = true := by
  cases i <;> first | rfl | cases checked

private theorem constant_special {i : MInst} (checked : Backend.ABIReadScalar.constant i = true) : special i = true := by
  obtain ⟨d,n,imm,sz,rfl⟩ := constant_cases checked
  rfl

private theorem constant_frame {i : MInst} (checked : Backend.ABIReadScalar.constant i = true)
    {sb : Nat} {us outs : List CV} {w t : Arm.ArmState} {ctl : Ctl}
    (run : mspec sb i us w = some (outs,t,ctl)) : FlagFrame w t ∧ ctl = .next := by
  obtain ⟨d,n,imm,sz,rfl⟩ := constant_cases checked
  cases us with
  | nil => cases run
  | cons a rest =>
    cases rest with
    | cons b tail => simp [mspec,ispec] at run
    | nil =>
      simp only [mspec,ispec] at run
      split at run
      · simp only [Option.some.injEq,Prod.mk.injEq] at run
        obtain ⟨rfl,rfl,rfl⟩ := run
        exact ⟨FlagFrame.refl _,rfl⟩
      · cases run

theorem checked_step_frame {sig : Clif.Signature} {b k : Nat} {i : MInst}
    (checked : Backend.ABIReadScalar.instruction sig b k i = true)
    {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem}
    {us outs : List CV} {w t : Arm.ArmState} {ctl : Ctl}
    (run : sem F ctx X i us w = some (outs,t,ctl)) :
    FlagFrame w t ∧ (ctl = .next ∨ ctl = .ret) := by
  simp only [Backend.ABIReadScalar.instruction,Bool.or_eq_true] at checked
  rcases checked with (((((((((old | added) | shifted) | extended) | bit) | popcount) | comparison) | boolean) | highmul) | narrowComparison) | mask
  · simp only [sem,old_not_special old,Bool.false_eq_true,↓reduceIte] at run
    exact MixedFlagBoundary.checked_step_frame old run
  · simp only [sem,constant_special added,↓reduceIte] at run
    obtain ⟨frame,control⟩ := constant_frame added run
    exact ⟨frame,.inl control⟩
  · simp only [sem,shift_special shifted,↓reduceIte] at run
    obtain ⟨frame,control⟩ := ShiftRead.step_frame shifted run
    exact ⟨frame,.inl control⟩
  · simp only [sem,extension_special extended,↓reduceIte] at run
    obtain ⟨frame,control⟩ := CastRead.step_frame extended run
    exact ⟨frame,.inl control⟩
  · simp only [sem,bit_special bit,↓reduceIte] at run
    obtain ⟨frame,control⟩ := BitRead.step_frame bit run
    exact ⟨frame,.inl control⟩
  · simp only [sem,popcount_special popcount,↓reduceIte] at run
    obtain ⟨frame,control⟩ := PopcountRead.step_frame popcount run
    exact ⟨frame,.inl control⟩
  · rw [comparison_sem_eq comparison] at run
    obtain ⟨frame,control⟩ := ComparisonRead.step_frame comparison run
    exact ⟨frame,.inl control⟩

  · simp only [sem,boolean_special boolean,↓reduceIte] at run
    obtain ⟨frame,control⟩ := BooleanRead.step_frame boolean run
    exact ⟨frame,.inl control⟩
  · simp only [sem,highmul_special highmul,↓reduceIte] at run
    obtain ⟨frame,control⟩ := HighMulRead.step_frame highmul run
    exact ⟨frame,.inl control⟩

  · simp only [sem,extended_comparison_special narrowComparison,↓reduceIte] at run
    obtain ⟨frame,control⟩ := ExtendedComparisonRead.step_frame narrowComparison run
    exact ⟨frame,.inl control⟩

  · simp only [sem,mask_special mask,↓reduceIte] at run
    obtain ⟨frame,control⟩ := MaskRead.step_frame mask run
    exact ⟨frame,.inl control⟩

theorem checked_step_transport {sig : Clif.Signature} {args : List Clif.Val}
    (types : args.map (·.ty) = sig.params.map (·.ty))
    {b k : Nat} {i : MInst}
    (checked : Backend.ABIReadScalar.instruction sig b k i = true)
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
  simp only [Backend.ABIReadScalar.instruction,Bool.or_eq_true] at checked
  rcases checked with (((((((((old | added) | shifted) | extended) | bit) | popcount) | comparison) | boolean) | highmul) | narrowComparison) | mask
  · simp only [sem,old_not_special old,Bool.false_eq_true,↓reduceIte] at run ⊢
    exact MixedFlagBoundary.checked_step_transport types old current other worlds registers stack run
  · simp only [sem,constant_special added,↓reduceIte] at run ⊢
    obtain ⟨d,n,imm,sz,shape⟩ := constant_cases added
    exact mspec_lockstep (by rw [shape]; rfl) worlds run
  · simp only [sem,shift_special shifted,↓reduceIte] at run ⊢
    exact mspec_lockstep (ShiftRead.no_mem shifted) worlds run
  · simp only [sem,extension_special extended,↓reduceIte] at run ⊢
    exact mspec_lockstep (CastRead.no_mem extended) worlds run
  · simp only [sem,bit_special bit,↓reduceIte] at run ⊢
    exact mspec_lockstep (BitRead.no_mem bit) worlds run
  · simp only [sem,popcount_special popcount,↓reduceIte] at run ⊢
    exact mspec_lockstep (PopcountRead.no_mem popcount) worlds run
  · rw [comparison_sem_eq comparison] at run ⊢
    exact mspec_lockstep (ComparisonRead.no_mem comparison) worlds run

  · simp only [sem,boolean_special boolean,↓reduceIte] at run ⊢
    exact mspec_lockstep (BooleanRead.no_mem boolean) worlds run
  · simp only [sem,highmul_special highmul,↓reduceIte] at run ⊢
    exact mspec_lockstep (HighMulRead.no_mem highmul) worlds run

  · simp only [sem,extended_comparison_special narrowComparison,↓reduceIte] at run ⊢
    exact mspec_lockstep (ExtendedComparisonRead.no_mem narrowComparison) worlds run

  · simp only [sem,mask_special mask,↓reduceIte] at run ⊢
    exact mspec_lockstep (MaskRead.no_mem mask) worlds run

namespace Realize
theorem step_realize {sig : Clif.Signature} {args : List Clif.Val}
    (types : args.map (·.ty) = sig.params.map (·.ty))
    {b k : Nat} {i : MInst}
    (checked : Backend.ABIReadScalar.instruction sig b k i = true)
    {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem}
    {initial w t final : Arm.ArmState} (frame : FlagFrame initial w)
    (arguments : ArgsAtEntry F sig args initial) (worlds : SameWorld F t w)
    (entry : k = 0 → t = w) {us outs : List CV} {ctl : Ctl}
    (executed : sem F ctx X i us w = some (outs,final,ctl)) :
    ∃ actual, valueSem F ctx X i us t = some (outs,actual,ctl) ∧ SameWorld F actual final := by
  simp only [Backend.ABIReadScalar.instruction,Bool.or_eq_true] at checked
  rcases checked with (((((((((old | added) | shifted) | extended) | bit) | popcount) | comparison) | boolean) | highmul) | narrowComparison) | mask
  · simp only [sem,old_not_special old,Bool.false_eq_true,↓reduceIte] at executed ⊢
    exact MixedFlagBoundary.Realize.step_realize types old frame arguments worlds entry executed
  · simp only [sem,constant_special added,↓reduceIte] at executed
    obtain ⟨d,n,imm,sz,rfl⟩ := constant_cases added
    obtain ⟨spec,run,related⟩ := mspec_lockstep (by rfl) worlds.symm executed
    change ispec _ us t = some (outs,spec,ctl) at run
    obtain ⟨actual,realized,related'⟩ := refines_valueSem F ctx X _ us t outs spec run
    exact ⟨actual,realized,related'.trans related.symm⟩
  · simp only [sem,shift_special shifted,↓reduceIte] at executed
    obtain ⟨spec,run,related⟩ := mspec_lockstep (ShiftRead.no_mem shifted) worlds.symm executed
    rw [ShiftRead.spec_eq shifted] at run
    obtain ⟨actual,realized,related'⟩ := refines_valueSem F ctx X _ us t outs spec run
    exact ⟨actual,realized,related'.trans related.symm⟩
  · simp only [sem,extension_special extended,↓reduceIte] at executed
    obtain ⟨spec,run,related⟩ := mspec_lockstep (CastRead.no_mem extended) worlds.symm executed
    rw [CastRead.spec_eq extended] at run
    obtain ⟨actual,realized,related'⟩ := refines_valueSem F ctx X _ us t outs spec run
    exact ⟨actual,realized,related'.trans related.symm⟩
  · simp only [sem,bit_special bit,↓reduceIte] at executed
    obtain ⟨spec,run,related⟩ := mspec_lockstep (BitRead.no_mem bit) worlds.symm executed
    rw [BitRead.spec_eq bit] at run
    obtain ⟨actual,realized,related'⟩ := refines_valueSem F ctx X _ us t outs spec run
    exact ⟨actual,realized,related'.trans related.symm⟩

  · simp only [sem,popcount_special popcount,↓reduceIte] at executed
    obtain ⟨spec,run,related⟩ := mspec_lockstep (PopcountRead.no_mem popcount) worlds.symm executed
    rw [PopcountRead.spec_eq popcount] at run
    obtain ⟨actual,realized,related'⟩ := refines_valueSem F ctx X _ us t outs spec run
    exact ⟨actual,realized,related'.trans related.symm⟩

  · rw [comparison_sem_eq comparison] at executed
    obtain ⟨spec,run,related⟩ := mspec_lockstep (ComparisonRead.no_mem comparison) worlds.symm executed
    rw [ComparisonRead.spec_eq comparison] at run
    obtain ⟨actual,realized,related'⟩ := refines_valueSem F ctx X _ us t outs spec run
    exact ⟨actual,realized,related'.trans related.symm⟩

  · simp only [sem,boolean_special boolean,↓reduceIte] at executed
    obtain ⟨spec,run,related⟩ := mspec_lockstep (BooleanRead.no_mem boolean) worlds.symm executed
    rw [BooleanRead.spec_eq boolean] at run
    obtain ⟨actual,realized,related'⟩ := refines_valueSem F ctx X _ us t outs spec run
    exact ⟨actual,realized,related'.trans related.symm⟩
  · simp only [sem,highmul_special highmul,↓reduceIte] at executed
    obtain ⟨spec,run,related⟩ := mspec_lockstep (HighMulRead.no_mem highmul) worlds.symm executed
    rw [HighMulRead.spec_eq highmul] at run
    obtain ⟨actual,realized,related'⟩ := refines_valueSem F ctx X _ us t outs spec run
    exact ⟨actual,realized,related'.trans related.symm⟩

  · simp only [sem,extended_comparison_special narrowComparison,↓reduceIte] at executed
    obtain ⟨spec,run,related⟩ := mspec_lockstep (ExtendedComparisonRead.no_mem narrowComparison) worlds.symm executed
    rw [ExtendedComparisonRead.spec_eq narrowComparison] at run
    obtain ⟨actual,realized,related'⟩ := refines_valueSem F ctx X _ us t outs spec run
    exact ⟨actual,realized,related'.trans related.symm⟩

  · simp only [sem,mask_special mask,↓reduceIte] at executed
    obtain ⟨spec,run,related⟩ := mspec_lockstep (MaskRead.no_mem mask) worlds.symm executed
    rw [MaskRead.spec_eq mask] at run
    obtain ⟨actual,realized,related'⟩ := refines_valueSem F ctx X _ us t outs spec run
    exact ⟨actual,realized,related'.trans related.symm⟩

end Realize

private noncomputable def boundaryModel : ABIReadBoundary.Model where
  instruction := Backend.ABIReadScalar.instruction
  eval := sem
  frame := checked_step_frame
  transport := checked_step_transport
  realize := Realize.step_realize

abbrev check := Backend.ABIReadScalar.check

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
  exact ABIReadBoundary.return_transport (model := boundaryModel) types checked worlds registers stack returned

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
  exact ABIReadBoundary.machine_return (model := boundaryModel) types readOnly prep check alloc emit layout frame covered arguments worlds returned H G base ra s entry

theorem checked_instruction {sig : Clif.Signature} {vc : VCode}
    (checked : check sig vc = true) {b k : Nat} {vb : VBlock} {i : MInst}
    (block : vc.blocks[b]? = some vb) (inst : vb.insts[k]? = some i) :
    Backend.ABIReadScalar.instruction sig b k i = true :=
  ABIReadBoundary.checked_instruction (model := boundaryModel) checked block inst

end E2E.ScalarBoundary
