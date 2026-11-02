import FV.Backend.ABIReadFlags
import FV.Backend.Proof.IselCmpRun
import FV.E2E.ABIReadOnlyRealize

namespace E2E.MixedFlagBoundary
open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup
set_option autoImplicit false
set_option Elab.async false

/-- Additional forms actually used by parameter-conditioned scalar select.
This classifier does not change the dead-code-removal whitelist. -/
abbrev extra := Backend.ABIReadFlags.extra

/-- Executable facts expose only concrete instruction shapes. -/
theorem extra_cases {i : MInst} (checked : extra i = true) :
    (∃ sz n, i = .aluRRR .subS sz .xzr (.vreg n .int) .xzr) ∨
    (∃ d n m c, i = .csel (.vreg d .int) (.vreg n .int) (.vreg m .int) c) := by
  cases i with
  | aluRRR op sz rd rn rm =>
    cases op <;> try cases checked
    cases rd <;> try cases checked
    cases rn <;> try cases checked
    case vreg n cls =>
      cases cls <;> try cases checked
      cases rm <;> try cases checked
      exact .inl ⟨sz,n,rfl⟩
  | csel rd rn rm c =>
    cases rd <;> try cases checked
    case vreg d cls =>
      cases cls <;> try cases checked
      cases rn <;> try cases checked
      case vreg n cls =>
        cases cls <;> try cases checked
        cases rm <;> try cases checked
        case vreg m cls =>
          cases cls <;> try cases checked
          exact .inr ⟨d,n,m,c,rfl⟩
  | _ => cases checked

private theorem no_mem {i : MInst} (checked : extra i = true) : i.isMemAcc = false := by
  rcases extra_cases checked with ⟨sz,n,rfl⟩ | ⟨d,n,m,c,rfl⟩ <;> rfl

private theorem spec_eq {i : MInst} (checked : extra i = true) (sb : Nat)
    (us : List CV) (w : Arm.ArmState) : mspec sb i us w = ispec i us w := by
  rcases extra_cases checked with ⟨sz,n,rfl⟩ | ⟨d,n,m,c,rfl⟩ <;> rfl

/-- Extra select forms may change NZCV, while preserving the full memory and
all non-flag world fields required by the source memory relation. -/
theorem step_frame {i : MInst} (checked : extra i = true) {sb : Nat}
    {us outs : List CV} {w t : Arm.ArmState} {ctl : Ctl}
    (run : mspec sb i us w = some (outs,t,ctl)) :
    SameWorldNF (fun _ => False) t w ∧ ctl = .next := by
  rw [spec_eq checked] at run
  rcases extra_cases checked with ⟨sz,n,rfl⟩ | ⟨d,n,m,c,rfl⟩
  · cases us with
    | nil => cases run
    | cons a rest =>
      cases rest with
      | cons b tail =>
        cases tail with
        | cons c rest => simp [ispec] at run
        | nil =>
          simp only [ispec,Option.some.injEq,Prod.mk.injEq] at run
          obtain ⟨rfl,rfl,rfl⟩ := run
          exact ⟨SameWorldNF.write_pstate _ _ _,rfl⟩
      | nil =>
        simp only [ispec,Option.some.injEq,Prod.mk.injEq] at run
        obtain ⟨rfl,rfl,rfl⟩ := run
        exact ⟨SameWorldNF.write_pstate _ _ _,rfl⟩
  · cases us with
    | nil => cases run
    | cons a rest =>
      cases rest with
      | nil => cases run
      | cons b tail =>
        cases tail with
        | cons c rest => cases run
        | nil =>
          simp only [ispec,Option.some.injEq,Prod.mk.injEq] at run
          obtain ⟨rfl,rfl,rfl⟩ := run
          exact ⟨SameWorld.nf (SameWorld.refl _ _),rfl⟩

/-- Equal virtual operands on related worlds produce equal values/control and
related successor worlds, including the newly computed flags. -/
theorem step_transport {i : MInst} (checked : extra i = true) {sb : Nat}
    {Z : BitVec 64 → Prop} {w w' : Arm.ArmState} (worlds : SameWorld Z w w')
    {us outs : List CV} {t : Arm.ArmState} {ctl : Ctl}
    (run : mspec sb i us w = some (outs,t,ctl)) :
    ∃ t', mspec sb i us w' = some (outs,t',ctl) ∧ SameWorld Z t t' :=
  mspec_lockstep (no_mem checked) worlds run

/-- Realize the flag-threaded specification through the existing shipped
value semantics, retaining identical outputs and flags on related worlds. -/
theorem step_realize {i : MInst} (checked : extra i = true)
    {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem}
    {us outs : List CV} {w w' t : Arm.ArmState} {ctl : Ctl}
    (worlds : SameWorld F w' w)
    (run : mspec ctx.slotBase i us w = some (outs,t,ctl)) :
    ∃ t', valueSem F ctx X i us w' = some (outs,t',ctl) ∧ SameWorld F t' t := by
  obtain ⟨spec,executed,related⟩ := step_transport checked worlds.symm run
  rw [spec_eq checked] at executed
  obtain ⟨actual,realized,related'⟩ := refines_valueSem F ctx X i us w' outs spec executed
  exact ⟨actual,realized,related'.trans related.symm⟩

/-- A real compare step and dependent conditional select preserve the flag
thread; both outcomes are covered for arbitrary words and caller state. -/
theorem compare_select_witness (sz : OperandSize) (a x y : CV) (w : Arm.ArmState) :
    ∃ t,
      mspec 0 (.aluRRR .subS sz .xzr (.vreg 0 .int) .xzr) [a] w = some ([],t,.next) ∧
      mspec 0 (.csel (.vreg 3 .int) (.vreg 1 .int) (.vreg 2 .int) .ne) [x,y] t =
        some ([ofX (if Arm.ConditionHolds Cond.ne.bits t then lo64 x else lo64 y)],t,.next) := by
  exact ⟨_,rfl,rfl⟩


/-- Proof semantics classify the operation independently of register names;
the executable boundary above restricts actual accepted shapes. -/
def special : MInst → Bool
  | .aluRRR .subS .. | .csel .. => true
  | _ => false

noncomputable def sem (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) : Sem :=
  fun i us w => if special i then mspec ctx.slotBase i us w else ABIReadOnly.sem F ctx X i us w

/-- The original source specification is preserved, including flag updates. -/
theorem refines (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) :
    Refines F (sem F ctx X) := by
  intro i us w outs w' ctl executed
  by_cases hs : special i = true
  · exact ⟨w',by simp only [sem,hs,↓reduceIte]; exact mspec_of_ispec executed,SameWorld.refl F w'⟩
  · simpa only [sem,show special i = false from Bool.eq_false_iff.mpr hs,Bool.false_eq_true,↓reduceIte] using
      ABIReadOnly.refines F ctx X i us w outs w' executed

/-- Memory and symbol contracts retain the existing implementation. -/
theorem memory (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem)
    {sb : Nat} {syms : String → Option Nat} (base : ctx.slotBase = sb)
    (symbols : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b) :
    MemRefines F sb syms (sem F ctx X) := by
  simpa only [MemRefines,sem,special,Bool.false_eq_true,↓reduceIte] using ABIReadOnly.memory F ctx X base symbols

/-- Alias resolution, retargeting and actual ABI argument reads retain their
original driver contracts. No chosen virtual file is added to source inputs. -/
theorem driver (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) :
    DriverSem (sem F ctx X) := by
  have hd := ABIReadOnly.driver F ctx X
  refine ⟨⟨?_,?_,?_⟩,?_⟩
  · intro l w; exact hd.jump l w
  · intro g gn hg i
    funext us w
    have old := congrFun (congrFun (hd.rename g gn hg i) us) w
    have spec := mspec_mapRegs hg ctx.slotBase i us w
    cases i with
    | aluRRR op sz rd rn rm =>
      cases op
      all_goals first
        | simpa only [sem,special,MInst.mapRegs,Bool.false_eq_true,↓reduceIte] using spec
        | simpa only [sem,special,MInst.mapRegs,Bool.false_eq_true,↓reduceIte] using old
    | csel rd rn rm c => simpa only [sem,special,MInst.mapRegs,Bool.false_eq_true,↓reduceIte] using spec
    | _ => simpa only [sem,special,MInst.mapRegs,Bool.false_eq_true,↓reduceIte] using old
  · intro i ls i' targets
    have old := hd.retarget i ls i' targets
    unfold MInst.setTargets at targets
    split at targets
    all_goals repeat' first | cases targets | split at targets
    all_goals
      funext us w
      simpa only [sem,special,Bool.false_eq_true,↓reduceIte] using congrFun (congrFun old us) w
  · intro ds w; exact hd.args ds w


/-- Specification worlds differ only in flags; even masked physical registers
are retained, so original ABI reads remain available while flags are threaded. -/
def FlagFrame (w t : Arm.ArmState) : Prop :=
  (∀ f, (∀ fl, f ≠ .FLAG fl) → Arm.r f t = Arm.r f w) ∧
  t.mem = w.mem ∧ t.program = w.program

theorem FlagFrame.refl (w : Arm.ArmState) : FlagFrame w w :=
  ⟨fun _ _ => rfl,rfl,rfl⟩

theorem FlagFrame.write_pstate (ps : Arm.PState) (w : Arm.ArmState) :
    FlagFrame w (Arm.write_pstate ps w) := by
  refine ⟨fun f nonflag => ?_,?_,?_⟩
  · simp only [Arm.write_pstate]
    rw [Arm.r_of_w_different (nonflag _),Arm.r_of_w_different (nonflag _),
      Arm.r_of_w_different (nonflag _),Arm.r_of_w_different (nonflag _)]
  · simp only [Arm.write_pstate,Arm.ArmState.mem_w_eq_mem]
  · simp only [Arm.write_pstate,Arm.w_program]

private theorem old_not_special {sig : Clif.Signature} {b k : Nat} {i : MInst}
    (checked : Backend.ABIReadOnly.instruction sig b k i = true) : special i = false := by
  cases i with
  | aluRRR op sz rd rn rm =>
    cases op <;> simp_all [special,Backend.ABIReadOnly.instruction,pureNoFlags,pureForm,pureAlu]
  | csel rd rn rm c => cases checked
  | _ => rfl

private theorem extra_special {i : MInst} (checked : extra i = true) : special i = true := by
  rcases extra_cases checked with ⟨sz,n,rfl⟩ | ⟨d,n,m,c,rfl⟩ <;> rfl

/-- Extra select forms may change NZCV, while preserving the full memory and
all non-flag world fields required by the source memory relation. -/
theorem step_flag_frame {i : MInst} (checked : extra i = true) {sb : Nat}
    {us outs : List CV} {w t : Arm.ArmState} {ctl : Ctl}
    (run : mspec sb i us w = some (outs,t,ctl)) :
    FlagFrame w t ∧ ctl = .next := by
  rw [spec_eq checked] at run
  rcases extra_cases checked with ⟨sz,n,rfl⟩ | ⟨d,n,m,c,rfl⟩
  · cases us with
    | nil => cases run
    | cons a rest =>
      cases rest with
      | cons b tail =>
        cases tail with
        | cons c rest => simp [ispec] at run
        | nil =>
          simp only [ispec,Option.some.injEq,Prod.mk.injEq] at run
          obtain ⟨rfl,rfl,rfl⟩ := run
          exact ⟨FlagFrame.write_pstate _ _,rfl⟩
      | nil =>
        simp only [ispec,Option.some.injEq,Prod.mk.injEq] at run
        obtain ⟨rfl,rfl,rfl⟩ := run
        exact ⟨FlagFrame.write_pstate _ _,rfl⟩
  · cases us with
    | nil => cases run
    | cons a rest =>
      cases rest with
      | nil => cases run
      | cons b tail =>
        cases tail with
        | cons c rest => cases run
        | nil =>
          simp only [ispec,Option.some.injEq,Prod.mk.injEq] at run
          obtain ⟨rfl,rfl,rfl⟩ := run
          exact ⟨FlagFrame.refl _,rfl⟩


/-- The executable combined boundary preserves every ABI register/memory byte,
threading the actual flag changes rather than assuming an unchanged world. -/
theorem checked_step_frame {sig : Clif.Signature} {b k : Nat} {i : MInst}
    (checked : (Backend.ABIReadOnly.instruction sig b k i || extra i) = true)
    {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem}
    {us outs : List CV} {w t : Arm.ArmState} {ctl : Ctl}
    (run : sem F ctx X i us w = some (outs,t,ctl)) :
    FlagFrame w t ∧ (ctl = .next ∨ ctl = .ret) := by
  simp only [Bool.or_eq_true] at checked
  rcases checked with old | added
  · have ordinary := old_not_special old
    simp only [sem,ordinary,Bool.false_eq_true,↓reduceIte] at run
    have unchanged := ABIReadOnly.step_world old run
    subst t
    exact ⟨FlagFrame.refl _,ABIReadOnly.step_control old run⟩
  · simp only [sem,extra_special added,↓reduceIte] at run
    obtain ⟨frame,control⟩ := step_flag_frame added run
    exact ⟨frame,.inl control⟩


theorem FlagFrame.trans {w t u : Arm.ArmState}
    (first : FlagFrame w t) (second : FlagFrame t u) : FlagFrame w u :=
  ⟨fun f h => (second.1 f h).trans (first.1 f h),
    second.2.1.trans first.2.1,second.2.2.trans first.2.2⟩

theorem FlagFrame.regVal {w t : Arm.ArmState} (frame : FlagFrame w t) (r : Reg) :
    regVal t r = regVal w r := by
  cases r with
  | x n => exact congrArg (fun bits : BitVec 64 => bits.setWidth 128) (frame.1 (.GPR (rnum n)) (by intro fl eq; cases eq))
  | v n => exact frame.1 (.SFP (rnum n)) (by intro fl eq; cases eq)
  | _ => rfl

/-- Transfer checked flag-threaded steps with the same virtual operands,
using only the original ABI agreement and internally preserved physical reads. -/
theorem checked_step_transport {sig : Clif.Signature} {args : List Clif.Val}
    (types : args.map (·.ty) = sig.params.map (·.ty))
    {b k : Nat} {i : MInst}
    (checked : (Backend.ABIReadOnly.instruction sig b k i || extra i) = true)
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
  simp only [Bool.or_eq_true] at checked
  rcases checked with old | added
  · have hs := old_not_special old
    simp only [sem,hs,Bool.false_eq_true,↓reduceIte] at run ⊢
    have fixed := ABIReadOnly.step_world old run
    subst t
    have regs : ∀ r v, (.reg r,v) ∈ (locsOf sig).zip args → regVal w' r = regVal w r := by
      intro r v member
      rw [other.regVal r,current.regVal r]
      exact registers r v member
    have bytes : ∀ (off : Nat) (v : Clif.Val), (.stack off,v) ∈ (locsOf sig).zip args →
        ∀ j < v.ty.bytes,
        w'.mem (Arm.r (.GPR 29#5) w + BitVec.ofInt 64 (16+(off : Int)) + BitVec.ofNat 64 j) =
        w.mem (Arm.r (.GPR 29#5) w + BitVec.ofInt 64 (16+(off : Int)) + BitVec.ofNat 64 j) := by
      intro off v member j bound
      rw [other.2.1,current.2.1,current.1 (.GPR 29#5) (by intro fl eq; cases eq)]
      exact stack off v member j bound
    exact ⟨w',ABIReadOnly.step_transport types old worlds regs bytes run,worlds⟩
  · have hs := extra_special added
    simp only [sem,hs,↓reduceIte] at run ⊢
    exact step_transport added worlds run

abbrev instruction := Backend.ABIReadFlags.instruction
abbrev check := Backend.ABIReadFlags.check

theorem checked_instruction {sig : Clif.Signature} {vc : VCode}
    (checked : check sig vc = true) {b k : Nat} {vb : VBlock} {i : MInst}
    (block : vc.blocks[b]? = some vb) (inst : vb.insts[k]? = some i) :
    (Backend.ABIReadOnly.instruction sig b k i || extra i) = true := by
  have bm : (vb,b) ∈ vc.blocks.toList.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr (by simpa using block)
  have im : (i,k) ∈ vb.insts.toList.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr (by simpa using inst)
  exact List.all_eq_true.mp (List.all_eq_true.mp checked (vb,b) bm) (i,k) im

def Related (Z : BitVec 64 → Prop) (initial initial' : Arm.ArmState)
    (c d : VConf CV Arm.ArmState) : Prop :=
  ∃ w w', c.mapW (fun _ => w) = c ∧ d = c.mapW (fun _ => w') ∧
    FlagFrame initial w ∧ FlagFrame initial' w' ∧ SameWorld Z w w'

theorem FlagFrame.arguments {F : BitVec 64 → Prop} {sig : Clif.Signature}
    {args : List Clif.Val} {w t : Arm.ArmState} (frame : FlagFrame w t)
    (arguments : ArgsAtEntry F sig args w) : ArgsAtEntry F sig args t := by
  intro loc value member
  have given := arguments loc value member
  cases loc with
  | reg r =>
    change VHolds value (Backend.Proof.regVal t r)
    rw [frame.regVal r]
    exact given
  | stack off =>
    have fp := frame.1 (.GPR 29#5) (by intro fl eq; cases eq)
    change Avoids F value.ty.bytes _ ∧ _
    rw [fp]
    refine ⟨given.1,?_⟩
    have bytes := read_mem_bytes_congr (s := t) (t := w) value.ty.bytes
      (Arm.r (.GPR 29#5) w + BitVec.ofInt 64 (16+(off : Int)))
      (fun j hj => congrFun frame.2.1 _)
    rw [bytes]
    exact given.2

namespace Realize
/-- Realize each checked flag-threaded step at the existing machine boundary. -/
theorem step_realize {sig : Clif.Signature} {args : List Clif.Val}
    (types : args.map (·.ty) = sig.params.map (·.ty))
    {b k : Nat} {i : MInst}
    (checked : (Backend.ABIReadOnly.instruction sig b k i || extra i) = true)
    {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem}
    {initial w t final : Arm.ArmState} (frame : FlagFrame initial w)
    (arguments : ArgsAtEntry F sig args initial) (worlds : SameWorld F t w)
    (entry : k = 0 → t = w) {us outs : List CV} {ctl : Ctl}
    (executed : sem F ctx X i us w = some (outs,final,ctl)) :
    ∃ actual, valueSem F ctx X i us t = some (outs,actual,ctl) ∧ SameWorld F actual final := by
  simp only [Bool.or_eq_true] at checked
  rcases checked with old | added
  · simp only [sem,old_not_special old,Bool.false_eq_true,↓reduceIte] at executed
    have unchanged := ABIReadOnly.step_world old executed
    subst final
    exact ABIReadOnly.step_realize types old (frame.arguments arguments) worlds entry executed
  · simp only [sem,extra_special added,↓reduceIte] at executed
    exact E2E.MixedFlagBoundary.step_realize added worlds executed

def Related (F : BitVec 64 → Prop) (initial : Arm.ArmState)
    (c d : VConf CV Arm.ArmState) : Prop :=
  ∃ w t, c.mapW (fun _ => w) = c ∧ d = c.mapW (fun _ => t) ∧
    FlagFrame initial w ∧ SameWorld F t w ∧
    ∀ vs, c = .run vs → vs.k = 0 → t = w

end Realize

end E2E.MixedFlagBoundary
