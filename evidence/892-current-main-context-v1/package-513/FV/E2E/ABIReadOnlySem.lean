import FV.E2E.DeadCleanupContracts

namespace E2E.ABIReadOnly
open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup
set_option autoImplicit false
set_option Elab.async false

/-- Ordinary loads use their unchanged-world specification. Other instruction
semantics are retained. The executable ABI-read checker supplies their actual
read boundary; no machine instruction or runtime compiler output is changed. -/
noncomputable def sem (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) : Sem :=
  fun i us w => match i with
    | .load .. => mspec ctx.slotBase i us w
    | _ => valueSem F ctx X i us w

/-- The source instruction specification remains valid. -/
theorem refines (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) :
    Refines F (sem F ctx X) := by
  intro i us w outs w' ctl h
  cases i with
  | load op rd am fl => simp [ispec] at h
  | _ => exact refines_valueSem F ctx X _ _ _ _ _ h

/-- The existing memory contract permits the unchanged-world load result. -/
theorem memory (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem)
    {sb : Nat} {syms : String → Option Nat} (hsb : ctx.slotBase = sb)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b) :
    MemRefines F sb syms (sem F ctx X) := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩ := memRefines_valueSem F ctx X hsb hsym
  refine ⟨?_,h2,h3,h4,h5,h6,h7,h8,h9⟩
  intro op d am fl us w a hop ha hav
  refine ⟨w,?_,SameWorld.refl F w⟩
  simp only [sem,mspec,hop,ite_false,hsb,ha,Option.map_some]

/-- The unchanged-world loads preserve the original renaming and control
interface; argument copies still read actual ABI registers. -/
theorem driver (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) :
    DriverSem (sem F ctx X) := by
  have hd := driverSem_valueSem F ctx X
  refine ⟨⟨?_,?_,?_⟩,?_⟩
  · intro l w; exact hd.jump l w
  · intro g gn hg i
    funext us w
    cases i with
    | load op rd am fl => exact mspec_mapRegs hg ctx.slotBase _ us w
    | _ => exact congrFun (congrFun (hd.rename g gn hg _) us) w
  · intro i ls i' h
    have old := hd.retarget i ls i' h
    unfold MInst.setTargets at h
    split at h
    all_goals repeat' first | cases h | split at h
    all_goals exact old
  · intro ds w; exact hd.args ds w

end E2E.ABIReadOnly
