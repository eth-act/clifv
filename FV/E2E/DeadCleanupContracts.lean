import FV.Backend.Proof.DeadCleanupAdapter
import FV.E2E.RegLevelDriverSem

namespace Backend.DeadCleanup
open Backend.Proof Backend.Proof.Driver

private theorem pureForm_mapRegs (g : Reg → Reg) (i : MInst) :
    pureForm (i.mapRegs g) = pureForm i := by
  cases i <;> simp [MInst.mapRegs, pureForm]
  case aluRRRR op size rd rn rm ra => cases op <;> rfl

private theorem pureForm_setTargets {i i' : MInst} {ls : List Label}
    (h : i.setTargets ls = some i') : pureForm i' = pureForm i := by
  unfold MInst.setTargets at h
  split at h <;> simp_all [pureForm]
  all_goals first | (cases h; rfl) | (rcases h with ⟨_, rfl⟩; rfl)

/-- The value semantics keeps all existing driver interface facts. -/
theorem driverSem_valueSem (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) :
    DriverSem (valueSem F ctx X) := by
  have hd := driverSem_csem F ctx X
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro l w; simpa [valueSem, pureForm] using hd.jump l w
  · intro g gn hg i
    funext us w
    simp only [valueSem, pureForm_mapRegs]
    by_cases hp : pureForm i = true
    · simp only [hp]
      exact mspec_mapRegs hg _ _ _ _
    · simp only [hp]
      exact congrFun (congrFun (hd.rename g gn hg i) us) w
  · intro i ls i' h
    have he := pureForm_setTargets h
    funext us w
    simp only [valueSem, he]
    by_cases hp : pureForm i = true
    · have hn := pureForm_targets hp
      cases i <;> simp [pureForm, MInst.setTargets] at hp h
    · simp only [hp]
      exact congrFun (congrFun (hd.retarget i ls i' h) us) w
  · intro ds w; simpa [valueSem, pureForm] using hd.args ds w

/-- Loads, stores, atomics, TLS and symbol contracts retain their original
meaning; the pure slot-address specification leaves the world unchanged. -/
theorem memRefines_valueSem (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem)
    {sb : Nat} {syms : String → Option Nat} (hsb : ctx.slotBase = sb)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b) :
    MemRefines F sb syms (valueSem F ctx X) := by
  subst sb
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := memRefines_csem F ctx X rfl hsym
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [valueSem, pureForm] using h1
  · simpa [valueSem, pureForm] using h2
  · intro d off w
    exact ⟨w, rfl, SameWorld.refl F w⟩
  · simpa [valueSem, pureForm] using h4
  · simpa [valueSem, pureForm] using h5
  · simpa [valueSem, pureForm] using h6
  · simpa [valueSem, pureForm] using h7
  · simpa [valueSem, pureForm] using h8
  · simpa [valueSem, pureForm] using h9

/-- Calls keep the external contract without changing signatures or scope. -/
theorem callsRefine_valueSem {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem}
    {env : Clif.Env} {exts : List Clif.ExtFunc} {MR : MemRelT}
    (hX : XCallsOk env exts MR X) : CallsRefine F env exts MR (valueSem F ctx X) := by
  simpa [CallsRefine, valueSem, pureForm] using
    (callsRefine_csem (ctx := ctx) (F := F) hX)

/-- Indirect calls keep the external contract as well. -/
theorem indCallsRefine_valueSem {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem}
    {env : Clif.Env} {sigs : List Clif.Signature} {MR : MemRelT}
    {syms : String → Option Nat}
    (hX : XCallsIndOk env sigs MR X) (hsym : ∀ n b, syms n = some b →
      X.sym n 0 = BitVec.ofNat 64 b)
    (hMR : ∀ sl cm w, MR sl cm w → cm.symbols = syms) :
    IndCallsRefine env sigs MR (valueSem F ctx X) := by
  simpa [IndCallsRefine, valueSem, pureForm] using
    (indCallsRefine_csem (ctx := ctx) (F := F) hX hsym hMR)

end Backend.DeadCleanup
