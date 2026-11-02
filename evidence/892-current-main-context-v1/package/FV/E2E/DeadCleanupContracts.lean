import FV.Backend.Proof.DeadCleanupAdapter
import FV.E2E.RegLevelDriverSem

namespace Backend.DeadCleanup
open Backend.Proof Backend.Proof.Driver

private theorem pureForm_mapRegs (g : Reg → Reg) (i : MInst) :
    pureForm (i.mapRegs g) = pureForm i := by
  cases i <;> simp [MInst.mapRegs, pureForm]
  case aluRRRR op size rd rn rm ra => cases op <;> rfl

/-- A vreg renaming keeps the compare forms (`xzr` and real registers are fixed, vregs stay
vregs). -/
theorem cmpForm_mapRegs {g : Reg → Reg} {gn : Nat → Nat} (hg : VRenaming g gn) (i : MInst) :
    cmpForm (i.mapRegs g) = cmpForm i := by
  have hx : ∀ n, g (.x n) = .x n := fun n => hg.real _ (by intro _ _ h; cases h)
  have hz : g .xzr = .xzr := hg.real _ (by intro _ _ h; cases h)
  have hs : g .sp = .sp := hg.real _ (by intro _ _ h; cases h)
  have hv : ∀ n, g (.v n) = .v n := fun n => hg.real _ (by intro _ _ h; cases h)
  cases i with
  | aluRRR op sz rd rn rm =>
    cases rd <;> cases rn <;> simp only [MInst.mapRegs, hg.vreg, hx, hz, hs, hv] <;>
      cases op <;> rfl
  | aluRRImm12 op sz rd rn imm =>
    cases rd <;> cases rn <;> simp only [MInst.mapRegs, hg.vreg, hx, hz, hs, hv] <;>
      cases op <;> rfl
  | aluRRRExtend op sz rd rn rm e =>
    cases rd <;> cases rn <;> cases rm <;> simp only [MInst.mapRegs, hg.vreg, hx, hz, hs, hv] <;>
      cases op <;> rfl
  | aluRRImmLogic op sz rd rn imm =>
    cases rd <;> cases rn <;> simp only [MInst.mapRegs, hg.vreg, hx, hz, hs, hv] <;>
      cases op <;> rfl
  | _ => rfl

theorem specForm_mapRegs {g : Reg → Reg} {gn : Nat → Nat} (hg : VRenaming g gn) (i : MInst) :
    specForm (i.mapRegs g) = specForm i := by
  simp only [specForm, pureForm_mapRegs, cmpForm_mapRegs hg]

theorem specForm_setTargets {i i' : MInst} {ls : List Label}
    (h : i.setTargets ls = some i') : specForm i' = specForm i := by
  unfold MInst.setTargets at h
  split at h
  all_goals (try split at h)
  all_goals (cases h)
  all_goals rfl

/-- The value semantics keeps all existing driver interface facts. -/
theorem driverSem_valueSem (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) :
    DriverSem (valueSem F ctx X) := by
  have hd := driverSem_csem F ctx X
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro l w; simpa [valueSem, specForm, pureForm, cmpForm] using hd.jump l w
  · intro g gn hg i
    funext us w
    simp only [valueSem, specForm_mapRegs hg]
    by_cases hp : specForm i = true
    · simp only [hp]
      exact mspec_mapRegs hg _ _ _ _
    · simp only [hp]
      exact congrFun (congrFun (hd.rename g gn hg i) us) w
  · intro i ls i' h
    have he := specForm_setTargets h
    funext us w
    simp only [valueSem, he]
    by_cases hp : specForm i = true
    · cases i <;> simp [MInst.setTargets] at h <;> simp [specForm, pureForm, cmpForm] at hp
    · simp only [hp]
      exact congrFun (congrFun (hd.retarget i ls i' h) us) w
  · intro ds w; simpa [valueSem, specForm, pureForm, cmpForm] using hd.args ds w

/-- Loads, stores, atomics, TLS and symbol contracts retain their original
meaning; the pure slot-address specification leaves the world unchanged. -/
theorem memRefines_valueSem (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem)
    {sb : Nat} {syms : String → Option Nat} (hsb : ctx.slotBase = sb)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b) :
    MemRefines F sb syms (valueSem F ctx X) := by
  subst sb
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := memRefines_csem F ctx X rfl hsym
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [valueSem, specForm, pureForm, cmpForm] using h1
  · simpa [valueSem, specForm, pureForm, cmpForm] using h2
  · intro d off w
    exact ⟨w, rfl, SameWorld.refl F w⟩
  · simpa [valueSem, specForm, pureForm, cmpForm] using h4
  · simpa [valueSem, specForm, pureForm, cmpForm] using h5
  · simpa [valueSem, specForm, pureForm, cmpForm] using h6
  · simpa [valueSem, specForm, pureForm, cmpForm] using h7
  · simpa [valueSem, specForm, pureForm, cmpForm] using h8
  · simpa [valueSem, specForm, pureForm, cmpForm] using h9

/-- Calls keep the external contract without changing signatures or scope. -/
theorem callsRefine_valueSem {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem}
    {env : Clif.Env} {exts : List Clif.ExtFunc} {MR : MemRelT}
    (hX : XCallsOk env exts MR X) : CallsRefine F env exts MR (valueSem F ctx X) := by
  simpa [CallsRefine, valueSem, specForm, pureForm, cmpForm] using
    (callsRefine_csem (ctx := ctx) (F := F) hX)

/-- Indirect calls keep the external contract as well. -/
theorem indCallsRefine_valueSem {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem}
    {env : Clif.Env} {sigs : List Clif.Signature} {MR : MemRelT}
    {syms : String → Option Nat}
    (hX : XCallsIndOk env sigs MR X) (hsym : ∀ n b, syms n = some b →
      X.sym n 0 = BitVec.ofNat 64 b)
    (hMR : ∀ sl cm w, MR sl cm w → cm.symbols = syms) :
    IndCallsRefine env sigs MR (valueSem F ctx X) := by
  simpa [IndCallsRefine, valueSem, specForm, pureForm, cmpForm] using
    (indCallsRefine_csem (ctx := ctx) (F := F) hX hsym hMR)

end Backend.DeadCleanup
