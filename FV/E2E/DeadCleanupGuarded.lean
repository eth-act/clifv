import FV.E2E.Guarded
import FV.E2E.DeadCleanupContracts

namespace E2E
open Backend Backend.Proof Backend.DeadCleanup

/-- The existing read/call guards, with pure producers using value semantics. -/
noncomputable def valueSemG (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) (Rd : BitVec 64 → Prop)
    (syms : String → Option Nat) (exts : List Clif.ExtFunc) (sigs : List Clif.Signature) (sp0 : BitVec 64)
    (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop) : Sem :=
  fun i us w => if pureForm i then mspec ctx.slotBase i us w
    else csemG F ctx X Rd syms exts sigs sp0 Pc i us w

variable {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {Rd : BitVec 64 → Prop}
  {syms : String → Option Nat} {exts : List Clif.ExtFunc} {sigs : List Clif.Signature}
  {sp0 : BitVec 64}
  {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop}

private theorem pure_guarded {i : MInst} (hp : pureForm i = true) (us : List CV) (w : Arm.ArmState) :
    csemG F ctx X Rd syms exts sigs sp0 Pc i us w = csem F ctx X i us w := by
  apply csemG_of
  · cases i <;> simp_all [GuardR, pureForm]
  · cases i <;> simp_all [GuardC, pureForm]

theorem valueSemG_sub {i : MInst} {us : List CV} {w : Arm.ArmState} {r : List CV × Arm.ArmState × Ctl}
    (h : valueSemG F ctx X Rd syms exts sigs sp0 Pc i us w = some r) :
    valueSem F ctx X i us w = some r := by
  by_cases hp : pureForm i = true
  · simpa [valueSemG, valueSem, hp] using h
  · simp only [valueSemG, hp, Bool.false_eq_true, ite_false] at h
    simpa [valueSem, hp] using (csemG_sub h).2.2

theorem refines_valueSemG : Refines F (valueSemG F ctx X Rd syms exts sigs sp0 Pc) := by
  intro i us w outs w' ctl h
  by_cases hp : pureForm i = true
  · exact ⟨w', by simp [valueSemG, hp, mspec_of_ispec h], SameWorld.refl F w'⟩
  · simpa [valueSemG, hp] using (refines_csemG (F := F) (ctx := ctx) (X := X)
      (Rd := Rd) (syms := syms) (exts := exts) (sigs := sigs) (sp0 := sp0) (Pc := Pc)) i us w outs w' h

theorem memRefinesR_valueSemG {sb : Nat} (hsb : ctx.slotBase = sb)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b) :
    MemRefinesR Rd F sb syms (valueSemG F ctx X Rd syms exts sigs sp0 Pc) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
    memRefinesR_csemG (F := F) (ctx := ctx) (X := X) (Rd := Rd) (exts := exts)
      (sigs := sigs) (sp0 := sp0) (Pc := Pc) hsb hsym
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [valueSemG, pureForm] using h1
  · simpa [valueSemG, pureForm] using h2
  · intro d off w
    subst sb
    exact ⟨w, rfl, SameWorld.refl F w⟩
  · simpa [valueSemG, pureForm] using h4
  · simpa [valueSemG, pureForm] using h5
  · simpa [valueSemG, pureForm] using h6
  · simpa [valueSemG, pureForm] using h7
  · simpa [valueSemG, pureForm] using h8
  · simpa [valueSemG, pureForm] using h9

theorem callsRefineP_valueSemG {env : Clif.Env} {exts : List Clif.ExtFunc} {MR : MemRelT}
    (hX : XCallsOk env exts MR X) (hMRm : ∀ sl cm w, MR sl cm w → MemRel F syms cm w)
    (hMRc : ∀ sl cm w, MR sl cm w → spv w = sp0) :
    CallsRefineP Pc F env exts MR (valueSemG F ctx X Rd syms exts sigs sp0 Pc) := by
  simpa [CallsRefineP, valueSemG, pureForm] using
    (callsRefineP_csemG (F := F) (ctx := ctx) (X := X) (Rd := Rd)
      (syms := syms) (exts := exts) (sigs := sigs) (sp0 := sp0) (Pc := Pc) hX hMRm hMRc)

theorem indCallsRefineP_valueSemG {env : Clif.Env} {sigs : List Clif.Signature} {MR : MemRelT}
    (hX : XCallsIndOk env sigs MR X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hMRm : ∀ sl cm w, MR sl cm w → MemRel F syms cm w)
    (hMRc : ∀ sl cm w, MR sl cm w → spv w = sp0) :
    IndCallsRefineP Pc env sigs MR (valueSemG F ctx X Rd syms exts sigs sp0 Pc) := by
  simpa [IndCallsRefineP, valueSemG, pureForm] using
    (indCallsRefineP_csemG (F := F) (ctx := ctx) (X := X) (Rd := Rd)
      (syms := syms) (exts := exts) (sigs := sigs) (sp0 := sp0) (Pc := Pc) hX hsym hMRm hMRc)
theorem valueSemG_lockstep2 {Z : BitVec 64 → Prop} (hFZ : ∀ a, F a → Z a) {i : MInst} {us : List CV}
    {w w' : Arm.ArmState} (hw : SameWorld Z w w')
    (hX : ∀ dest, CallG F syms X exts sigs sp0 Pc dest us w → CallG F syms X exts sigs sp0 Pc dest us w' →
      ∀ o x o' x', X.call (destName dest) us w = some (o, x) →
        X.call (destName dest) us w' = some (o', x') → o = o' ∧ SameWorld Z x x')
    (hT : ∀ n, X.tlsFlags n w = X.tlsFlags n w')
    {o o' : List CV} {w₁ w₁' : Arm.ArmState} {c c' : Ctl}
    (h : valueSemG F ctx X (fun b => ¬ Z b) syms exts sigs sp0 Pc i us w = some (o, w₁, c))
    (h' : valueSemG F ctx X (fun b => ¬ Z b) syms exts sigs sp0 Pc i us w' = some (o', w₁', c')) :
    o = o' ∧ c = c' ∧ SameWorld Z w₁ w₁' := by
  by_cases hp : pureForm i = true
  · have hs : mspec ctx.slotBase i us w = some (o, w₁, c) := by
      simpa [valueSemG, hp] using h
    have hs' : mspec ctx.slotBase i us w' = some (o', w₁', c') := by
      simpa [valueSemG, hp] using h'
    obtain ⟨hew, hec⟩ := mspec_pure hp hs
    obtain ⟨hew', hec'⟩ := mspec_pure hp hs'
    subst w₁; subst c; subst w₁'; subst c'
    obtain ⟨wc, hc, _⟩ := pure_mspec_csem (F := F) (X := X) hp hs
    obtain ⟨wc', hc', _⟩ := pure_mspec_csem (F := F) (X := X) hp hs'
    have hg : csemG F ctx X (fun b => ¬ Z b) syms exts sigs sp0 Pc i us w =
        some (o, wc, .next) := (pure_guarded hp us w).trans hc
    have hg' : csemG F ctx X (fun b => ¬ Z b) syms exts sigs sp0 Pc i us w' =
        some (o', wc', .next) := (pure_guarded hp us w').trans hc'
    exact ⟨(csemG_lockstep2 hFZ hw hX hT hg hg').1, rfl, hw⟩
  · simp only [valueSemG, hp, Bool.false_eq_true, ite_false] at h h'
    exact csemG_lockstep2 hFZ hw hX hT h h'

end E2E
