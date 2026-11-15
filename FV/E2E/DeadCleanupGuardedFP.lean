import FV.E2E.DeadCleanupFinal
import FV.E2E.DeadCleanupGuarded
import FV.E2E.GuardedFPPair

/-! # The guarded value semantics with the float accesses (S11e5, Stage C slice 4)

The shipped (dead-cleanup) route runs the non-interference driver on `valueSem` (pure producers
by their specification), guarded as `valueSemG`. `valueSemGF` is `valueSemG` with `csemGF` for
the non-pure forms (the scalar float loads and stores added): a sub-semantics of `valueSem`
(`valueSemGF_sub`) extending `valueSemG` (`valueSemG_valueSemGF`), with the rule premises
(`refines_valueSemGF`, `memRefinesR_valueSemGF`, `memRefinesFP_valueSemGF`,
`callsRefineP_valueSemGF`, `indCallsRefineP_valueSemGF`) and the lockstep
(`valueSemGF_lockstep2`), paired per step (`guardedStepF_value`, `guardedStep0F_value`) and
composed per statement (`lowerInstOk_pairF_value`); `instCalls_pair_value` is an instance
(`instCalls_pair_value_viaF`). -/

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

/-- The guarded value semantics with the float accesses: pure producers and compares by their
specification, every other form by `csemGF`. -/
noncomputable def valueSemGF (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem)
    (Rd : BitVec 64 → Prop) (syms : String → Option Nat) (exts : List Clif.ExtFunc)
    (sigs : List Clif.Signature) (sp0 : BitVec 64)
    (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop) : Sem :=
  fun i us w => if specForm i then mspec ctx.slotBase i us w
    else csemGF F ctx X Rd syms exts sigs sp0 Pc i us w

section
variable {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {Rd : BitVec 64 → Prop}
  {syms : String → Option Nat} {exts : List Clif.ExtFunc} {sigs : List Clif.Signature}
  {sp0 : BitVec 64}
  {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop}

/-- **`valueSemGF` is a sub-semantics of `valueSem`.** -/
theorem valueSemGF_sub {i : MInst} {us : List CV} {w : Arm.ArmState}
    {r : List CV × Arm.ArmState × Ctl}
    (h : valueSemGF F ctx X Rd syms exts sigs sp0 Pc i us w = some r) :
    valueSem F ctx X i us w = some r := by
  by_cases hp : specForm i = true
  · simpa [valueSemGF, valueSem, hp] using h
  · simp only [valueSemGF, hp, Bool.false_eq_true, ite_false] at h
    simpa [valueSem, hp] using csemGF_sub h

/-- **`valueSemGF` extends `valueSemG`.** -/
theorem valueSemG_valueSemGF {i : MInst} {us : List CV} {w : Arm.ArmState}
    {r : List CV × Arm.ArmState × Ctl}
    (h : valueSemG F ctx X Rd syms exts sigs sp0 Pc i us w = some r) :
    valueSemGF F ctx X Rd syms exts sigs sp0 Pc i us w = some r := by
  by_cases hp : specForm i = true
  · simpa [valueSemGF, valueSemG, hp] using h
  · simp only [valueSemG, hp, Bool.false_eq_true, ite_false] at h
    simp only [valueSemGF, hp, Bool.false_eq_true, ite_false]
    exact csemG_csemGF h

theorem refines_valueSemGF : Refines F (valueSemGF F ctx X Rd syms exts sigs sp0 Pc) := by
  intro i us w outs w' ctl h
  obtain ⟨w₁, h1, h2⟩ := refines_valueSemG (F := F) (ctx := ctx) (X := X) (Rd := Rd)
    (syms := syms) (exts := exts) (sigs := sigs) (sp0 := sp0) (Pc := Pc) i us w outs w' h
  exact ⟨w₁, valueSemG_valueSemGF h1, h2⟩

/-- The guarded value semantics with the float accesses lets the next compare overwrite a
compare's flags. -/
theorem valueSemGF_cmpOverwrite (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem)
    (Rd : BitVec 64 → Prop) (syms : String → Option Nat) (exts : List Clif.ExtFunc)
    (sigs : List Clif.Signature) (sp0 : BitVec 64)
    (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop) :
    CmpOverwrite (valueSemGF F ctx X Rd syms exts sigs sp0 Pc) :=
  cmpOverwrite_of_mspec (sb := ctx.slotBase)
    (fun i hs => by funext us w; simp only [valueSemGF, hs, ↓reduceIte])
    (jumpPlain_of_csem (F := F) (ctx := ctx) (X := X) fun l => by
      funext us w; simp [valueSemGF, csemGF, csemG, GuardR, GuardC, specForm, pureForm, cmpForm])

theorem memRefinesR_valueSemGF {sb : Nat} (hsb : ctx.slotBase = sb)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b) :
    MemRefinesR Rd F sb syms (valueSemGF F ctx X Rd syms exts sigs sp0 Pc) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
    memRefinesR_valueSemG (F := F) (ctx := ctx) (X := X) (Rd := Rd) (exts := exts)
      (sigs := sigs) (sp0 := sp0) (Pc := Pc) hsb hsym
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem memRefinesFP_valueSemGF {sb : Nat} (hsb : ctx.slotBase = sb) :
    MemRefinesFP Rd F sb (valueSemGF F ctx X Rd syms exts sigs sp0 Pc) := by
  obtain ⟨h1, h2⟩ := memRefinesFP_csemGF (F := F) (ctx := ctx) (X := X) (Rd := Rd)
    (syms := syms) (exts := exts) (sigs := sigs) (sp0 := sp0) (Pc := Pc) hsb
  exact ⟨h1, h2⟩

theorem callsRefineP_valueSemGF {env : Clif.Env} {MR : MemRelT}
    (hX : XCallsOk env exts MR X) (hMRm : ∀ sl cm w, MR sl cm w → MemRel F syms cm w)
    (hMRc : ∀ sl cm w, MR sl cm w → spv w = sp0) :
    CallsRefineP Pc F env exts MR (valueSemGF F ctx X Rd syms exts sigs sp0 Pc) := by
  obtain ⟨sym, h1, h2, h3⟩ := callsRefineP_valueSemG (ctx := ctx) (Rd := Rd) (sigs := sigs)
    (Pc := Pc) hX hMRm hMRc
  exact ⟨sym, h1, h2, h3⟩

theorem indCallsRefineP_valueSemGF {env : Clif.Env} {MR : MemRelT}
    (hX : XCallsIndOk env sigs MR X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hMRm : ∀ sl cm w, MR sl cm w → MemRel F syms cm w)
    (hMRc : ∀ sl cm w, MR sl cm w → spv w = sp0) :
    IndCallsRefineP Pc env sigs MR (valueSemGF F ctx X Rd syms exts sigs sp0 Pc) := by
  obtain ⟨h1, h2⟩ := indCallsRefineP_valueSemG (ctx := ctx) (Rd := Rd) (exts := exts) (Pc := Pc)
    hX hsym hMRm hMRc
  exact ⟨h1, h2⟩

/-- **Two guarded value runs of one instruction with the float accesses, in lockstep.** -/
theorem valueSemGF_lockstep2 {Z : BitVec 64 → Prop} (hFZ : ∀ a, F a → Z a) {i : MInst}
    {us : List CV} {w w' : Arm.ArmState} (hw : SameWorld Z w w')
    (hX : ∀ dest, CallG F syms X exts sigs sp0 Pc dest us w → CallG F syms X exts sigs sp0 Pc dest us w' →
      ∀ o x o' x', X.call (destName dest) us w = some (o, x) →
        X.call (destName dest) us w' = some (o', x') → o = o' ∧ SameWorld Z x x')
    (hT : ∀ n, X.tlsFlags n w = X.tlsFlags n w')
    {o o' : List CV} {w₁ w₁' : Arm.ArmState} {c c' : Ctl}
    (h : valueSemGF F ctx X (fun b => ¬ Z b) syms exts sigs sp0 Pc i us w = some (o, w₁, c))
    (h' : valueSemGF F ctx X (fun b => ¬ Z b) syms exts sigs sp0 Pc i us w' = some (o', w₁', c')) :
    o = o' ∧ c = c' ∧ SameWorld Z w₁ w₁' := by
  by_cases hp : specForm i = true
  · have e : ∀ x, valueSemGF F ctx X (fun b => ¬ Z b) syms exts sigs sp0 Pc i us x =
        valueSemG F ctx X (fun b => ¬ Z b) syms exts sigs sp0 Pc i us x := fun x => by
      simp [valueSemGF, valueSemG, hp]
    rw [e] at h h'
    exact valueSemG_lockstep2 hFZ hw hX hT h h'
  · simp only [valueSemGF, hp, Bool.false_eq_true, ite_false] at h h'
    exact csemGF_lockstep2 hFZ hw hX hT h h'

end

section
variable {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
  {af : AFunc} {fa : FnAsm} {fb : FnBin} {X : ExtSem} {syms : String → Option Nat}
  {slotOff : Nat} {env : Clif.Env} {F : BitVec 64 → Prop} {c : BitVec 64} {D : BitVec 64 → Prop}

/-- The paired lockstep of the `valueSemGF` runs of one step (memory `cm`, pin `Pc`). -/
theorem guardedStepF_value
    (hNI : XNI F syms (f.externs.map (·.2)) (indSigs f) c
      (CallLg env (f.externs.map (·.2)) (indSigs f)) X)
    (hTls : XTls F X) (ctx : FnCtx) (inst : Clif.Inst) (fr : Clif.Frame) (cm : Clif.Mem)
    (ms : List MInst) :
    ∀ i ∈ ms, ∀ us w w' o w₁ ct o' w₁' ct', SameWorld (Zof F D cm) w w' →
      valueSemGF F ctx X (fun b => ¬ Zof F D cm b) syms (f.externs.map (·.2)) (indSigs f) c
        (StepPin env (f.externs.map (·.2)) (indSigs f) inst fr cm) i us w = some (o, w₁, ct) →
      valueSemGF F ctx X (fun b => ¬ Zof F D cm b) syms (f.externs.map (·.2)) (indSigs f) c
        (StepPin env (f.externs.map (·.2)) (indSigs f) inst fr cm) i us w' = some (o', w₁', ct') →
      o = o' ∧ ct = ct' ∧ SameWorld (Zof F D cm) w₁ w₁' := by
  intro i _ us w w' o w₁ ct o' w₁' ct' hw h h'
  have hFZ : ∀ a, F a → Zof F D cm a := fun a h => .inl h
  exact valueSemGF_lockstep2 hFZ hw (callLockstep hNI hFZ hw) (fun n => hTls _ n w w' hFZ hw) h h'

/-- The paired lockstep of `valueSemGF` runs without calls (the pin `False`). -/
theorem guardedStep0F_value (hTls : XTls F X) (ctx : FnCtx) (cm : Clif.Mem) (ms : List MInst)
    (exts : List Clif.ExtFunc) (sigs : List Clif.Signature) :
    ∀ i ∈ ms, ∀ us w w' o w₁ c o' w₁' c', SameWorld (Zof F D cm) w w' →
      valueSemGF F ctx X (fun b => ¬ Zof F D cm b) syms exts sigs 0 (fun _ _ _ _ => False) i us w =
        some (o, w₁, c) →
      valueSemGF F ctx X (fun b => ¬ Zof F D cm b) syms exts sigs 0 (fun _ _ _ _ => False) i us w' =
        some (o', w₁', c') →
      o = o' ∧ c = c' ∧ SameWorld (Zof F D cm) w₁ w₁' := by
  intro i _ us w w' o w₁ c o' w₁' c' hw h h'
  have hFZ : ∀ a, F a → Zof F D cm a := fun a h => .inl h
  refine valueSemGF_lockstep2 hFZ hw (fun dest h1 => ?_) (fun n => hTls _ n w w' hFZ hw) h h'
  obtain ⟨_, _, _, _, _, hf, _⟩ := h1
  exact hf.elim

/-- **The guarded simulation composition of one statement on the value semantics, with the
float accesses** (`lowerInstOk_pairF` for `valueSem`). -/
theorem lowerInstOk_pairF_value
    (hNI : XNI F syms (f.externs.map (·.2)) (indSigs f) c
      (CallLg env (f.externs.map (·.2)) (indSigs f)) X) (hTls : XTls F X)
    {Γ : Rel} (hΓ : Γ.F = F) {ctx' : FnCtx} {ctx : Ctx} {inst : Clif.Inst} {results : List Nat}
    {st : LState} {rss : List (List Reg)} {st' : LState} {ms : List MInst}
    (hcf : ctx.func = f) (hsig : IndSigOk f (indSigs f) inst)
    (key : ∀ (Rd : BitVec 64 → Prop)
      (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop),
      LowerInstOkP Rd Pc (valueSemGF F ctx' X Rd syms (f.externs.map (·.2)) (indSigs f) c Pc)
        (RelW Γ f c) env p ctx inst results st rss st' ms) :
    LowerInstOk (pairSem (valueSem F ctx' X)) (MRP Γ f c D) env p ctx inst results st rss st' ms := by
  subst hΓ
  exact lowerInstOk_pair_of (fun _ _ _ _ _ _ h => valueSemGF_sub h)
    (fun fr cm => guardedStepF_value (D := D) hNI hTls ctx' inst fr cm ms) hcf hsig key

/-- **`instCalls_pair_value` through the composition with the float accesses**
(`instCalls_pair_value`'s statement, as an instance of `lowerInstOk_pairF_value`). -/
theorem instCalls_pair_value_viaF (hc : CompiledCleanup f k vc vcp rf af fa fb)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hNI : XNI F syms (f.externs.map (·.2)) (indSigs f) c
      (CallLg env (f.externs.map (·.2)) (indSigs f)) X) (hTls : XTls F X) :
    InstCalls f (pairSem (valueSem F ⟨fa.k, af.slotBase⟩ X))
      (MRP ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c D) env p := by
  intro ctx ii info inst st rss st' tr hctx hmem hE hi hcl hsig hemp hvb hrun
  let Γ : Rel := ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩
  have hstk := callsStack_mono (callsStack_of_check hc.lowerOk) (outgoing_le_intBaseCleanupA hc.toA)
  have hIstk := indStack_mono (indStack_of_check hc.lowerOk) (outgoing_le_intBaseCleanupA hc.toA)
  refine lowerInstOk_pairF_value hNI hTls (Γ := Γ) rfl hctx.func hsig fun Rd Pc => ?_
  obtain ⟨B, hB, stm, hstm, hst⟩ := hmem
  obtain ⟨ms, rss', hem, hov, hok⟩ := lowerInstOkP_runTerm lowerRulesCorrect_program
    excludedUnmatchable callRulesCorrectP indRulesCorrectP memRulesCorrectR_program
    refines_valueSemG (mrStable_relW Γ f c)
    (callsRefineP_valueSemG hX (fun _ _ _ h => h.1.1) (fun _ _ _ h => h.2.1))
    (indCallsRefineP_valueSemG hXI hsym (fun _ _ _ h => h.1.1) (fun _ _ _ h => h.2.1))
    (memRefinesR_valueSemG (ctx := ⟨fa.k, af.slotBase⟩) hslot hsym)
    hctx (outArgsOk_relW Γ f c) (externsIn_self f) hE (memRelOk_relW Γ f c) hi hcl hsig hIstk
    (fun fn args e hc' he => hstk B hB stm hstm fn args e (hst ▸ hc') he) hvb hrun
  cases hov
  rw [hemp, Array.empty_append] at hem
  rw [hem, List.toList_toArray]
  exact hok.sem_ext fun _ _ _ _ h => valueSemG_valueSemGF h

end

end E2E
