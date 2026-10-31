import FV.E2E.PairDriver
import FV.E2E.GuardedFP

/-! # The guarded lockstep with the float accesses, on pairs of worlds (S11e5, Stage C slice 4)

`PairDriver` pairs the guarded runs of `csemG` (`guardedStep`, `guardedStep0`, `csemG_sub'`);
here the same for `csemGF`, the guarded semantics with the scalar float loads and stores
(`guardedStepF`, `guardedStep0F`, `csemGF_sub'`, from `csemGF_lockstep2` and `csemGF_sub`).

**The guarded simulation composition of a statement** (`lowerInstOk_pairF`): per-step contracts
at `csemGF` (`LowerInstOkP`, for every read guard and call pin) on each world give the step's
contract on pairs of worlds (`pairSem csem`, memory relation `MRP`), the per-step fact of the
non-interference driver (`vcode_ni`). The typed lowering (rules over `CtxInvT`, the float memory
roots `MemRulesCorrectRT` under `memRefinesFP_csemGF`) supplies such contracts; the integer
contracts at `csemG` lift to `csemGF` (`LowerInstOkP.sem_ext`, `csemG_csemGF`), so
`instCalls_pair` is an instance of the composition (`instCalls_pair_viaF`). -/

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver

/-! ## Contracts along an extension of the semantics -/

/-- A straight-line run of a semantics is a run of every extension of it. -/
theorem seqRun_ext {V W : Type} {sem sem' : ISem V W}
    (hsub : ∀ i us w r, sem i us w = some r → sem' i us w = some r) :
    ∀ (ms : List MInst) (ρ : Nat → V) (w : W) (e : SeqEnd V W),
      seqRun sem ms ρ w = some e → seqRun sem' ms ρ w = some e
  | [], _, _, _, h => h
  | i :: ms, ρ, w, e, h => by
    simp only [seqRun] at h ⊢
    cases hops : i.operands with
    | error => simp [hops] at h
    | ok ops =>
      simp only [hops] at h ⊢
      cases hs : sem i (vuses ops ρ) w with
      | none => simp [hs] at h
      | some r =>
        obtain ⟨outs, w', ctl⟩ := r
        rw [hs] at h
        rw [hsub _ _ _ _ hs]
        simp only at h ⊢
        by_cases hlen : outs.length = (ops.toList.filter Operand.isDef).length
        · rw [if_pos hlen] at h ⊢
          cases ctl with
          | next =>
            simp only [Option.map_eq_some_iff] at h ⊢
            obtain ⟨e1, h1, rfl⟩ := h
            exact ⟨e1, seqRun_ext hsub ms _ _ _ h1, rfl⟩
          | _ => exact h
        · rw [if_neg hlen] at h
          cases h

/-- **A statement contract holds for every extension of the semantics** (where the semantics is
defined, the extension is too, with its result). -/
theorem _root_.Backend.Proof.LowerInstOkP.sem_ext {Rd : BitVec 64 → Prop}
    {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop} {isem isem' : Sem}
    {MR : MemRelT} {env : Clif.Env} {p : Clif.Program} {ctx : Ctx} {inst : Clif.Inst}
    {results : List Nat} {st : LState} {rss : List (List Reg)} {st' : LState} {ms : List MInst}
    (hsub : ∀ i us w r, isem i us w = some r → isem' i us w = some r)
    (h : LowerInstOkP Rd Pc isem MR env p ctx inst results st rss st' ms) :
    LowerInstOkP Rd Pc isem' MR env p ctx inst results st rss st' ms := by
  refine ⟨h.mono, h.defs, fun fr cm ρ w hf hv hd hmr hi hpc => ?_⟩
  have r := h.run fr cm ρ w hf hv hd hmr hi hpc
  revert r
  rcases instOutcome env p fr cm inst with ⟨vals, cm'⟩ | c0 | m <;> intro r
  · obtain ⟨hU, ρ', w', hs, hres, hmr'⟩ := r
    exact ⟨hU, ρ', w', seqRun_ext hsub _ _ _ _ hs, hres, hmr'⟩
  · intro hex
    obtain ⟨hU, k, i, ops, ρ₁, w₁, outs, w₂, hs, htc⟩ := r hex
    exact ⟨hU, k, i, ops, ρ₁, w₁, outs, w₂, seqRun_ext hsub _ _ _ _ hs, htc⟩
  · trivial

section
variable {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
  {af : AFunc} {fa : FnAsm} {fb : FnBin} {X : ExtSem} {syms : String → Option Nat}
  {slotOff : Nat} {env : Clif.Env} {F : BitVec 64 → Prop} {c : BitVec 64} {D : BitVec 64 → Prop}

/-! ## The paired lockstep of the guarded runs with the float accesses -/

/-- The paired lockstep of the `csemGF` runs of one step (memory `cm`, pin `Pc`). -/
theorem guardedStepF
    (hNI : XNI F syms (f.externs.map (·.2)) (indSigs f) c
      (CallLg env (f.externs.map (·.2)) (indSigs f)) X)
    (hTls : XTls F X) (ctx : FnCtx) (inst : Clif.Inst) (fr : Clif.Frame) (cm : Clif.Mem)
    (ms : List MInst) :
    ∀ i ∈ ms, ∀ us w w' o w₁ ct o' w₁' ct', SameWorld (Zof F D cm) w w' →
      csemGF F ctx X (fun b => ¬ Zof F D cm b) syms (f.externs.map (·.2)) (indSigs f) c
        (StepPin env (f.externs.map (·.2)) (indSigs f) inst fr cm) i us w = some (o, w₁, ct) →
      csemGF F ctx X (fun b => ¬ Zof F D cm b) syms (f.externs.map (·.2)) (indSigs f) c
        (StepPin env (f.externs.map (·.2)) (indSigs f) inst fr cm) i us w' = some (o', w₁', ct') →
      o = o' ∧ ct = ct' ∧ SameWorld (Zof F D cm) w₁ w₁' := by
  intro i _ us w w' o w₁ ct o' w₁' ct' hw h h'
  have hFZ : ∀ a, F a → Zof F D cm a := fun a h => .inl h
  exact csemGF_lockstep2 hFZ hw (callLockstep hNI hFZ hw) (fun n => hTls _ n w w' hFZ hw) h h'

/-- The paired lockstep of `csemGF` runs without calls (the pin `False`). -/
theorem guardedStep0F (hTls : XTls F X) (ctx : FnCtx) (cm : Clif.Mem) (ms : List MInst)
    (exts : List Clif.ExtFunc) (sigs : List Clif.Signature) :
    ∀ i ∈ ms, ∀ us w w' o w₁ c o' w₁' c', SameWorld (Zof F D cm) w w' →
      csemGF F ctx X (fun b => ¬ Zof F D cm b) syms exts sigs 0 (fun _ _ _ _ => False) i us w =
        some (o, w₁, c) →
      csemGF F ctx X (fun b => ¬ Zof F D cm b) syms exts sigs 0 (fun _ _ _ _ => False) i us w' =
        some (o', w₁', c') →
      o = o' ∧ c = c' ∧ SameWorld (Zof F D cm) w₁ w₁' := by
  intro i _ us w w' o w₁ c o' w₁' c' hw h h'
  have hFZ : ∀ a, F a → Zof F D cm a := fun a h => .inl h
  refine csemGF_lockstep2 hFZ hw (fun dest h1 => ?_) (fun n => hTls _ n w w' hFZ hw) h h'
  obtain ⟨_, _, _, _, _, hf, _⟩ := h1
  exact hf.elim

theorem csemGF_sub' {ctx : FnCtx} {Rd : BitVec 64 → Prop} {exts : List Clif.ExtFunc}
    {sigs : List Clif.Signature} {sp0 : BitVec 64}
    {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop} :
    ∀ i us w r, csemGF F ctx X Rd syms exts sigs sp0 Pc i us w = some r → csem F ctx X i us w = some r :=
  fun _ _ _ _ h => csemGF_sub h

/-! ## The guarded simulation composition of a statement -/

/-- **The guarded simulation composition of one statement**, for a guarded semantics `semG`
(read guard `Rd`, call pin `Pc`) contained in `sem` (`hsub`) whose runs with `Rd := ¬ Zof F D cm`
and the step's pin go in lockstep (`hlock`): contracts of the step at `semG` on each world give
its contract on pairs of worlds that agree outside `Zof F D cm` — one paired run (`pairSem sem`),
memory relation `MRP`. -/
theorem lowerInstOk_pair_of {sem : Sem}
    {semG : (BitVec 64 → Prop) → (String → Clif.Signature → List Clif.Val → Clif.Mem → Prop) → Sem}
    (hsub : ∀ Rd Pc i us w r, semG Rd Pc i us w = some r → sem i us w = some r)
    {Γ : Rel} {ctx : Ctx} {inst : Clif.Inst} {results : List Nat}
    {st : LState} {rss : List (List Reg)} {st' : LState} {ms : List MInst}
    (hlock : ∀ (fr : Clif.Frame) (cm : Clif.Mem), ∀ i ∈ ms, ∀ us w w' o w₁ ct o' w₁' ct',
      SameWorld (Zof Γ.F D cm) w w' →
      semG (fun b => ¬ Zof Γ.F D cm b) (StepPin env (f.externs.map (·.2)) (indSigs f) inst fr cm)
        i us w = some (o, w₁, ct) →
      semG (fun b => ¬ Zof Γ.F D cm b) (StepPin env (f.externs.map (·.2)) (indSigs f) inst fr cm)
        i us w' = some (o', w₁', ct') →
      o = o' ∧ ct = ct' ∧ SameWorld (Zof Γ.F D cm) w₁ w₁')
    (hcf : ctx.func = f) (hsig : IndSigOk f (indSigs f) inst)
    (key : ∀ (Rd : BitVec 64 → Prop)
      (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop),
      LowerInstOkP Rd Pc (semG Rd Pc) (RelW Γ f c) env p ctx inst results st rss st' ms) :
    LowerInstOk (pairSem sem) (MRP Γ f c D) env p ctx inst results st rss st' ms := by
  have k0 := key (fun _ => True) (fun _ _ _ _ => True)
  refine ⟨k0.mono, k0.defs, fun fr cm ρ q hfr hvh hdfg hmr => ?_⟩
  obtain ⟨hm1, hm2, hsw⟩ := hmr
  have hff : fr.func = f := hfr.trans hcf
  have L := key (fun b => ¬ Zof Γ.F D cm b)
    (StepPin env (f.externs.map (·.2)) (indSigs f) inst fr cm)
  have hII : InitIn (fun b => ¬ Zof Γ.F D cm b) cm := initIn_zof hm1 D
  have hpin := callPin_stepPin (env := env) (cm := cm) hff hsig
  have r1 := L.run fr cm ρ q.1 hfr hvh hdfg hm1 hII hpin
  have r2 := L.run fr cm ρ q.2 hfr hvh hdfg hm2 hII hpin
  have hstep := hlock fr cm
  have hsub' := hsub (fun b => ¬ Zof Γ.F D cm b)
    (StepPin env (f.externs.map (·.2)) (indSigs f) inst fr cm)
  revert r1 r2
  rcases ho : instOutcome env p fr cm inst with ⟨vals, cm'⟩ | c0 | m <;> intro r1 r2
  · obtain ⟨hU, ρ1, w1, hs1, hres, hmr1⟩ := r1
    obtain ⟨-, ρ2, w2, hs2, -, hmr2⟩ := r2
    obtain ⟨w1', he, hp, hR⟩ := pair_fall (sem := sem) hsub' hstep (w := q.1) (w' := q.2) hsw hs1 hs2
    have hw : w2 = w1' := by injection he
    rw [← hw] at hp hR
    exact ⟨hU, ρ1, (w1, w2), hp, hres, hmr1, hmr2,
      sameWorld_zof hmr1.1.1 hmr2.1.1 hR (zof_sub cm)⟩
  · intro hex
    obtain ⟨hU, k1, i1, ops1, ρ1, wa, outs1, wb, hs1, htc⟩ := r1 hex
    obtain ⟨-, k2, i2, ops2, ρ2, wa', outs2, wb', hs2, -⟩ := r2 hex
    obtain ⟨w1', w2', he, hp, -, -⟩ := pair_stop (sem := sem) hsub' hstep (w := q.1) (w' := q.2)
      hsw hs1 hs2
    exact ⟨hU, k1, i1, ops1, ρ1, (wa, w1'), outs1, (wb, w2'), hp, htc⟩
  · trivial

/-- **The guarded simulation composition of one statement, with the float accesses**: contracts
of the step at `csemGF` on each world (for every read guard `Rd` and call pin `Pc`; the lowering
supplies them with `Rd := ¬ Zof F D cm` and `Pc` the step's pin) give its contract on pairs of
worlds that agree outside `Zof F D cm`: one paired run (`pairSem csem`), memory relation `MRP`. -/
theorem lowerInstOk_pairF
    (hNI : XNI F syms (f.externs.map (·.2)) (indSigs f) c
      (CallLg env (f.externs.map (·.2)) (indSigs f)) X) (hTls : XTls F X)
    {Γ : Rel} (hΓ : Γ.F = F) {ctx' : FnCtx} {ctx : Ctx} {inst : Clif.Inst} {results : List Nat}
    {st : LState} {rss : List (List Reg)} {st' : LState} {ms : List MInst}
    (hcf : ctx.func = f) (hsig : IndSigOk f (indSigs f) inst)
    (key : ∀ (Rd : BitVec 64 → Prop)
      (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop),
      LowerInstOkP Rd Pc (csemGF F ctx' X Rd syms (f.externs.map (·.2)) (indSigs f) c Pc)
        (RelW Γ f c) env p ctx inst results st rss st' ms) :
    LowerInstOk (pairSem (csem F ctx' X)) (MRP Γ f c D) env p ctx inst results st rss st' ms := by
  subst hΓ
  exact lowerInstOk_pair_of (fun _ _ _ _ _ _ h => csemGF_sub h)
    (fun fr cm => guardedStepF (D := D) hNI hTls ctx' inst fr cm ms) hcf hsig key

/-- **`instCalls_pair` through the composition with the float accesses**: the integer rule
contracts at `csemG` lift to `csemGF` (`LowerInstOkP.sem_ext`, `csemG_csemGF`), and
`lowerInstOk_pairF` pairs them — `instCalls_pair`'s statement, as an instance. -/
theorem instCalls_pair_viaF (hc : Compiled f k vc vcp rf af fa fb)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hNI : XNI F syms (f.externs.map (·.2)) (indSigs f) c
      (CallLg env (f.externs.map (·.2)) (indSigs f)) X) (hTls : XTls F X) :
    InstCalls f (pairSem (csem F ⟨fa.k, af.slotBase⟩ X))
      (MRP ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c D) env p := by
  intro ctx ii info inst st rss st' tr hctx hmem hE hi hcl hsig hemp hvb hrun
  let Γ : Rel := ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩
  have hstk := callsStack_mono (callsStack_of_check hc.lowerOk) (outgoing_le_intBase hc)
  have hIstk := indStack_mono (indStack_of_check hc.lowerOk) (outgoing_le_intBase hc)
  refine lowerInstOk_pairF hNI hTls (Γ := Γ) rfl hctx.func hsig fun Rd Pc => ?_
  obtain ⟨B, hB, stm, hstm, hst⟩ := hmem
  obtain ⟨ms, rss', hem, hov, hok⟩ := lowerInstOkP_runTerm lowerRulesCorrect_program
    excludedUnmatchable callRulesCorrectP indRulesCorrectP memRulesCorrectR_program
    refines_csemG (mrStable_relW Γ f c) (callsRefineP_csemG hX (fun _ _ _ h => h.1.1) (fun _ _ _ h => h.2.1))
    (indCallsRefineP_csemG hXI hsym (fun _ _ _ h => h.1.1) (fun _ _ _ h => h.2.1))
    (memRefinesR_csemG (ctx := ⟨fa.k, af.slotBase⟩) hslot hsym)
    hctx (outArgsOk_relW Γ f c) (externsIn_self f) hE (memRelOk_relW Γ f c) hi hcl hsig hIstk
    (fun fn args e hc' he => hstk B hB stm hstm fn args e (hst ▸ hc') he) hvb hrun
  cases hov
  rw [hemp, Array.empty_append] at hem
  rw [hem, List.toList_toArray]
  exact hok.sem_ext fun _ _ _ _ h => csemG_csemGF h

/-! ## The guarded simulation composition of a `try_call` -/

/-- **A `try_call` contract holds for every extension of the semantics.** -/
theorem _root_.Backend.Proof.LowerTryOkP.sem_ext {Rd : BitVec 64 → Prop}
    {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop} {isem isem' : Sem}
    {MR : MemRelT} {env : Clif.Env} {p : Clif.Program} {ctx : Ctx} {ci : Clif.Inst}
    {info : TryInfo} {st st' : LState} {ms : List MInst}
    (hsub : ∀ i us w r, isem i us w = some r → isem' i us w = some r)
    (h : LowerTryOkP Rd Pc isem MR env p ctx ci info st st' ms) :
    LowerTryOkP Rd Pc isem' MR env p ctx ci info st st' ms := by
  refine ⟨h.mono, h.shape, fun fr cm ρ w hf hv hd hmr hi hpc => ?_⟩
  have r := h.run fr cm ρ w hf hv hd hmr hi hpc
  revert r
  rcases instOutcome env p fr cm ci with ⟨rvals, cm'⟩ | c0 | m <;> intro r
  · obtain ⟨hU, k, i, ops, ρ₁, w₁, outs, w₂, hs, hk, hres, hmr'⟩ := r
    exact ⟨hU, k, i, ops, ρ₁, w₁, outs, w₂, seqRun_ext hsub _ _ _ _ hs, hk, hres, hmr'⟩
  · trivial
  · trivial

/-- **The guarded simulation composition of a `try_call`** (`lowerInstOk_pair_of` for the call
of a `try_call`/`try_call_indirect`, whose CLIF call `ci` the step's pin admits, `hpin`). -/
theorem lowerTryOk_pair_of {sem : Sem}
    {semG : (BitVec 64 → Prop) → (String → Clif.Signature → List Clif.Val → Clif.Mem → Prop) → Sem}
    (hsub : ∀ Rd Pc i us w r, semG Rd Pc i us w = some r → sem i us w = some r)
    {Γ : Rel} {ctx : Ctx} {ci : Clif.Inst} {info : TryInfo} {st st' : LState} {ms : List MInst}
    (hlock : ∀ (fr : Clif.Frame) (cm : Clif.Mem), ∀ i ∈ tryFix info ms, ∀ us w w' o w₁ ct o' w₁' ct',
      SameWorld (Zof Γ.F D cm) w w' →
      semG (fun b => ¬ Zof Γ.F D cm b) (StepPin env (f.externs.map (·.2)) (indSigs f) ci fr cm)
        i us w = some (o, w₁, ct) →
      semG (fun b => ¬ Zof Γ.F D cm b) (StepPin env (f.externs.map (·.2)) (indSigs f) ci fr cm)
        i us w' = some (o', w₁', ct') →
      o = o' ∧ ct = ct' ∧ SameWorld (Zof Γ.F D cm) w₁ w₁')
    (hpin : ∀ (fr : Clif.Frame) (cm : Clif.Mem), fr.func = ctx.func →
      CallPin (StepPin env (f.externs.map (·.2)) (indSigs f) ci fr cm) env ci fr cm)
    (key : ∀ (Rd : BitVec 64 → Prop)
      (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop),
      LowerTryOkP Rd Pc (semG Rd Pc) (RelW Γ f c) env p ctx ci info st st' ms) :
    LowerTryOk (pairSem sem) (MRP Γ f c D) env p ctx ci info st st' ms := by
  have k0 := key (fun _ => True) (fun _ _ _ _ => True)
  refine ⟨k0.mono, k0.shape, fun fr cm ρ q hfr hvh hdfg hmr => ?_⟩
  obtain ⟨hm1, hm2, hsw⟩ := hmr
  have L := key (fun b => ¬ Zof Γ.F D cm b)
    (StepPin env (f.externs.map (·.2)) (indSigs f) ci fr cm)
  have hII : InitIn (fun b => ¬ Zof Γ.F D cm b) cm := initIn_zof hm1 D
  have r1 := L.run fr cm ρ q.1 hfr hvh hdfg hm1 hII (hpin fr cm hfr)
  have r2 := L.run fr cm ρ q.2 hfr hvh hdfg hm2 hII (hpin fr cm hfr)
  have hstep := hlock fr cm
  have hsub' := hsub (fun b => ¬ Zof Γ.F D cm b)
    (StepPin env (f.externs.map (·.2)) (indSigs f) ci fr cm)
  revert r1 r2
  rcases ho : instOutcome env p fr cm ci with ⟨vals, cm'⟩ | c0 | m <;> intro r1 r2
  · obtain ⟨hU, k1, i1, ops1, ρ1, wa, outs1, wb, hs1, hk, hres, hmr1⟩ := r1
    obtain ⟨-, k2, i2, ops2, ρ2, wa', outs2, wb', hs2, -, -, hmr2⟩ := r2
    obtain ⟨w1', w2', he, hp, hR1, hR⟩ := pair_stop (sem := sem) hsub' hstep
      (w := q.1) (w' := q.2) hsw hs1 hs2
    injection he with _ _ _ _ hwa _ hwb
    rw [← hwa, ← hwb] at hp
    rw [← hwb] at hR
    exact ⟨hU, k1, i1, ops1, ρ1, (wa, wa'), outs1, (wb, wb'), hp, hk, hres, hmr1, hmr2,
      sameWorld_zof hmr1.1.1 hmr2.1.1 hR (zof_sub cm)⟩
  · trivial
  · trivial

/-- **The guarded simulation composition of a `try_call`, with the float accesses** (contracts
at `csemGF`). -/
theorem lowerTryOk_pairF
    (hNI : XNI F syms (f.externs.map (·.2)) (indSigs f) c
      (CallLg env (f.externs.map (·.2)) (indSigs f)) X) (hTls : XTls F X)
    {Γ : Rel} (hΓ : Γ.F = F) {ctx' : FnCtx} {ctx : Ctx} {ci : Clif.Inst} {info : TryInfo}
    {st st' : LState} {ms : List MInst}
    (hpin : ∀ (fr : Clif.Frame) (cm : Clif.Mem), fr.func = ctx.func →
      CallPin (StepPin env (f.externs.map (·.2)) (indSigs f) ci fr cm) env ci fr cm)
    (key : ∀ (Rd : BitVec 64 → Prop)
      (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop),
      LowerTryOkP Rd Pc (csemGF F ctx' X Rd syms (f.externs.map (·.2)) (indSigs f) c Pc)
        (RelW Γ f c) env p ctx ci info st st' ms) :
    LowerTryOk (pairSem (csem F ctx' X)) (MRP Γ f c D) env p ctx ci info st st' ms := by
  subst hΓ
  exact lowerTryOk_pair_of (fun _ _ _ _ _ _ h => csemGF_sub h)
    (fun fr cm => guardedStepF (D := D) hNI hTls ctx' ci fr cm (tryFix info ms)) hpin key

/-- **`tryCalls_pair` through the composition with the float accesses** (`tryCalls_pair`'s
statement, as an instance of `lowerTryOk_pairF`). -/
theorem tryCalls_pair_viaF (_hc : Compiled f k vc vcp rf af fa fb)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hNI : XNI F syms (f.externs.map (·.2)) (indSigs f) c
      (CallLg env (f.externs.map (·.2)) (indSigs f)) X) (hTls : XTls F X) :
    TryCalls f (pairSem (csem F ⟨fa.k, af.slotBase⟩ X))
      (MRP ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c D) env p
      (RAFrame.compute vcp rf).intBase := by
  intro ctx ti fn args et data sig items targets info trs lo st1 out st' tr hctx hra hd he hph
    hinfo hregs hvb hrun
  let Γ : Rel := ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩
  have hctx' := ctxInv_tryRegs (ctxInv_termCtx hctx hph data) trs
  have hi : (tryCtx ctx ti data trs).insts[ti]? = some ⟨data, [], [], none⟩ :=
    termCtx_insts_self hph data
  have hregs' : tryRegsOf sig lo = some ((tryCtx ctx ti data trs).tryRegs, st1) := hregs
  have hvb' : ValsBelow (tryCtx ctx ti data trs) lo := hvb
  refine lowerTryOk_pairF hNI hTls (Γ := Γ) rfl
    (fun fr cm hfr => callPin_stepPin (env := env) (cm := cm) (inst := .call fn args)
      (hfr.trans hctx'.func) (fun _ _ _ _ h => by cases h)) fun Rd Pc => ?_
  obtain ⟨ms, hem, hok⟩ := tryOkP_runTerm tryRulesCorrectP tryUnmatchable refines_csemG
    (mrStable_relW Γ f c) (memRefinesR_csemG (ctx := ⟨fa.k, af.slotBase⟩) hslot hsym)
    (outArgsOk_relW Γ f c)
    (callsRefineP_csemG hX (fun _ _ _ h => h.1.1) (fun _ _ _ h => h.2.1)) hctx' (externsIn_self f)
    hra hd he hi hinfo hregs' hvb' (st := { st1 with emitted := #[] }) (Nat.le_refl _) hrun
  have : ms = st'.emitted.toList := by
    simp only [Array.empty_append] at hem; rw [hem, List.toList_toArray]
  rw [← this]
  exact hok.sem_ext fun _ _ _ _ h => csemG_csemGF h

/-- **`tryIndCalls_pair` through the composition with the float accesses**
(`tryIndCalls_pair`'s statement, as an instance of `lowerTryOk_pairF`). -/
theorem tryIndCalls_pair_viaF (hc : Compiled f k vc vcp rf af fa fb)
    (hXI : XCallsIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hNI : XNI F syms (f.externs.map (·.2)) (indSigs f) c
      (CallLg env (f.externs.map (·.2)) (indSigs f)) X) (hTls : XTls F X) :
    TryIndCalls (pairSem (csem F ⟨fa.k, af.slotBase⟩ X))
      (MRP ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c D) env p (indSigs f) := by
  intro g ctx ti callee args et data sig items targets info trs lo st1 out st' tr hctx hd he hsig
    hph hinfo hregs hvb hrun
  let Γ : Rel := ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩
  have hctx' := ctxInv_tryRegs (ctxInv_termCtx hctx hph data) trs
  have hi : (tryCtx ctx ti data trs).insts[ti]? = some ⟨data, [], [], none⟩ :=
    termCtx_insts_self hph data
  have hregs' : tryRegsOf sig lo = some ((tryCtx ctx ti data trs).tryRegs, st1) := hregs
  have hvb' : ValsBelow (tryCtx ctx ti data trs) lo := hvb
  have hsd := exnTableOpnd_sig he
  refine lowerTryOk_pairF hNI hTls (Γ := Γ) rfl (fun fr cm hfr => ?_) fun Rd Pc => ?_
  · have hfg : fr.func = g := hfr.trans hctx'.func
    refine ⟨(fun _ _ _ _ _ _ _ h => by cases h), fun sg cl ar s x vals n gg rvals cm' hi' hs hc' hv
      hsy hg hgo hty => ?_⟩
    cases hi'
    rw [hfg, hsd] at hs
    cases hs
    exact ⟨rfl, ⟨.inr ⟨hsig, hty⟩, gg, rvals, cm', hg, hgo⟩, .inr ⟨_, _, _, rfl, hfg ▸ hsd, hv⟩⟩
  · obtain ⟨ms, hem, hok⟩ := tryIndOkP_runTerm tryIndRulesCorrectP tryIndUnmatchable
      refines_csemG (mrStable_relW Γ f c)
      (memRefinesR_csemG (ctx := ⟨fa.k, af.slotBase⟩) rfl hsym) (outArgsOk_relW Γ f c)
      (indStack_mono (indStack_of_check hc.lowerOk) (outgoing_le_intBase hc))
      (indCallsRefineP_csemG hXI hsym (fun _ _ _ h => h.1.1) (fun _ _ _ h => h.2.1))
      hctx' hd he hsig hi hinfo hregs' hvb' (st := { st1 with emitted := #[] })
      (Nat.le_refl _) hrun
    have : ms = st'.emitted.toList := by
      simp only [Array.empty_append] at hem; rw [hem, List.toList_toArray]
    rw [← this]
    exact hok.sem_ext fun _ _ _ _ h => csemG_csemGF h

end

end E2E
