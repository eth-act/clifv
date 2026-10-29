module

public import FV.E2E.PairDriver
public import FV.E2E.GuardedFP
public import FV.E2E.DeadCleanupGuardedFP
public import FV.Backend.Proof.IselCtlTryF
public import FV.Backend.Proof.LowerContractTC
public import FV.Backend.Proof.DeadCleanupAdapter

@[expose] public section

/-! # The guarded lockstep with the float accesses, on pairs of worlds, typed try_calls

`GuardedFPPair.lean` for the scope with typed direct `try_call`s: the guarded runs of
`csemGF` (`guardedStepF`, `csemGF_sub`) paired into `pairSem csem` on pairs of worlds
(`lowerInstOk_pairF`); the guarded simulation composition of a `try_call`
(`lowerTryOkC_pair_of`, `lowerTryOkC_pairF`) from the typed contracts `LowerTryOkPC` (for any
read guard and call pin), and the value-semantics copy `lowerTryOkC_pairF_value`.
-/

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

section
variable {p : Clif.Program} {f : Clif.Function} {X : ExtSem} {syms : String → Option Nat}
  {env : Clif.Env} {F : BitVec 64 → Prop} {c : BitVec 64} {D : BitVec 64 → Prop}

/-- **The guarded simulation composition of a `try_call` contract** (`LowerTryOkPC` for any
extension of the semantics). -/
theorem _root_.Backend.Proof.LowerTryOkPC.sem_ext {Rd : BitVec 64 → Prop}
    {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop} {isem isem' : Sem}
    {MR : MemRelT} {env : Clif.Env} {p : Clif.Program} {ctx : Ctx} {ci : Clif.Inst}
    {info : TryInfo} {st st' : LState} {ms : List MInst}
    (hsub : ∀ i us w r, isem i us w = some r → isem' i us w = some r)
    (h : LowerTryOkPC Rd Pc isem MR env p ctx ci info st st' ms) :
    LowerTryOkPC Rd Pc isem' MR env p ctx ci info st st' ms := by
  refine ⟨h.mono, h.shape, fun fr cm ρ w hf hv hd hmr hII hpc => ?_⟩
  have r := h.run fr cm ρ w hf hv hd hmr hII hpc
  revert r
  rcases instOutcome env p fr cm ci with ⟨rvals, cm'⟩ | c0 | m <;> intro r
  · obtain ⟨hU, k, i, ops, ρ₁, w₁, outs, w₂, hs, hk, hres, hmr'⟩ := r
    exact ⟨hU, k, i, ops, ρ₁, w₁, outs, w₂, seqRun_ext hsub _ _ _ _ hs, hk, hres, hmr'⟩
  · trivial
  · trivial

/-- **The guarded simulation composition of a `try_call`** (`lowerInstOk_pair_of` for the call
of a `try_call`/`try_call_indirect`, whose CLIF call `ci` the step's pin admits, `hpin`): the
typed contracts at `csemGF` on each world give the typed contract on pairs of worlds
(`LowerTryOkC` of `pairSem csem`, memory relation `MRP`). -/
theorem lowerTryOkC_pair_of {sem : Sem}
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
      LowerTryOkPC Rd Pc (semG Rd Pc) (RelW Γ f c) env p ctx ci info st st' ms) :
    LowerTryOkC (pairSem sem) (MRP Γ f c D) env p ctx ci info st st' ms := by
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

/-- **The guarded simulation composition of a `try_call` with the float accesses** (contracts
at `csemGF`). -/
theorem lowerTryOkC_pairF
    (hNI : XNI F syms (f.externs.map (·.2)) (indSigs f) c
      (CallLg env (f.externs.map (·.2)) (indSigs f)) X) (hTls : XTls F X)
    {Γ : Rel} (hΓ : Γ.F = F) {ctx' : FnCtx} {ctx : Ctx} {ci : Clif.Inst} {info : TryInfo}
    {st st' : LState} {ms : List MInst}
    (hpin : ∀ (fr : Clif.Frame) (cm : Clif.Mem), fr.func = ctx.func →
      CallPin (StepPin env (f.externs.map (·.2)) (indSigs f) ci fr cm) env ci fr cm)
    (key : ∀ (Rd : BitVec 64 → Prop)
      (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop),
      LowerTryOkPC Rd Pc (csemGF F ctx' X Rd syms (f.externs.map (·.2)) (indSigs f) c Pc)
        (RelW Γ f c) env p ctx ci info st st' ms) :
    LowerTryOkC (pairSem (csem F ctx' X)) (MRP Γ f c D) env p ctx ci info st st' ms := by
  subst hΓ
  exact lowerTryOkC_pair_of (fun _ _ _ _ _ _ h => csemGF_sub h)
    (fun fr cm => guardedStepF (D := D) hNI hTls ctx' ci fr cm (tryFix info ms)) hpin key

/-- **The guarded simulation composition of a `try_call`, value semantics with the float
accesses** (`lowerTryOk_pairF` at `valueSemGF`). -/
theorem lowerTryOkC_pairF_value
    (hNI : XNI F syms (f.externs.map (·.2)) (indSigs f) c
      (CallLg env (f.externs.map (·.2)) (indSigs f)) X) (hTls : XTls F X)
    {Γ : Rel} (hΓ : Γ.F = F) {ctx' : FnCtx} {ctx : Ctx} {ci : Clif.Inst} {info : TryInfo}
    {st st' : LState} {ms : List MInst}
    (hpin : ∀ (fr : Clif.Frame) (cm : Clif.Mem), fr.func = ctx.func →
      CallPin (StepPin env (f.externs.map (·.2)) (indSigs f) ci fr cm) env ci fr cm)
    (key : ∀ (Rd : BitVec 64 → Prop)
      (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop),
      LowerTryOkPC Rd Pc (valueSemGF F ctx' X Rd syms (f.externs.map (·.2)) (indSigs f) c Pc)
        (RelW Γ f c) env p ctx ci info st st' ms) :
    LowerTryOkC (pairSem (valueSem F ctx' X)) (MRP Γ f c D) env p ctx ci info st st' ms := by
  subst hΓ
  exact lowerTryOkC_pair_of (fun _ _ _ _ _ _ h => valueSemGF_sub h)
    (fun fr cm => guardedStepF_value (D := D) hNI hTls ctx' ci fr cm (tryFix info ms)) hpin key

end

end E2E
