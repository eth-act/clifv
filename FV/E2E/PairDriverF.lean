import FV.E2E.PairDriver

/-!
# Non-interference of the external semantics at the exterior only (SEM1 #537, #713)

`XNI F …` (`PairDriver.lean`) asks the external semantics to keep two worlds agreeing outside
**every** set `Z ⊇ F`. At the link a program call is answered by the canonical callee run, so
`XNI` there is the callee's determinism with the world difference `Z`; for `Z ⊄ F` the callee's base
calls may read the differing bytes, and the trusted base-hook premise (`HookNIX`, `OkDNX`) covers
the exterior `F` only. The paired driver needs `XNI` only at the set `Zof F D cm` of its step, which
is `F` when the world difference `D` lies inside `F` (`DetPRBR`'s premise `∀ a, D a → F a`). So:

* **`XNIF`**: `XNI` at the one set `F`; `XNI.xnif`;
* `zof_iff_of_sub`, `sameWorld_zof_iff` (with `D ⊆ F`, `Zof F D cm` is `F`);
* **`callLockstepF`** (`callLockstep` from `XNIF` at any set equivalent to `F`);
* **`guardedStepF`** (`guardedStep` from `XNIF` and `D ⊆ F`).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- **Non-interference of the external semantics at the exterior `F` only** (module doc): `XNI`
with the difference set `Z` fixed to `F`. -/
def XNIF (F : BitVec 64 → Prop) (syms : String → Option Nat) (exts : List Clif.ExtFunc)
    (sigs : List Clif.Signature) (sp0 : BitVec 64)
    (Lg : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop) (X : ExtSem) : Prop :=
  ∀ (n : String) (sig : Clif.Signature) (vals : List Clif.Val) (cm : Clif.Mem) (args : List CV)
    (d : Option String) (uses : List CV) (w w' : Arm.ArmState)
    (o : List CV) (x : Arm.ArmState) (o' : List CV) (x' : Arm.ArmState),
    Lg n sig vals cm →
    (d = some n ∧ uses = args ∨ d = none ∧ ∃ u, uses = u :: args ∧ lo64 u = X.sym n 0) →
    SameWorld F w w' → MemRel F syms cm w → MemRel F syms cm w' →
    spv w = sp0 → spv w' = sp0 →
    ((∃ e ∈ exts, e.name = n ∧ e.sig = sig) ∧ ArgsAt sig vals args w ∧ ArgsAt sig vals args w' ∨
      sig ∈ sigs ∧ ArgsAt sig vals args w ∧ ArgsAt sig vals args w') →
    X.call d uses w = some (o, x) → X.call d uses w' = some (o', x') → o = o' ∧ SameWorld F x x'

/-- **`XNI` gives `XNIF`** (the set `F` itself). -/
theorem XNI.xnif {F : BitVec 64 → Prop} {syms : String → Option Nat} {exts : List Clif.ExtFunc}
    {sigs : List Clif.Signature} {sp0 : BitVec 64}
    {Lg : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop} {X : ExtSem}
    (h : XNI F syms exts sigs sp0 Lg X) : XNIF F syms exts sigs sp0 Lg X :=
  fun n sig vals cm args d uses w w' o x o' x' hlg hd hsw hm hm' h1 h2 hA hx hx' =>
    h n sig vals cm args d uses F w w' o x o' x' hlg hd (fun _ h => h) hsw hm hm' h1 h2 hA hx hx'

/-- With the world difference inside `F`, the step's difference set is `F`. -/
theorem zof_iff_of_sub {F D : BitVec 64 → Prop} (hD : ∀ a, D a → F a) (cm : Clif.Mem)
    (a : BitVec 64) : Zof F D cm a ↔ F a :=
  ⟨fun h => h.elim id fun h => hD a h.1, .inl⟩

theorem sameWorld_zof_iff {F D : BitVec 64 → Prop} (hD : ∀ a, D a → F a) (cm : Clif.Mem)
    {w w' : Arm.ArmState} : SameWorld (Zof F D cm) w w' ↔ SameWorld F w w' :=
  ⟨SameWorld.mono fun a h => (zof_iff_of_sub hD cm a).1 h,
    SameWorld.mono fun a h => (zof_iff_of_sub hD cm a).2 h⟩

/-- **The callee lockstep of a pinned step from `XNIF`**, at any set equivalent to `F`. -/
theorem callLockstepF {F : BitVec 64 → Prop} {syms : String → Option Nat} {X : ExtSem}
    {env : Clif.Env} {exts : List Clif.ExtFunc} {sigs : List Clif.Signature} {inst : Clif.Inst}
    {fr : Clif.Frame} {cm : Clif.Mem} {sp0 : BitVec 64}
    (hNI : XNIF F syms exts sigs sp0 (CallLg env exts sigs) X)
    {Z : BitVec 64 → Prop} (hZ : ∀ a, Z a ↔ F a) {us : List CV} {w w' : Arm.ArmState}
    (hw : SameWorld Z w w') :
    ∀ dest, CallG F syms X exts sigs sp0 (StepPin env exts sigs inst fr cm) dest us w →
      CallG F syms X exts sigs sp0 (StepPin env exts sigs inst fr cm) dest us w' →
      ∀ o x o' x', X.call (destName dest) us w = some (o, x) →
        X.call (destName dest) us w' = some (o', x') → o = o' ∧ SameWorld Z x x' := by
  intro dest h1 h2 o x o' x' hc hc'
  obtain ⟨n1, sig1, vals1, cm1, args1, ⟨hcm1, hlg1, hsc1⟩, ⟨hm1, hc1⟩, ha1, hd1⟩ := h1
  obtain ⟨n2, sig2, vals2, cm2, args2, ⟨hcm2, -, hsc2⟩, ⟨hm2, hc2⟩, ha2, hd2⟩ := h2
  rw [hcm2, ← hcm1] at hm2
  obtain ⟨rfl, rfl⟩ := stepCall_unique hsc1 hsc2
  have hargs : args1 = args2 := by
    rcases hd1 with ⟨rfl, rfl⟩ | ⟨⟨r, rfl⟩, u, rfl, -⟩ <;>
      rcases hd2 with ⟨he, rfl⟩ | ⟨⟨r', he⟩, u', hu', -⟩
    · rfl
    · cases he
    · cases he
    · exact (List.cons.inj hu').2
  subst hargs
  have hd : destName dest = some n1 ∧ us = args1 ∨
      destName dest = none ∧ ∃ u, us = u :: args1 ∧ lo64 u = X.sym n1 0 := by
    rcases hd1 with ⟨rfl, rfl⟩ | ⟨⟨r, rfl⟩, hu⟩
    · exact .inl ⟨rfl, rfl⟩
    · exact .inr ⟨rfl, hu⟩
  have hA : (∃ e ∈ exts, e.name = n1 ∧ e.sig = sig1) ∧ ArgsAt sig1 vals1 args1 w ∧
      ArgsAt sig1 vals1 args1 w' ∨
      sig1 ∈ sigs ∧ ArgsAt sig1 vals1 args1 w ∧ ArgsAt sig1 vals1 args1 w' := by
    rcases ha1 with ⟨hk, ha1⟩ | ⟨hs1, ha1⟩
    · rcases ha2 with ⟨-, ha2⟩ | ⟨-, ha2⟩
      · exact .inl ⟨hk, ha1, ha2⟩
      · exact .inl ⟨hk, ha1, ha2⟩
    · rcases ha2 with ⟨-, ha2⟩ | ⟨-, ha2⟩
      · exact .inr ⟨hs1, ha1, ha2⟩
      · exact .inr ⟨hs1, ha1, ha2⟩
  obtain ⟨ho, hx⟩ := hNI n1 sig1 vals1 cm1 args1 (destName dest) us w w' o x o' x' hlg1 hd
    (SameWorld.mono (fun a h => (hZ a).1 h) hw) hm1 hm2 hc1 hc2 hA hc hc'
  exact ⟨ho, SameWorld.mono (fun a h => (hZ a).2 h) hx⟩

section
variable {f : Clif.Function} {X : ExtSem} {syms : String → Option Nat} {env : Clif.Env}
  {F : BitVec 64 → Prop} {c : BitVec 64} {D : BitVec 64 → Prop}

/-- **The paired lockstep of the guarded runs of one step from `XNIF`**, the world difference
inside `F` (`guardedStep`). -/
theorem guardedStepF
    (hNI : XNIF F syms (f.externs.map (·.2)) (indSigs f) c
      (CallLg env (f.externs.map (·.2)) (indSigs f)) X)
    (hD : ∀ a, D a → F a) (hTls : XTls F X) (ctx : FnCtx) (inst : Clif.Inst) (fr : Clif.Frame)
    (cm : Clif.Mem) (ms : List MInst) :
    ∀ i ∈ ms, ∀ us w w' o w₁ ct o' w₁' ct', SameWorld (Zof F D cm) w w' →
      csemG F ctx X (fun b => ¬ Zof F D cm b) syms (f.externs.map (·.2)) (indSigs f) c
        (StepPin env (f.externs.map (·.2)) (indSigs f) inst fr cm) i us w = some (o, w₁, ct) →
      csemG F ctx X (fun b => ¬ Zof F D cm b) syms (f.externs.map (·.2)) (indSigs f) c
        (StepPin env (f.externs.map (·.2)) (indSigs f) inst fr cm) i us w' = some (o', w₁', ct') →
      o = o' ∧ ct = ct' ∧ SameWorld (Zof F D cm) w₁ w₁' := by
  intro i _ us w w' o w₁ ct o' w₁' ct' hw h h'
  have hFZ : ∀ a, F a → Zof F D cm a := fun a h => .inl h
  exact csemG_lockstep2 hFZ hw (callLockstepF hNI (zof_iff_of_sub hD cm) hw)
    (fun n => hTls _ n w w' hFZ hw) h h'

end

end E2E
