import FV.E2E.ClifEnvOnly
import FV.E2E.PairDriver

/-!
# The callee contracts of a restricted environment (SEM1 item (b), `docs/plans/uninit.md` §5.9)

The counted pipelines (`backend_correct_world_ni_pipelinePRI`) take the callee contracts
(`XCallsOk`, `XCallsIndOk`) and the external non-interference (`XNI`) per CLIF state, for the
environment restricted to the state's invocation (`Clif.Env.only env (Clif.Invoked env p s)`).
This file is the interface for discharging them:

* `xCallsOk_only_of`, `xCallsIndOk_only_of`, `xNI_only_of`: the restricted contracts from the
  contract at the admitted invocations only (`A name vals cm`), the shape item (b) discharges at
  the machine's `n`-th call;
* `xCallsOk_only`, `xCallsIndOk_only`, `xNI_only`: an environment's contract holds for every
  restriction of it (so the one-`ExtSem` premises of the uncounted pipelines give the per-state
  ones, for `ExtSemI.const X`).
-/

namespace E2E

open Backend Backend.Proof

theorem onlyFn_returned {A : String → List Clif.Val → Clif.Mem → Prop} {n : String}
    {g : List Clif.Val → Clif.Mem → Clif.Outcome} {vals : List Clif.Val} {m : Clif.Mem}
    {rv : List Clif.Val} {m' : Clif.Mem} (h : Clif.onlyFn A n g vals m = .returned rv m') :
    A n vals m ∧ g vals m = .returned rv m' := by
  by_cases hA : A n vals m
  · rw [Clif.onlyFn_of hA] at h; exact ⟨hA, h⟩
  · rw [Clif.onlyFn_of_not hA] at h; cases h

/-- **The restricted extern contract from the contract at the admitted invocations.** -/
theorem xCallsOk_only_of {env : Clif.Env} {A : String → List Clif.Val → Clif.Mem → Prop}
    {exts : List Clif.ExtFunc} {MR : MemRelT} {X : ExtSem}
    (h : ∀ ext ∈ exts, ∀ g (sl : List (Clif.SlotId × Nat)) (cm : Clif.Mem) (w : Arm.ArmState)
      (d : Option String) (uses args : List CV) (vals rvals : List Clif.Val) (cm' : Clif.Mem),
      A ext.name vals cm → env.extern ext.name = some g →
      (d = some ext.name ∧ uses = args ∨
        d = none ∧ ext.colocated = false ∧ uses = ofX (X.sym ext.name 0) :: args) →
      ArgsAt ext.sig vals args w → MR sl cm w →
      g vals cm = .returned rvals cm' → rvals.length = ext.sig.returns.length →
      ∃ outs w', X.call d uses w = some (outs, w') ∧ outs.length = (sigRets ext.sig).length ∧
        PrefixHold rvals outs ∧ MR sl cm' w') :
    XCallsOk (env.only A) exts MR X := by
  intro ext hext g' sl cm w d uses args vals rvals cm' hg hd hargs hmr hret hlen
  obtain ⟨g, hg0, rfl⟩ := Clif.Env.only_extern_eq hg
  obtain ⟨hA, hret'⟩ := onlyFn_returned hret
  exact h ext hext g sl cm w d uses args vals rvals cm' hA hg0 hd hargs hmr hret' hlen

/-- **The restricted indirect-call contract from the contract at the admitted invocations.** -/
theorem xCallsIndOk_only_of {env : Clif.Env} {A : String → List Clif.Val → Clif.Mem → Prop}
    {sigs : List Clif.Signature} {MR : MemRelT} {X : ExtSem}
    (h : ∀ sig ∈ sigs, ∀ (n : String) g (sl : List (Clif.SlotId × Nat)) (cm : Clif.Mem)
      (w : Arm.ArmState) (u : CV) (args : List CV) (vals rvals : List Clif.Val) (cm' : Clif.Mem),
      A n vals cm → env.extern n = some g → (∀ s, env.sigOf n = some s → sig.abiMatch s = true) →
      lo64 u = X.sym n 0 →
      ArgsAt sig vals args w → MR sl cm w →
      g vals cm = .returned rvals cm' → rvals.length = sig.returns.length →
      vals.map (·.ty) = Clif.AbiParam.tys sig.params →
      ∃ outs w', X.call none (u :: args) w = some (outs, w') ∧
        outs.length = (sigRets sig).length ∧ PrefixHold rvals outs ∧ MR sl cm' w') :
    XCallsIndOk (env.only A) sigs MR X := by
  intro sig hsig n g' sl cm w u args vals rvals cm' hg hs hu hargs hmr hret hlen hty
  obtain ⟨g, hg0, rfl⟩ := Clif.Env.only_extern_eq hg
  obtain ⟨hA, hret'⟩ := onlyFn_returned hret
  exact h sig hsig n g sl cm w u args vals rvals cm' hA hg0 (by simpa using hs) hu hargs hmr
    hret' hlen hty

/-- A call the restricted environment admits is one the environment admits, at an admitted
invocation. -/
theorem callLg_only {env : Clif.Env} {A : String → List Clif.Val → Clif.Mem → Prop}
    {exts : List Clif.ExtFunc} {sigs : List Clif.Signature} {n : String} {sig : Clif.Signature}
    {vals : List Clif.Val} {cm : Clif.Mem} (h : CallLg (env.only A) exts sigs n sig vals cm) :
    A n vals cm ∧ CallLg env exts sigs n sig vals cm := by
  obtain ⟨hk, g', rv, cm', hg, hret⟩ := h
  obtain ⟨g, hg0, rfl⟩ := Clif.Env.only_extern_eq hg
  obtain ⟨hA, hret'⟩ := onlyFn_returned hret
  exact ⟨hA, hk, g, rv, cm', hg0, hret'⟩

/-- **The restricted `XNI` from `XNI` at the admitted invocations.** -/
theorem xNI_only_of {env : Clif.Env} {A : String → List Clif.Val → Clif.Mem → Prop}
    {F : BitVec 64 → Prop} {syms : String → Option Nat} {exts : List Clif.ExtFunc}
    {sigs : List Clif.Signature} {sp0 : BitVec 64} {X : ExtSem}
    (h : XNI F syms exts sigs sp0 (fun n sig vals cm => A n vals cm ∧ CallLg env exts sigs n sig
      vals cm) X) :
    XNI F syms exts sigs sp0 (CallLg (env.only A) exts sigs) X :=
  fun n sig vals cm args d uses Z w w' o x o' x' hLg =>
    h n sig vals cm args d uses Z w w' o x o' x' (callLg_only hLg)

/-- An environment's extern contract holds for every restriction of it. -/
theorem xCallsOk_only {env : Clif.Env} (A : String → List Clif.Val → Clif.Mem → Prop)
    {exts : List Clif.ExtFunc} {MR : MemRelT} {X : ExtSem} (h : XCallsOk env exts MR X) :
    XCallsOk (env.only A) exts MR X :=
  xCallsOk_only_of fun ext hext g sl cm w d uses args vals rvals cm' _ hg hd hargs hmr hret hlen =>
    h ext hext g sl cm w d uses args vals rvals cm' hg hd hargs hmr hret hlen

/-- An environment's indirect-call contract holds for every restriction of it. -/
theorem xCallsIndOk_only {env : Clif.Env} (A : String → List Clif.Val → Clif.Mem → Prop)
    {sigs : List Clif.Signature} {MR : MemRelT} {X : ExtSem} (h : XCallsIndOk env sigs MR X) :
    XCallsIndOk (env.only A) sigs MR X :=
  xCallsIndOk_only_of fun sig hsig n g sl cm w u args vals rvals cm' _ hg hs hu hargs hmr hret
    hlen hty => h sig hsig n g sl cm w u args vals rvals cm' hg hs hu hargs hmr hret hlen hty

/-- An environment's `XNI` holds for every restriction of it. -/
theorem xNI_only {env : Clif.Env} (A : String → List Clif.Val → Clif.Mem → Prop)
    {F : BitVec 64 → Prop} {syms : String → Option Nat} {exts : List Clif.ExtFunc}
    {sigs : List Clif.Signature} {sp0 : BitVec 64} {X : ExtSem}
    (h : XNI F syms exts sigs sp0 (CallLg env exts sigs) X) :
    XNI F syms exts sigs sp0 (CallLg (env.only A) exts sigs) X :=
  xNI_only_of fun n sig vals cm args d uses Z w w' o x o' x' hLg =>
    h n sig vals cm args d uses Z w w' o x o' x' hLg.2

end E2E
