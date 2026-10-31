import FV.E2E.InvokedN
import FV.E2E.BackendWorldPRIC

/-!
# The counted per-function theorems for guarded call semantics (SEM1 item (b), `docs/plans/uninit.md` §5.9)

`ExtSemI.guardI XI Q`: call number `n` is `XI.at n` guarded by `Q n` (`ExtSem.guard`). With
`Q n := CallPostN … n`, the results the contracts accept for the environment restricted to the
invocation of call number `n` (`InvokedN`), the per-state premise `hX` of the counted pipelines
holds for every `XI` (`hX_guardI`), given

* `NoRetCall` (no reached state ends in `return_call`; cg_clif emits none), and
* `InvokedRetOk`: the invocation of each call, if it returns, keeps the live allocations and
  symbols, and the declarations it can stand for agree on the ABI return count.

`backend_correct_world_cleanupPRB`, `backend_correct_world_pipelinePRB`: the `*_PRIC` theorems
for `XI.guardI (CallPostN …)` with `hX` replaced by these two premises (the non-interference
clause is not needed: the oracle statement is per actual activation, §5.1 (i)).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- **`XI` with call number `n` guarded by `Q n`.** -/
noncomputable def _root_.Backend.Proof.ExtSemI.guardI (XI : ExtSemI)
    (Q : Nat → Option String → List CV → Arm.ArmState → List CV × Arm.ArmState → Prop) :
    ExtSemI where
  call n := ((XI.at n).guard (Q n)).call
  sym := XI.sym
  tp := XI.tp
  tlsFlags := XI.tlsFlags

theorem _root_.Backend.Proof.ExtSemI.guardI_at (XI : ExtSemI)
    (Q : Nat → Option String → List CV → Arm.ArmState → List CV × Arm.ArmState → Prop) (n : Nat) :
    (XI.guardI Q).at n = (XI.at n).guard (Q n) := rfl

/-- The results the contracts accept for call number `n` of the run from `cs`. -/
def CallPostN (env : Clif.Env) (p : Clif.Program) (cs : Clif.State) (exts : List Clif.ExtFunc)
    (sigs : List Clif.Signature) (MR : MemRelT) (sym : String → Int → BitVec 64) (n : Nat) :
    Option String → List CV → Arm.ArmState → List CV × Arm.ArmState → Prop :=
  CallPost (env.only (InvokedN env p cs n)) exts sigs MR sym

/-- **The invocations of the run from `cs` that return keep the live allocations and symbols, and
the declarations each can stand for agree on a return count** (the declared returns since #587:
an `sret` callee's struct pointer is not a call result). A declaration can stand for an
invocation only with as many parameters as the invocation has values (#733: a call through a
declaration passes one value per parameter, `ArgsAt`; an indirect call's values have its
signature's parameter types, `CallPost`). -/
def InvokedRetOk (env : Clif.Env) (p : Clif.Program) (cs : Clif.State)
    (exts : List Clif.ExtFunc) (sigs : List Clif.Signature) : Prop :=
  ∀ n nm vals m g rvals cm', InvokedN env p cs n nm vals m → env.extern nm = some g →
    g vals m = .returned rvals cm' →
    (∀ a k, cm'.valid a k = true → m.valid a k = true) ∧ cm'.symbols = m.symbols ∧
    ∃ ℓ, rvals.length ≤ ℓ ∧
      (∀ ext ∈ exts, ext.name = nm → vals.length = ext.sig.params.length →
        rvals.length = ext.sig.returns.length → ext.sig.returns.length = ℓ) ∧
      (∀ sig ∈ sigs, (∀ s', env.sigOf nm = some s' → sig.abiMatch s' = true) →
        vals.length = sig.params.length → rvals.length = sig.returns.length →
        sig.returns.length = ℓ)

/-- **The per-state callee contracts of the guarded semantics.** -/
theorem hX_guardI {env : Clif.Env} {p : Clif.Program} {cs : Clif.State}
    {exts : List Clif.ExtFunc} {sigs : List Clif.Signature} {Γ : Rel} {f : Clif.Function}
    {c : BitVec 64} (XI : ExtSemI) (hnrc : NoRetCall env p cs)
    (hR : InvokedRetOk env p cs exts sigs) :
    ∀ s n, ReachN env p cs s n →
      XCallsOk (env.only (Clif.Invoked env p s)) exts (RelW Γ f c)
        ((XI.guardI (CallPostN env p cs exts sigs (RelW Γ f c) XI.sym)).at n) ∧
      XCallsIndOk (env.only (Clif.Invoked env p s)) sigs (RelW Γ f c)
        ((XI.guardI (CallPostN env p cs exts sigs (RelW Γ f c) XI.sym)).at n) :=
  fun s n hs => xCallsOk_guard_only (invoked_sub_invokedN hnrc hs) (XI.at n)
    (callPost_invokedN_exists (hR n))

/-- **`backend_correct_world_cleanupPRIC` for the guarded semantics**, `hX` discharged. -/
theorem backend_correct_world_cleanupPRB {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledCleanup f k vc vcp rf af fa fb)
    {XI : ExtSemI} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hnrc : NoRetCall env p cs) (hR : InvokedRetOk env p cs (f.externs.map (·.2)) (indSigs f))
    (hsym : ∀ n b, syms n = some b → XI.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    let XG := XI.guardI (CallPostN env p cs (f.externs.map (·.2)) (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) XI.sym)
    (∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        RetPins vals us ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧ vc.RetsSite us ∧
        ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (Kp : Nat) (cc : BitVec 64)
          (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState) (s : Arm.ArmState),
          ActEntryPR vcp rf af fa fb K F G XG H base ra Kp cc P R s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (ArmStepX (XG.at 0) H fa) n s) ∧
            PostTrace fa af base (ArmStepX (XG.at 0) H fa) s n) ∧
    (∀ c', Clif.runLoop env p fuel cs = .trapped c' →
      ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (Kp : Nat) (cc : BitVec 64)
        (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState) (s : Arm.ArmState),
        ActEntryPR vcp rf af fa fb K F G XG H base ra Kp cc P R s w₀ →
        ∃ n, TrapAt fb base c' (runX (ArmStepX (XG.at 0) H fa) n s)) :=
  backend_correct_world_cleanupPRIC hsub hc hcov (hX_guardI XI hnrc hR) hsym hslot hcs hrel hargs
    htr fuel

/-- **`backend_correct_world_pipelinePRIC` for the guarded semantics**, `hX` discharged. -/
theorem backend_correct_world_pipelinePRB {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledEither f k vc vcp rf af fa fb)
    {XI : ExtSemI} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hnrc : NoRetCall env p cs) (hR : InvokedRetOk env p cs (f.externs.map (·.2)) (indSigs f))
    (hsym : ∀ n b, syms n = some b → XI.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    let XG := XI.guardI (CallPostN env p cs (f.externs.map (·.2)) (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) XI.sym)
    (∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        RetPins vals us ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧ vc.RetsSite us ∧
        ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (Kp : Nat) (cc : BitVec 64)
          (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState) (s : Arm.ArmState),
          ActEntryPR vcp rf af fa fb K F G XG H base ra Kp cc P R s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (ArmStepX (XG.at 0) H fa) n s) ∧
            PostTrace fa af base (ArmStepX (XG.at 0) H fa) s n) ∧
    (∀ c', Clif.runLoop env p fuel cs = .trapped c' →
      ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (Kp : Nat) (cc : BitVec 64)
        (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState) (s : Arm.ArmState),
        ActEntryPR vcp rf af fa fb K F G XG H base ra Kp cc P R s w₀ →
        ∃ n, TrapAt fb base c' (runX (ArmStepX (XG.at 0) H fa) n s)) :=
  backend_correct_world_pipelinePRIC hsub hc hcov (hX_guardI XI hnrc hR) hsym hslot hcs hrel hargs
    htr fuel

end E2E
