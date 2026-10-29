import FV.E2E.BackendWorldI
import FV.Backend.Proof.IselCallsOne

/-!
# The call-count premises of the counted simulation hold for every function (SEM1, `docs/plans/uninit.md` §5.9)

`InstCallsOne f` and `TryCallsOne f` (premises of `iselSim_relWI`, `backend_correct_worldPRI`)
are properties of the ISLE lowering. The rule-table certificate `Cov.lower_call_fmts` and the call
roots' runs (`FV/Backend/Proof/IselCallsOne.lean`: `Cov.lower_callsOne`, `Cov.tryCall_callsOne`,
`Cov.tryCallInd_callsOne`) prove them for **every** function:

* `instCallsOne_all f : InstCallsOne f`, `tryCallsOne_all f : TryCallsOne f`;
* `iselSim_relWIC`, `backend_correct_worldPRIC`: `iselSim_relWI`/`backend_correct_worldPRI`
  without the two premises (same conclusions; the originals stay).

The statements are universal, so every function of the typed scope (`InScopeIn`, any
`Compile.functionE*` subset) has them; `InstCallsOne` assumes `Compile.functionE f` itself (it
is vacuous outside the integer subset, where the integer pipeline does not apply).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- A `call`/`call_indirect` (`isCallLike`) in the form the rule lemmas take. -/
theorem callLike_cases {inst : Clif.Inst} (h : inst.isCallLike = true) :
    (∃ fn args, inst = .call fn args) ∨ ∃ sig callee args, inst = .callIndirect sig callee args := by
  cases inst <;> simp only [Clif.Inst.isCallLike, reduceCtorEq] at h
  · exact .inl ⟨_, _, rfl⟩
  · exact .inr ⟨_, _, _, rfl⟩

/-- **`InstCallsOne` holds for every function**: a `call`/`call_indirect` statement's lowering
has exactly one VCode call (`Cov.lower_callsOne`). -/
theorem instCallsOne_all (f : Clif.Function) : InstCallsOne f := by
  intro ctx ii info inst st rss st' tr hctx _ hE hi hc _ hemp _ hrun hcl
  obtain ⟨ms, hms, hk⟩ := Cov.lower_callsOne hctx hE hi hc (callLike_cases hcl) hrun
  rw [hemp, Array.empty_append] at hms
  rw [hms, List.toList_toArray]
  exact hk

/-- One call and nothing before it: the code `pre ++ [call]` with one call has none in `pre`. -/
theorem callsI_pre_of {ms pre : List MInst} {ci : CallInfo} (hk : callsI ms = 1)
    (h : ms = pre ++ [.call ci]) : callsI pre = 0 := by
  subst h
  rw [callsI_append] at hk
  have : callsI [MInst.call ci] = 1 := rfl
  omega

/-- **`TryCallsOne` holds for every function**: the code of a `try_call`/`try_call_indirect`
lowering has one call, its last instruction (`Cov.tryCall_callsOne`,
`Cov.tryCallInd_callsOne`). -/
theorem tryCallsOne_all (f : Clif.Function) : TryCallsOne f := by
  refine ⟨?_, ?_⟩
  · intro ctx ti fn args et data sig items targets info trs lo st1 out st' tr hctx _ hd he hph _ htr
      _ hrun pre ci hpre
    obtain ⟨ms, hms, hk⟩ := Cov.tryCall_callsOne hctx hph hd he htr hrun
    simp only [Array.empty_append] at hms
    rw [hms, List.toList_toArray] at hpre
    exact callsI_pre_of hk hpre
  · intro ctx ti callee args et data sig items targets info trs lo st1 out st' tr hctx _ hd he hph _
      htr _ hrun pre ci hpre
    obtain ⟨ms, hms, hk⟩ := Cov.tryCallInd_callsOne hctx hph hd he htr hrun
    simp only [Array.empty_append] at hms
    rw [hms, List.toList_toArray] at hpre
    exact callsI_pre_of hk hpre

/-- **`iselSim_relWI` without the call-count premises** (`instCallsOne_all`,
`tryCallsOne_all`). -/
theorem iselSim_relWIC {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : Compiled f k vc vcp rf af fa fb)
    {XI : ExtSemI} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    {F : BitVec 64 → Prop} {c : BitVec 64} {args : List Clif.Val} {cs : Clif.State}
    (hX : ∀ s n, ReachN env p cs s n →
      XCallsOk (env.only (Clif.Invoked env p s)) (f.externs.map (·.2))
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n) ∧
      XCallsIndOk (env.only (Clif.Invoked env p s)) (indSigs f)
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n))
    (hsym : ∀ n b, syms n = some b → XI.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {w₀ : Arm.ArmState} (ρ₀ : Nat → CV)
    (hce : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀) (htr : TrapsExplicit env p cs) (fuel : Nat) :
    (∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ us outs w, VRetFrom vc (csemI F ⟨fa.k, af.slotBase⟩ XI) ⟨0, 0, ρ₀, (w₀, 0)⟩ us outs w ∧
        RetPins vals us ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w.1) ∧
    (∀ c', Clif.runLoop env p fuel cs = .trapped c' →
      VTrapFrom vc (csemI F ⟨fa.k, af.slotBase⟩ XI) ⟨0, 0, ρ₀, (w₀, 0)⟩ c') :=
  iselSim_relWI hsub hc (instCallsOne_all f) (tryCallsOne_all f) hX hsym hslot ρ₀ hce hrel hargs
    htr fuel

/-- **`backend_correct_worldPRI` without the call-count premises** (`instCallsOne_all`,
`tryCallsOne_all`). -/
theorem backend_correct_worldPRIC {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : Compiled f k vc vcp rf af fa fb)
    {XI : ExtSemI} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hX : ∀ s n, ReachN env p cs s n →
      XCallsOk (env.only (Clif.Invoked env p s)) (f.externs.map (·.2))
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n) ∧
      XCallsIndOk (env.only (Clif.Invoked env p s)) (indSigs f)
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n))
    (hsym : ∀ n b, syms n = some b → XI.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    (∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        RetPins vals us ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧ vc.RetsSite us ∧
        ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (Kp : Nat) (cc : BitVec 64)
          (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState) (s : Arm.ArmState),
          ActEntryPR vcp rf af fa fb K F G XI H base ra Kp cc P R s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (ArmStepX (XI.at 0) H fa) n s) ∧
            PostTrace fa af base (ArmStepX (XI.at 0) H fa) s n) ∧
    (∀ c', Clif.runLoop env p fuel cs = .trapped c' →
      ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (Kp : Nat) (cc : BitVec 64)
        (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState) (s : Arm.ArmState),
        ActEntryPR vcp rf af fa fb K F G XI H base ra Kp cc P R s w₀ →
        ∃ n, TrapAt fb base c' (runX (ArmStepX (XI.at 0) H fa) n s)) :=
  backend_correct_worldPRI hsub hc (instCallsOne_all f) (tryCallsOne_all f) hcov hX hsym hslot hcs
    hrel hargs htr fuel

end E2E
