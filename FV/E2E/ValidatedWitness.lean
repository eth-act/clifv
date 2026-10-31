import FV.E2E.ValidatedNoninterference
import FV.E2E.ValidatedCleanup
import FV.E2E.WorldUnwindNIWitness
import FV.E2E.LowerDirect
import FV.E2E.DeadCleanupDirect

/-! Positive non-vacuity witnesses for the try-call and TLS helper premises.
These reuse real legacy compilation, preserving the old contract as an instance
of the new one. Actual Stock success is witnessed independently in
`FV.Backend.Proof.StockD0ActualConsumerWitness`. No runtime class is enabled here. -/
set_option autoImplicit false
namespace E2E.ValidatedWitness
open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup
open DeadCleanupUnwindWitness WorldUnwindWitness

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- The prepared try-call survives in both real compilation modes. -/
theorem try_flags : vcpL.hasTryCall = true ∧ vcp.hasTryCall = true := by
  native_decide

/-- Both new contracts accept the existing successful exceptional-control
fixture, with a positive try-call premise. -/
theorem try_contracts :
    CompiledValidated source 0 vc vcpL rfL afL faL fbL ∧
    CompiledCleanupValidated source 0 vc vcp rf af fa fb ∧
    vcpL.hasTryCall = true ∧ vcp.hasTryCall = true ∧
    (∃ B ∈ source.blocks, B.term.isTry = true) := by
  have plain := factsL.1.toValidated
  have clean := facts.2.2.2.1.toValidated
  exact ⟨plain, clean, try_flags.1, try_flags.2,
    hasTry_of_hasTryCallA_validated plain.toCompiledValidatedA try_flags.1⟩

/-- The paired try-call helpers have jointly inhabited external-semantics
premises on the compiled try-call fixture. The original raising environment
supplies the source call contracts; the existing world-independent TLS flags
supply both non-interference contracts. -/
theorem paired_try_calls (p0 : Arm.PState) (F D : BitVec 64 → Prop) (c : BitVec 64) :
    TryCalls source (pairSem (csem F ⟨faL.k, afL.slotBase⟩ (Xr (WorldUnwindNIWitness.X1 p0))))
      (MRP ⟨F, fun _ => none, afL.slotBase, (RAFrame.compute vcpL rfL).intBase⟩ source c D)
      IselSimUWitness.env.toEnv { funcs := [] } (RAFrame.compute vcpL rfL).intBase := by
  exact tryCalls_pair_validated (xCallsOk_env _ _ _)
    (fun _ _ h => by cases h) rfl (WorldUnwindNIWitness.xni _ _ _ _ _ _ _)
    (WorldUnwindNIWitness.xtls _ _)

/-- The indirect paired helper uses the same inhabited contracts, without a
legacy construction premise or a new restriction on indirect signatures. -/
theorem paired_try_indirect_calls (p0 : Arm.PState) (F D : BitVec 64 → Prop) (c : BitVec 64) :
    TryIndCalls (pairSem (csem F ⟨faL.k, afL.slotBase⟩ (Xr (WorldUnwindNIWitness.X1 p0))))
      (MRP ⟨F, fun _ => none, afL.slotBase, (RAFrame.compute vcpL rfL).intBase⟩ source c D)
      IselSimUWitness.env.toEnv { funcs := [] } (indSigs source) := by
  exact tryIndCalls_pair_validated try_contracts.1 (xCallsIndOk_env _ _ _)
    (fun _ _ h => by cases h) (WorldUnwindNIWitness.xni _ _ _ _ _ _ _)
    (WorldUnwindNIWitness.xtls _ _)

/-- Cleanup's paired direct-call helper has the same concrete source and
external semantics, using its actual cleaned allocation frame. -/
theorem paired_try_calls_cleanup (p0 : Arm.PState) (F D : BitVec 64 → Prop) (c : BitVec 64) :
    TryCalls source (pairSem (valueSem F ⟨fa.k, af.slotBase⟩ (Xr (WorldUnwindNIWitness.X1 p0))))
      (MRP ⟨F, fun _ => none, af.slotBase, (RAFrame.compute vcp rf).intBase⟩ source c D)
      IselSimUWitness.env.toEnv { funcs := [] } (RAFrame.compute vcp rf).intBase := by
  exact tryCalls_pair_value_validated (xCallsOk_env _ _ _)
    (fun _ _ h => by cases h) rfl (WorldUnwindNIWitness.xni _ _ _ _ _ _ _)
    (WorldUnwindNIWitness.xtls _ _)

/-- Cleanup's paired indirect-call helper has jointly inhabited premises. -/
theorem paired_try_indirect_calls_cleanup (p0 : Arm.PState) (F D : BitVec 64 → Prop) (c : BitVec 64) :
    TryIndCalls (pairSem (valueSem F ⟨fa.k, af.slotBase⟩ (Xr (WorldUnwindNIWitness.X1 p0))))
      (MRP ⟨F, fun _ => none, af.slotBase, (RAFrame.compute vcp rf).intBase⟩ source c D)
      IselSimUWitness.env.toEnv { funcs := [] } (indSigs source) := by
  exact tryIndCalls_pair_value_validated try_contracts.2.1 (xCallsIndOk_env _ _ _)
    (fun _ _ h => by cases h) (WorldUnwindNIWitness.xni _ _ _ _ _ _ _)
    (WorldUnwindNIWitness.xtls _ _)

namespace Tls
/-- A live TLS result, so cleanup cannot erase the tested instruction. -/
def source : Clif.Function :=
  { name := "validated_tls", sig := { returns := [{ ty := .i64 }] },
    globals := [(0, .tlsSymbol "thread_value" 0 false)],
    blocks := [{ id := 0, body := [{ results := [0], inst := .tlsValue .i64 0 }], term := .ret [0] }] }
def vc : VCode := (lowerFunction source).toOption.getD default
def vcp (cleanup : Bool) : VCode :=
  (Backend.prepare (if cleanup then prune vc else vc)).toOption.getD default
def rf (cleanup : Bool) : RFunc := spillAlloc (vcp cleanup)
def af (cleanup : Bool) : AFunc := (lowerRFunc (vcp cleanup) (rf cleanup)).toOption.getD default
def fa (cleanup : Bool) : FnAsm := (emitFunc 0 (af cleanup)).toOption.getD default
def fb (cleanup : Bool) : FnBin := (fa cleanup).layout.toOption.getD default

def checks (cleanup : Bool) : Bool :=
  dominatedB source && lowerScopeB source && (lowerFunction source).toBool &&
  (Backend.prepare (if cleanup then prune vc else vc)).toBool &&
  (checkAlloc (vcp cleanup) (rf cleanup)).toBool &&
  (lowerRFunc (vcp cleanup) (rf cleanup)).toBool &&
  (emitFunc 0 (af cleanup)).toBool && (fa cleanup).layout.toBool && (vcp cleanup).hasTls

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- Closed successful compilation and positive TLS detection in both modes. -/
theorem checks_true : checks false = true ∧ checks true = true := by native_decide

/-- Both new contracts are inhabited with a live TLS instruction; the positive
premise of each TLS transport lemma is satisfied by the emitted artifact. -/
theorem contracts :
    CompiledValidated source 0 vc (vcp false) (rf false) (af false) (fa false) (fb false) ∧
    CompiledCleanupValidated source 0 vc (vcp true) (rf true) (af true) (fa true) (fb true) ∧
    (vcp false).hasTls = true ∧ (vcp true).hasTls = true ∧ hasTls source = true := by
  have plain := checks_true.1
  have clean := checks_true.2
  simp only [checks, Bool.and_eq_true, and_assoc] at plain clean
  obtain ⟨hd, hs, hl, hp, hca, ha, he, hla, ht⟩ := plain
  obtain ⟨_, _, _, hpc, hcac, hac, hec, hlac, htc⟩ := clean
  have hplain := Compiled.of_lowerB hd hs (ok_getD hl) (ok_getD hp) (ok_unit hca)
    (ok_getD ha) (ok_getD he) (ok_getD hla)
  have hclean := CompiledCleanup.of_lowerB hd hs (ok_getD hl) (ok_getD hpc) (ok_unit hcac)
    (ok_getD hac) (ok_getD hec) (ok_getD hlac)
  exact ⟨hplain.toValidated, hclean.toValidated, ht, htc,
    hasTls_of_vcodeA_validated hplain.toValidated.toCompiledValidatedA ht⟩
end Tls
end E2E.ValidatedWitness
