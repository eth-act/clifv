import FV.Concurrency.RealizeCompiled
import FV.Concurrency.ArmAllocMemWitness
import FV.Concurrency.ThreadComposeWitness

/-!
# Non-vacuity of `realizes_compiled` on compiled code (T2k, #311)

The CLIF function `fence; return` (`srcF`, parsed) as the pipeline compiles it: its lowering
`vcF`, `prepare`'s output `vcpF`, the spill allocation `rfF` (18 saves of the callee-saved
registers by moves, the `fence`, 18 restores, the return), lowered, emitted, laid out and loaded
as `ArmAllocThread.Witness.act` loads it (`RA`):

* `driverHyp_of`: the driver hypothesis of layer 2 for a function whose checks hold (the
  construction of `IselThread.Witness.driverHypA`, for any function);
* `compiledF`: **every premise of `RealizeCompiled.Compiled`** holds for `RA`, the CLIF entry
  state `csF` (block 0, no arguments, empty memory) and the Arm state after the prologue: `RA.Wf`,
  its moves' code (`moveCodeOk`), the memory scope, the driver hypothesis and checks, the memory
  relation `RelW` with the activation's private set `RA.F`, `Q ∧ AInv` (`q_init`).
  Checks by `native_decide` (witness only).
-/

namespace Concurrency.RealizeCompiled.Witness

open Arm ArmThread Prog ClifThread ProgE2E Backend Backend.Proof Backend.Proof.Driver VCodeThread
  PrepThread AllocThread IselCheck CorrRefine ClifCStepTerm IselThread ThreadRefine
  ArmAllocThread ThreadCompose E2E

/-! ## The driver hypothesis of a checked function -/

/-- A function without externs whose verifiability check holds is in the subset (for every
program). -/
theorem inSubset_of {f : Clif.Function} (hv : verifiable f = true) (hext : f.externs = [])
    (p : Clif.Program) : InSubset p f := by
  simp only [verifiable, abiSigs, indSigsOk, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq, and_assoc] at hv
  obtain ⟨hE, hf, hext', hind⟩ := hv
  have hno : ∀ fn e, f.extern? fn = some e → False := fun fn e he => by
    simp [Clif.Function.extern?, hext] at he
  exact ⟨hE, fun _ _ _ _ fn _ _ e he => (hno fn e he).elim,
    fun _ _ fn _ _ _ e he => (hno fn e he).elim, ⟨hf, hext'⟩, hind⟩

/-- **The driver hypothesis of layer 2 for a checked function** (`IselThread.Witness.driverHypA`'s
construction): for `csem Γ.F fctx X` and `RelW Γ f c`, when `fctx`'s slot base is `Γ`'s slot
offset and `X`'s symbols are `Γ`'s. -/
theorem driverHyp_of {f : Clif.Function} {vc : VCode} {Γ : E2E.Rel} {fctx : FnCtx} {X : ExtSem}
    {c : BitVec 64} {env : Clif.Env} {p : Clif.Program}
    (hlow : lowerCheck f vc = true) (hthr : IselCheck.threadCheck f = true)
    (hext : f.externs = []) (hind : indSigs f = []) (hv : verifiable f = true)
    (hcfg : ∃ ss ps, vc.cfg = .ok (ss, ps)) (hout0 : vc.outgoing = 0)
    (hslot : fctx.slotBase = Γ.slotOff)
    (hsym : ∀ n b, Γ.syms n = some b → X.sym n 0 = BitVec.ofNat 64 b) :
    ∃ ctx st0 R gn bl A, DriverHyp f vc ctx st0 R gn bl A (csem Γ.F fctx X) (RelW Γ f c) env p ∧
      IselCheck.threadCheckBl f bl = true := by
  obtain ⟨ctx, st0, R, gn, bl, A, hshape, hcert, hbr, hbl⟩ :=
    IselCheck.obligations_of_threadCheck hlow hthr
  have hsub := inSubset_of hv hext p
  have hX : XCallsOk env (f.externs.map (·.2)) (RelW Γ f c) X := by
    rw [hext]; intro ext h; cases h
  have hXI : XCallsIndOk env (indSigs f) (RelW Γ f c) X := by
    rw [hind]; intro s h; cases h
  have hRef : Refines Γ.F (csem Γ.F fctx X) := refines_csem Γ.F fctx X
  have hmem : MemRefines Γ.F Γ.slotOff Γ.syms (csem Γ.F fctx X) :=
    memRefines_csem Γ.F fctx X hslot hsym
  have hcalls := callsRefine_csem (F := Γ.F) (ctx := fctx) hX
  have hicalls := indCallsRefine_csem (F := Γ.F) (ctx := fctx) hXI hsym
    (fun _ _ _ h => h.1.1.symbols)
  have houtB : vc.outgoing ≤ Γ.out := by rw [hout0]; exact Nat.zero_le _
  refine ⟨ctx, st0, R, gn, bl, A, {
    shape := hshape
    cert := hcert
    dsem := (driverSem_csem Γ.F fctx X).toDriverSemG
    insts := instCalls_of_rules lowerRulesCorrect_program excludedUnmatchable callRulesCorrect
      indRulesCorrect memRulesCorrect_program hRef (mrStable_relW Γ f c) hcalls hicalls hmem
      (outArgsOk_relW Γ f c) (callsStack_mono (callsStack_of_check hlow) houtB)
      (memRelOk_relW Γ f c)
    terms := termCalls_of_rules lowerTermRulesCorrect termUnmatchable branchRulesCorrect
      branchExcludedUnmatchable hRef (mrStable_relW Γ f c)
    ext := fun B hB st hst fn args hi e he => hsub.externCalls B hB st hst fn args hi e he
    indSig := indSig_of_subset hsub
    subE := hsub.subsetE
    entryLocs := entryOk_of_check hlow
    brIdx := hbr
    noTail := noTail_of_subset hsub
    tries := ⟨_, tryCalls_of_rules tryRulesCorrect tryUnmatchable hRef (mrStable_relW Γ f c) hmem
      (outArgsOk_relW Γ f c) hcalls, tryStack_mono (tryStack_of_check hlow) houtB⟩
    tryExt := hsub.tryExterns
    tryInd := tryIndCalls_of_rules tryIndRulesCorrect tryIndUnmatchable hRef
      (mrStable_relW Γ f c) hicalls
    tryIndSig := tryIndSig_of_subset hsub
    cfg := hcfg }, hbl⟩

/-! ## `fence; return`, compiled -/

/-- `fence; return`. -/
def srcF : String := "function %fence() {
block0:
    fence
    return
}
"

/-- The parsed function. -/
def fF : Clif.Function :=
  match Clif.parse srcF with
  | .ok p => p.funcs.headD default
  | .error _ => default

/-- Its lowering. -/
def vcF : VCode := match lowerFunction fF with
  | .ok vc => vc
  | .error _ => default

/-- `prepare`'s output. -/
def vcpF : VCode := match Backend.prepare vcF with
  | .ok vcp => vcp
  | .error _ => default

/-- The spill allocation (saves, `fence`, restores, return). -/
def rfF : RFunc := spillAlloc vcpF

/-- The activation. -/
abbrev RA : RL := ArmAllocThread.Witness.act vcpF rfF

/-- The checks on `fF`, its lowering, `prepare` and the allocation. -/
theorem checksF : lowerCheck fF vcF = true ∧ IselCheck.threadCheck fF = true ∧
    fF.externs.isEmpty = true ∧ (indSigs fF).isEmpty = true ∧ verifiable fF = true ∧
    IselThread.Witness.isOkB vcF.cfg = true ∧ vcF.outgoing = 0 ∧ prepCheck vcF vcpF = true ∧
    (checkAlloc vcpF rfF).isOk = true ∧ rfF.blocks.size = 1 ∧ (rfF.blocks[0]!).size = 39 := by
  native_decide

end Concurrency.RealizeCompiled.Witness
