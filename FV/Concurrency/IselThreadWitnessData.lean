import FV.E2E.LinkWorld
import FV.Concurrency.IselCheck
import FV.Concurrency.SegShapeWitness

/-!
# A concrete driver hypothesis for layer 2 (T2h, #311, layer 2e)

The function `SegShape.Witness.fA` (`atomic_load`, `atomic_store`, `atomic_rmw`, `atomic_cas`,
`fence`, `load`, `store`, `iadd`, `return`):

* `vcA`: its VCode (`lowerA`: `lowerFunction fA = .ok vcA`);
* `checksA`: `lowerCheck fA vcA` and `IselCheck.threadCheck fA` hold (evaluated with
  `native_decide`), as do the facts the driver hypothesis reads off the function (no externs,
  no indirect calls, `verifiable`, `vcA.cfg` succeeds, no outgoing area);
* `inSubsetA`: `fA` is in the subset for every program `p` (it has no calls);
* **`driverHypA`**: the driver hypothesis exactly as `E2E.iselSim_relW` builds it, for `csem Γ.F
  fctx X` and the memory relation `E2E.RelW Γ fA c`, with the multi-threaded check on the same
  lowering `bl` — for every `Γ`, `fctx`, `X`, `c`, `env`, `p`, given only that the slot base is
  `Γ`'s and `X`'s symbols are `Γ`'s.
-/

namespace Concurrency.IselThread.Witness

open Backend Backend.Proof Backend.Proof.Driver E2E SegShape.Witness

/-- Whether an `Except` is a value. -/
def isOkB {ε α : Type} : Except ε α → Bool
  | .ok _ => true
  | .error _ => false

theorem ok_of_isOkB {ε α : Type} {e : Except ε α} (d : α) (h : isOkB e = true) :
    e = .ok (match e with | .ok x => x | .error _ => d) := by
  cases e with
  | ok x => rfl
  | error _ => cases h

/-- The VCode of `fA`. -/
def vcA : VCode := match lowerFunction fA with
  | .ok vc => vc
  | .error _ => default

theorem lowerA : lowerFunction fA = .ok vcA := by
  have h : isOkB (lowerFunction fA) = true := by native_decide
  unfold vcA
  revert h
  cases lowerFunction fA with
  | ok x => intro _; rfl
  | error e => intro h; cases h

/-- The checks on `fA` and its lowering. -/
theorem checksA : lowerCheck fA vcA = true ∧ IselCheck.threadCheck fA = true ∧
    fA.externs.isEmpty = true ∧ (indSigs fA).isEmpty = true ∧ verifiable fA = true ∧
    isOkB vcA.cfg = true ∧ vcA.outgoing = 0 := by
  native_decide

theorem externsA : fA.externs = [] := List.isEmpty_iff.mp checksA.2.2.1

theorem indSigsA : indSigs fA = [] := List.isEmpty_iff.mp checksA.2.2.2.1

/-- **`fA` is in the subset for every program** (it calls nothing). -/
theorem inSubsetA (p : Clif.Program) : InSubset p fA := by
  have hv := checksA.2.2.2.2.1
  simp only [verifiable, abiSigs, indSigsAbiOk, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq, and_assoc] at hv
  obtain ⟨hE, hf, hext, hind⟩ := hv
  have hno : ∀ fn e, fA.extern? fn = some e → False := fun fn e he => by
    simp [Clif.Function.extern?, externsA] at he
  exact ⟨hE, fun _ _ _ _ fn _ _ e he => (hno fn e he).elim,
    fun _ _ fn _ _ _ e he => (hno fn e he).elim, ⟨hf, hext⟩, hind⟩

theorem cfgA : ∃ ss ps, vcA.cfg = .ok (ss, ps) := by
  have hb := checksA.2.2.2.2.2.1
  revert hb
  cases vcA.cfg with
  | ok r => intro _; exact ⟨r.1, r.2, rfl⟩
  | error e => intro h; cases h

/-- **The driver hypothesis for `fA`**, as `E2E.iselSim_relW` builds it (with the multi-threaded
check on the same lowering): for `csem Γ.F fctx X` and `RelW Γ fA c`, when `fctx`'s slot base is
`Γ`'s slot offset and `X`'s symbols are `Γ`'s. -/
theorem driverHypA {Γ : E2E.Rel} {fctx : FnCtx} {X : ExtSem} {c : BitVec 64} {env : Clif.Env}
    {p : Clif.Program} (hslot : fctx.slotBase = Γ.slotOff)
    (hsym : ∀ n b, Γ.syms n = some b → X.sym n 0 = BitVec.ofNat 64 b) :
    ∃ ctx st0 R gn bl A, DriverHyp fA vcA ctx st0 R gn bl A (csem Γ.F fctx X) (RelW Γ fA c) env p ∧
      IselCheck.threadCheckBl fA bl = true := by
  obtain ⟨hlow, hthr, -, -, -, -, hout0⟩ := checksA
  obtain ⟨ctx, st0, R, gn, bl, A, hshape, hcert, hbr, hbl⟩ :=
    IselCheck.obligations_of_threadCheck hlow hthr
  have hsub := inSubsetA p
  have hX : XCallsOk env (fA.externs.map (·.2)) (RelW Γ fA c) X := by
    rw [externsA]; intro ext h; cases h
  have hXI : XCallsIndOk env (indSigs fA) (RelW Γ fA c) X := by
    rw [indSigsA]; intro s h; cases h
  have hRef : Refines Γ.F (csem Γ.F fctx X) := refines_csem Γ.F fctx X
  have hmem : MemRefines Γ.F Γ.slotOff Γ.syms (csem Γ.F fctx X) :=
    memRefines_csem Γ.F fctx X hslot hsym
  have hcalls := callsRefine_csem (F := Γ.F) (ctx := fctx) hX
  have hicalls := indCallsRefine_csem (F := Γ.F) (ctx := fctx) hXI hsym
    (fun _ _ _ h => h.1.1.symbols)
  have houtB : vcA.outgoing ≤ Γ.out := by rw [hout0]; exact Nat.zero_le _
  refine ⟨ctx, st0, R, gn, bl, A, {
    shape := hshape
    cert := hcert
    dsem := (driverSem_csem Γ.F fctx X).toDriverSemG
    insts := instCalls_of_rules lowerRulesCorrect_program excludedUnmatchable callRulesCorrect
      indRulesCorrect memRulesCorrect_program hRef (mrStable_relW Γ fA c) hcalls hicalls hmem
      (outArgsOk_relW Γ fA c) (callsStack_mono (callsStack_of_check hlow) houtB)
      (indStack_mono (indStack_of_check hlow) houtB) (memRelOk_relW Γ fA c)
    terms := termCalls_of_rules lowerTermRulesCorrect termUnmatchable branchRulesCorrect
      branchExcludedUnmatchable hRef (mrStable_relW Γ fA c)
    ext := fun B hB st hst fn args hi e he => hsub.externCalls B hB st hst fn args hi e he
    indSig := indSig_of_subset hsub
    subE := hsub.subsetE
    entryLocs := entryOk_of_check hlow
    brIdx := hbr
    noTail := noTail_of_subset hsub
    tries := ⟨_, tryCalls_of_rules tryRulesCorrect tryUnmatchable hRef (mrStable_relW Γ fA c) hmem
      (outArgsOk_relW Γ fA c) hcalls, tryStack_mono (tryStack_of_check hlow) houtB⟩
    tryExt := hsub.tryExterns
    tryInd := tryIndCalls_of_rules tryIndRulesCorrect tryIndUnmatchable hRef
      (mrStable_relW Γ fA c) hmem (outArgsOk_relW Γ fA c)
      (indStack_mono (indStack_of_check hlow) houtB) hicalls
    tryIndSig := tryIndSig_of_subset hsub
    cfg := cfgA }, hbl⟩

end Concurrency.IselThread.Witness
