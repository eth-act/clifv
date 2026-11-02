import FV.E2E.SpillAvail
import FV.E2E.SpillCtlWitness
import FV.Backend.Proof.KillDriver
import FV.Backend.Proof.KillTryDefs
import FV.Backend.Proof.KillPrep

/-!
# `SpillKillFree` and `SpillAccepted` proven (V4 (a))

`spillKillFree : SpillKillFree`: the prepared VCode of in-scope input passes `Spill.killFreeB`.

* `Kill.killRunsHyp` (`FV/Backend/Proof/KillDriver.lean`): every ISLE run of the driver emits
  code whose killed vregs are fresh vregs of the run and whose uses are CLIF values' vregs or
  vregs of the run it does not kill (a uniform invariant of the ISLE interpreter,
  `Isle.Interp.uSound`/`uRoot` in `KillGen.lean`; the killing forms are built only inside
  `atomic_rmw_loop`, `atomic_cas_loop` and `br_table_impl`, checked as oracles);
* `Kill.tryDefsExact` (`KillTryDefs.lean`): a `try_call`'s call defines exactly its result
  vregs, in order;
* `Kill.killFreeB_lower` (`KillAssemble.lean`): the driver's VCode passes `killFreeB` (disjoint
  vreg ranges of the runs, alias resolution, `try_call` edge blocks);
* `Spill.killFreeB_prepare_of` (`KillPrep.lean`): `prepare` keeps it.

Then `spillAccepted : SpillAccepted` (`spillAccepted_of_killFree` with the proven step 4), and
`backend_correct_final_alloc_proven`: the backend's end-to-end theorem for the allocation it
lowers (regalloc2's if `checkAlloc` accepts it, else the spill allocation), with neither a
`SpillAccepted` nor a `checkAlloc` premise.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- **`SpillKillFree`, proven.** -/
theorem spillKillFree : SpillKillFree :=
  fun _ _ _ _ hsub har hd hs hl hp =>
    Spill.killFreeB_prepare_of hd hs har hl
      (Kill.killFreeB_lower Kill.killRunsHyp Kill.tryDefsExact hd hs (abiSigsOk_of_inSubset hsub) har hl)
      hp

/-- **`SpillAccepted`, proven**: `checkAlloc` accepts the spill allocation of every in-scope
function's prepared VCode. -/
theorem spillAccepted : SpillAccepted := spillAccepted_of_killFree Spill.spillStep4 spillKillFree

/-- **The backend's end-to-end theorem for the allocation the backend lowers** (V4 (a)):
`backend_correct_final_alloc` with `SpillAccepted` proven: for any answer `ra` of the untrusted
allocator (regalloc2), the allocation `allocResult vcp ra` (regalloc2's if `checkAlloc` accepts it,
else `spillAlloc vcp`) is lowered correctly; no allocation-checker premise. -/
theorem backend_correct_final_alloc_proven {p : Clif.Program}
    {f : Clif.Function} {k : Nat} {vc vcp : VCode} {ra : Except String RFunc} {rf : RFunc}
    {af : AFunc} {fa : FnAsm}
    {fb : FnBin} (hsub : InSubset p f) (hd : dominatedB f = true) (hs : lowerScopeB f = true)
    (har : Spill.arityOkB f = true)
    (hl : lowerFunction f = .ok vc) (hp : Backend.prepare vc = .ok vcp)
    (hrf : rf = allocResult vcp ra) (ha : lowerRFunc vcp rf = .ok af)
    (he : emitFunc k af = .ok fa) (hla : fa.layout = .ok fb)
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    {K : Nat}
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : (∃ B ∈ f.blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : hasTls f = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hX : ∀ s, XCallsOk env (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hXI : ∀ s, XCallsIndOk env (indSigs f) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {base ra' : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra' s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ArmRefines fb base ra' (ArmStepX X H fa) s (Clif.runLoop env p fuel cs) :=
  backend_correct_final_alloc spillAccepted hsub hd hs har hl hp hrf ha he hla hC hCT hTls hX hXI
    hsym hslot hent hres hbe hargs hcs hrel htr fuel

/-! ## Non-vacuity -/

/-- **Non-vacuity of `backend_correct_final_alloc_proven`**: on `lowerWitness`, with regalloc2
absent, the input conditions hold, the pipeline runs through the spill allocation, `checkAlloc`
accepts it and `lowerRFunc` lowers it (`backend_correct_final_alloc_witness`); and on
`rmwWitness` (an LL/SC loop, so killed vregs exist) `killFreeB` holds as `spillKillFree` states
(`spillKillFree_witness`). -/
theorem backend_correct_final_alloc_proven_witness :
    (Dominated lowerWitness ∧ LowerScope lowerWitness ∧ Spill.arityOkB lowerWitness = true ∧
      ∃ vc vcp af, lowerFunction lowerWitness = .ok vc ∧ Backend.prepare vc = .ok vcp ∧
        AllocChecked vcp (spillAlloc vcp) ∧
        lowerRFunc vcp (allocResult vcp (.error "regalloc2 absent")) = .ok af) ∧
    (Dominated rmwWitness ∧ LowerScope rmwWitness ∧ Spill.ArityOk rmwWitness ∧
      ∃ vc vcp, lowerFunction rmwWitness = .ok vc ∧ Backend.prepare vc = .ok vcp ∧
        Spill.killFreeB vcp = true ∧ Spill.SpillAvail vcp (Spill.killD vcp) ∧
        ∃ v, Spill.killD vcp 1 v = false) :=
  ⟨backend_correct_final_alloc_witness, spillKillFree_witness⟩

end E2E
