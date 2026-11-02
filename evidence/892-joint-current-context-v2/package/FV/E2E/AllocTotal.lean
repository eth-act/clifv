import FV.E2E.SpillLower
import FV.E2E.SpillKillFree
import FV.E2E.SpillCtlCheck

/-!
# The backend is total on in-scope input (V5)

`lowerRFunc_spillAlloc`: for every function in scope (`InSubset`, `Dominated`, `LowerScope`,
`ArityOk`), `lowerRFunc` lowers the spill allocation of its prepared VCode (there is no frame-size
limit: slots beyond 32 KiB are addressed through x16). The parts are `lowerRFunc_spill_of`
(`FV/E2E/SpillLower.lean`: the local facts `spillLocalAll`, the CFG `Spill.cfg_ok_of_prepare`) and
`ctlInsts_pipeline` (`FV/E2E/SpillCtlCheck.lean`: `ctlInstOk` everywhere, `Args` first in block 0).

The backend lowers `allocResult vcp ra`: regalloc2's allocation if `checkAlloc` accepts it and
`lowerRFunc` lowers it, else the spill allocation (`lowerAlloc`, `lowerAlloc_eq_lowerRFunc`). So
`lowerAlloc_total`: whatever regalloc2 answers, `lowerAlloc` succeeds, and
`backend_correct_final_total` is `backend_correct_final_alloc_proven` without the premise that the
allocation is lowered: only emission (`emitFunc`, `layout`: V6's branch ranges) remains as a
premise about the compiler's success.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.Proof.Cov

/-- **`lowerRFunc` lowers the spill allocation of every in-scope function** (V5). -/
theorem lowerRFunc_spillAlloc {p : Clif.Program} {f : Clif.Function} {vc vcp : VCode}
    (hsub : InSubset p f) (har : Spill.ArityOk f) (hd : Dominated f) (hs : LowerScope f)
    (hl : lowerFunction f = .ok vc) (hp : Backend.prepare vc = .ok vcp) :
    ∃ af, lowerRFunc vcp (spillAlloc vcp) = .ok af := by
  obtain ⟨ss, ps, hcfg⟩ := Spill.cfg_ok_of_prepare hp (prepDomain_of_lower hs hl hs.nonempty)
  obtain ⟨hins, h0⟩ := ctlInsts_pipeline hsub hd hs hl hp
  exact lowerRFunc_spill_of hcfg (spillLocalAll p f vc vcp hsub har hd hs hl hp) hins h0

/-- **Allocation and lowering are total** (V5): for every in-scope function and every answer `ra`
of the untrusted allocator (or none), `lowerAlloc` succeeds. -/
theorem lowerAlloc_total {p : Clif.Program} {f : Clif.Function} {vc vcp : VCode}
    (hsub : InSubset p f) (har : Spill.ArityOk f) (hd : Dominated f) (hs : LowerScope f)
    (hl : lowerFunction f = .ok vc) (hp : Backend.prepare vc = .ok vcp)
    (ra : Except String RFunc) : ∃ af, lowerAlloc vcp ra = .ok af := by
  rw [lowerAlloc_eq_lowerRFunc]
  have hsp := lowerRFunc_spillAlloc hsub har hd hs hl hp
  unfold allocResult
  cases ra with
  | error e => exact hsp
  | ok rf =>
    simp only
    by_cases hc : (checkAlloc vcp rf).isOk = true
    · simp only [hc, ite_true]
      cases hlr : lowerRFunc vcp rf with
      | ok af => exact ⟨af, hlr⟩
      | error e => exact hsp
    · simp only [hc]; exact hsp

set_option linter.unusedVariables false in -- the conclusion's premises are named for readability
/-- **The backend's end-to-end theorem, total** (V5): for every in-scope function and every
answer `ra` of the untrusted allocator, the backend's allocation and lowering succeed
(`lowerAlloc vcp ra = .ok af`), and if emission and layout succeed, the machine code refines the
CLIF run under `backend_correct_final`'s contract, link-time and run premises. Compared with
`backend_correct_final_alloc_proven`, the lowering premise `ha` is gone. -/
theorem backend_correct_final_total {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} (hsub : InSubset p f) (hd : dominatedB f = true) (hs : lowerScopeB f = true)
    (har : Spill.arityOkB f = true)
    (hl : lowerFunction f = .ok vc) (hp : Backend.prepare vc = .ok vcp)
    (ra : Except String RFunc) :
    ∃ af, lowerAlloc vcp ra = .ok af ∧
      ∀ {fa : FnAsm} {fb : FnBin}, emitFunc k af = .ok fa → fa.layout = .ok fb →
      ∀ {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
        {K : Nat},
      ∀
        (hC : ∀ s, CalleeOk
          (frameW K (RAFrame.compute vcp (allocResult vcp ra)).intBase
            (RAFrame.compute vcp (allocResult vcp ra)).size af s) K X H vcp.CallSite)
        (hCT : (∃ B ∈ f.blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
          (frameW K (RAFrame.compute vcp (allocResult vcp ra)).intBase
            (RAFrame.compute vcp (allocResult vcp ra)).size af s) X H vcp.TrySite)
        (hTls : hasTls f = true → ∀ s, TlsOk
          (frameW K (RAFrame.compute vcp (allocResult vcp ra)).intBase
            (RAFrame.compute vcp (allocResult vcp ra)).size af s) K X H)
        (hX : ∀ s, XCallsOk env (f.externs.map (·.2)) (fun sl cm w =>
          Rel.holds ⟨frameW K (RAFrame.compute vcp (allocResult vcp ra)).intBase
            (RAFrame.compute vcp (allocResult vcp ra)).size af s, syms,
            slotOff, (RAFrame.compute vcp (allocResult vcp ra)).intBase⟩ f sl cm w) X)
        (hXI : ∀ s, XCallsIndOk env (indSigs f) (fun sl cm w =>
          Rel.holds ⟨frameW K (RAFrame.compute vcp (allocResult vcp ra)).intBase
            (RAFrame.compute vcp (allocResult vcp ra)).size af s, syms,
            slotOff, (RAFrame.compute vcp (allocResult vcp ra)).intBase⟩ f sl cm w) X)
        (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
        (hslot : af.slotBase = slotOff)
        {base ra' : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
        (hent : AbiEntry fb base ra' s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
        (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
        (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp (allocResult vcp ra)).intBase
            (RAFrame.compute vcp (allocResult vcp ra)).size af s,
          syms, slotOff, (RAFrame.compute vcp (allocResult vcp ra)).intBase⟩ f cs.frame.slots cs.mem
          w₀)
        (htr : TrapsExplicit env p cs) (fuel : Nat),
      ArmRefines fb base ra' (ArmStepX X H fa) s (Clif.runLoop env p fuel cs) := by
  obtain ⟨af, ha⟩ := lowerAlloc_total hsub (Spill.arityOk_of har) (dominated_of hd)
    (lowerScope_of hs) hl hp ra
  refine ⟨af, ha, ?_⟩
  intro fa fb he hla X H syms slotOff env K hC hCT hTls hX hXI hsym hslot base ra' s w₀ args cs
    hent hres hbe hargs hcs hrel htr fuel
  exact backend_correct_final_alloc_proven hsub hd hs har hl hp rfl (lowerAlloc_eq ha) he hla hC hCT
    hTls hX hXI hsym hslot hent hres hbe hargs hcs hrel htr fuel

/-! ## Non-vacuity -/

/-- **Non-vacuity of `backend_correct_final_total`**: on `lowerWitness`, the input conditions
(other than `InSubset`, as in `backend_correct_final_alloc_witness`) hold, and `lowerAlloc`
succeeds with regalloc2 absent. -/
theorem backend_correct_final_total_witness :
    Dominated lowerWitness ∧ LowerScope lowerWitness ∧ Spill.arityOkB lowerWitness = true ∧
      ∃ vc vcp af, lowerFunction lowerWitness = .ok vc ∧ Backend.prepare vc = .ok vcp ∧
        lowerAlloc vcp (.error "regalloc2 absent") = .ok af := by
  obtain ⟨hd, hs, har, vc, vcp, af, hl, hp, -, hr⟩ := backend_correct_final_alloc_witness
  exact ⟨hd, hs, har, vc, vcp, af, hl, hp, (lowerAlloc_eq_lowerRFunc _ _).trans hr⟩

end E2E
