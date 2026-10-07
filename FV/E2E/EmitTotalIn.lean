import FV.E2E.EmitTotal
import FV.E2E.EmitCondsLower
import FV.Backend.Proof.IselEmitDriver

/-!
# Emission conditions from the input (V6c)

`backend_correct_final_total_emit` (V6b) assumed `emitCondsB vcp` on the prepared VCode. Three
of its four parts are facts about instruction selection's output, proven here from the ISLE rule
data (`Driver.iselEmit`: the emission analysis `IselEmit*`, a fifth instantiation of V3's
abstract interpreter, with the table `emitTab`; assembled by `emitConds_lower`):

* `immsOkB` (immediates in the encoder's ranges) and `noAlwaysB` (no `al`/`nv` branch);
* `branchTargetsOkB` (branch-target instructions only block-final, so `VCode.cfg` resolves their
  targets to block labels).

They hold for every in-scope function with the new decidable input condition `extendsWidenB f`
(every `uextend`/`sextend` widens — CLIF's verifier rule, which the run semantics only checks at
run time: a non-widening `uextend.i32` of an `i64` selects an `Extend` from 64 bits, which has no
encoding). The size bound `spillSizeOkB vcp` remains a condition on the prepared VCode.

* `emitCondsB_of_input`: `emitCondsB vcp` from `lowerScopeB`, `extendsWidenB` and `spillSizeOkB`.
* `backend_correct_final_total_emit_in`: `backend_correct_final_total_emit` with `emitCondsB`
  replaced by `extendsWidenB f` and `spillSizeOkB vcp`.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- **`emitCondsB` from the input**: for an in-scope function whose extends widen, the prepared
VCode meets `emitCondsB` given the size bound. -/
theorem emitCondsB_of_input {f : Clif.Function} {vc vcp : VCode} (hs : lowerScopeB f = true)
    (hw : extendsWidenB f = true) (hl : lowerFunction f = .ok vc)
    (hp : Backend.prepare vc = .ok vcp) (hsz : spillSizeOkB vcp = true) : emitCondsB vcp = true := by
  obtain ⟨h1, h2, h3⟩ := emitConds_lower (lowerScope_of hs) (iselEmit (lowerScope_of hs) hw) hl hp
  simp [emitCondsB, hsz, h1, h2, h3]

set_option linter.unusedVariables false in -- the conclusion's premises are named for readability
/-- **The backend's end-to-end theorem, total including emission and layout, with the emission
conditions from the input** (V6c): for every in-scope function (`InSubset`, `dominatedB`,
`lowerScopeB`, `arityOkB`) whose extends widen (`extendsWidenB`) and whose prepared VCode meets
the size bound `spillSizeOkB`, and every answer `ra` of the untrusted allocator, the backend's
allocation `lowerAllocReady`, emission and layout succeed, and the machine code refines the CLIF
run under `backend_correct_final`'s contract, link-time and run premises. Compared with
`backend_correct_final_total_emit`, `immsOkB`, `noAlwaysB` and `branchTargetsOkB` are proven. -/
theorem backend_correct_final_total_emit_in {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} (hsub : InSubset p f) (hd : dominatedB f = true) (hs : lowerScopeB f = true)
    (har : Spill.arityOkB f = true) (hw : extendsWidenB f = true)
    (hl : lowerFunction f = .ok vc) (hp : Backend.prepare vc = .ok vcp)
    (hsz : spillSizeOkB vcp = true)
    (ra : Except String RFunc) :
    ∃ af, lowerAllocReady vcp ra = .ok af ∧
      ∃ fa fb, emitFunc k af = .ok fa ∧ fa.layout = .ok fb ∧
      ∀ {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
        {K : Nat},
      ∀
        (hC : ∀ s, CalleeOk
          (frameW K (RAFrame.compute vcp (allocResult vcp (readyAnswer vcp ra))).intBase
            (RAFrame.compute vcp (allocResult vcp (readyAnswer vcp ra))).size af s) K X H
            vcp.CallSite)
        (hCT : (∃ B ∈ f.blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
          (frameW K (RAFrame.compute vcp (allocResult vcp (readyAnswer vcp ra))).intBase
            (RAFrame.compute vcp (allocResult vcp (readyAnswer vcp ra))).size af s) X H
            vcp.TrySite)
        (hTls : hasTls f = true → ∀ s, TlsOk
          (frameW K (RAFrame.compute vcp (allocResult vcp (readyAnswer vcp ra))).intBase
            (RAFrame.compute vcp (allocResult vcp (readyAnswer vcp ra))).size af s) K X H)
        (hX : ∀ s, XCallsOk env (f.externs.map (·.2)) (fun sl cm w =>
          Rel.holds ⟨frameW K (RAFrame.compute vcp (allocResult vcp (readyAnswer vcp ra))).intBase
            (RAFrame.compute vcp (allocResult vcp (readyAnswer vcp ra))).size af s, syms,
            slotOff, (RAFrame.compute vcp (allocResult vcp (readyAnswer vcp ra))).intBase⟩
            f sl cm w) X)
        (hXI : ∀ s, XCallsIndOk env (indSigs f) (fun sl cm w =>
          Rel.holds ⟨frameW K (RAFrame.compute vcp (allocResult vcp (readyAnswer vcp ra))).intBase
            (RAFrame.compute vcp (allocResult vcp (readyAnswer vcp ra))).size af s, syms,
            slotOff, (RAFrame.compute vcp (allocResult vcp (readyAnswer vcp ra))).intBase⟩
            f sl cm w) X)
        (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
        (hslot : af.slotBase = slotOff)
        {base ra' : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
        (hent : AbiEntry fb base ra' s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
        (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
        (hrel : Rel.holds ⟨frameW K
            (RAFrame.compute vcp (allocResult vcp (readyAnswer vcp ra))).intBase
            (RAFrame.compute vcp (allocResult vcp (readyAnswer vcp ra))).size af s,
          syms, slotOff, (RAFrame.compute vcp (allocResult vcp (readyAnswer vcp ra))).intBase⟩
          f cs.frame.slots cs.mem w₀)
        (htr : TrapsExplicit env p cs) (fuel : Nat),
      ArmRefines fb base ra' (ArmStepX X H fa) s (Clif.runLoop env p fuel cs) :=
  backend_correct_final_total_emit hsub hd hs har hl hp (emitCondsB_of_input hs hw hl hp hsz) ra

/-- **Non-vacuity of `backend_correct_final_total_emit_in`**: `lowerWitness` (whose other input
conditions `backend_correct_final_total_witness` discharges) has widening extends, and its
prepared VCode meets the size bound. -/
theorem backend_correct_final_total_emit_in_witness :
    extendsWidenB lowerWitness = true ∧
    ∃ vc vcp, lowerFunction lowerWitness = .ok vc ∧ Backend.prepare vc = .ok vcp ∧
      spillSizeOkB vcp = true := by
  obtain ⟨vc, vcp, -, hl, hp, hem, -⟩ := backend_correct_final_total_emit_witness
  refine ⟨by native_decide, vc, vcp, hl, hp, ?_⟩
  simp only [emitCondsB, Bool.and_eq_true] at hem
  exact hem.1.1.1

end E2E
