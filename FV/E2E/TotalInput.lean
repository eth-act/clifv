import FV.E2E.SizeIn
import FV.E2E.DeadCleanupSize
import FV.Backend.Proof.DeadCleanupPrepareMap
import FV.Backend.Proof.IselPrgDriver
import FV.Backend.Proof.PrepareTotal
import FV.E2E.LinkScopeInputDefs

/-! # The backend's end-to-end theorems, total on input conditions alone (V7)

`backend_correct_final_total_emit_input` (`FV/E2E/SizeIn.lean`) and
`backend_correct_final_cleanup_total_emit_input` (`FV/E2E/DeadCleanupSize.lean`) still take the
success of `lowerFunction` (`hl`) and of `prepare` (`hp`) as premises. Here they follow from the
decidable input conditions `driverInB` and `iselInB` (`Prg.lowerFunction_ok_input`, the ISLE
progress analysis) with the scope conditions (`Prep.prepare_ok`); the cleanup pipeline's
`prepare (prune vc)` from `prepare vc` (`prune_prepare_ok`). Every premise on the code is a
condition on the CLIF function `f`: the lowering, `prepare`, the allocation, emission and layout
succeed, and the machine code refines the CLIF run under the contract and run premises.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

set_option linter.unusedVariables false in -- the conclusion's premises are named for readability
/-- **The backend's end-to-end theorem, total from the input conditions** (V7):
`backend_correct_final_total_emit_input` without the premises `lowerFunction f = .ok vc` and
`prepare vc = .ok vcp` — for every function in scope (`InSubset`, `dominatedB`, `lowerScopeB`,
`arityOkB`, `entryParamsB`, `extendsWidenB`, `sizeOkB`, `driverInB`, `iselInB`) and every answer
`ra` of the untrusted allocator, `lowerFunction`, `prepare`, `lowerAllocReady`, emission and
layout succeed, and the machine code refines the CLIF run. -/
theorem backend_correct_final_total_input {p : Clif.Program} {f : Clif.Function} {k : Nat}
    (hsub : InSubset p f) (hd : dominatedB f = true) (hs : lowerScopeB f = true)
    (har : Spill.arityOkB f = true) (hent : Spill.entryParamsB f = true)
    (hw : extendsWidenB f = true) (hsz : sizeOkB f = true) (hdrv : driverInB f = true)
    (hin : Prg.iselInB f = true) (ra : Except String RFunc) :
    ∃ vc vcp, lowerFunction f = .ok vc ∧ Backend.prepare vc = .ok vcp ∧
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
      ArmRefines fb base ra' (ArmStepX X H fa) s (Clif.runLoop env p fuel cs) := by
  obtain ⟨vc, hl⟩ := Prg.lowerFunction_ok_input hsub.subsetE hsub.abiSigs.1 hd hs har hent hw hdrv hin
  obtain ⟨vcp, hp⟩ := Prep.prepare_ok hd hs hl
  exact ⟨vc, vcp, hl, hp, backend_correct_final_total_emit_input hsub hd hs har hw hsz hl hp ra⟩

set_option linter.unusedVariables false in
/-- **The cleanup pipeline's end-to-end theorem, total from the input conditions** (V7):
`backend_correct_final_cleanup_total_emit_input` without the premises `lowerFunction f = .ok vc`
and `prepare (cleanupStage f vc) = .ok vcp` (the production cleanup stage; formerly
`prepare (prune vc)`: the compiler now runs Cranelift's skip of unused instructions first). -/
theorem backend_correct_final_cleanup_total_input {p : Clif.Program} {f : Clif.Function} {k : Nat}
    (hsub : InSubset p f) (hd : dominatedB f = true) (hs : lowerScopeB f = true)
    (har : Spill.arityOkB f = true) (hent : Spill.entryParamsB f = true)
    (hw : extendsWidenB f = true) (hsz : sizeOkB f = true) (hdrv : driverInB f = true)
    (hin : Prg.iselInB f = true) (ra : Except String RFunc) :
    ∃ vc vcp, lowerFunction f = .ok vc ∧ Backend.prepare (cleanupStage f vc) = .ok vcp ∧
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
      ArmRefines fb base ra' (ArmStepX X H fa) s (Clif.runLoop env p fuel cs) := by
  obtain ⟨vc, hl⟩ := Prg.lowerFunction_ok_input hsub.subsetE hsub.abiSigs.1 hd hs har hent hw hdrv hin
  obtain ⟨vcp, hp⟩ := Prep.prepare_ok hd hs hl
  have hp' := cleanupStage_prepare_ok (f := f) hp
  exact ⟨vc, _, hl, hp',
    backend_correct_final_cleanup_total_emit_input hsub hd hs har hw hsz hl hp' ra⟩

/-- **Non-vacuity**: the per-function input conditions of both theorems (`fnScopeInB`, which
contains `InSubset`'s `functionE` and `sigAbiOk`) hold on the loop witness `driverWitness` and the
`call`/`try_call` witness `driverWitnessTry`, checked by the kernel, except `dominatedB`: its
availability fixpoint (`inFix`) uses `Std.HashMap`/`Std.HashSet`, which the kernel does not reduce
(`USize`), so it is stated as the premise here; `lean-e2e-check` and `lean-link --verified`
evaluate it (every function of the corpus and the crates, `docs/TO-PROVE.md` §3 V7). -/
theorem backend_correct_final_total_input_witness :
    (dominatedB driverWitness = true → LinkCheck.fnScopeInB driverWitness = true) ∧
    (dominatedB driverWitnessTry = true → LinkCheck.fnScopeInB driverWitnessTry = true) := by
  refine ⟨fun h => ?_, fun h => ?_⟩ <;>
  · simp only [LinkCheck.fnScopeInB, h, Bool.and_true]
    decide +kernel

end E2E
