import FV.Link.DeadCleanupExeSource
import FV.Link.NonVacuityExeSource

/-! # The shipped compiler's source theorems with the `__*ti3` helpers as the only outside code

`Link.SourceWitness.compileExe_correct_source_helper` for `Link.DeadCleanup.compileExe`: the base
premises of `helperBase` (`Link.SourceWitness.baseOk_helper`, generic in the compiled results, so
also the cleanup input's) decided on the program, the hooks (the closed base environment's), the
`i128` contracts, and the source run's memory bound (`Link.SourceWitness.srcBounded`). Instances:
`crate-proofs/Crates/DeadCleanupExeSourceWitness.lean`,
`crate-proofs/Crates/DeadCleanupExePeakWitness.lean`.
-/

namespace Link.DeadCleanup.SourceWitness

open Clif E2E E2E.LinkCheck E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes E2E.BinCheck
  E2E.LegalProgram Opt.Legal Opt.Legalize128 Backend Backend.Proof Link.SourceWitness

/-- The hooks of `helperBase` are `closedBase`'s (the cleanup input's `HooksSim`). -/
theorem hooksSim_helper (I : LinkInput) : HooksSim I helperBase :=
  ⟨(E2E.DeadCleanupExecBytes.hooksSim_closed I).call,
    (E2E.DeadCleanupExecBytes.hooksSim_closed I).tls⟩

/-- **`Link.DeadCleanup.compileExe_correct_source` under `helperBase`**. -/
theorem compileExe_correct_source_helper {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExe S file0 = .ok file) (hsrc : SrcScopeB S.inputCleanup = true)
    (htls : ∀ g ∈ (prog S.inputCleanup).funcs, Backend.hasTls g = false)
    (hdiv : ∀ g ∈ (prog S.inputCleanup).funcs, ∀ e ∈ g.externs,
      (prog S.inputCleanup).func? e.2.name = none → Clif.Rust.isDivHelper e.2.name = false)
    (hind : ∀ g ∈ (prog S.inputCleanup).funcs, Clif.IndFree g)
    (hsigs : ∀ g ∈ (prog S.inputCleanup).funcs, Backend.indSigs g = [])
    (hslots : ∀ g ∈ S.inputCleanup.srcProg.funcs, g.slots = [])
    {n : String} {f : Clif.Function} (hf : S.inputCleanup.srcProg.func? n = some f)
    (hc : ¬ DeadCleanupStackBound.CycleFrom
      (DeadCleanupStackBound.Calls S.inputCleanup S.inputCleanup.resultsCleanup) (legalize f))
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.inputCleanup (BinCheck.roByte S.inputCleanup S.data) (legalize f)
      (DeadCleanupStackBound.stackFn S.inputCleanup (legalize f)) r args' cs'.mem)
    (hr : ClifRun S.inputCleanup helperBase (legalize f) r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hM : MemBounded cs.mem) (M : Nat) :
    ∀ vals cm, Clif.runLoop helperEnv S.inputCleanup.srcProg M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefines (art S.inputCleanup (legalize f)).fb (art S.inputCleanup (legalize f)).base
          (xreg 30 r) (step S.inputCleanup helperBase file) r
          (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.returned vals' cm) :=
  (compileExe_correct_source h hsrc helperBase (baseOk_helper htls hdiv hind hsigs)
    (hooksSim_helper _) (fun _ => ⟨helperOk, extLegal, keepsBounded⟩)
    (fun ⟨g, hg, hn⟩ => absurd (hind g hg) hn) hf hc hX ho hr hcs hexp hsl hmem
    (srcBounded hsrc hslots (Clif.Program.func?_some hf).1 hcs hM) M).1

/-- **`Link.DeadCleanup.compileExe_correct_source_peak` under `helperBase`**. -/
theorem compileExe_correct_source_peak_helper {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExe S file0 = .ok file) (hsrc : SrcScopeB S.inputCleanup = true)
    (htls : ∀ g ∈ (prog S.inputCleanup).funcs, Backend.hasTls g = false)
    (hdiv : ∀ g ∈ (prog S.inputCleanup).funcs, ∀ e ∈ g.externs,
      (prog S.inputCleanup).func? e.2.name = none → Clif.Rust.isDivHelper e.2.name = false)
    (hind : ∀ g ∈ (prog S.inputCleanup).funcs, Clif.IndFree g)
    (hsigs : ∀ g ∈ (prog S.inputCleanup).funcs, Backend.indSigs g = [])
    (hslots : ∀ g ∈ S.inputCleanup.srcProg.funcs, g.slots = [])
    {n : String} {f : Clif.Function} (hf : S.inputCleanup.srcProg.func? n = some f) (d : Nat)
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.inputCleanup (BinCheck.roByte S.inputCleanup S.data) (legalize f)
      (frameDrop (art S.inputCleanup (legalize f)).af +
        (S.inputCleanup.D * d + pbMax S.inputCleanup)) r args' cs'.mem)
    (hr : ClifRun S.inputCleanup helperBase (legalize f) r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hM : MemBounded cs.mem) (hd : Clif.DepthLe helperEnv S.inputCleanup.srcProg d cs)
    (M : Nat) :
    ∀ vals cm, Clif.runLoop helperEnv S.inputCleanup.srcProg M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefines (art S.inputCleanup (legalize f)).fb (art S.inputCleanup (legalize f)).base
          (xreg 30 r) (step S.inputCleanup helperBase file) r
          (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.returned vals' cm) :=
  (compileExe_correct_source_peak h hsrc helperBase (baseOk_helper htls hdiv hind hsigs)
    (hooksSim_helper _) (fun _ => ⟨helperOk, extLegal, keepsBounded⟩)
    (fun ⟨g, hg, hn⟩ => absurd (hind g hg) hn) hf d hX ho hr hcs hexp hsl hmem
    (srcBounded hsrc hslots (Clif.Program.func?_some hf).1 hcs hM) hd M).1

end Link.DeadCleanup.SourceWitness
