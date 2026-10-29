module

public import FV.Link.OptExe
public import FV.Link.DeadCleanupOptExe
public import FV.Link.NonVacuityExeSource
public import FV.Link.NonVacuityDeadCleanupExeSource

@[expose] public section

/-! # `compileExeOpt_correct_source` with the `__*ti3` helpers as the only outside code

`compileExeOpt_correct_source_helper`: `Link.compileExeOpt_correct_source` under
`Link.SourceWitness.helperBase` (the closed base environment with the trusted Rust `__*ti3`
helpers in CLIF), its premises decided on the input's and the optimised input's programs as for
`compileExe_correct_source_helper` (`FV/Link/NonVacuityExeSource.lean`); the helpers return the
caller's memory, so they keep the link-time symbols (`envKeepsSymbols_helper`, the mid-end's
contract). `Link.DeadCleanup.SourceWitness.compileExeOpt_correct_source_helper`: the same for the
shipped compiler. Instances: `crate-proofs/Crates/CompileExeOptSourceWitness.lean`,
`crate-proofs/Crates/DeadCleanupExeOptSourceWitness.lean`.
-/

namespace Link.SourceWitness

open Clif E2E E2E.LinkCheck E2E.Binary E2E.ExecBytes E2E.BinCheck E2E.LegalProgram Opt.Legal
  Opt.Legalize128 Backend Backend.Proof

/-- The helpers keep the link-time symbols. -/
theorem envKeepsSymbols_helper : Opt.EnvKeepsSymbols helperEnv := fun _ _ he _ _ _ _ hr => by
  rw [helper_mem he hr]

/-- **`compileExeOpt_correct_source` under `helperBase`**: the base premises decided on the
optimised program (no TLS, no indirect call, no `__*ti3` helper declared outside the program),
the input's program without indirect calls, no stack slot in the source program, the source
run's memory bound from an entry memory with valid ranges below `2^64`. -/
theorem compileExeOpt_correct_source_helper {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExeOpt S file0 = .ok file) (hsrc : SrcScopeB S.input = true)
    (htls : ∀ g ∈ (prog S.opt.input).funcs, Backend.hasTls g = false)
    (hdiv : ∀ g ∈ (prog S.opt.input).funcs, ∀ e ∈ g.externs,
      (prog S.opt.input).func? e.2.name = none → Clif.Rust.isDivHelper e.2.name = false)
    (hind : ∀ g ∈ (prog S.opt.input).funcs, Clif.IndFree g)
    (hsigs : ∀ g ∈ (prog S.opt.input).funcs, Backend.indSigs g = [])
    (hind0 : ∀ g ∈ (prog S.input).funcs, Clif.IndFree g)
    (hslots : ∀ g ∈ S.input.srcProg.funcs, g.slots = [])
    {n : String} {f f' : Clif.Function} (hf : S.input.srcProg.func? n = some f)
    (hf' : (prog S.opt.input).func? n = some f')
    (hc : ¬ StackBound.CycleFrom (StackBound.Calls S.opt.input S.opt.input.results) f')
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.opt.input (BinCheck.roByte S.opt.input S.opt.data) f'
      (StackBound.stackFn S.opt.input f') r args' cs'.mem)
    (hr : ClifRun S.opt.input helperBase f' r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hM : MemBounded cs.mem) (M : Nat) :
    ∀ vals cm, Clif.runLoop helperEnv S.input.srcProg M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefines (art S.opt.input f').fb (art S.opt.input f').base (xreg 30 r)
          (step S.opt.input helperBase file) r (RelocAt S.opt.input) (.returned vals' cm) := by
  have hbnd := srcBounded hsrc hslots (Clif.Program.func?_some hf).1 hcs hM
  exact (compileExeOpt_correct_source h hsrc helperBase (baseOk_helper htls hdiv hind hsigs)
    (hooksSim_helper _) envKeepsSymbols_helper (fun _ => ⟨helperOk, extLegal, keepsBounded⟩)
    (fun ⟨g, hg, hn⟩ => absurd (hind0 g hg) hn) hf hf' hc hX ho hr hcs hexp hsl hmem hbnd M).1

end Link.SourceWitness

namespace Link.DeadCleanup.SourceWitness

open Clif E2E E2E.LinkCheck E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes E2E.BinCheck
  E2E.LegalProgram Opt.Legal Opt.Legalize128 Backend Backend.Proof Link.SourceWitness

/-- **`Link.DeadCleanup.compileExeOpt_correct_source` under `helperBase`**. -/
theorem compileExeOpt_correct_source_helper {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExeOpt S file0 = .ok file) (hsrc : SrcScopeB S.inputCleanup = true)
    (htls : ∀ g ∈ (prog S.opt.inputCleanup).funcs, Backend.hasTls g = false)
    (hdiv : ∀ g ∈ (prog S.opt.inputCleanup).funcs, ∀ e ∈ g.externs,
      (prog S.opt.inputCleanup).func? e.2.name = none → Clif.Rust.isDivHelper e.2.name = false)
    (hind : ∀ g ∈ (prog S.opt.inputCleanup).funcs, Clif.IndFree g)
    (hsigs : ∀ g ∈ (prog S.opt.inputCleanup).funcs, Backend.indSigs g = [])
    (hind0 : ∀ g ∈ (prog S.inputCleanup).funcs, Clif.IndFree g)
    (hslots : ∀ g ∈ S.inputCleanup.srcProg.funcs, g.slots = [])
    {n : String} {f f' : Clif.Function} (hf : S.inputCleanup.srcProg.func? n = some f)
    (hf' : (prog S.opt.inputCleanup).func? n = some f')
    (hc : ¬ DeadCleanupStackBound.CycleFrom
      (DeadCleanupStackBound.Calls S.opt.inputCleanup S.opt.inputCleanup.resultsCleanup) f')
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.opt.inputCleanup (BinCheck.roByte S.opt.inputCleanup S.opt.data) f'
      (DeadCleanupStackBound.stackFn S.opt.inputCleanup f') r args' cs'.mem)
    (hr : ClifRun S.opt.inputCleanup helperBase f' r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hM : MemBounded cs.mem) (M : Nat) :
    ∀ vals cm, Clif.runLoop helperEnv S.inputCleanup.srcProg M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefines (art S.opt.inputCleanup f').fb (art S.opt.inputCleanup f').base (xreg 30 r)
          (step S.opt.inputCleanup helperBase file) r
          (E2E.DeadCleanupBinCheck.RelocAt S.opt.inputCleanup) (.returned vals' cm) :=
  (compileExeOpt_correct_source h hsrc helperBase (baseOk_helper htls hdiv hind hsigs)
    (hooksSim_helper _) envKeepsSymbols_helper (fun _ => ⟨helperOk, extLegal, keepsBounded⟩)
    (fun ⟨g, hg, hn⟩ => absurd (hind0 g hg) hn) hf hf' hc hX ho hr hcs hexp hsl hmem
    (srcBounded hsrc hslots (Clif.Program.func?_some hf).1 hcs hM) M).1

end Link.DeadCleanup.SourceWitness
