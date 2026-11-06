import Crates.DeadCleanupExePeakWitness
import Crates.DeadCleanupExeSourceWitness
import Crates.FrontendBundleWitnessRaw
import Crates.FrontendBundleWitnessPeak
import FV.Front.RawExeNB

/-! # Non-vacuity of the source theorems without the memory-bound premise (A2/B1)

The witnesses of `Link.DeadCleanup.compileExe_correct_source{,_peak}` and
`Front.bundle_correct_{source,raw}{,_peak}` for their `_nobnd` variants: the same runs, every
premise discharged — without the source run's memory bound (`srcBounded`, `pre_bnd`), which the
variants derive.

* `cleanup_source_nobnd_witness`: `Link.DeadCleanup.compileExe_correct_source_nobnd` on
  `wmul_u128` (`Crates.DeadCleanupExeSourceWitness`);
* `cleanup_source_peak_nobnd_witness`: `Link.DeadCleanup.compileExe_correct_source_peak_nobnd` on
  the recursive `rec128` (`Crates.DeadCleanupExePeakWitness`);
* `bundle_source_nobnd_witness`, `bundle_source_peak_nobnd_witness`, `bundle_raw_nobnd_witness`,
  `bundle_raw_peak_nobnd_witness`: `Front.bundle_correct_source_nobnd`,
  `Front.bundle_correct_source_peak_nobnd`, `Front.bundle_correct_raw_nobnd`,
  `Front.bundle_correct_raw_peak_nobnd` on the real codegen unit of `g_u128`
  (`Crates.FrontendBundleWitness`).
-/

namespace Crates.DeadCleanupExeSourceWitness

open E2E E2E.LinkCheck E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes Backend Backend.Proof
  Opt.Legalize128
open Link (LinkSpec inScopePar_eq)
open Link.SourceWitness (helperEnv helperBase)
open Crates.BinaryWitness (memOf)
open Crates.CompileExeSourceWitness (input n args args' M sp0 ra0 sp0_toNat)

/-- **Per-run non-vacuity of `Link.DeadCleanup.compileExe_correct_source_nobnd`** on the original
`i128` program `{wmul_u128, wrapping_mul}` of `g_u128`: the shipped compiler produces the
executable `file`; the input is in the source domain (`SrcScopeB`) and its source function
`wmul_u128` mentions `i128`; the original program's CLIF run of `wmul_u128` on `2^64 + 3` and `5`
returns `5 * 2^64 + 15`; and, the outside code calling the executable's compiled `wmul_u128` with
the split arguments in x0–x3, the executable machine returns to the caller with the split result
`15, 5` in x0, x1. -/
theorem cleanup_source_nobnd_witness :
    Link.DeadCleanup.compileExe spec file0 = .ok file ∧ SrcScopeB J = true ∧
    J.srcProg.func? n = some fs ∧ mentions128 fs = true ∧
    Clif.runLoop helperEnv J.srcProg M cs = .returned [⟨.i128, 5#64 ++ 15#64⟩]
      (LinkWitness.retMem run) ∧
    ∃ k, ArmRet ra0 (r (memOf file)) (runX (step J helperBase file) k (r (memOf file))) ∧
      XHolds ⟨.i64, 15#64⟩ (xreg 0 (runX (step J helperBase file) k (r (memOf file)))) ∧
      XHolds ⟨.i64, 5#64⟩ (xreg 1 (runX (step J helperBase file) k (r (memOf file)))) := by
  obtain ⟨hf, -, -, hm, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hst, htls, hdivB, hindB,
    hsigsB, -, hsrc⟩ := facts
  have hexp : Opt.Legal.ExpRel ((Opt.Legal.groups fs.sig.params).getD []) args args' := by
    rw [gp, Option.getD_some]
    exact ⟨⟨3#64, 1#64, rfl, rfl, rfl⟩, ⟨5#64, 0#64, rfl, rfl, rfl⟩, trivial⟩
  have hdiv : ∀ g ∈ (prog J).funcs, ∀ e ∈ g.externs, (prog J).func? e.2.name = none →
      Clif.Rust.isDivHelper e.2.name = false := by
    intro g hg e he hn
    have := List.all_eq_true.mp (List.all_eq_true.mp hdivB g hg) e he
    simpa [hn] using this
  have hoc := outsideCall (memOf file) (BinCheck.roByte J spec.data) hst
  have hind : ∀ g ∈ (prog J).funcs, Clif.IndFree g :=
    fun g hg => indFreeB_sound (List.all_eq_true.mp hindB g hg)
  have h := (Link.DeadCleanup.compileExe_correct_source_nobnd compile_eq hsrc helperBase
    (Link.SourceWitness.baseOk_helper (fun g hg => by simpa using List.all_eq_true.mp htls g hg)
      hdiv hind (fun g hg => by simpa using List.all_eq_true.mp hsigsB g hg))
    (Link.DeadCleanup.SourceWitness.hooksSim_helper _)
    (fun _ => ⟨Link.SourceWitness.helperOk, Link.SourceWitness.extLegal,
      Link.SourceWitness.keepsBounded⟩)
    (fun ⟨g, hg, hn⟩ => absurd (hind g hg) hn) hf acyclic (intact file) hoc (clifRun _)
    clifEntry hexp rfl rfl M).1 _ _ run_eq
  rw [x30_r] at h
  obtain ⟨vals', hrel, k, hret, hx, -⟩ := h
  rw [gr, Option.getD_some] at hrel
  obtain ⟨a, b, rest, rfl, ⟨l, hh', e1, rfl, rfl⟩, hrest⟩ : ∃ a b rest, vals' = a :: b :: rest ∧
      Opt.Legal.Halves ⟨.i128, 5#64 ++ 15#64⟩ a b ∧ Opt.Legal.ExpRel [] [] rest := by
    match vals', hrel with
    | a :: b :: rest, ⟨hv, hr⟩ => exact ⟨a, b, rest, rfl, hv, hr⟩
  cases rest with
  | cons => exact absurd hrest id
  | nil =>
    obtain ⟨-, e1⟩ := Clif.Val.mk.inj e1
    have hl : l = 15#64 := by
      have := congrArg (fun x : BitVec 128 => x.extractLsb' 0 64) (eq_of_heq e1)
      have h2 : (hh' ++ l).extractLsb' 0 64 = 15#64 := by simpa using this.symm
      exact (BitVec.extractLsb'_append_eq_right (a := hh')).symm.trans h2
    have hh2 : hh' = 5#64 := by
      have := congrArg (fun x : BitVec 128 => x.extractLsb' 64 64) (eq_of_heq e1)
      have h2 : (hh' ++ l).extractLsb' 64 64 = 5#64 := by simpa using this.symm
      exact (BitVec.extractLsb'_append_eq_left (b := l)).symm.trans h2
    subst hl hh2
    exact ⟨compile_eq, hsrc, hf, hm, run_eq, k, hret, hx 0 _ rfl, hx 1 _ rfl⟩

end Crates.DeadCleanupExeSourceWitness

namespace Crates.DeadCleanupExePeakWitness

open E2E E2E.LinkCheck E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes Backend Backend.Proof
  Opt.Legalize128
open Link (LinkSpec inScopePar_eq)
open Link.SourceWitness (helperEnv helperBase baseOk_helper)
open Crates.BinaryWitness (memOf)
open Crates.CompileExeSourcePeakWitness (fnInput n args args' sp0 ra0 sp0_toNat d)

/-- **Per-run non-vacuity of `Link.DeadCleanup.compileExe_correct_source_peak_nobnd`** on the original
recursive `i128` program `rec128`: the shipped compiler produces the executable `file`; the input
is in the source domain and `rec128` mentions `i128`; the legalised entry reaches a call cycle;
the original program's CLIF run of `rec128` on `2^64 + 3` and `3` returns `8 * 2^64 + 24` with call
depth at most `3`; and, the outside code calling the executable's compiled `rec128` with the
split arguments in x0–x2 and `frameDrop + D * 3` bytes of stack, the executable machine returns
to the caller with the split result `24, 8` in x0, x1. -/
theorem cleanup_source_peak_nobnd_witness :
    Link.DeadCleanup.compileExe spec file0 = .ok file ∧ SrcScopeB J = true ∧
    J.srcProg.func? n = some fs ∧ mentions128 fs = true ∧
    DeadCleanupStackBound.CycleFrom (DeadCleanupStackBound.Calls J J.resultsCleanup) (legalize fs) ∧
    Clif.DepthLe helperEnv J.srcProg d cs ∧
    Clif.runLoop helperEnv J.srcProg M cs = .returned [⟨.i128, 8#64 ++ 24#64⟩]
      (LinkWitness.retMem run) ∧
    ∃ k, ArmRet ra0 (r (memOf file)) (runX (step J helperBase file) k (r (memOf file))) ∧
      XHolds ⟨.i64, 24#64⟩ (xreg 0 (runX (step J helperBase file) k (r (memOf file)))) ∧
      XHolds ⟨.i64, 8#64⟩ (xreg 1 (runX (step J helperBase file) k (r (memOf file)))) := by
  have hf := facts.1
  have hm := facts.2.2.2.1
  have hsrc := facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hexp : Opt.Legal.ExpRel ((Opt.Legal.groups fs.sig.params).getD []) args args' := by
    obtain ⟨p, hp⟩ := gp
    rw [hp, Option.getD_some]
    exact ⟨⟨3#64, 1#64, rfl, rfl, rfl⟩, rfl, trivial⟩
  have hoc := outsideCall (memOf file) (BinCheck.roByte J spec.data) stack_le
  have h := (Link.DeadCleanup.compileExe_correct_source_peak_nobnd compile_eq hsrc helperBase
    (baseOk_helper htls hdiv hind hsigs) (Link.DeadCleanup.SourceWitness.hooksSim_helper _)
    (fun _ => ⟨Link.SourceWitness.helperOk, Link.SourceWitness.extLegal,
      Link.SourceWitness.keepsBounded⟩)
    (fun ⟨g, hg, hn⟩ => absurd (hind g hg) hn) hf d (intact file) hoc (clifRun _) clifEntry hexp
    rfl rfl depth M).1 _ _ run_eq
  rw [x30_r] at h
  obtain ⟨vals', hrel, k, hret, hx, -⟩ := h
  rw [gr, Option.getD_some] at hrel
  obtain ⟨a, b, rest, rfl, ⟨l, hh', e1, rfl, rfl⟩, hrest⟩ : ∃ a b rest, vals' = a :: b :: rest ∧
      Opt.Legal.Halves ⟨.i128, 8#64 ++ 24#64⟩ a b ∧ Opt.Legal.ExpRel [] [] rest := by
    match vals', hrel with
    | a :: b :: rest, ⟨hv, hr⟩ => exact ⟨a, b, rest, rfl, hv, hr⟩
  cases rest with
  | cons => exact absurd hrest id
  | nil =>
    obtain ⟨-, e1⟩ := Clif.Val.mk.inj e1
    have hl' : l = 24#64 := by
      have := congrArg (fun x : BitVec 128 => x.extractLsb' 0 64) (eq_of_heq e1)
      have h2 : (hh' ++ l).extractLsb' 0 64 = 24#64 := by simpa using this.symm
      exact (BitVec.extractLsb'_append_eq_right (a := hh')).symm.trans h2
    have hh2 : hh' = 8#64 := by
      have := congrArg (fun x : BitVec 128 => x.extractLsb' 64 64) (eq_of_heq e1)
      have h2 : (hh' ++ l).extractLsb' 64 64 = 8#64 := by simpa using this.symm
      exact (BitVec.extractLsb'_append_eq_left (b := l)).symm.trans h2
    subst hl' hh2
    exact ⟨compile_eq, hsrc, hf, hm, cyclic, depth, run_eq, k, hret, hx 0 _ rfl, hx 1 _ rfl⟩

end Crates.DeadCleanupExePeakWitness

namespace Crates.FrontendBundleWitness

open E2E E2E.LinkCheck E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes Backend Backend.Proof
  Opt.Legalize128
open Link (LinkSpec inScopePar_eq)
open Link.SourceWitness (helperEnv helperBase)
open Crates.BinaryWitness (memOf)
open Crates.CompileExeSourceWitness (n args args' M sp0 ra0 sp0_toNat)
open Crates.FrontendBundleInput (fn26 fn2 unitWith symbols fns)

/-- **Per-run non-vacuity of `Front.bundle_correct_source_nobnd`** on the real codegen unit of
`g_u128` (functions `wmul_u128` and the local `wrapping_mul`): `lean-link`'s `LinkSpec` is built
from the bundle in Lean, the shipped compiler produces the executable `file`; the linked program
is the pre-renaming program (the names as the frontend wrote them) renamed by a bijection `σ`
moving `wrapping_mul`'s CLIF name to its linked name; the **pre-renaming** program's CLIF run of
`wmul_u128` on `2^64 + 3` and `5` (in the outside world `helperBase` renamed back) returns
`5 * 2^64 + 15`; and, the outside code calling the executable's compiled `wmul_u128` with the
split arguments in x0–x3, the executable machine returns to the caller with the split result
`15, 5` in x0, x1. -/
theorem bundle_source_nobnd_witness :
    Front.buildSpec bw = .ok S ∧ Link.DeadCleanup.compileExe S file0 = .ok file ∧
    bw.units.mapM Front.parseUnit = .ok us ∧ Front.ScopingOk us sc ∧
    (Front.link us sc).func? n = some f0 ∧ mentions128 f0 = true ∧
    ∃ σ : Clif.Ren,
      Front.link us (Front.finOf us) = (Front.link us sc).rename σ.fwd ∧
      σ.fwd mulClif = mulLinked ∧
      Clif.runLoop (helperEnv.ren σ.symm) (Front.link us sc) M (cs.ren σ.symm) =
        .returned [⟨.i128, 5#64 ++ 15#64⟩] ((LinkWitness.retMem run).ren σ.symm) ∧
      ∃ k, ArmRet ra0 (r (memOf file)) (runX (step J helperBase file) k (r (memOf file))) ∧
        XHolds ⟨.i64, 15#64⟩ (xreg 0 (runX (step J helperBase file) k (r (memOf file)))) ∧
        XHolds ⟨.i64, 5#64⟩ (xreg 1 (runX (step J helperBase file) k (r (memOf file)))) := by
  obtain ⟨hf, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hst, htls, hdivB, hindB,
    hsigsB, -, hsrc⟩ := facts
  obtain ⟨σ, hσ, hσn, hσm⟩ := alpha
  have hP := srcProg_eq hσ
  -- the pre-renaming `wmul_u128` renamed is the source `wmul_u128`
  have hfs : f0.rename σ.fwd = fs := pre_fn hP hσn hf
  have hsig0 : f0.sig = fs.sig := by rw [← hfs, Clif.Function.rename_sig]
  -- the base premises of `helperBase`
  have hind : ∀ g ∈ (prog J).funcs, Clif.IndFree g :=
    fun g hg => indFreeB_sound (List.all_eq_true.mp hindB g hg)
  have hdiv : ∀ g ∈ (prog J).funcs, ∀ e ∈ g.externs, (prog J).func? e.2.name = none →
      Clif.Rust.isDivHelper e.2.name = false := by
    intro g hg e he hn
    have := List.all_eq_true.mp (List.all_eq_true.mp hdivB g hg) e he
    simpa [hn] using this
  have hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f0.sig.params).getD []) args args' := by
    rw [hsig0, gp, Option.getD_some]
    exact ⟨⟨3#64, 1#64, rfl, rfl, rfl⟩, ⟨5#64, 0#64, rfl, rfl, rfl⟩, trivial⟩
  have hoc := outsideCall (memOf file) (BinCheck.roByte J S.data) hst
  have H := Front.bundle_correct_source_nobnd (r := r (memOf file)) (args := args) (args' := args')
    (cs := cs.ren σ.symm) (cs' := cs') buildSpec_eq compile_eq hsrc hus hσ
    (helperEnv.ren σ.symm) helperBase (Front.Env.ren_symm_ren σ _).symm
    (Link.SourceWitness.baseOk_helper (fun g hg => by simpa using List.all_eq_true.mp htls g hg)
      hdiv hind (fun g hg => by simpa using List.all_eq_true.mp hsigsB g hg))
    (Link.DeadCleanup.SourceWitness.hooksSim_helper _)
    (fun _ => ⟨Link.SourceWitness.helperOk, Link.SourceWitness.extLegal,
      Link.SourceWitness.keepsBounded⟩)
    (fun ⟨g, hg, hn⟩ => absurd (hind g hg) hn) hf0 (by rw [hfs]; exact acyclic)
    (intact file) (by rw [hfs]; exact hoc) (by rw [hfs]; exact clifRun _)
    (pre_entry hfs clifEntry) hexp rfl (Front.Mem.ren_symm_ren σ cm).symm M
  -- the pre-renaming run, from the linked one
  have hrun0 := pre_run hP run_eq
  have h := H.1 _ _ hrun0
  rw [hfs, hsig0, x30_r] at h
  obtain ⟨vals', hrel, k, hret, hx, -⟩ := h
  rw [gr, Option.getD_some] at hrel
  cases split_ret hrel
  exact ⟨buildSpec_eq, compile_eq, hus, sc_ok, hf0, f0_mentions, σ, hσ, hσm, hrun0, k, hret,
    hx 0 _ rfl, hx 1 _ rfl⟩

end Crates.FrontendBundleWitness

namespace Crates.FrontendBundleWitnessPeak

open E2E E2E.LinkCheck E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes Backend Backend.Proof
  Opt.Legalize128
open Link.SourceWitness (helperEnv helperBase)
open Crates.BinaryWitness (memOf)
open Crates.CompileExeSourceWitness (n args args' M ra0)
open Crates.FrontendBundleWitness

/-- **Per-run non-vacuity of `Front.bundle_correct_source_peak_nobnd`** on the real codegen unit of
`g_u128`: as `Crates.FrontendBundleWitness.bundle_source_witness`, the call-depth premise
instead of the call-graph one: the pre-renaming program's CLIF run of `wmul_u128` on `2^64 + 3`
and `5` has call depth at most `1` and returns `5 * 2^64 + 15`; the outside code calling the
executable's compiled `wmul_u128` with the split arguments in x0–x3 and `frameDrop + D * 1` bytes
of stack, the executable machine returns to the caller with the split result `15, 5` in x0,
x1. -/
theorem bundle_source_peak_nobnd_witness :
    Front.buildSpec bw = .ok S ∧ Link.DeadCleanup.compileExe S file0 = .ok file ∧
    bw.units.mapM Front.parseUnit = .ok us ∧ Front.ScopingOk us sc ∧
    (Front.link us sc).func? n = some f0 ∧ mentions128 f0 = true ∧
    ∃ σ : Clif.Ren,
      Front.link us (Front.finOf us) = (Front.link us sc).rename σ.fwd ∧
      σ.fwd mulClif = mulLinked ∧
      Clif.DepthLe (helperEnv.ren σ.symm) (Front.link us sc) d (cs.ren σ.symm) ∧
      Clif.runLoop (helperEnv.ren σ.symm) (Front.link us sc) M (cs.ren σ.symm) =
        .returned [⟨.i128, 5#64 ++ 15#64⟩] ((LinkWitness.retMem run).ren σ.symm) ∧
      ∃ k, ArmRet ra0 (r (memOf file)) (runX (step J helperBase file) k (r (memOf file))) ∧
        XHolds ⟨.i64, 15#64⟩ (xreg 0 (runX (step J helperBase file) k (r (memOf file)))) ∧
        XHolds ⟨.i64, 5#64⟩ (xreg 1 (runX (step J helperBase file) k (r (memOf file)))) := by
  obtain ⟨hf, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, htls, hdivB, hindB,
    hsigsB, -, hsrc⟩ := FrontendBundleWitness.facts
  obtain ⟨σ, hσ, hσn, hσm⟩ := alpha
  have hP := srcProg_eq hσ
  have hfs : f0.rename σ.fwd = fs := pre_fn hP hσn hf
  have hsig0 : f0.sig = fs.sig := by rw [← hfs, Clif.Function.rename_sig]
  have hind : ∀ g ∈ (prog J).funcs, Clif.IndFree g :=
    fun g hg => indFreeB_sound (List.all_eq_true.mp hindB g hg)
  have hdiv : ∀ g ∈ (prog J).funcs, ∀ e ∈ g.externs, (prog J).func? e.2.name = none →
      Clif.Rust.isDivHelper e.2.name = false := by
    intro g hg e he hn
    have := List.all_eq_true.mp (List.all_eq_true.mp hdivB g hg) e he
    simpa [hn] using this
  have hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f0.sig.params).getD []) args args' := by
    rw [hsig0, gp, Option.getD_some]
    exact ⟨⟨3#64, 1#64, rfl, rfl, rfl⟩, ⟨5#64, 0#64, rfl, rfl, rfl⟩, trivial⟩
  have hoc := outsideCall (memOf file) (BinCheck.roByte J S.data) stack_le
  have hd := pre_depth hP depth
  have H := Front.bundle_correct_source_peak_nobnd (r := r (memOf file)) (args := args)
    (args' := args') (cs := cs.ren σ.symm) (cs' := cs') buildSpec_eq compile_eq hsrc hus hσ
    (helperEnv.ren σ.symm) helperBase (Front.Env.ren_symm_ren σ _).symm
    (Link.SourceWitness.baseOk_helper (fun g hg => by simpa using List.all_eq_true.mp htls g hg)
      hdiv hind (fun g hg => by simpa using List.all_eq_true.mp hsigsB g hg))
    (Link.DeadCleanup.SourceWitness.hooksSim_helper _)
    (fun _ => ⟨Link.SourceWitness.helperOk, Link.SourceWitness.extLegal,
      Link.SourceWitness.keepsBounded⟩)
    (fun ⟨g, hg, hn⟩ => absurd (hind g hg) hn) hf0 d
    (intact file) (by rw [hfs]; exact hoc) (by rw [hfs]; exact clifRun _)
    (pre_entry hfs clifEntry) hexp rfl (Front.Mem.ren_symm_ren σ cm).symm hd M
  have hrun0 := pre_run hP run_eq
  have h := H.1 _ _ hrun0
  rw [hfs, hsig0, x30_r] at h
  obtain ⟨vals', hrel, k, hret, hx, -⟩ := h
  rw [gr, Option.getD_some] at hrel
  cases split_ret hrel
  exact ⟨buildSpec_eq, compile_eq, hus, sc_ok, hf0, f0_mentions, σ, hσ, hσm, hd, hrun0, k, hret,
    hx 0 _ rfl, hx 1 _ rfl⟩

end Crates.FrontendBundleWitnessPeak

namespace Crates.FrontendBundleWitnessRaw

open E2E E2E.LinkCheck E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes Backend Backend.Proof
  Opt.Legalize128
open Link (LinkSpec)
open Link.SourceWitness (helperEnv helperBase)
open Crates.BinaryWitness (memOf)
open Crates.CompileExeSourceWitness (n args args' M ra0)
open Crates.FrontendBundleWitness

/-- **Per-run non-vacuity of `Front.bundle_correct_raw_nobnd`** on the real codegen unit of `g_u128`:
the linked program is cg_clif's program under the naming `scd` renamed by a bijection `σ`;
cg_clif's program's run of `wmul_u128` on `2^64 + 3` and `5` (in the outside world `helperBase`
renamed back) returns `5 * 2^64 + 15`, and the executable returns `15, 5` in x0, x1. -/
theorem bundle_raw_nobnd_witness :
    Front.RawScopingOk us scd ∧ (Front.rawLink us scd).func? n = some f0 ∧
    ∃ σ : Clif.Ren,
      Front.link us (Front.finOf us) = (Front.rawLink us scd).rename σ.fwd ∧
      Clif.runLoop (helperEnv.ren σ.symm) (Front.rawLink us scd) M (cs.ren σ.symm) =
        .returned [⟨.i128, 5#64 ++ 15#64⟩] ((LinkWitness.retMem run).ren σ.symm) ∧
      ∃ k, ArmRet ra0 (r (memOf file)) (runX (step J helperBase file) k (r (memOf file))) ∧
        XHolds ⟨.i64, 15#64⟩ (xreg 0 (runX (step J helperBase file) k (r (memOf file)))) ∧
        XHolds ⟨.i64, 5#64⟩ (xreg 1 (runX (step J helperBase file) k (r (memOf file)))) := by
  obtain ⟨hf, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hst, htls, hdivB, hindB,
    hsigsB, -, hsrc⟩ := FrontendBundleWitness.facts
  obtain ⟨σ, hσ, hσn, -⟩ := alpha
  have hP := srcProg_eq hσ
  have hfs : f0.rename σ.fwd = fs := pre_fn hP hσn hf
  have hsig0 : f0.sig = fs.sig := by rw [← hfs, Clif.Function.rename_sig]
  have hind : ∀ g ∈ (prog J).funcs, Clif.IndFree g :=
    fun g hg => indFreeB_sound (List.all_eq_true.mp hindB g hg)
  have hdiv : ∀ g ∈ (prog J).funcs, ∀ e ∈ g.externs, (prog J).func? e.2.name = none →
      Clif.Rust.isDivHelper e.2.name = false := by
    intro g hg e he hn
    have := List.all_eq_true.mp (List.all_eq_true.mp hdivB g hg) e he
    simpa [hn] using this
  have hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f0.sig.params).getD []) args args' := by
    rw [hsig0, gp, Option.getD_some]
    exact ⟨⟨3#64, 1#64, rfl, rfl, rfl⟩, ⟨5#64, 0#64, rfl, rfl, rfl⟩, trivial⟩
  have hoc := outsideCall (memOf file) (BinCheck.roByte J S.data) hst
  have hσr : Front.link us (Front.finOf us) = (Front.rawLink us scd).rename σ.fwd := by
    rw [rawLink_eq]; exact hσ
  have hf0r : (Front.rawLink us scd).func? n = some f0 := by rw [rawLink_eq]; exact hf0
  have H := Front.bundle_correct_raw_nobnd (r := r (memOf file)) (args := args) (args' := args')
    (cs := cs.ren σ.symm) (cs' := cs') buildSpec_eq compile_eq hsrc hus scd_ok hσr
    (helperEnv.ren σ.symm) helperBase (Front.Env.ren_symm_ren σ _).symm
    (Link.SourceWitness.baseOk_helper (fun g hg => by simpa using List.all_eq_true.mp htls g hg)
      hdiv hind (fun g hg => by simpa using List.all_eq_true.mp hsigsB g hg))
    (Link.DeadCleanup.SourceWitness.hooksSim_helper _)
    (fun _ => ⟨Link.SourceWitness.helperOk, Link.SourceWitness.extLegal,
      Link.SourceWitness.keepsBounded⟩)
    (fun ⟨g, hg, hn⟩ => absurd (hind g hg) hn) hf0r (by rw [hfs]; exact acyclic)
    (intact file) (by rw [hfs]; exact hoc) (by rw [hfs]; exact clifRun _)
    (pre_entry hfs clifEntry) hexp rfl (Front.Mem.ren_symm_ren σ cm).symm M
  have hrun0 := pre_run hP run_eq
  have hrun0r : Clif.runLoop (helperEnv.ren σ.symm) (Front.rawLink us scd) M (cs.ren σ.symm) =
      .returned [⟨.i128, 5#64 ++ 15#64⟩] ((LinkWitness.retMem run).ren σ.symm) := by
    rw [rawLink_eq]; exact hrun0
  have h := H.1 _ _ hrun0r
  rw [hfs, hsig0, x30_r] at h
  obtain ⟨vals', hrel, k, hret, hx, -⟩ := h
  rw [gr, Option.getD_some] at hrel
  cases split_ret hrel
  exact ⟨scd_ok, hf0r, σ, hσr, hrun0r, k, hret, hx 0 _ rfl, hx 1 _ rfl⟩

/-- **Per-run non-vacuity of `Front.bundle_correct_raw_peak_nobnd`** on the real codegen unit of
`g_u128`: as `bundle_raw_nobnd_witness`, the call-depth premise instead of the call-graph one:
cg_clif's program's run of `wmul_u128` on `2^64 + 3` and `5` has call depth at most `1`
(`Crates.FrontendBundleWitnessPeak.depth`) and returns `5 * 2^64 + 15`; the outside code
providing `frameDrop + D * 1` bytes of stack, the executable returns `15, 5` in x0, x1. -/
theorem bundle_raw_peak_nobnd_witness :
    Front.RawScopingOk us scd ∧ (Front.rawLink us scd).func? n = some f0 ∧
    ∃ σ : Clif.Ren,
      Front.link us (Front.finOf us) = (Front.rawLink us scd).rename σ.fwd ∧
      Clif.DepthLe (helperEnv.ren σ.symm) (Front.rawLink us scd) FrontendBundleWitnessPeak.d
        (cs.ren σ.symm) ∧
      Clif.runLoop (helperEnv.ren σ.symm) (Front.rawLink us scd) M (cs.ren σ.symm) =
        .returned [⟨.i128, 5#64 ++ 15#64⟩] ((LinkWitness.retMem run).ren σ.symm) ∧
      ∃ k, ArmRet ra0 (r (memOf file)) (runX (step J helperBase file) k (r (memOf file))) ∧
        XHolds ⟨.i64, 15#64⟩ (xreg 0 (runX (step J helperBase file) k (r (memOf file)))) ∧
        XHolds ⟨.i64, 5#64⟩ (xreg 1 (runX (step J helperBase file) k (r (memOf file)))) := by
  obtain ⟨hf, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, htls, hdivB, hindB,
    hsigsB, -, hsrc⟩ := FrontendBundleWitness.facts
  obtain ⟨σ, hσ, hσn, -⟩ := alpha
  have hP := srcProg_eq hσ
  have hfs : f0.rename σ.fwd = fs := pre_fn hP hσn hf
  have hsig0 : f0.sig = fs.sig := by rw [← hfs, Clif.Function.rename_sig]
  have hind : ∀ g ∈ (prog J).funcs, Clif.IndFree g :=
    fun g hg => indFreeB_sound (List.all_eq_true.mp hindB g hg)
  have hdiv : ∀ g ∈ (prog J).funcs, ∀ e ∈ g.externs, (prog J).func? e.2.name = none →
      Clif.Rust.isDivHelper e.2.name = false := by
    intro g hg e he hn
    have := List.all_eq_true.mp (List.all_eq_true.mp hdivB g hg) e he
    simpa [hn] using this
  have hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f0.sig.params).getD []) args args' := by
    rw [hsig0, gp, Option.getD_some]
    exact ⟨⟨3#64, 1#64, rfl, rfl, rfl⟩, ⟨5#64, 0#64, rfl, rfl, rfl⟩, trivial⟩
  have hoc := outsideCall (memOf file) (BinCheck.roByte J S.data)
    FrontendBundleWitnessPeak.stack_le
  have hσr : Front.link us (Front.finOf us) = (Front.rawLink us scd).rename σ.fwd := by
    rw [rawLink_eq]; exact hσ
  have hf0r : (Front.rawLink us scd).func? n = some f0 := by rw [rawLink_eq]; exact hf0
  have hd : Clif.DepthLe (helperEnv.ren σ.symm) (Front.rawLink us scd) FrontendBundleWitnessPeak.d
      (cs.ren σ.symm) := by
    rw [rawLink_eq]; exact pre_depth hP FrontendBundleWitnessPeak.depth
  have H := Front.bundle_correct_raw_peak_nobnd (r := r (memOf file)) (args := args)
    (args' := args') (cs := cs.ren σ.symm) (cs' := cs') buildSpec_eq compile_eq hsrc hus scd_ok
    hσr (helperEnv.ren σ.symm) helperBase (Front.Env.ren_symm_ren σ _).symm
    (Link.SourceWitness.baseOk_helper (fun g hg => by simpa using List.all_eq_true.mp htls g hg)
      hdiv hind (fun g hg => by simpa using List.all_eq_true.mp hsigsB g hg))
    (Link.DeadCleanup.SourceWitness.hooksSim_helper _)
    (fun _ => ⟨Link.SourceWitness.helperOk, Link.SourceWitness.extLegal,
      Link.SourceWitness.keepsBounded⟩)
    (fun ⟨g, hg, hn⟩ => absurd (hind g hg) hn) hf0r FrontendBundleWitnessPeak.d
    (intact file) (by rw [hfs]; exact hoc) (by rw [hfs]; exact clifRun _)
    (pre_entry hfs clifEntry) hexp rfl (Front.Mem.ren_symm_ren σ cm).symm hd M
  have hrun0 := pre_run hP run_eq
  have hrun0r : Clif.runLoop (helperEnv.ren σ.symm) (Front.rawLink us scd) M (cs.ren σ.symm) =
      .returned [⟨.i128, 5#64 ++ 15#64⟩] ((LinkWitness.retMem run).ren σ.symm) := by
    rw [rawLink_eq]; exact hrun0
  have h := H.1 _ _ hrun0r
  rw [hfs, hsig0, x30_r] at h
  obtain ⟨vals', hrel, k, hret, hx, -⟩ := h
  rw [gr, Option.getD_some] at hrel
  cases split_ret hrel
  exact ⟨scd_ok, hf0r, σ, hσr, hd, hrun0r, k, hret, hx 0 _ rfl, hx 1 _ rfl⟩

end Crates.FrontendBundleWitnessRaw
