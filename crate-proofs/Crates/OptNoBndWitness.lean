import Crates.DeadCleanupExeOptSourceWitness
import FV.Link.DeadCleanupOptExeSourceNB

/-! # Non-vacuity of the optimising compilers' source theorems without the memory-bound premise
(A2/B1)

The witnesses of `Link.compileExeOpt_correct_source` and
`Link.DeadCleanup.compileExeOpt_correct_source` (`Crates.CompileExeOptSourceWitness`,
`Crates.DeadCleanupExeOptSourceWitness`: the optimised `wmul_u128` of `g_u128`, an original
`i128` program) for their `_nobnd` variants: the same runs, every premise discharged — without
the source run's memory bound (`srcBounded`, `cm_bounded`), which the variants derive
(`srcBoundedOpt_acyclic`).

* `compileExeOpt_source_nobnd_witness`: `Link.compileExeOpt_correct_source_nobnd`;
* `cleanup_opt_source_nobnd_witness`: `Link.DeadCleanup.compileExeOpt_correct_source_nobnd`.
-/

namespace Crates.CompileExeOptSourceWitness

open E2E E2E.LinkCheck E2E.Binary E2E.ExecBytes Backend Backend.Proof Link Link.SourceWitness
  Opt.Legalize128
open Crates.BinaryWitness (memOf)

/-- **Per-run non-vacuity of `Link.compileExeOpt_correct_source_nobnd`** on the original `i128`
program `{wmul_u128, wrapping_mul}` of `g_u128`: `compileExeOpt` produces the executable `file`,
with the compiled `wmul_u128` the mid-end's result (`f ≠ legalize fs`) and no print/parse
fallback; the input is in the source domain and `wmul_u128` mentions `i128`; the original
program's CLIF run of `wmul_u128` on `2^64 + 3` and `5` returns `5 * 2^64 + 15`; and, the outside
code calling the executable's compiled `wmul_u128` with the split arguments in x0–x3, the
executable machine returns to the caller with the split result `15, 5` in x0, x1. -/
theorem compileExeOpt_source_nobnd_witness :
    compileExeOpt spec file0 = .ok file ∧ spec.optFallbacks = [] ∧ SrcScopeB I0 = true ∧
    I0.srcProg.func? n = some fs ∧ (prog J).func? n = some f ∧ legalize fs ≠ f ∧
    mentions128 fs = true ∧
    Clif.runLoop helperEnv I0.srcProg M cs = .returned [⟨.i128, 5#64 ++ 15#64⟩]
      (LinkWitness.retMem run) ∧
    ∃ k, ArmRet ra0 (r (memOf file)) (runX (step J helperBase file) k (r (memOf file))) ∧
      XHolds ⟨.i64, 15#64⟩ (xreg 0 (runX (step J helperBase file) k (r (memOf file)))) ∧
      XHolds ⟨.i64, 5#64⟩ (xreg 1 (runX (step J helperBase file) k (r (memOf file)))) := by
  obtain ⟨hf, hf', hne, hm, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hst, htls, hdivB,
    hindB, hsigsB, -, hsrc⟩ := facts
  have hexp : Opt.Legal.ExpRel ((Opt.Legal.groups fs.sig.params).getD []) args args' := by
    rw [gp, Option.getD_some]
    exact ⟨⟨3#64, 1#64, rfl, rfl, rfl⟩, ⟨5#64, 0#64, rfl, rfl, rfl⟩, trivial⟩
  have hdiv : ∀ g ∈ (prog J).funcs, ∀ e ∈ g.externs, (prog J).func? e.2.name = none →
      Clif.Rust.isDivHelper e.2.name = false := by
    intro g hg e he hn
    have := List.all_eq_true.mp (List.all_eq_true.mp hdivB g hg) e he
    simpa [hn] using this
  have hoc := outsideCall (memOf file) (BinCheck.roByte J spec.opt.data) hst
  have hind0 : ∀ g ∈ (prog I0).funcs, Clif.IndFree g :=
    fun g hg => indFreeB_sound (List.all_eq_true.mp indFree0 g hg)
  have h := (compileExeOpt_correct_source_nobnd compile_eq hsrc helperBase
    (baseOk_helper (fun g hg => by simpa using List.all_eq_true.mp htls g hg) hdiv
      (fun g hg => indFreeB_sound (List.all_eq_true.mp hindB g hg))
      (fun g hg => by simpa using List.all_eq_true.mp hsigsB g hg))
    (hooksSim_helper _) envKeepsSymbols_helper (fun _ => ⟨helperOk, extLegal, keepsBounded⟩)
    (fun ⟨g, hg, hn⟩ => absurd (hind0 g hg) hn) hf hf' acyclic (intact file) hoc (clifRun _)
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
    exact ⟨compile_eq, noFallbacks, hsrc, hf, hf', hne, hm, run_eq, k, hret, hx 0 _ rfl,
      hx 1 _ rfl⟩

end Crates.CompileExeOptSourceWitness

namespace Crates.DeadCleanupExeOptSourceWitness

open E2E E2E.LinkCheck E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes Backend Backend.Proof
  Opt.Legalize128
open Link (LinkSpec inScopePar_eq)
open Link.SourceWitness (helperEnv helperBase baseOk_helper envKeepsSymbols_helper helperOk
  extLegal keepsBounded)
open Crates.BinaryWitness (memOf)
open Crates.CompileExeOptSourceWitness (input n args args' M sp0 ra0 sp0_toNat)

/-- **Per-run non-vacuity of `Link.DeadCleanup.compileExeOpt_correct_source_nobnd`** on the
original `i128` program `{wmul_u128, wrapping_mul}` of `g_u128`: the shipped optimising compiler
produces the executable `file`, with the compiled `wmul_u128` the mid-end's result
(`f ≠ legalize fs`); the input is in the source domain and `wmul_u128` mentions `i128`; the
original program's CLIF run of `wmul_u128` on `2^64 + 3` and `5` returns `5 * 2^64 + 15`; and, the
outside code calling the executable's compiled `wmul_u128` with the split arguments in x0–x3, the
executable machine returns to the caller with the split result `15, 5` in x0, x1. -/
theorem cleanup_opt_source_nobnd_witness :
    Link.DeadCleanup.compileExeOpt spec file0 = .ok file ∧ SrcScopeB I0 = true ∧
    I0.srcProg.func? n = some fs ∧ (prog J).func? n = some f ∧ legalize fs ≠ f ∧
    mentions128 fs = true ∧
    Clif.runLoop helperEnv I0.srcProg M cs = .returned [⟨.i128, 5#64 ++ 15#64⟩]
      (LinkWitness.retMem run) ∧
    ∃ k, ArmRet ra0 (r (memOf file)) (runX (step J helperBase file) k (r (memOf file))) ∧
      XHolds ⟨.i64, 15#64⟩ (xreg 0 (runX (step J helperBase file) k (r (memOf file)))) ∧
      XHolds ⟨.i64, 5#64⟩ (xreg 1 (runX (step J helperBase file) k (r (memOf file)))) := by
  obtain ⟨hf, hf', hne, hm, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hst, htls, hdivB,
    hindB, hsigsB, -, hsrc⟩ := facts
  have hexp : Opt.Legal.ExpRel ((Opt.Legal.groups fs.sig.params).getD []) args args' := by
    rw [gp, Option.getD_some]
    exact ⟨⟨3#64, 1#64, rfl, rfl, rfl⟩, ⟨5#64, 0#64, rfl, rfl, rfl⟩, trivial⟩
  have hdiv : ∀ g ∈ (prog J).funcs, ∀ e ∈ g.externs, (prog J).func? e.2.name = none →
      Clif.Rust.isDivHelper e.2.name = false := by
    intro g hg e he hn
    have := List.all_eq_true.mp (List.all_eq_true.mp hdivB g hg) e he
    simpa [hn] using this
  have hoc := outsideCall (memOf file) (BinCheck.roByte J spec.opt.data) hst
  have hind0 : ∀ g ∈ (prog I0).funcs, Clif.IndFree g :=
    fun g hg => indFreeB_sound (List.all_eq_true.mp indFree0 g hg)
  have h := (Link.DeadCleanup.compileExeOpt_correct_source_nobnd compile_eq hsrc helperBase
    (baseOk_helper (fun g hg => by simpa using List.all_eq_true.mp htls g hg) hdiv
      (fun g hg => indFreeB_sound (List.all_eq_true.mp hindB g hg))
      (fun g hg => by simpa using List.all_eq_true.mp hsigsB g hg))
    (Link.DeadCleanup.SourceWitness.hooksSim_helper _) envKeepsSymbols_helper
    (fun _ => ⟨helperOk, extLegal, keepsBounded⟩)
    (fun ⟨g, hg, hn⟩ => absurd (hind0 g hg) hn) hf hf' acyclic (intact file) hoc (clifRun _)
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
    exact ⟨compile_eq, hsrc, hf, hf', hne, hm, run_eq, k, hret, hx 0 _ rfl, hx 1 _ rfl⟩

end Crates.DeadCleanupExeOptSourceWitness
