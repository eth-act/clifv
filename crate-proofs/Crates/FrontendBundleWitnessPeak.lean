import Crates.FrontendBundleWitness

/-! # Non-vacuity of `Front.bundle_correct_source_peak` on a real codegen unit (T7e)

The bundle, `LinkSpec`, executable, renaming and run of `Crates.FrontendBundleWitness`
(`wmul_u128` and the local `wrapping_mul` of `g_u128`'s codegen unit, the shipped compiler). The
peak theorem needs no call-graph premise, but the source run's call depth: the linked run of
`wmul_u128` on `2^64 + 3` and `5` has call depth at most `d = 1` (it calls `wrapping_mul`, which
calls nothing), decided by `Clif.depthB` and transported back to the pre-renaming program
(`pre_depth`). The outside caller provides `frameDrop + D * 1` bytes of stack
(`bundle_source_peak_witness`).
-/

namespace Crates.FrontendBundleWitnessPeak

open E2E E2E.LinkCheck E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes Backend Backend.Proof
  Opt.Legalize128
open Link.SourceWitness (helperEnv helperBase)
open Crates.BinaryWitness (memOf)
open Crates.CompileExeSourceWitness (n args args' M ra0)
open Crates.FrontendBundleWitness

/-- The source run's call-depth bound. -/
def d : Nat := 1

/-- The linked run's call depth is at most `d`, and `frameDrop + D * d` bytes of stack fit. -/
theorem peakFacts :
    Clif.depthB helperEnv J.srcProg d M cs = true ∧
    frameDrop (artOf J.resultsCleanup f).af + J.D * d ≤ 2 ^ 20 := by
  refine ⟨?_, ?_⟩
  · native_decide
  · exact of_decide_eq_true (by native_decide)

/-- The linked program's run has call depth at most `d`. -/
theorem depth : Clif.DepthLe helperEnv J.srcProg d cs := Clif.depthLe_of_depthB M cs peakFacts.1

theorem stack_le : frameDrop (art J (legalize fs)).af + J.D * d ≤ 2 ^ 20 := by
  rw [FrontendBundleWitness.facts.2.2.1]; exact peakFacts.2

/-- **Per-run non-vacuity of `Front.bundle_correct_source_peak`** on the real codegen unit of
`g_u128`: as `Crates.FrontendBundleWitness.bundle_source_witness`, the call-depth premise
instead of the call-graph one: the pre-renaming program's CLIF run of `wmul_u128` on `2^64 + 3`
and `5` has call depth at most `1` and returns `5 * 2^64 + 15`; the outside code calling the
executable's compiled `wmul_u128` with the split arguments in x0–x3 and `frameDrop + D * 1` bytes
of stack, the executable machine returns to the caller with the split result `15, 5` in x0,
x1. -/
theorem bundle_source_peak_witness :
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
    hsigsB, hslotsB, hsrc⟩ := FrontendBundleWitness.facts
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
  have hslots : ∀ g ∈ J.srcProg.funcs, g.slots = [] :=
    fun g hg => by simpa using List.all_eq_true.mp hslotsB g hg
  have hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f0.sig.params).getD []) args args' := by
    rw [hsig0, gp, Option.getD_some]
    exact ⟨⟨3#64, 1#64, rfl, rfl, rfl⟩, ⟨5#64, 0#64, rfl, rfl, rfl⟩, trivial⟩
  have hoc := outsideCall (memOf file) (BinCheck.roByte J S.data) stack_le
  have hd := pre_depth hP depth
  have H := Front.bundle_correct_source_peak (r := r (memOf file)) (args := args)
    (args' := args') (cs := cs.ren σ.symm) (cs' := cs') buildSpec_eq compile_eq hsrc hus hσ
    (helperEnv.ren σ.symm) helperBase (Front.Env.ren_symm_ren σ _).symm
    (Link.SourceWitness.baseOk_helper (fun g hg => by simpa using List.all_eq_true.mp htls g hg)
      hdiv hind (fun g hg => by simpa using List.all_eq_true.mp hsigsB g hg))
    (Link.DeadCleanup.SourceWitness.hooksSim_helper _)
    (fun _ => ⟨Link.SourceWitness.helperOk, Link.SourceWitness.extLegal,
      Link.SourceWitness.keepsBounded⟩)
    (fun ⟨g, hg, hn⟩ => absurd (hind g hg) hn) hf0 d
    (intact file) (by rw [hfs]; exact hoc) (by rw [hfs]; exact clifRun _)
    (pre_entry hfs clifEntry) hexp rfl (Front.Mem.ren_symm_ren σ cm).symm
    (pre_bnd hP (Link.SourceWitness.srcBounded hsrc hslots (Clif.Program.func?_some hf).1
      clifEntry cm_bounded)) hd M
  have hrun0 := pre_run hP run_eq
  have h := H.1 _ _ hrun0
  rw [hfs, hsig0, x30_r] at h
  obtain ⟨vals', hrel, k, hret, hx, -⟩ := h
  rw [gr, Option.getD_some] at hrel
  cases split_ret hrel
  exact ⟨buildSpec_eq, compile_eq, hus, sc_ok, hf0, f0_mentions, σ, hσ, hσm, hd, hrun0, k, hret,
    hx 0 _ rfl, hx 1 _ rfl⟩

end Crates.FrontendBundleWitnessPeak
