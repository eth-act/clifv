import Crates.DeadCleanupExePeakWitness
import Crates.FrontendBundleWitnessRaw
import FV.Front.RawExeTls

/-! # Non-vacuity of the shipped compiler's hook-free TLS theorems (T1)

The programs of `Crates.DeadCleanupExePeakWitness` (the recursive `i128` function `rec128`) and
`Crates.FrontendBundleWitnessRaw` (cg_clif's `wmul_u128` of `g_u128`), with the outside world
`Link.SourceWitness.helperBase` and its local-exec TLS hook (`leBase`, whose base premises hold:
`E2E.DeadCleanupExecBytes.baseOk_le`), the outside-call clause of `HooksSim`, and the loader's
thread-pointer contract `TlsLoader` (the entry's thread pointer is `helperBase.tp = 0`; the
outside-call hook keeps it; the programs have no TLSDESC relocation):

* `cleanup_peak_tls_witness`: `Link.DeadCleanup.compileExe_correct_peak_tls` on `rec128` — the
  hook-free machine `stepT` returns to the caller with `24, 8` in x0, x1;
* `cleanup_source_peak_tls_witness`: `Link.DeadCleanup.compileExe_correct_source_peak_tls` on
  the original `rec128` — `stepT` returns the split result `24, 8`;
* `bundle_raw_tls_witness`: `Front.bundle_correct_raw_tls` on cg_clif's program (through
  `Front.bundle_correct_source_tls`, `Link.DeadCleanup.compileExe_correct_source_tls` and
  `compileExe_correct_tls`) — `stepT` returns `15, 5`.
-/

namespace Crates.DeadCleanupExeTlsWitness

open E2E E2E.LinkCheck E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes Backend Backend.Proof
  Opt.Legalize128
open Link.SourceWitness (helperEnv helperBase baseOk_helper)
open Crates.BinaryWitness (memOf)

/-- **`TlsLoader` of `helperBase`**: thread pointer `0` at the entry, kept by the outside-call
hook (`closedBase`'s), and no TLSDESC relocation in the program. -/
theorem tlsLoader_helper {I : LinkInput} {file : ByteArray} {r : Arm.ArmState}
    (htp : Arm.r .TPIDR r = 0)
    (hno : (tabOf I.resultsCleanup).all (fun e =>
      e.2.fb.relocs.all fun rl => rl.type != .tlsDescAdrPage21) = true)
    (hI : okBCleanup I = true) : TlsLoader I helperBase file r where
  tp := htp
  call d s := by
    show Arm.r .TPIDR (Arm.w .PC (Arm.r .PC s + 4) s) = _
    exact Arm.r_of_w_different (by simp)
  addr g hg rl hrl ht := by
    have hm := tab_mem (okBCleanup_names hI) hg
    have := List.all_eq_true.1 (List.all_eq_true.1 hno _ hm) rl hrl
    rw [ht] at this
    exact absurd this (by decide)

section Peak

open Crates.DeadCleanupExePeakWitness
open Crates.CompileExeSourcePeakWitness (n args args' ra0 d)

theorem noTlsReloc : (tabOf J.resultsCleanup).all (fun e =>
    e.2.fb.relocs.all fun rl => rl.type != .tlsDescAdrPage21) = true := by native_decide

theorem tp_r (m : Arm.Memory) : Arm.r .TPIDR (r m) = 0 := by
  simp only [r, Arm.r_of_w_different (by decide : Arm.StateField.TPIDR ≠ .PC),
    Arm.r_of_w_different (by decide : Arm.StateField.TPIDR ≠ .GPR 30#5),
    Arm.r_of_w_different (by decide : Arm.StateField.TPIDR ≠ .GPR 31#5),
    Arm.r_of_w_different (by decide : Arm.StateField.TPIDR ≠ .GPR 0#5),
    Arm.r_of_w_different (by decide : Arm.StateField.TPIDR ≠ .GPR 1#5),
    Arm.r_of_w_different (by decide : Arm.StateField.TPIDR ≠ .GPR 2#5), r_setMem]
  with_unfolding_all rfl

/-- **Per-run non-vacuity of `Link.DeadCleanup.compileExe_correct_peak_tls`** on the recursive
legalised `rec128` (every premise of `cleanup_peak_witness`, with `leBase` and `TlsLoader`): the
hook-free executable machine returns to the caller with `24, 8` in x0, x1. -/
theorem cleanup_peak_tls_witness :
    ∃ k, ArmRet ra0 (r (memOf file)) (runX (stepT J helperBase file) k (r (memOf file))) ∧
      XHolds ⟨.i64, 24#64⟩ (xreg 0 (runX (stepT J helperBase file) k (r (memOf file)))) ∧
      XHolds ⟨.i64, 8#64⟩ (xreg 1 (runX (stepT J helperBase file) k (r (memOf file)))) := by
  have hf : (prog J).func? n = some (legalize fs) := by rw [facts.2.2.1]; exact facts.2.1
  have hfm := (Clif.Program.func?_some hf).1
  have hB : BaseOk (sys J (leBase J helperBase file)) := baseOk_le (baseOk_helper htls hdiv hind hsigs)
  have hoc := outsideCall (memOf file) (BinCheck.roByte J spec.data) stack_le
  have hL : (LinkSys.ofInputCleanup J helperBase fun _ => True).Ok :=
    okBCleanup_sound okB_J (baseOk_helper htls hdiv hind hsigs) fun _ _ => trivial
  have htr := E2E.Binary.trapsExplicit_of_runD hL hfm clifEntry' rfl depthT runT_eq
  have h := Link.DeadCleanup.compileExe_correct_peak_tls compile_eq helperBase hB
    (Link.DeadCleanup.SourceWitness.hooksSim_helper J).call hf F d (intact file) hoc (clifRun _)
    depthT htr (tlsLoader_helper (tp_r _) noTlsReloc okB_J)
  rw [show Clif.runLoop helperBase.env (prog J) (F + 1) cs' = runT from rfl, runT_eq, x30_r] at h
  obtain ⟨k, hret, hx, -⟩ := h
  exact ⟨k, hret, hx 0 _ rfl, hx 1 _ rfl⟩

/-- **Per-run non-vacuity of `Link.DeadCleanup.compileExe_correct_source_peak_tls`** on the
original recursive `i128` program `rec128` (the premises of `cleanup_source_peak_witness`, with
`leBase` and `TlsLoader`): the hook-free executable machine returns to the caller with the split
result `24, 8` in x0, x1. -/
theorem cleanup_source_peak_tls_witness :
    ∃ k, ArmRet ra0 (r (memOf file)) (runX (stepT J helperBase file) k (r (memOf file))) ∧
      XHolds ⟨.i64, 24#64⟩ (xreg 0 (runX (stepT J helperBase file) k (r (memOf file)))) ∧
      XHolds ⟨.i64, 8#64⟩ (xreg 1 (runX (stepT J helperBase file) k (r (memOf file)))) := by
  have hf := facts.1
  have hsrc := facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hslots : ∀ g ∈ J.srcProg.funcs, g.slots = [] := fun g hg => by
    simpa using
      List.all_eq_true.mp facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 g hg
  have hexp : Opt.Legal.ExpRel ((Opt.Legal.groups fs.sig.params).getD []) args args' := by
    obtain ⟨p, hp⟩ := gp
    rw [hp, Option.getD_some]
    exact ⟨⟨3#64, 1#64, rfl, rfl, rfl⟩, rfl, trivial⟩
  have hoc := outsideCall (memOf file) (BinCheck.roByte J spec.data) stack_le
  have h := (Link.DeadCleanup.compileExe_correct_source_peak_tls compile_eq hsrc helperBase
    (baseOk_le (baseOk_helper htls hdiv hind hsigs))
    (Link.DeadCleanup.SourceWitness.hooksSim_helper J).call
    (fun _ => ⟨Link.SourceWitness.helperOk, Link.SourceWitness.extLegal,
      Link.SourceWitness.keepsBounded⟩)
    (fun ⟨g, hg, hn⟩ => absurd (hind g hg) hn) hf d (intact file)
    (tlsLoader_helper (tp_r _) noTlsReloc okB_J) hoc (clifRun _) clifEntry hexp rfl rfl
    (Link.SourceWitness.srcBounded hsrc hslots (Clif.Program.func?_some hf).1 clifEntry
      cm_bounded) depth M).1 _ _ run_eq
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
    exact ⟨k, hret, hx 0 _ rfl, hx 1 _ rfl⟩

end Peak

section Raw

open Crates.FrontendBundleWitness Crates.FrontendBundleWitnessRaw
open Crates.CompileExeSourceWitness (n args args' M ra0)

theorem noTlsReloc_raw : (tabOf J.resultsCleanup).all (fun e =>
    e.2.fb.relocs.all fun rl => rl.type != .tlsDescAdrPage21) = true := by native_decide

theorem tp_r_raw (m : Arm.Memory) : Arm.r .TPIDR (r m) = 0 := by
  simp only [r, Arm.r_of_w_different (by decide : Arm.StateField.TPIDR ≠ .PC),
    Arm.r_of_w_different (by decide : Arm.StateField.TPIDR ≠ .GPR 30#5),
    Arm.r_of_w_different (by decide : Arm.StateField.TPIDR ≠ .GPR 31#5),
    Arm.r_of_w_different (by decide : Arm.StateField.TPIDR ≠ .GPR 0#5),
    Arm.r_of_w_different (by decide : Arm.StateField.TPIDR ≠ .GPR 1#5),
    Arm.r_of_w_different (by decide : Arm.StateField.TPIDR ≠ .GPR 2#5),
    Arm.r_of_w_different (by decide : Arm.StateField.TPIDR ≠ .GPR 3#5), r_setMem]
  with_unfolding_all rfl

/-- **Per-run non-vacuity of `Front.bundle_correct_raw_tls`** on cg_clif's program of `g_u128`
(the premises of `bundle_raw_witness`, with `leBase` and `TlsLoader`): cg_clif's program's run of
`wmul_u128` on `2^64 + 3` and `5` returns `5 * 2^64 + 15`, and the hook-free executable machine
returns `15, 5` in x0, x1. -/
theorem bundle_raw_tls_witness :
    ∃ σ : Clif.Ren,
      Front.link us (Front.finOf us) = (Front.rawLink us scd).rename σ.fwd ∧
      Clif.runLoop (helperEnv.ren σ.symm) (Front.rawLink us scd) M (cs.ren σ.symm) =
        .returned [⟨.i128, 5#64 ++ 15#64⟩] ((LinkWitness.retMem run).ren σ.symm) ∧
      ∃ k, ArmRet ra0 (r (memOf file)) (runX (stepT J helperBase file) k (r (memOf file))) ∧
        XHolds ⟨.i64, 15#64⟩ (xreg 0 (runX (stepT J helperBase file) k (r (memOf file)))) ∧
        XHolds ⟨.i64, 5#64⟩ (xreg 1 (runX (stepT J helperBase file) k (r (memOf file)))) := by
  obtain ⟨hf, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hst, htls, hdivB, hindB,
    hsigsB, hslotsB, hsrc⟩ := FrontendBundleWitness.facts
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
  have hslots : ∀ g ∈ J.srcProg.funcs, g.slots = [] :=
    fun g hg => by simpa using List.all_eq_true.mp hslotsB g hg
  have hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f0.sig.params).getD []) args args' := by
    rw [hsig0, gp, Option.getD_some]
    exact ⟨⟨3#64, 1#64, rfl, rfl, rfl⟩, ⟨5#64, 0#64, rfl, rfl, rfl⟩, trivial⟩
  have hoc := outsideCall (memOf file) (BinCheck.roByte J S.data) hst
  have hσr : Front.link us (Front.finOf us) = (Front.rawLink us scd).rename σ.fwd := by
    rw [rawLink_eq]; exact hσ
  have hf0r : (Front.rawLink us scd).func? n = some f0 := by rw [rawLink_eq]; exact hf0
  have H := Front.bundle_correct_raw_tls (r := r (memOf file)) (args := args) (args' := args')
    (cs := cs.ren σ.symm) (cs' := cs') buildSpec_eq compile_eq hsrc hus scd_ok hσr
    (helperEnv.ren σ.symm) helperBase (Front.Env.ren_symm_ren σ _).symm
    (baseOk_le (baseOk_helper (fun g hg => by simpa using List.all_eq_true.mp htls g hg)
      hdiv hind (fun g hg => by simpa using List.all_eq_true.mp hsigsB g hg)))
    (Link.DeadCleanup.SourceWitness.hooksSim_helper _).call
    (fun _ => ⟨Link.SourceWitness.helperOk, Link.SourceWitness.extLegal,
      Link.SourceWitness.keepsBounded⟩)
    (fun ⟨g, hg, hn⟩ => absurd (hind g hg) hn) hf0r (by rw [hfs]; exact acyclic)
    (intact file) (tlsLoader_helper (tp_r_raw _) noTlsReloc_raw okB_J) (by rw [hfs]; exact hoc)
    (by rw [hfs]; exact clifRun _)
    (pre_entry hfs clifEntry) hexp rfl (Front.Mem.ren_symm_ren σ cm).symm
    (by rw [rawLink_eq]; exact pre_bnd hP (Link.SourceWitness.srcBounded hsrc hslots
      (Clif.Program.func?_some hf).1 clifEntry cm_bounded)) M
  have hrun0 := pre_run hP run_eq
  have hrun0r : Clif.runLoop (helperEnv.ren σ.symm) (Front.rawLink us scd) M (cs.ren σ.symm) =
      .returned [⟨.i128, 5#64 ++ 15#64⟩] ((LinkWitness.retMem run).ren σ.symm) := by
    rw [rawLink_eq]; exact hrun0
  have h := H.1 _ _ hrun0r
  rw [hfs, hsig0, x30_r] at h
  obtain ⟨vals', hrel, k, hret, hx, -⟩ := h
  rw [gr, Option.getD_some] at hrel
  cases split_ret hrel
  exact ⟨σ, hσr, hrun0r, k, hret, hx 0 _ rfl, hx 1 _ rfl⟩

end Raw

end Crates.DeadCleanupExeTlsWitness
