import Crates.FrontendBundleWitness
import FV.Front.RawExe

/-! # Non-vacuity of the theorems about cg_clif's program (T7b, T7c) on a real codegen unit

The bundle `bw` of `Crates.FrontendBundleWitness`: cg_clif's dumps of `wmul_u128` and of the
local `wrapping_mul` of the survey crate `g_u128`, as the patched cg_clif wrote them.

* `raw_names`: in cg_clif's program (`PCgu.raw`, read from the dumps without the decoding) the
  two functions are the module identities `u0:27` and `u0:3`, and `wmul_u128` calls `u0:3`; the
  unit's declarations (`PCgu.ren`, the dumps' tables) name them `wmul_u128` and
  `_RNvMs8_…wrapping_mul`.
* `scd_ok`: naming each module identity by its declared symbol (`scd`, `Front.rawScoping_of` of
  the pre-renaming scoping) is a naming of cg_clif's program (`Front.RawScopingOk`), and
  cg_clif's program under it is the decoded pre-renaming program (`rawLink_eq`,
  `Front.rawLink_decl`).
* **`bundle_raw_witness`**: `Front.bundle_correct_raw` instantiated, all premises discharged
  (those of `Crates.FrontendBundleWitness.bundle_source_witness`): cg_clif's program's CLIF run of
  `wmul_u128` on `2^64 + 3` and `5` returns `5 * 2^64 + 15`, and the executable machine, called
  with the split arguments in x0–x3, returns `15, 5` in x0, x1.
-/

namespace Crates.FrontendBundleWitnessRaw

open E2E E2E.LinkCheck E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes Backend Backend.Proof
  Opt.Legalize128
open Link (LinkSpec)
open Link.SourceWitness (helperEnv helperBase)
open Crates.BinaryWitness (memOf)
open Crates.CompileExeSourceWitness (n args args' M ra0)
open Crates.FrontendBundleWitness

/-- cg_clif's functions are named by module identities; `wmul_u128` calls `wrapping_mul` by its
identity; the declarations name them. -/
theorem raw_names :
    u0.raw.map (·.name) = ["u0:27", "u0:3"] ∧
    (u0.raw.headD default).externs.map (·.2.name) = ["u0:3"] ∧
    u0.raw.map (fun g => u0.ren g.name) = [n, mulClif] := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-- **The declarations' naming of cg_clif's program** (each module identity named by its declared
symbol, then by the pre-renaming scoping `sc`). -/
def scd : Nat → String → String :=
  fun i a => match us[i]? with | some u => sc i (u.ren a) | none => sc i a

theorem scd_ok : Front.RawScopingOk us scd := Front.rawScoping_of (Front.units_ok hus) sc_ok

/-- cg_clif's program under `scd` is the decoded pre-renaming program. -/
theorem rawLink_eq : Front.rawLink us scd = Front.link us sc :=
  Front.rawLink_decl (Front.units_ok hus) sc

/-- **Per-run non-vacuity of `Front.bundle_correct_raw`** on the real codegen unit of `g_u128`:
the linked program is cg_clif's program under the naming `scd` renamed by a bijection `σ`;
cg_clif's program's run of `wmul_u128` on `2^64 + 3` and `5` (in the outside world `helperBase`
renamed back) returns `5 * 2^64 + 15`, and the executable returns `15, 5` in x0, x1. -/
theorem bundle_raw_witness :
    Front.RawScopingOk us scd ∧ (Front.rawLink us scd).func? n = some f0 ∧
    ∃ σ : Clif.Ren,
      Front.link us (Front.finOf us) = (Front.rawLink us scd).rename σ.fwd ∧
      Clif.runLoop (helperEnv.ren σ.symm) (Front.rawLink us scd) M (cs.ren σ.symm) =
        .returned [⟨.i128, 5#64 ++ 15#64⟩] ((LinkWitness.retMem run).ren σ.symm) ∧
      ∃ k, ArmRet ra0 (r (memOf file)) (runX (step J helperBase file) k (r (memOf file))) ∧
        XHolds ⟨.i64, 15#64⟩ (xreg 0 (runX (step J helperBase file) k (r (memOf file)))) ∧
        XHolds ⟨.i64, 5#64⟩ (xreg 1 (runX (step J helperBase file) k (r (memOf file)))) := by
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
  have H := Front.bundle_correct_raw (r := r (memOf file)) (args := args) (args' := args')
    (cs := cs.ren σ.symm) (cs' := cs') buildSpec_eq compile_eq hsrc hus scd_ok hσr
    (helperEnv.ren σ.symm) helperBase (Front.Env.ren_symm_ren σ _).symm
    (Link.SourceWitness.baseOk_helper (fun g hg => by simpa using List.all_eq_true.mp htls g hg)
      hdiv hind (fun g hg => by simpa using List.all_eq_true.mp hsigsB g hg))
    (Link.DeadCleanup.SourceWitness.hooksSim_helper _)
    (fun _ => ⟨Link.SourceWitness.helperOk, Link.SourceWitness.extLegal,
      Link.SourceWitness.keepsBounded⟩)
    (fun ⟨g, hg, hn⟩ => absurd (hind g hg) hn) hf0r (by rw [hfs]; exact acyclic)
    (intact file) (by rw [hfs]; exact hoc) (by rw [hfs]; exact clifRun _)
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
  exact ⟨scd_ok, hf0r, σ, hσr, hrun0r, k, hret, hx 0 _ rfl, hx 1 _ rfl⟩

end Crates.FrontendBundleWitnessRaw
