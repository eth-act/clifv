import Crates.FrontendBundleWitnessRaw
import Crates.FrontendBundleWitnessPeak
import FV.Front.RawExeContract

/-! # Non-vacuity of the runtime-contract theorems (A5, #411) on a real codegen unit

The bundle, executable, renaming and run of `Crates.FrontendBundleWitness` (`wmul_u128` and the
local `wrapping_mul` of `g_u128`'s codegen unit, the shipped compiler), with cg_clif's naming of
`Crates.FrontendBundleWitnessRaw`.

* `not_ro`: every `PT_LOAD` segment of the written executable ends below `sp0 - 2^20` (decided on
  its program headers), so the `2^20` bytes below `sp0` are in no read-only segment.
* `contract`: the single runtime contract `Front.EntryContract` holds for the outside call of the
  compiled `wmul_u128` with the split arguments in x0–x3 and up to `2^20` bytes of stack (the
  outside world `helperBase`; the loader's kept bytes; the AAPCS64 entry); `view`: the CLIF view.
* **`bundle_raw_contract_witness`**, **`bundle_raw_peak_contract_witness`**:
  `Front.bundle_correct_raw_contract` and `Front.bundle_correct_raw_peak_contract` instantiated:
  cg_clif's program's run of `wmul_u128` on `2^64 + 3` and `5` returns `5 * 2^64 + 15`, and the
  executable machine returns `15, 5` in x0, x1.
-/

namespace Crates.FrontendBundleWitnessContract

open E2E E2E.LinkCheck E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes E2E.EntryContract Backend
  Backend.Proof Opt.Legalize128
open Link (LinkSpec)
open Link.SourceWitness (helperEnv helperBase)
open Crates.BinaryWitness (memOf)
open Crates.CompileExeSourceWitness (n args args' M ra0 sp0 sp0_toNat)
open Crates.FrontendBundleWitness
open Crates.FrontendBundleWitnessRaw (scd scd_ok rawLink_eq)

/-- Every `PT_LOAD` segment of the executable ends `2^20` bytes below `sp0 = 2^40`. -/
def loadBelowB : Bool :=
  match Elf.phdrs (Elf.fileRd file) with
  | some phs => phs.all fun p => p.type != 1 || decide (p.vaddr + p.memsz + 2 ^ 20 ≤ 2 ^ 40)
  | none => false

theorem loadBelowB_true : loadBelowB = true := by native_decide

/-- The `N ≤ 2^20` bytes below `sp0` are in no read-only segment of the executable. -/
theorem not_ro {N : Nat} (hN : N ≤ 2 ^ 20) {a : BitVec 64} (hb : StackBelow N sp0 a) :
    ¬ Elf.ro file a := by
  rintro ⟨phs, p, hp, hs, -⟩
  have h := loadBelowB_true
  unfold loadBelowB at h
  rw [hp] at h
  have hmem := List.mem_of_find?_eq_some hs
  have hl := List.find?_some hs
  have hp' := List.all_eq_true.mp h p hmem
  simp only [Elf.isLoad, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hl
  simp only [bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq] at hp'
  obtain ⟨⟨h1, h2⟩, h3⟩ := hl
  unfold StackBelow at hb
  rw [sp0_toNat] at hb
  rcases hp' with h4 | h4
  · exact h4 h1
  · omega

/-- **The loader's contract**: the machine holds the loaded image of the executable; `N ≤ 2^20`
bytes of writable stack below `sp0`. -/
theorem loader {N : Nat} (hN : N ≤ 2 ^ 20) : Loader file N (r (memOf file)) where
  intact := intact file
  stack := by rw [spv_r, sp0_toNat]; omega
  stackRw := fun a hb => not_ro hN (by rw [spv_r] at hb; exact hb)

/-- **The outside caller's contract**: the AAPCS64 entry of the legalised `wmul_u128` with the
split arguments in x0–x3. -/
theorem caller : Caller J file (legalize fs) (r (memOf file)) args' where
  pc := (outsideCall (memOf file) (fun _ => none) (N := 0) (Nat.zero_le _)).pc
  err := (outsideCall (memOf file) (fun _ => none) (N := 0) (Nat.zero_le _)).err
  ra := (outsideCall (memOf file) (fun _ => none) (N := 0) (Nat.zero_le _)).ra
  spAligned := (outsideCall (memOf file) (fun _ => none) (N := 0) (Nat.zero_le _)).spAligned
  args := fun loc v hm => by
    have h := (outsideCall (memOf file) (fun _ => none) (N := 0) (Nat.zero_le _)).args loc v hm
    rw [facts.2.2.1, locs] at hm
    simp only [args', List.zip_cons_cons, List.zip_nil_right, List.mem_cons, Prod.mk.injEq,
      List.not_mem_nil, or_false] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact h

/-- **The CLIF view** of the entry: no live allocation, the CLIF image's symbols, the reference
run `clifRun`. -/
theorem view {N : Nat} : ClifView J helperBase (legalize fs) N (r (memOf file)) args' cs' where
  bytes := fun _ _ hv => by simp [cs', cm, Clif.Mem.valid] at hv
  valid := fun _ _ hv => by simp [cs', cm, Clif.Mem.valid] at hv
  symbols := rfl
  run := clifRun _

/-- **The runtime contract holds** for the outside call of the compiled `wmul_u128` with up to
`2^20` bytes of stack. -/
theorem contract {N : Nat} (hN : N ≤ 2 ^ 20) :
    Front.EntryContract S helperBase file (legalize fs) N (r (memOf file)) args' := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, htls, hdivB, hindB,
    hsigsB, -, -⟩ := FrontendBundleWitness.facts
  have hind : ∀ g ∈ (prog J).funcs, Clif.IndFree g :=
    fun g hg => indFreeB_sound (List.all_eq_true.mp hindB g hg)
  have hdiv : ∀ g ∈ (prog J).funcs, ∀ e ∈ g.externs, (prog J).func? e.2.name = none →
      Clif.Rust.isDivHelper e.2.name = false := by
    intro g hg e he hn
    have := List.all_eq_true.mp (List.all_eq_true.mp hdivB g hg) e he
    simpa [hn] using this
  exact {
    base := Link.SourceWitness.baseOk_helper
      (fun g hg => by simpa using List.all_eq_true.mp htls g hg) hdiv hind
      (fun g hg => by simpa using List.all_eq_true.mp hsigsB g hg)
    hooks := Link.DeadCleanup.SourceWitness.hooksSim_helper _
    legal := fun _ => ⟨Link.SourceWitness.helperOk, Link.SourceWitness.extLegal,
      Link.SourceWitness.keepsBounded⟩
    sigs := fun ⟨g, hg, hn⟩ => absurd (hind g hg) hn
    loader := loader hN
    caller := caller }

/-- **Per-run non-vacuity of `Front.bundle_correct_raw_contract`**: as
`Crates.FrontendBundleWitnessRaw.bundle_raw_witness`, with the runtime contract `contract` and the
CLIF view `view` in place of the seven entry premises. -/
theorem bundle_raw_contract_witness :
    Front.RawScopingOk us scd ∧ (Front.rawLink us scd).func? n = some f0 ∧
    ∃ σ : Clif.Ren,
      Front.link us (Front.finOf us) = (Front.rawLink us scd).rename σ.fwd ∧
      Clif.runLoop (helperEnv.ren σ.symm) (Front.rawLink us scd) M (cs.ren σ.symm) =
        .returned [⟨.i128, 5#64 ++ 15#64⟩] ((LinkWitness.retMem run).ren σ.symm) ∧
      ∃ k, ArmRet ra0 (r (memOf file)) (runX (step J helperBase file) k (r (memOf file))) ∧
        XHolds ⟨.i64, 15#64⟩ (xreg 0 (runX (step J helperBase file) k (r (memOf file)))) ∧
        XHolds ⟨.i64, 5#64⟩ (xreg 1 (runX (step J helperBase file) k (r (memOf file)))) := by
  obtain ⟨hf, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hst, -, -, -,
    -, hslotsB, hsrc⟩ := FrontendBundleWitness.facts
  obtain ⟨σ, hσ, hσn, -⟩ := alpha
  have hP := srcProg_eq hσ
  have hfs : f0.rename σ.fwd = fs := pre_fn hP hσn hf
  have hsig0 : f0.sig = fs.sig := by rw [← hfs, Clif.Function.rename_sig]
  have hslots : ∀ g ∈ J.srcProg.funcs, g.slots = [] :=
    fun g hg => by simpa using List.all_eq_true.mp hslotsB g hg
  have hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f0.sig.params).getD []) args args' := by
    rw [hsig0, gp, Option.getD_some]
    exact ⟨⟨3#64, 1#64, rfl, rfl, rfl⟩, ⟨5#64, 0#64, rfl, rfl, rfl⟩, trivial⟩
  have hσr : Front.link us (Front.finOf us) = (Front.rawLink us scd).rename σ.fwd := by
    rw [rawLink_eq]; exact hσ
  have hf0r : (Front.rawLink us scd).func? n = some f0 := by rw [rawLink_eq]; exact hf0
  have H := Front.bundle_correct_raw_contract (r := r (memOf file)) (args := args) (args' := args')
    (cs := cs.ren σ.symm) (cs' := cs') buildSpec_eq compile_eq hsrc hus scd_ok hσr
    (helperEnv.ren σ.symm) helperBase (Front.Env.ren_symm_ren σ _).symm hf0r
    (by rw [hfs]; exact acyclic) (by rw [hfs]; exact contract hst) (by rw [hfs]; exact view)
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

/-- **Per-run non-vacuity of `Front.bundle_correct_raw_peak_contract`**: as
`bundle_raw_contract_witness`, the source run's call depth `d = 1`
(`Crates.FrontendBundleWitnessPeak.depth`) instead of the call-graph premise, and
`frameDrop + D * 1` bytes of stack. -/
theorem bundle_raw_peak_contract_witness :
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
  obtain ⟨hf, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, hslotsB, hsrc⟩ := FrontendBundleWitness.facts
  obtain ⟨σ, hσ, hσn, -⟩ := alpha
  have hP := srcProg_eq hσ
  have hfs : f0.rename σ.fwd = fs := pre_fn hP hσn hf
  have hsig0 : f0.sig = fs.sig := by rw [← hfs, Clif.Function.rename_sig]
  have hslots : ∀ g ∈ J.srcProg.funcs, g.slots = [] :=
    fun g hg => by simpa using List.all_eq_true.mp hslotsB g hg
  have hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f0.sig.params).getD []) args args' := by
    rw [hsig0, gp, Option.getD_some]
    exact ⟨⟨3#64, 1#64, rfl, rfl, rfl⟩, ⟨5#64, 0#64, rfl, rfl, rfl⟩, trivial⟩
  have hσr : Front.link us (Front.finOf us) = (Front.rawLink us scd).rename σ.fwd := by
    rw [rawLink_eq]; exact hσ
  have hf0r : (Front.rawLink us scd).func? n = some f0 := by rw [rawLink_eq]; exact hf0
  have hd : Clif.DepthLe (helperEnv.ren σ.symm) (Front.rawLink us scd) FrontendBundleWitnessPeak.d
      (cs.ren σ.symm) := by
    rw [rawLink_eq]; exact pre_depth hP FrontendBundleWitnessPeak.depth
  have H := Front.bundle_correct_raw_peak_contract (r := r (memOf file)) (args := args)
    (args' := args') (cs := cs.ren σ.symm) (cs' := cs') buildSpec_eq compile_eq hsrc hus scd_ok hσr
    (helperEnv.ren σ.symm) helperBase (Front.Env.ren_symm_ren σ _).symm hf0r
    FrontendBundleWitnessPeak.d
    (by rw [hfs]; exact contract FrontendBundleWitnessPeak.stack_le) (by rw [hfs]; exact view)
    (pre_entry hfs clifEntry) hexp rfl (Front.Mem.ren_symm_ren σ cm).symm
    (by rw [rawLink_eq]; exact pre_bnd hP (Link.SourceWitness.srcBounded hsrc hslots
      (Clif.Program.func?_some hf).1 clifEntry cm_bounded)) hd M
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

end Crates.FrontendBundleWitnessContract
