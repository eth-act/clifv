import Crates.CompileExeOptPeakWitness
import Crates.DeadCleanupExeOptPeakWitness
import FV.Link.NonVacuityOptExeSource
import FV.Link.OptExeSourceNB
import FV.Link.DeadCleanupOptExeSourceNB

/-! # Per-run non-vacuity of the optimising compilers' peak-call-depth source theorems without
the memory-bound premise (A2/B1)

The witnesses of `Link.compileExeOpt_correct_source_peak` and
`Link.DeadCleanup.compileExeOpt_correct_source_peak`
(`Crates.CompileExeOptPeakWitness`, `Crates.DeadCleanupExeOptPeakWitness`: the optimised
`rec128`, a recursive `i128` program) for their `_nobnd` variants: the same runs and the same
executable, every premise discharged — without the source run's memory bound
(`∀ s', Opt.Legal.SReach _ _ cs s' → Opt.Legal.MemBounded s'.mem`), which the variants derive
(`srcBoundedOpt_peak`). The source fixture's memory is the same `cm` with the slot-placement
oracle of `helperBase`'s frames (like `Crates.CompileExeSourcePeakWitness.cm`), and the outside
world is `Link.SourceWitness.helperBase`.

* `compileExeOpt_source_peak_nobnd_witness`: `Link.compileExeOpt_correct_source_peak_nobnd`;
* `cleanup_opt_source_peak_nobnd_witness`:
  `Link.DeadCleanup.compileExeOpt_correct_source_peak_nobnd`.
-/

namespace Crates.CompileExeOptSourcePeakNBWitness

open E2E E2E.LinkCheck E2E.Binary E2E.ExecBytes Backend Backend.Proof Link
  Opt.Legalize128
open Link.SourceWitness (helperEnv helperBase baseOk_helper hooksSim_helper
  envKeepsSymbols_helper helperOk extLegal keepsBounded)
open Crates.BinaryWitness (memOf)
open Crates.CompileExeSourcePeakWitness (n args args' d sp0 ra0 sp0_toNat)
open Crates.CompileExeOptPeakWitness (spec file0 file compile_eq I0 J f0 f b0 bF regs locB locs img_lt
  setMany_eq)

/-- The source `rec128` and its entry block. -/
def fsS : Clif.Function := Crates.CompileExeSourcePeakWitness.fs
def bS : Clif.Block := Crates.CompileExeSourcePeakWitness.bS

/-- The run's fuel (the source run returns within it). -/
def M : Nat := 24

/-- The body's stack pointer of the entry (`helperBase`'s oracle). -/
def sb : BitVec 64 := sp0 - BitVec.ofNat 64 (frameDrop (artOf J.results f).af)

/-- The caller's CLIF memory: no live allocation, the CLIF image's symbols, the slot-placement
oracle at the entry's body `sp` with `helperBase`'s frames. -/
def cm : Clif.Mem :=
  { symbols := fun n => J.syms.lookup n, place := some ⟨[sb], (sys J helperBase).frames⟩ }

/-- The source entry state of the original `rec128` on `x`, `n` (the source function's entry
block's parameters bound to the `i128` argument and `n`, `helperBase`'s memory). -/
def cs : Clif.State where
  frame := { func := fsS,
             regs := (Clif.Regs.empty.setMany (bS.params.map (·.1)) args).getD default,
             slots := [], body := bS.body, term := bS.term }
  callers := []
  mem := cm

/-- The target entry state of the optimised `rec128` on the split arguments (the same memory). -/
def cs' : Clif.State where
  frame := { func := f, regs, slots := [], body := bF.body, term := bF.term }
  callers := []
  mem := cm

/-- The original program's CLIF run from `cs` (the source `rec128` returns `8 * x`). -/
def run : Clif.Outcome := Clif.runLoop helperEnv I0.srcProg M cs

/-- The machine state of the call with memory `m`: pc at `f`'s address, x30 the caller's return
address, `sp0`, the split arguments in x0–x2. -/
def r (m : Arm.Memory) : Arm.ArmState :=
  Arm.w .PC (artOf J.results f).base (Arm.w (.GPR 30#5) ra0 (Arm.w (.GPR 31#5) sp0
    (Arm.w (.GPR 0#5) 3#64 (Arm.w (.GPR 1#5) 1#64 (Arm.w (.GPR 2#5) 3#64
      (setMem Arm.ArmState.default m))))))

/-- The facts decided on the source and the optimised program, under `helperBase`. -/
def factsB : Bool :=
  decide (I0.srcProg.func? n = some fsS) && decide ((prog I0).func? n = some f0) &&
  decide ((prog J).func? n = some f) && decide (f0 ≠ f) && mentions128 fsS &&
  decide (fsS.entry? = some bS) && decide (f0.entry? = some b0) && decide (f.entry? = some bF) &&
  decide (b0.params = bF.params) &&
  decide (args.map (·.ty) = fsS.sig.params.map (·.ty)) &&
  decide (bS.params.map (·.2) = args.map (·.ty)) &&
  (Clif.Regs.empty.setMany (bS.params.map (·.1)) args).isSome &&
  decide (args'.map (·.ty) = f0.sig.params.map (·.ty)) &&
  decide (args'.map (·.ty) = f.sig.params.map (·.ty)) &&
  decide (bF.params.map (·.2) = args'.map (·.ty)) &&
  (Clif.Regs.empty.setMany (bF.params.map (·.1)) args').isSome &&
  decide (fsS.slots = []) && decide (f0.slots = []) && decide (f.slots = []) && locB &&
  LinkWitness.isRet run && decide (LinkWitness.retVals run = [⟨.i128, 8#64 ++ 24#64⟩]) &&
  Clif.depthB helperEnv I0.srcProg d M cs &&
  (tabOf J.results).all (fun e => decide (e.2.base.toNat + 4 * e.2.fb.words.size + 4 ≤ 2 ^ 32)) &&
  !StackBound.goodN J n && decide (frameDrop (artOf J.results f).af + J.D * d ≤ 2 ^ 20) &&
  (prog J).funcs.all (fun g => !Backend.hasTls g) &&
  (prog J).funcs.all (fun g => g.externs.all fun e =>
    ((prog J).func? e.2.name).isSome || !Clif.Rust.isDivHelper e.2.name) &&
  (prog J).funcs.all indFreeB && (prog J).funcs.all (fun g => (indSigs g).isEmpty) &&
  I0.srcProg.funcs.all (fun g => g.slots.isEmpty) && SrcScopeB I0

theorem factsB_true : factsB = true := by native_decide

theorem facts :
    I0.srcProg.func? n = some fsS ∧ (prog I0).func? n = some f0 ∧ (prog J).func? n = some f ∧
    f0 ≠ f ∧ mentions128 fsS = true ∧ fsS.entry? = some bS ∧ f0.entry? = some b0 ∧
    f.entry? = some bF ∧ b0.params = bF.params ∧
    args.map (·.ty) = fsS.sig.params.map (·.ty) ∧ bS.params.map (·.2) = args.map (·.ty) ∧
    (Clif.Regs.empty.setMany (bS.params.map (·.1)) args).isSome = true ∧
    args'.map (·.ty) = f0.sig.params.map (·.ty) ∧ args'.map (·.ty) = f.sig.params.map (·.ty) ∧
    bF.params.map (·.2) = args'.map (·.ty) ∧
    (Clif.Regs.empty.setMany (bF.params.map (·.1)) args').isSome = true ∧
    fsS.slots = [] ∧ f0.slots = [] ∧ f.slots = [] ∧ locB = true ∧
    LinkWitness.isRet run = true ∧ LinkWitness.retVals run = [⟨.i128, 8#64 ++ 24#64⟩] ∧
    Clif.depthB helperEnv I0.srcProg d M cs = true ∧
    (tabOf J.results).all (fun e => decide (e.2.base.toNat + 4 * e.2.fb.words.size + 4 ≤ 2 ^ 32))
      = true ∧
    StackBound.goodN J n = false ∧ frameDrop (artOf J.results f).af + J.D * d ≤ 2 ^ 20 ∧
    (prog J).funcs.all (fun g => !Backend.hasTls g) = true ∧
    (prog J).funcs.all (fun g => g.externs.all fun e =>
      ((prog J).func? e.2.name).isSome || !Clif.Rust.isDivHelper e.2.name) = true ∧
    (prog J).funcs.all indFreeB = true ∧ (prog J).funcs.all (fun g => (indSigs g).isEmpty) = true ∧
    I0.srcProg.funcs.all (fun g => g.slots.isEmpty) = true ∧ SrcScopeB I0 = true := by
  have h := factsB_true
  simp only [factsB, Bool.and_assoc, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨hfs, hf0, hf, hne, hm, hbs, hb0, hbf, hbpar, hsigS, hparS, hsetS, hpar0, hparF, hparB, hsetF, hslS, hsl0, hslF, hloc, hisRet, hretV, hdepthB, htab, hgood, hstack, htls, hdivB, hindB, hsigsB, hslotsB, hsrc⟩ := h
  exact ⟨hfs, hf0, hf, hne, hm, hbs, hb0, hbf, hbpar, hsigS, hparS, hsetS, hpar0, hparF, hparB, hsetF, hslS, hsl0, hslF, hloc, hisRet, hretV, hdepthB, htab, hgood, hstack, htls, hdivB, hindB, hsigsB, hslotsB, hsrc⟩

/-- The input's (unoptimised) program has no indirect call. -/
theorem indFree0 : (prog I0).funcs.all indFreeB = true := by native_decide

/-- The source run's call depth is at most `d = 3`. -/
theorem depth : Clif.DepthLe helperEnv I0.srcProg d cs :=
  Clif.depthLe_of_depthB M cs facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- The source run of `rec128` on `2^64 + 3`, `3` returns `8 * 2^64 + 24`. -/
theorem run_eq : run = .returned [⟨.i128, 8#64 ++ 24#64⟩] (LinkWitness.retMem run) := by
  rw [← facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
  exact LinkWitness.eq_returned facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- The source entry registers. -/
def regsS : Clif.Regs := (Clif.Regs.empty.setMany (bS.params.map (·.1)) args).getD default

theorem setManyS_eq : Clif.Regs.empty.setMany (bS.params.map (·.1)) args = some regsS := by
  have hset := facts.2.2.2.2.2.2.2.2.2.2.2.1
  show _ = some ((Clif.Regs.empty.setMany (bS.params.map (·.1)) args).getD default)
  revert hset
  cases Clif.Regs.empty.setMany (bS.params.map (·.1)) args <;> simp

section State

variable (m : Arm.Memory)

theorem pc_r : Arm.r .PC (r m) = (artOf J.results f).base := Arm.r_of_w_same

theorem spv_r : spv (r m) = sp0 := by
  simp only [spv, r]
  rw [Arm.r_of_w_different (by decide), Arm.r_of_w_different (by decide), Arm.r_of_w_same]

theorem x30_r : xreg 30 (r m) = ra0 := by
  simp only [xreg, r]
  rw [Arm.r_of_w_different (by decide), Arm.r_of_w_same]

theorem err_r : Arm.r .ERR (r m) = .None := by
  simp only [r]
  rw [Arm.r_of_w_different (by decide), Arm.r_of_w_different (by decide),
    Arm.r_of_w_different (by decide), Arm.r_of_w_different (by decide),
    Arm.r_of_w_different (by decide), Arm.r_of_w_different (by decide), r_setMem]
  simp [Arm.r, Arm.read_base_error, Arm.ArmState.default]

theorem x0_r : Arm.r (.GPR (rnum 0)) (r m) = 3#64 := by
  simp only [r, rnum]
  rw [Arm.r_of_w_different (by decide), Arm.r_of_w_different (by decide),
    Arm.r_of_w_different (by decide), Arm.r_of_w_same]

theorem x1_r : Arm.r (.GPR (rnum 1)) (r m) = 1#64 := by
  simp only [r, rnum]
  rw [Arm.r_of_w_different (by decide), Arm.r_of_w_different (by decide),
    Arm.r_of_w_different (by decide), Arm.r_of_w_different (by decide), Arm.r_of_w_same]

theorem x2_r : Arm.r (.GPR (rnum 2)) (r m) = 3#64 := by
  simp only [r, rnum]
  rw [Arm.r_of_w_different (by decide), Arm.r_of_w_different (by decide),
    Arm.r_of_w_different (by decide), Arm.r_of_w_different (by decide),
    Arm.r_of_w_different (by decide), Arm.r_of_w_same]

/-- The outside caller's contract for the optimised `rec128` in `r m` (the split arguments in
x0–x2) with a stack of `N ≤ 2^20` bytes. -/
theorem outsideCall (roB : BitVec 64 → Option (BitVec 8)) {N : Nat} (hN : N ≤ 2 ^ 20) :
    OutsideCall J roB f N (r m) args' cs'.mem where
  pc := pc_r m
  err := err_r m
  ra := fun h => by have := img_lt h; rw [x30_r] at this; simp [ra0] at this
  spAligned := by rw [spv_r]; decide
  stack := by rw [spv_r, sp0_toNat]; omega
  stackFree := fun a ha hb => by
    have := img_lt ha
    rw [spv_r] at hb
    obtain ⟨-, h2⟩ := hb
    rw [sp0_toNat] at h2
    omega
  args := fun loc v hm => by
    rw [locs] at hm
    simp only [args', List.zip_cons_cons, List.zip_nil_right, List.mem_cons, Prod.mk.injEq,
      List.not_mem_nil, or_false] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp only [VHolds, regVal, x0_r m]; rfl
    · simp only [VHolds, regVal, x1_r m]; rfl
    · simp only [VHolds, regVal, x2_r m]; rfl
  bytes := fun _ _ hv => by simp [cs', cm, Clif.Mem.valid] at hv
  image := fun _ _ _ hv => by simp [cs', cm, Clif.Mem.valid] at hv
  valid := fun _ _ hv => by simp [cs', cm, Clif.Mem.valid] at hv
  symbols := rfl

omit m in
theorem clifEntry' : ClifEntry f args' cs' :=
  ⟨rfl, rfl, facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1, ⟨bF, facts.2.2.2.2.2.2.2.1, rfl, rfl, facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, setMany_eq⟩,
    by simp [cs', facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]⟩

omit m in
theorem clifEntry : ClifEntry fsS args cs :=
  ⟨rfl, rfl, facts.2.2.2.2.2.2.2.2.2.1,
    ⟨bS, facts.2.2.2.2.2.1, rfl, rfl, facts.2.2.2.2.2.2.2.2.2.2.1, setManyS_eq⟩, by simp [cs, facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]⟩

/-- The target entry for `compileExeOpt_correct_source_peak_nobnd` (`helperBase`'s oracle). -/
theorem clifRun : ClifRun J helperBase f (r m) args' cs' where
  entry := clifEntry'
  slots := fun _ _ h => by simp [cs'] at h
  place := fun _ => ⟨[], by
    show some _ = some _
    rw [show spBody (art J f).af (r m) = sb by simp only [spBody, spv_r, sb]]⟩

end State

/-- The machine's memory is the loaded image of any file. -/
theorem intact (file : ByteArray) : (imageOf file).Intact (r (memOf file)) := fun a b _ hb => by
  simp only [r, LinkWitness.mem_w, mem_setMem, memOf]
  exact (congrArg (Option.getD · 0) hb).trans rfl

/-- The base premises of `helperBase` on the optimised input. -/
theorem hBase : BaseOk (sys J helperBase) :=
  baseOk_helper (fun g hg => by simpa using List.all_eq_true.mp facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 g hg)
    (fun g hg e he hn => by
      have h := List.all_eq_true.mp (List.all_eq_true.mp facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 g hg) e he
      simpa [hn] using h)
    (fun g hg => indFreeB_sound (List.all_eq_true.mp facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 g hg))
    (fun g hg => by simpa using List.all_eq_true.mp facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 g hg)

/-- The `i128` contracts of `helperEnv`. -/
theorem hlegal : (∃ g ∈ I0.srcProg.funcs, mentions128 g = true) →
    Opt.Legal.HelperOk helperEnv ∧ Opt.Legal.ExtLegal helperEnv ∧
      Opt.Legal.EnvKeepsBounded helperEnv :=
  fun _ => ⟨helperOk, extLegal, keepsBounded⟩

/-- `helperEnv` declares no helper: `hsig` holds vacuously (the optimised program has no
indirect call). -/
theorem hsig : (∃ g ∈ (prog I0).funcs, ¬ Clif.IndFree g) → ∀ n, helperEnv.sigOf n = none := fun
    ⟨g, hg, hn⟩ => absurd (indFreeB_sound (List.all_eq_true.mp indFree0 g hg)) hn

/-- **Per-run non-vacuity of `compileExeOpt_correct_source_peak_nobnd`** on the recursive `i128` program `rec128`:
`compileExeOpt` produces the executable `file` (the optimised `rec128` the mid-end's result);
the input is in the source domain and `rec128` mentions `i128`; the original program's CLIF run of
`rec128` on `2^64 + 3` and `3` (in `helperEnv`) returns `8 * 2^64 + 24` with call depth at most
`3`; and, the outside code calling the executable's compiled optimised `rec128` with the split
arguments in x0–x2 and `frameDrop + D * 3` bytes of stack, the executable machine returns to the
caller with the split result `24, 8` in x0, x1 — **without** the premise that the source run's
memories lie below `2^64`. -/
theorem compileExeOpt_source_peak_nobnd_witness :
    compileExeOpt spec file0 = .ok file ∧ SrcScopeB I0 = true ∧
    I0.srcProg.func? n = some fsS ∧ (prog J).func? n = some f ∧ mentions128 fsS = true ∧
    Clif.DepthLe helperEnv I0.srcProg d cs ∧
    Clif.runLoop helperEnv I0.srcProg M cs = .returned [⟨.i128, 8#64 ++ 24#64⟩]
      (LinkWitness.retMem run) ∧
    ∃ k, ArmRet ra0 (r (memOf file)) (runX (step J helperBase file) k (r (memOf file))) ∧
      XHolds ⟨.i64, 24#64⟩ (xreg 0 (runX (step J helperBase file) k (r (memOf file)))) ∧
      XHolds ⟨.i64, 8#64⟩ (xreg 1 (runX (step J helperBase file) k (r (memOf file)))) := by
  have hfs := facts.1
  have hf := facts.2.2.1
  have hm := facts.2.2.2.2.1
  have hstack := facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hsrc := facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨p, hgp⟩ := Crates.CompileExeSourcePeakWitness.gp
  have hgp' : Opt.Legal.groups fsS.sig.params = some [[.lo, .hi], [.val p]] := hgp
  have hexp : Opt.Legal.ExpRel ((Opt.Legal.groups fsS.sig.params).getD []) args args' := by
    rw [hgp', Option.getD_some]
    exact ⟨⟨3#64, 1#64, rfl, rfl, rfl⟩, rfl, trivial⟩
  have hoc := outsideCall (memOf file) (BinCheck.roByte J spec.opt.data) hstack
  have h := (compileExeOpt_correct_source_peak_nobnd compile_eq hsrc helperBase hBase (hooksSim_helper _) envKeepsSymbols_helper hlegal hsig
    hfs hf d (intact file) hoc (clifRun _) clifEntry hexp rfl rfl depth M).1 _ _ run_eq
  rw [x30_r] at h
  obtain ⟨vals', hrel, k, hret, hx, -⟩ := h
  have hgr : Opt.Legal.groups fsS.sig.returns = some [[.lo, .hi]] :=
    Crates.CompileExeSourcePeakWitness.gr
  rw [hgr, Option.getD_some] at hrel
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
    exact ⟨compile_eq, hsrc, hfs, hf, hm, depth, run_eq, k, hret, hx 0 _ rfl, hx 1 _ rfl⟩

end Crates.CompileExeOptSourcePeakNBWitness

namespace Crates.DeadCleanupExeOptSourcePeakNBWitness

open E2E E2E.LinkCheck E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes Backend Backend.Proof Link
  Opt.Legalize128
open Link (LinkSpec inScopePar_eq)
open Link.SourceWitness (helperEnv helperBase baseOk_helper hooksSim_helper
  envKeepsSymbols_helper helperOk extLegal keepsBounded)
open Crates.BinaryWitness (memOf)
open Crates.CompileExeSourcePeakWitness (n args args' d sp0 ra0 sp0_toNat)
open Crates.DeadCleanupExeOptPeakWitness (spec file0 file compile_eq I0 J f0 f b0 bF regs locB locs img_lt
  setMany_eq)

/-- The source `rec128` and its entry block. -/
def fsS : Clif.Function := Crates.CompileExeSourcePeakWitness.fs
def bS : Clif.Block := Crates.CompileExeSourcePeakWitness.bS

/-- The run's fuel (the source run returns within it). -/
def M : Nat := 24

/-- The body's stack pointer of the entry (`helperBase`'s oracle). -/
def sb : BitVec 64 := sp0 - BitVec.ofNat 64 (frameDrop (artOf J.resultsCleanup f).af)

/-- The caller's CLIF memory: no live allocation, the CLIF image's symbols, the slot-placement
oracle at the entry's body `sp` with `helperBase`'s frames. -/
def cm : Clif.Mem :=
  { symbols := fun n => J.syms.lookup n, place := some ⟨[sb], (sys J helperBase).frames⟩ }

/-- The source entry state of the original `rec128` on `x`, `n` (the source function's entry
block's parameters bound to the `i128` argument and `n`, `helperBase`'s memory). -/
def cs : Clif.State where
  frame := { func := fsS,
             regs := (Clif.Regs.empty.setMany (bS.params.map (·.1)) args).getD default,
             slots := [], body := bS.body, term := bS.term }
  callers := []
  mem := cm

/-- The target entry state of the optimised `rec128` on the split arguments (the same memory). -/
def cs' : Clif.State where
  frame := { func := f, regs, slots := [], body := bF.body, term := bF.term }
  callers := []
  mem := cm

/-- The original program's CLIF run from `cs` (the source `rec128` returns `8 * x`). -/
def run : Clif.Outcome := Clif.runLoop helperEnv I0.srcProg M cs

/-- The machine state of the call with memory `m`: pc at `f`'s address, x30 the caller's return
address, `sp0`, the split arguments in x0–x2. -/
def r (m : Arm.Memory) : Arm.ArmState :=
  Arm.w .PC (artOf J.resultsCleanup f).base (Arm.w (.GPR 30#5) ra0 (Arm.w (.GPR 31#5) sp0
    (Arm.w (.GPR 0#5) 3#64 (Arm.w (.GPR 1#5) 1#64 (Arm.w (.GPR 2#5) 3#64
      (setMem Arm.ArmState.default m))))))

/-- The facts decided on the source and the optimised program, under `helperBase`. -/
def factsB : Bool :=
  decide (I0.srcProg.func? n = some fsS) && decide ((prog I0).func? n = some f0) &&
  decide ((prog J).func? n = some f) && decide (f0 ≠ f) && mentions128 fsS &&
  decide (fsS.entry? = some bS) && decide (f0.entry? = some b0) && decide (f.entry? = some bF) &&
  decide (b0.params = bF.params) &&
  decide (args.map (·.ty) = fsS.sig.params.map (·.ty)) &&
  decide (bS.params.map (·.2) = args.map (·.ty)) &&
  (Clif.Regs.empty.setMany (bS.params.map (·.1)) args).isSome &&
  decide (args'.map (·.ty) = f0.sig.params.map (·.ty)) &&
  decide (args'.map (·.ty) = f.sig.params.map (·.ty)) &&
  decide (bF.params.map (·.2) = args'.map (·.ty)) &&
  (Clif.Regs.empty.setMany (bF.params.map (·.1)) args').isSome &&
  decide (fsS.slots = []) && decide (f0.slots = []) && decide (f.slots = []) && locB &&
  LinkWitness.isRet run && decide (LinkWitness.retVals run = [⟨.i128, 8#64 ++ 24#64⟩]) &&
  Clif.depthB helperEnv I0.srcProg d M cs &&
  (tabOf J.resultsCleanup).all (fun e => decide (e.2.base.toNat + 4 * e.2.fb.words.size + 4 ≤ 2 ^ 32)) &&
  !DeadCleanupStackBound.goodN J n && decide (frameDrop (artOf J.resultsCleanup f).af + J.D * d ≤ 2 ^ 20) &&
  (prog J).funcs.all (fun g => !Backend.hasTls g) &&
  (prog J).funcs.all (fun g => g.externs.all fun e =>
    ((prog J).func? e.2.name).isSome || !Clif.Rust.isDivHelper e.2.name) &&
  (prog J).funcs.all indFreeB && (prog J).funcs.all (fun g => (indSigs g).isEmpty) &&
  I0.srcProg.funcs.all (fun g => g.slots.isEmpty) && SrcScopeB I0

theorem factsB_true : factsB = true := by native_decide

theorem facts :
    I0.srcProg.func? n = some fsS ∧ (prog I0).func? n = some f0 ∧ (prog J).func? n = some f ∧
    f0 ≠ f ∧ mentions128 fsS = true ∧ fsS.entry? = some bS ∧ f0.entry? = some b0 ∧
    f.entry? = some bF ∧ b0.params = bF.params ∧
    args.map (·.ty) = fsS.sig.params.map (·.ty) ∧ bS.params.map (·.2) = args.map (·.ty) ∧
    (Clif.Regs.empty.setMany (bS.params.map (·.1)) args).isSome = true ∧
    args'.map (·.ty) = f0.sig.params.map (·.ty) ∧ args'.map (·.ty) = f.sig.params.map (·.ty) ∧
    bF.params.map (·.2) = args'.map (·.ty) ∧
    (Clif.Regs.empty.setMany (bF.params.map (·.1)) args').isSome = true ∧
    fsS.slots = [] ∧ f0.slots = [] ∧ f.slots = [] ∧ locB = true ∧
    LinkWitness.isRet run = true ∧ LinkWitness.retVals run = [⟨.i128, 8#64 ++ 24#64⟩] ∧
    Clif.depthB helperEnv I0.srcProg d M cs = true ∧
    (tabOf J.resultsCleanup).all (fun e => decide (e.2.base.toNat + 4 * e.2.fb.words.size + 4 ≤ 2 ^ 32))
      = true ∧
    DeadCleanupStackBound.goodN J n = false ∧ frameDrop (artOf J.resultsCleanup f).af + J.D * d ≤ 2 ^ 20 ∧
    (prog J).funcs.all (fun g => !Backend.hasTls g) = true ∧
    (prog J).funcs.all (fun g => g.externs.all fun e =>
      ((prog J).func? e.2.name).isSome || !Clif.Rust.isDivHelper e.2.name) = true ∧
    (prog J).funcs.all indFreeB = true ∧ (prog J).funcs.all (fun g => (indSigs g).isEmpty) = true ∧
    I0.srcProg.funcs.all (fun g => g.slots.isEmpty) = true ∧ SrcScopeB I0 = true := by
  have h := factsB_true
  simp only [factsB, Bool.and_assoc, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨hfs, hf0, hf, hne, hm, hbs, hb0, hbf, hbpar, hsigS, hparS, hsetS, hpar0, hparF, hparB, hsetF, hslS, hsl0, hslF, hloc, hisRet, hretV, hdepthB, htab, hgood, hstack, htls, hdivB, hindB, hsigsB, hslotsB, hsrc⟩ := h
  exact ⟨hfs, hf0, hf, hne, hm, hbs, hb0, hbf, hbpar, hsigS, hparS, hsetS, hpar0, hparF, hparB, hsetF, hslS, hsl0, hslF, hloc, hisRet, hretV, hdepthB, htab, hgood, hstack, htls, hdivB, hindB, hsigsB, hslotsB, hsrc⟩

/-- The input's (unoptimised) program has no indirect call. -/
theorem indFree0 : (prog I0).funcs.all indFreeB = true := by native_decide

/-- The source run's call depth is at most `d = 3`. -/
theorem depth : Clif.DepthLe helperEnv I0.srcProg d cs :=
  Clif.depthLe_of_depthB M cs facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- The source run of `rec128` on `2^64 + 3`, `3` returns `8 * 2^64 + 24`. -/
theorem run_eq : run = .returned [⟨.i128, 8#64 ++ 24#64⟩] (LinkWitness.retMem run) := by
  rw [← facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
  exact LinkWitness.eq_returned facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- The source entry registers. -/
def regsS : Clif.Regs := (Clif.Regs.empty.setMany (bS.params.map (·.1)) args).getD default

theorem setManyS_eq : Clif.Regs.empty.setMany (bS.params.map (·.1)) args = some regsS := by
  have hset := facts.2.2.2.2.2.2.2.2.2.2.2.1
  show _ = some ((Clif.Regs.empty.setMany (bS.params.map (·.1)) args).getD default)
  revert hset
  cases Clif.Regs.empty.setMany (bS.params.map (·.1)) args <;> simp

section State

variable (m : Arm.Memory)

theorem pc_r : Arm.r .PC (r m) = (artOf J.resultsCleanup f).base := Arm.r_of_w_same

theorem spv_r : spv (r m) = sp0 := by
  simp only [spv, r]
  rw [Arm.r_of_w_different (by decide), Arm.r_of_w_different (by decide), Arm.r_of_w_same]

theorem x30_r : xreg 30 (r m) = ra0 := by
  simp only [xreg, r]
  rw [Arm.r_of_w_different (by decide), Arm.r_of_w_same]

theorem err_r : Arm.r .ERR (r m) = .None := by
  simp only [r]
  rw [Arm.r_of_w_different (by decide), Arm.r_of_w_different (by decide),
    Arm.r_of_w_different (by decide), Arm.r_of_w_different (by decide),
    Arm.r_of_w_different (by decide), Arm.r_of_w_different (by decide), r_setMem]
  simp [Arm.r, Arm.read_base_error, Arm.ArmState.default]

theorem x0_r : Arm.r (.GPR (rnum 0)) (r m) = 3#64 := by
  simp only [r, rnum]
  rw [Arm.r_of_w_different (by decide), Arm.r_of_w_different (by decide),
    Arm.r_of_w_different (by decide), Arm.r_of_w_same]

theorem x1_r : Arm.r (.GPR (rnum 1)) (r m) = 1#64 := by
  simp only [r, rnum]
  rw [Arm.r_of_w_different (by decide), Arm.r_of_w_different (by decide),
    Arm.r_of_w_different (by decide), Arm.r_of_w_different (by decide), Arm.r_of_w_same]

theorem x2_r : Arm.r (.GPR (rnum 2)) (r m) = 3#64 := by
  simp only [r, rnum]
  rw [Arm.r_of_w_different (by decide), Arm.r_of_w_different (by decide),
    Arm.r_of_w_different (by decide), Arm.r_of_w_different (by decide),
    Arm.r_of_w_different (by decide), Arm.r_of_w_same]

/-- The outside caller's contract for the optimised `rec128` in `r m` (the split arguments in
x0–x2) with a stack of `N ≤ 2^20` bytes. -/
theorem outsideCall (roB : BitVec 64 → Option (BitVec 8)) {N : Nat} (hN : N ≤ 2 ^ 20) :
    OutsideCall J roB f N (r m) args' cs'.mem where
  pc := pc_r m
  err := err_r m
  ra := fun h => by have := img_lt h; rw [x30_r] at this; simp [ra0] at this
  spAligned := by rw [spv_r]; decide
  stack := by rw [spv_r, sp0_toNat]; omega
  stackFree := fun a ha hb => by
    have := img_lt ha
    rw [spv_r] at hb
    obtain ⟨-, h2⟩ := hb
    rw [sp0_toNat] at h2
    omega
  args := fun loc v hm => by
    rw [locs] at hm
    simp only [args', List.zip_cons_cons, List.zip_nil_right, List.mem_cons, Prod.mk.injEq,
      List.not_mem_nil, or_false] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp only [VHolds, regVal, x0_r m]; rfl
    · simp only [VHolds, regVal, x1_r m]; rfl
    · simp only [VHolds, regVal, x2_r m]; rfl
  bytes := fun _ _ hv => by simp [cs', cm, Clif.Mem.valid] at hv
  image := fun _ _ _ hv => by simp [cs', cm, Clif.Mem.valid] at hv
  valid := fun _ _ hv => by simp [cs', cm, Clif.Mem.valid] at hv
  symbols := rfl

omit m in
theorem clifEntry' : ClifEntry f args' cs' :=
  ⟨rfl, rfl, facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1, ⟨bF, facts.2.2.2.2.2.2.2.1, rfl, rfl, facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, setMany_eq⟩,
    by simp [cs', facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]⟩

omit m in
theorem clifEntry : ClifEntry fsS args cs :=
  ⟨rfl, rfl, facts.2.2.2.2.2.2.2.2.2.1,
    ⟨bS, facts.2.2.2.2.2.1, rfl, rfl, facts.2.2.2.2.2.2.2.2.2.2.1, setManyS_eq⟩, by simp [cs, facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]⟩

/-- The target entry for `compileExeOpt_correct_source_peak_nobnd` (`helperBase`'s oracle). -/
theorem clifRun : ClifRun J helperBase f (r m) args' cs' where
  entry := clifEntry'
  slots := fun _ _ h => by simp [cs'] at h
  place := fun _ => ⟨[], by
    show some _ = some _
    rw [show spBody (art J f).af (r m) = sb by simp only [spBody, spv_r, sb]]⟩

end State

/-- The machine's memory is the loaded image of any file. -/
theorem intact (file : ByteArray) : (imageOf file).Intact (r (memOf file)) := fun a b _ hb => by
  simp only [r, LinkWitness.mem_w, mem_setMem, memOf]
  exact (congrArg (Option.getD · 0) hb).trans rfl

/-- The base premises of `helperBase` on the optimised input. -/
theorem hBase : BaseOk (sys J helperBase) :=
  baseOk_helper (fun g hg => by simpa using List.all_eq_true.mp facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 g hg)
    (fun g hg e he hn => by
      have h := List.all_eq_true.mp (List.all_eq_true.mp facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 g hg) e he
      simpa [hn] using h)
    (fun g hg => indFreeB_sound (List.all_eq_true.mp facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 g hg))
    (fun g hg => by simpa using List.all_eq_true.mp facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 g hg)

/-- The `i128` contracts of `helperEnv`. -/
theorem hlegal : (∃ g ∈ I0.srcProg.funcs, mentions128 g = true) →
    Opt.Legal.HelperOk helperEnv ∧ Opt.Legal.ExtLegal helperEnv ∧
      Opt.Legal.EnvKeepsBounded helperEnv :=
  fun _ => ⟨helperOk, extLegal, keepsBounded⟩

/-- `helperEnv` declares no helper: `hsig` holds vacuously (the optimised program has no
indirect call). -/
theorem hsig : (∃ g ∈ (prog I0).funcs, ¬ Clif.IndFree g) → ∀ n, helperEnv.sigOf n = none := fun
    ⟨g, hg, hn⟩ => absurd (indFreeB_sound (List.all_eq_true.mp indFree0 g hg)) hn

/-- **Per-run non-vacuity of `Link.DeadCleanup.compileExeOpt_correct_source_peak_nobnd`** on the recursive `i128` program `rec128`: the shipped
optimising compiler produces the executable `file` (the optimised `rec128` the mid-end's result);
the input is in the source domain and `rec128` mentions `i128`; the original program's CLIF run of
`rec128` on `2^64 + 3` and `3` (in `helperEnv`) returns `8 * 2^64 + 24` with call depth at most
`3`; and, the outside code calling the executable's compiled optimised `rec128` with the split
arguments in x0–x2 and `frameDrop + D * 3` bytes of stack, the executable machine returns to the
caller with the split result `24, 8` in x0, x1 — **without** the premise that the source run's
memories lie below `2^64`. -/
theorem cleanup_opt_source_peak_nobnd_witness :
    Link.DeadCleanup.compileExeOpt spec file0 = .ok file ∧ SrcScopeB I0 = true ∧
    I0.srcProg.func? n = some fsS ∧ (prog J).func? n = some f ∧ mentions128 fsS = true ∧
    Clif.DepthLe helperEnv I0.srcProg d cs ∧
    Clif.runLoop helperEnv I0.srcProg M cs = .returned [⟨.i128, 8#64 ++ 24#64⟩]
      (LinkWitness.retMem run) ∧
    ∃ k, ArmRet ra0 (r (memOf file)) (runX (step J helperBase file) k (r (memOf file))) ∧
      XHolds ⟨.i64, 24#64⟩ (xreg 0 (runX (step J helperBase file) k (r (memOf file)))) ∧
      XHolds ⟨.i64, 8#64⟩ (xreg 1 (runX (step J helperBase file) k (r (memOf file)))) := by
  have hfs := facts.1
  have hf := facts.2.2.1
  have hm := facts.2.2.2.2.1
  have hstack := facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hsrc := facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨p, hgp⟩ := Crates.CompileExeSourcePeakWitness.gp
  have hgp' : Opt.Legal.groups fsS.sig.params = some [[.lo, .hi], [.val p]] := hgp
  have hexp : Opt.Legal.ExpRel ((Opt.Legal.groups fsS.sig.params).getD []) args args' := by
    rw [hgp', Option.getD_some]
    exact ⟨⟨3#64, 1#64, rfl, rfl, rfl⟩, rfl, trivial⟩
  have hoc := outsideCall (memOf file) (BinCheck.roByte J spec.opt.data) hstack
  have h := (Link.DeadCleanup.compileExeOpt_correct_source_peak_nobnd compile_eq hsrc helperBase hBase (Link.DeadCleanup.SourceWitness.hooksSim_helper _) envKeepsSymbols_helper hlegal hsig
    hfs hf d (intact file) hoc (clifRun _) clifEntry hexp rfl rfl depth M).1 _ _ run_eq
  rw [x30_r] at h
  obtain ⟨vals', hrel, k, hret, hx, -⟩ := h
  have hgr : Opt.Legal.groups fsS.sig.returns = some [[.lo, .hi]] :=
    Crates.CompileExeSourcePeakWitness.gr
  rw [hgr, Option.getD_some] at hrel
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
    exact ⟨compile_eq, hsrc, hfs, hf, hm, depth, run_eq, k, hret, hx 0 _ rfl, hx 1 _ rfl⟩

end Crates.DeadCleanupExeOptSourcePeakNBWitness
