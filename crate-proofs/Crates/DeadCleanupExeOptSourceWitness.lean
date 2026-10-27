import Crates.CompileExeOptSourceWitness
import FV.Link.NonVacuityOptExeSource

/-! # Non-vacuity of the shipped optimising compiler's theorem on the original `i128` program
(S1, S2, S3)

`Link.DeadCleanup.compileExeOpt` — what `lake exe lean-link --opt` and
`cargo fv --lean-link --opt-proven-only` run — compiles the two functions of
`Crates.CompileExeOptSourceWitness` (`wmul_u128` and its callee
`core::num::<u128>::wrapping_mul` of the survey crate `g_u128`), placed at 16 MiB with the
cleanup pipeline's sizes of the optimised functions in the placeholder executable of
`Crates.LeanLinkWitness` (`compile_eq`). The mid-end changes both legalised functions
(`legalize fs ≠ f`). The input is in the source domain (`SrcScopeB`); the outside world is
`Link.SourceWitness.helperBase`.

Outside code calls the compiled optimised legalised `wmul_u128` with the ABI-split arguments
`3, 1, 5, 0` in x0–x3; the **original** program's CLIF run of `wmul_u128` on `2^64 + 3` and `5`
returns `5 * 2^64 + 15`; `Link.DeadCleanup.SourceWitness.compileExeOpt_correct_source_helper`
(`Link.DeadCleanup.compileExeOpt_correct_source` with the base premises discharged) gives the
executable machine's return to the caller with the split result `15, 5` in x0, x1
(`cleanup_opt_source_witness`).
-/

namespace Crates.DeadCleanupExeOptSourceWitness

open E2E E2E.LinkCheck E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes Backend Backend.Proof
  Opt.Legalize128
open Link (LinkSpec inScopePar_eq)
open Link.SourceWitness (helperEnv helperBase)
open Crates.BinaryWitness (memOf)
open Crates.CompileExeOptSourceWitness (input n args args' M sp0 ra0 sp0_toNat)

/-- The two functions placed at 16 MiB with the sizes the cleanup pipeline compiles their
optimised functions to, the other names at rust-lld's addresses. -/
def spec : LinkSpec :=
  let I := input
  let names := I.funcs.map (·.func.name)
  { funcs := I.funcs, names,
    sizes := I.funcs.map fun fi =>
      (getOk (pipeCleanupT fi.opt.func fi.opt.k 0 (raJ fi.opt.ra fi.opt.j))).fb.words.size,
    outside := I.addrs.filter (fun p => !names.contains p.1),
    symNames := I.syms.map (·.1), R := 0x1000000 }

/-- The executable before the compiler: the region's placeholder, the link map's symbols. -/
def file0 : ByteArray :=
  LeanLinkWitness.placeholder spec.R spec.size
    (spec.addrs.map fun p => (BinCheck.symName p.1, p.2))

theorem link_ok : (Link.DeadCleanup.leanLink spec.opt file0).toBool = true := by native_decide

/-- The executable. -/
def file : ByteArray := getOk (Link.DeadCleanup.leanLink spec.opt file0)

theorem link_eq : Link.DeadCleanup.leanLink spec.opt file0 = .ok file :=
  E2E.LinkCheck.getOk_eq link_ok

theorem inScope : InScopeP spec.opt.input0 = true := by native_decide

/-- **The shipped optimising executable compiler compiles the two functions to `file`.** -/
theorem compile_eq : Link.DeadCleanup.compileExeOpt spec file0 = .ok file := by
  show Link.DeadCleanup.compileExe spec.opt file0 = _
  simp only [Link.DeadCleanup.compileExe, inScopePar_eq, inScope, ↓reduceIte, link_eq]

/-- The cleanup input (the source program's side). -/
abbrev I0 : LinkInput := spec.inputCleanup

/-- The optimised cleanup input (the compiled side). -/
abbrev J : LinkInput := spec.opt.inputCleanup

/-- The **source** `wmul_u128` (as parsed, with `i128` parameters and result). -/
def fs : Clif.Function := (I0.srcProg.func? n).getD default

/-- The compiled function: its legalisation, optimised. -/
def f : Clif.Function := ((prog J).func? n).getD default

def bS : Clif.Block := fs.entry?.getD default
def bF : Clif.Block := f.entry?.getD default

/-- The body's stack pointer of the entry. -/
def sb : BitVec 64 := sp0 - BitVec.ofNat 64 (frameDrop (artOf J.resultsCleanup f).af)

/-- The caller's CLIF memory: no live allocation, the CLIF image's symbols, the slot-placement
oracle at the entry's body `sp`. -/
def cm : Clif.Mem :=
  { symbols := fun n => J.syms.lookup n, place := some ⟨[sb], (sys J helperBase).frames, none⟩ }

/-- The source entry state of `wmul_u128` on the two `i128` values. -/
def cs : Clif.State where
  frame := { func := fs, regs := (Clif.Regs.empty.setMany (bS.params.map (·.1)) args).getD default,
             slots := [], body := bS.body, term := bS.term }
  callers := []
  mem := cm

/-- The target entry state of the optimised legalised `wmul_u128` on the split arguments. -/
def cs' : Clif.State where
  frame := { func := f, regs := (Clif.Regs.empty.setMany (bF.params.map (·.1)) args').getD default,
             slots := [], body := bF.body, term := bF.term }
  callers := []
  mem := cm

/-- The original program's CLIF run from `cs`. -/
def run : Clif.Outcome := Clif.runLoop helperEnv I0.srcProg M cs

/-- The machine state of the call with memory `m`: pc at `f`'s address, x30 the caller's return
address, `sp0`, the split arguments in x0–x3. -/
def r (m : Arm.Memory) : Arm.ArmState :=
  Arm.w .PC (artOf J.resultsCleanup f).base (Arm.w (.GPR 30#5) ra0 (Arm.w (.GPR 31#5) sp0
    (Arm.w (.GPR 0#5) 3#64 (Arm.w (.GPR 1#5) 1#64 (Arm.w (.GPR 2#5) 5#64
      (Arm.w (.GPR 3#5) 0#64 (setMem Arm.ArmState.default m)))))))

def gpB : Bool :=
  match Opt.Legal.groups fs.sig.params with
  | some [[.lo, .hi], [.lo, .hi]] => true
  | _ => false

def grB : Bool :=
  match Opt.Legal.groups fs.sig.returns with
  | some [[.lo, .hi]] => true
  | _ => false

def locB : Bool :=
  match locsOf f.sig with
  | [.reg (.x 0), .reg (.x 1), .reg (.x 2), .reg (.x 3)] => true
  | _ => false

/-- The facts decided on the source and the compiled program (the compiled function is not the
legalisation: the mid-end changed it). -/
def factsB : Bool :=
  decide (I0.srcProg.func? n = some fs) && decide ((prog J).func? n = some f) &&
  decide (legalize fs ≠ f) && mentions128 fs &&
  decide (fs.entry? = some bS) && decide (f.entry? = some bF) &&
  decide (args.map (·.ty) = fs.sig.params.map (·.ty)) &&
  decide (bS.params.map (·.2) = args.map (·.ty)) &&
  (Clif.Regs.empty.setMany (bS.params.map (·.1)) args).isSome &&
  decide (args'.map (·.ty) = f.sig.params.map (·.ty)) &&
  decide (bF.params.map (·.2) = args'.map (·.ty)) &&
  (Clif.Regs.empty.setMany (bF.params.map (·.1)) args').isSome &&
  decide (fs.slots = []) && decide (f.slots = []) && locB &&
  gpB && grB &&
  LinkWitness.isRet run && decide (LinkWitness.retVals run = [⟨.i128, 5#64 ++ 15#64⟩]) &&
  (tabOf J.resultsCleanup).all
    (fun e => decide (e.2.base.toNat + 4 * e.2.fb.words.size + 4 ≤ 2 ^ 32)) &&
  DeadCleanupStackBound.goodN J n &&
  decide (DeadCleanupStackBound.stackFn J f ≤ 2 ^ 20) &&
  (prog J).funcs.all (fun g => !Backend.hasTls g) &&
  (prog J).funcs.all (fun g => g.externs.all fun e =>
    ((prog J).func? e.2.name).isSome || !Clif.Rust.isDivHelper e.2.name) &&
  (prog J).funcs.all indFreeB && (prog J).funcs.all (fun g => (indSigs g).isEmpty) &&
  I0.srcProg.funcs.all (fun g => g.slots.isEmpty) && SrcScopeB I0

theorem factsB_true : factsB = true := by native_decide

theorem facts :
    I0.srcProg.func? n = some fs ∧ (prog J).func? n = some f ∧ legalize fs ≠ f ∧
    mentions128 fs = true ∧ fs.entry? = some bS ∧ f.entry? = some bF ∧
    args.map (·.ty) = fs.sig.params.map (·.ty) ∧ bS.params.map (·.2) = args.map (·.ty) ∧
    (Clif.Regs.empty.setMany (bS.params.map (·.1)) args).isSome = true ∧
    args'.map (·.ty) = f.sig.params.map (·.ty) ∧ bF.params.map (·.2) = args'.map (·.ty) ∧
    (Clif.Regs.empty.setMany (bF.params.map (·.1)) args').isSome = true ∧
    fs.slots = [] ∧ f.slots = [] ∧ locB = true ∧
    gpB = true ∧ grB = true ∧
    LinkWitness.isRet run = true ∧ LinkWitness.retVals run = [⟨.i128, 5#64 ++ 15#64⟩] ∧
    (tabOf J.resultsCleanup).all
      (fun e => decide (e.2.base.toNat + 4 * e.2.fb.words.size + 4 ≤ 2 ^ 32)) = true ∧
    DeadCleanupStackBound.goodN J n = true ∧
    DeadCleanupStackBound.stackFn J f ≤ 2 ^ 20 ∧
    (prog J).funcs.all (fun g => !Backend.hasTls g) = true ∧
    (prog J).funcs.all (fun g => g.externs.all fun e =>
      ((prog J).func? e.2.name).isSome || !Clif.Rust.isDivHelper e.2.name) = true ∧
    (prog J).funcs.all indFreeB = true ∧ (prog J).funcs.all (fun g => (indSigs g).isEmpty) = true ∧
    I0.srcProg.funcs.all (fun g => g.slots.isEmpty) = true ∧ SrcScopeB I0 = true := by
  have h := factsB_true
  simp only [factsB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩,
    h13⟩, h14⟩, h15⟩, h16⟩, h17⟩, h18⟩, h19⟩, h20⟩, h21⟩, h22⟩, h23⟩, h24⟩, h25⟩, h26⟩, h27⟩,
    h28⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    h21, h22, h23, h24, h25, h26, h27, h28⟩

/-- The input's (unoptimised) program has no indirect call. -/
theorem indFree0 : (prog I0).funcs.all indFreeB = true := by native_decide

/-- `okBCleanup` of the cleanup input (by construction, `Link.DeadCleanup.okB_leanLink`). -/
theorem okB_J : okBCleanup J = true :=
  Link.DeadCleanup.okB_leanLink (by rw [Link.DeadCleanup.inScope_input]; exact inScope) link_eq

/-- No call cycle of the program's call graph is reachable from the entry. -/
theorem acyclic : ¬ DeadCleanupStackBound.CycleFrom
    (DeadCleanupStackBound.Calls J J.resultsCleanup) f := by
  obtain ⟨f', hf', hc⟩ := (DeadCleanupStackBound.goodN_iff okB_J).1
    facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [facts.2.1] at hf'
  cases hf'
  exact hc

/-- Every code address of the program is below `2^32`. -/
theorem img_lt {x : BitVec 64} (h : img J x) : x.toNat < 2 ^ 32 := by
  obtain ⟨e, he, p, hp, hx⟩ := h
  have hb' : e.2.base.toNat + 4 * e.2.fb.words.size + 4 ≤ 2 ^ 32 := by
    have := List.all_eq_true.mp facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e he
    simpa using this
  obtain ⟨j, hj, e'⟩ := LinkWitness.wordsAt_mem_inv (k := 0) hp
  simp only [Array.length_toList] at hj
  rw [e', BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat] at hx
  have := e.2.base.isLt
  have := x.isLt
  rw [Nat.mod_eq_of_lt (by omega : 4 * (0 + j) < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : e.2.base.toNat + 4 * (0 + j) < 2 ^ 64)] at hx
  omega

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
    Arm.r_of_w_different (by decide), Arm.r_of_w_different (by decide),
    Arm.r_of_w_different (by decide), r_setMem]
  simp [Arm.r, Arm.read_base_error, Arm.ArmState.default]

theorem x0_r : Arm.r (.GPR (rnum 0)) (r m) = 3#64 := by
  simp only [r, rnum]
  rw [Arm.r_of_w_different (by decide), Arm.r_of_w_different (by decide),
    Arm.r_of_w_different (by decide), Arm.r_of_w_same]

theorem x1_r : Arm.r (.GPR (rnum 1)) (r m) = 1#64 := by
  simp only [r, rnum]
  rw [Arm.r_of_w_different (by decide), Arm.r_of_w_different (by decide),
    Arm.r_of_w_different (by decide), Arm.r_of_w_different (by decide), Arm.r_of_w_same]

theorem x2_r : Arm.r (.GPR (rnum 2)) (r m) = 5#64 := by
  simp only [r, rnum]
  rw [Arm.r_of_w_different (by decide), Arm.r_of_w_different (by decide),
    Arm.r_of_w_different (by decide), Arm.r_of_w_different (by decide),
    Arm.r_of_w_different (by decide), Arm.r_of_w_same]

theorem x3_r : Arm.r (.GPR (rnum 3)) (r m) = 0#64 := by
  simp only [r, rnum]
  rw [Arm.r_of_w_different (by decide), Arm.r_of_w_different (by decide),
    Arm.r_of_w_different (by decide), Arm.r_of_w_different (by decide),
    Arm.r_of_w_different (by decide), Arm.r_of_w_different (by decide), Arm.r_of_w_same]

omit m in
theorem locs : locsOf f.sig = [.reg (.x 0), .reg (.x 1), .reg (.x 2), .reg (.x 3)] := by
  have h := facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold locB at h
  split at h
  · assumption
  · cases h

omit m in
theorem gp : Opt.Legal.groups fs.sig.params = some [[.lo, .hi], [.lo, .hi]] := by
  have h := facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold gpB at h
  split at h
  · assumption
  · cases h

omit m in
theorem gr : Opt.Legal.groups fs.sig.returns = some [[.lo, .hi]] := by
  have h := facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold grB at h
  split at h
  · assumption
  · cases h

/-- The outside caller's contract for the optimised legalised `wmul_u128` in `r m` (the split
arguments in x0–x3) with a stack of `N ≤ 2^20` bytes. -/
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
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp only [VHolds, regVal, x0_r m]; rfl
    · simp only [VHolds, regVal, x1_r m]; rfl
    · simp only [VHolds, regVal, x2_r m]; rfl
    · simp only [VHolds, regVal, x3_r m]; rfl
  bytes := fun _ _ hv => by simp [cs', cm, Clif.Mem.valid] at hv
  image := fun _ _ _ hv => by simp [cs', cm, Clif.Mem.valid] at hv
  valid := fun _ _ hv => by simp [cs', cm, Clif.Mem.valid] at hv
  symbols := rfl

omit m in
theorem clifEntry' : ClifEntry f args' cs' := by
  obtain ⟨-, -, -, -, -, hb, -, -, -, hsig, hpar, hset, -, hsl, -⟩ := facts
  refine ⟨rfl, rfl, hsig, ⟨bF, hb, rfl, rfl, hpar, ?_⟩, by simp [cs', hsl]⟩
  show _ = some ((Clif.Regs.empty.setMany (bF.params.map (·.1)) args').getD default)
  revert hset
  cases Clif.Regs.empty.setMany (bF.params.map (·.1)) args' <;> simp

omit m in
theorem clifEntry : ClifEntry fs args cs := by
  obtain ⟨-, -, -, -, hb, -, hsig, hpar, hset, -, -, -, hsl, -⟩ := facts
  refine ⟨rfl, rfl, hsig, ⟨bS, hb, rfl, rfl, hpar, ?_⟩, by simp [cs, hsl]⟩
  show _ = some ((Clif.Regs.empty.setMany (bS.params.map (·.1)) args).getD default)
  revert hset
  cases Clif.Regs.empty.setMany (bS.params.map (·.1)) args <;> simp

/-- The target entry for `compileExeOpt_correct_source`. -/
theorem clifRun : ClifRun J helperBase f (r m) args' cs' where
  entry := clifEntry'
  slots := fun _ _ h => by simp [cs'] at h
  place := fun _ => ⟨[], by
    show some _ = some _
    rw [show spBody (art J f).af (r m) = sb by
      simp only [spBody, spv_r, sb]]⟩

end State

/-- The machine's memory is the loaded image of any file. -/
theorem intact (file : ByteArray) : (imageOf file).Intact (r (memOf file)) := fun a b _ hb => by
  simp only [r, LinkWitness.mem_w, mem_setMem, memOf]
  exact (congrArg (Option.getD · 0) hb).trans rfl

/-- The original program's CLIF run of `wmul_u128` returns `5 * 2^64 + 15`. -/
theorem run_eq : run = .returned [⟨.i128, 5#64 ++ 15#64⟩] (LinkWitness.retMem run) := by
  rw [← facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
  exact LinkWitness.eq_returned facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem cm_bounded : Opt.Legal.MemBounded cs.mem := fun _ _ h => by
  simp [cs, cm, Clif.Mem.valid] at h

/-- **Per-run non-vacuity of `Link.DeadCleanup.compileExeOpt_correct_source`** on the original
`i128` program `{wmul_u128, wrapping_mul}` of `g_u128`: the shipped optimising compiler
produces the executable `file`, with the compiled `wmul_u128` the mid-end's result
(`f ≠ legalize fs`); the input is in the source domain (`SrcScopeB`) and its source function
`wmul_u128` mentions `i128`; the original program's CLIF run of `wmul_u128` on `2^64 + 3` and `5`
returns `5 * 2^64 + 15`; and, the outside code calling the executable's compiled `wmul_u128` with
the split arguments in x0–x3, the executable machine returns to the caller with the split result
`15, 5` in x0, x1. -/
theorem cleanup_opt_source_witness :
    Link.DeadCleanup.compileExeOpt spec file0 = .ok file ∧ SrcScopeB I0 = true ∧
    I0.srcProg.func? n = some fs ∧ (prog J).func? n = some f ∧ legalize fs ≠ f ∧
    mentions128 fs = true ∧
    Clif.runLoop helperEnv I0.srcProg M cs = .returned [⟨.i128, 5#64 ++ 15#64⟩]
      (LinkWitness.retMem run) ∧
    ∃ k, ArmRet ra0 (r (memOf file)) (runX (step J helperBase file) k (r (memOf file))) ∧
      XHolds ⟨.i64, 15#64⟩ (xreg 0 (runX (step J helperBase file) k (r (memOf file)))) ∧
      XHolds ⟨.i64, 5#64⟩ (xreg 1 (runX (step J helperBase file) k (r (memOf file)))) := by
  obtain ⟨hf, hf', hne, hm, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hst, htls, hdivB,
    hindB, hsigsB, hslotsB, hsrc⟩ := facts
  have hexp : Opt.Legal.ExpRel ((Opt.Legal.groups fs.sig.params).getD []) args args' := by
    rw [gp, Option.getD_some]
    exact ⟨⟨3#64, 1#64, rfl, rfl, rfl⟩, ⟨5#64, 0#64, rfl, rfl, rfl⟩, trivial⟩
  have hdiv : ∀ g ∈ (prog J).funcs, ∀ e ∈ g.externs, (prog J).func? e.2.name = none →
      Clif.Rust.isDivHelper e.2.name = false := by
    intro g hg e he hn
    have := List.all_eq_true.mp (List.all_eq_true.mp hdivB g hg) e he
    simpa [hn] using this
  have hoc := outsideCall (memOf file) (BinCheck.roByte J spec.opt.data) hst
  have h := Link.DeadCleanup.SourceWitness.compileExeOpt_correct_source_helper compile_eq hsrc
    (fun g hg => by simpa using List.all_eq_true.mp htls g hg) hdiv
    (fun g hg => indFreeB_sound (List.all_eq_true.mp hindB g hg))
    (fun g hg => by simpa using List.all_eq_true.mp hsigsB g hg)
    (fun g hg => indFreeB_sound (List.all_eq_true.mp indFree0 g hg))
    (fun g hg => by simpa using List.all_eq_true.mp hslotsB g hg)
    hf hf' acyclic (intact file) hoc (clifRun _) clifEntry hexp rfl rfl cm_bounded M _ _ run_eq
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
