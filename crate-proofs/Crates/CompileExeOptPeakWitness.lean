import Crates.CompileExeSourcePeakWitness
import FV.Link.OptExe

/-! # Per-run non-vacuity of the optimising executable compiler's peak-call-depth theorem (S1, S2)

`Link.compileExeOpt` compiles the self-recursive `i128` function `rec128` of
`Crates.CompileExeSourcePeakWitness` (`rec128(x, n) = n = 0 ? x : rec128(x + x, n - 1)`), placed
at 16 MiB with the compiled size of its optimised function in the placeholder executable of
`Crates.LeanLinkWitness` (`compile_eq`). The mid-end (`Opt.optimizeExe`) changes the legalised
`rec128` (`f0 ≠ f`), which prints and parses back (`spec.optFallbacks = []`). The optimised entry
reaches a call cycle (`cyclic`), so `Link.compileExeOpt_correct` does not apply. The outside world
is the closed base environment `closedBase`.

Outside code calls the compiled optimised `rec128` with the split arguments `3, 1, 3` in x0–x2
(`x = 2^64 + 3`, `n = 3`) and `frameDrop + D * 3` bytes of stack. The **unoptimised** legalised
program's CLIF run of `rec128` on the same arguments returns `24, 8` (`8 * x`) after four
activations, with call depth `3` (`depth`). Every premise of `Link.compileExeOpt_correct_peak`
holds, and it gives the executable machine's return to the caller with `24, 8` in x0, x1
(`compileExeOpt_peak_witness`).
-/

namespace Crates.CompileExeOptPeakWitness

open E2E E2E.LinkCheck E2E.Binary E2E.ExecBytes Backend Backend.Proof Link
open Crates.BinaryWitness (memOf)
open Crates.CompileExeSourcePeakWitness (fnInput n args' d sp0 ra0 sp0_toNat)

/-- `rec128` placed at 16 MiB with the compiled size of its optimised function. -/
def spec : LinkSpec :=
  let fs := [fnInput]
  let names := fs.map (·.func.name)
  { funcs := fs, names,
    sizes := fs.map fun fi =>
      (getOk (pipeT fi.opt.func fi.opt.k 0 (raJ fi.opt.ra fi.opt.j))).fb.words.size,
    outside := [], symNames := names, R := 0x1000000 }

/-- The executable before the compiler: the region's placeholder, the link map's symbols. -/
def file0 : ByteArray :=
  LeanLinkWitness.placeholder spec.R spec.size
    (spec.addrs.map fun p => (BinCheck.symName p.1, p.2))

theorem link_ok : (leanLink spec.opt file0).toBool = true := by native_decide

/-- The executable. -/
def file : ByteArray := getOk (leanLink spec.opt file0)

theorem link_eq : leanLink spec.opt file0 = .ok file := E2E.LinkCheck.getOk_eq link_ok

theorem inScope : InScopeP spec.opt.input = true := by native_decide

/-- **The optimising executable compiler compiles `rec128` to `file`.** -/
theorem compile_eq : compileExeOpt spec file0 = .ok file := by
  show compileExe spec.opt file0 = _
  have h : InScopeP spec.opt.input0 = true := by rw [← LinkSpec.inScope_input]; exact inScope
  simp only [compileExe, inScopePar_eq, h, ↓reduceIte, link_eq]

/-- The input (the unoptimised side). -/
abbrev I0 : LinkInput := spec.input

/-- The optimised input (the compiled side). -/
abbrev J : LinkInput := spec.opt.input

/-- The legalised `rec128`. -/
def f0 : Clif.Function := ((prog I0).func? n).getD default

/-- The compiled function: the legalised `rec128`, optimised. -/
def f : Clif.Function := ((prog J).func? n).getD default

def b0 : Clif.Block := f0.entry?.getD default
def bF : Clif.Block := f.entry?.getD default

/-- The run's fuel (the legalised run returns within it). -/
def M : Nat := 64

/-- The body's stack pointer of the entry. -/
def sb : BitVec 64 := sp0 - BitVec.ofNat 64 (frameDrop (artOf J.results f).af)

/-- The caller's CLIF memory: no live allocation, the CLIF image's symbols, the slot-placement
oracle at the entry's body `sp`. -/
def cm : Clif.Mem :=
  { symbols := fun n => J.syms.lookup n, place := some ⟨[sb], (sys J closedBase).frames⟩ }

/-- The entry registers: the entry block's parameters bound to the split arguments. -/
def regs : Clif.Regs := (Clif.Regs.empty.setMany (bF.params.map (·.1)) args').getD default

/-- The entry state of the unoptimised legalised `rec128`. -/
def cs : Clif.State where
  frame := { func := f0, regs, slots := [], body := b0.body, term := b0.term }
  callers := []
  mem := cm

/-- The entry state of the optimised `rec128`. -/
def cs' : Clif.State where
  frame := { func := f, regs, slots := [], body := bF.body, term := bF.term }
  callers := []
  mem := cm

/-- The unoptimised program's CLIF run from `cs`. -/
def run : Clif.Outcome := Clif.runLoop closedBase.env (prog I0) M cs

/-- The machine state of the call with memory `m`: pc at `f`'s address, x30 the caller's return
address, `sp0`, the split arguments in x0–x2. -/
def r (m : Arm.Memory) : Arm.ArmState :=
  Arm.w .PC (artOf J.results f).base (Arm.w (.GPR 30#5) ra0 (Arm.w (.GPR 31#5) sp0
    (Arm.w (.GPR 0#5) 3#64 (Arm.w (.GPR 1#5) 1#64 (Arm.w (.GPR 2#5) 3#64
      (setMem Arm.ArmState.default m))))))

def locB : Bool :=
  match locsOf f.sig with
  | [.reg (.x 0), .reg (.x 1), .reg (.x 2)] => true
  | _ => false

/-- The facts decided on the unoptimised and the optimised program. -/
def factsB : Bool :=
  decide ((prog I0).func? n = some f0) && decide ((prog J).func? n = some f) && decide (f0 ≠ f) &&
  decide (f0.entry? = some b0) && decide (f.entry? = some bF) && decide (b0.params = bF.params) &&
  decide (args'.map (·.ty) = f0.sig.params.map (·.ty)) &&
  decide (args'.map (·.ty) = f.sig.params.map (·.ty)) &&
  decide (bF.params.map (·.2) = args'.map (·.ty)) &&
  (Clif.Regs.empty.setMany (bF.params.map (·.1)) args').isSome &&
  decide (f0.slots = []) && decide (f.slots = []) && locB &&
  LinkWitness.isRet run && decide (LinkWitness.retVals run = [⟨.i64, 24#64⟩, ⟨.i64, 8#64⟩]) &&
  Clif.depthB closedBase.env (prog I0) d M cs &&
  (tabOf J.results).all (fun e => decide (e.2.base.toNat + 4 * e.2.fb.words.size + 4 ≤ 2 ^ 32)) &&
  !StackBound.goodN J n && decide (frameDrop (artOf J.results f).af + J.D * d ≤ 2 ^ 20) &&
  (prog J).funcs.all (fun g => !Backend.hasTls g)

theorem factsB_true : factsB = true := by native_decide

theorem facts :
    (prog I0).func? n = some f0 ∧ (prog J).func? n = some f ∧ f0 ≠ f ∧
    f0.entry? = some b0 ∧ f.entry? = some bF ∧ b0.params = bF.params ∧
    args'.map (·.ty) = f0.sig.params.map (·.ty) ∧ args'.map (·.ty) = f.sig.params.map (·.ty) ∧
    bF.params.map (·.2) = args'.map (·.ty) ∧
    (Clif.Regs.empty.setMany (bF.params.map (·.1)) args').isSome = true ∧
    f0.slots = [] ∧ f.slots = [] ∧ locB = true ∧
    LinkWitness.isRet run = true ∧
    LinkWitness.retVals run = [⟨.i64, 24#64⟩, ⟨.i64, 8#64⟩] ∧
    Clif.depthB closedBase.env (prog I0) d M cs = true ∧
    (tabOf J.results).all (fun e => decide (e.2.base.toNat + 4 * e.2.fb.words.size + 4 ≤ 2 ^ 32))
      = true ∧
    StackBound.goodN J n = false ∧ frameDrop (artOf J.results f).af + J.D * d ≤ 2 ^ 20 ∧
    (prog J).funcs.all (fun g => !Backend.hasTls g) = true := by
  have h := factsB_true
  simp only [factsB, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩,
    h14⟩, h15⟩, h16⟩, h17⟩, h18⟩, h19⟩, h20⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩

/-- The optimised function prints and parses back: the compiled input is the optimised one. -/
theorem noFallbacks : spec.optFallbacks = [] := by native_decide

/-- `okB` of the placed optimised input (by construction, `okB_leanLink`). -/
theorem okB_J : okB J = true := okB_leanLink inScope link_eq

/-- **The optimised entry reaches a call cycle**: `compileExeOpt_correct`'s premise
`¬ CycleFrom` fails. -/
theorem cyclic : StackBound.CycleFrom (StackBound.Calls J J.results) f := by
  refine Classical.byContradiction fun hc => ?_
  have h := (StackBound.goodN_iff okB_J).2 ⟨f, facts.2.1, hc⟩
  rw [facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1] at h
  cases h

/-- Every code address of the program is below `2^32`. -/
theorem img_lt {x : BitVec 64} (h : img J x) : x.toNat < 2 ^ 32 := by
  obtain ⟨e, he, p, hp, hx⟩ := h
  have hb' : e.2.base.toNat + 4 * e.2.fb.words.size + 4 ≤ 2 ^ 32 := by
    have := List.all_eq_true.mp facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e he
    simpa using this
  obtain ⟨j, hj, e'⟩ := LinkWitness.wordsAt_mem_inv (k := 0) hp
  simp only [Array.length_toList] at hj
  rw [e', BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat] at hx
  have := e.2.base.isLt
  have := x.isLt
  rw [Nat.mod_eq_of_lt (by omega : 4 * (0 + j) < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : e.2.base.toNat + 4 * (0 + j) < 2 ^ 64)] at hx
  omega

/-- The closed base environment's premises. -/
theorem base_closed (F : BitVec 64 → Prop) : BaseOk (LinkSys.ofInput J closedBase F) :=
  baseOk_closed fun g hg => by
    simpa using List.all_eq_true.1 facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 g hg

/-- The closed base environment has no outside function: it keeps the link-time symbols. -/
theorem keepsSymbols : Opt.EnvKeepsSymbols closedBase.env := fun _ _ he => by
  simp [closedBase, Clif.Env.empty] at he

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

omit m in
theorem locs : locsOf f.sig = [.reg (.x 0), .reg (.x 1), .reg (.x 2)] := by
  have h := facts.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold locB at h
  split at h
  · assumption
  · cases h

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
theorem setMany_eq : Clif.Regs.empty.setMany (bF.params.map (·.1)) args' = some regs := by
  have hset := facts.2.2.2.2.2.2.2.2.2.1
  show _ = some ((Clif.Regs.empty.setMany (bF.params.map (·.1)) args').getD default)
  revert hset
  cases Clif.Regs.empty.setMany (bF.params.map (·.1)) args' <;> simp

omit m in
theorem clifEntry' : ClifEntry f args' cs' := by
  obtain ⟨-, -, -, -, hb, -, -, hsig, hpar, -, -, hsl, -⟩ := facts
  exact ⟨rfl, rfl, hsig, ⟨bF, hb, rfl, rfl, hpar, setMany_eq⟩, by simp [cs', hsl]⟩

omit m in
theorem clifEntry : ClifEntry f0 args' cs := by
  obtain ⟨-, -, -, hb, -, hp, hsig, -, hpar, -, hsl, -⟩ := facts
  exact ⟨rfl, rfl, hsig, ⟨b0, hb, rfl, rfl, by rw [hp]; exact hpar, by rw [hp]; exact setMany_eq⟩,
    by simp [cs, hsl]⟩

/-- The target entry for `compileExeOpt_correct_peak`. -/
theorem clifRun : ClifRun J closedBase f (r m) args' cs' where
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

/-- The unoptimised program's CLIF run of `rec128` returns `24, 8`. -/
theorem run_eq : run = .returned [⟨.i64, 24#64⟩, ⟨.i64, 8#64⟩] (LinkWitness.retMem run) := by
  rw [← facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
  exact LinkWitness.eq_returned facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- The unoptimised run's call depth is at most `d = 3`. -/
theorem depth : Clif.DepthLe closedBase.env (prog I0) d cs :=
  Clif.depthLe_of_depthB M cs facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- **Per-run non-vacuity of `Link.compileExeOpt_correct_peak`** on the recursive `rec128`:
`compileExeOpt` produces the executable `file`, with the compiled `rec128` the mid-end's result
(`f0 ≠ f`) and no print/parse fallback; the optimised entry reaches a call cycle (so
`compileExeOpt_correct` does not apply); the unoptimised program's CLIF run of `rec128` on the
split arguments of `2^64 + 3`, `3` returns `24, 8` with call depth at most `3`; and, the outside
code calling the executable's compiled `rec128` with them in x0–x2 and `frameDrop + D * 3` bytes
of stack, the executable machine returns to the caller with `24, 8` in x0, x1. -/
theorem compileExeOpt_peak_witness :
    compileExeOpt spec file0 = .ok file ∧ spec.optFallbacks = [] ∧
    (prog I0).func? n = some f0 ∧ (prog J).func? n = some f ∧ f0 ≠ f ∧
    StackBound.CycleFrom (StackBound.Calls J J.results) f ∧
    Clif.DepthLe closedBase.env (prog I0) d cs ∧
    OutsideCall J (BinCheck.roByte J spec.opt.data) f (frameDrop (art J f).af + J.D * d)
      (r (memOf file)) args' cs'.mem ∧
    Clif.runLoop closedBase.env (prog I0) M cs =
      .returned [⟨.i64, 24#64⟩, ⟨.i64, 8#64⟩] (LinkWitness.retMem run) ∧
    ∃ k, ArmRet ra0 (r (memOf file)) (runX (step J closedBase file) k (r (memOf file))) ∧
      XHolds ⟨.i64, 24#64⟩ (xreg 0 (runX (step J closedBase file) k (r (memOf file)))) ∧
      XHolds ⟨.i64, 8#64⟩ (xreg 1 (runX (step J closedBase file) k (r (memOf file)))) := by
  obtain ⟨hf0, hf, hne, -⟩ := facts
  have hoc := outsideCall (memOf file) (BinCheck.roByte J spec.opt.data)
    facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h := (compileExeOpt_correct_peak compile_eq closedBase (base_closed _) (hooksSim_closed J)
    keepsSymbols hf0 hf d (intact file) hoc (clifRun _) clifEntry rfl rfl rfl depth M).1 _ _ run_eq
  rw [x30_r] at h
  obtain ⟨k, hret, hx, -⟩ := h
  exact ⟨compile_eq, noFallbacks, hf0, hf, hne, cyclic, depth, hoc, run_eq, k, hret, hx 0 _ rfl,
    hx 1 _ rfl⟩

end Crates.CompileExeOptPeakWitness
