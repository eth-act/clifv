import Crates.CompileExeSourcePeakWitness
import FV.Link.TailExe

/-! # Per-run non-vacuity of the tail-loop compiler's peak-call-depth theorem (S8, #32)

`Link.DeadCleanup.compileExeTail` compiles the self-tail-recursive `sum(n, acc)` (`n = 0 ? acc :
return_call sum(n - 1, acc + n)`, its own declaration `fn0 = colocated %sum`), placed at 16 MiB
with the cleanup pipeline's size of its transformed function in the placeholder executable of
`Crates.LeanLinkWitness` (`compile_eq`). The transform turns the self `return_call` into a loop
(`spec.tailLoops = [sum]`, `f0 ≠ f`); the compiled function has no call at all. The outside world
is `closedBase` (no extern: it keeps the slot-placement oracle).

The input program's CLIF run of `sum(10, 0)` makes ten self tail calls and returns `55` with call
depth `0` (`depth`: a `return_call` replaces the frame, no state of the run has a caller). Outside
code calls the compiled `sum` with `10, 0` in x0, x1 and `frameDrop + D * 0` bytes of stack — one
frame, whatever the number of tail calls; `Link.DeadCleanup.compileExeTail_correct_peak` gives the
executable machine's return to the caller with `55` in x0 (`cleanup_tail_peak_witness`).
-/

namespace Crates.DeadCleanupExeTailPeakWitness

open E2E E2E.LinkCheck E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes Backend Backend.Proof
open Link (LinkSpec inScopePar_eq)
open Crates.BinaryWitness (memOf)
open Crates.CompileExeSourcePeakWitness (sp0 ra0 sp0_toNat)

/-- The self-tail-recursive function. -/
def src : String := "function %sum(i64, i64) -> i64 system_v {
    fn0 = colocated %sum(i64, i64) -> i64 system_v
block0(v0: i64, v1: i64):
    brif v0, block1, block2
block1:
    v2 = iconst.i64 1
    v3 = isub v0, v2
    v4 = iadd v1, v0
    return_call fn0(v3, v4)
block2:
    return v1
}
"

/-- `sum` as an input of the executable compiler (the spill-fallback allocation). -/
def fnInput : FnInput := { clif := src, ra := "{}" }

def n : String := "sum"

/-- The arguments `10, 0`. -/
def args' : List Clif.Val := [⟨.i64, 10#64⟩, ⟨.i64, 0#64⟩]

/-- The call depth of the input program's run. -/
def d : Nat := 0

/-- `sum` placed at 16 MiB with the cleanup pipeline's size of its transformed function. -/
def spec : LinkSpec :=
  let fs := [fnInput]
  let names := fs.map (·.func.name)
  { funcs := fs, names,
    sizes := fs.map fun fi =>
      (getOk (pipeCleanupT fi.tail.func fi.tail.k 0 (raJ fi.tail.ra fi.tail.j))).fb.words.size,
    outside := [], symNames := names, R := 0x1000000 }

/-- The executable before the compiler: the region's placeholder, the link map's symbols. -/
def file0 : ByteArray :=
  LeanLinkWitness.placeholder spec.R spec.size
    (spec.addrs.map fun p => (BinCheck.symName p.1, p.2))

theorem link_ok : (Link.DeadCleanup.leanLink spec.tail file0).toBool = true := by native_decide

/-- The executable. -/
def file : ByteArray := getOk (Link.DeadCleanup.leanLink spec.tail file0)

theorem link_eq : Link.DeadCleanup.leanLink spec.tail file0 = .ok file :=
  E2E.LinkCheck.getOk_eq link_ok

theorem inScope : InScopeP spec.tail.input0 = true := by native_decide

/-- **The tail-loop executable compiler compiles `sum` to `file`.** -/
theorem compile_eq : Link.DeadCleanup.compileExeTail spec file0 = .ok file := by
  show Link.DeadCleanup.compileExe spec.tail file0 = _
  simp only [Link.DeadCleanup.compileExe, inScopePar_eq, inScope, ↓reduceIte, link_eq]

/-- The input (with the self `return_call`). -/
abbrev I0 : LinkInput := spec.inputCleanup

/-- The transformed input (the compiled side). -/
abbrev J : LinkInput := spec.tail.inputCleanup

/-- The input's `sum`. -/
def f0 : Clif.Function := ((prog I0).func? n).getD default

/-- The compiled function: `sum` with its self tail call as a loop. -/
def f : Clif.Function := ((prog J).func? n).getD default

def b0 : Clif.Block := f0.entry?.getD default
def bF : Clif.Block := f.entry?.getD default

/-- The run's fuel (the input program's run returns within it). -/
def M : Nat := 128

/-- The body's stack pointer of the entry. -/
def sb : BitVec 64 := sp0 - BitVec.ofNat 64 (frameDrop (artOf J.resultsCleanup f).af)

/-- The caller's CLIF memory: no live allocation, the CLIF image's symbols, the slot-placement
oracle at the entry's body `sp` above the caller's `sp`. -/
def cm : Clif.Mem :=
  { symbols := fun n => J.syms.lookup n, place := some ⟨[sb, sp0], (sys J closedBase).frames⟩ }

/-- The entry registers of the input's `sum`. -/
def regs0 : Clif.Regs := (Clif.Regs.empty.setMany (b0.params.map (·.1)) args').getD default

/-- The entry registers of the transformed `sum` (its new entry block's parameters). -/
def regsF : Clif.Regs := (Clif.Regs.empty.setMany (bF.params.map (·.1)) args').getD default

/-- The entry state of the input's `sum`. -/
def cs : Clif.State where
  frame := { func := f0, regs := regs0, slots := [], body := b0.body, term := b0.term }
  callers := []
  mem := cm

/-- The entry state of the transformed `sum`. -/
def cs' : Clif.State where
  frame := { func := f, regs := regsF, slots := [], body := bF.body, term := bF.term }
  callers := []
  mem := cm

/-- The input program's CLIF run from `cs`. -/
def run : Clif.Outcome := Clif.runLoop closedBase.env (prog I0) M cs

/-- The machine state of the call with memory `m`: pc at `f`'s address, x30 the caller's return
address, `sp0`, the arguments in x0, x1. -/
def r (m : Arm.Memory) : Arm.ArmState :=
  Arm.w .PC (artOf J.resultsCleanup f).base (Arm.w (.GPR 30#5) ra0 (Arm.w (.GPR 31#5) sp0
    (Arm.w (.GPR 0#5) 10#64 (Arm.w (.GPR 1#5) 0#64 (setMem Arm.ArmState.default m)))))

def locB : Bool :=
  match locsOf f.sig with
  | [.reg (.x 0), .reg (.x 1)] => true
  | _ => false

/-- The facts decided on the input and the transformed program. -/
def factsB : Bool :=
  decide ((prog I0).func? n = some f0) && decide ((prog J).func? n = some f) && decide (f0 ≠ f) &&
  decide (f0.entry? = some b0) && decide (f.entry? = some bF) &&
  decide (args'.map (·.ty) = f0.sig.params.map (·.ty)) &&
  decide (args'.map (·.ty) = f.sig.params.map (·.ty)) &&
  decide (b0.params.map (·.2) = args'.map (·.ty)) &&
  decide (bF.params.map (·.2) = args'.map (·.ty)) &&
  (Clif.Regs.empty.setMany (b0.params.map (·.1)) args').isSome &&
  (Clif.Regs.empty.setMany (bF.params.map (·.1)) args').isSome &&
  decide (f0.slots = []) && decide (f.slots = []) && locB &&
  LinkWitness.isRet run && decide (LinkWitness.retVals run = [⟨.i64, 55#64⟩]) &&
  Clif.depthB closedBase.env (prog I0) d M cs &&
  (tabOf J.resultsCleanup).all
    (fun e => decide (e.2.base.toNat + 4 * e.2.fb.words.size + 4 ≤ 2 ^ 32)) &&
  decide (frameDrop (artOf J.resultsCleanup f).af + J.D * d ≤ 2 ^ 20) &&
  (prog J).funcs.all (fun g => !Backend.hasTls g) &&
  decide (sb = Opt.TailLoop.spOf (sys J closedBase).frames f0.name [sp0]) &&
  decide (spec.tailLoops = [n])

theorem factsB_true : factsB = true := by native_decide

theorem facts :
    (prog I0).func? n = some f0 ∧ (prog J).func? n = some f ∧ f0 ≠ f ∧
    f0.entry? = some b0 ∧ f.entry? = some bF ∧
    args'.map (·.ty) = f0.sig.params.map (·.ty) ∧ args'.map (·.ty) = f.sig.params.map (·.ty) ∧
    b0.params.map (·.2) = args'.map (·.ty) ∧ bF.params.map (·.2) = args'.map (·.ty) ∧
    (Clif.Regs.empty.setMany (b0.params.map (·.1)) args').isSome = true ∧
    (Clif.Regs.empty.setMany (bF.params.map (·.1)) args').isSome = true ∧
    f0.slots = [] ∧ f.slots = [] ∧ locB = true ∧
    LinkWitness.isRet run = true ∧
    LinkWitness.retVals run = [⟨.i64, 55#64⟩] ∧
    Clif.depthB closedBase.env (prog I0) d M cs = true ∧
    (tabOf J.resultsCleanup).all
      (fun e => decide (e.2.base.toNat + 4 * e.2.fb.words.size + 4 ≤ 2 ^ 32)) = true ∧
    frameDrop (artOf J.resultsCleanup f).af + J.D * d ≤ 2 ^ 20 ∧
    (prog J).funcs.all (fun g => !Backend.hasTls g) = true ∧
    sb = Opt.TailLoop.spOf (sys J closedBase).frames f0.name [sp0] ∧
    spec.tailLoops = [n] := by
  have h := factsB_true
  simp only [factsB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩,
    h13⟩, h14⟩, h15⟩, h16⟩, h17⟩, h18⟩, h19⟩, h20⟩, h21⟩, h22⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22⟩

/-- Every code address of the program is below `2^32`. -/
theorem img_lt {x : BitVec 64} (h : img J x) : x.toNat < 2 ^ 32 := by
  obtain ⟨e, he, p, hp, hx⟩ := h
  have hb' : e.2.base.toNat + 4 * e.2.fb.words.size + 4 ≤ 2 ^ 32 := by
    have := List.all_eq_true.mp facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e he
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
theorem base_closed (F : BitVec 64 → Prop) : BaseOk (LinkSys.ofInputCleanup J closedBase F) :=
  baseOk_closedCleanup fun g hg => by
    simpa using List.all_eq_true.1 facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 g hg

/-- The closed base environment has no extern: it keeps the slot-placement oracle. -/
theorem keepsPlace : Clif.EnvKeepsPlace closedBase.env := fun _ _ h => by
  simp [closedBase, Clif.Env.empty] at h

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
    Arm.r_of_w_different (by decide), r_setMem]
  simp [Arm.r, Arm.read_base_error, Arm.ArmState.default]

theorem x0_r : Arm.r (.GPR (rnum 0)) (r m) = 10#64 := by
  simp only [r, rnum]
  rw [Arm.r_of_w_different (by decide), Arm.r_of_w_different (by decide),
    Arm.r_of_w_different (by decide), Arm.r_of_w_same]

theorem x1_r : Arm.r (.GPR (rnum 1)) (r m) = 0#64 := by
  simp only [r, rnum]
  rw [Arm.r_of_w_different (by decide), Arm.r_of_w_different (by decide),
    Arm.r_of_w_different (by decide), Arm.r_of_w_different (by decide), Arm.r_of_w_same]

omit m in
theorem locs : locsOf f.sig = [.reg (.x 0), .reg (.x 1)] := by
  have h := facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold locB at h
  split at h
  · assumption
  · cases h

/-- The outside caller's contract for the transformed `sum` in `r m` (the arguments in x0, x1)
with a stack of `N ≤ 2^20` bytes. -/
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
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp only [VHolds, regVal, x0_r m]; rfl
    · simp only [VHolds, regVal, x1_r m]; rfl
  bytes := fun _ _ hv => by simp [cs', cm, Clif.Mem.valid] at hv
  image := fun _ _ _ hv => by simp [cs', cm, Clif.Mem.valid] at hv
  valid := fun _ _ hv => by simp [cs', cm, Clif.Mem.valid] at hv
  symbols := rfl

omit m in
theorem setMany0 : Clif.Regs.empty.setMany (b0.params.map (·.1)) args' = some regs0 := by
  have hset := facts.2.2.2.2.2.2.2.2.2.1
  show _ = some ((Clif.Regs.empty.setMany (b0.params.map (·.1)) args').getD default)
  revert hset
  cases Clif.Regs.empty.setMany (b0.params.map (·.1)) args' <;> simp

omit m in
theorem setManyF : Clif.Regs.empty.setMany (bF.params.map (·.1)) args' = some regsF := by
  have hset := facts.2.2.2.2.2.2.2.2.2.2.1
  show _ = some ((Clif.Regs.empty.setMany (bF.params.map (·.1)) args').getD default)
  revert hset
  cases Clif.Regs.empty.setMany (bF.params.map (·.1)) args' <;> simp

omit m in
theorem clifEntry' : ClifEntry f args' cs' := by
  obtain ⟨-, -, -, -, hb, -, hsig, -, hpar, -, -, -, hsl, -⟩ := facts
  exact ⟨rfl, rfl, hsig, ⟨bF, hb, rfl, rfl, hpar, setManyF⟩, by simp [cs', hsl]⟩

omit m in
theorem clifEntry : ClifEntry f0 args' cs := by
  obtain ⟨-, -, -, hb, -, hsig, -, hpar, -, -, -, hsl, -⟩ := facts
  exact ⟨rfl, rfl, hsig, ⟨b0, hb, rfl, rfl, hpar, setMany0⟩, by simp [cs, hsl]⟩

/-- The target entry for `compileExeTail_correct_peak`. -/
theorem clifRun : ClifRun J closedBase f (r m) args' cs' where
  entry := clifEntry'
  slots := fun _ _ h => by simp [cs'] at h
  place := fun _ => ⟨[sp0], by
    show some _ = some _
    rw [show spBody (art J f).af (r m) = sb by simp only [spBody, spv_r, sb]]⟩

end State

/-- The input run's entry has a consistent oracle stack: `sb` is what entering `sum` from
`sp0` pushes. -/
theorem spsOk : Opt.TailLoop.SpsOk cs :=
  Opt.TailLoop.spsOk_entry rfl rfl fun pl hp => by
    simp only [cs, cm, Option.some.injEq] at hp
    subst hp
    refine ⟨[sp0], ?_⟩
    show [sb, sp0] = [Opt.TailLoop.spOf (sys J closedBase).frames f0.name [sp0], sp0]
    rw [← facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]

/-- The machine's memory is the loaded image of any file. -/
theorem intact (file : ByteArray) : (imageOf file).Intact (r (memOf file)) := fun a b _ hb => by
  simp only [r, LinkWitness.mem_w, mem_setMem, memOf]
  exact (congrArg (Option.getD · 0) hb).trans rfl

/-- The input program's CLIF run of `sum(10, 0)` returns `55`. -/
theorem run_eq : run = .returned [⟨.i64, 55#64⟩] (LinkWitness.retMem run) := by
  rw [← facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
  exact LinkWitness.eq_returned facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- The input run's call depth is `0`: ten self tail calls add no caller. -/
theorem depth : Clif.DepthLe closedBase.env (prog I0) d cs :=
  Clif.depthLe_of_depthB M cs facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- **Per-run non-vacuity of `Link.DeadCleanup.compileExeTail_correct_peak`** on the
self-tail-recursive `sum`: `Link.DeadCleanup.compileExeTail` produces the executable `file`, with
`sum`'s self tail call turned into a loop (`spec.tailLoops = [sum]`, `f0 ≠ f`); the input
program's CLIF run of `sum(10, 0)` returns `55` with call depth `0`; and, the outside code
calling the compiled `sum` with `10, 0` in x0, x1 and `frameDrop + D * 0` bytes of stack (one
frame for ten tail calls), the executable machine returns to the caller with `55` in x0. -/
theorem cleanup_tail_peak_witness :
    Link.DeadCleanup.compileExeTail spec file0 = .ok file ∧ spec.tailLoops = [n] ∧
    (prog I0).func? n = some f0 ∧ (prog J).func? n = some f ∧ f0 ≠ f ∧
    Clif.DepthLe closedBase.env (prog I0) 0 cs ∧
    OutsideCall J (BinCheck.roByte J spec.tail.data) f (frameDrop (art J f).af + J.D * 0)
      (r (memOf file)) args' cs'.mem ∧
    Clif.runLoop closedBase.env (prog I0) M cs =
      .returned [⟨.i64, 55#64⟩] (LinkWitness.retMem run) ∧
    ∃ k, ArmRet ra0 (r (memOf file)) (runX (step J closedBase file) k (r (memOf file))) ∧
      XHolds ⟨.i64, 55#64⟩ (xreg 0 (runX (step J closedBase file) k (r (memOf file)))) := by
  obtain ⟨hf0, hf, hne, -⟩ := facts
  have hoc := outsideCall (memOf file) (BinCheck.roByte J spec.tail.data)
    facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h := (Link.DeadCleanup.compileExeTail_correct_peak compile_eq closedBase (base_closed _)
    (hooksSim_closed J) keepsPlace hf0 hf d (intact file) hoc (clifRun _) clifEntry rfl rfl
    spsOk depth M).1 _ _ run_eq
  rw [x30_r] at h
  obtain ⟨k, hret, hx, -⟩ := h
  exact ⟨compile_eq, facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2, hf0, hf, hne, depth, hoc,
    run_eq, k, hret, hx 0 _ rfl⟩

end Crates.DeadCleanupExeTailPeakWitness
