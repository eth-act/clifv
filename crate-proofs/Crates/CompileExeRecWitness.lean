import Crates.BinaryWitness
import Crates.LeanLinkWitness
import FV.Link.Exe

/-! # Per-run non-vacuity of the executable compiler's theorem for recursive programs (L1d)

`Link.compileExe` compiles the natively self-recursive function `direct`
(`E2E.LinkWitness.DirectSelf`: `direct(n) = n = 0 ? 0 : direct(n - 1) + 2`, its own declaration
`fn0 = colocated %direct`) placed at 16 MiB, the placeholder executable of
`Crates.LeanLinkWitness`: `compile_eq`. Its call graph has a cycle reachable from the entry
(`cyclic`), so `Link.compileExe_correct` does not apply. On the executable it produces (`file`),
outside code calls `direct` with `3`, with the file's loaded image as the machine's memory and
`frameDrop + D * M` bytes of stack: every premise of `Link.compileExe_correct_depth` holds, the
reference CLIF run (four activations of `direct`) returns `6`, and the theorem gives the
**executable machine's** return (the processor on `file`'s own words) to the caller with `6` in x0
(`compileExe_rec_witness`). The stack premise is not vacuous (`stack_needed`): it asks for more
than the static amount `stackFn` (which ignores the recursion), and fails for the same call with a
stack pointer of `16`.
-/

namespace Crates.CompileExeRecWitness

open E2E E2E.LinkCheck E2E.Binary E2E.ExecBytes Backend Backend.Proof Link
open Crates.BinaryWitness (memOf)

/-- The program for the executable compiler: `direct` placed at 16 MiB with its compiled size. -/
def spec : LinkSpec :=
  let fs := [E2E.LinkWitness.DirectSelf.fnInput]
  let names := fs.map (·.func.name)
  { funcs := fs, names,
    sizes := fs.map fun fi => (getOk (pipeT fi.func fi.k 0 (raJ fi.ra fi.j))).fb.words.size,
    outside := [], symNames := names, R := 0x1000000 }

/-- The executable before the compiler: the region's placeholder, the link map's symbols. -/
def file0 : ByteArray :=
  LeanLinkWitness.placeholder spec.R spec.size
    (spec.addrs.map fun p => (BinCheck.symName p.1, p.2))

theorem link_ok : (leanLink spec file0).toBool = true := by native_decide

/-- The executable. -/
def file : ByteArray := getOk (leanLink spec file0)

theorem link_eq : leanLink spec file0 = .ok file := E2E.LinkCheck.getOk_eq link_ok

theorem inScope : InScopeP spec.input = true := by native_decide

/-- **The executable compiler compiles the recursive `direct` to `file`.** -/
theorem compile_eq : compileExe spec file0 = .ok file := by
  have h : InScopeIn spec.input0 = true := by native_decide
  simp only [compileExe, inScopeInPar_eq, h, ↓reduceIte, link_eq]

/-- The placed input. -/
abbrev J : LinkInput := spec.input

/-! ## The outside call of `direct` with `3` -/

def n : String := "direct"

def f : Clif.Function := E2E.LinkWitness.DirectSelf.func

def bF : Clif.Block := f.entry?.getD default

def args : List Clif.Val := [⟨.i64, 3#64⟩]

/-- The CLIF run's fuel `M + 1` and the machine's depth. -/
def M : Nat := 64

/-- The caller's stack pointer and return address (outside the program's code). -/
def sp0 : BitVec 64 := 0x10000000000
def ra0 : BitVec 64 := 0x20000000000

/-- The body's stack pointer of the entry. -/
def sb : BitVec 64 := sp0 - BitVec.ofNat 64 (frameDrop (artOf J.results f).af)

/-- The caller's CLIF memory: no live allocation, the CLIF image's symbols, the slot-placement
oracle at the entry's body `sp`. -/
def cm : Clif.Mem :=
  { symbols := fun n => J.syms.lookup n, place := some ⟨[sb], (sys J closedBase).frames, none⟩ }

/-- The reference CLIF entry state of `direct` on `3`. -/
def cs : Clif.State where
  frame := { func := f, regs := (Clif.Regs.empty.setMany (bF.params.map (·.1)) args).getD default,
             slots := [], body := bF.body, term := bF.term }
  callers := []
  mem := cm

/-- The program's CLIF run from `cs`. -/
def run : Clif.Outcome := Clif.runLoop closedBase.env (progOf J.results) (M + 1) cs

/-- The machine state of the call with stack pointer `sp` and memory `m`: pc at `direct`'s
address, x30 the caller's return address, the argument in x0. -/
def r (sp : BitVec 64) (m : Arm.Memory) : Arm.ArmState :=
  Arm.w .PC (artOf J.results f).base (Arm.w (.GPR 30#5) ra0 (Arm.w (.GPR 31#5) sp
    (Arm.w (.GPR 0#5) 3#64 (setMem Arm.ArmState.default m))))

def locB : Bool :=
  match locsOf f.sig with
  | [.reg (.x 0)] => true
  | _ => false

/-- The facts of the placed program decided on its compiled code. -/
def factsB : Bool :=
  decide ((progOf J.results).func? n = some f) && decide (f.entry? = some bF) &&
  decide (args.map (·.ty) = f.sig.params.map (·.ty)) &&
  decide (bF.params.map (·.2) = args.map (·.ty)) &&
  (Clif.Regs.empty.setMany (bF.params.map (·.1)) args).isSome && decide (f.slots = []) &&
  locB &&
  LinkWitness.isRet run && decide (LinkWitness.retVals run = [⟨.i64, 6#64⟩]) &&
  (tabOf J.results).all (fun e => decide (e.2.base.toNat + 4 * e.2.fb.words.size + 4 ≤ 2 ^ 32)) &&
  decide (frameDrop (artOf J.results f).af + (J.D * M + pbMaxOf J.results) ≤ 2 ^ 20) &&
  decide (StackBound.stackFn J f < frameDrop (artOf J.results f).af + (J.D * M + pbMaxOf J.results)) &&
  decide (16 < frameDrop (artOf J.results f).af + (J.D * M + pbMaxOf J.results)) &&
  (progOf J.results).funcs.all (fun g => !Backend.hasTls g) &&
  !StackBound.goodN J n

theorem factsB_true : factsB = true := by native_decide

theorem facts :
    (progOf J.results).func? n = some f ∧ f.entry? = some bF ∧
    args.map (·.ty) = f.sig.params.map (·.ty) ∧ bF.params.map (·.2) = args.map (·.ty) ∧
    (Clif.Regs.empty.setMany (bF.params.map (·.1)) args).isSome = true ∧ f.slots = [] ∧
    locB = true ∧ LinkWitness.isRet run = true ∧ LinkWitness.retVals run = [⟨.i64, 6#64⟩] ∧
    (tabOf J.results).all (fun e => decide (e.2.base.toNat + 4 * e.2.fb.words.size + 4 ≤ 2 ^ 32))
      = true ∧
    frameDrop (artOf J.results f).af + (J.D * M + pbMaxOf J.results) ≤ 2 ^ 20 ∧
    StackBound.stackFn J f < frameDrop (artOf J.results f).af + (J.D * M + pbMaxOf J.results) ∧
    16 < frameDrop (artOf J.results f).af + (J.D * M + pbMaxOf J.results) ∧
    (progOf J.results).funcs.all (fun g => !Backend.hasTls g) = true ∧
    StackBound.goodN J n = false := by
  have h := factsB_true
  simp only [factsB, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩,
    h15⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩

/-- `okB` of the placed input (by construction, `okB_leanLink`). -/
theorem okB_J : okB J = true := okB_leanLink inScope link_eq

/-- The closed base environment's premises. -/
theorem base_closed (F : BitVec 64 → Prop) : BaseOk (LinkSys.ofInput J closedBase F) :=
  baseOk_closed fun g hg => by simpa using List.all_eq_true.1 facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1 g hg

/-- **The entry reaches a call cycle**: `compileExe_correct`'s premise `¬ CycleFrom` fails. -/
theorem cyclic : StackBound.CycleFrom (StackBound.Calls J J.results) f := by
  refine Classical.byContradiction fun hc => ?_
  have h := (StackBound.goodN_iff okB_J).2 ⟨f, facts.1, hc⟩
  rw [facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2] at h
  cases h

/-- Every code address of the program is below `2^32`. -/
theorem img_lt {x : BitVec 64} (h : img J x) : x.toNat < 2 ^ 32 := by
  obtain ⟨e, he, p, hp, hx⟩ := h
  have hb' : e.2.base.toNat + 4 * e.2.fb.words.size + 4 ≤ 2 ^ 32 := by
    have := List.all_eq_true.mp facts.2.2.2.2.2.2.2.2.2.1 e he
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

variable (sp : BitVec 64) (m : Arm.Memory)

theorem pc_r : Arm.r .PC (r sp m) = (artOf J.results f).base := Arm.r_of_w_same

theorem spv_r : spv (r sp m) = sp := by
  simp only [spv, r]
  rw [Arm.r_of_w_different (by decide), Arm.r_of_w_different (by decide), Arm.r_of_w_same]

theorem x30_r : xreg 30 (r sp m) = ra0 := by
  simp only [xreg, r]
  rw [Arm.r_of_w_different (by decide), Arm.r_of_w_same]

theorem err_r : Arm.r .ERR (r sp m) = .None := by
  simp only [r]
  rw [Arm.r_of_w_different (by decide), Arm.r_of_w_different (by decide),
    Arm.r_of_w_different (by decide), Arm.r_of_w_different (by decide), r_setMem]
  simp [Arm.r, Arm.read_base_error, Arm.ArmState.default]

theorem x0_r : Arm.r (.GPR (rnum 0)) (r sp m) = 3#64 := by
  simp only [r, rnum]
  rw [Arm.r_of_w_different (by decide), Arm.r_of_w_different (by decide),
    Arm.r_of_w_different (by decide), Arm.r_of_w_same]

omit sp m in
theorem locs : locsOf f.sig = [.reg (.x 0)] := by
  have h := facts.2.2.2.2.2.2.1
  unfold locB at h
  split at h
  · assumption
  · cases h

/-- The outside caller's contract holds in `r sp0 m` with a stack of `N ≤ 2^20` bytes. -/
theorem outsideCall (roB : BitVec 64 → Option (BitVec 8)) {N : Nat} (hN : N ≤ 2 ^ 20) :
    OutsideCall J roB f N (r sp0 m) args cs.mem where
  pc := pc_r sp0 m
  err := err_r sp0 m
  ra := fun h => by have := img_lt h; rw [x30_r] at this; simp [ra0] at this
  spAligned := by rw [spv_r]; decide
  stack := by rw [spv_r, show sp0.toNat = 2 ^ 40 from rfl]; omega
  stackFree := fun a ha hb => by
    have := img_lt ha
    rw [spv_r] at hb
    obtain ⟨-, h2⟩ := hb
    rw [show sp0.toNat = 2 ^ 40 from rfl] at h2
    omega
  args := fun loc v hm => by
    rw [locs] at hm
    simp only [args, List.zip_cons_cons, List.zip_nil_right, List.mem_cons, Prod.mk.injEq,
      List.not_mem_nil, or_false] at hm
    obtain ⟨rfl, rfl⟩ := hm
    simp only [VHolds, regVal, x0_r sp0 m]; rfl
  bytes := fun _ _ hv => by simp [cs, cm, Clif.Mem.valid] at hv
  image := fun _ _ _ hv => by simp [cs, cm, Clif.Mem.valid] at hv
  valid := fun _ _ hv => by simp [cs, cm, Clif.Mem.valid] at hv
  symbols := rfl

omit sp m in
theorem clifEntry : ClifEntry f args cs := by
  obtain ⟨-, hb, hsig, hpar, hset, hsl, -⟩ := facts
  refine ⟨rfl, rfl, hsig, ⟨bF, hb, rfl, rfl, hpar, ?_⟩, by simp [cs, hsl]⟩
  show _ = some ((Clif.Regs.empty.setMany (bF.params.map (·.1)) args).getD default)
  revert hset
  cases Clif.Regs.empty.setMany (bF.params.map (·.1)) args <;> simp

/-- The reference CLIF run. -/
theorem clifRun : ClifRun J closedBase f (r sp0 m) args cs where
  entry := clifEntry
  slots := fun _ _ h => by simp [cs] at h
  place := fun _ => ⟨[], by
    show some _ = some _
    rw [show spBody (art J f).af (r sp0 m) = sb by simp only [spBody, spv_r, sb]]⟩

end State

/-- The machine's memory is the loaded image of any file. -/
theorem intact (file : ByteArray) : (imageOf file).Intact (r sp0 (memOf file)) :=
  fun a b _ hb => by
    simp only [r, LinkWitness.mem_w, mem_setMem, memOf]
    exact (congrArg (Option.getD · 0) hb).trans rfl

/-- The program's CLIF run returns `6`. -/
theorem run_eq : run = .returned [⟨.i64, 6#64⟩] (LinkWitness.retMem run) := by
  rw [← facts.2.2.2.2.2.2.2.2.1]
  exact LinkWitness.eq_returned facts.2.2.2.2.2.2.2.1

/-- **Per-run non-vacuity of `Link.compileExe_correct_depth`** on the recursive `direct`:
`compileExe` produces the executable `file`; the entry reaches a call cycle (so
`compileExe_correct` does not apply); in the machine state whose memory is `file`'s loaded image
and in which outside code calls `direct` with `3`, every premise of `compileExe_correct_depth`
holds — the closed base environment (`BaseOk`, `HooksSim`), the loader's image (`Intact`), the
boundary contract (`OutsideCall` with `frameDrop + D * M` bytes of stack), the reference CLIF run
(which returns `6` after four activations of `direct`), `TrapsExplicit` — and the theorem gives the
executable machine (`step`: the processor on `file`'s own words) returning to the caller with `6`
in x0. -/
theorem compileExe_rec_witness :
    compileExe spec file0 = .ok file ∧
    StackBound.CycleFrom (StackBound.Calls J J.results) f ∧
    BaseOk (sys J closedBase) ∧ HooksSim J closedBase ∧ (prog J).func? n = some f ∧
    (imageOf file).Intact (r sp0 (memOf file)) ∧
    OutsideCall J (BinCheck.roByte J spec.data) f (frameDrop (art J f).af + (J.D * M + pbMaxOf J.results))
      (r sp0 (memOf file)) args cs.mem ∧
    ClifRun J closedBase f (r sp0 (memOf file)) args cs ∧
    TrapsExplicit (Clif.linkEnvN (prog J) closedBase.env M) (prog J).bare cs ∧
    Clif.runLoop closedBase.env (prog J) (M + 1) cs =
      .returned [⟨.i64, 6#64⟩] (LinkWitness.retMem run) ∧
    ∃ k, ArmRet ra0 (r sp0 (memOf file)) (runX (step J closedBase file) k (r sp0 (memOf file))) ∧
      XHolds ⟨.i64, 6#64⟩ (xreg 0 (runX (step J closedBase file) k (r sp0 (memOf file)))) := by
  have hf := facts.1
  have hfm := (Clif.Program.func?_some hf).1
  have hB := base_closed fun _ => False
  have hX := intact file
  have hoc := outsideCall (memOf file) (BinCheck.roByte J spec.data) facts.2.2.2.2.2.2.2.2.2.2.1
  have hL := okB_sound okB_J (base_closed (img J)) (fun _ h => h)
  have htr := trapsExplicit_of_run hL hfm clifEntry rfl run_eq
  have h := compileExe_correct_depth compile_eq closedBase hB (hooksSim_closed J) hf M hX hoc
    (clifRun _) htr
  rw [show Clif.runLoop closedBase.env (prog J) (M + 1) cs = run from rfl, run_eq, x30_r] at h
  obtain ⟨k, hret, hx, -⟩ := h
  exact ⟨compile_eq, cyclic, hB, hooksSim_closed J, hf, hX, hoc, clifRun _, htr, run_eq, k, hret,
    hx 0 _ rfl⟩

/-- **The stack premise is not vacuous**: `frameDrop + D * M` is more than the static amount
`stackFn` (which, for a recursive entry, counts no callee frame), and the same call with the
stack pointer at `16` does not meet `OutsideCall` with it. -/
theorem stack_needed :
    StackBound.stackFn J f < frameDrop (art J f).af + (J.D * M + pbMaxOf J.results) ∧
    ∀ (m : Arm.Memory) (roB : BitVec 64 → Option (BitVec 8)),
      ¬ OutsideCall J roB f (frameDrop (art J f).af + (J.D * M + pbMaxOf J.results)) (r 16#64 m) args
        cs.mem := by
  refine ⟨facts.2.2.2.2.2.2.2.2.2.2.2.1, fun m roB h => ?_⟩
  have hs := h.stack
  rw [spv_r] at hs
  have : 16 < frameDrop (art J f).af + (J.D * M + pbMaxOf J.results) :=
    facts.2.2.2.2.2.2.2.2.2.2.2.2.1
  simp only [BitVec.toNat_ofNat] at hs
  omega

end Crates.CompileExeRecWitness
