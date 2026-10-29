import Crates.BinaryWitness
import Crates.LeanLinkWitness
import FV.Link.NonVacuityExeSource

/-! # Non-vacuity of the executable compiler's theorem on an original recursive `i128` program

`Link.compileExe` compiles the natively self-recursive `i128` function
`rec128(x : i128, n : i64) -> i128` (`rec128(x, n) = n = 0 ? x : rec128(x + x, n - 1)`, its own
declaration `fn0 = colocated %rec128`), legalised to `(i64, i64, i64) -> (i64, i64)` (the `i128`
addition split into halves with a carry, the self call with split arguments), placed at 16 MiB in
the placeholder executable of `Crates.LeanLinkWitness` (`compile_eq`). The input is in the source
domain (`SrcScopeB`); the legalised entry reaches a call cycle (`cyclic`), so neither
`Link.compileExe_correct` nor `Link.compileExe_correct_source` applies. The outside world is
`Link.SourceWitness.helperBase`.

Outside code calls the compiled `rec128` with the ABI-split arguments `3, 1, 3` in x0–x2
(`x = 2^64 + 3`, `n = 3`) and `frameDrop + D * 3` bytes of stack. The **original** program's CLIF
run of `rec128` returns `8 * x = 8 * 2^64 + 24` after four activations: its call depth is `3`
(`depth`: no state of the source run has more than three callers). Every premise of
`Link.compileExe_correct_source_peak` holds (through
`Link.SourceWitness.compileExe_correct_source_peak_helper`), and it gives the executable
machine's return to the caller with the split result `24, 8` in x0, x1
(`compileExe_source_peak_witness`).
-/

namespace Crates.CompileExeSourcePeakWitness

open E2E E2E.LinkCheck E2E.Binary E2E.ExecBytes Backend Backend.Proof Link Link.SourceWitness
  Opt.Legalize128
open Crates.BinaryWitness (memOf)

/-- The self-recursive `i128` function. -/
def src : String := "function %rec128(i128, i64) -> i128 system_v {
    fn0 = colocated %rec128(i128, i64) -> i128 system_v
block0(v0: i128, v1: i64):
    brif v1, block1, block2
block1:
    v2 = iconst.i64 1
    v3 = isub v1, v2
    v4 = iadd v0, v0
    v5 = call fn0(v4, v3)
    return v5
block2:
    return v0
}
"

/-- `rec128` as an input of the executable compiler (the spill-fallback allocation). -/
def fnInput : FnInput := { clif := src, ra := "{}" }

/-- `rec128` placed at 16 MiB with its compiled size. -/
def spec : LinkSpec :=
  let fs := [fnInput]
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

/-- **The executable compiler compiles `rec128` to `file`.** -/
theorem compile_eq : compileExe spec file0 = .ok file := by
  have h : InScopeIn spec.input0 = true := by native_decide
  simp only [compileExe, inScopeInPar_eq, h, ↓reduceIte, link_eq]

/-- The placed input. -/
abbrev J : LinkInput := spec.input

/-- The entry's name. -/
def n : String := "rec128"

/-- The **source** `rec128` (as parsed, with an `i128` parameter and result). -/
def fs : Clif.Function := (J.srcProg.func? n).getD default

/-- The compiled function: its legalisation. -/
def f : Clif.Function := ((prog J).func? n).getD default

def bS : Clif.Block := fs.entry?.getD default
def bF : Clif.Block := f.entry?.getD default

/-- The source arguments `x = 2^64 + 3`, `n = 3`. -/
def args : List Clif.Val := [⟨.i128, 1#64 ++ 3#64⟩, ⟨.i64, 3#64⟩]

/-- Their ABI split: `x`'s low and high halves, `n`. -/
def args' : List Clif.Val := [⟨.i64, 3#64⟩, ⟨.i64, 1#64⟩, ⟨.i64, 3#64⟩]

/-- The source run's fuel (it returns within `20` steps). -/
def M : Nat := 24

/-- The source run's peak call depth: three callers below the running activation. -/
def d : Nat := 3

/-- The caller's stack pointer and return address (outside the program's code). -/
def sp0 : BitVec 64 := 0x10000000000
def ra0 : BitVec 64 := 0x20000000000

theorem sp0_toNat : sp0.toNat = 2 ^ 40 := rfl

/-- The body's stack pointer of the entry. -/
def sb : BitVec 64 := sp0 - BitVec.ofNat 64 (frameDrop (artOf J.results f).af)

/-- The caller's CLIF memory: no live allocation, the CLIF image's symbols, the slot-placement
oracle at the entry's body `sp`. -/
def cm : Clif.Mem :=
  { symbols := fun n => J.syms.lookup n, place := some ⟨[sb], (sys J helperBase).frames, none⟩ }

/-- The source entry state of `rec128` on `x`, `n`. -/
def cs : Clif.State where
  frame := { func := fs, regs := (Clif.Regs.empty.setMany (bS.params.map (·.1)) args).getD default,
             slots := [], body := bS.body, term := bS.term }
  callers := []
  mem := cm

/-- The target entry state of the legalised `rec128` on the split arguments. -/
def cs' : Clif.State where
  frame := { func := f, regs := (Clif.Regs.empty.setMany (bF.params.map (·.1)) args').getD default,
             slots := [], body := bF.body, term := bF.term }
  callers := []
  mem := cm

/-- The original program's CLIF run from `cs`. -/
def run : Clif.Outcome := Clif.runLoop helperEnv J.srcProg M cs

/-- The machine state of the call with memory `m`: pc at `f`'s address, x30 the caller's return
address, `sp0`, the split arguments in x0–x2. -/
def r (m : Arm.Memory) : Arm.ArmState :=
  Arm.w .PC (artOf J.results f).base (Arm.w (.GPR 30#5) ra0 (Arm.w (.GPR 31#5) sp0
    (Arm.w (.GPR 0#5) 3#64 (Arm.w (.GPR 1#5) 1#64 (Arm.w (.GPR 2#5) 3#64
      (setMem Arm.ArmState.default m))))))

/-- The source parameters' ABI groups: an `i128` value (low then high half), an `i64`. -/
def gpB : Bool :=
  match Opt.Legal.groups fs.sig.params with
  | some [[.lo, .hi], [.val _]] => true
  | _ => false

/-- The source result's ABI groups: one `i128` value. -/
def grB : Bool :=
  match Opt.Legal.groups fs.sig.returns with
  | some [[.lo, .hi]] => true
  | _ => false

def locB : Bool :=
  match locsOf f.sig with
  | [.reg (.x 0), .reg (.x 1), .reg (.x 2)] => true
  | _ => false

/-- The facts decided on the source and the compiled program. -/
def factsB : Bool :=
  decide (J.srcProg.func? n = some fs) && decide ((prog J).func? n = some f) &&
  decide (legalize fs = f) && mentions128 fs &&
  decide (fs.entry? = some bS) && decide (f.entry? = some bF) &&
  decide (args.map (·.ty) = fs.sig.params.map (·.ty)) &&
  decide (bS.params.map (·.2) = args.map (·.ty)) &&
  (Clif.Regs.empty.setMany (bS.params.map (·.1)) args).isSome &&
  decide (args'.map (·.ty) = f.sig.params.map (·.ty)) &&
  decide (bF.params.map (·.2) = args'.map (·.ty)) &&
  (Clif.Regs.empty.setMany (bF.params.map (·.1)) args').isSome &&
  decide (fs.slots = []) && decide (f.slots = []) && locB &&
  gpB && grB &&
  LinkWitness.isRet run && decide (LinkWitness.retVals run = [⟨.i128, 8#64 ++ 24#64⟩]) &&
  Clif.depthB helperEnv J.srcProg d M cs &&
  (tabOf J.results).all (fun e => decide (e.2.base.toNat + 4 * e.2.fb.words.size + 4 ≤ 2 ^ 32)) &&
  !StackBound.goodN J n &&
    decide (frameDrop (artOf J.results f).af + (J.D * d + pbMaxOf J.results) ≤ 2 ^ 20) &&
  (prog J).funcs.all (fun g => !Backend.hasTls g) &&
  (prog J).funcs.all (fun g => g.externs.all fun e =>
    ((prog J).func? e.2.name).isSome || !Clif.Rust.isDivHelper e.2.name) &&
  (prog J).funcs.all indFreeB && (prog J).funcs.all (fun g => (indSigs g).isEmpty) &&
  J.srcProg.funcs.all (fun g => g.slots.isEmpty) && SrcScopeB J

theorem factsB_true : factsB = true := by native_decide

theorem facts :
    J.srcProg.func? n = some fs ∧ (prog J).func? n = some f ∧ legalize fs = f ∧
    mentions128 fs = true ∧ fs.entry? = some bS ∧ f.entry? = some bF ∧
    args.map (·.ty) = fs.sig.params.map (·.ty) ∧ bS.params.map (·.2) = args.map (·.ty) ∧
    (Clif.Regs.empty.setMany (bS.params.map (·.1)) args).isSome = true ∧
    args'.map (·.ty) = f.sig.params.map (·.ty) ∧ bF.params.map (·.2) = args'.map (·.ty) ∧
    (Clif.Regs.empty.setMany (bF.params.map (·.1)) args').isSome = true ∧
    fs.slots = [] ∧ f.slots = [] ∧ locB = true ∧
    gpB = true ∧ grB = true ∧
    LinkWitness.isRet run = true ∧ LinkWitness.retVals run = [⟨.i128, 8#64 ++ 24#64⟩] ∧
    Clif.depthB helperEnv J.srcProg d M cs = true ∧
    (tabOf J.results).all (fun e => decide (e.2.base.toNat + 4 * e.2.fb.words.size + 4 ≤ 2 ^ 32))
      = true ∧
    StackBound.goodN J n = false ∧
    frameDrop (artOf J.results f).af + (J.D * d + pbMaxOf J.results) ≤ 2 ^ 20 ∧
    (prog J).funcs.all (fun g => !Backend.hasTls g) = true ∧
    (prog J).funcs.all (fun g => g.externs.all fun e =>
      ((prog J).func? e.2.name).isSome || !Clif.Rust.isDivHelper e.2.name) = true ∧
    (prog J).funcs.all indFreeB = true ∧ (prog J).funcs.all (fun g => (indSigs g).isEmpty) = true ∧
    J.srcProg.funcs.all (fun g => g.slots.isEmpty) = true ∧ SrcScopeB J = true := by
  have h := factsB_true
  simp only [factsB, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩,
    h12⟩, h13⟩, h14⟩, h15⟩, h16⟩, h17⟩, h18⟩, h19⟩, h20⟩, h21⟩, h22⟩, h23⟩, h24⟩, h25⟩, h26⟩,
    h27⟩, h28⟩, h29⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    h21, h22, h23, h24, h25, h26, h27, h28, h29⟩

/-- `okB` of the placed input (by construction, `okB_leanLink`). -/
theorem okB_J : okB J = true := okB_leanLink inScope link_eq

/-- **The legalised entry reaches a call cycle**: the premise `¬ CycleFrom` of
`compileExe_correct` and `compileExe_correct_source` fails. -/
theorem cyclic : StackBound.CycleFrom (StackBound.Calls J J.results) (legalize fs) := by
  refine Classical.byContradiction fun hc => ?_
  have h := (StackBound.goodN_iff okB_J).2 ⟨legalize fs, by rw [facts.2.2.1]; exact facts.2.1, hc⟩
  rw [facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1] at h
  cases h

/-- Every code address of the program is below `2^32`. -/
theorem img_lt {x : BitVec 64} (h : img J x) : x.toNat < 2 ^ 32 := by
  obtain ⟨e, he, p, hp, hx⟩ := h
  have hb' : e.2.base.toNat + 4 * e.2.fb.words.size + 4 ≤ 2 ^ 32 := by
    have := List.all_eq_true.mp facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e he
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
  have h := facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold locB at h
  split at h
  · assumption
  · cases h

omit m in
theorem gp : ∃ p, Opt.Legal.groups fs.sig.params = some [[.lo, .hi], [.val p]] := by
  have h := facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold gpB at h
  split at h
  · exact ⟨_, ‹_›⟩
  · cases h

omit m in
theorem gr : Opt.Legal.groups fs.sig.returns = some [[.lo, .hi]] := by
  have h := facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold grB at h
  split at h
  · assumption
  · cases h

/-- The outside caller's contract for the legalised `rec128` in `r m` (the split arguments in
x0–x2) with a stack of `N ≤ 2^20` bytes. -/
theorem outsideCall (roB : BitVec 64 → Option (BitVec 8)) {N : Nat} (hN : N ≤ 2 ^ 20) :
    OutsideCall J roB (legalize fs) N (r m) args' cs'.mem where
  pc := by rw [facts.2.2.1]; exact pc_r m
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
    rw [facts.2.2.1, locs] at hm
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
theorem clifEntry' : ClifEntry (legalize fs) args' cs' := by
  obtain ⟨-, -, hl, -, -, hb, -, -, -, hsig, hpar, hset, -, hsl, -⟩ := facts
  rw [hl]
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

/-- The target entry for `compileExe_correct_peak`. -/
theorem clifRun : ClifRun J helperBase (legalize fs) (r m) args' cs' where
  entry := clifEntry'
  slots := fun _ _ h => by simp [cs'] at h
  place := fun _ => ⟨[], by
    show some _ = some _
    rw [show spBody (art J (legalize fs)).af (r m) = sb by
      simp only [spBody, spv_r, sb, facts.2.2.1]]⟩

end State

/-- The machine's memory is the loaded image of any file. -/
theorem intact (file : ByteArray) : (imageOf file).Intact (r (memOf file)) := fun a b _ hb => by
  simp only [r, LinkWitness.mem_w, mem_setMem, memOf]
  exact (congrArg (Option.getD · 0) hb).trans rfl

/-- The original program's CLIF run of `rec128` returns `8 * 2^64 + 24`. -/
theorem run_eq : run = .returned [⟨.i128, 8#64 ++ 24#64⟩] (LinkWitness.retMem run) := by
  rw [← facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
  exact LinkWitness.eq_returned facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- The source run's call depth is at most `d = 3`. -/
theorem depth : Clif.DepthLe helperEnv J.srcProg d cs :=
  Clif.depthLe_of_depthB M cs facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem cm_bounded : Opt.Legal.MemBounded cs.mem := fun _ _ h => by
  simp [cs, cm, Clif.Mem.valid] at h

/-- **Per-run non-vacuity of `Link.compileExe_correct_source_peak`** on the original recursive
`i128` program `rec128`: `compileExe` produces the executable `file`; the input is in the source
domain and `rec128` mentions `i128`; the legalised entry reaches a call cycle (so the acyclic
theorems do not apply); the original program's CLIF run of `rec128` on `2^64 + 3` and `3` returns
`8 * 2^64 + 24` with call depth at most `3`; and, the outside code calling the executable's
compiled `rec128` with the split arguments in x0–x2 and `frameDrop + D * 3` bytes of stack, the
executable machine returns to the caller with the split result `24, 8` in x0, x1. -/
theorem compileExe_source_peak_witness :
    compileExe spec file0 = .ok file ∧ SrcScopeB J = true ∧
    J.srcProg.func? n = some fs ∧ mentions128 fs = true ∧
    StackBound.CycleFrom (StackBound.Calls J J.results) (legalize fs) ∧
    Clif.DepthLe helperEnv J.srcProg d cs ∧
    OutsideCall J (BinCheck.roByte J spec.data) (legalize fs)
      (frameDrop (art J (legalize fs)).af + (J.D * d + pbMaxOf J.results)) (r (memOf file)) args'
      cs'.mem ∧
    Clif.runLoop helperEnv J.srcProg M cs = .returned [⟨.i128, 8#64 ++ 24#64⟩]
      (LinkWitness.retMem run) ∧
    ∃ k, ArmRet ra0 (r (memOf file)) (runX (step J helperBase file) k (r (memOf file))) ∧
      XHolds ⟨.i64, 24#64⟩ (xreg 0 (runX (step J helperBase file) k (r (memOf file)))) ∧
      XHolds ⟨.i64, 8#64⟩ (xreg 1 (runX (step J helperBase file) k (r (memOf file)))) := by
  obtain ⟨hf, -, hl, hm, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hst, htls, hdivB,
    hindB, hsigsB, hslotsB, hsrc⟩ := facts
  have hexp : Opt.Legal.ExpRel ((Opt.Legal.groups fs.sig.params).getD []) args args' := by
    obtain ⟨p, hp⟩ := gp
    rw [hp, Option.getD_some]
    exact ⟨⟨3#64, 1#64, rfl, rfl, rfl⟩, rfl, trivial⟩
  have hdiv : ∀ g ∈ (prog J).funcs, ∀ e ∈ g.externs, (prog J).func? e.2.name = none →
      Clif.Rust.isDivHelper e.2.name = false := by
    intro g hg e he hn
    have := List.all_eq_true.mp (List.all_eq_true.mp hdivB g hg) e he
    simpa [hn] using this
  have hst' : frameDrop (art J (legalize fs)).af + (J.D * d + pbMaxOf J.results) ≤ 2 ^ 20 := by
    rw [hl]; exact hst
  have hoc := outsideCall (memOf file) (BinCheck.roByte J spec.data) hst'
  have h := compileExe_correct_source_peak_helper compile_eq hsrc
    (fun g hg => by simpa using List.all_eq_true.mp htls g hg) hdiv
    (fun g hg => indFreeB_sound (List.all_eq_true.mp hindB g hg))
    (fun g hg => by simpa using List.all_eq_true.mp hsigsB g hg)
    (fun g hg => by simpa using List.all_eq_true.mp hslotsB g hg)
    hf d (intact file) hoc (clifRun _) clifEntry hexp rfl rfl cm_bounded depth M _ _ run_eq
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
    exact ⟨compile_eq, hsrc, hf, hm, cyclic, depth, hoc, run_eq, k, hret, hx 0 _ rfl,
      hx 1 _ rfl⟩

end Crates.CompileExeSourcePeakWitness
