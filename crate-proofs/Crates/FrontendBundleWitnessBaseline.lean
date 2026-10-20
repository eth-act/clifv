import Crates.FrontendBundleWitness

/-! # Non-vacuity of the baseline compiler's bundle theorems on a real codegen unit (T7e)

The baseline executable compiler `Link.compileExe` on the `LinkSpec` built from the bundle of
`Crates.FrontendBundleWitness` (the unit of `g_u128` with `wmul_u128` and the local
`wrapping_mul`, as the frontend wrote them), with the **baseline** pipeline's sizes (`bwB`: the
same units, symbols and markers, the sizes `pipeT`'s). The facts of
`Crates.CompileExeSourceWitness`, re-derived for its input `J := SB.input`; the renaming and the
pre-renaming run are `Crates.FrontendBundleWitness`'s.

* `bundle_baseline_witness`: `Front.bundle_correct_source_baseline` (acyclic entry);
* `bundle_baseline_peak_witness`: `Front.bundle_correct_source_peak_baseline` (call depth `1`,
  `frameDrop + D * 1` bytes of stack).

Both: the pre-renaming program's CLIF run of `wmul_u128` on `2^64 + 3` and `5` returns
`5 * 2^64 + 15`, and the executable machine, called with the split arguments `3, 1, 5, 0` in
x0–x3, returns to the caller with `15, 5` in x0, x1.
-/

namespace Crates.FrontendBundleWitnessBaseline

open E2E E2E.LinkCheck E2E.Binary E2E.ExecBytes Backend Backend.Proof Opt.Legalize128
open Link (LinkSpec inScopePar_eq)
open Link.SourceWitness (helperEnv helperBase)
open Crates.BinaryWitness (memOf)
open Crates.CompileExeSourceWitness (n args args' M sp0 ra0 sp0_toNat)
open Crates.FrontendBundleWitness (b0 us hus sc sc_ok f0 hf0 f0_mentions alpha mulClif mulLinked
  srcProg_of pre_fn pre_entry pre_bnd pre_depth pre_run split_ret)

/-! ## The bundle with the baseline sizes and its `LinkSpec` -/

/-- The baseline pipeline's sizes of the assembled (renamed) functions, by linked name. -/
def sizesB : List (String × Nat) :=
  match Front.assemble b0 with
  | .ok A => A.names.zip (A.funcs.map fun fi =>
      (getOk (pipeT fi.func fi.k 0 (raJ fi.ra fi.j))).fb.words.size)
  | .error _ => []

/-- **The bundle** for the baseline compiler. -/
def bwB : Front.Bundle := { b0 with sizes := sizesB }

theorem husB : bwB.units.mapM Front.parseUnit = .ok us := hus

theorem buildSpec_ok : (Front.buildSpec bwB).toBool = true := by native_decide

/-- The `LinkSpec` built from the bundle. -/
def SB : LinkSpec := getOk (Front.buildSpec bwB)

theorem buildSpec_eq : Front.buildSpec bwB = .ok SB := getOk_eq buildSpec_ok

/-- The executable before the compiler: the region's placeholder, the link map's symbols. -/
def file0 : ByteArray :=
  LeanLinkWitness.placeholder SB.R SB.size (SB.addrs.map fun p => (BinCheck.symName p.1, p.2))

theorem link_ok : (Link.leanLink SB file0).toBool = true := by native_decide

/-- The executable. -/
def file : ByteArray := getOk (Link.leanLink SB file0)

theorem link_eq : Link.leanLink SB file0 = .ok file := getOk_eq link_ok

theorem inScope : InScopeP SB.input = true := by native_decide

/-- **The baseline executable compiler compiles the bundle's `LinkSpec` to `file`.** -/
theorem compile_eq : Link.compileExe SB file0 = .ok file := by
  have h : InScopeP SB.input0 = true := by rw [← Link.LinkSpec.inScope_input]; exact inScope
  simp only [Link.compileExe, inScopePar_eq, h, ↓reduceIte, link_eq]

/-! ## The compiler's input: the facts of `Crates.CompileExeSourceWitness`, for `SB` -/

/-- The placed input. -/
abbrev J : LinkInput := SB.input

/-- The **source** `wmul_u128` (as parsed, with `i128` parameters and result). -/
def fs : Clif.Function := (J.srcProg.func? n).getD default

/-- The compiled function: its legalisation. -/
def f : Clif.Function := ((prog J).func? n).getD default

def bS : Clif.Block := fs.entry?.getD default
def bF : Clif.Block := f.entry?.getD default

/-- The body's stack pointer of the entry. -/
def sb : BitVec 64 := sp0 - BitVec.ofNat 64 (frameDrop (artOf J.results f).af)

/-- The caller's CLIF memory: no live allocation, the CLIF image's symbols, the slot-placement
oracle at the entry's body `sp`. -/
def cm : Clif.Mem :=
  { symbols := fun n => J.syms.lookup n, place := some ⟨[sb], (sys J helperBase).frames⟩ }

/-- The source entry state of `wmul_u128` on the two `i128` values (linked names). -/
def cs : Clif.State where
  frame := { func := fs, regs := (Clif.Regs.empty.setMany (bS.params.map (·.1)) args).getD default,
             slots := [], body := bS.body, term := bS.term }
  callers := []
  mem := cm

/-- The target entry state of the legalised `wmul_u128` on the split arguments. -/
def cs' : Clif.State where
  frame := { func := f, regs := (Clif.Regs.empty.setMany (bF.params.map (·.1)) args').getD default,
             slots := [], body := bF.body, term := bF.term }
  callers := []
  mem := cm

/-- The linked program's CLIF run from `cs`. -/
def run : Clif.Outcome := Clif.runLoop helperEnv J.srcProg M cs

/-- The machine state of the call with memory `m`: pc at `f`'s address, x30 the caller's return
address, `sp0`, the split arguments in x0–x3. -/
def r (m : Arm.Memory) : Arm.ArmState :=
  Arm.w .PC (artOf J.results f).base (Arm.w (.GPR 30#5) ra0 (Arm.w (.GPR 31#5) sp0
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

/-- The source run's call-depth bound (the peak theorem). -/
def d : Nat := 1

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
  LinkWitness.isRet run && decide (LinkWitness.retVals run = [⟨.i128, 5#64 ++ 15#64⟩]) &&
  (tabOf J.results).all (fun e => decide (e.2.base.toNat + 4 * e.2.fb.words.size + 4 ≤ 2 ^ 32)) &&
  StackBound.goodN J n && decide (StackBound.stackFn J (legalize fs) ≤ 2 ^ 20) &&
  (prog J).funcs.all (fun g => !Backend.hasTls g) &&
  (prog J).funcs.all (fun g => g.externs.all fun e =>
    ((prog J).func? e.2.name).isSome || !Clif.Rust.isDivHelper e.2.name) &&
  (prog J).funcs.all indFreeB && (prog J).funcs.all (fun g => (indSigs g).isEmpty) &&
  J.srcProg.funcs.all (fun g => g.slots.isEmpty) && SrcScopeB J &&
  Clif.depthB helperEnv J.srcProg d M cs &&
  decide (frameDrop (artOf J.results f).af + J.D * d ≤ 2 ^ 20)

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
    LinkWitness.isRet run = true ∧ LinkWitness.retVals run = [⟨.i128, 5#64 ++ 15#64⟩] ∧
    (tabOf J.results).all (fun e => decide (e.2.base.toNat + 4 * e.2.fb.words.size + 4 ≤ 2 ^ 32))
      = true ∧
    StackBound.goodN J n = true ∧ StackBound.stackFn J (legalize fs) ≤ 2 ^ 20 ∧
    (prog J).funcs.all (fun g => !Backend.hasTls g) = true ∧
    (prog J).funcs.all (fun g => g.externs.all fun e =>
      ((prog J).func? e.2.name).isSome || !Clif.Rust.isDivHelper e.2.name) = true ∧
    (prog J).funcs.all indFreeB = true ∧ (prog J).funcs.all (fun g => (indSigs g).isEmpty) = true ∧
    J.srcProg.funcs.all (fun g => g.slots.isEmpty) = true ∧ SrcScopeB J = true ∧
    Clif.depthB helperEnv J.srcProg d M cs = true ∧
    frameDrop (artOf J.results f).af + J.D * d ≤ 2 ^ 20 := by
  have h := factsB_true
  simp only [factsB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩,
    h12⟩, h13⟩, h14⟩, h15⟩, h16⟩, h17⟩, h18⟩, h19⟩, h20⟩, h21⟩, h22⟩, h23⟩, h24⟩, h25⟩, h26⟩,
    h27⟩, h28⟩, h29⟩, h30⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    h21, h22, h23, h24, h25, h26, h27, h28, h29, h30⟩

/-- `okB` of the placed input (by construction, `okB_leanLink`). -/
theorem okB_J : okB J = true := Link.okB_leanLink inScope link_eq

/-- No call cycle of the program's call graph is reachable from the entry. -/
theorem acyclic : ¬ StackBound.CycleFrom (StackBound.Calls J J.results) (legalize fs) := by
  obtain ⟨f', hf', hc⟩ :=
    (StackBound.goodN_iff okB_J).1 facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [facts.2.1] at hf'
  cases hf'
  rw [facts.2.2.1]
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

/-- The outside caller's contract for the legalised `wmul_u128` in `r m` (the split arguments in
x0–x3) with a stack of `N ≤ 2^20` bytes. -/
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

/-- The target entry for `compileExe_correct`. -/
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

/-- The linked program's CLIF run of `wmul_u128` returns `5 * 2^64 + 15`. -/
theorem run_eq : run = .returned [⟨.i128, 5#64 ++ 15#64⟩] (LinkWitness.retMem run) := by
  rw [← facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
  exact LinkWitness.eq_returned facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem cm_bounded : Opt.Legal.MemBounded cs.mem := fun _ _ h => by
  simp [cs, cm, Clif.Mem.valid] at h

/-- The linked program's run has call depth at most `d`. -/
theorem depth : Clif.DepthLe helperEnv J.srcProg d cs :=
  Clif.depthLe_of_depthB M cs facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem stack_le : frameDrop (art J (legalize fs)).af + J.D * d ≤ 2 ^ 20 := by
  rw [facts.2.2.1]; exact facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-! ## The bundle theorems on the pre-renaming program -/

/-- The premises both theorems share, from `facts` and the renaming. -/
theorem common {σ : Clif.Ren} (hσ : Front.link us (Front.finOf us) = (Front.link us sc).rename σ.fwd)
    (hσn : σ.fwd n = n) :
    f0.rename σ.fwd = fs ∧ f0.sig = fs.sig ∧
    BaseOk (sys J helperBase) ∧
    ((∃ g ∈ (prog J).funcs, ¬ Clif.IndFree g) → ∀ n, helperBase.env.sigOf n = none) ∧
    Opt.Legal.ExpRel ((Opt.Legal.groups f0.sig.params).getD []) args args' ∧
    ClifEntry f0 args (cs.ren σ.symm) ∧
    (∀ s', Opt.Legal.SReach (helperEnv.ren σ.symm) (Front.link us sc) (cs.ren σ.symm) s' →
      Opt.Legal.MemBounded s'.mem) ∧
    Clif.runLoop (helperEnv.ren σ.symm) (Front.link us sc) M (cs.ren σ.symm) =
      .returned [⟨.i128, 5#64 ++ 15#64⟩] ((LinkWitness.retMem run).ren σ.symm) := by
  obtain ⟨hf, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, htls, hdivB, hindB,
    hsigsB, hslotsB, hsrc, -⟩ := facts
  have hP : J.srcProg = (Front.link us sc).rename σ.fwd := srcProg_of buildSpec_eq husB hσ
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
  refine ⟨hfs, hsig0,
    Link.SourceWitness.baseOk_helper (fun g hg => by simpa using List.all_eq_true.mp htls g hg)
      hdiv hind (fun g hg => by simpa using List.all_eq_true.mp hsigsB g hg),
    fun ⟨g, hg, hn⟩ => absurd (hind g hg) hn, ?_, pre_entry hfs clifEntry,
    pre_bnd hP (Link.SourceWitness.srcBounded hsrc hslots (Clif.Program.func?_some hf).1
      clifEntry cm_bounded),
    pre_run hP run_eq⟩
  rw [hsig0, gp, Option.getD_some]
  exact ⟨⟨3#64, 1#64, rfl, rfl, rfl⟩, ⟨5#64, 0#64, rfl, rfl, rfl⟩, trivial⟩

/-- **Per-run non-vacuity of `Front.bundle_correct_source_baseline`** on the real codegen unit
of `g_u128`: the baseline compiler produces the executable `file` from the `LinkSpec` built from
the bundle; the linked program is the pre-renaming program renamed by a bijection `σ` moving
`wrapping_mul`'s CLIF name to its linked name; the pre-renaming program's CLIF run of
`wmul_u128` on `2^64 + 3` and `5` returns `5 * 2^64 + 15`; and, the outside code calling the
executable's compiled `wmul_u128` with the split arguments in x0–x3, the executable machine
returns to the caller with the split result `15, 5` in x0, x1. -/
theorem bundle_baseline_witness :
    Front.buildSpec bwB = .ok SB ∧ Link.compileExe SB file0 = .ok file ∧
    bwB.units.mapM Front.parseUnit = .ok us ∧ Front.ScopingOk us sc ∧
    (Front.link us sc).func? n = some f0 ∧ mentions128 f0 = true ∧
    ∃ σ : Clif.Ren,
      Front.link us (Front.finOf us) = (Front.link us sc).rename σ.fwd ∧
      σ.fwd mulClif = mulLinked ∧
      Clif.runLoop (helperEnv.ren σ.symm) (Front.link us sc) M (cs.ren σ.symm) =
        .returned [⟨.i128, 5#64 ++ 15#64⟩] ((LinkWitness.retMem run).ren σ.symm) ∧
      ∃ k, ArmRet ra0 (r (memOf file)) (runX (step J helperBase file) k (r (memOf file))) ∧
        XHolds ⟨.i64, 15#64⟩ (xreg 0 (runX (step J helperBase file) k (r (memOf file)))) ∧
        XHolds ⟨.i64, 5#64⟩ (xreg 1 (runX (step J helperBase file) k (r (memOf file)))) := by
  obtain ⟨σ, hσ, hσn, hσm⟩ := alpha
  obtain ⟨hfs, hsig0, hB, hsig, hexp, hcs0, hbnd, hrun0⟩ := common hσ hσn
  have hoc := outsideCall (memOf file) (BinCheck.roByte J SB.data)
    facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have H := Front.bundle_correct_source_baseline (r := r (memOf file)) (args := args)
    (args' := args') (cs := cs.ren σ.symm) (cs' := cs') buildSpec_eq compile_eq
    facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 husB hσ
    (helperEnv.ren σ.symm) helperBase (Front.Env.ren_symm_ren σ _).symm hB
    (Link.SourceWitness.hooksSim_helper _)
    (fun _ => ⟨Link.SourceWitness.helperOk, Link.SourceWitness.extLegal,
      Link.SourceWitness.keepsBounded⟩)
    hsig hf0 (by rw [hfs]; exact acyclic)
    (intact file) (by rw [hfs]; exact hoc) (by rw [hfs]; exact clifRun _)
    hcs0 hexp rfl (Front.Mem.ren_symm_ren σ cm).symm hbnd M
  have h := H.1 _ _ hrun0
  rw [hfs, hsig0, x30_r] at h
  obtain ⟨vals', hrel, k, hret, hx, -⟩ := h
  rw [gr, Option.getD_some] at hrel
  cases split_ret hrel
  exact ⟨buildSpec_eq, compile_eq, husB, sc_ok, hf0, f0_mentions, σ, hσ, hσm, hrun0, k, hret,
    hx 0 _ rfl, hx 1 _ rfl⟩

/-- **Per-run non-vacuity of `Front.bundle_correct_source_peak_baseline`**: as
`bundle_baseline_witness`, the call-depth premise instead of the call-graph one: the
pre-renaming program's CLIF run of `wmul_u128` has call depth at most `1`; the outside code
provides `frameDrop + D * 1` bytes of stack. -/
theorem bundle_baseline_peak_witness :
    Front.buildSpec bwB = .ok SB ∧ Link.compileExe SB file0 = .ok file ∧
    bwB.units.mapM Front.parseUnit = .ok us ∧ Front.ScopingOk us sc ∧
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
  obtain ⟨σ, hσ, hσn, hσm⟩ := alpha
  obtain ⟨hfs, hsig0, hB, hsig, hexp, hcs0, hbnd, hrun0⟩ := common hσ hσn
  have hP : J.srcProg = (Front.link us sc).rename σ.fwd := srcProg_of buildSpec_eq husB hσ
  have hd := pre_depth hP depth
  have hoc := outsideCall (memOf file) (BinCheck.roByte J SB.data) stack_le
  have H := Front.bundle_correct_source_peak_baseline (r := r (memOf file)) (args := args)
    (args' := args') (cs := cs.ren σ.symm) (cs' := cs') buildSpec_eq compile_eq
    facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 husB hσ
    (helperEnv.ren σ.symm) helperBase (Front.Env.ren_symm_ren σ _).symm hB
    (Link.SourceWitness.hooksSim_helper _)
    (fun _ => ⟨Link.SourceWitness.helperOk, Link.SourceWitness.extLegal,
      Link.SourceWitness.keepsBounded⟩)
    hsig hf0 d
    (intact file) (by rw [hfs]; exact hoc) (by rw [hfs]; exact clifRun _)
    hcs0 hexp rfl (Front.Mem.ren_symm_ren σ cm).symm hbnd hd M
  have h := H.1 _ _ hrun0
  rw [hfs, hsig0, x30_r] at h
  obtain ⟨vals', hrel, k, hret, hx, -⟩ := h
  rw [gr, Option.getD_some] at hrel
  cases split_ret hrel
  exact ⟨buildSpec_eq, compile_eq, husB, sc_ok, hf0, f0_mentions, σ, hσ, hσm, hd, hrun0, k, hret,
    hx 0 _ rfl, hx 1 _ rfl⟩

end Crates.FrontendBundleWitnessBaseline
