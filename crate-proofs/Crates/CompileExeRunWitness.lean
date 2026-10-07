import Crates.BinaryWitness
import Crates.LeanLinkWitness
import FV.Link.Exe

/-! # Per-run non-vacuity of the executable compiler's theorem (L1)

`Link.compileExe` compiles the panic=abort build of `a_arith` (`Crates.AArithAbort.input`, its 58
functions placed at 16 MiB, the placeholder executable `file0` of `Crates.LeanLinkWitness`):
`compile_eq`. On the executable it produces (`file`), outside code calls the Lean-compiled
`core::num::<i32>::wrapping_add` (`Crates.BinaryWitness.f`) with `2` and `3`, with the file's
loaded image as the machine's memory: every premise of `Link.compileExe_correct` holds together —
the closed base environment (`BaseOk`, `HooksSim`), no call cycle reachable from the entry, the
loader's image (`Intact`), the boundary contract (`OutsideCall`), the reference CLIF run (which
returns `5`), `TrapsExplicit` — and the theorem gives the **executable machine's** return (the
processor on `file`'s own words) to the caller with `5` in x0 (`compileExe_run_witness`).
-/

namespace Crates.CompileExeRunWitness

open E2E E2E.LinkCheck E2E.Binary E2E.ExecBytes Backend Backend.Proof Link
open Crates.BinaryWitness (n f bF args M sp0 ra0 memOf sp0_toNat)

/-- `a_arith`'s panic=abort program for the executable compiler: its functions placed at 16 MiB
with their compiled sizes, the other names at rust-lld's addresses. -/
def spec : LinkSpec :=
  let I := Crates.AArithAbort.input
  let names := I.funcs.map (·.func.name)
  { funcs := I.funcs, names,
    sizes := I.funcs.map fun fi => (getOk (pipeT fi.func fi.k 0 (raJ fi.ra fi.j))).fb.words.size,
    outside := I.addrs.filter (fun p => !names.contains p.1),
    symNames := I.syms.map (·.1), R := 0x1000000 }

/-- The executable before the compiler: the region's placeholder, the link map's symbols. -/
def file0 : ByteArray :=
  LeanLinkWitness.placeholder spec.R spec.size
    (spec.addrs.map fun p => (BinCheck.symName p.1, p.2))

theorem link_ok : (leanLink spec file0).toBool = true := by native_decide

/-- The executable. -/
def file : ByteArray := getOk (leanLink spec file0)

theorem link_eq : leanLink spec file0 = .ok file := E2E.LinkCheck.getOk_eq link_ok

theorem inScope : InScopeP spec.input = true := by native_decide

/-- **The executable compiler compiles `a_arith` (panic=abort) to `file`.** -/
theorem compile_eq : compileExe spec file0 = .ok file := by
  have h : InScopeP spec.input0 = true := by rw [← LinkSpec.inScope_input]; exact inScope
  simp only [compileExe, inScopePar_eq, h, ↓reduceIte, link_eq]

/-- The placed input. -/
abbrev J : LinkInput := spec.input

/-! ## The outside call of `wrapping_add` with `2` and `3` -/

/-- The body's stack pointer of the entry. -/
def sb : BitVec 64 := sp0 - BitVec.ofNat 64 (frameDrop (artOf J.results f).af)

/-- The caller's CLIF memory: no live allocation, the CLIF image's symbols, the slot-placement
oracle at the entry's body `sp`. -/
def cm : Clif.Mem :=
  { symbols := fun n => J.syms.lookup n, place := some ⟨[sb], (sys J closedBase).frames⟩ }

/-- The reference CLIF entry state of `f` on `2, 3`. -/
def cs : Clif.State where
  frame := { func := f, regs := (Clif.Regs.empty.setMany (bF.params.map (·.1)) args).getD default,
             slots := [], body := bF.body, term := bF.term }
  callers := []
  mem := cm

/-- The program's CLIF run from `cs`. -/
def run : Clif.Outcome := Clif.runLoop closedBase.env (progOf J.results) (M + 1) cs

/-- The machine state of the call with memory `m`: pc at `f`'s address, x30 the caller's return
address, `sp0`, the arguments in x0 and x1. -/
def r (m : Arm.Memory) : Arm.ArmState :=
  Arm.w .PC (artOf J.results f).base (Arm.w (.GPR 30#5) ra0 (Arm.w (.GPR 31#5) sp0
    (Arm.w (.GPR 0#5) 2#64 (Arm.w (.GPR 1#5) 3#64 (setMem Arm.ArmState.default m)))))

/-- The facts of the placed program decided on its compiled code. -/
def factsB : Bool :=
  decide ((progOf J.results).func? n = some f) &&
  LinkWitness.isRet run && decide (LinkWitness.retVals run = [⟨.i32, 5#32⟩]) &&
  (tabOf J.results).all (fun e => decide (e.2.base.toNat + 4 * e.2.fb.words.size + 4 ≤ 2 ^ 32)) &&
  decide (StackBound.stackFn J f ≤ 2 ^ 20) &&
  (progOf J.results).funcs.all (fun g => !Backend.hasTls g)

theorem factsB_true : factsB = true := by native_decide

theorem facts :
    (progOf J.results).func? n = some f ∧
    LinkWitness.isRet run = true ∧ LinkWitness.retVals run = [⟨.i32, 5#32⟩] ∧
    (tabOf J.results).all (fun e => decide (e.2.base.toNat + 4 * e.2.fb.words.size + 4 ≤ 2 ^ 32))
      = true ∧
    StackBound.stackFn J f ≤ 2 ^ 20 ∧
    (progOf J.results).funcs.all (fun g => !Backend.hasTls g) = true := by
  have h := factsB_true
  simp only [factsB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- `okB` of the placed input (by construction, `okB_leanLink`). -/
theorem okB_J : okB J = true := okB_leanLink inScope link_eq

/-- The closed base environment's premises. -/
theorem base_closed (F : BitVec 64 → Prop) : BaseOk (LinkSys.ofInput J closedBase F) :=
  baseOk_closed fun g hg => by simpa using List.all_eq_true.1 facts.2.2.2.2.2 g hg

/-- No call cycle of the program's call graph is reachable from the entry. -/
theorem acyclic : ¬ StackBound.CycleFrom (StackBound.Calls J J.results) f := by
  have hg : StackBound.goodN J n = true := by native_decide
  obtain ⟨f', hf', hc⟩ := (StackBound.goodN_iff okB_J).1 hg
  rw [facts.1] at hf'
  cases hf'
  exact hc

/-- Every code address of the program is below `2^32`. -/
theorem img_lt {x : BitVec 64} (h : img J x) : x.toNat < 2 ^ 32 := by
  obtain ⟨e, he, p, hp, hx⟩ := h
  have hb' : e.2.base.toNat + 4 * e.2.fb.words.size + 4 ≤ 2 ^ 32 := by
    have := List.all_eq_true.mp facts.2.2.2.1 e he
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
    Arm.r_of_w_different (by decide), r_setMem]
  simp [Arm.r, Arm.read_base_error, Arm.ArmState.default]

theorem x0_r : Arm.r (.GPR (rnum 0)) (r m) = 2#64 := by
  simp only [r, rnum]
  rw [Arm.r_of_w_different (by decide), Arm.r_of_w_different (by decide),
    Arm.r_of_w_different (by decide), Arm.r_of_w_same]

theorem x1_r : Arm.r (.GPR (rnum 1)) (r m) = 3#64 := by
  simp only [r, rnum]
  rw [Arm.r_of_w_different (by decide), Arm.r_of_w_different (by decide),
    Arm.r_of_w_different (by decide), Arm.r_of_w_different (by decide), Arm.r_of_w_same]

/-- The outside caller's contract holds in `r m` with a stack of `N ≤ 2^20` bytes. -/
theorem outsideCall (roB : BitVec 64 → Option (BitVec 8)) {N : Nat} (hN : N ≤ 2 ^ 20) :
    OutsideCall J roB f N (r m) args cs.mem where
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
    rw [BinaryWitness.locs] at hm
    simp only [args, List.zip_cons_cons, List.zip_nil_right, List.mem_cons, Prod.mk.injEq,
      List.not_mem_nil, or_false] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp only [VHolds, regVal, x0_r m]; rfl
    · simp only [VHolds, regVal, x1_r m]; rfl
  bytes := fun _ _ hv => by simp [cs, cm, Clif.Mem.valid] at hv
  image := fun _ _ _ hv => by simp [cs, cm, Clif.Mem.valid] at hv
  valid := fun _ _ hv => by simp [cs, cm, Clif.Mem.valid] at hv
  symbols := rfl

omit m in
theorem clifEntry : ClifEntry f args cs := by
  obtain ⟨-, hb, hsig, hpar, hset, hsl, -⟩ := BinaryWitness.facts
  refine ⟨rfl, rfl, hsig, ⟨bF, hb, rfl, rfl, hpar, ?_⟩, by simp [cs, hsl]⟩
  show _ = some ((Clif.Regs.empty.setMany (bF.params.map (·.1)) args).getD default)
  revert hset
  cases Clif.Regs.empty.setMany (bF.params.map (·.1)) args <;> simp

/-- The reference CLIF run. -/
theorem clifRun : ClifRun J closedBase f (r m) args cs where
  entry := clifEntry
  slots := fun _ _ h => by simp [cs] at h
  place := fun _ => ⟨[], by
    show some _ = some _
    rw [show spBody (art J f).af (r m) = sb by simp only [spBody, spv_r, sb]]⟩

end State

/-- The machine's memory is the loaded image of any file. -/
theorem intact (file : ByteArray) : (imageOf file).Intact (r (memOf file)) := fun a b _ hb => by
  simp only [r, LinkWitness.mem_w, mem_setMem, memOf]
  exact (congrArg (Option.getD · 0) hb).trans rfl

/-- The program's CLIF run returns `5`. -/
theorem run_eq : run = .returned [⟨.i32, 5#32⟩] (LinkWitness.retMem run) := by
  rw [← facts.2.2.1]
  exact LinkWitness.eq_returned facts.2.1

/-- **Per-run non-vacuity of `Link.compileExe_correct`** on `a_arith` (panic=abort):
`compileExe` produces the executable `file`; in the machine state whose memory is `file`'s loaded
image and in which outside code calls its Lean-compiled `core::num::<i32>::wrapping_add` with `2`
and `3`, every premise of `compileExe_correct` holds — the closed base environment (`BaseOk`,
`HooksSim`), the entry with no reachable call cycle, the loader's image (`Intact`), the boundary
contract (`OutsideCall`, `stackFn` bytes of stack), the reference CLIF run (which returns `5`),
`TrapsExplicit` — and the theorem gives the executable machine (`step`: the processor on
`file`'s own words) returning to the caller with `5` in x0. -/
theorem compileExe_run_witness :
    compileExe spec file0 = .ok file ∧
    BaseOk (sys J closedBase) ∧ HooksSim J closedBase ∧
    (prog J).func? n = some f ∧ ¬ StackBound.CycleFrom (StackBound.Calls J J.results) f ∧
    (imageOf file).Intact (r (memOf file)) ∧
    OutsideCall J (BinCheck.roByte J spec.data) f (StackBound.stackFn J f) (r (memOf file))
      args cs.mem ∧
    ClifRun J closedBase f (r (memOf file)) args cs ∧
    TrapsExplicit (Clif.linkEnvN (prog J) closedBase.env M) ((prog J).only f) cs ∧
    Clif.runLoop closedBase.env (prog J) (M + 1) cs =
      .returned [⟨.i32, 5#32⟩] (LinkWitness.retMem run) ∧
    ∃ k, ArmRet ra0 (r (memOf file)) (runX (step J closedBase file) k (r (memOf file))) ∧
      XHolds ⟨.i32, 5#32⟩ (xreg 0 (runX (step J closedBase file) k (r (memOf file)))) := by
  have hf := facts.1
  have hfm := (Clif.Program.func?_some hf).1
  have hB := base_closed fun _ => False
  have hX : (imageOf file).Intact (r (memOf file)) := intact file
  have hoc := outsideCall (memOf file) (BinCheck.roByte J spec.data) facts.2.2.2.2.1
  have hL := okB_sound okB_J (base_closed (img J)) (fun _ h => h)
  have htr := trapsExplicit_of_run hL hfm clifEntry rfl run_eq
  have h := compileExe_correct compile_eq closedBase hB (hooksSim_closed J) hf acyclic M hX hoc
    (clifRun _) htr
  rw [show Clif.runLoop closedBase.env (prog J) (M + 1) cs = run from rfl, run_eq, x30_r] at h
  obtain ⟨k, hret, hx, -⟩ := h
  exact ⟨compile_eq, hB, hooksSim_closed J, hf, acyclic, hX, hoc, clifRun _, htr, run_eq, k, hret,
    hx 0 _ rfl⟩

end Crates.CompileExeRunWitness
