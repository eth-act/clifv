import Crates.CompileExeRecWitness

/-! # Per-run non-vacuity of the peak-call-depth theorem for recursive programs (L1d)

`Link.compileExe_correct_peak` on the executable of `Crates.CompileExeRecWitness` (`compileExe`
on the natively self-recursive `direct`): outside code calls `direct(3)` with the stack pointer
`spT`, which leaves room for `frameDrop + D * 3` bytes above the program's code. The CLIF run's
peak call depth is `3` (`facts`: no state of the run has more than three callers, four
activations of `direct`), so every premise of `compileExe_correct_peak` holds, and the theorem
gives the executable machine (the processor on `file`'s own words) returning to the caller with
`6` in x0 (`compileExe_peak_witness`).

The fuel-indexed `Link.compileExe_correct_depth` does not cover this call
(`depth_premise_fails`): the run does not return within `M0` steps, so its conclusion is about a
run out of fuel below `M0 + 1` steps, and for every fuel `M ≥ M0` its stack premise
`frameDrop + D * M` exceeds the stack below `spT`.
-/

namespace Crates.CompileExePeakWitness

open E2E E2E.LinkCheck E2E.Binary E2E.ExecBytes Backend Backend.Proof Link
open Crates.BinaryWitness (memOf)
open Crates.CompileExeRecWitness (spec file0 file J n f bF args M ra0 r)

/-- The run's peak call depth: at most three callers below the running activation. -/
def d : Nat := 3

/-- The caller's stack pointer: exactly `frameDrop + D * d = 288 + 288 * 3` bytes below it,
all below the program's code (at 16 MiB). -/
def spT : BitVec 64 := 0x480

/-- The fuel below which the CLIF run does not return (it returns within `24` steps). -/
def M0 : Nat := 23

/-- The body's stack pointer of the entry. -/
def sbT : BitVec 64 := spT - BitVec.ofNat 64 (frameDrop (artOf J.results f).af)

/-- The caller's CLIF memory: no live allocation, the CLIF image's symbols, the slot-placement
oracle at the entry's body `sp`. -/
def cmT : Clif.Mem :=
  { symbols := fun n => J.syms.lookup n, place := some ⟨[sbT], (sys J closedBase).frames⟩ }

/-- The reference CLIF entry state of `direct` on `3`. -/
def csT : Clif.State where
  frame := CompileExeRecWitness.cs.frame
  callers := []
  mem := cmT

/-- The program's CLIF run from `csT`. -/
def runT : Clif.Outcome := Clif.runLoop closedBase.env (progOf J.results) (M + 1) csT

def oofB : Clif.Outcome → Bool
  | .outOfFuel => true
  | _ => false

/-- The facts of the run and of the layout, decided. -/
def factsB : Bool :=
  LinkWitness.isRet runT && decide (LinkWitness.retVals runT = [⟨.i64, 6#64⟩]) &&
  Clif.depthB closedBase.env (progOf J.results) d (M + 1) csT &&
  oofB (Clif.runLoop closedBase.env (progOf J.results) M0 csT) &&
  decide (frameDrop (artOf J.results f).af + J.D * d ≤ spT.toNat) &&
  decide (spT.toNat % 16 = 0) &&
  decide (spT.toNat < frameDrop (artOf J.results f).af + J.D * M0) &&
  (tabOf J.results).all (fun e => decide (spT.toNat ≤ e.2.base.toNat))

theorem factsB_true : factsB = true := by native_decide

theorem facts :
    LinkWitness.isRet runT = true ∧ LinkWitness.retVals runT = [⟨.i64, 6#64⟩] ∧
    Clif.depthB closedBase.env (progOf J.results) d (M + 1) csT = true ∧
    oofB (Clif.runLoop closedBase.env (progOf J.results) M0 csT) = true ∧
    frameDrop (artOf J.results f).af + J.D * d ≤ spT.toNat ∧ spT.toNat % 16 = 0 ∧
    spT.toNat < frameDrop (artOf J.results f).af + J.D * M0 ∧
    (tabOf J.results).all (fun e => decide (spT.toNat ≤ e.2.base.toNat)) = true := by
  have h := factsB_true
  simp only [factsB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- Every code address of the program is at or above `spT`. -/
theorem img_ge {x : BitVec 64} (h : img J x) : spT.toNat ≤ x.toNat := by
  obtain ⟨e, he, p, hp, hx⟩ := h
  have hb : spT.toNat ≤ e.2.base.toNat := by
    have := List.all_eq_true.mp facts.2.2.2.2.2.2.2 e he
    simpa using this
  have hb' : e.2.base.toNat + 4 * e.2.fb.words.size + 4 ≤ 2 ^ 32 := by
    have := List.all_eq_true.mp CompileExeRecWitness.facts.2.2.2.2.2.2.2.2.2.1 e he
    simpa using this
  obtain ⟨j, hj, e'⟩ := LinkWitness.wordsAt_mem_inv (k := 0) hp
  simp only [Array.length_toList] at hj
  rw [e', BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat] at hx
  have := e.2.base.isLt
  have := x.isLt
  rw [Nat.mod_eq_of_lt (by omega : 4 * (0 + j) < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : e.2.base.toNat + 4 * (0 + j) < 2 ^ 64)] at hx
  omega

/-- The outside caller's contract holds in `r spT m` with a stack of `N ≤ spT` bytes. -/
theorem outsideCall (m : Arm.Memory) (roB : BitVec 64 → Option (BitVec 8)) {N : Nat}
    (hN : N ≤ spT.toNat) : OutsideCall J roB f N (r spT m) args csT.mem where
  pc := CompileExeRecWitness.pc_r spT m
  err := CompileExeRecWitness.err_r spT m
  ra := fun h => by
    have := CompileExeRecWitness.img_lt h
    rw [CompileExeRecWitness.x30_r] at this; simp [ra0] at this
  spAligned := by rw [CompileExeRecWitness.spv_r]; exact facts.2.2.2.2.2.1
  stack := by rw [CompileExeRecWitness.spv_r]; exact hN
  stackFree := fun a ha hb => by
    have := img_ge ha
    rw [CompileExeRecWitness.spv_r] at hb
    obtain ⟨h1, -⟩ := hb
    omega
  args := fun loc v hm => by
    rw [CompileExeRecWitness.locs] at hm
    simp only [args, List.zip_cons_cons, List.zip_nil_right, List.mem_cons, Prod.mk.injEq,
      List.not_mem_nil, or_false] at hm
    obtain ⟨rfl, rfl⟩ := hm
    simp only [VHolds, regVal, CompileExeRecWitness.x0_r spT m]; rfl
  bytes := fun _ _ hv => by simp [csT, cmT, Clif.Mem.valid] at hv
  image := fun _ _ _ hv => by simp [csT, cmT, Clif.Mem.valid] at hv
  valid := fun _ _ hv => by simp [csT, cmT, Clif.Mem.valid] at hv
  symbols := rfl

theorem clifEntry : ClifEntry f args csT :=
  have h := CompileExeRecWitness.clifEntry
  ⟨rfl, h.func, h.sig, h.entry, h.slotIds⟩

/-- The reference CLIF run. -/
theorem clifRun (m : Arm.Memory) : ClifRun J closedBase f (r spT m) args csT where
  entry := clifEntry
  slots := fun _ _ h => by simp [csT, CompileExeRecWitness.cs] at h
  place := fun _ => ⟨[], by
    show some _ = some _
    rw [show spBody (art J f).af (r spT m) = sbT by
      simp only [spBody, CompileExeRecWitness.spv_r, sbT]]⟩

/-- The machine's memory is the loaded image of any file. -/
theorem intact (file : ByteArray) : (imageOf file).Intact (r spT (memOf file)) :=
  fun a b _ hb => by
    simp only [r, LinkWitness.mem_w, mem_setMem, memOf]
    exact (congrArg (Option.getD · 0) hb).trans rfl

/-- The program's CLIF run returns `6`. -/
theorem run_eq : runT = .returned [⟨.i64, 6#64⟩] (LinkWitness.retMem runT) := by
  rw [← facts.2.1]
  exact LinkWitness.eq_returned facts.1

/-- The run's call depth is at most `d`. -/
theorem depth : Clif.DepthLe closedBase.env (prog J) d csT :=
  Clif.depthLe_of_depthB (M + 1) csT facts.2.2.1

/-- **Per-run non-vacuity of `Link.compileExe_correct_peak`** on the recursive `direct`:
`compileExe` produces the executable `file`; the entry reaches a call cycle (so
`compileExe_correct` does not apply); in the machine state whose memory is `file`'s loaded image,
with the stack pointer `spT`, in which outside code calls `direct` with `3`, every premise of
`compileExe_correct_peak` holds for the peak call depth `d = 3` — the closed base environment
(`BaseOk`, `HooksSim`), the loader's image (`Intact`), the boundary contract (`OutsideCall` with
`frameDrop + D * 3` bytes of stack), the reference CLIF run (which returns `6`), its call depth
(`Clif.DepthLe`), `TrapsExplicit` — and the theorem gives the executable machine returning to the
caller with `6` in x0. -/
theorem compileExe_peak_witness :
    compileExe spec file0 = .ok file ∧
    StackBound.CycleFrom (StackBound.Calls J J.results) f ∧
    Clif.DepthLe closedBase.env (prog J) d csT ∧
    OutsideCall J (BinCheck.roByte J spec.data) f (frameDrop (art J f).af + J.D * d)
      (r spT (memOf file)) args csT.mem ∧
    ClifRun J closedBase f (r spT (memOf file)) args csT ∧
    TrapsExplicit (Clif.linkEnvD (prog J) closedBase.env M d) (prog J).bare csT ∧
    Clif.runLoop closedBase.env (prog J) (M + 1) csT =
      .returned [⟨.i64, 6#64⟩] (LinkWitness.retMem runT) ∧
    ∃ k, ArmRet ra0 (r spT (memOf file)) (runX (step J closedBase file) k (r spT (memOf file))) ∧
      XHolds ⟨.i64, 6#64⟩ (xreg 0 (runX (step J closedBase file) k (r spT (memOf file)))) := by
  have hf := CompileExeRecWitness.facts.1
  have hfm := (Clif.Program.func?_some hf).1
  have hB := CompileExeRecWitness.base_closed fun _ => False
  have hX := intact file
  have hoc := outsideCall (memOf file) (BinCheck.roByte J spec.data) facts.2.2.2.2.1
  have hL := okB_sound CompileExeRecWitness.okB_J (CompileExeRecWitness.base_closed (img J))
    (fun _ h => h)
  have htr := trapsExplicit_of_runD hL hfm clifEntry rfl depth run_eq
  have h := compileExe_correct_peak CompileExeRecWitness.compile_eq closedBase hB
    (hooksSim_closed J) hf M d hX hoc (clifRun _) depth htr
  rw [show Clif.runLoop closedBase.env (prog J) (M + 1) csT = runT from rfl, run_eq,
    CompileExeRecWitness.x30_r] at h
  obtain ⟨k, hret, hx, -⟩ := h
  exact ⟨CompileExeRecWitness.compile_eq, CompileExeRecWitness.cyclic, depth, hoc, clifRun _, htr,
    run_eq, k, hret, hx 0 _ rfl⟩

/-- **The fuel-indexed theorem does not cover this call**: the CLIF run does not return within
`M0` steps (so `Link.compileExe_correct_depth` at a fuel `M` with `M + 1 ≤ M0` is about a run out
of fuel), and for every fuel `M` at which the run ends, the stack premise
`frameDrop + D * M` of `compileExe_correct_depth` fails in the same machine state (`M ≥ M0`, and
`spT < frameDrop + D * M0`), while `frameDrop + D * d` holds (`compileExe_peak_witness`). -/
theorem depth_premise_fails :
    Clif.runLoop closedBase.env (prog J) M0 csT = .outOfFuel ∧
    ∀ M', Clif.runLoop closedBase.env (prog J) (M' + 1) csT ≠ .outOfFuel →
      ∀ (m : Arm.Memory) (roB : BitVec 64 → Option (BitVec 8)),
        ¬ OutsideCall J roB f (frameDrop (art J f).af + J.D * M') (r spT m) args csT.mem := by
  have h0 : Clif.runLoop closedBase.env (prog J) M0 csT = .outOfFuel := by
    have := facts.2.2.2.1
    revert this
    cases Clif.runLoop closedBase.env (prog J) M0 csT <;> simp [oofB]
  refine ⟨h0, fun M' hM' m roB ho => ?_⟩
  have hge : M0 ≤ M' := by
    refine Nat.le_of_not_lt fun hlt => hM' ?_
    have := Clif.runLoop_add closedBase.env (prog J) (M' + 1) csT hM' (M0 - (M' + 1))
    rw [show M' + 1 + (M0 - (M' + 1)) = M0 by omega, h0] at this
    exact this.symm
  have hs := ho.stack
  rw [CompileExeRecWitness.spv_r] at hs
  have hlt : spT.toNat < frameDrop (art J f).af + J.D * M0 := facts.2.2.2.2.2.2.1
  have : J.D * M0 ≤ J.D * M' := Nat.mul_le_mul_left _ hge
  omega

end Crates.CompileExePeakWitness
