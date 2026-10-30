import FV.Concurrency.ArmAllocLoopMem
import FV.Concurrency.ArmAllocWitness

/-!
# Non-vacuity of layer 4b with the LL/SC loops (T2, #311)

* `loop_premises`: the compiled `args; movz; movz; atomic_rmw_loop; movz; atomic_cas_loop; rets`
  (`RLp`: a hand-written VCode `vcL` and allocation `rfL`, lowered, emitted and laid out by the
  compiler, loaded as `ArmAllocWitness.act` loads it) meets the premises of
  `arm_alloc_refines_loop`: `R.Wf`, `MemScopeL` (and not `MemScope`: the loops are not memory
  forms of `MemScope`), and `Q ∧ AInv` at `MConf.init` after the prologue (`Backend.Proof.q_init`).
  The loops' fixed registers x24–x28 are callee-saved, so the checker needs their entry values back
  at the return: `rfL` saves them at the entry and restores them before `rets` (`saved`, save
  moves, as `spillAlloc` does), so `RLp` has moves (`¬ NoMoves RLp`), which `arm_alloc_refines_loop`
  allows.
* `rmw_retry_w`, `cas_retry_w`: `rmw_retry`/`cas_retry` at `RLp`'s loops (labels `loop 0` at line
  8 and `loop 1` at line 14), from the state `RLp.s0` with the pc at the label (a head of its own
  loop); `retry_run_w`: `retry_run` on the `atomic_rmw` loop from there.

The layout facts (the label map is a hash map, which the kernel does not reduce) and the lines of
the loops are by `native_decide`.
-/

namespace Concurrency.ArmAllocThread.LoopWitness

open Arm ArmFoot ArmThread Backend Backend.Proof VCodeThread Witness

-- The lines' equality (for the layout facts `hd1`, `hdrop`).
deriving instance DecidableEq for Line

def flW : Clif.MemFlags := default

/-- `movz` of `k` into vreg `v`. -/
def mw (v k : Nat) : MInst := .movWide .movZ (.vreg v .int) ⟨k, 0⟩ .size64

/-- `args; v0 := 0x100; v1 := 1; atomic_rmw_loop add [v0] v1; v7 := 2;
atomic_cas_loop [v0] v1 v7; rets`. -/
def vcL : VCode :=
  { name := "l", blocks := #[{ label := 0, insts := #[.args [], mw 0 0x100, mw 1 1,
      .atomicRmwLoop (.int 64) .add flW (.vreg 0 .int) (.vreg 1 .int) (.vreg 2 .int) (.vreg 3 .int)
        (.vreg 4 .int),
      mw 7 2,
      .atomicCasLoop (.int 64) flW (.vreg 0 .int) (.vreg 1 .int) (.vreg 7 .int) (.vreg 5 .int)
        (.vreg 6 .int),
      .rets []] }], classes := #[],
    slotBytes := 0, outgoing := 0, rulesFired := #[] }

def xr (n : Nat) : Loc := .reg (.x n)

/-- The callee-saved registers the loops use. -/
def svd : List Nat := [24, 25, 26, 27, 28]

/-- The allocation: the loops' fixed registers, saved at the entry and restored before `rets`. -/
def rfL : RFunc :=
  { blocks := #[(svd.map fun n => RItem.move (xr n) (.save (.x n))).toArray ++
      #[.op 0 #[], .op 1 #[xr 25], .op 2 #[xr 26], .op 3 #[xr 25, xr 26, xr 27, xr 24, xr 28],
      .op 4 #[xr 28], .op 5 #[xr 25, xr 26, xr 28, xr 27, xr 24]] ++
      (svd.map fun n => RItem.move (.save (.x n)) (xr n)).toArray ++ #[.op 6 #[]]],
    spillSlots := 0, saved := svd.map .x }

abbrev RLp : RL := act vcL rfL

theorem wfL : RLp.Wf :=
  wf_of (VCodeThread.Witness.ok_of_isOkB () (by decide +kernel)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by native_decide) (by native_decide) (by native_decide)
    (by decide +kernel) (by native_decide) (by decide +kernel)

theorem szL : 4 * RLp.fb.words.size ≤ 0x10000 := by native_decide

theorem codeL : ∀ k < RLp.fb.words.size,
    Arm.read_mem_bytes 4 (0x10000#64 + BitVec.ofNat 64 (4 * k)) RLp.s0 = RLp.fb.words[k]! := by
  native_decide

theorem entryArgL : ∀ r, RLp.vc.EntryArg r → r.isArgReg = true := by
  intro r ⟨vb, ds, h1, h2, v, hv⟩
  simp only [RLp, act, vcL] at h1
  cases h1
  simp at h2
  subst h2
  simp at hv

/-- **`Q ∧ AInv` at the allocated code's entry configuration** after the prologue
(`Backend.Proof.q_init`), with the body-entry world `E2E.bodyOf`. -/
theorem qL : ∃ n, Q RLp (iterN RLp.step n RLp.s0)
      (MConf.init RLp.rf (locVal RLp.fr (iterN RLp.step n RLp.s0)) (E2E.bodyOf RLp.af RLp.s0)) ∧
    AInv RLp (MConf.init RLp.rf (locVal RLp.fr (iterN RLp.step n RLp.s0)) (E2E.bodyOf RLp.af RLp.s0)) := by
  obtain ⟨n, -, hq, hA, -⟩ := q_init wfL (abi_of szL codeL)
    ((E2E.Binary.bodyEntry_bodyOf RLp.af RLp.s0).w RLp.F entryArgL)
  exact ⟨n, hq, hA⟩

theorem mw_noEv (ctx : FnCtx) (v k : Nat) : NoEvForm ctx (mw v k) := .inl ⟨rfl, rfl, rfl⟩

theorem scopeL : MemScopeL RLp := by
  intro b vb k i hb hi
  rcases b with _ | b
  · simp only [RLp, act, vcL] at hb
    cases hb
    rcases k with _ | _ | _ | _ | _ | _ | _ | k
    · simp at hi; subst hi; exact .inl (.inl (.inr (.inl ⟨_, rfl⟩)))
    · simp at hi; subst hi; exact .inl (.inl (mw_noEv _ _ _))
    · simp at hi; subst hi; exact .inl (.inl (mw_noEv _ _ _))
    · simp at hi; subst hi; exact .inr (.inl ⟨_, _, _, _, _, _, _, _, rfl⟩)
    · simp at hi; subst hi; exact .inl (.inl (mw_noEv _ _ _))
    · simp at hi; subst hi; exact .inr (.inr ⟨_, _, _, _, _, _, _, rfl⟩)
    · simp at hi; subst hi; exact .inl (.inl (.inr (.inr (.inl ⟨_, rfl⟩))))
    · simp at hi
  · simp [RLp, act, vcL] at hb

/-- The `atomic_rmw` loop is outside `MemScope`. -/
theorem not_memScope : ¬ MemScope RLp := by
  intro h
  rcases h 0 _ 3 _ rfl rfl with
    (⟨h1, -, -⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩) | h | ⟨_, _, _, _, h, -⟩ | ⟨_, _, _, _, h, -⟩
  · exact absurd h1 (by decide)
  all_goals cases h

/-- `RLp` has moves (the saves and restores of x24–x28). -/
theorem not_noMoves : ¬ NoMoves RLp :=
  fun h => h 0 _ rfl (xr 24) (.save (.x 24)) (by decide)

/-- **Non-vacuity of `arm_alloc_refines_loop`**: the compiled function with an `atomic_rmw` and an
`atomic_cas` loop (`RLp`) satisfies its premises — `R.Wf`, the scope with LL/SC loops (beyond
`MemScope`), and `Q ∧ AInv` at `MConf.init` after the prologue; the theorem then applies to every
precise Arm run under `OkPriv` from there. -/
theorem loop_premises : RLp.Wf ∧ MemScopeL RLp ∧ ¬ MemScope RLp ∧
    ∃ n, Q RLp (iterN RLp.step n RLp.s0)
      (MConf.init RLp.rf (locVal RLp.fr (iterN RLp.step n RLp.s0)) (E2E.bodyOf RLp.af RLp.s0)) ∧
    AInv RLp (MConf.init RLp.rf (locVal RLp.fr (iterN RLp.step n RLp.s0)) (E2E.bodyOf RLp.af RLp.s0)) ∧
    ∀ (mon : Mon) (ls : List Lab) (t' : ArmState × Mon),
      PRun Policy.arm RLp.step (OkPriv RLp) (iterN RLp.step n RLp.s0, mon) ls t' →
      ∃ k trS cE ψ, k ≤ ls.length ∧ AllocThread.MTRun RLp.vc RLp.rf RLp.sem ckeep (cEvs RLp.F RLp.ctx)
        (MConf.init RLp.rf (locVal RLp.fr (iterN RLp.step n RLp.s0)) (E2E.bodyOf RLp.af RLp.s0)) trS cE ∧
        ThreadRefine.Refines (· = ·) (PrivA RLp) (MonPair (evTr (ls.take k))) (PrepThread.conv trS)
          (PrepThread.conv (evTr (ls.take k))) ψ ∧ (k = ls.length ∨ Done RLp cE) := by
  obtain ⟨n, hq, hA⟩ := qL
  exact ⟨wfL, scopeL, not_memScope, n, hq, hA, fun _ _ _ hr =>
    arm_alloc_refines_loop wfL scopeL hq hA hr⟩

/-! ## The retry loops -/

/-- `RLp.s0` with the pc at line `j`. -/
def sAt (j : Nat) : ArmState := Arm.w .PC (RLp.pcOf j) RLp.s0

theorem sAt_prog (j : Nat) : (sAt j).program = RLp.fb.program RLp.base := by
  rw [sAt, Arm.w_program]; exact entry_program _ _

theorem sAt_pc (j : Nat) : Arm.r .PC (sAt j) = RLp.pcOf j := by rw [sAt, Arm.r_of_w_same]

theorem sAt_err (j : Nat) : Arm.r .ERR (sAt j) = .None := by
  rw [sAt, Arm.r_of_w_different (by simp)]; exact (abi_of szL codeL).err

theorem hty64 : AtomTy (.int 64) := .inr (.inr (.inr rfl))

/-- **Non-vacuity of `rmw_retry`**: `RLp`'s `atomic_rmw` loop (label `loop 0` at line 8) is a retry
loop from `sAt 8`, which is a head of its own loop. -/
theorem rmw_retry_w :
    RetryLoop RLp.step (RmwHd (.int 64) .add (sAt 8)) (loopRd (.int 64) (sAt 8))
        ((rmwLoopMid .add 64).length + 1) 24#5 (fun _ => False) ∧
      RmwHd (.int 64) .add (sAt 8) (sAt 8) :=
  ⟨rmw_retry wfL hty64 (op := .add) (fl := flW) (j0 := 8) (n := 0) (T := RLp.L.drop 13)
    (by native_decide) (by native_decide) (sAt_prog 8) (sAt_pc 8) (sAt_err 8),
    loopInv_refl _ _ _ _⟩

/-- **Non-vacuity of `cas_retry`**: `RLp`'s `atomic_cas` loop (label `loop 1` at line 14) is a retry
loop from `sAt 14`, which is a head of its own loop. -/
theorem cas_retry_w :
    RetryLoop RLp.step (CasHd (.int 64) (sAt 14)) (loopRd (.int 64) (sAt 14)) 3 24#5
        (fun z => Arm.ConditionHolds Cond.ne.bits z = true) ∧
      CasHd (.int 64) (sAt 14) (sAt 14) :=
  ⟨cas_retry wfL hty64 (fl := flW) (j0 := 14) (n := 1) (X := RLp.L.drop 21)
    (by native_decide) (sAt_prog 14) (sAt_pc 14) (sAt_err 14),
    loopInv_refl _ _ _ _⟩

/-- **Non-vacuity of `retry_run`**: every precise run under `OkPriv` from the head `sAt 8` of
`RLp`'s `atomic_rmw` loop writes nothing or ends in a final iteration (`RetryOut`). -/
theorem retry_run_w (mon : Mon) (ls : List Lab) (t' : ArmState × Mon)
    (hr : PRun Policy.arm RLp.step (OkPriv RLp) (sAt 8, mon) ls t') :
    RetryOut Policy.arm RLp.step (OkPriv RLp) (RmwHd (.int 64) .add (sAt 8))
      (loopRd (.int 64) (sAt 8)) ((rmwLoopMid .add 64).length + 1) 24#5 (fun _ => False)
      (sAt 8, mon) ls :=
  retry_run rmw_retry_w.1 ls.length ls (sAt 8) mon t' (Nat.le_refl _) rmw_retry_w.2 hr

end Concurrency.ArmAllocThread.LoopWitness
