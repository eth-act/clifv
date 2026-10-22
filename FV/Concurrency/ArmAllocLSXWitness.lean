import FV.Concurrency.ArmAllocLSX
import FV.Concurrency.ArmAllocLSWitness

/-!
# Non-vacuity of layer 4b with the stack offsets built in `x16` (T2j, #473)

* `lsx_premises`: the function `args; v0 := ldr [sp, #0x10000]; str v0, [sp, #0x10008];
  d1 := ldr [sp, #0x10010]; str d1, [sp, #0x10018]; rets` (`RX`: a hand-written VCode `vcX` and
  allocation `rfX`, lowered, emitted and laid out by the compiler, loaded as
  `ArmAllocWitness.act` loads it, as `ArmAllocLSWitness.ls_premises`) meets the premises of
  `arm_alloc_refines_lsx` — `R.Wf` and `MemScopeLSX` — and is outside `MemScopeLS` (**strict
  widening**: its offsets fit no immediate, so `memFinalize` builds them in `x16` with
  `loadConst64`). Its four accesses are a GPR and a SIMD&FP load and store.
* `lsx_run`: with `Q ∧ AInv` at `MConf.init` after the prologue (`Backend.Proof.q_init`), the
  theorem applies to every precise Arm run under `OkPriv` from there.

The layout facts (the label map is a hash map, which the kernel does not reduce) are by
`native_decide`.
-/

namespace Concurrency.ArmAllocThread.LSXWitness

open Arm ArmFoot ArmThread Backend Backend.Proof VCodeThread Witness LSWitness

def vcX : VCode :=
  { name := "x", blocks := #[{ label := 0, insts := #[.args [],
      .load .uload64 (.vreg 0 .int) (.spOffset 0x10000) flS,
      .store .store64 (.vreg 0 .int) (.spOffset 0x10008) flS,
      .fpuLoad .size64 (.vreg 1 .float) (.spOffset 0x10010) flS,
      .fpuStore .size64 (.vreg 1 .float) (.spOffset 0x10018) flS,
      .rets []] }], classes := #[],
    slotBytes := 0, outgoing := 0, rulesFired := #[] }

def rfX : RFunc :=
  { blocks := #[#[.op 0 #[], .op 1 #[xr 9], .op 2 #[xr 9], .op 3 #[vr 1], .op 4 #[vr 1],
      .op 5 #[]]],
    spillSlots := 0, saved := [] }

abbrev RX : RL := act vcX rfX

theorem wfX : RX.Wf :=
  wf_of (VCodeThread.Witness.ok_of_isOkB () (by decide +kernel)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by native_decide) (by native_decide) (by native_decide)
    (by decide +kernel) (by native_decide) (by decide +kernel)

theorem szX : 4 * RX.fb.words.size ≤ 0x10000 := by native_decide

theorem codeX : ∀ k < RX.fb.words.size,
    Arm.read_mem_bytes 4 (0x10000#64 + BitVec.ofNat 64 (4 * k)) RX.s0 = RX.fb.words[k]! := by
  native_decide

theorem entryArgX : ∀ r, RX.vc.EntryArg r → r.isArgReg = true := by
  intro r ⟨vb, ds, h1, h2, v, hv⟩
  simp only [RX, act, vcX] at h1
  cases h1
  simp at h2
  subst h2
  simp at hv

/-- `memFinalize` builds the offsets in `x16`. -/
theorem finX (o : Int) (n : Nat) (h9 : simm9? o = none) (hu : uimm12Scaled? o n = none) :
    memFinalize RX.ctx (.spOffset o) n =
      .ok (loadConst64 (.x 16) (u64 o), .regExtended .sp (.x 16) .sxtx) := by
  simp [memFinalize, h9, hu, pure, Except.pure]

theorem scopeX : MemScopeLSX RX := by
  intro b vb k i hb hi
  rcases b with _ | b
  · simp only [RX, act, vcX] at hb
    cases hb
    rcases k with _ | _ | _ | _ | _ | _ | k
    · simp at hi; subst hi; exact .inl (.inl (.inl (.inr (.inl ⟨_, rfl⟩))))
    · simp at hi; subst hi
      exact .inr (.inr ⟨by decide, .inr ⟨.inr (.inl ⟨_, rfl⟩), _, _, finX _ _ (by decide) (by decide)⟩⟩)
    · simp at hi; subst hi
      exact .inr (.inr ⟨by decide, .inr ⟨.inr (.inl ⟨_, rfl⟩), _, _, finX _ _ (by decide) (by decide)⟩⟩)
    · simp at hi; subst hi
      exact .inr (.inr ⟨by decide, .inr ⟨.inr (.inl ⟨_, rfl⟩), _, _, finX _ _ (by decide) (by decide)⟩⟩)
    · simp at hi; subst hi
      exact .inr (.inr ⟨by decide, .inr ⟨.inr (.inl ⟨_, rfl⟩), _, _, finX _ _ (by decide) (by decide)⟩⟩)
    · simp at hi; subst hi; exact .inl (.inl (.inl (.inr (.inr (.inl ⟨_, rfl⟩)))))
    · simp at hi
  · simp [RX, act, vcX] at hb

/-- The load at `[sp, #0x10000]` is outside `MemScopeLS` (its offset is built in `x16`). -/
theorem not_memScopeLS : ¬ MemScopeLS RX := by
  intro h
  rcases h 0 _ 1 _ rfl rfl with
    (((⟨-, -, h1⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩) | h | ⟨_, _, _, _, h, -⟩ | ⟨_, _, _, _, h, -⟩) |
      ⟨_, _, _, _, _, _, _, _, h⟩ | ⟨_, _, _, _, _, _, _, h⟩) |
      (⟨_, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, _, _, h⟩) | ⟨-, hm⟩
  · exact absurd h1 (by decide)
  all_goals try cases h
  rcases hm with hm | ⟨-, m', hf⟩
  · cases hm
  · rw [finX 0x10000 LoadOp.uload64.bytes (by decide) (by decide), loadConst64_eq] at hf
    simp at hf

/-- **Non-vacuity and strict widening of `arm_alloc_refines_lsx`**: the compiled function with
GPR and SIMD&FP loads and stores at stack offsets built in `x16` (`RX`) satisfies `R.Wf` and
`MemScopeLSX`, and is outside `MemScopeLS`. -/
theorem lsx_premises : RX.Wf ∧ MemScopeLSX RX ∧ ¬ MemScopeLS RX :=
  ⟨wfX, scopeX, not_memScopeLS⟩

/-- **`Q ∧ AInv` at the allocated code's entry configuration** after the prologue
(`Backend.Proof.q_init`), with the body-entry world `E2E.bodyOf`, and `arm_alloc_refines_lsx` for
every precise Arm run under `OkPriv` from there. -/
theorem lsx_run : ∃ n, Q RX (iterN RX.step n RX.s0)
      (MConf.init RX.rf (locVal RX.fr (iterN RX.step n RX.s0)) (E2E.bodyOf RX.af RX.s0)) ∧
    AInv RX (MConf.init RX.rf (locVal RX.fr (iterN RX.step n RX.s0)) (E2E.bodyOf RX.af RX.s0)) ∧
    ∀ (mon : Mon) (ls : List Lab) (t' : ArmState × Mon),
      PRun Policy.arm RX.step (OkPriv RX) (iterN RX.step n RX.s0, mon) ls t' →
      ∃ k trS cE ψ, k ≤ ls.length ∧ AllocThread.MTRun RX.vc RX.rf RX.sem ckeep (cEvs RX.F RX.ctx)
        (MConf.init RX.rf (locVal RX.fr (iterN RX.step n RX.s0)) (E2E.bodyOf RX.af RX.s0)) trS cE ∧
        ThreadRefine.Refines (· = ·) (PrivA RX) (MonPair (evTr (ls.take k))) (PrepThread.conv trS)
          (PrepThread.conv (evTr (ls.take k))) ψ ∧ (k = ls.length ∨ Done RX cE) := by
  obtain ⟨n, -, hq, hA, -⟩ := q_init wfX (abi_of szX codeX)
    ((E2E.Binary.bodyEntry_bodyOf RX.af RX.s0).w RX.F entryArgX)
  exact ⟨n, hq, hA, fun _ _ _ hr => arm_alloc_refines_lsx wfX scopeX hq hA hr⟩

end Concurrency.ArmAllocThread.LSXWitness
