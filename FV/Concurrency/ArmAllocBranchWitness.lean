import FV.Concurrency.ArmAllocBranch
import FV.Concurrency.ArmAllocWitness

/-!
# Non-vacuity of layer 4b with the block-ending branches (T2, #311)

* `br_premises`: the compiled two-block function `args; jump 1` / `rets` (`RB`: a hand-written
  VCode `vcB` and allocation `rfB`, lowered, emitted and laid out by the compiler, loaded as
  `ArmAllocWitness.act` loads it) meets the premises of `arm_alloc_refines_br`: `R.Wf`,
  `MemScopeB` (and not `MemScopeL`: the `jump` is no memory form), and `Q ∧ AInv` at
  `MConf.init` after the prologue (`Backend.Proof.q_init`). Block 1 follows block 0, so
  `MachBuffer` removes the `jump`'s `b` (`jump_dropped`): the branch item takes no Arm step and
  the rank decreases (`goto_op`'s zero-step case).

The layout facts (the label map is a hash map, which the kernel does not reduce) are by
`native_decide`.
-/

namespace Concurrency.ArmAllocThread.BranchWitness

open Arm ArmFoot ArmThread Backend Backend.Proof VCodeThread Witness

/-- Block 0: `args; jump 1`; block 1: `rets`. -/
def vcB : VCode :=
  { name := "b", blocks := #[{ label := 0, insts := #[.args [], .jump 1] },
      { label := 1, insts := #[.rets []] }], classes := #[],
    slotBytes := 0, outgoing := 0, rulesFired := #[] }

def rfB : RFunc :=
  { blocks := #[#[.op 0 #[], .op 1 #[]], #[.op 0 #[]]], spillSlots := 0, saved := [] }

abbrev RB : RL := act vcB rfB

theorem wfB : RB.Wf :=
  wf_of (VCodeThread.Witness.ok_of_isOkB () (by decide +kernel)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by native_decide) (by native_decide) (by native_decide)
    (by decide +kernel) (by native_decide) (by decide +kernel)

theorem szB : 4 * RB.fb.words.size ≤ 0x10000 := by native_decide

theorem codeB : ∀ k < RB.fb.words.size,
    Arm.read_mem_bytes 4 (0x10000#64 + BitVec.ofNat 64 (4 * k)) RB.s0 = RB.fb.words[k]! := by
  native_decide

theorem entryArgB : ∀ r, RB.vc.EntryArg r → r.isArgReg = true := by
  intro r ⟨vb, ds, h1, h2, v, hv⟩
  simp only [RB, act, vcB] at h1
  cases h1
  simp at h2
  subst h2
  simp at hv

/-- **`Q ∧ AInv` at the allocated code's entry configuration** after the prologue
(`Backend.Proof.q_init`), with the body-entry world `E2E.bodyOf`. -/
theorem qB : ∃ n, Q RB (iterN RB.step n RB.s0)
      (MConf.init RB.rf (locVal RB.fr (iterN RB.step n RB.s0)) (E2E.bodyOf RB.af RB.s0)) ∧
    AInv RB (MConf.init RB.rf (locVal RB.fr (iterN RB.step n RB.s0)) (E2E.bodyOf RB.af RB.s0)) := by
  obtain ⟨n, -, hq, hA, -⟩ := q_init wfB (abi_of szB codeB)
    ((E2E.Binary.bodyEntry_bodyOf RB.af RB.s0).w RB.F entryArgB)
  exact ⟨n, hq, hA⟩

theorem scopeB : MemScopeB RB := by
  intro b vb k i hb hi
  rcases b with _ | _ | b
  · simp only [RB, act, vcB] at hb
    cases hb
    rcases k with _ | _ | k
    · simp at hi; subst hi; exact .inl (.inl (.inl (.inr (.inl ⟨_, rfl⟩))))
    · simp at hi; subst hi; exact .inr (.inl ⟨_, rfl⟩)
    · simp at hi
  · simp only [RB, act, vcB] at hb
    cases hb
    rcases k with _ | k
    · simp at hi; subst hi; exact .inl (.inl (.inl (.inr (.inr (.inl ⟨_, rfl⟩)))))
    · simp at hi
  · simp [RB, act, vcB] at hb

/-- The `jump` is outside `MemScopeL`. -/
theorem not_memScopeL : ¬ MemScopeL RB :=
  fun h => noGoto_memFormL (h 0 _ 1 _ rfl rfl) (.inl (.inl ⟨_, rfl⟩))

/-- A `b` line. -/
def isB : Line → Bool
  | .ins (.b _) _ => true
  | _ => false

/-- `fallthrough` drops the `jump`'s `b`: no line of the emitted code is a `b`. -/
theorem jump_dropped : RB.fa.lines.toList.all (fun ln => !isB ln) = true := by
  native_decide

/-- **Non-vacuity of `arm_alloc_refines_br`**: the compiled two-block function with a `jump`
(`RB`) satisfies its premises — `R.Wf`, the scope with branches (beyond `MemScopeL`), and
`Q ∧ AInv` at `MConf.init` after the prologue; the theorem then applies to every precise Arm run
under `OkPriv` from there. -/
theorem br_premises : RB.Wf ∧ MemScopeB RB ∧ ¬ MemScopeL RB ∧
    ∃ n, Q RB (iterN RB.step n RB.s0)
      (MConf.init RB.rf (locVal RB.fr (iterN RB.step n RB.s0)) (E2E.bodyOf RB.af RB.s0)) ∧
    AInv RB (MConf.init RB.rf (locVal RB.fr (iterN RB.step n RB.s0)) (E2E.bodyOf RB.af RB.s0)) ∧
    ∀ (mon : Mon) (ls : List Lab) (t' : ArmState × Mon),
      PRun Policy.arm RB.step (OkPriv RB) (iterN RB.step n RB.s0, mon) ls t' →
      ∃ k trS cE ψ, k ≤ ls.length ∧ AllocThread.MTRun RB.vc RB.rf RB.sem ckeep (cEvs RB.F RB.ctx)
        (MConf.init RB.rf (locVal RB.fr (iterN RB.step n RB.s0)) (E2E.bodyOf RB.af RB.s0)) trS cE ∧
        ThreadRefine.Refines (· = ·) (PrivA RB) (MonPair (evTr (ls.take k))) (PrepThread.conv trS)
          (PrepThread.conv (evTr (ls.take k))) ψ ∧ (k = ls.length ∨ Done RB cE) := by
  obtain ⟨n, hq, hA⟩ := qB
  exact ⟨wfB, scopeB, not_memScopeL, n, hq, hA, fun _ _ _ hr =>
    arm_alloc_refines_br wfB scopeB hq hA hr⟩

end Concurrency.ArmAllocThread.BranchWitness
