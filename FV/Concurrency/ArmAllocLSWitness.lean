module

public import FV.Concurrency.ArmAllocLS
public import FV.Concurrency.ArmAllocWitness

@[expose] public section

/-!
# Non-vacuity of layer 4b with the plain loads/stores (T2h, #311)

* `ls_premises`: the compiled function `args; v0 := 0x100; v2 := 8; v1 := ldr [v0]; str v1,
  [v0, v2]; d3 := ldur [v0, #16]; str d3, [v0, v2, lsl #3]; v4 := ldr [sp, #8]; rets` (`RS`: a hand-written VCode
  `vcS` and allocation `rfS`, lowered, emitted and laid out by the compiler, loaded as
  `ArmAllocWitness.act` loads it) meets the premises of `arm_alloc_refines_ls`: `R.Wf`,
  `MemScopeLS` (and not `MemScopeB`: the plain loads/stores are no memory form of that scope),
  and `Q ∧ AInv` at `MConf.init` after the prologue (`Backend.Proof.q_init`). Its four accesses
  cover GPR and SIMD&FP loads and stores at the unsigned-offset, unscaled, register and scaled
  register modes, and a stack mode (`spOffset`, lowered without the `x16` prefix).

The layout facts (the label map is a hash map, which the kernel does not reduce) are by
`native_decide`.
-/

namespace Concurrency.ArmAllocThread.LSWitness

open Arm ArmFoot ArmThread Backend Backend.Proof VCodeThread Witness

def flS : Clif.MemFlags := default

/-- `movz` of `k` into vreg `v`. -/
def mz (v k : Nat) : MInst := .movWide .movZ (.vreg v .int) ⟨k, 0⟩ .size64

def vcS : VCode :=
  { name := "s", blocks := #[{ label := 0, insts := #[.args [], mz 0 0x100, mz 2 8,
      .load .uload64 (.vreg 1 .int) (.unsignedOffset (.vreg 0 .int) 0) flS,
      .store .store64 (.vreg 1 .int) (.regReg (.vreg 0 .int) (.vreg 2 .int)) flS,
      .fpuLoad .size64 (.vreg 3 .float) (.unscaled (.vreg 0 .int) 16) flS,
      .fpuStore .size64 (.vreg 3 .float) (.regScaled (.vreg 0 .int) (.vreg 2 .int)) flS,
      .load .uload64 (.vreg 4 .int) (.spOffset 8) flS,
      .rets []] }], classes := #[],
    slotBytes := 0, outgoing := 0, rulesFired := #[] }

def xr (n : Nat) : Loc := .reg (.x n)
def vr (n : Nat) : Loc := .reg (.v n)

def rfS : RFunc :=
  { blocks := #[#[.op 0 #[], .op 1 #[xr 9], .op 2 #[xr 10], .op 3 #[xr 11, xr 9],
      .op 4 #[xr 11, xr 9, xr 10], .op 5 #[vr 1, xr 9], .op 6 #[vr 1, xr 9, xr 10], .op 7 #[xr 12],
      .op 8 #[]]],
    spillSlots := 0, saved := [] }

abbrev RS : RL := act vcS rfS

theorem wfS : RS.Wf :=
  wf_of (VCodeThread.Witness.ok_of_isOkB () (by decide +kernel)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by native_decide) (by native_decide) (by native_decide)
    (by decide +kernel) (by native_decide) (by decide +kernel)

theorem szS : 4 * RS.fb.words.size ≤ 0x10000 := by native_decide

theorem codeS : ∀ k < RS.fb.words.size,
    Arm.read_mem_bytes 4 (0x10000#64 + BitVec.ofNat 64 (4 * k)) RS.s0 = RS.fb.words[k]! := by
  native_decide

theorem entryArgS : ∀ r, RS.vc.EntryArg r → r.isArgReg = true := by
  intro r ⟨vb, ds, h1, h2, v, hv⟩
  simp only [RS, act, vcS] at h1
  cases h1
  simp at h2
  subst h2
  simp at hv

/-- **`Q ∧ AInv` at the allocated code's entry configuration** after the prologue
(`Backend.Proof.q_init`), with the body-entry world `E2E.bodyOf`. -/
theorem qS : ∃ n, Q RS (iterN RS.step n RS.s0)
      (MConf.init RS.rf (locVal RS.fr (iterN RS.step n RS.s0)) (E2E.bodyOf RS.af RS.s0)) ∧
    AInv RS (MConf.init RS.rf (locVal RS.fr (iterN RS.step n RS.s0)) (E2E.bodyOf RS.af RS.s0)) := by
  obtain ⟨n, -, hq, hA, -⟩ := q_init wfS (abi_of szS codeS)
    ((E2E.Binary.bodyEntry_bodyOf RS.af RS.s0).w RS.F entryArgS)
  exact ⟨n, hq, hA⟩

theorem scopeS : MemScopeLS RS := by
  intro b vb k i hb hi
  rcases b with _ | b
  · simp only [RS, act, vcS] at hb
    cases hb
    rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | k
    · simp at hi; subst hi; exact .inl (.inl (.inl (.inr (.inl ⟨_, rfl⟩))))
    · simp at hi; subst hi; exact .inl (.inl (.inl (.inl ⟨rfl, rfl, rfl⟩)))
    · simp at hi; subst hi; exact .inl (.inl (.inl (.inl ⟨rfl, rfl, rfl⟩)))
    · simp at hi; subst hi; exact .inr (.inr ⟨by decide, .inl rfl⟩)
    · simp at hi; subst hi; exact .inr (.inr ⟨by decide, .inl rfl⟩)
    · simp at hi; subst hi; exact .inr (.inr ⟨by decide, .inl rfl⟩)
    · simp at hi; subst hi; exact .inr (.inr ⟨by decide, .inl rfl⟩)
    · simp at hi; subst hi
      exact .inr (.inr ⟨by decide, .inr ⟨.inr (.inl ⟨_, rfl⟩), .unscaled .sp 8, by
        simp [memFinalize, simm9?, pure, Except.pure]⟩⟩)
    · simp at hi; subst hi; exact .inl (.inl (.inl (.inr (.inr (.inl ⟨_, rfl⟩)))))
    · simp at hi
  · simp [RS, act, vcS] at hb

/-- The plain load is outside `MemScopeB`. -/
theorem not_memScopeB : ¬ MemScopeB RS := by
  intro h
  rcases h 0 _ 3 _ rfl rfl with
    (((⟨-, -, h1⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩) | h | ⟨_, _, _, _, h, -⟩ | ⟨_, _, _, _, h, -⟩) |
      ⟨_, _, _, _, _, _, _, _, h⟩ | ⟨_, _, _, _, _, _, _, h⟩) | (⟨_, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, _, _, h⟩)
  · exact absurd h1 (by decide)
  all_goals cases h

/-- **Non-vacuity of `arm_alloc_refines_ls`**: the compiled function with GPR and SIMD&FP plain
loads and stores (`RS`) satisfies its premises — `R.Wf`, the scope with plain loads/stores
(beyond `MemScopeB`), and `Q ∧ AInv` at `MConf.init` after the prologue; the theorem then applies
to every precise Arm run under `OkPriv` from there. -/
theorem ls_premises : RS.Wf ∧ MemScopeLS RS ∧ ¬ MemScopeB RS ∧
    ∃ n, Q RS (iterN RS.step n RS.s0)
      (MConf.init RS.rf (locVal RS.fr (iterN RS.step n RS.s0)) (E2E.bodyOf RS.af RS.s0)) ∧
    AInv RS (MConf.init RS.rf (locVal RS.fr (iterN RS.step n RS.s0)) (E2E.bodyOf RS.af RS.s0)) ∧
    ∀ (mon : Mon) (ls : List Lab) (t' : ArmState × Mon),
      PRun Policy.arm RS.step (OkPriv RS) (iterN RS.step n RS.s0, mon) ls t' →
      ∃ k trS cE ψ, k ≤ ls.length ∧ AllocThread.MTRun RS.vc RS.rf RS.sem ckeep (cEvs RS.F RS.ctx)
        (MConf.init RS.rf (locVal RS.fr (iterN RS.step n RS.s0)) (E2E.bodyOf RS.af RS.s0)) trS cE ∧
        ThreadRefine.Refines (· = ·) (PrivA RS) (MonPair (evTr (ls.take k))) (PrepThread.conv trS)
          (PrepThread.conv (evTr (ls.take k))) ψ ∧ (k = ls.length ∨ Done RS cE) := by
  obtain ⟨n, hq, hA⟩ := qS
  exact ⟨wfS, scopeS, not_memScopeB, n, hq, hA, fun _ _ _ hr =>
    arm_alloc_refines_ls wfS scopeS hq hA hr⟩

end Concurrency.ArmAllocThread.LSWitness
