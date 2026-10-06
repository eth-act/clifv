import FV.Backend.Proof.Encode

/-!
# M5: label-relative operands and the branch-range policy

* `Env.pcRel_ok`: what a successful `Env.pcRel` guarantees (target defined, offset aligned,
  immediate = offset / scale, in the signed field's range).
* `Insn.pcRelSpec?`: the label operand of each PC-relative form with its architectural reach
  (Arm ARM C6.2: B ±128 MiB, B.cond/CBZ/CBNZ ±1 MiB, TBZ/TBNZ ±32 KiB, ADR ±1 MiB) and
  alignment, written out independently of the encoder.
* `Insn.toArmInst_pcRel`: the decoded instruction's PC offset (`ArmInst.pcRelOffset?`, the
  quantity the model adds to `PC`) is exactly `target - pc`, and it is within reach.
* `Insn.encode_inRange`: the branch-range policy. Every instruction the encoder accepts has
  its label operand within reach; equivalently an out-of-range branch is an encoding error,
  never a truncated word.
* `signExtend_append_zero`: the model's `branch_taken_pc` offset
  `SignExtend(imm:'00', 64)` is `4 * imm.toInt`.
-/

namespace Backend

open Arm

theorem bind_eq_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β} :
    (x >>= f) = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp [bind, Except.bind]

theorem map_eq_ok {ε α β : Type} {x : Except ε α} {f : α → β} {b : β} :
    (f <$> x) = .ok b ↔ ∃ a, x = .ok a ∧ f a = b := by
  cases x <;> simp [Functor.map, Except.map]

theorem bmod_ofInt_toInt (n : Nat) (q : Int) (h1 : -(2 ^ n : Int) ≤ q) (h2 : q < 2 ^ n) :
    (BitVec.ofInt (n + 1) q).toInt = q := by
  rw [BitVec.toInt_ofInt]
  apply Int.bmod_eq_of_le
  · rw [Nat.pow_succ]; push_cast; omega
  · rw [Nat.pow_succ]; push_cast; omega

/-- `Env.pcRel` succeeds only for a defined target at an aligned, in-range offset, and then the
field is the offset divided by `scale`. -/
theorem Env.pcRel_ok {env : Env} {what : String} {n scale : Nat} {l : Lbl}
    {v : BitVec (n + 1)} (h : env.pcRel what (n + 1) scale l = .ok v) :
    ∃ o q, env.target l = some o ∧ (o : Int) - env.pc = scale * q ∧ v.toInt = q ∧
      -(2 ^ n : Int) ≤ q ∧ q < 2 ^ n := by
  unfold Env.pcRel Env.rel at h
  cases hl : env.target l with
  | none => simp [hl, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  | some o =>
    simp only [hl, Nat.add_sub_cancel] at h
    by_cases ha : ((o : Int) - env.pc) % scale = 0
    · by_cases hr : -(2 ^ n : Int) ≤ ((o : Int) - env.pc) / scale ∧
          ((o : Int) - env.pc) / scale < 2 ^ n
      · simp only [ha, hr, bne_self_eq_false, Bool.false_eq_true, ite_false, ite_true, and_self,
          pure, bind, Except.bind, Except.pure, Except.ok.injEq] at h
        subst h
        refine ⟨o, _, rfl, ?_, bmod_ofInt_toInt n _ hr.1 hr.2, hr.1, hr.2⟩
        exact (Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero ha)).symm
      · simp [ha, hr, pure, bind, Except.bind, Except.pure, throw, throwThe,
          MonadExceptOf.throw] at h
    · simp [ha, pure, bind, Except.bind, Except.pure, throw, throwThe, MonadExceptOf.throw] at h

theorem Env.target_of_ne {env : Env} {l : Lbl} (h : l ≠ .skip) : env.target l = env.lbl l := by
  cases l <;> first | rfl | exact absurd rfl h

/-- The byte offset a decoded PC-relative instruction adds to its own address (the model's
`branch_taken_pc` / ADR result is `PC + SignExtend(…)`, `signExtend_append_zero`). -/
def _root_.Arm.ArmInst.pcRelOffset? : ArmInst → Option Int
  | .BR (.Uncond_branch_imm x) => some (4 * x.imm26.toInt)
  | .BR (.Cond_branch_imm x) => some (4 * x.imm19.toInt)
  | .BR (.Compare_branch x) => some (4 * x.imm19.toInt)
  | .BR (.Test_branch x) => some (4 * x.imm14.toInt)
  | .DPI (.PC_rel_addressing x) => if x.op = 0 then some (x.immhi ++ x.immlo).toInt else none
  | _ => none

theorem signExtend_append_zero {n : Nat} (x : BitVec (n + 1)) :
    BitVec.signExtend 64 (x ++ 0#2) = BitVec.ofInt 64 (4 * x.toInt) := by
  simp only [BitVec.signExtend, BitVec.toInt_append]
  simp

theorem Env.pcRel_ok' {env : Env} {what : String} {n scale : Nat} {l : Lbl}
    {v : BitVec (n + 1)} (hs : 0 < scale) (h : env.pcRel what (n + 1) scale l = .ok v) :
    ∃ o, env.target l = some o ∧ (scale : Int) * v.toInt = (o : Int) - env.pc ∧
      -((scale : Int) * 2 ^ n) ≤ (o : Int) - env.pc ∧ (o : Int) - env.pc < (scale : Int) * 2 ^ n ∧
      (scale : Int) ∣ (o : Int) - env.pc := by
  obtain ⟨o, q, hl, ho, rfl, h1, h2⟩ := Env.pcRel_ok h
  refine ⟨o, hl, ho.symm, ?_, ?_, ⟨_, ho⟩⟩
  · rw [ho, ← Int.mul_neg]; exact Int.mul_le_mul_of_nonneg_left h1 (Int.natCast_nonneg _)
  · rw [ho]; exact Int.mul_lt_mul_of_pos_left h2 (by omega)

/-- **Label resolution.** For every PC-relative form, the offset the decoded instruction adds
to its address is `target - pc` for the target's offset `o`, and `o - pc` is within the
form's reach and aligned. -/
theorem Insn.toArmInst_pcRel {env : Env} {i : Insn} {a : ArmInst} {t : Lbl} {reach align : Int}
    (h : i.toArmInst env = .ok a) (hs : i.pcRelSpec? = some (t, reach, align)) :
    ∃ o, env.target t = some o ∧ a.pcRelOffset? = some ((o : Int) - env.pc) ∧
      -reach ≤ (o : Int) - env.pc ∧ (o : Int) - env.pc < reach ∧ align ∣ (o : Int) - env.pc := by
  simp only [Insn.toArmInst, map_eq_ok] at h
  obtain ⟨b, hb, rfl⟩ := h
  cases i <;> simp only [Insn.pcRelSpec?, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hs
  all_goals
    obtain ⟨rfl, rfl, rfl⟩ := hs
    simp only [Insn.armFields, bind_eq_ok, pure, Except.pure, Except.ok.injEq] at hb
  case b =>
    obtain ⟨v, hv, rfl⟩ := hb
    obtain ⟨o, hl, h1, h2, h3, h4⟩ := Env.pcRel_ok' (by decide) hv
    push_cast at h1 h2 h3 h4 ⊢
    exact ⟨o, hl, by simp [ArmInst.norm, ArmInst.pcRelOffset?, h1], h2, h3, h4⟩
  case bcond =>
    obtain ⟨v, hv, rfl⟩ := hb
    obtain ⟨o, hl, h1, h2, h3, h4⟩ := Env.pcRel_ok' (by decide) hv
    push_cast at h1 h2 h3 h4 ⊢
    exact ⟨o, hl, by simp [ArmInst.norm, ArmInst.pcRelOffset?, h1], h2, h3, h4⟩
  case cbz =>
    obtain ⟨v, hv, _, _, rfl⟩ := hb
    obtain ⟨o, hl, h1, h2, h3, h4⟩ := Env.pcRel_ok' (by decide) hv
    push_cast at h1 h2 h3 h4 ⊢
    exact ⟨o, hl, by simp [ArmInst.norm, ArmInst.pcRelOffset?, h1], h2, h3, h4⟩
  case tbz =>
    split at hb
    · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hb
    · simp only [bind_eq_ok, Except.ok.injEq] at hb
      obtain ⟨v, hv, _, _, rfl⟩ := hb
      obtain ⟨o, hl, h1, h2, h3, h4⟩ := Env.pcRel_ok' (by decide) hv
      push_cast at h1 h2 h3 h4 ⊢
      exact ⟨o, hl, by simp [ArmInst.norm, ArmInst.pcRelOffset?, h1], h2, h3, h4⟩
  case adr =>
    obtain ⟨v, hv, _, _, rfl⟩ := hb
    obtain ⟨o, hl, h1, h2, h3, h4⟩ := Env.pcRel_ok' (by decide) hv
    push_cast at h1 h2 h3 h4 ⊢; simp only [Int.one_mul] at h1
    refine ⟨o, hl, ?_, h2, h3, h4⟩
    have hv' : BitVec.extractLsb' 2 19 v ++ BitVec.extractLsb' 0 2 v = v := by bv_decide
    simp [ArmInst.norm, ArmInst.pcRelOffset?, hv', h1]

/-- **Branch-range policy.** Every instruction the encoder accepts has its label operand
defined, aligned and within the form's reach. -/
theorem Insn.encode_inRange {env : Env} {i : Insn} {w : BitVec 32} {t : Lbl} {reach align : Int}
    (h : i.encode env = .ok w) (hs : i.pcRelSpec? = some (t, reach, align)) :
    ∃ o, env.target t = some o ∧ -reach ≤ (o : Int) - env.pc ∧ (o : Int) - env.pc < reach ∧
      align ∣ (o : Int) - env.pc := by
  obtain ⟨a, ha, _⟩ := Insn.encode_eq_ok.mp h
  obtain ⟨o, hl, _, h1, h2, h3⟩ := Insn.toArmInst_pcRel ha hs
  exact ⟨o, hl, h1, h2, h3⟩

/-- The same policy, stated as "never silently emit": a label operand out of reach is an
encoding error. -/
theorem Insn.encode_error_of_out_of_range {env : Env} {i : Insn} {t : Lbl} {reach align : Int}
    (hs : i.pcRelSpec? = some (t, reach, align)) (o : Nat) (hl : env.target t = some o)
    (hout : ¬ (-reach ≤ (o : Int) - env.pc ∧ (o : Int) - env.pc < reach)) :
    ∃ e, i.encode env = .error e := by
  cases h : i.encode env with
  | error e => exact ⟨e, rfl⟩
  | ok w =>
    obtain ⟨o', hl', h1, h2, _⟩ := Insn.encode_inRange h hs
    rw [hl] at hl'
    cases hl'
    exact absurd ⟨h1, h2⟩ hout

end Backend
