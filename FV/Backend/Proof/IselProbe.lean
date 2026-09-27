import FV.Backend.Proof.IselRules
import FV.Backend.Proof.IselSem

/-!
# Probe: `iadd` (`iadd_base_case`, `lower.isle:86`) end to end

* Width convention (Cranelift's, which the exported rules rely on): a CLIF value of type `ty`
  lives in the low `ty.width` bits of its 64-bit register; the upper bits are unspecified
  (`Holds`). `iadd_base_case` at i8/i16 emits a 32-bit `add` that leaves garbage in bits
  `ty.width..31`; a zero-upper-bits invariant (`CanonReg`) would therefore be *false* for
  rule outputs. Rules that need clean upper bits re-extend (`put_in_reg_zext32`, …), so the
  obligation stays local to each rule.
-/

namespace Backend.Proof

open Arm Isle Isle.Interp Isle.Aarch64

/-- A CLIF value `v : ty` is held by `x k` (low `ty.width` bits; upper bits unspecified). -/
def Holds (ty : Clif.Ty) (s : ArmState) (k : Nat) (v : BitVec ty.width) : Prop :=
  (X k s).setWidth ty.width = v

theorem frame_write_gpr {d : Nat} (hd : d ≤ 30) (v pc : BitVec 64) (s : ArmState) :
    Frame [d] false s (w (gpr d) v (w .PC pc s)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k hk hkd
    have hne : gpr k ≠ gpr d := by
      intro h; injection h with h; exact hkd (by simp [ofNat5_inj hk (by omega) h])
    simp only [X]; rw [r_of_w_different hne, r_of_w_different (by simp)]
  · intro i; rw [r_of_w_different (by simp), r_of_w_different (by simp)]
  · intro _ f; rw [r_of_w_different (by simp), r_of_w_different (by simp)]
  · rw [r_of_w_different (by simp), r_of_w_different (by simp)]
  · intro a; rw [read_mem_of_w, read_mem_of_w]

/-- A 32-bit add truncated to `w ≤ 32` bits is the `w`-bit add of the truncations (upper bits of
the inputs are irrelevant: the width convention is local to this rule). -/
theorem trunc_add32 (w : Nat) (hw : w ≤ 32) (A B : BitVec 64) :
    ((A.setWidth 32 + B.setWidth 32).setWidth 64).setWidth w = A.setWidth w + B.setWidth w := by
  apply BitVec.eq_of_toNat_eq
  have h1 : 2 ^ w ∣ 2 ^ 32 := Nat.pow_dvd_pow 2 hw
  have h2 : 2 ^ w ∣ 2 ^ 64 := Nat.pow_dvd_pow 2 (by omega)
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add]
  rw [Nat.mod_mod_of_dvd _ h2, Nat.mod_mod_of_dvd _ h1, Nat.add_mod (A.toNat % 2 ^ 32),
    Nat.mod_mod_of_dvd _ h1, Nat.mod_mod_of_dvd _ h1, ← Nat.add_mod]

/-- Arm meaning of the 32-bit `add` the rule emits for i8/i16/i32. -/
theorem add32_correct {d a b : Nat} (hd : d ≤ 30) (ha : a ≤ 30) (hb : b ≤ 30) (ty : Clif.Ty)
    (hty : ty.width ≤ 32) (s : ArmState) (u v : BitVec ty.width)
    (hu : Holds ty s a u) (hv : Holds ty s b v) :
    ∃ s', MInst.sem (.aluRRR .add .size32 (.x d) (.x a) (.x b)) s = .ok s' ∧
      Holds ty s' d (Clif.Sem.iadd u v) ∧ Frame [d] false s s' ∧ read_pc s' = read_pc s + 4#64 := by
  rw [sem_add32 hd ha hb]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · simp only [Holds, X, write_gpr, write_pc, read_gpr, r_of_w_same] at *
    subst hu hv
    exact trunc_add32 _ hty _ _
  · exact frame_write_gpr hd _ _ s
  · simp [read_pc, write_gpr, write_pc, r_of_w_same, r_of_w_different]

/-- Arm meaning of the 64-bit `add` the rule emits for i64. -/
theorem add64_correct {d a b : Nat} (hd : d ≤ 30) (ha : a ≤ 30) (hb : b ≤ 30) (s : ArmState)
    (u v : BitVec 64) (hu : Holds .i64 s a u) (hv : Holds .i64 s b v) :
    ∃ s', MInst.sem (.aluRRR .add .size64 (.x d) (.x a) (.x b)) s = .ok s' ∧
      Holds .i64 s' d (Clif.Sem.iadd u v) ∧ Frame [d] false s s' ∧ read_pc s' = read_pc s + 4#64 := by
  rw [sem_add64 hd ha hb]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · simp only [Holds, X, write_gpr, write_pc, read_gpr, r_of_w_same] at *
    subst hu hv
    simp [Clif.Ty.width, Clif.Sem.iadd]; rfl
  · exact frame_write_gpr hd _ _ s
  · simp [read_pc, write_gpr, write_pc, r_of_w_same, r_of_w_different]

variable {p : Isle.Program} (hp : Data p) (ctx : Ctx) {cfg : Config} (hc : cfg.checkOverlap = false)

include hp hc in
/-- **Rule correctness, `iadd_base_case` at i8/i16/i32** (M4 shape). For every CLIF
instruction `i` whose `InstructionData` is `Binary(Iadd, [x, y])` with result type `ty`
(`instData_iadd`: exactly what the backend builds for `iadd.ty x y`), the rule's left-hand
side matches, its right-hand side emits one `MInst` over a fresh vreg `dst`, and executing
that instruction under any register assignment `ρ` (vreg `n` in `x (ρ n)`), from any Arm
state where `x (ρ vx)`, `x (ρ vy)` hold the operands, ends in a state where `x (ρ dst)` holds
`Clif.Sem.iadd`, only `x (ρ dst)` and the PC changed. -/
theorem iadd_base_case_correct_32 (ty : Clif.Ty) (hty : ty.width ≤ 32)
    {i x y vx vy : Nat} {info : IInfo} (hi : ctx.insts[i]? = some info)
    (hres : info.resTys.head? = some (.int ty.width))
    (hd : info.data = .data 152 2 [.data 151 73 [], .values [x, y]])
    (hx : ctx.valueReg? x = some (.vreg vx .int)) (hy : ctx.valueReg? y = some (.vreg vy .int))
    (st : LState) (tr : Array RuleId) (n : Nat) :
    ∃ env m dst st' tr',
      (matchRule p (sem ctx) cfg (n+2) rule_lower_86 [.inst i]).run (st, tr) =
        .ok (some env, (st, tr)) ∧
      (evalExpr p (sem ctx) cfg (n+40) rule_lower_86.rhs env).run (st, tr) =
        .ok (some (.regsVec [[.vreg dst .int]]), (st', tr')) ∧
      st'.emitted = st.emitted.push m ∧
      ∀ (ρ : Nat → Nat), ρ vx ≤ 30 → ρ vy ≤ 30 → ρ dst ≤ 30 →
      ∀ (s : ArmState) (u v : BitVec ty.width), Holds ty s (ρ vx) u → Holds ty s (ρ vy) v →
        ∃ s', MInst.sem (m.mapRegs (alloc ρ)) s = .ok s' ∧
          Holds ty s' (ρ dst) (Clif.Sem.iadd u v) ∧ Frame [ρ dst] false s s' := by
  refine ⟨_, _, st.nextVreg, _, _, match_86 hp ctx hi hres (by omega) hd st tr n,
    rhs_86_32 hp ctx hc hx hy hty st tr n, rfl, ?_⟩
  intro ρ h1 h2 h3 s u v hu hv
  obtain ⟨s', h, hr, hf, -⟩ := add32_correct h3 h1 h2 ty hty s u v hu hv
  exact ⟨s', by simpa [MInst.mapRegs, alloc, LState.fresh] using h, hr, hf⟩

end Backend.Proof
