import FV.Backend.Proof.IselSzBrTable

/-!
# The size of the ISLE lowering's output (V6c): `br_table` with its sub-runs as hypotheses

`IselSzBrTable`'s `br_table_impl_w`/`brTable_w`, with the facts about the two sub-runs
(`put_in_reg_zext32` on the table index, `imm $I64 (ImmExtend.Zero) n`) stated on the concrete
runs (`SubRun`: the measure grows by at most a bound, the result is an int vreg) instead of
through V3's untyped abstract values, so that a typed analysis (`IselSzTDriver`) can supply them:
`brTable_wG`, `handW_brTable_wtG`, `handW_brTable_tgG`.
-/

namespace Backend.Proof.Cov

open Backend Backend.Proof Backend.Proof.Spill Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-- **A sub-run on concrete arguments**: every run of term `t` on `vs` grows `emW w` by at most
`c`, and a result is an int vreg. -/
def SubRun (p : Program) (ctx : Ctx) (t : TermId) (vs : List V) (w : MInst → Nat) (c : Nat) : Prop :=
  ∀ (cfg : Config), cfg.checkOverlap = false →
  ∀ (n : Nat) (ty : TypeId) (s : LState) (tr : Array RuleId) (r : Option V) (s' : LState)
    (tr' : Array RuleId),
    (applyTerm p (sem ctx) cfg n ty t vs).run (s, tr) = .ok (r, (s', tr')) →
    emW w s' ≤ emW w s + c ∧ ∀ v, r = some v → ∃ d, v = .reg (.vreg d .int)

/-- `x` is the index field of the `BranchTable` data at slot `ti`. -/
def BrIdx (ctx : Ctx) (ti : Nat) (x : V) : Prop :=
  ∃ info a b, ctx.insts[ti]? = some info ∧ V.data 152 4 [a, x, b] = info.data

section
variable {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx} {cfg : Config}
  (hc : cfg.checkOverlap = false) {w : MInst → Nat} {a j kj : Nat}
  (hA : ∀ rn imm, w (.aluRRImm12 .subS .size32 .xzr rn imm) ≤ a)
  (hB : ∀ rn rm, w (.aluRRR .subS .size32 .xzr rn rm) ≤ a)
  (hJ : ∀ d ts r x y, w (.jtSequence d ts r x y) ≤ j + kj * (ts.length + 1))

set_option maxHeartbeats 4000000 in
include hp hc hA hB hJ in
/-- **`br_table_impl n ridx default targets`** (on an int vreg `ridx`) grows `emW w` by at most
the sub-run `imm`'s `c3`, the bound check's `a` and the `JTSequence`'s weight. -/
theorem br_table_impl_wG {c3 n : Nat} (hn : 300 ≤ n) {k : Int} {r : Nat} {d : Label}
    {ts : List Label} {s s' : LState × Array RuleId} {v : V}
    (h553 : ∀ k : Int, SubRun p ctx 553 [.ty (.int 64), .data 122 1 [], .int k] w c3)
    (h : ApplyInternal p (sem ctx) cfg n 13 670 [.int k, .reg (.vreg r .int), .label d, .labels ts]
      s v s') :
    emW w s'.1 ≤ emW w s.1 + c3 + a + (j + kj * (ts.length + 1)) := by
  have kJ := fun n (hn : 30 ≤ n) r d ts s v s' h => jt_sequence_ok hp (ctx := ctx) hc (n := n)
    (r := r) (d := d) (ts := ts) (s := s) (v := v) (s' := s') hn h
  have kW := fun n (hn : 40 ≤ n) mi ci s v s' h => with_flags_side_effect_ok hp (ctx := ctx) hc
    (n := n) (mi := mi) (ci := ci) (s := s) (v := v) (s' := s') hn h
  have kE2 := fun n (hn : 30 ≤ n) i j s v s' h => emit_side_effect_inst2_ok hp (ctx := ctx) hc
    (n := n) (i := i) (j := j) (s := s) (v := v) (s' := s') hn h
  have kCI := fun n (hn : 30 ≤ n) a b c s v s' h => cmp_imm_ok hp (ctx := ctx) hc (n := n)
    (a := a) (b := b) (c := c) (s := s) (v := v) (s' := s') hn h
  have kC := fun n (hn : 30 ≤ n) a b c s v s' h => cmp_ok hp (ctx := ctx) hc (n := n)
    (a := a) (b := b) (c := c) (s := s) (v := v) (s' := s') hn h
  isel_split hp hc h 670
  · brif_inv [*, rule_inst_5450, ext_imm12_from_u64_iff] at hm he
    have h391 := ‹ApplyInternal _ _ _ _ 47 391 _ _ _ _›
    obtain ⟨hs1, rfl⟩ := kCI _ (by omega) _ _ _ _ _ _ h391
    have h662 := ‹ApplyInternal _ _ _ _ 49 662 _ _ _ _›
    obtain ⟨hs2, rfl⟩ := kJ _ (by omega) _ _ _ _ _ _ h662
    have h256 := ‹ApplyInternal _ _ _ _ 46 256 _ _ _ _›
    obtain ⟨hs3, rfl⟩ := kW _ (by omega) _ _ _ _ _ h256
    have h242 := ‹ApplyInternal _ _ _ _ 13 242 _ _ _ _›
    obtain ⟨m1, m2, hs4, hm1, hm2⟩ := kE2 _ (by omega) _ _ _ _ _ h242
    rw [ofV_cmpImm32] at hm1
    rw [ofV_jtSeq] at hm2
    cases hm1; cases hm2
    simp only at hs1 hs2 hs3 hs4
    rw [hs4, hs3, hs2, hs1]
    exact Nat.le_trans (emW_jt hJ (hA _ _) (Nat.le_add_right _ 0) _ _ _ _ _) (by omega)
  · brif_inv [*, rule_inst_5454] at hm he
    have h553' := ‹ApplyInternal _ _ _ _ 27 553 _ _ _ _›
    obtain ⟨hwA, hvA⟩ := h553 k cfg hc _ _ _ _ _ _ _ h553'
    obtain ⟨dd, rfl⟩ := hvA _ rfl
    have h390 := ‹ApplyInternal _ _ _ _ 47 390 _ _ _ _›
    obtain ⟨hs1, rfl⟩ := kC _ (by omega) _ _ _ _ _ _ h390
    have h662 := ‹ApplyInternal _ _ _ _ 49 662 _ _ _ _›
    obtain ⟨hs2, rfl⟩ := kJ _ (by omega) _ _ _ _ _ _ h662
    have h256 := ‹ApplyInternal _ _ _ _ 46 256 _ _ _ _›
    obtain ⟨hs3, rfl⟩ := kW _ (by omega) _ _ _ _ _ h256
    have h242 := ‹ApplyInternal _ _ _ _ 13 242 _ _ _ _›
    obtain ⟨m1, m2, hs4, hm1, hm2⟩ := kE2 _ (by omega) _ _ _ _ _ h242
    rw [ofV_cmpRR32] at hm1
    rw [ofV_jtSeq] at hm2
    cases hm1; cases hm2
    simp only at hs1 hs2 hs3 hs4
    rw [hs4, hs3, hs2, hs1]
    exact emW_jt hJ (hB _ _) hwA _ _ _ _ _

set_option maxHeartbeats 8000000 in
include hp hc hA hB hJ in
/-- **Rule 1140** (`rule_lower_3277`, over an abstract program) grows `emW w` by at most the
island's `i`, the sub-runs' `c6` and `c3`, the bound check's `a` and the `JTSequence`'s weight on
the targets. -/
theorem brTable_wG {i c6 c3 : Nat} (hI : ∀ k, w (.emitIsland k) ≤ i) {ti : Nat}
    (h556 : ∀ x, BrIdx ctx ti x → SubRun p ctx 556 [x] w c6)
    (h553 : ∀ k : Int, SubRun p ctx 553 [.ty (.int 64), .data 122 1 [], .int k] w c3) {targets : List Label} {m n : Nat} {s : LState} {tr : Array RuleId}
    {env : Isle.Interp.Env V} {s1 : LState × Array RuleId} {out : V} {s2 : LState}
    {tr2 : Array RuleId} (hm : 1000 ≤ m) (hn : 1000 ≤ n)
    (hmatch : (matchRule p (sem ctx) cfg m rule_lower_3277 [.inst ti, .labels targets]).run (s, tr) =
      .ok (some env, s1))
    (heval : (evalExpr p (sem ctx) cfg n rule_lower_3277.rhs env).run s1 = .ok (some out, (s2, tr2))) :
    emW w s2 ≤ emW w s + (i + c6 + c3 + a + (j + kj * targets.length)) := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 400 := ⟨n - 400, by omega⟩
  have kS := fun n (hn : 60 ≤ n) i s v s' h => side_effect_inst_ok hp (ctx := ctx) hc (n := n)
    (i := i) (s := s) (v := v) (s' := s') hn h
  have kI := fun n (hn : 30 ≤ n) k s v s' h => emit_island_ok hp (ctx := ctx) hc (n := n)
    (k := k) (s := s) (v := v) (s' := s') hn h
  have kB := fun n (hn : 300 ≤ n) k r d ts s v s' h =>
    br_table_impl_wG hp hc hA hB hJ (n := n) (k := k) (r := r) (d := d) (ts := ts) (s := s)
      (v := v) (s' := s') hn h553 h
  cases hp
  brif_inv [*, rule_lower_3277, ext_jump_table_targets_iff, ctor_jump_table_size_iff,
    ctor_targets_jt_space_iff, ctor_u32_into_u64_iff] at hmatch heval
  repeat (isel_inv_simp [ext_jump_table_targets_iff, ctor_jump_table_size_iff,
    ctor_targets_jt_space_iff, ctor_u32_into_u64_iff] at * <;> isel_destruct <;> subst_vars)
  have hi := ‹ctx.insts[ti]? = some _›
  have hdat := ‹V.data 152 4 _ = _›
  have h669 := ‹ApplyInternal _ _ _ _ 46 669 _ _ _ _›
  obtain ⟨hs1, rfl⟩ := kI _ (by omega) _ _ _ _ h669
  have h243 := ‹ApplyInternal _ _ _ _ 25 243 _ _ _ _›
  obtain ⟨mi, hmi, hs2, -⟩ := kS _ (by omega) _ _ _ _ h243
  rw [show ∀ n : Nat, (4 * (8 + (n : Int))) = ((4 * (8 + n) : Nat) : Int) from
    fun n => by push_cast; omega, ofV_emitIsland] at hmi
  cases hmi
  simp only at hs1
  rw [hs1] at hs2
  have hwI := emW_island hI hs2
  have h556' := ‹ApplyInternal _ _ _ _ 27 556 _ _ _ _›
  obtain ⟨hwZ, hvZ⟩ := h556 _ ⟨_, _, _, hi, hdat⟩ cfg hc _ _ _ _ _ _ _ h556'
  obtain ⟨dd, rfl⟩ := hvZ _ rfl
  have h670 := ‹ApplyInternal _ _ _ _ 13 670 _ _ _ _›
  have hwB := kB _ (by omega) _ _ _ _ _ _ _ h670
  simp only at hwB ⊢
  omega

end

/-- **The weight of rule 1140 (`br_table`)**, given its sub-runs: at most `szBrK` plus two per
target. -/
theorem handW_brTable_wtG {ctx : Ctx} {ti : Nat}
    (h556 : ∀ x, BrIdx ctx ti x → SubRun program ctx 556 [x] szInstW 107)
    (h553 : ∀ k : Int, SubRun program ctx 553 [.ty (.int 64), .data 122 1 [], .int k] szInstW 428)
    {targets : List Label} {rl : Rule}
    (hrl : rl ∈ program.rulesOf TId.lower_branch) (hid : rl.id = 1140) :
    HandW program ctx [.inst ti, .labels targets] rl (fun s => wtA s.emitted)
      (szBrK + 2 * targets.length) := by
  refine brTable_run hrl hid fun cfg hc m n s tr env s1 out s2 tr2 hm hn hmatch heval => ?_
  have := brTable_wG (w := szInstW) (a := 101) (j := 106) (kj := 2) (i := 101) data_program hc
    (fun rn imm => Nat.le_of_eq (szInstW_cmpImm32 rn imm))
    (fun rn rm => Nat.le_of_eq (szInstW_cmpRR32 rn rm))
    (fun d ts r x y => Nat.le_of_eq (szInstW_jt d ts r x y))
    (fun k => Nat.le_of_eq (szInstW_island k)) h556 h553 hm hn hmatch heval
  change wtA s2.emitted ≤ wtA s.emitted + (101 + 107 + 428 + 101 + (106 + 2 * targets.length))
    at this
  show wtA s2.emitted ≤ wtA s.emitted + (1500 + 2 * targets.length)
  omega

/-- **The branch targets of rule 1140 (`br_table`)**, given its sub-runs: the targets. -/
theorem handW_brTable_tgG {ctx : Ctx} {ti : Nat}
    (h556 : ∀ x, BrIdx ctx ti x → SubRun program ctx 556 [x] (fun m => m.targets.length) 0)
    (h553 : ∀ k : Int, SubRun program ctx 553 [.ty (.int 64), .data 122 1 [], .int k]
      (fun m => m.targets.length) 0)
    {targets : List Label} {rl : Rule}
    (hrl : rl ∈ program.rulesOf TId.lower_branch) (hid : rl.id = 1140) :
    HandW program ctx [.inst ti, .labels targets] rl (fun s => tgA s.emitted) targets.length := by
  refine brTable_run hrl hid fun cfg hc m n s tr env s1 out s2 tr2 hm hn hmatch heval => ?_
  have := brTable_wG (w := fun m => m.targets.length) (a := 0) (j := 0) (kj := 1) (i := 0)
    data_program hc (fun _ _ => Nat.le_refl _) (fun _ _ => Nat.le_refl _)
    (fun _ ts _ _ _ => by simp [MInst.targets]) (fun _ => Nat.le_refl _) h556 h553
    hm hn hmatch heval
  change tgA s2.emitted ≤ tgA s.emitted + (0 + 0 + 0 + 0 + (0 + 1 * targets.length)) at this
  show tgA s2.emitted ≤ tgA s.emitted + targets.length
  omega

end Backend.Proof.Cov
