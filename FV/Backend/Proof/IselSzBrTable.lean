import FV.Backend.Proof.IselSzDefs
import FV.Backend.Proof.IselShpBrTable
import FV.Backend.Proof.IselShpTotal

/-!
# The size of the ISLE lowering's output (V6c): `br_table` (`lower_branch` rule 1140)

`br_table idx, default, [targets]` → `emit_island; ridx = put_in_reg_zext32 idx;
br_table_impl n ridx default targets` (`IselShpBrTable`). Its run emits the `EmitIsland`, the
code of the sub-run `put_in_reg_zext32`, for a bound `n` that is no `imm12` the code of the
sub-run `imm $I64 (ImmExtend.Zero) n`, the bound check (`cmp`) and the `JTSequence` on
`default :: targets`, whose weight and branch targets grow with the table.

The proofs run over a measure `emW w s` (the sum of `w` over the emitted instructions) for any
`w` bounded on these instructions; `wtA` (`w = szInstW`) and `tgA` (`w`: the targets) are its
instances (`handW_brTable_wt`, `handW_brTable_tg`). The sub-runs are hypotheses (`SubW`, from the
cost tables: `put_in_reg_zext32` on `[.c0]` weighs 107, `imm` on
`[.ty [.int 64], .data 122 1 [], .c0]` 428, neither emits targets), as is the shape fact `BrSub`
(`IselShpBrTable`: the context is clean and both sub-runs return an int vreg).
-/

namespace Backend.Proof.Cov

open Backend Backend.Proof Backend.Proof.Spill Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-- The sum of `w` over the instructions a lowering state has emitted (`wtA`: `w = szInstW`;
`tgA`: `w` the number of branch targets). -/
def emW (w : MInst → Nat) (s : LState) : Nat := (s.emitted.toList.map w).sum

theorem emW_fresh (w : MInst → Nat) (s : LState) (c : RegClass) : emW w (s.fresh c).2 = emW w s :=
  rfl

theorem emW_emit (w : MInst → Nat) (s : LState) (m : MInst) : emW w (s.emit m) = emW w s + w m := by
  simp [emW, LState.emit]

/-- **A sub-run's growth**: every run of term `t` on arguments the abstract values `as` describe
grows the measure `W` by at most `c` (at every fuel). -/
def SubW (p : Program) (f : Clif.Function) (ctx : Ctx) (t : TermId) (as : List AW)
    (W : LState → Nat) (c : Nat) : Prop :=
  ∀ (cfg : Config), cfg.checkOverlap = false →
  ∀ (n : Nat) (ty : TypeId) (vs : List V) (s : LState) (tr : Array RuleId) (r : Option V)
    (s' : LState) (tr' : Array RuleId),
    Holds2 f ctx as vs →
    (applyTerm p (sem ctx) cfg n ty t vs).run (s, tr) = .ok (r, (s', tr')) → W s' ≤ W s + c

/-- The shape invariant from a state to itself, with no vreg bound. -/
theorem shpIs_zero (s : LState) : ShpIs 0 s s :=
  ⟨⟨[], by simp, by simp⟩, Nat.zero_le _⟩

/-- The tail of `br_table_impl`: a bound check `m` after two fresh temporaries, then the
`JTSequence`. -/
theorem emW_jt {w : MInst → Nat} {a j kj c : Nat}
    (hJ : ∀ d ts r x y, w (.jtSequence d ts r x y) ≤ j + kj * (ts.length + 1)) {s0 s : LState}
    {m : MInst} (hm : w m ≤ a) (hs : emW w s ≤ emW w s0 + c) (d : Label) (ts : List Label)
    (r x y : Reg) :
    emW w ((((s.fresh .int).2.fresh .int).2.emit m).emit (.jtSequence d ts r x y)) ≤
      emW w s0 + c + a + (j + kj * (ts.length + 1)) := by
  simp only [emW_emit, emW_fresh]
  have := hJ d ts r x y
  omega

theorem emW_island {w : MInst → Nat} {i : Nat} (hI : ∀ k, w (.emitIsland k) ≤ i) {s s' : LState}
    {k : Nat} (h : s' = s.emit (.emitIsland k)) : emW w s' ≤ emW w s + i := by
  rw [h, emW_emit]; exact Nat.add_le_add_left (hI k) _

/-! ## `br_table_impl` -/

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
theorem br_table_impl_w {c3 n : Nat} (hn : 300 ≤ n) {k : Int} {r : Nat} {d : Label}
    {ts : List Label} {s s' : LState × Array RuleId} {v : V}
    (h553W : SubW p f ctx 553 [.ty [.int 64], .data 122 1 [], .c0] (emW w) c3)
    (h553 : SubOkP p f ctx 0 553 [.ty [.int 64], .data 122 1 [], .c0] (.reg 1))
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
    have hwA := h553W cfg hc _ _ _ _ _ _ _ _ (holds2_imm64 k) h553'
    obtain ⟨-, hvA⟩ := h553 cfg hc _ _ _ _ _ _ _ _ _ (holds2_imm64 k) (shpIs_zero _) h553'
    obtain ⟨dd, rfl⟩ := reg1_int (hvA _ rfl)
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
theorem brTable_w {i c6 c3 : Nat} (hI : ∀ k, w (.emitIsland k) ≤ i) (hcl : Clean ctx)
    (h556W : SubW p f ctx 556 [.c0] (emW w) c6)
    (h556 : SubOkP p f ctx 0 556 [.c0] (.reg 1))
    (h553W : SubW p f ctx 553 [.ty [.int 64], .data 122 1 [], .c0] (emW w) c3)
    (h553 : SubOkP p f ctx 0 553 [.ty [.int 64], .data 122 1 [], .c0] (.reg 1))
    {ti : Nat} {targets : List Label} {m n : Nat} {s : LState} {tr : Array RuleId}
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
    br_table_impl_w hp hc hA hB hJ (n := n) (k := k) (r := r) (d := d) (ts := ts) (s := s)
      (v := v) (s' := s') hn h553W h553 h
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
  have hidx := clean_field3 (hdat ▸ hcl _ _ hi)
  have hwZ := h556W cfg hc _ _ _ _ _ _ _ _ (holds2_c0 hidx) h556'
  obtain ⟨-, hvZ⟩ := h556 cfg hc _ _ _ _ _ _ _ _ _ (holds2_c0 hidx) (shpIs_zero _) h556'
  obtain ⟨dd, rfl⟩ := reg1_int (hvZ _ rfl)
  have h670 := ‹ApplyInternal _ _ _ _ 13 670 _ _ _ _›
  have hwB := kB _ (by omega) _ _ _ _ _ _ _ h670
  simp only at hwB ⊢
  omega

end

/-! ## The hand-checked rule 1140 -/

theorem szInstW_cmpImm32 (rn : Reg) (imm : Imm12) :
    szInstW (.aluRRImm12 .subS .size32 .xzr rn imm) = 101 := rfl

theorem szInstW_cmpRR32 (rn rm : Reg) : szInstW (.aluRRR .subS .size32 .xzr rn rm) = 101 := rfl

theorem szInstW_island (k : Nat) : szInstW (.emitIsland k) = 101 := rfl

theorem szInstW_jt (d : Label) (ts : List Label) (r x y : Reg) :
    szInstW (.jtSequence d ts r x y) = 106 + 2 * (ts.length + 1) := by
  simp only [szInstW, szWords, regCount, MInst.targets, List.length_cons]
  omega

/-- Rule 1140 is `rule_lower_3277`; its runs return. -/
theorem brTable_run {ctx : Ctx} {vs : List V} {rl : Rule}
    (hrl : rl ∈ program.rulesOf TId.lower_branch) (hid : rl.id = 1140) {W : LState → Nat}
    {c : Nat}
    (h : ∀ (cfg : Config), cfg.checkOverlap = false → ∀ (m n : Nat) (s : LState)
      (tr : Array RuleId) (env : Isle.Interp.Env V) (s1 : LState × Array RuleId) (out : V)
      (s2 : LState) (tr2 : Array RuleId), 1000 ≤ m → 1000 ≤ n →
      (matchRule program (sem ctx) cfg m rule_lower_3277 vs).run (s, tr) = .ok (some env, s1) →
      (evalExpr program (sem ctx) cfg n rule_lower_3277.rhs env).run s1 =
        .ok (some out, (s2, tr2)) → W s2 ≤ W s + c) :
    HandW program ctx vs rl W c := by
  have hmem : rule_lower_3277 ∈ program.rulesOf TId.lower_branch := by
    rw [show TId.lower_branch = 687 from rfl, program_rulesOf_687]; simp
  obtain rfl := eq_of_mem_of_id lower_branch_ids_nodup hrl hmem hid
  intro cfg hc m n s tr env s1 r s2 tr2 hm hn hmatch heval
  obtain ⟨out, rfl⟩ := Option.isSome_iff_exists.1
    (totality.1 ctx cfg n _ env s1 r (s2, tr2) totalE_brTable heval)
  exact h cfg hc m n s tr env s1 out s2 tr2 hm hn hmatch heval

/-- **The weight of rule 1140 (`br_table`)**: at most `szBrK` plus two per target (the
`JTSequence`'s words and targets). Beyond the contract: `BrSub` (the clean context and the
int-vreg results of the sub-runs, `IselShpBrTable`) and the sub-runs' weights, from the cost
table `szCTab` (`put_in_reg_zext32` on `[.c0]`: 107; `imm` on
`[.ty [.int 64], .data 122 1 [], .c0]`: 428). -/
theorem handW_brTable_wt {f : Clif.Function} {ctx : Ctx} (hsub : BrSub f ctx 0)
    (h556 : SubW program f ctx 556 [.c0] (fun s => wtA s.emitted) 107)
    (h553 : SubW program f ctx 553 [.ty [.int 64], .data 122 1 [], .c0]
      (fun s => wtA s.emitted) 428)
    {ti : Nat} {targets : List Label} {rl : Rule}
    (hrl : rl ∈ program.rulesOf TId.lower_branch) (hid : rl.id = 1140) :
    HandW program ctx [.inst ti, .labels targets] rl (fun s => wtA s.emitted)
      (szBrK + 2 * targets.length) := by
  obtain ⟨hcl, h556v, h553v⟩ := hsub
  refine brTable_run hrl hid fun cfg hc m n s tr env s1 out s2 tr2 hm hn hmatch heval => ?_
  have := brTable_w (w := szInstW) (a := 101) (j := 106) (kj := 2) (i := 101) data_program hc
    (fun rn imm => Nat.le_of_eq (szInstW_cmpImm32 rn imm))
    (fun rn rm => Nat.le_of_eq (szInstW_cmpRR32 rn rm))
    (fun d ts r x y => Nat.le_of_eq (szInstW_jt d ts r x y))
    (fun k => Nat.le_of_eq (szInstW_island k)) hcl h556
    h556v h553 h553v hm hn hmatch heval
  change wtA s2.emitted ≤ wtA s.emitted + (101 + 107 + 428 + 101 + (106 + 2 * targets.length))
    at this
  show wtA s2.emitted ≤ wtA s.emitted + (1500 + 2 * targets.length)
  omega

/-- **The branch targets of rule 1140 (`br_table`)**: its `JTSequence`'s, the targets. Beyond
the contract: `BrSub` and the sub-runs' targets, from the cost table `tgCTab` (none). -/
theorem handW_brTable_tg {f : Clif.Function} {ctx : Ctx} (hsub : BrSub f ctx 0)
    (h556 : SubW program f ctx 556 [.c0] (fun s => tgA s.emitted) 0)
    (h553 : SubW program f ctx 553 [.ty [.int 64], .data 122 1 [], .c0]
      (fun s => tgA s.emitted) 0)
    {ti : Nat} {targets : List Label} {rl : Rule}
    (hrl : rl ∈ program.rulesOf TId.lower_branch) (hid : rl.id = 1140) :
    HandW program ctx [.inst ti, .labels targets] rl (fun s => tgA s.emitted) targets.length := by
  obtain ⟨hcl, h556v, h553v⟩ := hsub
  refine brTable_run hrl hid fun cfg hc m n s tr env s1 out s2 tr2 hm hn hmatch heval => ?_
  have := brTable_w (w := fun m => m.targets.length) (a := 0) (j := 0) (kj := 1) (i := 0)
    data_program hc (fun _ _ => Nat.le_refl _) (fun _ _ => Nat.le_refl _)
    (fun _ ts _ _ _ => by simp [MInst.targets]) (fun _ => Nat.le_refl _) hcl h556 h556v h553
    h553v hm hn hmatch heval
  change tgA s2.emitted ≤ tgA s.emitted + (0 + 0 + 0 + 0 + (0 + 1 * targets.length)) at this
  show tgA s2.emitted ≤ tgA s.emitted + targets.length
  omega

end Backend.Proof.Cov
