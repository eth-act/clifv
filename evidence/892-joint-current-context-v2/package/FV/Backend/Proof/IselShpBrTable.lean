import FV.Backend.Proof.IselShpBase
import FV.Backend.Proof.IselCtlBrTable

/-!
# Control shapes of the ISLE lowering (V4): `br_table` (`lower_branch` rule 1140)

`br_table idx, default, [targets]` → `emit_island; ridx = put_in_reg_zext32 idx;
br_table_impl n ridx default targets` (`cmp ridx, #n` or `cmp ridx, rn` after `rn = imm n`,
then `jt_sequence` with two fresh temporaries). The only control forms are the `EmitIsland`
(`CtlShape.emitIsland`) and the `JTSequence` on the int vreg `ridx` with fresh distinct
temporaries `≥ s.nextVreg ≥ N` (`CtlShape.jt`); the sub-runs `put_in_reg_zext32` and `imm`
are the abstract interpreter's (`SubOk`).
-/

namespace Backend.Proof.Cov

open Backend Backend.Proof Backend.Proof.Spill Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-- `SubOk` over an abstract program (`SubOkP program = SubOk`), for the `Data p` proofs. -/
def SubOkP (p : Program) (f : Clif.Function) (ctx : Ctx) (N : Nat) (t : TermId) (as : List AW)
    (out : AW) : Prop :=
  ∀ (cfg : Config), cfg.checkOverlap = false →
  ∀ (n : Nat) (ty : TypeId) (vs : List V) (s0 s : LState) (tr : Array RuleId) (r : Option V)
    (s' : LState) (tr' : Array RuleId),
    Holds2 f ctx as vs → ShpIs N s0 s →
    (applyTerm p (sem ctx) cfg n ty t vs).run (s, tr) = .ok (r, (s', tr')) →
    ShpIs N s0 s' ∧ ∀ v, r = some v → γ f ctx out v

/-! ## The state invariant through `fresh` and `emit` -/

section
variable {N : Nat} {s0 s : LState}

theorem ShpIs.fresh (h : ShpIs N s0 s) (c : RegClass) : ShpIs N s0 (s.fresh c).2 :=
  ⟨h.1, by simp only [LState.fresh]; have := h.2; omega⟩

theorem ShpIs.emit (h : ShpIs N s0 s) {m : MInst} (hm : m.isCtl = true → CtlShape N m) :
    ShpIs N s0 (s.emit m) := by
  obtain ⟨⟨ms, he, hms⟩, hn⟩ := h
  refine ⟨⟨ms ++ [m], by simp [LState.emit, he], fun x hx => ?_⟩, hn⟩
  rcases List.mem_append.1 hx with hx | hx
  · exact hms x hx
  · rw [List.mem_singleton.1 hx]; exact hm

theorem ShpIs.emit_nctl (h : ShpIs N s0 s) {m : MInst} (hm : m.isCtl = false) :
    ShpIs N s0 (s.emit m) :=
  h.emit fun h' => absurd (hm ▸ h') (by decide)

theorem ShpIs.emit_eq (h : ShpIs N s0 s) {m : MInst} {s' : LState} (he : s' = s.emit m)
    (hm : m.isCtl = true → CtlShape N m) : ShpIs N s0 s' :=
  he ▸ h.emit hm

end

/-- A register `γ (.reg 1)` describes is an int vreg. -/
theorem reg1_int {f : Clif.Function} {ctx : Ctx} {v : V} (h : γ f ctx (.reg 1) v) :
    ∃ n, v = .reg (.vreg n .int) := by
  obtain ⟨r, rfl, hk⟩ := h
  obtain ⟨n, rfl⟩ := isV_sound (a := .reg 1) rfl (f := f) (ctx := ctx) ⟨r, rfl, hk⟩
  exact ⟨n, rfl⟩

/-- The middle field of a clean three-field value is clean. -/
theorem clean_field3 {t k : Nat} {a x b : V}
    (h : (V.data t k [a, x, b]).regsIn = [] ∧ covV (.data t k [a, x, b]) = true) :
    x.regsIn = [] ∧ covV x = true := by
  obtain ⟨h1, h2⟩ := h
  simp only [V.regsIn, Flow.regsInL, List.append_eq_nil_iff] at h1
  rw [covV_data] at h2
  simp only [covVL, Bool.and_eq_true] at h2
  exact ⟨h1.2.1, h2.2.2.1⟩

/-- A clean value is described by `.c0`. -/
theorem holds2_c0 {f : Clif.Function} {ctx : Ctx} {x : V} (h : x.regsIn = [] ∧ covV x = true) :
    Holds2 f ctx [.c0] [x] :=
  ⟨γ_c0 h, trivial⟩

/-- The arguments of `imm $I64 (ImmExtend.Zero) n`. -/
theorem holds2_imm64 {f : Clif.Function} {ctx : Ctx} (k : Int) :
    Holds2 f ctx [.ty [.int 64], .data 122 1 [], .c0] [.ty (.int 64), .data 122 1 [], .int k] :=
  ⟨⟨_, List.mem_singleton_self _, rfl⟩, ⟨[], rfl, trivial⟩, γ_c0 ⟨rfl, rfl⟩, trivial⟩

/-- The tail of `br_table_impl`: a non-control bound check `m` after two fresh temporaries,
then the `jt_sequence` on them. -/
theorem ShpIs.jt {N : Nat} {s0 s : LState} (hs : ShpIs N s0 s) {m : MInst} (hm : m.isCtl = false)
    (d : Label) (ts : List Label) (r : Nat) :
    ShpIs N s0 ((((s.fresh .int).2.fresh .int).2.emit m).emit
      (.jtSequence d ts (.vreg r .int) (s.fresh .int).1 ((s.fresh .int).2.fresh .int).1)) :=
  (((hs.fresh _).fresh _).emit_nctl hm).emit fun _ =>
    .jt d ts r s.nextVreg (s.nextVreg + 1) (by omega) hs.2 (by have := hs.2; omega)

/-! ## `br_table_impl` -/

section
variable {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx} {cfg : Config}
  (hc : cfg.checkOverlap = false)

set_option maxHeartbeats 4000000 in
include hp hc in
/-- **`br_table_impl n ridx default targets`** (on an int vreg `ridx`) keeps the invariant: the
bound check (`cmp`, after `imm` if `n` is no `imm12`) and the `jt_sequence` on two fresh
temporaries. -/
theorem br_table_impl_shp {N n : Nat} (hn : 300 ≤ n) {k : Int} {r : Nat} {d : Label}
    {ts : List Label} {s s' : LState × Array RuleId} {v : V} {s0 : LState}
    (h553 : SubOkP p f ctx N 553 [.ty [.int 64], .data 122 1 [], .c0] (.reg 1))
    (hs : ShpIs N s0 s.1)
    (h : ApplyInternal p (sem ctx) cfg n 13 670 [.int k, .reg (.vreg r .int), .label d, .labels ts]
      s v s') :
    ShpIs N s0 s'.1 := by
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
    exact hs.jt rfl d ts r
  · brif_inv [*, rule_inst_5454] at hm he
    have h553' := ‹ApplyInternal _ _ _ _ 27 553 _ _ _ _›
    obtain ⟨hsA, hvA⟩ := h553 cfg hc _ _ _ _ _ _ _ _ _ (holds2_imm64 k) hs h553'
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
    exact hsA.jt rfl d ts r

set_option maxHeartbeats 8000000 in
include hp hc in
/-- **Rule 1140** (`rule_lower_3277`, over an abstract program) keeps the invariant. -/
theorem brTable_shp {N : Nat} (hcl : Clean ctx)
    (h556 : SubOkP p f ctx N 556 [.c0] (.reg 1))
    (h553 : SubOkP p f ctx N 553 [.ty [.int 64], .data 122 1 [], .c0] (.reg 1))
    {ti : Nat} {targets : List Label} {m n : Nat} {s0 s : LState} {tr : Array RuleId}
    {env : Isle.Interp.Env V} {s1 : LState × Array RuleId} {out : V} {s2 : LState}
    {tr2 : Array RuleId} (hm : 1000 ≤ m) (hn : 1000 ≤ n) (hs : ShpIs N s0 s)
    (hmatch : (matchRule p (sem ctx) cfg m rule_lower_3277 [.inst ti, .labels targets]).run (s, tr) =
      .ok (some env, s1))
    (heval : (evalExpr p (sem ctx) cfg n rule_lower_3277.rhs env).run s1 = .ok (some out, (s2, tr2))) :
    ShpIs N s0 s2 := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 400 := ⟨n - 400, by omega⟩
  have kS := fun n (hn : 60 ≤ n) i s v s' h => side_effect_inst_ok hp (ctx := ctx) hc (n := n)
    (i := i) (s := s) (v := v) (s' := s') hn h
  have kI := fun n (hn : 30 ≤ n) k s v s' h => emit_island_ok hp (ctx := ctx) hc (n := n)
    (k := k) (s := s) (v := v) (s' := s') hn h
  have kB := fun n (hn : 300 ≤ n) k r d ts s v s' (hs : ShpIs N s0 s.1) h =>
    br_table_impl_shp hp hc (n := n) (k := k) (r := r) (d := d) (ts := ts) (s := s) (v := v)
      (s' := s') hn h553 hs h
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
  have hsI := hs.emit_eq hs2 fun _ => .emitIsland _
  have h556' := ‹ApplyInternal _ _ _ _ 27 556 _ _ _ _›
  have hidx := clean_field3 (hdat ▸ hcl _ _ hi)
  obtain ⟨hsZ, hvZ⟩ := h556 cfg hc _ _ _ _ _ _ _ _ _ (holds2_c0 hidx) hsI h556'
  obtain ⟨dd, rfl⟩ := reg1_int (hvZ _ rfl)
  have h670 := ‹ApplyInternal _ _ _ _ 13 670 _ _ _ _›
  exact kB _ (by omega) _ _ _ _ _ _ _ hsZ h670
end

/-! ## The hand-checked rule 1140 -/

/-- `br_table`'s right-hand side calls no `partial` term. -/
theorem totalE_brTable : totalE program rule_lower_3277.rhs = true := by decide +kernel

/-- What rule 1140 needs beyond the contract: the context is clean (`idx` is a clean field of
the `BranchTable` data) and the table's sub-runs `put_in_reg_zext32` on a clean value and
`imm $I64 (ImmExtend.Zero) n` (both returning an int vreg). -/
def BrSub (f : Clif.Function) (ctx : Ctx) (N : Nat) : Prop :=
  Clean ctx ∧ SubOk f ctx N 556 [.c0] (.reg 1) ∧
    SubOk f ctx N 553 [.ty [.int 64], .data 122 1 [], .c0] (.reg 1)

/-- **Rule 1140 (`br_table`) keeps the invariant** (`HandOk`). -/
theorem handOk_brTable (htot : Totality) {f : Clif.Function} {ctx : Ctx} (_hctx : CtxInv f ctx)
    (hsub : ∀ N, BrSub f ctx N) {ti : Nat} {targets : List Label} {rl : Rule}
    (hrl : rl ∈ program.rulesOf TId.lower_branch) (hid : rl.id = 1140) (N : Nat) :
    HandOk ctx N [.inst ti, .labels targets] rl := by
  have hmem : rule_lower_3277 ∈ program.rulesOf TId.lower_branch := by
    rw [show TId.lower_branch = 687 from rfl, program_rulesOf_687]; simp
  obtain rfl := eq_of_mem_of_id lower_branch_ids_nodup hrl hmem hid
  obtain ⟨hcl, h556, h553⟩ := hsub N
  intro cfg hc m n s0 s tr env s1 r s2 tr2 hm hn hs hmatch heval
  obtain ⟨out, rfl⟩ := Option.isSome_iff_exists.1
    (htot.1 ctx cfg n _ env s1 r (s2, tr2) totalE_brTable heval)
  exact brTable_shp data_program hc hcl h556 h553 hm hn hs hmatch heval

end Backend.Proof.Cov
