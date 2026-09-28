import FV.Backend.Proof.IselFamAluBBfm

/-!
# Family B: `popcnt` (`lower.isle:2074–2092`)

`fmov` the operand into a vector register, `cnt` the bits of each byte, sum the bytes (`addp` for
`i16`, `addv` for `i32`/`i64`, nothing for `i8`), `umov` byte 0 back. The vector temporaries are
float-class vregs (`temp_writable_reg $I8X16`).
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-- What an emitting helper returned: a fresh vreg of class `cls`, defined by one instruction. -/
def EmitOutC (cls : RegClass) (s s' : LState) (v : V) (iv : Reg → V) : Prop :=
  v = .reg (s.fresh cls).1 ∧ ∃ m, MInst.ofV (iv (s.fresh cls).1) = some m ∧
    s' = (s.fresh cls).2.emit m

section Ctor
variable (ctx : Ctx) (st : LState)

theorem ctor_temp_writable_reg_i8x16_iff (v : V) (st' : LState) :
    externCtor ctx T.temp_writable_reg [.ty (.vec 8 16 false)] st = .ok (v, st') ↔
      v = .reg (st.fresh .float).1 ∧ st' = (st.fresh .float).2 := by
  have : externCtor ctx T.temp_writable_reg [.ty (.vec 8 16 false)] st =
      .ok (.reg (st.fresh .float).1, (st.fresh .float).2) := rfl
  rw [this]; simp [eq_comm]

end Ctor

section Terms
variable {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)

set_option maxHeartbeats 1000000 in
include hp hc in
theorem size_for_mov_to_fpu_ok {n : Nat} (hn : 40 ≤ n) {k : Nat} (hk : k = 2 ∨ k = 3)
    {st st' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 95 410 [.data 95 k []] st v st') :
    v = .data 95 k [] ∧ st'.1 = st.1 := by
  rcases hk with rfl | rfl
  all_goals
    isel_split hp hc h 410
    all_goals first
      | (isel_inv [*, rule_inst_2941] at hm he; done)
      | (isel_inv [*, rule_inst_2938] at hm he; done)
      | skip

set_option maxHeartbeats 1000000 in
include hp hc in
theorem mov_to_fpu_ok {n : Nat} (hn : 50 ≤ n) {a : V} {k : Nat} (hk : k = 2 ∨ k = 3)
    {st st' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 409 [a, .data 95 k []] st v st') :
    EmitOutC .float st.1 st'.1 v (fun rd => .data 58 75 [.reg rd, a, .data 95 k []]) := by
  have hp' := hp
  rcases hk with rfl | rfl
  all_goals
  isel_split hp hc h 409
  isel_inv [*, rule_inst_2930, ctor_emit_iff, ctor_writable_reg_to_reg'] at hm he
  have hsz := ‹ApplyInternal _ _ _ _ 95 410 _ _ _ _›
  obtain ⟨rfl, hs⟩ := size_for_mov_to_fpu_ok hp' hc (by omega)
    (by first | exact .inl rfl | exact .inr rfl) hsz
  obtain ⟨rfl, rfl⟩ :=
    (ctor_temp_writable_reg_i8x16_iff ctx _ _ _).mp ‹externCtor ctx T.temp_writable_reg _ _ = _›
  rw [hs] at *
  exact ⟨rfl, _, ‹_›, rfl⟩

set_option maxHeartbeats 1000000 in
include hp hc in
theorem mov_from_vec_ok {n : Nat} (hn : 50 ≤ n) {a i k : V} {st st' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 414 [a, i, k] st v st') :
    EmitOutC .int st.1 st'.1 v (fun rd => .data 58 78 [.reg rd, a, i, k]) := by
  have hp' := hp
  isel_split hp hc h 414
  isel_inv [*, rule_inst_2970, ctor_emit_iff, ctor_writable_reg_to_reg',
    ctor_temp_writable_reg_i64'] at hm he
  exact ⟨rfl, _, ‹_›, rfl⟩

set_option maxHeartbeats 1000000 in
include hp hc in
theorem vec_misc_ok {n : Nat} (hn : 40 ≤ n) {op a k : V} {st st' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 395 [op, a, k] st v st') :
    EmitOutC .float st.1 st'.1 v (fun rd => .data 58 96 [op, .reg rd, a, k]) := by
  isel_split hp hc h 395
  isel_inv [*, rule_inst_2802, ctor_emit_iff, ctor_writable_reg_to_reg'] at hm he
  obtain ⟨rfl, rfl⟩ :=
    (ctor_temp_writable_reg_i8x16_iff ctx _ _ _).mp ‹externCtor ctx T.temp_writable_reg _ _ = _›
  exact ⟨rfl, _, ‹_›, rfl⟩

set_option maxHeartbeats 1000000 in
include hp hc in
theorem vec_lanes_ok {n : Nat} (hn : 40 ≤ n) {op a k : V} {st st' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 371 [op, a, k] st v st') :
    EmitOutC .float st.1 st'.1 v (fun rd => .data 58 97 [op, .reg rd, a, k]) := by
  isel_split hp hc h 371
  isel_inv [*, rule_inst_2612, ctor_emit_iff, ctor_writable_reg_to_reg'] at hm he
  obtain ⟨rfl, rfl⟩ :=
    (ctor_temp_writable_reg_i8x16_iff ctx _ _ _).mp ‹externCtor ctx T.temp_writable_reg _ _ = _›
  exact ⟨rfl, _, ‹_›, rfl⟩

set_option maxHeartbeats 1000000 in
include hp hc in
theorem vec_rrr_ok {n : Nat} (hn : 40 ≤ n) {op a b k : V} {st st' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 363 [op, a, b, k] st v st') :
    EmitOutC .float st.1 st'.1 v (fun rd => .data 58 93 [op, .reg rd, a, b, k]) := by
  isel_split hp hc h 363
  isel_inv [*, rule_inst_2552, ctor_emit_iff, ctor_writable_reg_to_reg'] at hm he
  obtain ⟨rfl, rfl⟩ :=
    (ctor_temp_writable_reg_i8x16_iff ctx _ _ _).mp ‹externCtor ctx T.temp_writable_reg _ _ = _›
  exact ⟨rfl, _, ‹_›, rfl⟩

include hp hc in
theorem vec_cnt_ok {n : Nat} (hn : 50 ≤ n) {a k : V} {st st' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 524 [a, k] st v st') :
    EmitOutC .float st.1 st'.1 v (fun rd => .data 58 96 [.data 107 17 [], .reg rd, a, k]) := by
  have hp' := hp
  isel_split hp hc h 524
  isel_inv [*, rule_inst_3545] at hm he
  rename_i hl
  exact vec_misc_ok hp' hc (by omega) hl

include hp hc in
theorem addp_ok {n : Nat} (hn : 50 ≤ n) {a b k : V} {st st' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 469 [a, b, k] st v st') :
    EmitOutC .float st.1 st'.1 v (fun rd => .data 58 93 [.data 105 34 [], .reg rd, a, b, k]) := by
  have hp' := hp
  isel_split hp hc h 469
  isel_inv [*, rule_inst_3290] at hm he
  rename_i hl
  exact vec_rrr_ok hp' hc (by omega) hl

include hp hc in
theorem addv_ok {n : Nat} (hn : 50 ≤ n) {a k : V} {st st' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 473 [a, k] st v st') :
    EmitOutC .float st.1 st'.1 v (fun rd => .data 58 97 [.data 114 0 [], .reg rd, a, k]) := by
  have hp' := hp
  isel_split hp hc h 473
  isel_inv [*, rule_inst_3311] at hm he
  rename_i hl
  exact vec_lanes_ok hp' hc (by omega) hl

end Terms

/-! ## Runs and results -/

section Run
variable {F : BitVec 64 → Prop} {isem : Sem}

theorem prun_rr_c (hR : Refines F isem) {i : MInst} {ms : List MInst} {ρ ρ' : Nat → CV}
    {d x : Nat} {c1 c2 : RegClass} {r : CV}
    (hops : i.operands = .ok #[⟨d, c1, .def, .late, .reg⟩, ⟨x, c2, .use, .early, .reg⟩])
    (hs : ∀ w, ispec i [ρ x] w = some ([r], w, .next)) (ht : PRun F isem ms (upd ρ d r) ρ') :
    PRun F isem (i :: ms) ρ ρ' :=
  prun_cons hR hops hs rfl ht

theorem prun_rrr_c (hR : Refines F isem) {i : MInst} {ms : List MInst} {ρ ρ' : Nat → CV}
    {d x y : Nat} {c1 c2 c3 : RegClass} {r : CV}
    (hops : i.operands = .ok #[⟨d, c1, .def, .late, .reg⟩, ⟨x, c2, .use, .early, .reg⟩,
      ⟨y, c3, .use, .early, .reg⟩])
    (hs : ∀ w, ispec i [ρ x, ρ y] w = some ([r], w, .next)) (ht : PRun F isem ms (upd ρ d r) ρ') :
    PRun F isem (i :: ms) ρ ρ' :=
  prun_cons hR hops hs rfl ht

end Run

section Shapes
variable {d x y : Nat} {c1 c2 c3 : RegClass}

theorem vd_movToFpu {sz : ScalarSize} : vdefs (.movToFpu (.vreg d c1) (.vreg x c2) sz) = [d] := rfl
theorem vu_movToFpu {sz : ScalarSize} : vuseNums (.movToFpu (.vreg d c1) (.vreg x c2) sz) = [x] :=
  rfl
theorem vd_vecMisc {op : VecMisc2} {sz : VectorSize} :
    vdefs (.vecMisc op (.vreg d c1) (.vreg x c2) sz) = [d] := rfl
theorem vu_vecMisc {op : VecMisc2} {sz : VectorSize} :
    vuseNums (.vecMisc op (.vreg d c1) (.vreg x c2) sz) = [x] := rfl
theorem vd_vecLanes {op : VecLanesOp} {sz : VectorSize} :
    vdefs (.vecLanes op (.vreg d c1) (.vreg x c2) sz) = [d] := rfl
theorem vu_vecLanes {op : VecLanesOp} {sz : VectorSize} :
    vuseNums (.vecLanes op (.vreg d c1) (.vreg x c2) sz) = [x] := rfl
theorem vd_vecRRR {op : VecALUOp} {sz : VectorSize} :
    vdefs (.vecRRR op (.vreg d c1) (.vreg x c2) (.vreg y c3) sz) = [d] := rfl
theorem vu_vecRRR {op : VecALUOp} {sz : VectorSize} :
    vuseNums (.vecRRR op (.vreg d c1) (.vreg x c2) (.vreg y c3) sz) = [x, y] := rfl
theorem vd_movFromVec {i : Nat} {sz : ScalarSize} :
    vdefs (.movFromVec (.vreg d c1) (.vreg x c2) i sz) = [d] := rfl
theorem vu_movFromVec {i : Nat} {sz : ScalarSize} :
    vuseNums (.movFromVec (.vreg d c1) (.vreg x c2) i sz) = [x] := rfl

end Shapes

set_option hygiene false in
/-- `vdefs`/`vuseNums` facts of concrete vector code. -/
macro "vec_facts" : tactic => `(tactic| (
  intro mi hmi e he
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmi
  rcases hmi with rfl | rfl | rfl | rfl | rfl <;> (
    simp only [vd_movToFpu, vu_movToFpu, vd_vecMisc, vu_vecMisc, vd_vecLanes, vu_vecLanes,
      vd_vecRRR, vu_vecRRR, vd_movFromVec, vu_movFromVec, List.mem_cons, List.mem_nil_iff,
      or_false] at he ⊢
    omega)))

set_option maxHeartbeats 4000000 in
theorem popcnt64_fin (X : CV) :
    (ofX ((((addvBytes (lo64 ((cntBytes (lo64 ((lo64 X).setWidth 128))).setWidth 128))).setWidth
      128).extractLsb' (8 * 0) 8).setWidth 64)).setWidth 64 = (X.setWidth 64).cpop := by
  simp only [ofX, lo64, addvBytes, cntBytes, byteOf]
  bv_decide

theorem variantNames_Popcnt_fb : (variantNames 151)[111]? = some "Popcnt" := rfl

section Rules
variable {F : BitVec 64 → Prop} {isem : Sem}

set_option maxHeartbeats 1000000 in
/-- **`popcnt_64`** (`lower.isle:2092`). -/
theorem popcnt_64_ok {p : Program} (hp : Data p) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOk isem MR env cp p rule_lower_2092 := by
  intro f ctx hctx ii info inst hi hc cfg hco m n st tr env' s1 out st' tr' hm hn hvb _hfirst
    hmatch heval
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 200 := ⟨n - 200, by omega⟩
  obtain ⟨ty, x, rfl, hety, -, hd, hhead⟩ := unary_front hp (cop := .popcnt) rfl hp.t2395
    term_2395_kind variantNames_Popcnt_fb rfl hctx hi hc (m := m' + 9) hmatch
  have hp' := hp
  cases hp
  fbrot_inv [*, rule_lower_2092] at hmatch heval
  have hii := Option.some.inj (hi.symm.trans ‹ctx.insts[ii]? = some _›)
  subst hii
  have hdat := ‹V.data 152 29 _ = info.data›
  rw [hd] at hdat
  simp only [hhead, Option.getD_some] at *
  simp only [V.data.injEq, List.cons.injEq, and_true, true_and] at hdat
  subst hdat
  have hty := ‹CTy.int 64 = CTy.int ty.width›
  simp only [CTy.int.injEq] at hty
  obtain ⟨rx, hrx, rfl, rfl⟩ :=
    (ctor_put_in_reg_iff ctx _ _ _ _).mp ‹externCtor ctx T.put_in_reg _ _ = _›
  obtain rfl := hctx.valueReg x _ hrx
  have hxlt := vreg_lt hvb hrx
  have h1 := ‹ApplyInternal _ _ _ _ 27 409 _ _ _ _›
  obtain ⟨rfl, m1, hm1, hs1⟩ := mov_to_fpu_ok hp' hco (by omega) (.inr rfl) h1
  have h2 := ‹ApplyInternal _ _ _ _ 27 524 _ _ _ _›
  obtain ⟨rfl, m2, hm2, hs2⟩ := vec_cnt_ok hp' hco (by omega) h2
  have h3 := ‹ApplyInternal _ _ _ _ 27 473 _ _ _ _›
  obtain ⟨rfl, m3, hm3, hs3⟩ := addv_ok hp' hco (by omega) h3
  have h4 := ‹ApplyInternal _ _ _ _ 27 414 _ _ _ _›
  obtain ⟨rfl, m4, hm4, hs4⟩ := mov_from_vec_ok hp' hco (by omega) h4
  have hO := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
  obtain ⟨rfl, hst⟩ := output_reg_ok hp' hco (by omega) hO
  rw [hs3] at hm4 hs4
  rw [hs2] at hm3 hs3 hm4 hs4
  rw [hs1] at hm2 hs2 hm3 hs3 hm4 hs4
  rename LState => st0
  have e1 : m1 = .movToFpu (.vreg st0.nextVreg .float) (.vreg x .int) .size64 :=
    Option.some.inj (hm1.symm.trans rfl)
  subst e1
  have e2 : m2 = .vecMisc .cnt (.vreg (st0.nextVreg + 1) .float) (.vreg st0.nextVreg .float)
      .size8x8 := Option.some.inj (hm2.symm.trans rfl)
  subst e2
  have e3 : m3 = .vecLanes .addv (.vreg (st0.nextVreg + 2) .float)
      (.vreg (st0.nextVreg + 1) .float) .size8x8 := Option.some.inj (hm3.symm.trans rfl)
  subst e3
  have e4 : m4 = .movFromVec (.vreg (st0.nextVreg + 3) .int) (.vreg (st0.nextVreg + 2) .float) 0
      .size8 := Option.some.inj (hm4.symm.trans rfl)
  subst e4
  have hst' := hst.trans hs4
  simp only at hst'
  rw [hs3]
  have hsh : CodeShapeU st0 st'
      [.movToFpu (.vreg st0.nextVreg .float) (.vreg x .int) .size64,
       .vecMisc .cnt (.vreg (st0.nextVreg + 1) .float) (.vreg st0.nextVreg .float) .size8x8,
       .vecLanes .addv (.vreg (st0.nextVreg + 2) .float) (.vreg (st0.nextVreg + 1) .float) .size8x8,
       .movFromVec (.vreg (st0.nextVreg + 3) .int) (.vreg (st0.nextVreg + 2) .float) 0 .size8]
      (st0.nextVreg + 3) [x] :=
    codeShapeU_of (k := 4) (by rw [hst']; simp only [LState.emit, LState.fresh]; apply Array.ext'; simp)
      (by rw [hst']; rfl) (by omega) (by vec_facts) (by vec_facts)
  refine ⟨_, hsh.emitted, _, rfl, ?_⟩
  refine lowerInstOk_one_fb hMR hsh.mono hsh.defs rfl ?_
  intro fr cm ρ vals cm' _ hvals hdfg ho
  have ho' : Clif.evalInst fr cm (.unary .popcnt ty x) = .ok (vals, cm') := ho
  obtain ⟨u, hu, rfl, rfl⟩ := evalInst_unary_ok ho'
  refine ⟨rfl, usesOk_of [x] hsh.uses (by simp [getAs_ok hu]), .inl hsh.res, _, _, rfl,
    prun_rr_c hR rfl (fun w => rfl) (prun_rr_c hR rfl (fun w => rfl)
      (prun_rr_c hR rfl (fun w => rfl) (prun_rr_c hR rfl (fun w => rfl) (prun_nil _)))), ?_⟩
  have hX : (ρ x).setWidth ty.width = u := hvals x _ (getAs_ok hu)
  cases ty <;> simp [Clif.Ty.width] at hty
  simp only [VHolds, upd, Clif.Sem.unary, Clif.Sem.popcnt, ↓reduceIte, Nat.left_eq_add,
    Nat.add_right_cancel_iff, Nat.add_eq_left, Nat.succ_ne_self, LState.emit, LState.fresh,
    Nat.add_left_cancel_iff, show (1 : Nat) ≠ 2 by decide, show (2 : Nat) ≠ 1 by decide,
    show (3 : Nat) ≠ 2 by decide, show (3 : Nat) ≠ 1 by decide, show (2 : Nat) ≠ 3 by decide]
  rw [← hX]
  exact popcnt64_fin (ρ x)

end Rules

end Backend.Proof
