import FV.Backend.Proof.IselCmpRoot

/-!
# Family C: `select` (2267) and integer min/max (1222/1224/1226/1228)

`lower_select ty c x y` on a condition of E: the flag instruction of `c` then `csel` into a
fresh vreg (`lower_select_cond`, integer types only).
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

theorem ofV_csel' (rd rn rm : Reg) (c : V) :
    MInst.ofV (.data 58 31 [.reg rd, c, .reg rn, .reg rm]) = c.cond?.map (.csel rd rn rm) := by
  have e1 : MInst.ofV (.data 58 31 [.reg rd, c, .reg rn, .reg rm]) =
      (do return .csel rd rn rm (← c.cond?)) := rfl
  rw [e1]; cases c.cond? <;> rfl

theorem ofV_cmpXzr {i : Nat} {sz : OperandSize} (hi : OperandSize.ofIdx? i = some sz) (k : Nat) :
    MInst.ofV (.data 58 2 [.data 59 10 [], .data 93 i [], .reg .xzr, .reg (.vreg k .int), .reg .xzr]) =
      some (cmpXzr sz k) := by
  have e : (V.data 93 i []).size? = OperandSize.ofIdx? i := rfl
  have e1 : MInst.ofV (.data 58 2 [.data 59 10 [], .data 93 i [], .reg .xzr, .reg (.vreg k .int), .reg .xzr]) =
      (do return .aluRRR .subS (← (V.data 93 i []).size?) .xzr (.vreg k .int) .xzr) := rfl
  rw [e1, e, hi]; rfl

section
variable {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)

set_option maxHeartbeats 4000000 in
include hp hc in
theorem lower_select_cond_ok {n : Nat} (hn : 60 ≤ n) {w : Nat} (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64)
    {mi cd : V} {x y : Nat} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 22 660 [.ty (.int w), .data 47 1 [mi], cd, .value x, .value y]
      s v s') :
    ∃ m1 rx ry c, MInst.ofV mi = some m1 ∧ ctx.valueReg? x = some rx ∧ ctx.valueReg? y = some ry ∧
      cd.cond? = some c ∧ v = .regs [(s.1.fresh .int).1] ∧
      s'.1 = (((s.1.fresh .int).2.emit m1).emit (.csel (s.1.fresh .int).1 rx ry c)) := by
  rcases hw with rfl | rfl | rfl | rfl <;>
  isel_split' hp hc h 660 <;>
  (try (isel_refute hp at hm; done))
  all_goals (try isel_refute hp at hm)
  all_goals try (exact absurd hm.1 (by decide))
  all_goals try (obtain ⟨_, _, ⟨_, h1, _⟩, _⟩ := hm; cases h1; done)
  all_goals isel_inv' hp [] at hm he
  all_goals
    obtain ⟨h0⟩ : Nonempty (externCtor ctx T.ty_int_ref_scalar_64 _ _ = _) := ⟨‹_›⟩
    cases h0
    isel_call hp hc [csel_ok, with_flags_ok]
    obtain ⟨h1⟩ : Nonempty (MInst.ofV (.data 58 31 _) = _) := ⟨‹_›⟩
    rw [ofV_csel', Option.map_eq_some_iff] at h1
    obtain ⟨c, hcd, rfl⟩ := h1
    obtain ⟨h2⟩ : Nonempty ((_ : LState × Array RuleId).fst = ((_ : LState × Array RuleId).fst.fresh RegClass.int).snd) := ⟨‹_›⟩
    exact ⟨_, ‹_›, _, ‹_›, _, ‹_›, c, hcd, rfl, by rw [h2]⟩

set_option maxHeartbeats 8000000 in
include hp hc in
theorem lower_select_ok {n : Nat} (hn : 100 ≤ n) {w : Nat} (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64)
    {c : V} {P : Nat → Prop} (hsh : CondShape c P) {x y : Nat} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 22 659 [.ty (.int w), c, .value x, .value y] s v s') :
    ∃ m cond rx ry, CondFlag cmpXzr c m cond ∧ ctx.valueReg? x = some rx ∧ ctx.valueReg? y = some ry ∧
      v = .regs [(s.1.fresh .int).1] ∧
      s'.1 = (((s.1.fresh .int).2.emit m).emit (.csel (s.1.fresh .int).1 rx ry cond)) := by
  rcases hsh with ⟨k, i, sz, rfl, hi, -⟩ | ⟨k, i, sz, rfl, hi, -⟩ | ⟨mi, m, cond, rfl, hm0, -⟩ <;>
  isel_split' hp hc h 659 <;>
  (try (isel_refute hp at hm; done))
  all_goals try (first
    | (obtain ⟨m', s1, h2⟩ := hpre rule_inst_5320 (List.mem_cons_self ..)
       revert h2
       isel_eval [rule_inst_5320, hp.t2236, hp.t2237, hp.t2238]
       simp
       done)
    | (obtain ⟨m', s1, h2⟩ := hpre rule_inst_5322 (List.mem_cons_of_mem _ (List.mem_cons_self ..))
       revert h2
       isel_eval [rule_inst_5322, hp.t2236, hp.t2237, hp.t2238]
       simp
       done)
    | (obtain ⟨m', s1, h2⟩ := hpre rule_inst_5324 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
       revert h2
       isel_eval [rule_inst_5324, hp.t2236, hp.t2237, hp.t2238]
       simp
       done)
    )
  all_goals isel_inv' hp [] at hm he
  all_goals isel_call hp hc [cmp_ok]
  all_goals
    obtain ⟨h660⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 22 660 _ _ _ _) := ⟨‹_›⟩
    obtain ⟨m1, rx, ry, c, hm1, hrx, hry, hc', rfl, hs⟩ :=
      lower_select_cond_ok hp hc (hn := by omega) (by decide) h660
    try simp only at hs
    clear h660
    subst_vars
    first
      | (rw [ofV_cmpXzr hi] at hm1; cases hm1
         rw [V.cond?_data, cond_ofIdx_0] at hc'; cases hc'
         exact ⟨_, _, .inl ⟨k, i, sz, rfl, hi, rfl, rfl⟩, _, hrx, _, hry, by simp_all, by simp_all⟩)
      | (rw [ofV_cmpXzr hi] at hm1; cases hm1
         rw [V.cond?_data, cond_ofIdx_1] at hc'; cases hc'
         exact ⟨_, _, .inr (.inl ⟨k, i, sz, rfl, hi, rfl, rfl⟩), _, hrx, _, hry, by simp_all, by simp_all⟩)
      | (rw [hm0] at hm1; cases hm1
         rw [V.cond?_data, cond_ofIdx_idx] at hc'; cases hc'
         exact ⟨_, _, .inr (.inr ⟨mi, rfl, hm0⟩), _, hrx, _, hry, by simp_all, by simp_all⟩)

end

end Backend.Proof
