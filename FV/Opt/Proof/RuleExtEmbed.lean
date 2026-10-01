import FV.Opt.Proof.RuleIcmpEmbed2

/-!
# Template variants for `extends.isle`, `shifts.isle`, `spaceship.isle`

- `opt_den_x`/`opt_node_x`: `opt_den`/`opt_node` that also close the width side condition of a
  made `ireduce` (`t.width < v.ty.width`, `evalNode_ireduce`) from a hypothesis or by deciding
  it at literal types. `opt_node`'s `repeat` works on the main goal only, so an open side
  condition stops it before the remaining operands.
- `rule_auto_x` / `rule_auto_xi` (with if-lets): `rule_auto_b` / `rule_auto_i` with these.
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt Clif

/-- A width side condition `a < b` of `evalNode_ireduce`/`uextend`/`sextend`. -/
macro "opt_width_side" : tactic => `(tactic| first
  | assumption
  | decide
  | (simp only [Ty.width] at *; omega))

syntax "opt_den_x" : tactic
syntax "opt_node_x" : tactic

open Lean Meta Elab Tactic in
/-- `opt_val_ty_subst`: for every hypothesis `h : a.ty = b.ty` between local `Val`s (two operands
the left-hand side requires to have one type), split both values and substitute the types, so
that the bit-vectors share a width before `opt_cases_ty`. -/
elab "opt_val_ty_subst" : tactic => do
  for _ in [0:4] do
    let g ← getMainGoal
    let found ← g.withContext do
      for d in ← getLCtx do
        if d.isImplementationDetail then continue
        let t ← instantiateMVars d.type
        if let some (_, l, r) := t.eq? then
          if l.isAppOfArity ``Clif.Val.ty 1 && r.isAppOfArity ``Clif.Val.ty 1 &&
              l.appArg!.isFVar && r.appArg!.isFVar && l.appArg! != r.appArg! then
            return some (d.fvarId, l.appArg!.fvarId!, r.appArg!.fvarId!)
      return none
    let some (h, a, b) := found | return
    let gs ← g.cases a
    let [s] := gs.toList | return
    let b := (s.subst.get b).fvarId!
    let h := (s.subst.get h).fvarId!
    let gs ← s.mvarId.cases b
    let [s] := gs.toList | return
    let h := (s.subst.get h).fvarId!
    let g ← s.mvarId.withContext do
      let hT ← whnfR (← instantiateMVars (← h.getType))
      let g ← s.mvarId.replaceLocalDeclDefEq h hT
      pure g
    let g ← g.withContext do
      let hT ← instantiateMVars (← h.getType)
      let some (_, l, r) := hT.eq? | return g
      let l ← whnfR l; let r ← whnfR r
      let g ← g.replaceLocalDeclDefEq h (← mkEq l r)
      if l.isFVar || r.isFVar then return (← subst g h) else return g
    replaceMainGoal [g]

set_option hygiene false in
macro_rules
  | `(tactic| opt_den_x) => `(tactic| first
      | (apply Valuation.le_trans hle1 hle3; assumption)
      | (apply GraphOk.make_val hG (by opt_P); opt_node_x)
      | (apply GraphOk.make_le hG (by opt_P); opt_den_x))

set_option hygiene false in
macro_rules
  | `(tactic| opt_node_x) => `(tactic| (
      simp only [evalNode_binary_iff, evalNode_unary, evalNode_icmp, evalNode_iconst,
        evalNode_select, evalNode_bitselect, evalNode_bmask, evalNode_uextend, evalNode_sextend,
        evalNode_ireduce,
        Clif.BinaryOp.isShift, Bool.false_eq_true, ite_false, ite_true, Clif.Frame.regs]
      repeat (first | (apply Exists.intro) | (apply And.intro) | opt_den_x | opt_width_side)
      all_goals (try rfl)))

/-! ### `Int` immediates as bit-vectors

The if-let conditions and immediates of shift-amount rules are `Int`s built from bit-vector
operands (`Rust.band64 (↑k.toNat) 7`, `Rust.asI64 …`). `int_bv` rewrites them into 64-bit
`BitVec` terms (and `Nat` comparisons of `toNat`s into `BitVec` comparisons) for `bv_decide`. -/

theorem band64_bv (a b : Int) :
    Rust.band64 a b = ((BitVec.ofInt 64 a &&& BitVec.ofInt 64 b).toNat : Int) := rfl
theorem bor64_bv (a b : Int) :
    Rust.bor64 a b = ((BitVec.ofInt 64 a ||| BitVec.ofInt 64 b).toNat : Int) := rfl
theorem bxor64_bv (a b : Int) :
    Rust.bxor64 a b = ((BitVec.ofInt 64 a ^^^ BitVec.ofInt 64 b).toNat : Int) := rfl
theorem asU64_bv (a : Int) : Rust.asU64 a = ((BitVec.ofInt 64 a).toNat : Int) := rfl
theorem asI64_bv (a : Int) : Rust.asI64 a = (BitVec.ofInt 64 a).toInt := rfl
theorem ofInt_natCast_toNat {w v : Nat} (x : BitVec v) :
    BitVec.ofInt w (x.toNat : Int) = x.setWidth w := by
  rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat]
theorem toNat_beq_toNat_wide {v u : Nat} (x : BitVec v) (y : BitVec u) :
    (x.toNat == y.toNat) = (x.setWidth (v + u) == y.setWidth (v + u)) := by
  have hx := x.isLt; have hy := y.isLt
  have h1 : 2 ^ v ≤ 2 ^ (v + u) := Nat.pow_le_pow_right (by decide) (by omega)
  have h2 : 2 ^ u ≤ 2 ^ (v + u) := Nat.pow_le_pow_right (by decide) (by omega)
  rw [Bool.eq_iff_iff]
  simp only [beq_iff_eq, BitVec.toNat_eq, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hx h1), Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hy h2)]
theorem toNat_le_toNat_wide {v u : Nat} (x : BitVec v) (y : BitVec u) :
    x.toNat ≤ y.toNat ↔ x.setWidth (v + u) ≤ y.setWidth (v + u) := by
  have hx := x.isLt; have hy := y.isLt
  have h1 : 2 ^ v ≤ 2 ^ (v + u) := Nat.pow_le_pow_right (by decide) (by omega)
  have h2 : 2 ^ u ≤ 2 ^ (v + u) := Nat.pow_le_pow_right (by decide) (by omega)
  simp only [BitVec.le_def, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hx h1), Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hy h2)]
theorem toNat_lt_toNat_wide {v u : Nat} (x : BitVec v) (y : BitVec u) :
    x.toNat < y.toNat ↔ x.setWidth (v + u) < y.setWidth (v + u) := by
  have hx := x.isLt; have hy := y.isLt
  have h1 : 2 ^ v ≤ 2 ^ (v + u) := Nat.pow_le_pow_right (by decide) (by omega)
  have h2 : 2 ^ u ≤ 2 ^ (v + u) := Nat.pow_le_pow_right (by decide) (by omega)
  simp only [BitVec.lt_def, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hx h1), Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hy h2)]
theorem natCast_le_lit {n k : Nat} :
    ((n : Int) ≤ no_index (OfNat.ofNat k : Int)) ↔ n ≤ OfNat.ofNat k := Int.ofNat_le
theorem natCast_lt_lit {n k : Nat} :
    ((n : Int) < no_index (OfNat.ofNat k : Int)) ↔ n < OfNat.ofNat k := Int.ofNat_lt
theorem lit_le_natCast {n k : Nat} :
    (no_index (OfNat.ofNat k : Int) ≤ (n : Int)) ↔ OfNat.ofNat k ≤ n := Int.ofNat_le
theorem lit_lt_natCast {n k : Nat} :
    (no_index (OfNat.ofNat k : Int) < (n : Int)) ↔ OfNat.ofNat k < n := Int.ofNat_lt
theorem natCast_beq_lit {n k : Nat} :
    ((n : Int) == no_index (OfNat.ofNat k : Int)) = (n == OfNat.ofNat k) := natCast_beq_natCast
theorem lit_beq_natCast {n k : Nat} :
    (no_index (OfNat.ofNat k : Int) == (n : Int)) = (OfNat.ofNat k == n) := natCast_beq_natCast
theorem lit_beq_toNat {w k : Nat} (x : BitVec w) (h : k < 2 ^ w) :
    (k == x.toNat) = (BitVec.ofNat w k == x) := by
  rw [Bool.eq_iff_iff]; simp only [beq_iff_eq, BitVec.toNat_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
theorem natCast_eq_lit {n k : Nat} :
    ((n : Int) = no_index (OfNat.ofNat k : Int)) ↔ n = OfNat.ofNat k := Int.ofNat_inj
theorem lit_eq_natCast {n k : Nat} :
    (no_index (OfNat.ofNat k : Int) = (n : Int)) ↔ OfNat.ofNat k = n := Int.ofNat_inj
theorem toNat_eq_lit {w k : Nat} (x : BitVec w) (h : k < 2 ^ w) :
    x.toNat = k ↔ x = BitVec.ofNat w k := by
  simp only [BitVec.toNat_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
theorem lit_eq_toNat {w k : Nat} (x : BitVec w) (h : k < 2 ^ w) :
    k = x.toNat ↔ BitVec.ofNat w k = x := by
  simp only [BitVec.toNat_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
theorem imm64OfBits_bv {w : Nat} (b : BitVec w) : imm64OfBits b = (b.setWidth 64).toInt := by
  simp only [imm64OfBits, Rust.asI64, ofInt_natCast_toNat]
/-- A signed immediate fact `x.toInt = k` (`iconst_s`) as a bit-vector equation. -/
theorem toInt_eq_iff_ofInt {w : Nat} (x : BitVec w) (k : Int) (h : (BitVec.ofInt w k).toInt = k) :
    x.toInt = k ↔ x = BitVec.ofInt w k := by
  constructor
  · intro hx; rw [← BitVec.toInt_inj, hx, h]
  · rintro rfl; exact h
theorem toNat_le_lit {w k : Nat} (x : BitVec w) (h : k < 2 ^ w) :
    x.toNat ≤ k ↔ x ≤ BitVec.ofNat w k := by
  simp only [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
theorem toNat_lt_lit {w k : Nat} (x : BitVec w) (h : k < 2 ^ w) :
    x.toNat < k ↔ x < BitVec.ofNat w k := by
  simp only [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
theorem lit_le_toNat {w k : Nat} (x : BitVec w) (h : k < 2 ^ w) :
    k ≤ x.toNat ↔ BitVec.ofNat w k ≤ x := by
  simp only [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
theorem lit_lt_toNat {w k : Nat} (x : BitVec w) (h : k < 2 ^ w) :
    k < x.toNat ↔ BitVec.ofNat w k < x := by
  simp only [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
theorem toNat_beq_lit {w k : Nat} (x : BitVec w) (h : k < 2 ^ w) :
    (x.toNat == k) = (x == BitVec.ofNat w k) := by
  rw [Bool.eq_iff_iff]; simp only [beq_iff_eq, BitVec.toNat_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- `Int` immediates and if-let conditions to `BitVec` (see above). -/
macro "int_bv" : tactic => `(tactic| simp (disch := decide) only [band64_bv, bor64_bv, bxor64_bv,
  asU64_bv, asI64_bv, ofInt_natCast_toNat, ofInt_toInt_signExtend, BitVec.ofInt_add, ofInt_sub',
  BitVec.ofInt_neg, BitVec.ofInt_mul, BitVec.ofInt_natCast, Int.toNat_natCast, BitVec.ofNat_toNat,
  BitVec.ofInt_ofNat, natCast_beq_natCast, natCast_beq_lit, lit_beq_natCast, lit_beq_toNat, toNat_beq_toNat,
  natCast_eq_lit, lit_eq_natCast, toNat_eq_lit, lit_eq_toNat, Int.natCast_inj, toInt_eq_iff_ofInt,
  imm64OfBits_bv, BitVec.toInt_inj, toNat_beq_toNat_wide,
  natCast_le_lit, natCast_lt_lit, lit_le_natCast, lit_lt_natCast, Int.ofNat_le, Int.ofNat_lt,
  toNat_le_lit, toNat_lt_lit, lit_le_toNat, lit_lt_toNat, toNat_beq_lit, toNat_le_toNat_wide,
  toNat_lt_toNat_wide, decide_eq_true_eq, beq_true, Int.reducePow, Int.reduceSub, Int.reduceAdd,
  Nat.reduceAdd, Nat.reducePow, Int.reduceToNat, ofClif_bits, Ty.width, BitVec.setWidth_eq] at *)

/-- `rule_bits_b` with `int_bv` before `bv_decide`. -/
macro "rule_bits_xb" : tactic => `(tactic| (
  try simp (disch := assumption) only [asU64_imm64OfBits, Int.natCast_eq_zero, Int.natCast_inj,
    toNat_eq_iff_ofNat, ofInt_imm64OfBits, bne_iff_ne, ne_eq, toNat_eq_zero_iff] at *
  opt_destruct
  all_goals subst_vars
  all_goals first
    | (simp only [val_some_eq, val_mk_same]; done)
    | rfl
    | (first | apply some_val_congr | apply val_congr | skip
       first
         | (simp only [Clif.Sem.binary, Clif.Sem.unary, Clif.Sem.iadd, Clif.Sem.imul, Clif.Sem.band,
              Clif.Sem.bor, Clif.Sem.bxor]
            ac_rfl)
         | (simp only [Clif.Sem.unary, bswap_bswap, popcnt_bswap, bitrev_bitrev, popcnt_bitrev]; done)
         | (opt_cases_val <;> opt_cases_ty <;> opt_widths <;> sem_simp_b <;> (try int_bv) <;>
            first | ac_rfl | bv_decide))))

set_option hygiene false in
macro "rule_finish_make_x" : tactic => `(tactic| (
  try dsimp only
  apply GraphOk.make_val hG (by opt_P)
  opt_node_x
  all_goals rule_bits_xb))

set_option hygiene false in
macro "rule_finish_var_x" : tactic => `(tactic| (
  try dsimp only
  apply Valuation.le_trans hle1 hle3
  opt_rw_lhs
  rule_bits_xb))

macro "rule_finish_x" : tactic => `(tactic| first | rule_finish_var_x | rule_finish_make_x)

set_option hygiene false in
/-- `rule_rhs` that also resolves the `Option` if-let results of internal constructors on the
right (`iconst_u ty k`: `if k ≤ ty_umax then some env else none`), keeping the condition. -/
syntax "rule_rhs_x" ("[" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|> Lean.Parser.Tactic.simpLemma),* "]")? : tactic
set_option hygiene false in
macro_rules
  | `(tactic| rule_rhs_x) => `(tactic| rule_rhs_x [])
  | `(tactic| rule_rhs_x [$ts,*]) => `(tactic| (
      opt_eval hev [$ts,*]
      repeat' (split at hev <;>
        (try (rename_i hq; opt_split_ite hq <;>
           (try simp only [Option.some.injEq, reduceCtorEq, Bool.false_eq_true, ite_false,
             ↓reduceIte] at hq) <;> (try subst hq))) <;>
        try opt_eval hev [$ts,*])
      all_goals (try (simp only [reduceCtorEq] at hev; done))
      all_goals (try simp only [Option.map_eq_some_iff, Option.map_eq_none_iff] at *)
      opt_destruct
      all_goals subst_vars
      all_goals (
        simp only [Except.ok.injEq, Prod.mk.injEq] at hev
        obtain ⟨rfl, rfl, rfl⟩ := hev
        simp only [List.mem_singleton, List.mem_cons, List.not_mem_nil, or_false, V.value.injEq,
          reduceCtorEq] at hm <;>
        subst hm)
      all_goals opt_types))

/-- `rule_auto_xi` with `rule_rhs_x`. -/
syntax "rule_auto_xr " ident ("[" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|> Lean.Parser.Tactic.simpLemma),* "]")? : tactic
set_option hygiene false in
macro_rules
  | `(tactic| rule_auto_xr $r:ident) => `(tactic| rule_auto_xr $r [])
  | `(tactic| rule_auto_xr $r:ident [$ts,*]) => `(tactic| (
      rule_intro $r
      rule_lhs hG
      all_goals (first | rule_no_iflets | rule_iflets)
      all_goals (rule_rhs_x [$ts,*]; opt_some_subst; (try opt_val_ty_subst); rule_finish_x)))

/-- `rule_auto_b` with `opt_node_x`. -/
syntax "rule_auto_x " ident ("[" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|> Lean.Parser.Tactic.simpLemma),* "]")? : tactic
set_option hygiene false in
macro_rules
  | `(tactic| rule_auto_x $r:ident) => `(tactic| rule_auto_x $r [])
  | `(tactic| rule_auto_x $r:ident [$ts,*]) => `(tactic| (
      rule_intro $r
      rule_no_iflets
      rule_lhs hG
      all_goals (rule_rhs [$ts,*]; opt_some_subst; (try opt_val_ty_subst); rule_finish_x)))

/-- `rule_auto_i` with `opt_node_x`. -/
syntax "rule_auto_xi " ident ("[" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|> Lean.Parser.Tactic.simpLemma),* "]")? : tactic
set_option hygiene false in
macro_rules
  | `(tactic| rule_auto_xi $r:ident) => `(tactic| rule_auto_xi $r [])
  | `(tactic| rule_auto_xi $r:ident [$ts,*]) => `(tactic| (
      rule_intro $r
      rule_lhs hG
      all_goals rule_iflets
      all_goals (rule_rhs [$ts,*]; opt_some_subst; (try opt_val_ty_subst); rule_finish_x)))

end Opt.Proof

/-! ## `iconcat` shift amounts (`shifts.isle` 139–143) -/

namespace Opt.Proof

open Isle Isle.Opt Clif

theorem append_toNat_mod {u : Nat} (b c : BitVec u) (k : Nat) (hk : k ∣ 2 ^ u) :
    (c ++ b).toNat % k = b.toNat % k := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt b.isLt, Nat.shiftLeft_eq]
  obtain ⟨j, hj⟩ := hk
  rw [hj, Nat.mul_left_comm, Nat.mul_add_mod]

/-- The low half of an `iconcat` operand, and the amount it gives every shift of a type `w`
(a power of two dividing `2 ^ t.width`). -/
theorem evalNode_iconcat_amt {fr : Frame} {mem : Mem} {t : Ty} {lo hi : ValueId} {a : Val}
    (h : evalNode fr mem (.iconcat t lo hi) = some a) :
    ∃ b : BitVec t.width, fr.regs lo = some ⟨t, b⟩ ∧
      ∀ w : Ty, Sem.shiftAmt w.width a.bits = Sem.shiftAmt w.width b := by
  rw [evalNode_eq_some] at h
  obtain ⟨m, h⟩ := h
  simp only [evalInst] at h
  cases ht : t.double? with
  | none => simp [ht, Res.ofOption] at h
  | some t2 =>
    simp only [ht, Res.ofOption, Res.ok_bind, getAs_bind_ok, pure, Res.ok.injEq, Prod.mk.injEq,
      List.cons.injEq, and_true] at h
    obtain ⟨b, hb, c, -, rfl, -⟩ := h
    refine ⟨b, hb, fun w => ?_⟩
    simp only [Sem.shiftAmt, Sem.iconcat, BitVec.toNat_setWidth]
    have hk : w.width ∣ 2 ^ t.width := by cases w <;> cases t <;> decide
    cases t <;> simp only [Ty.double?, Option.some.injEq, reduceCtorEq] at ht <;> subst ht <;>
      rw [Nat.mod_mod_of_dvd _ (by cases w <;> decide), append_toNat_mod b c _ hk]

theorem shift_amt_congr {op : BinaryOp} {w v v' : Nat} {x : BitVec w} {y : BitVec v}
    {y' : BitVec v'} (h : Sem.shiftAmt w y = Sem.shiftAmt w y') :
    Sem.shift op x y = Sem.shift op x y' := by
  cases op <;> simp only [Sem.shift, Sem.ishl, Sem.ushr, Sem.sshr, Sem.rotl, Sem.rotr, h]

set_option hygiene false in
/-- A shift whose amount is an `iconcat`, rewritten to shift by the low half. -/
macro "rule_auto_cat " r:ident : tactic => `(tactic| (
  rule_intro $r
  rule_no_iflets
  rule_lhs hG
  all_goals (rule_rhs; opt_some_subst)
  all_goals (
    obtain ⟨b, hb, hm⟩ := evalNode_iconcat_amt ‹evalNode _ _ (Clif.Inst.iconcat _ _ _) = some _›
    simp only [Clif.Frame.regs] at hb
    try dsimp only
    apply GraphOk.make_val hG (by opt_P)
    simp only [evalNode_binary_iff, Clif.BinaryOp.isShift, ite_true, Clif.Frame.regs]
    refine ⟨_, Valuation.le_trans hle1 hle3 _ _ ‹_›, _, Valuation.le_trans hle1 hle3 _ _ hb, _, ?_, rfl⟩
    rw [← shift_amt_congr (hm _)]
    assumption)))

end Opt.Proof

namespace Opt.Proof

open Isle Isle.Opt Clif

theorem tyMask_ofClif_i128 :
    Rust.tyMask (CTy.ofClif .i128) = throw "ty_mask: unimplemented for > 64 bits" := rfl
theorem panics_throw_bind {α β : Type} (e : String) (k : α → R β) :
    (panics (throw e : Rust.Panics α) >>= k) = (throw s!"panic: {e}" : R β) := rfl
theorem except_throw_bind {α β : Type} (e : String) (k : α → R β) :
    ((throw e : R α) >>= k) = (throw e : R β) := rfl
theorem toExt_throw {α : Type} (e : String) : toExt (throw e : R (Option α)) = .unmodeled e := rfl

/-- `rule_auto_xr` with every local `Val` split and every type split on `= .i128` before the
if-lets (`ty_mask`/`ty_umax` of an operand's type only evaluate at non-`i128` types). -/
syntax "rule_auto_xz " ident ("[" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|> Lean.Parser.Tactic.simpLemma),* "]")? : tactic
set_option hygiene false in
macro_rules
  | `(tactic| rule_auto_xz $r:ident) =>
    `(tactic| rule_auto_xz $r [tyMask_ofClif, tyMask_ofClif_i128, Rust.tyUmax, panics_throw_bind,
      except_throw_bind, toExt_throw])
  | `(tactic| rule_auto_xz $r:ident [$ts,*]) => `(tactic| (
      rule_intro $r
      rule_lhs hG
      all_goals (try opt_val_ty_subst)
      opt_cases_val
      all_goals opt_split_i128
      all_goals (first | rule_no_iflets | rule_iflets_c [$ts,*])
      all_goals (rule_rhs_x [$ts,*]; opt_some_subst; rule_finish_x)))

end Opt.Proof

namespace Opt.Proof

set_option hygiene false in
/-- `rule_rhs_x` that cases on every `typeOf` read of a made node's operand as soon as it
appears (`opt_split_typeof`, then `opt_types`), instead of after the whole right-hand side:
with two made `icmp`s feeding constructors (`spaceship_u`/`_s` under `sextend_maybe`) the
unsplit reads are copied into every later state and the term grows exponentially. -/
syntax "rule_rhs_y" ("[" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|> Lean.Parser.Tactic.simpLemma),* "]")? : tactic
set_option hygiene false in
macro_rules
  | `(tactic| rule_rhs_y) => `(tactic| rule_rhs_y [])
  | `(tactic| rule_rhs_y [$ts,*]) => `(tactic| (
      opt_norm hev [$ts,*]
      repeat' (first
        | (opt_split_typeof hev <;> (try opt_types) <;> try opt_norm hev [$ts,*])
        | (opt_unfold hev; opt_norm hev [$ts,*]))
      repeat' (split at hev <;>
        (try (rename_i hq; opt_split_ite hq <;>
           (try simp only [Option.some.injEq, reduceCtorEq, Bool.false_eq_true, ite_false,
             ↓reduceIte] at hq) <;> (try subst hq))) <;>
        try opt_eval hev [$ts,*])
      all_goals (try (simp only [reduceCtorEq] at hev; done))
      all_goals (try simp only [Option.map_eq_some_iff, Option.map_eq_none_iff] at *)
      opt_destruct
      all_goals subst_vars
      all_goals (
        simp only [Except.ok.injEq, Prod.mk.injEq] at hev
        obtain ⟨rfl, rfl, rfl⟩ := hev
        simp only [List.mem_singleton, List.mem_cons, List.not_mem_nil, or_false, V.value.injEq,
          reduceCtorEq] at hm <;>
        subst hm)
      all_goals opt_types))

/-- `rule_auto_xr` with `rule_rhs_y`. -/
syntax "rule_auto_y " ident ("[" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|> Lean.Parser.Tactic.simpLemma),* "]")? : tactic
set_option hygiene false in
macro_rules
  | `(tactic| rule_auto_y $r:ident) => `(tactic| rule_auto_y $r [])
  | `(tactic| rule_auto_y $r:ident [$ts,*]) => `(tactic| (
      rule_intro $r
      rule_lhs hG
      all_goals (first | rule_no_iflets | rule_iflets)
      all_goals (rule_rhs_y [$ts,*]; opt_some_subst; (try opt_val_ty_subst); rule_finish_x)))

end Opt.Proof

/-! ## Mask immediates of `shifts.isle` 27, 32, 41 (`imm64_shl ty -1 k`, `imm64_ushr ty (ty_mask ty) k`) -/

namespace Opt.Proof

open Isle Isle.Opt Clif

set_option linter.unusedSimpArgs false

@[opt_imm] theorem asI64_u64_max : Rust.asI64 18446744073709551615 = -1 := by decide

@[opt_imm] theorem imm64Shl_neg_one {t t' : Ty} (ht : t ≠ .i128) (ht' : t' ≠ .i128)
    (c : BitVec t'.width) :
    Rust.imm64Shl (CTy.ofClif t) (-1) (imm64OfBits c) =
      .ok (imm64OfBits (Sem.ishl (BitVec.allOnes t.width) c)) := by
  imm_pre [Rust.imm64Shl]
  simp only [Rust.band64, Rust.asU64, int_toNat_natCast, ofInt_mul_two_pow, shiftLeft_toNat']
  cases t <;> (try contradiction) <;> imm_cases t' c <;> simp (disch := decide) only [ishl_mask,
    Nat.reduceBEq, Bool.false_eq_true, reduceIte, Int.reduceSub, Int.reducePow, Nat.reduceSub] <;>
    imm_solve

@[opt_imm] theorem imm64Ushr_ty_mask {t t' : Ty} (ht : t ≠ .i128) (ht' : t' ≠ .i128)
    (c : BitVec t'.width) :
    Rust.imm64Ushr (CTy.ofClif t) (Rust.asI64 (2 ^ t.width - 1)) (imm64OfBits c) =
      .ok (imm64OfBits (Sem.ushr (BitVec.allOnes t.width) c)) := by
  imm_pre [Rust.imm64Ushr]
  simp only [Rust.band64, Rust.asU64, int_toNat_natCast, natCast_div_two_pow, ushiftRight_toNat']
  cases t <;> (try contradiction) <;> imm_cases t' c <;> simp (disch := decide) only [ushr_mask,
    Nat.reduceBEq, Bool.false_eq_true, reduceIte, Int.reduceSub, Int.reducePow, Nat.reduceSub,
    Ty.width] <;> imm_solve

end Opt.Proof
