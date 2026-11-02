import FV.Opt.Proof.LegalPat
import FV.Opt.Proof.KernelBV

/-!
# The canonical patterns of `Opt.Legal` compute the `i128` operations

Each theorem runs one canonical pattern (`Opt.Legal.Pat.*`) on symbolic `i64` halves and states
that its outputs are the halves of the `Clif.Sem` result at `i128` (`Out128`). The runs are
computed by `simp` (`pat_eval`); the remaining bit-vector identities are closed by
kernel-checked proofs, per operation:

* bitwise operations and copies: the halves of `++` (`lo_app`, `hi_app`, `BitVec.and_append`, …);
* additive operations, comparisons, selects, masks, extensions: the `toNat` arithmetic of the
  halves, after a case split on the conditions, by `omega` (`nat_route`);
* `clz`/`ctz`/`cls`/`popcnt`/`bitrev`/`bswap`: lemmas on the halves (`clz_app`, `clz_xor_sshr`,
  `BitVec.toNat_cpop_append`, `BitVec.reverse_append`), `bswap` bit by bit;
* shifts by a constant: the halves of a 128-bit shift by a `Nat` amount (`shl_lo`, …), proved
  bit by bit (`bit_cases`);
* the multiplication: the 128-bit product by the cross products (`mul128`), by the `toNat`
  arithmetic.

None of these realizes auxiliary declarations such as `Clif.Ty.enumToBitVec` in this module:
`FV.Backend.Proof.IselCmpExt` realizes it too, and two modules realizing it cannot be imported
together (`FV.E2E.Legal`).
-/

namespace Opt.Legal

open Clif

/-- The outputs at `a`/`b` are the low/high halves of `X`. -/
def Out128 (ρ : Regs) (a b : ValueId) (X : BitVec 128) : Prop :=
  ρ a = some ⟨.i64, X.extractLsb' 0 64⟩ ∧ ρ b = some ⟨.i64, X.extractLsb' 64 64⟩

@[simp] theorem as?_i64 (x : BitVec 64) : (Val.mk .i64 x).as? .i64 = some x := Val.as?_mk _ _
@[simp] theorem as?_i8 (x : BitVec 8) : (Val.mk .i8 x).as? .i8 = some x := Val.as?_mk _ _
@[simp] theorem as?_i16 (x : BitVec 16) : (Val.mk .i16 x).as? .i16 = some x := Val.as?_mk _ _
@[simp] theorem as?_i32 (x : BitVec 32) : (Val.mk .i32 x).as? .i32 = some x := Val.as?_mk _ _
@[simp] theorem as?_i128 (x : BitVec 128) : (Val.mk .i128 x).as? .i128 = some x :=
  Val.as?_mk _ _

@[simp] theorem mk_i64_inj (a b : BitVec 64) : (Val.mk .i64 a = Val.mk .i64 b) ↔ a = b :=
  ⟨fun h => eq_of_heq (Val.mk.inj h).2, fun h => h ▸ rfl⟩
@[simp] theorem mk_i16_inj (a b : BitVec 16) : (Val.mk .i16 a = Val.mk .i16 b) ↔ a = b :=
  ⟨fun h => eq_of_heq (Val.mk.inj h).2, fun h => h ▸ rfl⟩
@[simp] theorem mk_i32_inj (a b : BitVec 32) : (Val.mk .i32 a = Val.mk .i32 b) ↔ a = b :=
  ⟨fun h => eq_of_heq (Val.mk.inj h).2, fun h => h ▸ rfl⟩
@[simp] theorem mk_i8_inj (a b : BitVec 8) : (Val.mk .i8 a = Val.mk .i8 b) ↔ a = b :=
  ⟨fun h => eq_of_heq (Val.mk.inj h).2, fun h => h ▸ rfl⟩
@[simp] theorem mk_i128_inj (a b : BitVec 128) : (Val.mk .i128 a = Val.mk .i128 b) ↔ a = b :=
  ⟨fun h => eq_of_heq (Val.mk.inj h).2, fun h => h ▸ rfl⟩

/-- The `i64` value `x` (canonical inputs). -/
abbrev V64 (x : BitVec 64) : Val := ⟨.i64, x⟩

@[simp] theorem width_i8 : Ty.i8.width = 8 := rfl
@[simp] theorem width_i16 : Ty.i16.width = 16 := rfl
@[simp] theorem width_i32 : Ty.i32.width = 32 := rfl
@[simp] theorem width_i64 : Ty.i64.width = 64 := rfl
@[simp] theorem width_i128 : Ty.i128.width = 128 := rfl

theorem bool8_eq (b : Bool) : Sem.bool8 b = (bif b then 1#8 else 0#8) := by cases b <;> rfl

theorem select_bif {v w : Nat} (c : BitVec v) (x y : BitVec w) :
    Sem.select c x y = bif c != 0 then x else y := by
  unfold Sem.select Sem.truthy; cases (c != 0) <;> rfl

theorem bmask_bif {v w : Nat} (x : BitVec v) :
    (Sem.bmask x : BitVec w) = bif x != 0 then BitVec.allOnes w else 0 := by
  unfold Sem.bmask Sem.truthy; cases (x != 0) <;> rfl

theorem iabs_bif {w : Nat} (x : BitVec w) : Sem.iabs x = bif x.msb then -x else x := by
  unfold Sem.iabs; cases x.msb <;> rfl

theorem cls_bif {w : Nat} (x : BitVec w) :
    Sem.cls x = bif x.msb then (~~~x).clz - 1 else x.clz - 1 := by
  unfold Sem.cls; cases x.msb <;> rfl

theorem smin_bif {w : Nat} (x y : BitVec w) : Sem.smin x y = bif x.sle y then x else y := by
  unfold Sem.smin; cases x.sle y <;> rfl
theorem smax_bif {w : Nat} (x y : BitVec w) : Sem.smax x y = bif y.sle x then x else y := by
  unfold Sem.smax; cases y.sle x <;> rfl
theorem umin_bif {w : Nat} (x y : BitVec w) : Sem.umin x y = bif x.ule y then x else y := by
  unfold Sem.umin; cases x.ule y <;> rfl
theorem umax_bif {w : Nat} (x y : BitVec w) : Sem.umax x y = bif y.ule x then x else y := by
  unfold Sem.umax; cases y.ule x <;> rfl

/-! ## Kernel-checked finishers -/

theorem lo_app (a b : BitVec 64) : (a ++ b).extractLsb' 0 64 = b :=
  BitVec.extractLsb'_append_eq_right

example : (0xAB#64 ++ 0xCD#64).extractLsb' 0 64 = 0xCD#64 := lo_app _ _

theorem hi_app (a b : BitVec 64) : (a ++ b).extractLsb' 64 64 = a :=
  BitVec.extractLsb'_append_eq_left

example : (0xAB#64 ++ 0xCD#64).extractLsb' 64 64 = 0xAB#64 := hi_app _ _

/-! The halves of `++` at the width `128` of the `i128` operations (the generic lemmas, at
`w + v`, do not unify with `128`). -/

theorem not_app (a b : BitVec 64) : (~~~(a ++ b) : BitVec 128) = ~~~a ++ ~~~b := BitVec.not_append

example : (~~~(0#64 ++ 0#64) : BitVec 128) = ~~~0#64 ++ ~~~0#64 := not_app _ _

theorem and_app (a b c d : BitVec 64) : ((a ++ b) &&& (c ++ d) : BitVec 128) = (a &&& c) ++ (b &&& d) :=
  BitVec.and_append

example : ((1#64 ++ 2#64) &&& (3#64 ++ 4#64) : BitVec 128) = (1#64 &&& 3#64) ++ (2#64 &&& 4#64) :=
  and_app _ _ _ _

theorem or_app (a b c d : BitVec 64) : ((a ++ b) ||| (c ++ d) : BitVec 128) = (a ||| c) ++ (b ||| d) :=
  BitVec.or_append

example : ((1#64 ++ 2#64) ||| (3#64 ++ 4#64) : BitVec 128) = (1#64 ||| 3#64) ++ (2#64 ||| 4#64) :=
  or_app _ _ _ _

theorem xor_app (a b c d : BitVec 64) : ((a ++ b) ^^^ (c ++ d) : BitVec 128) = (a ^^^ c) ++ (b ^^^ d) :=
  BitVec.xor_append

example : ((1#64 ++ 2#64) ^^^ (3#64 ++ 4#64) : BitVec 128) = (1#64 ^^^ 3#64) ++ (2#64 ^^^ 4#64) :=
  xor_app _ _ _ _

theorem getLsbD_app (a b : BitVec 64) (i : Nat) :
    (a ++ b : BitVec 128).getLsbD i = if i < 64 then b.getLsbD i else a.getLsbD (i - 64) :=
  BitVec.getLsbD_append

example : (1#64 ++ 0#64 : BitVec 128).getLsbD 64 = true := by rw [getLsbD_app]; decide

theorem msb_app (a b : BitVec 64) : (a ++ b : BitVec 128).msb = a.msb := by
  rw [BitVec.msb_append]; rfl

example : (1#64 ++ 0#64 : BitVec 128).msb = false := by rw [msb_app]; decide

theorem append_toNat (a b : BitVec 64) : (a ++ b).toNat = a.toNat * 2^64 + b.toNat := by
  rw [BitVec.toNat_append, Nat.shiftLeft_eq, Nat.mul_comm, Nat.two_pow_add_eq_or_of_lt b.isLt]

theorem toNat_lo (X : BitVec 128) : (X.extractLsb' 0 64).toNat = X.toNat % 2^64 := by
  simp [BitVec.extractLsb'_toNat]

example : ((0x1#64 ++ 0x2#64).extractLsb' 0 64).toNat = (0x1#64 ++ 0x2#64).toNat % 2^64 :=
  toNat_lo _

theorem toNat_hi (X : BitVec 128) : (X.extractLsb' 64 64).toNat = X.toNat / 2^64 % 2^64 := by
  simp [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

example : ((0x1#64 ++ 0x2#64).extractLsb' 64 64).toNat = (0x1#64 ++ 0x2#64).toNat / 2^64 % 2^64 :=
  toNat_hi _

theorem xor_m1 (x : BitVec 64) : x ^^^ 18446744073709551615#64 = ~~~x := BitVec.xor_allOnes

example : 5#64 ^^^ 18446744073709551615#64 = ~~~5#64 := xor_m1 _

/-- Signed `<` by the `toNat`s. -/
theorem slt_nat {w : Nat} (hw : 0 < w) (x y : BitVec w) :
    x.slt y = decide ((x.toNat < 2^(w-1) ∧ y.toNat < 2^(w-1) ∧ x.toNat < y.toNat) ∨
      (2^(w-1) ≤ x.toNat ∧ (y.toNat < 2^(w-1) ∨ x.toNat < y.toNat))) := by
  have hp : 2^w = 2 * 2^(w-1) := by rw [← Nat.pow_succ']; congr 1; omega
  have hx := x.isLt; have hy := y.isLt
  rw [Bool.eq_iff_iff, BitVec.slt_iff_toInt_lt, BitVec.toInt_eq_toNat_cond,
    BitVec.toInt_eq_toNat_cond, decide_eq_true_eq]
  generalize 2^(w-1) = P at *
  rw [hp]; rw [hp] at hx hy
  split <;> split <;> omega

example : (255#8).slt 1#8 = true := by rw [slt_nat (by decide)]; decide

/-- Signed `≤` by the `toNat`s. -/
theorem sle_nat {w : Nat} (hw : 0 < w) (x y : BitVec w) :
    x.sle y = decide ((x.toNat < 2^(w-1) ∧ y.toNat < 2^(w-1) ∧ x.toNat ≤ y.toNat) ∨
      (2^(w-1) ≤ x.toNat ∧ (y.toNat < 2^(w-1) ∨ x.toNat ≤ y.toNat))) := by
  have hp : 2^w = 2 * 2^(w-1) := by rw [← Nat.pow_succ']; congr 1; omega
  have hx := x.isLt; have hy := y.isLt
  rw [Bool.eq_iff_iff, BitVec.sle_iff_toInt_le, BitVec.toInt_eq_toNat_cond,
    BitVec.toInt_eq_toNat_cond, decide_eq_true_eq]
  generalize 2^(w-1) = P at *
  rw [hp]; rw [hp] at hx hy
  split <;> split <;> omega

example : (255#8).sle 255#8 = true := by rw [sle_nat (by decide)]; decide

theorem b8_or (a b : Bool) :
    ((bif a then 1#8 else 0#8) ||| bif b then 1#8 else 0#8) = bif (a || b) then 1#8 else 0#8 := by
  cases a <;> cases b <;> rfl

example : ((bif true then 1#8 else 0#8) ||| bif false then 1#8 else 0#8) = 1#8 := b8_or _ _

theorem b8_and (a b : Bool) :
    ((bif a then 1#8 else 0#8) &&& bif b then 1#8 else 0#8) = bif (a && b) then 1#8 else 0#8 := by
  cases a <;> cases b <;> rfl

example : ((bif true then 1#8 else 0#8) &&& bif false then 1#8 else 0#8) = 0#8 := b8_and _ _

theorem b8_ne0 (a : Bool) : ((bif a then 1#8 else 0#8) != 0) = a := by
  cases a <;> rfl

example : ((bif true then 1#8 else 0#8) != 0) = true := b8_ne0 _

open Lean Meta Elab Tactic in
/-- Add `x.toNat < 2 ^ w` for every bit-vector local `x`. -/
elab "bv_bounds" : tactic => do
  let g ← getMainGoal
  let g ← g.withContext do
    let mut g := g
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let ty ← whnfR (← instantiateMVars d.type)
      if ty.isAppOfArity ``BitVec 1 then
        let pf ← mkAppM ``BitVec.isLt #[d.toExpr]
        g ← (·.2) <$> (← g.assert `hb (← inferType pf) pf).intro1P
    pure g
  replaceMainGoal [g]

/-- An identity of `toNat`-arithmetic bit vectors (`+`, `-`, `~~~`, `++`, halves, extensions,
comparisons, `bif`s of them): split on the conditions, then `omega` on the `toNat`s. -/
macro "nat_route" : tactic => `(tactic| (
  (try simp only [b8_or, b8_and, b8_ne0, xor_m1, BitVec.or_self] at *)
  (try simp only [Bool.cond_eq_ite] at *)
  (repeat' split) <;>
  (first | apply BitVec.eq_of_toNat_eq | rw [Bool.eq_iff_iff] | skip) <;>
  simp only [beq_iff_eq, bne_iff_ne, ne_eq, Bool.not_eq_true, Bool.or_eq_true, Bool.and_eq_true,
    BitVec.toNat_eq, BitVec.ult_eq_decide, BitVec.ule_eq_decide, slt_nat (show 0 < 64 by decide),
    slt_nat (show 0 < 128 by decide), sle_nat (show 0 < 64 by decide),
    sle_nat (show 0 < 128 by decide), BitVec.msb_eq_decide, decide_eq_true_eq,
    decide_eq_false_iff_not, toNat_lo, toNat_hi, append_toNat, BitVec.toNat_add, BitVec.toNat_sub,
    BitVec.toNat_neg, BitVec.toNat_not, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    BitVec.toNat_ofNatLT, Bool.false_eq_true, not_false_eq_true, Nat.reducePow, Nat.reduceSub,
    Nat.reduceMod, Nat.add_one_sub_one, BitVec.toNat_zero, BitVec.ofNat_eq_ofNat, BitVec.toNat_allOnes] at * <;>
  bv_bounds <;> omega))

open Lean Meta Elab Tactic in
/-- Close an equation by `rfl`/`omega`, else by congruence (to depth `d`) down to `Nat`
equations closed by `omega`. -/
partial def eqLeafCore (d : Nat) : TacticM Unit := do
  if ← tryTactic (evalTactic (← `(tactic| first | rfl | trivial | omega))) then return
  if d = 0 then throwError m!"eq_leaf: failed{indentExpr (← getMainTarget)}"
  evalTactic (← `(tactic| congr 1))
  for g in ← getGoals do
    setGoals [g]
    eqLeafCore (d - 1)
  setGoals []

/-- Close an equation by congruence down to `omega` (`eqLeafCore`). -/
elab "eq_leaf" : tactic => eqLeafCore 4

open Lean Meta Elab Tactic in
/-- Close a per-bit goal over index arithmetic: evaluate the decided conditions (`omega`), drop
out-of-range bits, case split on the first open condition, repeat; leaves by `eqLeafCore`. -/
partial def bitCasesCore : TacticM Unit := do
  let _ ← tryTactic (evalTactic (← `(tactic| simp (disch := omega) only [decide_eq_true,
    decide_eq_false, ite_eq_left, ite_eq_right, BitVec.getLsbD_of_ge, Bool.false_or, Bool.or_false,
    Bool.and_false, Bool.false_and, Bool.true_and, Bool.and_true, Bool.true_or, Bool.or_true,
    Bool.not_true, Bool.not_false, Bool.or_self, Bool.and_self])))
  if (← getGoals).isEmpty then return
  let s ← saveState
  try
    eqLeafCore 3
    if (← getGoals).isEmpty then return
  catch _ => s.restore
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let c? := t.find? fun s => !s.hasLooseBVars &&
    (s.isAppOfArity ``Decidable.decide 2 || s.isAppOfArity ``ite 5)
  let some c := c? | throwError m!"bit_cases: stuck{indentExpr t}"
  let p := if c.isAppOfArity ``Decidable.decide 2 then c.appFn!.appArg! else c.getArg! 1
  let (pos, neg) ← g.byCases p
  for g' in [pos.mvarId, neg.mvarId] do
    setGoals [g']
    bitCasesCore
  setGoals []

/-- Close a per-bit goal over index arithmetic (`bitCasesCore`). -/
elab "bit_cases" : tactic => bitCasesCore

/-- A bit-vector identity bit by bit, symbolic index, then `bit_cases`. -/
macro "bit_route" : tactic => `(tactic| (
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_sshiftRight, BitVec.getLsbD_signExtend, BitVec.getLsbD_setWidth,
    msb_app, BitVec.msb_append, BitVec.msb_eq_getLsbD_last, getLsbD_app, BitVec.getLsbD_append,
    BitVec.getLsbD_or,
    BitVec.getLsbD_and, BitVec.getLsbD_xor, BitVec.getLsbD_not, BitVec.getLsbD_zero, hi, decide_true,
    Bool.true_and, Nat.zero_add, Nat.reducePow, Nat.reduceMod]
  bit_cases))

/-- The halves of bitwise operations on `++`. -/
macro "app_fin" : tactic => `(tactic|
  (simp only [BitVec.not_append, BitVec.and_append, BitVec.or_append, BitVec.xor_append, not_app,
    and_app, or_app, xor_app, lo_app, hi_app, BitVec.or_self]; done))

/-! ### `clz`, `ctz`, `cls`, `popcnt`, `bitrev` of halves -/

/-- The bits of `clz`: zeros above, a one at `w - 1 - clz` (if `x ≠ 0`). -/
private theorem clz_bits {w : Nat} (x : BitVec w) :
    x.clz.toNat ≤ w ∧ (∀ i, w - x.clz.toNat ≤ i → x.getLsbD i = false) ∧
      (x.clz.toNat < w → x.getLsbD (w - 1 - x.clz.toNat) = true) := by
  have hle : x.clz.toNat ≤ w := by
    have h := BitVec.clz_le (x := x)
    rw [BitVec.le_def] at h
    have : ((w : Nat) : BitVec w).toNat = w := by
      simp [Nat.mod_eq_of_lt (Nat.lt_two_pow_self)]
    omega
  refine ⟨hle, ?_, ?_⟩
  · intro i hi
    have h := BitVec.getLsbD_false_of_clzAuxRec (x := x) (n := w - 1)
      (fun i hi => BitVec.getLsbD_of_ge x i (by omega)) (i - (w - x.clz.toNat))
    have hc : x.clz = x.clzAuxRec (w - 1) := rfl
    rw [← hc] at h
    rwa [show w - x.clz.toNat + (i - (w - x.clz.toNat)) = i by omega] at h
  · intro hc
    apply BitVec.getLsbD_true_clz_of_ne_zero (by omega)
    intro hx
    subst hx
    have := (BitVec.clz_eq_iff_eq_zero (x := 0#w)).2 rfl
    have h2 : (BitVec.clz 0#w).toNat = w := by
      rw [this]; simp [Nat.mod_eq_of_lt (Nat.lt_two_pow_self)]
    omega

/-- `clz` is determined by the bits. -/
private theorem clz_of_bits {w : Nat} (x : BitVec w) (c : Nat) (hc : c ≤ w)
    (hz : ∀ i, w - c ≤ i → x.getLsbD i = false) (ht : c < w → x.getLsbD (w - 1 - c) = true) :
    x.clz.toNat = c := by
  obtain ⟨hle, hz', ht'⟩ := clz_bits x
  rcases Nat.lt_trichotomy x.clz.toNat c with h | h | h
  · have := ht' (by omega); rw [hz _ (by omega)] at this; cases this
  · exact h
  · have := ht (by omega)
    rw [hz' _ (by omega)] at this; cases this

private theorem clz_app (a b : BitVec 64) :
    (a ++ b).clz.toNat = if a = 0#64 then 64 + b.clz.toNat else a.clz.toNat := by
  obtain ⟨hla, hza, hta⟩ := clz_bits a
  obtain ⟨hlb, hzb, htb⟩ := clz_bits b
  split
  · next ha =>
    subst ha
    apply clz_of_bits _ _ (by omega)
    · intro i hi
      rw [BitVec.getLsbD_append]
      split
      · exact hzb _ (by omega)
      · simp
    · intro hc
      rw [BitVec.getLsbD_append, ite_eq_left (by omega)]
      rw [show 64 + 64 - 1 - (64 + b.clz.toNat) = 64 - 1 - b.clz.toNat by omega]
      exact htb (by omega)
  · next ha =>
    have hca : a.clz.toNat < 64 := by
      apply Nat.lt_of_le_of_ne hla
      intro h
      apply ha
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      rw [hza i (by omega)]; simp
    apply clz_of_bits _ _ (by omega)
    · intro i hi
      rw [BitVec.getLsbD_append, ite_eq_right (by omega)]
      exact hza _ (by omega)
    · intro _
      rw [BitVec.getLsbD_append, ite_eq_right (by omega)]
      rw [show 64 + 64 - 1 - a.clz.toNat - 64 = 64 - 1 - a.clz.toNat by omega]
      exact hta hca

private theorem clz_le64 (b : BitVec 64) : b.clz.toNat ≤ 64 := (clz_bits b).1

private theorem clz128_lo (a b : BitVec 64) :
    (a ++ b).clz.extractLsb' 0 64 = bif a != 0#64 then a.clz else 64#64 + b.clz := by
  apply BitVec.eq_of_toNat_eq
  have := clz_le64 b
  rw [toNat_lo, clz_app]
  by_cases ha : a = 0#64
  · simp [ha]; (try omega)
  · simp [ha]; have := clz_le64 a; (try omega)

private theorem clz128_hi (a b : BitVec 64) : (a ++ b).clz.extractLsb' 64 64 = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  have := clz_le64 b; have := clz_le64 a
  rw [toNat_hi, clz_app]
  split <;> simp <;> (try omega)

private theorem ctz_app (a b : BitVec 64) : (a ++ b).ctz = (b.reverse ++ a.reverse).clz := by
  rw [BitVec.ctz, BitVec.reverse_append, BitVec.cast_eq]

private theorem ctz128_lo (a b : BitVec 64) :
    (a ++ b).ctz.extractLsb' 0 64 = bif b != 0#64 then b.ctz else 64#64 + a.ctz := by
  rw [ctz_app, clz128_lo]
  have : (b.reverse != 0#64) = (b != 0#64) := by
    simp only [bne]; congr 1
    rw [Bool.eq_iff_iff]; simp only [beq_iff_eq, BitVec.reverse_eq_zero_iff]
  rw [this]; rfl

private theorem ctz128_hi (a b : BitVec 64) : (a ++ b).ctz.extractLsb' 64 64 = 0#64 := by
  rw [ctz_app, clz128_hi]

private theorem cpop128_lo (a b : BitVec 64) : (a ++ b).cpop.extractLsb' 0 64 = b.cpop + a.cpop := by
  apply BitVec.eq_of_toNat_eq
  have := BitVec.toNat_cpop_le a; have := BitVec.toNat_cpop_le b
  rw [toNat_lo, BitVec.toNat_cpop_append, BitVec.toNat_add]
  omega

private theorem cpop128_hi (a b : BitVec 64) : (a ++ b).cpop.extractLsb' 64 64 = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  have := BitVec.toNat_cpop_le a; have := BitVec.toNat_cpop_le b
  rw [toNat_hi, BitVec.toNat_cpop_append]
  simp only [BitVec.toNat_ofNat]
  omega

private theorem rev128_lo (a b : BitVec 64) : (a ++ b).reverse.extractLsb' 0 64 = a.reverse := by
  rw [BitVec.reverse_append, BitVec.cast_eq, lo_app]

private theorem rev128_hi (a b : BitVec 64) : (a ++ b).reverse.extractLsb' 64 64 = b.reverse := by
  rw [BitVec.reverse_append, BitVec.cast_eq, hi_app]

/-- With the top bit clear, `x ^^^ (x >>>ₛ 1)` has the leading zeros of `x`. -/
private theorem clz_xor_sshr_of_msb {w : Nat} (x : BitVec w) (hm : x.msb = false) :
    (x ^^^ x.sshiftRight 1).clz.toNat = x.clz.toNat := by
  obtain ⟨hle, hz, ht⟩ := clz_bits x
  apply clz_of_bits _ _ hle
  · intro i hi
    rw [BitVec.getLsbD_xor, BitVec.getLsbD_sshiftRight, hz i hi, hm]
    by_cases h : 1 + i < w
    · rw [ite_eq_left h, hz (1 + i) (by omega)]; simp
    · rw [ite_eq_right h]; simp
  · intro hc
    rw [BitVec.getLsbD_xor, BitVec.getLsbD_sshiftRight, ht hc, hm]
    by_cases h : 1 + (w - 1 - x.clz.toNat) < w
    · rw [ite_eq_left h, hz _ (show w - x.clz.toNat ≤ 1 + (w - 1 - x.clz.toNat) by omega)]
      simp [show ¬ w ≤ w - 1 - x.clz.toNat by omega]
    · rw [ite_eq_right h]; simp [show ¬ w ≤ w - 1 - x.clz.toNat by omega]

private theorem xor_sshr_not {w : Nat} (x : BitVec w) :
    x ^^^ x.sshiftRight 1 = ~~~x ^^^ (~~~x).sshiftRight 1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_sshiftRight, BitVec.getLsbD_not, BitVec.msb_not,
    show 0 < w by omega, hi, decide_true, Bool.true_and, show ¬ w ≤ i by omega, decide_false,
    Bool.not_false]
  split <;> simp [*]

/-- `cls` as a leading-zero count: `clz (x ^^^ (x >>>ₛ 1))`. -/
private theorem clz_xor_sshr {w : Nat} (hw : 0 < w) (x : BitVec w) :
    (x ^^^ x.sshiftRight 1).clz = bif x.msb then (~~~x).clz else x.clz := by
  cases hm : x.msb
  · exact BitVec.eq_of_toNat_eq (clz_xor_sshr_of_msb x hm)
  · rw [xor_sshr_not]
    exact BitVec.eq_of_toNat_eq (clz_xor_sshr_of_msb _ (by simp [hm, hw]))

private theorem clz_xor_sshr_pos {w : Nat} (hw : 0 < w) (x : BitVec w) :
    0 < (x ^^^ x.sshiftRight 1).clz.toNat := by
  have hm : (x ^^^ x.sshiftRight 1).msb = false := by
    rw [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_xor, BitVec.getLsbD_sshiftRight,
      ← BitVec.msb_eq_getLsbD_last]
    simp [show ¬ 1 + (w - 1) < w by omega, show ¬ w ≤ w - 1 by omega]
  rw [BitVec.msb_eq_decide, decide_eq_false_iff_not] at hm
  rcases Nat.eq_zero_or_pos (x ^^^ x.sshiftRight 1).clz.toNat with h | h
  · exact absurd ((BitVec.clz_eq_zero_iff hw).1 h) hm
  · exact h

/-- The source of `cls` at `i128` as `clz (X ^^^ (X >>>ₛ 1)) - 1`, the operand by halves. -/
private theorem cls128_eq (x1 x0 : BitVec 64) :
    (bif (x1 ++ x0).msb then (~~~(x1 ++ x0)).clz - 1 else (x1 ++ x0).clz - 1) =
      ((x1 ^^^ x1.sshiftRight 1) ++ (x0 ^^^ (x0 >>> 1 ||| x1 <<< 63))).clz - 1 := by
  have e2 : (x1 ++ x0) ^^^ (x1 ++ x0).sshiftRight 1 =
      (x1 ^^^ x1.sshiftRight 1) ++ (x0 ^^^ (x0 >>> 1 ||| x1 <<< 63)) := by
    bit_route
  rw [← e2, clz_xor_sshr (by decide)]
  cases (x1 ++ x0).msb <;> rfl

private theorem cls128_pos (x1 x0 : BitVec 64) :
    0 < ((x1 ^^^ x1.sshiftRight 1) ++ (x0 ^^^ (x0 >>> 1 ||| x1 <<< 63))).clz.toNat := by
  have h := clz_xor_sshr_pos (by decide) (x1 ++ x0)
  have e2 : (x1 ++ x0) ^^^ (x1 ++ x0).sshiftRight 1 =
      (x1 ^^^ x1.sshiftRight 1) ++ (x0 ^^^ (x0 >>> 1 ||| x1 <<< 63)) := by
    bit_route
  rwa [e2] at h

private theorem cls128_lo (x1 x0 : BitVec 64) :
    (bif (x1 ++ x0).msb then (~~~(x1 ++ x0)).clz - 1 else (x1 ++ x0).clz - 1).extractLsb' 0 64 =
      (bif x1 ^^^ x1.sshiftRight 1 != 0#64 then (x1 ^^^ x1.sshiftRight 1).clz
        else 64#64 + (x0 ^^^ (x0 >>> 1 ||| x1 <<< 63)).clz) - 1#64 := by
  rw [cls128_eq, ← clz128_lo]
  have := cls128_pos x1 x0
  generalize ((x1 ^^^ x1.sshiftRight 1) ++ (x0 ^^^ (x0 >>> 1 ||| x1 <<< 63))).clz = Z at *
  apply BitVec.eq_of_toNat_eq
  have := Z.isLt
  simp only [toNat_lo, BitVec.toNat_sub, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat]
  omega

private theorem cls128_hi (x1 x0 : BitVec 64) :
    (bif (x1 ++ x0).msb then (~~~(x1 ++ x0)).clz - 1 else (x1 ++ x0).clz - 1).extractLsb' 64 64 =
      0#64 := by
  rw [cls128_eq]
  have := cls128_pos x1 x0
  have := (clz_bits ((x1 ^^^ x1.sshiftRight 1) ++ (x0 ^^^ (x0 >>> 1 ||| x1 <<< 63)))).1
  generalize ((x1 ^^^ x1.sshiftRight 1) ++ (x0 ^^^ (x0 >>> 1 ||| x1 <<< 63))).clz = Z at *
  apply BitVec.eq_of_toNat_eq
  simp only [toNat_hi, BitVec.toNat_sub, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat]
  omega

/-- `Sem.bswap` bit by bit, at each concrete index. -/
macro "bswap_fin" : tactic => `(tactic| (
  apply BitVec.eq_of_getLsbD_eq
  idx_split
  all_goals (simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_extractLsb', getLsbD_app]; simp)))

/-- The `Clif.Sem` definitions, unfolded to bit-vector operations. -/
macro "sem_bv" : tactic => `(tactic| simp only [Sem.unary, Sem.binary, Sem.shift, Sem.iadd,
  Sem.isub, Sem.imul, Sem.ineg, Sem.band, Sem.bor, Sem.bxor, Sem.bnot, Sem.bitselect,
  Sem.clz, Sem.ctz, Sem.popcnt, Sem.bitrev, Sem.ishl, Sem.ushr, Sem.sshr, Sem.rotl, Sem.rotr,
  Sem.shiftAmt, Sem.uextend, Sem.sextend, Sem.ireduce, Sem.icmp, Sem.intcc, bool8_eq,
  select_bif, bmask_bif, iabs_bif, cls_bif, smin_bif, smax_bif, umin_bif, umax_bif,
  BitVec.toNat_ofInt, BitVec.toNat_ofNat, width_i8, width_i16, width_i32, width_i64, width_i128])

/-- Compute a canonical run. -/
macro "pat_eval" : tactic => `(tactic| simp (config := { maxSteps := 4000000 }) [Regs.setMany_cons, Regs.setMany_nil, Pat.unary, Pat.binary, Pat.cmp, Pat.icmp, Pat.cond,
  Pat.select128c, Pat.select128, Pat.selectc, Pat.bitselect, Pat.bmaskEmit, Pat.bmask128c,
  Pat.bmask128, Pat.bmaskc, Pat.extend, Pat.ireduce, Pat.copy2, Pat.shiftNarrow, S, K, bin,
  runPat, evalInst, dframe, canon, Frame.getAs, Frame.get, Regs.set, Res.ofOption,
  BinaryOp.isShift, Sem.shift, bind, Res.bind, Res.check, width_i8, width_i16, width_i32, width_i64,
  width_i128, Out128])

set_option maxHeartbeats 4000000

/-! ## Unary -/

theorem pat_bnot (xl xh : BitVec 64) : ∃ ρ, runPat (canon [V64 xl, V64 xh]) (Pat.unary .bnot) =
    some ρ ∧ Out128 ρ 2 3 (Sem.unary .bnot (xh ++ xl)) := by
  pat_eval
  simp only [Sem.unary, Sem.bnot]
  constructor <;> app_fin

theorem pat_ineg (xl xh : BitVec 64) : ∃ ρ, runPat (canon [V64 xl, V64 xh]) (Pat.unary .ineg) =
    some ρ ∧ Out128 ρ 2 3 (Sem.unary .ineg (xh ++ xl)) := by
  pat_eval
  simp only [Sem.unary, Sem.ineg, Sem.binary, Sem.bxor, Sem.iadd, Sem.uextend, Sem.icmp,
    bool8_eq, Sem.intcc]
  constructor <;> nat_route

theorem pat_unary (op : UnaryOp) (xl xh : BitVec 64) :
    ∃ ρ, runPat (canon [V64 xl, V64 xh]) (Pat.unary op) = some ρ ∧
      Out128 ρ 2 3 (Sem.unary op (xh ++ xl)) := by
  cases op
  case ineg => exact pat_ineg xl xh
  case bnot => exact pat_bnot xl xh
  case iabs => pat_eval; sem_bv; constructor <;> nat_route
  case clz =>
    pat_eval; sem_bv
    simp only [b8_ne0, clz128_lo, clz128_hi]
    trivial
  case ctz =>
    pat_eval; sem_bv
    simp only [b8_ne0, ctz128_lo, ctz128_hi]
    trivial
  case cls =>
    pat_eval; sem_bv
    simp only [b8_ne0, Nat.reducePow, Nat.reduceMod, cls128_lo, cls128_hi]
    trivial
  case popcnt =>
    pat_eval; sem_bv
    simp only [cpop128_lo, cpop128_hi]
    trivial
  case bitrev =>
    pat_eval; sem_bv
    simp only [rev128_lo, rev128_hi]
    trivial
  case bswap =>
    pat_eval
    simp only [Sem.unary, Sem.bswap, List.range, List.range.loop, List.foldl]
    constructor <;> bswap_fin

/-! ## Binary -/

theorem pat_binary {op : BinaryOp} {pat : List Stmt} (h : Pat.binary op = some pat)
    (hm : op ≠ .imul) (xl xh yl yh : BitVec 64) :
    ∃ ρ, runPat (canon [V64 xl, V64 xh, V64 yl, V64 yh]) pat = some ρ ∧
      Out128 ρ 4 5 (Sem.binary op (xh ++ xl) (yh ++ yl)) := by
  cases op <;> simp only [Pat.binary, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    (try exact absurd rfl hm) <;> (pat_eval; sem_bv; constructor <;> first | app_fin | nat_route)

theorem pat_icmp (cc : IntCC) (xl xh yl yh : BitVec 64) :
    ∃ ρ, runPat (canon [V64 xl, V64 xh, V64 yl, V64 yh]) (Pat.icmp cc) = some ρ ∧
      ρ 4 = some ⟨.i8, Sem.icmp cc (xh ++ xl) (yh ++ yl)⟩ := by
  cases cc <;> (pat_eval; sem_bv; nat_route)

/-! ## Overflow-flag arithmetic -/

theorem slt0_msb (z : BitVec 64) : z.slt 0#64 = z.msb := by
  rw [Bool.eq_iff_iff]
  simp only [slt_nat (show 0 < 64 by decide), BitVec.msb_eq_decide, decide_eq_true_eq,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.add_one_sub_one]
  bv_bounds; omega

theorem msb128_hi (Z : BitVec 128) : Z.msb = (Z.extractLsb' 64 64).msb := by
  rw [Bool.eq_iff_iff]
  simp only [BitVec.msb_eq_decide, decide_eq_true_eq, toNat_hi, Nat.add_one_sub_one,
    Nat.reducePow]
  bv_bounds; omega

/-- The high half of an `i128` sum, as `Pat.addPair` computes it. -/
theorem add128_hi (xl xh yl yh : BitVec 64) : (xh ++ xl + (yh ++ yl)).extractLsb' 64 64 =
    xh + yh + BitVec.zeroExtend 64 (bif (xl + yl).ult xl then 1#8 else 0#8) := by
  nat_route

/-- The high half of an `i128` difference, as `Pat.subPair` computes it. -/
theorem sub128_hi (xl xh yl yh : BitVec 64) : (xh ++ xl - (yh ++ yl)).extractLsb' 64 64 =
    xh - yh - BitVec.zeroExtend 64 (bif xl.ult (xl - yl) then 1#8 else 0#8) := by
  nat_route

/-- `*_overflow` at `i128`: the wrapped result's halves at `4`/`5`, the flag at `6`. -/
theorem pat_overflow {op : OverflowOp} {pat : List Stmt} (h : Pat.overflow op = some pat)
    (xl xh yl yh : BitVec 64) :
    ∃ ρ, runPat (canon [V64 xl, V64 xh, V64 yl, V64 yh]) pat = some ρ ∧
      Out128 ρ 4 5 (Sem.overflow op (xh ++ xl) (yh ++ yl)).1 ∧
      ρ 6 = some (Val.ofBool (Sem.overflow op (xh ++ xl) (yh ++ yl)).2) := by
  cases op <;> simp only [Pat.overflow, Option.some.injEq, reduceCtorEq] at h <;> subst h
  case uaddOverflow =>
    simp only [Pat.addPair, List.cons_append, List.nil_append, Sem.overflow, Sem.uaddOverflow,
      BitVec.uaddOverflow, Val.ofBool]
    pat_eval; sem_bv
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;> nat_route
  case usubOverflow =>
    simp only [Pat.subPair, List.cons_append, List.nil_append, Sem.overflow, Sem.usubOverflow,
      BitVec.usubOverflow_eq, BitVec.lt_def, Val.ofBool]
    pat_eval; sem_bv
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;> nat_route
  case saddOverflow =>
    simp only [Pat.addPair, Pat.signOvf, List.cons_append, List.nil_append, Sem.overflow,
      Sem.saddOverflow, BitVec.saddOverflow_eq, Val.ofBool]
    pat_eval; sem_bv
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · nat_route
    · nat_route
    · rw [msb128_hi (xh ++ xl + (yh ++ yl)), add128_hi, msb_app, msb_app]
      simp only [slt0_msb]
      generalize xh.msb = a; generalize yh.msb = b
      generalize (xh + yh + BitVec.zeroExtend 64 (bif (xl + yl).ult xl then 1#8 else 0#8)).msb = c
      cases a <;> cases b <;> cases c <;> decide
  case ssubOverflow =>
    simp only [Pat.subPair, Pat.signOvf, List.cons_append, List.nil_append, Sem.overflow,
      Sem.ssubOverflow, BitVec.ssubOverflow_eq, Val.ofBool]
    pat_eval; sem_bv
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · nat_route
    · nat_route
    · rw [msb128_hi (xh ++ xl - (yh ++ yl)), sub128_hi, msb_app, msb_app]
      simp only [slt0_msb]
      generalize xh.msb = a; generalize yh.msb = b
      generalize (xh - yh - BitVec.zeroExtend 64 (bif xl.ult (xl - yl) then 1#8 else 0#8)).msb = c
      cases a <;> cases b <;> cases c <;> decide

/-! ## Selects, `bmask`, conditions -/

theorem pat_cond (lo hi : BitVec 64) :
    ∃ ρ, runPat (canon [V64 lo, V64 hi]) Pat.cond = some ρ ∧
      ρ 2 = some ⟨.i8, Sem.bool8 (Sem.truthy (hi ++ lo))⟩ := by
  pat_eval; sem_bv; simp only [Sem.truthy]; nat_route

theorem pat_select128c (cl ch xl xh yl yh : BitVec 64) :
    ∃ ρ, runPat (canon [V64 cl, V64 ch, V64 xl, V64 xh, V64 yl, V64 yh]) Pat.select128c =
      some ρ ∧ Out128 ρ 6 7 (Sem.select (ch ++ cl) (xh ++ xl) (yh ++ yl)) := by
  pat_eval; sem_bv; constructor <;> nat_route

theorem pat_select128 (c : Val) (xl xh yl yh : BitVec 64) :
    ∃ ρ, runPat (canon [c, V64 xl, V64 xh, V64 yl, V64 yh]) Pat.select128 = some ρ ∧
      Out128 ρ 5 6 (Sem.select c.bits (xh ++ xl) (yh ++ yl)) := by
  pat_eval; sem_bv
  cases (c.bits != 0) <;> simp <;> constructor <;> app_fin

theorem pat_selectc (t : Ty) (cl ch : BitVec 64) (x y : BitVec t.width) :
    ∃ ρ, runPat (canon [V64 cl, V64 ch, ⟨t, x⟩, ⟨t, y⟩]) (Pat.selectc t) = some ρ ∧
      ρ 4 = some ⟨t, Sem.select (ch ++ cl) x y⟩ := by
  pat_eval
  simp only [Sem.binary, Sem.bor, Sem.icmp, Sem.intcc, bool8_eq]
  have : ((bif cl != 0#64 then 1#8 else 0#8) ||| (bif ch != 0#64 then 1#8 else 0#8) !=
      (0 : BitVec 8)) = (ch ++ cl != (0 : BitVec 128)) := by nat_route
  unfold Sem.select Sem.truthy
  rw [this]

theorem pat_bitselect (cl ch xl xh yl yh : BitVec 64) :
    ∃ ρ, runPat (canon [V64 cl, V64 ch, V64 xl, V64 xh, V64 yl, V64 yh]) Pat.bitselect =
      some ρ ∧ Out128 ρ 6 7 (Sem.bitselect (ch ++ cl) (xh ++ xl) (yh ++ yl)) := by
  pat_eval; sem_bv; constructor <;> app_fin

theorem pat_bmask128c (xl xh : BitVec 64) :
    ∃ ρ, runPat (canon [V64 xl, V64 xh]) Pat.bmask128c = some ρ ∧
      Out128 ρ 2 3 (Sem.bmask (xh ++ xl)) := by
  pat_eval; sem_bv; constructor <;> nat_route

theorem pat_bmask128 (x : Val) :
    ∃ ρ, runPat (canon [x]) Pat.bmask128 = some ρ ∧ Out128 ρ 1 2 (Sem.bmask x.bits) := by
  pat_eval; sem_bv
  cases (x.bits != 0) <;> simp <;> constructor <;> nat_route

theorem pat_bmaskc (t : Ty) (hi : t.isInt = true) (xl xh : BitVec 64) :
    ∃ ρ, runPat (canon [V64 xl, V64 xh]) (Pat.bmaskc t) = some ρ ∧
      ρ 2 = some ⟨t, Sem.bmask (xh ++ xl)⟩ := by
  cases t <;> simp at hi <;> (pat_eval; sem_bv; nat_route)

/-! ## Width changes and copies -/

theorem pat_extend64 (op : ExtendOp) (x : BitVec 64) :
    ∃ ρ, runPat (canon [V64 x]) (Pat.extend op true) = some ρ ∧
      Out128 ρ 1 2 (match op with
        | .uextend => Sem.uextend 128 x | .sextend => Sem.sextend 128 x) := by
  cases op <;> (pat_eval; sem_bv; constructor <;> first | nat_route | bit_route)

theorem pat_extend8 (op : ExtendOp) (x : BitVec 8) :
    ∃ ρ, runPat (canon [⟨.i8, x⟩]) (Pat.extend op false) = some ρ ∧
      Out128 ρ 1 2 (match op with
        | .uextend => Sem.uextend 128 x | .sextend => Sem.sextend 128 x) := by
  cases op <;> (pat_eval; sem_bv; constructor <;> first | nat_route | bit_route)

theorem pat_extend16 (op : ExtendOp) (x : BitVec 16) :
    ∃ ρ, runPat (canon [⟨.i16, x⟩]) (Pat.extend op false) = some ρ ∧
      Out128 ρ 1 2 (match op with
        | .uextend => Sem.uextend 128 x | .sextend => Sem.sextend 128 x) := by
  cases op <;> (pat_eval; sem_bv; constructor <;> first | nat_route | bit_route)

theorem pat_extend32 (op : ExtendOp) (x : BitVec 32) :
    ∃ ρ, runPat (canon [⟨.i32, x⟩]) (Pat.extend op false) = some ρ ∧
      Out128 ρ 1 2 (match op with
        | .uextend => Sem.uextend 128 x | .sextend => Sem.sextend 128 x) := by
  cases op <;> (pat_eval; sem_bv; constructor <;> first | nat_route | bit_route)

theorem pat_extendN (op : ExtendOp) (t : Ty) (hi : t.isInt = true) (ht : t.width < 64)
    (x : BitVec t.width) :
    ∃ ρ, runPat (canon [⟨t, x⟩]) (Pat.extend op false) = some ρ ∧
      Out128 ρ 1 2 (match op with
        | .uextend => Sem.uextend 128 x | .sextend => Sem.sextend 128 x) := by
  cases t
  · exact pat_extend8 op x
  · exact pat_extend16 op x
  · exact pat_extend32 op x
  all_goals simp [Ty.width] at ht hi

theorem pat_ireduce (t : Ty) (hi : t.isInt = true) (ht : t.width < 128) (xl xh : BitVec 64) :
    ∃ ρ, runPat (canon [V64 xl]) (Pat.ireduce t) = some ρ ∧
      ρ 1 = some ⟨t, Sem.ireduce t.width (xh ++ xl)⟩ := by
  cases t <;> simp only [Ty.width] at ht <;> simp at hi <;> (try omega) <;>
    (pat_eval; sem_bv; nat_route)

theorem pat_copy2 (a b : BitVec 64) :
    ∃ ρ, runPat (canon [V64 a, V64 b]) Pat.copy2 = some ρ ∧
      ρ 2 = some (V64 a) ∧ ρ 3 = some (V64 b) := by
  pat_eval; sem_bv; constructor <;> exact BitVec.or_self

/-! ## Constant shifts -/

theorem ishl64 (x b : BitVec 64) : Sem.ishl x b = x <<< (b % 64#64) := by
  simp only [Sem.ishl, Sem.shiftAmt, BitVec.shiftLeft_eq', BitVec.toNat_umod]; rfl
theorem ushr64 (x b : BitVec 64) : Sem.ushr x b = x >>> (b % 64#64) := by
  simp only [Sem.ushr, Sem.shiftAmt, BitVec.ushiftRight_eq', BitVec.toNat_umod]; rfl
theorem sshr64 (x b : BitVec 64) : Sem.sshr x b = x.sshiftRight' (b % 64#64) := by
  simp only [Sem.sshr, Sem.shiftAmt, BitVec.sshiftRight', BitVec.toNat_umod]; rfl

theorem kn_toNat {n : Nat} (h : n < 128) : (BitVec.ofNat 128 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
theorem ofNat_n {n : Nat} (h : n < 128) :
    BitVec.ofNat 64 n = (BitVec.ofNat 128 n).setWidth 64 := by
  apply BitVec.eq_of_toNat_eq; simp <;> omega
theorem ofNat_64sub {n : Nat} (h : n ≤ 64) :
    BitVec.ofNat 64 (64 - n) = 64#64 - (BitVec.ofNat 128 n).setWidth 64 := by
  apply BitVec.eq_of_toNat_eq; simp <;> omega
theorem ofNat_sub64 {n : Nat} (h1 : 64 ≤ n) (h2 : n < 128) :
    BitVec.ofNat 64 (n - 64) = (BitVec.ofNat 128 n).setWidth 64 - 64#64 := by
  apply BitVec.eq_of_toNat_eq; simp <;> omega
theorem ofNat_64subsub {n : Nat} (h1 : 64 ≤ n) (h2 : n < 128) :
    BitVec.ofNat 64 (64 - (n - 64)) = 128#64 - (BitVec.ofNat 128 n).setWidth 64 := by
  apply BitVec.eq_of_toNat_eq; simp <;> omega
theorem kn_lt {n c : Nat} (h : n < c) (hc : c < 128) : BitVec.ofNat 128 n < BitVec.ofNat 128 c := by
  rw [BitVec.lt_def, kn_toNat (by omega), kn_toNat hc]; exact h
theorem kn_le {n c : Nat} (h : c ≤ n) (hn : n < 128) : BitVec.ofNat 128 c ≤ BitVec.ofNat 128 n := by
  rw [BitVec.le_def, kn_toNat (by omega), kn_toNat hn]; exact h

/-! ### The halves of a 128-bit shift by a `Nat` amount -/

theorem shl_lo (xl xh : BitVec 64) (n : Nat) :
    ((xh ++ xl) <<< n).extractLsb' 0 64 = if n < 64 then xl <<< n else 0#64 := by
  by_cases hn : n < 64 <;> simp only [hn, ite_true, ite_false] <;> bit_route

example : ((0#64 ++ 1#64) <<< 1).extractLsb' 0 64 = 2#64 := by
  rw [shl_lo]; decide

theorem shl_hi (xl xh : BitVec 64) (n : Nat) :
    ((xh ++ xl) <<< n).extractLsb' 64 64 =
      if n < 64 then xh <<< n ||| xl >>> (64 - n) else xl <<< (n - 64) := by
  by_cases hn : n < 64 <;> simp only [hn, ite_true, ite_false] <;> bit_route

example : ((0#64 ++ 1#64) <<< 64).extractLsb' 64 64 = 1#64 := by
  rw [shl_hi]; decide

theorem ushr_lo (xl xh : BitVec 64) (n : Nat) :
    ((xh ++ xl) >>> n).extractLsb' 0 64 =
      if n < 64 then xl >>> n ||| xh <<< (64 - n) else xh >>> (n - 64) := by
  by_cases hn : n < 64 <;> simp only [hn, ite_true, ite_false] <;> bit_route

example : ((1#64 ++ 0#64) >>> 64).extractLsb' 0 64 = 1#64 := by
  rw [ushr_lo]; decide

theorem ushr_hi (xl xh : BitVec 64) (n : Nat) :
    ((xh ++ xl) >>> n).extractLsb' 64 64 = if n < 64 then xh >>> n else 0#64 := by
  by_cases hn : n < 64 <;> simp only [hn, ite_true, ite_false] <;> bit_route

example : ((2#64 ++ 0#64) >>> 1).extractLsb' 64 64 = 1#64 := by
  rw [ushr_hi]; decide

theorem sshr_lo (xl xh : BitVec 64) (n : Nat) :
    ((xh ++ xl).sshiftRight n).extractLsb' 0 64 =
      if n < 64 then xl >>> n ||| xh <<< (64 - n) else xh.sshiftRight (n - 64) := by
  by_cases hn : n < 64 <;> simp only [hn, ite_true, ite_false] <;> bit_route

example : ((1#64 ++ 0#64).sshiftRight 64).extractLsb' 0 64 = 1#64 := by
  rw [sshr_lo]; decide

theorem sshr_hi (xl xh : BitVec 64) (n : Nat) :
    ((xh ++ xl).sshiftRight n).extractLsb' 64 64 =
      if n < 64 then xh.sshiftRight n else xh.sshiftRight 63 := by
  by_cases hn : n < 64 <;> simp only [hn, ite_true, ite_false] <;> bit_route

example : ((2#64 ++ 0#64).sshiftRight 1).extractLsb' 64 64 = 1#64 := by
  rw [sshr_hi]; decide

theorem getLsbD_idx {w : Nat} (x : BitVec w) {i j : Nat} (h : i = j) :
    x.getLsbD i = x.getLsbD j := by
  rw [h]

theorem rotl_lo (xl xh : BitVec 64) (n : Nat) (hn : n < 128) :
    ((xh ++ xl).rotateLeft n).extractLsb' 0 64 =
      if n < 64 then xl <<< n ||| xh >>> (64 - n) else xh <<< (n - 64) ||| xl >>> (128 - n) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_rotateLeft, BitVec.getLsbD_append,
    hi, decide_true, Bool.true_and, Nat.zero_add, Nat.mod_eq_of_lt (show n < 64 + 64 by omega)]
  by_cases h2 : n < 64
  · simp only [h2, ite_true, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_ushiftRight, hi, decide_true, Bool.true_and]
    by_cases h1 : i < n
    · simp only [h1, ite_true, show ¬ (64 + 64 - n + i < 64) by omega, ite_false,
        decide_true, Bool.not_true, Bool.false_and, Bool.false_or]
      exact getLsbD_idx _ (by omega)
    · simp only [h1, ite_false, show i < 64 + 64 by omega, show i - n < 64 by omega,
        decide_true, decide_false, Bool.not_false, Bool.true_and, ite_true,
        BitVec.getLsbD_of_ge xh (64 - n + i) (by omega), Bool.or_false]
  · simp only [h2, ite_false, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_ushiftRight, hi, decide_true, Bool.true_and, show i < n by omega]
    by_cases h3 : i < n - 64
    · simp only [show 64 + 64 - n + i < 64 by omega, ite_true, h3, decide_true, Bool.not_true,
        Bool.false_and, Bool.false_or]
    · simp only [show ¬ (64 + 64 - n + i < 64) by omega, ite_false, h3, decide_false,
        Bool.not_false, Bool.true_and, BitVec.getLsbD_of_ge xl (128 - n + i) (by omega),
        Bool.or_false]
      exact getLsbD_idx _ (by omega)

theorem rotl_hi (xl xh : BitVec 64) (n : Nat) (hn : n < 128) :
    ((xh ++ xl).rotateLeft n).extractLsb' 64 64 =
      if n < 64 then xh <<< n ||| xl >>> (64 - n) else xl <<< (n - 64) ||| xh >>> (128 - n) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_rotateLeft, BitVec.getLsbD_append,
    hi, decide_true, Bool.true_and, Nat.mod_eq_of_lt (show n < 64 + 64 by omega)]
  by_cases h2 : n < 64
  · simp only [h2, ite_true, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_ushiftRight, hi, decide_true, Bool.true_and, show ¬ (64 + i < n) by omega,
      ite_false, show 64 + i < 64 + 64 by omega]
    by_cases h1 : i < n
    · simp only [h1, show 64 + i - n < 64 by omega, ite_true, decide_true, Bool.not_true,
        Bool.false_and, Bool.false_or]
      exact getLsbD_idx _ (by omega)
    · simp only [h1, show ¬ (64 + i - n < 64) by omega, ite_false, decide_false,
        Bool.not_false, Bool.true_and, BitVec.getLsbD_of_ge xl (64 - n + i) (by omega),
        Bool.or_false]
      exact getLsbD_idx _ (by omega)
  · simp only [h2, ite_false, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_ushiftRight, hi, decide_true, Bool.true_and]
    by_cases h3 : i < n - 64
    · simp only [show 64 + i < n by omega, ite_true, show ¬ (64 + 64 - n + (64 + i) < 64) by omega,
        ite_false, h3, decide_true, Bool.not_true, Bool.false_and, Bool.false_or]
      exact getLsbD_idx _ (by omega)
    · simp only [show ¬ (64 + i < n) by omega, ite_false, show 64 + i < 64 + 64 by omega,
        show 64 + i - n < 64 by omega, ite_true, h3, decide_true, decide_false,
        Bool.not_false, Bool.true_and, BitVec.getLsbD_of_ge xh (128 - n + i) (by omega),
        Bool.or_false]
      exact getLsbD_idx _ (by omega)

/-- The source shifts, by a constant amount. -/
def shiftC (op : BinaryOp) (X : BitVec 128) (n : Nat) : BitVec 128 :=
  match op with
  | .ishl => X <<< n
  | .ushr => X >>> n
  | .sshr => X.sshiftRight n
  | _ => X.rotateLeft n

/-- Rewrite the source shift by the amount `n < 128` as a shift by the bit vector `k`. -/
theorem shiftC_bv {op : BinaryOp} {n : Nat} (hn : n < 128) (X : BitVec 128) :
    shiftC op X n = match op with
      | .ishl => X <<< BitVec.ofNat 128 n
      | .ushr => X >>> BitVec.ofNat 128 n
      | .sshr => X.sshiftRight' (BitVec.ofNat 128 n)
      | _ => X <<< BitVec.ofNat 128 n ||| X >>> (128#128 - BitVec.ofNat 128 n) := by
  cases op <;> simp only [shiftC, BitVec.shiftLeft_eq', BitVec.ushiftRight_eq',
    BitVec.sshiftRight', kn_toNat hn] <;>
    first
    | rfl
    | (rw [BitVec.rotateLeft_def, Nat.mod_eq_of_lt hn]
       have : (128#128 - BitVec.ofNat 128 n).toNat = 128 - n := by
         rw [BitVec.toNat_sub, kn_toNat hn]; simp; omega
       rw [this])

/-- The end of a constant-shift branch: the run, the 64-bit amounts as `Nat`s, the source halves
by `shl_lo`, …, then the `Nat` amounts by `omega`. -/
macro "cs_fin" : tactic => `(tactic| (
  pat_eval
  simp only [Sem.binary, Sem.bor, Sem.ishl, Sem.ushr, Sem.sshr, Sem.shiftAmt, width_i64,
    BitVec.toNat_ofNat, BitVec.ofInt_natCast, BitVec.ofInt_ofNat, shl_lo, shl_hi, ushr_lo, ushr_hi,
    sshr_lo, sshr_hi, lo_app, hi_app, Nat.reducePow, Nat.reduceMod, Nat.reduceSub]
  simp (disch := omega) only [rotl_lo, rotl_hi, ite_eq_left, ite_eq_right, Nat.mod_eq_of_lt, BitVec.shiftLeft_zero,
    BitVec.ushiftRight_zero, BitVec.sshiftRight_zero, BitVec.ushiftRight_eq_zero,
    BitVec.shiftLeft_eq_zero, BitVec.or_zero, BitVec.zero_or, Nat.reduceSub]
  constructor <;> eq_leaf))

/-- The four branches of `constShift` (amount `0`, `(0, 64)`, `64`, `(64, 128)`), for one
normalised operation `op` whose source value, by the bit-vector amount `k`, is `src k`. -/
theorem cs_branches (op : BinaryOp) (hop : op = .ishl ∨ op = .ushr ∨ op = .sshr ∨ op = .rotl)
    (n : Nat) (hn : n < 128) (xl xh : BitVec 64) (X : BitVec 128)
    (hX : X = match op with
      | .ishl => (xh ++ xl) <<< BitVec.ofNat 128 n
      | .ushr => (xh ++ xl) >>> BitVec.ofNat 128 n
      | .sshr => (xh ++ xl).sshiftRight' (BitVec.ofNat 128 n)
      | _ => (xh ++ xl) <<< BitVec.ofNat 128 n ||| (xh ++ xl) >>> (128#128 - BitVec.ofNat 128 n)) :
    ∃ ρ, runPat (canon [V64 xl, V64 xh]) (Pat.constShift op n) = some ρ ∧ Out128 ρ 2 3 X := by
  have hX' : X = shiftC op (xh ++ xl) n := by
    rw [shiftC_bv hn]; rcases hop with rfl | rfl | rfl | rfl <;> exact hX
  clear hX; subst hX'
  rcases (show n = 0 ∨ (0 < n ∧ n < 64) ∨ n = 64 ∨ (64 < n ∧ n < 128) by omega) with
    rfl | ⟨h1, h2⟩ | rfl | ⟨h1, h2⟩ <;>
  rcases hop with rfl | rfl | rfl | rfl <;>
  simp (disch := omega) only [shiftC, Pat.constShift, ite_eq_left, ite_eq_right, beq_iff_eq] <;>
  cs_fin

/-- The constant-shift patterns (`op` normalised: every operation other than `ishl`, `ushr`,
`sshr` is a left rotation). -/
theorem pat_constShift (op : BinaryOp) (n : Nat) (hn : n < 128) (xl xh : BitVec 64) :
    ∃ ρ, runPat (canon [V64 xl, V64 xh]) (Pat.constShift op n) = some ρ ∧
      Out128 ρ 2 3 (shiftC op (xh ++ xl) n) := by
  rw [shiftC_bv hn]
  have h := fun op' hop => cs_branches op' hop n hn xl xh _ rfl
  cases op
  case ishl => exact h .ishl (.inl rfl)
  case ushr => exact h .ushr (.inr (.inl rfl))
  case sshr => exact h .sshr (.inr (.inr (.inl rfl)))
  all_goals exact h .rotl (.inr (.inr (.inr rfl)))

/-! ## Multiplication (by the `toNat` arithmetic) -/

/-- The 128-bit product by the cross products. -/
theorem mul128 (xl xh yl yh : BitVec 64) :
    (xh ++ xl) * (yh ++ yl) = (xl * yh + xh * yl + Sem.umulhi xl yl) ++ (xl * yl) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, append_toNat, BitVec.toNat_add, Sem.umulhi,
    BitVec.extractLsb'_toNat, BitVec.toNat_setWidth, Nat.shiftRight_eq_div_pow,
    show (64 : Nat) + 64 = 128 from rfl]
  have ha := xh.isLt; have hb := xl.isLt; have hc := yh.isLt; have hd := yl.isLt
  generalize xh.toNat = a at *; generalize xl.toNat = b at *
  generalize yh.toNat = c at *; generalize yl.toNat = d at *
  have hbd : b * d < 2^128 := by
    have := Nat.mul_lt_mul_of_lt_of_lt hb hd; rwa [← Nat.pow_add] at this
  rw [Nat.mod_eq_of_lt (a := b) (by omega), Nat.mod_eq_of_lt (a := d) (by omega),
    Nat.mod_eq_of_lt (a := b * d) hbd]
  have e : (a * 2^64 + b) * (c * 2^64 + d) = a * c * 2^128 + (b * c + a * d) * 2^64 + b * d := by
    simp only [Nat.add_mul, Nat.mul_add]
    rw [show 2^128 = 2^64 * 2^64 by rw [← Nat.pow_add]]
    simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm]
  rw [e]
  generalize a * c = p0; generalize b * c = p1; generalize a * d = p2
  generalize b * d = P at *
  omega

theorem pat_imul (xl xh yl yh : BitVec 64) :
    ∃ ρ, runPat (canon [V64 xl, V64 xh, V64 yl, V64 yh]) ((Pat.binary .imul).getD []) = some ρ ∧
      Out128 ρ 4 5 (Sem.binary .imul (xh ++ xl) (yh ++ yl)) := by
  generalize hX : Sem.binary .imul (xh ++ xl) (yh ++ yl) = X
  pat_eval
  simp only [Sem.binary, Sem.imul, Sem.iadd] at hX ⊢
  rw [← hX, mul128]
  constructor <;> app_fin

/-! ## A narrow shift by an `i128` amount -/

/-- A shift depends on the amount only modulo the width. -/
theorem shift_congr {op : BinaryOp} {w v v' : Nat} (x : BitVec w) (b : BitVec v) (b' : BitVec v')
    (h : b.toNat % w = b'.toNat % w) : Sem.shift op x b = Sem.shift op x b' := by
  cases op <;> simp only [Sem.shift, Sem.ishl, Sem.ushr, Sem.sshr, Sem.rotl, Sem.rotr,
    Sem.shiftAmt, h]

theorem amt_narrow {w : Nat} (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) (yl yh : BitVec 64) :
    (yl &&& BitVec.ofNat 64 (w - 1)).toNat % w = (yh ++ yl).toNat % w := by
  rw [append_toNat, BitVec.toNat_and, BitVec.toNat_ofNat]
  rcases hw with rfl | rfl | rfl | rfl
  · have h := Nat.and_two_pow_sub_one_eq_mod yl.toNat 3
    simp only [show 2 ^ 3 - 1 = 7 from rfl] at h
    simp only [show 8 - 1 = 7 from rfl, show 7 % 2 ^ 64 = 7 from rfl, h]; omega
  · have h := Nat.and_two_pow_sub_one_eq_mod yl.toNat 4
    simp only [show 2 ^ 4 - 1 = 15 from rfl] at h
    simp only [show 16 - 1 = 15 from rfl, show 15 % 2 ^ 64 = 15 from rfl, h]; omega
  · have h := Nat.and_two_pow_sub_one_eq_mod yl.toNat 5
    simp only [show 2 ^ 5 - 1 = 31 from rfl] at h
    simp only [show 32 - 1 = 31 from rfl, show 31 % 2 ^ 64 = 31 from rfl, h]; omega
  · have h := Nat.and_two_pow_sub_one_eq_mod yl.toNat 6
    simp only [show 2 ^ 6 - 1 = 63 from rfl] at h
    simp only [show 64 - 1 = 63 from rfl, show 63 % 2 ^ 64 = 63 from rfl, h]; omega

theorem pat_shiftNarrow (op : BinaryOp) (hop : op.isShift = true) (t : Ty)
    (ht : t = .i8 ∨ t = .i16 ∨ t = .i32 ∨ t = .i64) (x : BitVec t.width) (yl yh : BitVec 64) :
    ∃ ρ, runPat (canon [⟨t, x⟩, V64 yl]) (Pat.shiftNarrow op t) = some ρ ∧
      ∀ r, Sem.shift op x (yh ++ yl) = some r → ρ 2 = some ⟨t, r⟩ := by
  obtain ⟨r, hr⟩ : ∃ r, Sem.shift op x (yh ++ yl) = some r := by
    cases op <;> simp_all [BinaryOp.isShift, Sem.shift]
  have hw : t.width = 8 ∨ t.width = 16 ∨ t.width = 32 ∨ t.width = 64 := by
    rcases ht with rfl | rfl | rfl | rfl <;> simp
  have hc := shift_congr (op := op) x (yl &&& BitVec.ofNat 64 (t.width - 1)) (yh ++ yl)
    (amt_narrow hw yl yh)
  rw [hr] at hc
  rcases ht with rfl | rfl | rfl | rfl <;>
    (simp only [width_i8, width_i16, width_i32, width_i64, Nat.reduceSub] at hc
     simp (config := { maxSteps := 4000000 }) [Pat.shiftNarrow, S, bin, runPat, evalInst,
      dframe, canon, Frame.getAs, Frame.get, Res.ofOption, hop,
      show BinaryOp.band.isShift = false from rfl, bind, Res.bind,
      Regs.set, Sem.binary, Sem.band]
     erw [hc]; simp
     intro r1 h1
     have e : r = r1 := Option.some.inj (hr.symm.trans h1)
     subst e; rfl)

end Opt.Legal
