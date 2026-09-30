import FV.Opt.Proof.LegalPat
import Std.Tactic.BVDecide

/-!
# The canonical patterns of `Opt.Legal` compute the `i128` operations

Each theorem runs one canonical pattern (`Opt.Legal.Pat.*`) on symbolic `i64` halves and states
that its outputs are the halves of the `Clif.Sem` result at `i128` (`Out128`). The runs are
computed by `simp` (`pat_eval`); the remaining bit-vector identities are closed by
`bv_decide`, per operation (the multiplication by the toNat arithmetic of `BitVec`), without
its enum pass (`-enums`): the pass realizes `Clif.Ty.enumToBitVec` in the calling module, and
`FV.Backend.Proof.IselCmpExt` realizes it too — two modules realizing it cannot be imported
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

/-- The `Clif.Sem` definitions in `bv_decide -enums`'s fragment. -/
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
  constructor <;> bv_decide -enums

theorem pat_ineg (xl xh : BitVec 64) : ∃ ρ, runPat (canon [V64 xl, V64 xh]) (Pat.unary .ineg) =
    some ρ ∧ Out128 ρ 2 3 (Sem.unary .ineg (xh ++ xl)) := by
  pat_eval
  simp only [Sem.unary, Sem.ineg, Sem.binary, Sem.bxor, Sem.iadd, Sem.uextend, Sem.icmp,
    bool8_eq, Sem.intcc]
  constructor <;> bv_decide -enums

theorem pat_unary (op : UnaryOp) (xl xh : BitVec 64) :
    ∃ ρ, runPat (canon [V64 xl, V64 xh]) (Pat.unary op) = some ρ ∧
      Out128 ρ 2 3 (Sem.unary op (xh ++ xl)) := by
  cases op
  case bswap =>
    pat_eval
    simp only [Sem.unary, Sem.bswap, List.range, List.range.loop, List.foldl]
    constructor <;> bv_decide -enums
  all_goals (pat_eval; sem_bv; constructor <;> bv_decide -enums)

/-! ## Binary -/

theorem pat_binary {op : BinaryOp} {pat : List Stmt} (h : Pat.binary op = some pat)
    (hm : op ≠ .imul) (xl xh yl yh : BitVec 64) :
    ∃ ρ, runPat (canon [V64 xl, V64 xh, V64 yl, V64 yh]) pat = some ρ ∧
      Out128 ρ 4 5 (Sem.binary op (xh ++ xl) (yh ++ yl)) := by
  cases op <;> simp only [Pat.binary, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    (try exact absurd rfl hm) <;> (pat_eval; sem_bv; constructor <;> bv_decide -enums)

theorem pat_icmp (cc : IntCC) (xl xh yl yh : BitVec 64) :
    ∃ ρ, runPat (canon [V64 xl, V64 xh, V64 yl, V64 yh]) (Pat.icmp cc) = some ρ ∧
      ρ 4 = some ⟨.i8, Sem.icmp cc (xh ++ xl) (yh ++ yl)⟩ := by
  cases cc <;> (pat_eval; sem_bv; bv_decide -enums)

/-! ## Selects, `bmask`, conditions -/

theorem pat_cond (lo hi : BitVec 64) :
    ∃ ρ, runPat (canon [V64 lo, V64 hi]) Pat.cond = some ρ ∧
      ρ 2 = some ⟨.i8, Sem.bool8 (Sem.truthy (hi ++ lo))⟩ := by
  pat_eval; sem_bv; simp only [Sem.truthy]; bv_decide -enums

theorem pat_select128c (cl ch xl xh yl yh : BitVec 64) :
    ∃ ρ, runPat (canon [V64 cl, V64 ch, V64 xl, V64 xh, V64 yl, V64 yh]) Pat.select128c =
      some ρ ∧ Out128 ρ 6 7 (Sem.select (ch ++ cl) (xh ++ xl) (yh ++ yl)) := by
  pat_eval; sem_bv; constructor <;> bv_decide -enums

theorem pat_select128 (c : Val) (xl xh yl yh : BitVec 64) :
    ∃ ρ, runPat (canon [c, V64 xl, V64 xh, V64 yl, V64 yh]) Pat.select128 = some ρ ∧
      Out128 ρ 5 6 (Sem.select c.bits (xh ++ xl) (yh ++ yl)) := by
  pat_eval; sem_bv
  cases (c.bits != 0) <;> simp <;> constructor <;> bv_decide -enums

theorem pat_selectc (t : Ty) (cl ch : BitVec 64) (x y : BitVec t.width) :
    ∃ ρ, runPat (canon [V64 cl, V64 ch, ⟨t, x⟩, ⟨t, y⟩]) (Pat.selectc t) = some ρ ∧
      ρ 4 = some ⟨t, Sem.select (ch ++ cl) x y⟩ := by
  pat_eval
  simp only [Sem.binary, Sem.bor, Sem.icmp, Sem.intcc, bool8_eq]
  have : ((bif cl != 0#64 then 1#8 else 0#8) ||| (bif ch != 0#64 then 1#8 else 0#8) !=
      (0 : BitVec 8)) = (ch ++ cl != (0 : BitVec 128)) := by bv_decide -enums
  unfold Sem.select Sem.truthy
  rw [this]

theorem pat_bitselect (cl ch xl xh yl yh : BitVec 64) :
    ∃ ρ, runPat (canon [V64 cl, V64 ch, V64 xl, V64 xh, V64 yl, V64 yh]) Pat.bitselect =
      some ρ ∧ Out128 ρ 6 7 (Sem.bitselect (ch ++ cl) (xh ++ xl) (yh ++ yl)) := by
  pat_eval; sem_bv; constructor <;> bv_decide -enums

theorem pat_bmask128c (xl xh : BitVec 64) :
    ∃ ρ, runPat (canon [V64 xl, V64 xh]) Pat.bmask128c = some ρ ∧
      Out128 ρ 2 3 (Sem.bmask (xh ++ xl)) := by
  pat_eval; sem_bv; constructor <;> bv_decide -enums

theorem pat_bmask128 (x : Val) :
    ∃ ρ, runPat (canon [x]) Pat.bmask128 = some ρ ∧ Out128 ρ 1 2 (Sem.bmask x.bits) := by
  pat_eval; sem_bv
  cases (x.bits != 0) <;> simp <;> constructor <;> bv_decide -enums

theorem pat_bmaskc (t : Ty) (xl xh : BitVec 64) :
    ∃ ρ, runPat (canon [V64 xl, V64 xh]) (Pat.bmaskc t) = some ρ ∧
      ρ 2 = some ⟨t, Sem.bmask (xh ++ xl)⟩ := by
  cases t <;> (pat_eval; sem_bv; bv_decide -enums)

/-! ## Width changes and copies -/

theorem pat_extend64 (op : ExtendOp) (x : BitVec 64) :
    ∃ ρ, runPat (canon [V64 x]) (Pat.extend op true) = some ρ ∧
      Out128 ρ 1 2 (match op with
        | .uextend => Sem.uextend 128 x | .sextend => Sem.sextend 128 x) := by
  cases op <;> (pat_eval; sem_bv; constructor <;> bv_decide -enums)

theorem pat_extend8 (op : ExtendOp) (x : BitVec 8) :
    ∃ ρ, runPat (canon [⟨.i8, x⟩]) (Pat.extend op false) = some ρ ∧
      Out128 ρ 1 2 (match op with
        | .uextend => Sem.uextend 128 x | .sextend => Sem.sextend 128 x) := by
  cases op <;> (pat_eval; sem_bv; constructor <;> bv_decide -enums)

theorem pat_extend16 (op : ExtendOp) (x : BitVec 16) :
    ∃ ρ, runPat (canon [⟨.i16, x⟩]) (Pat.extend op false) = some ρ ∧
      Out128 ρ 1 2 (match op with
        | .uextend => Sem.uextend 128 x | .sextend => Sem.sextend 128 x) := by
  cases op <;> (pat_eval; sem_bv; constructor <;> bv_decide -enums)

theorem pat_extend32 (op : ExtendOp) (x : BitVec 32) :
    ∃ ρ, runPat (canon [⟨.i32, x⟩]) (Pat.extend op false) = some ρ ∧
      Out128 ρ 1 2 (match op with
        | .uextend => Sem.uextend 128 x | .sextend => Sem.sextend 128 x) := by
  cases op <;> (pat_eval; sem_bv; constructor <;> bv_decide -enums)

theorem pat_extendN (op : ExtendOp) (t : Ty) (ht : t.width < 64) (x : BitVec t.width) :
    ∃ ρ, runPat (canon [⟨t, x⟩]) (Pat.extend op false) = some ρ ∧
      Out128 ρ 1 2 (match op with
        | .uextend => Sem.uextend 128 x | .sextend => Sem.sextend 128 x) := by
  cases t
  · exact pat_extend8 op x
  · exact pat_extend16 op x
  · exact pat_extend32 op x
  all_goals simp [Ty.width] at ht

theorem pat_ireduce (t : Ty) (ht : t.width < 128) (xl xh : BitVec 64) :
    ∃ ρ, runPat (canon [V64 xl]) (Pat.ireduce t) = some ρ ∧
      ρ 1 = some ⟨t, Sem.ireduce t.width (xh ++ xl)⟩ := by
  cases t <;> simp only [Ty.width] at ht <;> (try omega) <;> (pat_eval; sem_bv; bv_decide -enums)

theorem pat_copy2 (a b : BitVec 64) :
    ∃ ρ, runPat (canon [V64 a, V64 b]) Pat.copy2 = some ρ ∧
      ρ 2 = some (V64 a) ∧ ρ 3 = some (V64 b) := by
  pat_eval; sem_bv; constructor <;> bv_decide -enums

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

/-- The end of a constant-shift branch: the amount generalised to `k`, the source value `X`
opaque during the run, then the identities by `bv_decide -enums`. -/
macro "cs_fin" : tactic => `(tactic| (
  generalize BitVec.ofNat 128 _ = k at *
  pat_eval
  simp only [ishl64, ushr64, sshr64, Sem.binary, Sem.bor]
  subst_vars
  try (generalize hk2 : 128#128 - k = k2 at *)
  constructor <;> bv_decide -enums))

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
  have hk : BitVec.ofNat 128 n < 128#128 := by rw [BitVec.lt_def, kn_toNat hn]; simp; omega
  by_cases h64 : n < 64
  · have e1 := ofNat_n hn
    by_cases h0 : n = 0
    · have hz : BitVec.ofNat 128 n = 0#128 := by subst h0; rfl
      have h0' : (n == 0) = true := by simp [h0]
      rcases hop with rfl | rfl | rfl | rfl <;> simp only at hX <;>
        simp only [Pat.constShift, h64, ite_true, h0', K, BitVec.ofInt_natCast, e1] <;> cs_fin
    · have hk1 := kn_lt h64 (by omega)
      have hk0 := kn_lt (show 0 < n by omega) hn
      have e2 := ofNat_64sub (show n ≤ 64 by omega)
      rcases hop with rfl | rfl | rfl | rfl <;> simp only at hX <;>
        simp only [Pat.constShift, h64, ite_true, beq_iff_eq, h0, ite_false, K,
          BitVec.ofInt_natCast, e1, e2] <;> cs_fin
  · have hk1 := kn_le (show 64 ≤ n by omega) hn
    have e3 := ofNat_sub64 (show 64 ≤ n by omega) hn
    by_cases h0 : n = 64
    · have hz : BitVec.ofNat 128 n = 64#128 := by subst h0; rfl
      have hm : (n - 64 == 0) = true := by simp; omega
      rcases hop with rfl | rfl | rfl | rfl <;> simp only at hX <;>
        simp only [Pat.constShift, h64, ite_false, hm, ite_true, K, BitVec.ofInt_natCast,
          e3] <;> cs_fin
    · have hk0 := kn_lt (show 64 < n by omega) hn
      have e4 := ofNat_64subsub (show 64 ≤ n by omega) hn
      have hm : ¬ (n - 64 = 0) := by omega
      rcases hop with rfl | rfl | rfl | rfl <;> simp only at hX <;>
        simp only [Pat.constShift, h64, ite_false, beq_iff_eq, hm, K, BitVec.ofInt_natCast,
          e3, e4] <;> cs_fin

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

/-! ## Multiplication (by the `toNat` arithmetic: products are out of `bv_decide -enums`'s reach) -/

theorem append_toNat (a b : BitVec 64) : (a ++ b).toNat = a.toNat * 2^64 + b.toNat := by
  rw [BitVec.toNat_append, Nat.shiftLeft_eq, Nat.mul_comm, Nat.two_pow_add_eq_or_of_lt b.isLt]

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
  constructor <;> bv_decide -enums

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
