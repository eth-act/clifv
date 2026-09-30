import FV.Opt.Proof.LegalPat
import Std.Tactic.BVDecide

/-!
# The canonical patterns of `Opt.Legal` compute the `i128` operations

Each theorem runs one canonical pattern (`Opt.Legal.Pat.*`) on symbolic `i64` halves and states
that its outputs are the halves of the `Clif.Sem` result at `i128` (`Out128`). The runs are
computed by `simp` (`pat_eval`); the remaining bit-vector identities are closed by
`bv_decide`, per operation (the multiplication by the toNat arithmetic of `BitVec`).
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

/-- The `Clif.Sem` definitions in `bv_decide`'s fragment. -/
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
  constructor <;> bv_decide

theorem pat_ineg (xl xh : BitVec 64) : ∃ ρ, runPat (canon [V64 xl, V64 xh]) (Pat.unary .ineg) =
    some ρ ∧ Out128 ρ 2 3 (Sem.unary .ineg (xh ++ xl)) := by
  pat_eval
  simp only [Sem.unary, Sem.ineg, Sem.binary, Sem.bxor, Sem.iadd, Sem.uextend, Sem.icmp,
    bool8_eq, Sem.intcc]
  constructor <;> bv_decide

theorem pat_unary (op : UnaryOp) (xl xh : BitVec 64) :
    ∃ ρ, runPat (canon [V64 xl, V64 xh]) (Pat.unary op) = some ρ ∧
      Out128 ρ 2 3 (Sem.unary op (xh ++ xl)) := by
  cases op
  case bswap =>
    pat_eval
    simp only [Sem.unary, Sem.bswap, List.range, List.range.loop, List.foldl]
    constructor <;> bv_decide
  all_goals (pat_eval; sem_bv; constructor <;> bv_decide)

/-! ## Binary -/

theorem pat_binary {op : BinaryOp} {pat : List Stmt} (h : Pat.binary op = some pat)
    (hm : op ≠ .imul) (xl xh yl yh : BitVec 64) :
    ∃ ρ, runPat (canon [V64 xl, V64 xh, V64 yl, V64 yh]) pat = some ρ ∧
      Out128 ρ 4 5 (Sem.binary op (xh ++ xl) (yh ++ yl)) := by
  cases op <;> simp only [Pat.binary, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    (try exact absurd rfl hm) <;> (pat_eval; sem_bv; constructor <;> bv_decide)

theorem pat_icmp (cc : IntCC) (xl xh yl yh : BitVec 64) :
    ∃ ρ, runPat (canon [V64 xl, V64 xh, V64 yl, V64 yh]) (Pat.icmp cc) = some ρ ∧
      ρ 4 = some ⟨.i8, Sem.icmp cc (xh ++ xl) (yh ++ yl)⟩ := by
  cases cc <;> (pat_eval; sem_bv; bv_decide)

/-! ## Selects, `bmask`, conditions -/

theorem pat_cond (lo hi : BitVec 64) :
    ∃ ρ, runPat (canon [V64 lo, V64 hi]) Pat.cond = some ρ ∧
      ρ 2 = some ⟨.i8, Sem.bool8 (Sem.truthy (hi ++ lo))⟩ := by
  pat_eval; sem_bv; simp only [Sem.truthy]; bv_decide

theorem pat_select128c (cl ch xl xh yl yh : BitVec 64) :
    ∃ ρ, runPat (canon [V64 cl, V64 ch, V64 xl, V64 xh, V64 yl, V64 yh]) Pat.select128c =
      some ρ ∧ Out128 ρ 6 7 (Sem.select (ch ++ cl) (xh ++ xl) (yh ++ yl)) := by
  pat_eval; sem_bv; constructor <;> bv_decide

theorem pat_select128 (c : Val) (xl xh yl yh : BitVec 64) :
    ∃ ρ, runPat (canon [c, V64 xl, V64 xh, V64 yl, V64 yh]) Pat.select128 = some ρ ∧
      Out128 ρ 5 6 (Sem.select c.bits (xh ++ xl) (yh ++ yl)) := by
  pat_eval; sem_bv
  cases (c.bits != 0) <;> simp <;> constructor <;> bv_decide

theorem pat_selectc (t : Ty) (cl ch : BitVec 64) (x y : BitVec t.width) :
    ∃ ρ, runPat (canon [V64 cl, V64 ch, ⟨t, x⟩, ⟨t, y⟩]) (Pat.selectc t) = some ρ ∧
      ρ 4 = some ⟨t, Sem.select (ch ++ cl) x y⟩ := by
  pat_eval
  simp only [Sem.binary, Sem.bor, Sem.icmp, Sem.intcc, bool8_eq]
  have : ((bif cl != 0#64 then 1#8 else 0#8) ||| (bif ch != 0#64 then 1#8 else 0#8) !=
      (0 : BitVec 8)) = (ch ++ cl != (0 : BitVec 128)) := by bv_decide
  unfold Sem.select Sem.truthy
  rw [this]

theorem pat_bitselect (cl ch xl xh yl yh : BitVec 64) :
    ∃ ρ, runPat (canon [V64 cl, V64 ch, V64 xl, V64 xh, V64 yl, V64 yh]) Pat.bitselect =
      some ρ ∧ Out128 ρ 6 7 (Sem.bitselect (ch ++ cl) (xh ++ xl) (yh ++ yl)) := by
  pat_eval; sem_bv; constructor <;> bv_decide

theorem pat_bmask128c (xl xh : BitVec 64) :
    ∃ ρ, runPat (canon [V64 xl, V64 xh]) Pat.bmask128c = some ρ ∧
      Out128 ρ 2 3 (Sem.bmask (xh ++ xl)) := by
  pat_eval; sem_bv; constructor <;> bv_decide

theorem pat_bmask128 (x : Val) :
    ∃ ρ, runPat (canon [x]) Pat.bmask128 = some ρ ∧ Out128 ρ 1 2 (Sem.bmask x.bits) := by
  pat_eval; sem_bv
  cases (x.bits != 0) <;> simp <;> constructor <;> bv_decide

theorem pat_bmaskc (t : Ty) (xl xh : BitVec 64) :
    ∃ ρ, runPat (canon [V64 xl, V64 xh]) (Pat.bmaskc t) = some ρ ∧
      ρ 2 = some ⟨t, Sem.bmask (xh ++ xl)⟩ := by
  cases t <;> (pat_eval; sem_bv; bv_decide)

/-! ## Width changes and copies -/

theorem pat_extend64 (op : ExtendOp) (x : BitVec 64) :
    ∃ ρ, runPat (canon [V64 x]) (Pat.extend op true) = some ρ ∧
      Out128 ρ 1 2 (match op with
        | .uextend => Sem.uextend 128 x | .sextend => Sem.sextend 128 x) := by
  cases op <;> (pat_eval; sem_bv; constructor <;> bv_decide)

theorem pat_extend8 (op : ExtendOp) (x : BitVec 8) :
    ∃ ρ, runPat (canon [⟨.i8, x⟩]) (Pat.extend op false) = some ρ ∧
      Out128 ρ 1 2 (match op with
        | .uextend => Sem.uextend 128 x | .sextend => Sem.sextend 128 x) := by
  cases op <;> (pat_eval; sem_bv; constructor <;> bv_decide)

theorem pat_extend16 (op : ExtendOp) (x : BitVec 16) :
    ∃ ρ, runPat (canon [⟨.i16, x⟩]) (Pat.extend op false) = some ρ ∧
      Out128 ρ 1 2 (match op with
        | .uextend => Sem.uextend 128 x | .sextend => Sem.sextend 128 x) := by
  cases op <;> (pat_eval; sem_bv; constructor <;> bv_decide)

theorem pat_extend32 (op : ExtendOp) (x : BitVec 32) :
    ∃ ρ, runPat (canon [⟨.i32, x⟩]) (Pat.extend op false) = some ρ ∧
      Out128 ρ 1 2 (match op with
        | .uextend => Sem.uextend 128 x | .sextend => Sem.sextend 128 x) := by
  cases op <;> (pat_eval; sem_bv; constructor <;> bv_decide)

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
  cases t <;> simp only [Ty.width] at ht <;> (try omega) <;> (pat_eval; sem_bv; bv_decide)

theorem pat_copy2 (a b : BitVec 64) :
    ∃ ρ, runPat (canon [V64 a, V64 b]) Pat.copy2 = some ρ ∧
      ρ 2 = some (V64 a) ∧ ρ 3 = some (V64 b) := by
  pat_eval; sem_bv; constructor <;> bv_decide

end Opt.Legal
