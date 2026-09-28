import FV.Opt.Proof.InterpEval
import Std.Tactic.BVDecide

/-!
# Helper specifications: `Imm64` arithmetic as `BitVec` operations

**Normal form.** An `iconst.t` node of the e-graph (`t ≠ i128`) presents its immediate as
`imm64OfBits b` (`b : BitVec t.width`), and `make_inst` turns an immediate `k` back into
`BitVec.ofInt t.width k` (`toInst`). Every `imm64_*` helper at type `t` maps immediates of
that form to one of that form: `Rust.imm64Add (ofClif t) (imm64OfBits b) (imm64OfBits c) =
.ok (imm64OfBits (b + c))`, etc. (`opt_imm`), and `ofInt_imm64OfBits` closes the round trip, so
right-hand sides built from helper results evaluate to `BitVec` terms over the matched
immediates, which `bv_decide` compares with the left-hand side's value.

**Proofs** (`imm_solve`): split the type (four widths), unfold the helper, rewrite every `Int`
operation of the Rust transcription (`asU64`, `asI64`, `band64`, `sext`, `maskTo`, the `ty_mask`
literal, comparisons, `if`) into `BitVec 64` operations (`BitVec.ofInt 64` distributes over
`+ - *` and `if`; `imm64OfBits b = (b.setWidth 64).toInt`; `BitVec.toInt_inj`), then
`bv_decide`.

Also here: the forward-evaluation facts for building nodes (`make_inst` of a concrete
`InstructionData`: `toInst`, `makeInst`; `cfg`; `panics`).
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt Isle.Interp Clif

/-! ## Evaluating `make_inst` and helpers in right-hand sides -/

@[opt_monad] theorem cfg_checkOverlap : cfg.checkOverlap = false := rfl

@[opt_monad] theorem panics_ok {α : Type} (a : α) : panics (.ok a : Rust.Panics α) = .ok a := rfl

@[opt_monad] theorem except_bind_assoc {ε α β γ : Type} (x : Except ε α) (f : α → Except ε β)
    (g : β → Except ε γ) : (x >>= f) >>= g = x >>= fun a => f a >>= g := by
  cases x <;> rfl

attribute [opt_monad] Option.map_some Option.map_none Option.bind_some Option.bind_none toInst makeInst unaryOfIdx? binaryOfIdx?
  ccOfIdx? TyId.«InstructionData»

/-- `toInst` of an `icmp`: the operand type is read off the graph (`typeOf x`, which a proof
splits on: `none` makes a poison value). Stated for any condition-code index (`cc c` unfolds to
`.data 46 (ccIdx c) []`, `ccOfIdx?_ccIdx`), before `toInst` is unfolded (`↓`). -/
@[opt_monad ↓] theorem toInst_icmp (tf : Nat → Option Ty) (t : Ty) (k k' c : Nat) (x y : Nat) :
    toInst tf (CTy.ofClif t) (.data 53 14 [.data k 72 [], .values [.value x, .value y], .data k' c []]) =
      (ccOfIdx? c).bind fun cc => (tf x).map fun xt => .icmp cc xt x y := by
  cases t <;> cases h : tf x <;> cases h' : ccOfIdx? c <;> simp [toInst, h, h', CTy.ofClif, CTy.toClif?]

@[opt_monad] theorem cc_data (c : IntCC) : cc c = .data 46 (ccIdx c) [] := rfl

@[opt_monad ↓] theorem ccOfIdx?_ccIdx (c : IntCC) : ccOfIdx? (ccIdx c) = some c := by cases c <;> rfl

@[opt_monad] theorem V.cc?_data (ty : Nat) (c : IntCC) : (V.data ty (ccIdx c) []).cc? = .ok c := by
  cases c <;> rfl

@[opt_monad] theorem toClif?_ofClif (t : Ty) : (CTy.ofClif t).toClif? = some t := by
  cases t <;> rfl

/-- (Discharged from the context: presented `iconst`s are not `i128`.) -/
@[opt_monad] theorem beq_i128_false {t : Ty} (ht : t ≠ .i128) : (t == .i128) = false := by
  simpa using ht

/-! ## `Int` to `BitVec 64` -/

theorem imm64OfBits_eq {w : Nat} (_hw : w ≤ 64) (b : BitVec w) :
    imm64OfBits b = (b.setWidth 64).toInt := by
  simp only [imm64OfBits, Rust.asI64, BitVec.ofInt_natCast, BitVec.ofNat_toNat]

/-- `imm64OfBits` at any width up to 64 is undone by `BitVec.ofInt`. -/
theorem ofInt_imm64OfBits' {w : Nat} (hw : w ≤ 64) (b : BitVec w) :
    BitVec.ofInt w (imm64OfBits b) = b := by
  rw [imm64OfBits_eq hw]
  show (b.setWidth 64).signExtend w = b
  rw [BitVec.signExtend_eq_setWidth_of_le _ hw, BitVec.setWidth_setWidth_of_le _ hw,
    BitVec.setWidth_eq]

/-- The round trip of an immediate: `toInst` of a presented `iconst` immediate. -/
@[opt_monad, opt_imm] theorem ofInt_imm64OfBits {t : Ty} (ht : t ≠ .i128) (b : BitVec t.width) :
    BitVec.ofInt t.width (imm64OfBits b) = b :=
  ofInt_imm64OfBits' (by cases t <;> simp_all [Ty.width]) b

/-- `Imm64::sign_extend_from_width` of a presented immediate is its signed value. -/
theorem sext_imm64OfBits {w : Nat} (hw : w ≤ 64) (b : BitVec w) :
    Rust.sext w (imm64OfBits b) = b.toInt := by
  unfold Rust.sext
  split
  · obtain rfl : w = 64 := by omega
    rw [imm64OfBits_eq hw, BitVec.setWidth_eq]
  · rw [ofInt_imm64OfBits' hw]

theorem ofInt_eq_setWidth {w : Nat} (h : w < 64) (z : Int) :
    BitVec.ofInt w z = (BitVec.ofInt 64 z).setWidth w := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt, BitVec.toNat_setWidth]
  have h2 : (2:Int)^w ∣ (2:Int)^64 := by
    obtain ⟨k, hk⟩ : ∃ k, 64 = w + k := ⟨64 - w, by omega⟩
    rw [hk, Int.pow_add]; exact Int.dvd_mul_right _ _
  have hp : (0:Int) < (2:Int)^w := Int.pow_pos (by decide)
  have e1 : z % (2:Int)^w = (z % (2:Int)^64) % (2:Int)^w := (Int.emod_emod_of_dvd z h2).symm
  have hnn : 0 ≤ z % (2:Int)^64 := Int.emod_nonneg _ (by decide)
  show (z % (2:Int)^w).toNat = (z % (2:Int)^64).toNat % 2 ^ w
  rw [e1, Int.toNat_emod hnn (by omega)]
  congr 1

theorem natCast_toNat_lt {w : Nat} (h : w < 64) (x : BitVec w) :
    (x.toNat : Int) = (x.setWidth 64).toInt := by
  have hx := x.isLt
  have hp : 2 ^ w ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) (by omega)
  rw [BitVec.toInt_eq_toNat_cond]
  simp only [BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt (by omega)]
  split <;> omega

theorem ofInt64_natCast_toNat {w : Nat} (x : BitVec w) : BitVec.ofInt 64 (x.toNat : Int) = x.setWidth 64 := by
  simp
theorem ite_toInt {w : Nat} (c : Prop) [Decidable c] (x y : BitVec w) :
    (if c then x.toInt else y.toInt) = (if c then x else y).toInt := by split <;> rfl
theorem ite_natCast_toNat {w : Nat} (c : Prop) [Decidable c] (x y : BitVec w) :
    (if c then (x.toNat : Int) else y.toNat) = ((if c then x else y).toNat : Int) := by split <;> rfl
theorem int_one_toInt : (1 : Int) = (1#64).toInt := by decide
theorem int_zero_toInt : (0 : Int) = (0#64).toInt := by decide
theorem natCast_inj' {w : Nat} {x y : BitVec w} : ((x.toNat : Int) = (y.toNat : Int)) ↔ x = y := by
  rw [Int.natCast_inj, BitVec.toNat_inj]
theorem natCast_bne_natCast {w : Nat} {x y : BitVec w} : ((x.toNat : Int) != (y.toNat : Int)) = (x != y) := by
  rw [Bool.eq_iff_iff]; simp [bne_iff_ne, BitVec.toNat_inj, Int.natCast_inj]
theorem toInt_bne_toInt {w : Nat} {x y : BitVec w} : (x.toInt != y.toInt) = (x != y) := by
  rw [Bool.eq_iff_iff]; simp [bne_iff_ne, BitVec.toInt_inj]
theorem setWidth_ite {w v : Nat} (c : Prop) [Decidable c] (x y : BitVec w) :
    (if c then x else y).setWidth v = if c then x.setWidth v else y.setWidth v := by split <;> rfl

/-! `Sem.icmp` per condition code, as `bif` (no `Decidable` instance to go stale under `simp`). -/
theorem icmp_eq {w : Nat} (x y : BitVec w) : Sem.icmp .eq x y = bif x == y then 1#8 else 0#8 := by
  unfold Sem.icmp Sem.intcc Sem.bool8; cases (x == y) <;> rfl
theorem icmp_ne {w : Nat} (x y : BitVec w) : Sem.icmp .ne x y = bif x != y then 1#8 else 0#8 := by
  unfold Sem.icmp Sem.intcc Sem.bool8; cases (x != y) <;> rfl
theorem icmp_slt {w : Nat} (x y : BitVec w) : Sem.icmp .slt x y = bif x.slt y then 1#8 else 0#8 := by
  unfold Sem.icmp Sem.intcc Sem.bool8; cases (x.slt y) <;> rfl
theorem icmp_sge {w : Nat} (x y : BitVec w) : Sem.icmp .sge x y = bif y.sle x then 1#8 else 0#8 := by
  unfold Sem.icmp Sem.intcc Sem.bool8; cases (y.sle x) <;> rfl
theorem icmp_sgt {w : Nat} (x y : BitVec w) : Sem.icmp .sgt x y = bif y.slt x then 1#8 else 0#8 := by
  unfold Sem.icmp Sem.intcc Sem.bool8; cases (y.slt x) <;> rfl
theorem icmp_sle {w : Nat} (x y : BitVec w) : Sem.icmp .sle x y = bif x.sle y then 1#8 else 0#8 := by
  unfold Sem.icmp Sem.intcc Sem.bool8; cases (x.sle y) <;> rfl
theorem icmp_ult {w : Nat} (x y : BitVec w) : Sem.icmp .ult x y = bif x.ult y then 1#8 else 0#8 := by
  unfold Sem.icmp Sem.intcc Sem.bool8; cases (x.ult y) <;> rfl
theorem icmp_uge {w : Nat} (x y : BitVec w) : Sem.icmp .uge x y = bif y.ule x then 1#8 else 0#8 := by
  unfold Sem.icmp Sem.intcc Sem.bool8; cases (y.ule x) <;> rfl
theorem icmp_ugt {w : Nat} (x y : BitVec w) : Sem.icmp .ugt x y = bif y.ult x then 1#8 else 0#8 := by
  unfold Sem.icmp Sem.intcc Sem.bool8; cases (y.ult x) <;> rfl
theorem icmp_ule {w : Nat} (x y : BitVec w) : Sem.icmp .ule x y = bif x.ule y then 1#8 else 0#8 := by
  unfold Sem.icmp Sem.intcc Sem.bool8; cases (x.ule y) <;> rfl
theorem ofInt_toInt_signExtend {w v : Nat} (x : BitVec w) : BitVec.ofInt v x.toInt = x.signExtend v := rfl
theorem asU64_eq (z : Int) : Rust.asU64 z = ((BitVec.ofInt 64 z).toNat : Int) := rfl
theorem asI64_eq (z : Int) : Rust.asI64 z = (BitVec.ofInt 64 z).toInt := rfl
theorem band64_eq (a b : Int) :
    Rust.band64 a b = ((BitVec.ofInt 64 a &&& BitVec.ofInt 64 b).toNat : Int) := rfl
theorem bor64_eq (a b : Int) :
    Rust.bor64 a b = ((BitVec.ofInt 64 a ||| BitVec.ofInt 64 b).toNat : Int) := rfl
theorem bxor64_eq (a b : Int) :
    Rust.bxor64 a b = ((BitVec.ofInt 64 a ^^^ BitVec.ofInt 64 b).toNat : Int) := rfl
theorem ofInt_sub' {n : Nat} (x y : Int) :
    BitVec.ofInt n (x - y) = BitVec.ofInt n x - BitVec.ofInt n y := by
  rw [Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.sub_eq_add_neg]
theorem ofInt_ite {n : Nat} (c : Prop) [Decidable c] (x y : Int) :
    BitVec.ofInt n (if c then x else y) = if c then BitVec.ofInt n x else BitVec.ofInt n y := by
  split <;> rfl
theorem natCast_le_natCast {a b : Nat} : ((a : Int) ≤ (b : Int)) ↔ a ≤ b := Int.ofNat_le
theorem natCast_lt_natCast {a b : Nat} : ((a : Int) < (b : Int)) ↔ a < b := Int.ofNat_lt
theorem toNat_le_toNat {w : Nat} {x y : BitVec w} : x.toNat ≤ y.toNat ↔ x ≤ y := BitVec.le_def.symm
theorem toNat_lt_toNat {w : Nat} {x y : BitVec w} : x.toNat < y.toNat ↔ x < y := BitVec.lt_def.symm
theorem toInt_le_toInt {w : Nat} {x y : BitVec w} : x.toInt ≤ y.toInt ↔ x.sle y := by
  rw [BitVec.sle_iff_toInt_le]
theorem toInt_lt_toInt {w : Nat} {x y : BitVec w} : x.toInt < y.toInt ↔ x.slt y := by
  rw [BitVec.slt_iff_toInt_lt]
theorem toInt_beq_toInt {w : Nat} {x y : BitVec w} : (x.toInt == y.toInt) = (x == y) := by
  rw [Bool.eq_iff_iff]; simp [BitVec.toInt_inj]
theorem natCast_beq_natCast {a b : Nat} : ((a : Int) == (b : Int)) = (a == b) := by
  rw [Bool.eq_iff_iff]; simp; omega
theorem toNat_beq_toNat {w : Nat} {x y : BitVec w} : (x.toNat == y.toNat) = (x == y) := by
  rw [Bool.eq_iff_iff]; simp [BitVec.toNat_inj]

/-! ### The type-dependent constants of the helpers, at a non-`i128` type -/

theorem ofClif_bits (t : Ty) : (CTy.ofClif t).bits = t.width := by cases t <;> rfl

theorem tyMask_ofClif {t : Ty} (ht : t ≠ .i128) : Rust.tyMask (CTy.ofClif t) = .ok (2 ^ t.width - 1) := by
  cases t <;> first | rfl | exact absurd rfl ht

theorem width64_ofClif {t : Ty} (ht : t ≠ .i128) (fn : String) :
    Rust.width64 fn (CTy.ofClif t) = .ok t.width := by
  cases t <;> first | rfl | exact absurd rfl ht

theorem maskTo_of_lt {w : Nat} (h : w < 64) (x : Int) : Rust.maskTo w x = (BitVec.ofInt w x).toNat := by
  simp [Rust.maskTo, Nat.not_le.2 h]

theorem maskTo_64 (x : Int) : Rust.maskTo 64 x = x := rfl

theorem sext_of_lt {w : Nat} (h : w < 64) (x : Int) : Rust.sext w x = (BitVec.ofInt w x).toInt := by
  simp [Rust.sext, Nat.not_le.2 h]

theorem sext_64 (x : Int) : Rust.sext 64 x = x := rfl

/-- Phase 1 of a helper specification (the type still symbolic): unfold the helper and its
type-dependent constants (`ty_mask`, the width assertion). -/
syntax "imm_pre" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| imm_pre [$ts,*]) => `(tactic|
    simp (disch := assumption) only [$ts,*, Rust.andMask, tyMask_ofClif, width64_ofClif,
      ofClif_bits, except_ok_bind', except_pure', Rust.i64SextendImm64, Rust.u64UextendImm64])

/-- Phase 2 (at one concrete width): turn every `Int` operation into a `BitVec 64` one
(`Int` values of the helpers are `.toInt`/`.toNat` of `BitVec 64` terms), decide. -/
macro "imm_solve" : tactic => `(tactic| (
    try simp (disch := decide) only [sext_imm64OfBits, maskTo_of_lt, maskTo_64, sext_of_lt, sext_64]
    simp (disch := decide) only [imm64OfBits_eq, asU64_eq, asI64_eq, band64_eq,
      bor64_eq, bxor64_eq, BitVec.ofInt_toInt, ofInt64_natCast_toNat, BitVec.setWidth_eq,
      BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_neg, ofInt_sub', ofInt_ite, ofInt_eq_setWidth,
      natCast_toNat_lt, ite_toInt, ite_natCast_toNat, int_one_toInt, int_zero_toInt,
      BitVec.toInt_inj, natCast_inj', Except.ok.injEq, BitVec.ofInt_ofNat,
      Int.reduceNeg, Int.reducePow, natCast_le_natCast, natCast_lt_natCast, toNat_le_toNat,
      toNat_lt_toNat, toInt_le_toInt, toInt_lt_toInt, toInt_beq_toInt, natCast_beq_natCast,
      toNat_beq_toNat, decide_eq_true_eq, natCast_bne_natCast, toInt_bne_toInt,
      ofInt_toInt_signExtend, setWidth_ite, Sem.umin, Sem.umax, Sem.smin, Sem.smax, icmp_eq,
      icmp_ne, icmp_slt, icmp_sge, icmp_sgt, icmp_sle, icmp_ult, icmp_uge, icmp_ugt, icmp_ule]
    all_goals bv_decide))

/-- Split a non-`i128` type into its four widths (reverting the given bit vectors). -/
syntax "imm_cases" ident (ppSpace ident)* : tactic
macro_rules
  | `(tactic| imm_cases $t) => `(tactic| (
    cases $t:ident <;>
      simp only [ne_eq, not_true_eq_false, Ty.width, Nat.reducePow, Nat.reduceSub] at *))
  | `(tactic| imm_cases $t $bs*) => `(tactic| (
    revert $bs*
    cases $t:ident <;>
      simp only [ne_eq, not_true_eq_false, Ty.width, Nat.reducePow, Nat.reduceSub] at * <;>
      intro $bs*))

/-! ## Specifications (`opt_imm`) -/

@[opt_imm] theorem imm64Add_spec {t : Ty} (ht : t ≠ .i128) (b c : BitVec t.width) :
    Rust.imm64Add (CTy.ofClif t) (imm64OfBits b) (imm64OfBits c) = .ok (imm64OfBits (b + c)) := by
  imm_pre [Rust.imm64Add]
  imm_cases t b c <;> imm_solve

@[opt_imm] theorem imm64Sub_spec {t : Ty} (ht : t ≠ .i128) (b c : BitVec t.width) :
    Rust.imm64Sub (CTy.ofClif t) (imm64OfBits b) (imm64OfBits c) = .ok (imm64OfBits (b - c)) := by
  imm_pre [Rust.imm64Sub]
  imm_cases t b c <;> imm_solve

@[opt_imm] theorem imm64Mul_spec {t : Ty} (ht : t ≠ .i128) (b c : BitVec t.width) :
    Rust.imm64Mul (CTy.ofClif t) (imm64OfBits b) (imm64OfBits c) = .ok (imm64OfBits (b * c)) := by
  imm_pre [Rust.imm64Mul]
  imm_cases t b c <;> imm_solve

@[opt_imm] theorem imm64And_spec {t : Ty} (ht : t ≠ .i128) (b c : BitVec t.width) :
    Rust.imm64And (CTy.ofClif t) (imm64OfBits b) (imm64OfBits c) = .ok (imm64OfBits (b &&& c)) := by
  imm_pre [Rust.imm64And]
  imm_cases t b c <;> imm_solve

@[opt_imm] theorem imm64Or_spec {t : Ty} (ht : t ≠ .i128) (b c : BitVec t.width) :
    Rust.imm64Or (CTy.ofClif t) (imm64OfBits b) (imm64OfBits c) = .ok (imm64OfBits (b ||| c)) := by
  imm_pre [Rust.imm64Or]
  imm_cases t b c <;> imm_solve

@[opt_imm] theorem imm64Xor_spec {t : Ty} (ht : t ≠ .i128) (b c : BitVec t.width) :
    Rust.imm64Xor (CTy.ofClif t) (imm64OfBits b) (imm64OfBits c) = .ok (imm64OfBits (b ^^^ c)) := by
  imm_pre [Rust.imm64Xor]
  imm_cases t b c <;> imm_solve

@[opt_imm] theorem imm64Not_spec {t : Ty} (ht : t ≠ .i128) (b : BitVec t.width) :
    Rust.imm64Not (CTy.ofClif t) (imm64OfBits b) = .ok (imm64OfBits (~~~b)) := by
  imm_pre [Rust.imm64Not]
  imm_cases t b <;> imm_solve

@[opt_imm] theorem imm64Neg_spec {t : Ty} (ht : t ≠ .i128) (b : BitVec t.width) :
    Rust.imm64Neg (CTy.ofClif t) (imm64OfBits b) = .ok (imm64OfBits (-b)) := by
  imm_pre [Rust.imm64Neg]
  imm_cases t b <;> imm_solve

@[opt_imm] theorem imm64Umin_spec {t : Ty} (ht : t ≠ .i128) (b c : BitVec t.width) :
    Rust.imm64Umin (CTy.ofClif t) (imm64OfBits b) (imm64OfBits c) = .ok (imm64OfBits (Sem.umin b c)) := by
  imm_pre [Rust.imm64Umin]
  imm_cases t b c <;> imm_solve

@[opt_imm] theorem imm64Umax_spec {t : Ty} (ht : t ≠ .i128) (b c : BitVec t.width) :
    Rust.imm64Umax (CTy.ofClif t) (imm64OfBits b) (imm64OfBits c) = .ok (imm64OfBits (Sem.umax b c)) := by
  imm_pre [Rust.imm64Umax]
  imm_cases t b c <;> imm_solve

@[opt_imm] theorem imm64Smin_spec {t : Ty} (ht : t ≠ .i128) (b c : BitVec t.width) :
    Rust.imm64Smin (CTy.ofClif t) (imm64OfBits b) (imm64OfBits c) = .ok (imm64OfBits (Sem.smin b c)) := by
  imm_pre [Rust.imm64Smin]
  imm_cases t b c <;> imm_solve

@[opt_imm] theorem imm64Smax_spec {t : Ty} (ht : t ≠ .i128) (b c : BitVec t.width) :
    Rust.imm64Smax (CTy.ofClif t) (imm64OfBits b) (imm64OfBits c) = .ok (imm64OfBits (Sem.smax b c)) := by
  imm_pre [Rust.imm64Smax]
  imm_cases t b c <;> imm_solve

theorem imm64Icmp_eq_spec {t : Ty} (ht : t ≠ .i128) (b c : BitVec t.width) :
    Rust.imm64Icmp (CTy.ofClif t) .eq (imm64OfBits b) (imm64OfBits c) =
      .ok (imm64OfBits (Sem.icmp .eq b c)) := by
  imm_pre [Rust.imm64Icmp, Rust.u64UextendImm64, Rust.i64SextendImm64]
  imm_cases t b c <;> imm_solve

theorem imm64Icmp_ne_spec {t : Ty} (ht : t ≠ .i128) (b c : BitVec t.width) :
    Rust.imm64Icmp (CTy.ofClif t) .ne (imm64OfBits b) (imm64OfBits c) =
      .ok (imm64OfBits (Sem.icmp .ne b c)) := by
  imm_pre [Rust.imm64Icmp, Rust.u64UextendImm64, Rust.i64SextendImm64]
  imm_cases t b c <;> imm_solve

theorem imm64Icmp_slt_spec {t : Ty} (ht : t ≠ .i128) (b c : BitVec t.width) :
    Rust.imm64Icmp (CTy.ofClif t) .slt (imm64OfBits b) (imm64OfBits c) =
      .ok (imm64OfBits (Sem.icmp .slt b c)) := by
  imm_pre [Rust.imm64Icmp, Rust.u64UextendImm64, Rust.i64SextendImm64]
  imm_cases t b c <;> imm_solve

theorem imm64Icmp_sge_spec {t : Ty} (ht : t ≠ .i128) (b c : BitVec t.width) :
    Rust.imm64Icmp (CTy.ofClif t) .sge (imm64OfBits b) (imm64OfBits c) =
      .ok (imm64OfBits (Sem.icmp .sge b c)) := by
  imm_pre [Rust.imm64Icmp, Rust.u64UextendImm64, Rust.i64SextendImm64]
  imm_cases t b c <;> imm_solve

theorem imm64Icmp_sgt_spec {t : Ty} (ht : t ≠ .i128) (b c : BitVec t.width) :
    Rust.imm64Icmp (CTy.ofClif t) .sgt (imm64OfBits b) (imm64OfBits c) =
      .ok (imm64OfBits (Sem.icmp .sgt b c)) := by
  imm_pre [Rust.imm64Icmp, Rust.u64UextendImm64, Rust.i64SextendImm64]
  imm_cases t b c <;> imm_solve

theorem imm64Icmp_sle_spec {t : Ty} (ht : t ≠ .i128) (b c : BitVec t.width) :
    Rust.imm64Icmp (CTy.ofClif t) .sle (imm64OfBits b) (imm64OfBits c) =
      .ok (imm64OfBits (Sem.icmp .sle b c)) := by
  imm_pre [Rust.imm64Icmp, Rust.u64UextendImm64, Rust.i64SextendImm64]
  imm_cases t b c <;> imm_solve

theorem imm64Icmp_ult_spec {t : Ty} (ht : t ≠ .i128) (b c : BitVec t.width) :
    Rust.imm64Icmp (CTy.ofClif t) .ult (imm64OfBits b) (imm64OfBits c) =
      .ok (imm64OfBits (Sem.icmp .ult b c)) := by
  imm_pre [Rust.imm64Icmp, Rust.u64UextendImm64, Rust.i64SextendImm64]
  imm_cases t b c <;> imm_solve

theorem imm64Icmp_uge_spec {t : Ty} (ht : t ≠ .i128) (b c : BitVec t.width) :
    Rust.imm64Icmp (CTy.ofClif t) .uge (imm64OfBits b) (imm64OfBits c) =
      .ok (imm64OfBits (Sem.icmp .uge b c)) := by
  imm_pre [Rust.imm64Icmp, Rust.u64UextendImm64, Rust.i64SextendImm64]
  imm_cases t b c <;> imm_solve

theorem imm64Icmp_ugt_spec {t : Ty} (ht : t ≠ .i128) (b c : BitVec t.width) :
    Rust.imm64Icmp (CTy.ofClif t) .ugt (imm64OfBits b) (imm64OfBits c) =
      .ok (imm64OfBits (Sem.icmp .ugt b c)) := by
  imm_pre [Rust.imm64Icmp, Rust.u64UextendImm64, Rust.i64SextendImm64]
  imm_cases t b c <;> imm_solve

theorem imm64Icmp_ule_spec {t : Ty} (ht : t ≠ .i128) (b c : BitVec t.width) :
    Rust.imm64Icmp (CTy.ofClif t) .ule (imm64OfBits b) (imm64OfBits c) =
      .ok (imm64OfBits (Sem.icmp .ule b c)) := by
  imm_pre [Rust.imm64Icmp, Rust.u64UextendImm64, Rust.i64SextendImm64]
  imm_cases t b c <;> imm_solve

@[opt_imm] theorem imm64Icmp_spec {t : Ty} (ht : t ≠ .i128) (cc : IntCC) (b c : BitVec t.width) :
    Rust.imm64Icmp (CTy.ofClif t) cc (imm64OfBits b) (imm64OfBits c) =
      .ok (imm64OfBits (Sem.icmp cc b c)) := by
  cases cc
  · exact imm64Icmp_eq_spec ht b c
  · exact imm64Icmp_ne_spec ht b c
  · exact imm64Icmp_slt_spec ht b c
  · exact imm64Icmp_sge_spec ht b c
  · exact imm64Icmp_sgt_spec ht b c
  · exact imm64Icmp_sle_spec ht b c
  · exact imm64Icmp_ult_spec ht b c
  · exact imm64Icmp_uge_spec ht b c
  · exact imm64Icmp_ugt_spec ht b c
  · exact imm64Icmp_ule_spec ht b c

/-- `imm64_masked` of the `u64` of a presented immediate (`u64_from_imm64`: its bits). -/
@[opt_imm] theorem imm64Masked_spec {t t' : Ty} (ht : t ≠ .i128) (ht' : t' ≠ .i128) (b : BitVec t.width) :
    Rust.imm64Masked (CTy.ofClif t') (b.toNat : Int) = .ok (imm64OfBits (b.setWidth t'.width)) := by
  imm_pre [Rust.imm64Masked]
  imm_cases t b <;> imm_cases t' <;> imm_solve

end Opt.Proof

namespace Opt.Proof
attribute [opt_imm] asU64_imm64OfBits
end Opt.Proof

/-! ## Bit counting: `u64::leading_zeros`/`trailing_zeros` as `BitVec.clz`/`ctz` -/

namespace Opt.Proof

open Isle Isle.Opt Clif

theorem clz64_eq (x : Int) : Rust.clz64 x = (BitVec.ofInt 64 x).clz.toNat := by
  unfold Rust.clz64 Rust.asU64
  generalize BitVec.ofInt 64 x = b
  simp only [Int.toNat_natCast]
  by_cases h0 : b = 0#64
  · subst h0; simp
  · have hn : b.toNat ≠ 0 := by intro h; exact h0 (BitVec.eq_of_toNat_eq (by simpa using h))
    have hlt := BitVec.clz_lt_iff_ne_zero.2 h0
    have h1 := BitVec.two_pow_sub_clz_le_toNat_of_ne_zero (by decide) h0
    have h2 := BitVec.toNat_lt_two_pow_sub_clz (x := b)
    have hc : b.clz.toNat < 64 := by
      have := BitVec.lt_def.1 hlt; simpa using this
    have hl : b.toNat.log2 = 63 - b.clz.toNat := by
      rw [Nat.log2_eq_iff hn]
      refine ⟨by simpa using h1, ?_⟩
      have : 63 - b.clz.toNat + 1 = 64 - b.clz.toNat := by omega
      rw [this]; exact h2
    simp only [hn, beq_iff_eq, ite_false, hl]
    omega

theorem ctz64_go (j : Nat) : ∀ (n k f : Nat), (∀ i < j, n.testBit i = false) → n.testBit j = true →
    j < f → Rust.ctz64.go n k f = k + j := by
  induction j with
  | zero =>
    intro n k f _ hj hf
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    have : n % 2 = 1 := by simpa [Nat.testBit_zero] using hj
    simp [Rust.ctz64.go, this]
  | succ j ih =>
    intro n k f hb hj hf
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    have h0 : n % 2 = 0 := by
      have := hb 0 (by omega); simp [Nat.testBit_zero] at this; omega
    simp only [Rust.ctz64.go, h0]
    simp only [Nat.zero_ne_one, beq_iff_eq, ite_false]
    rw [ih (n / 2) (k + 1) f (fun i hi => by rw [← Nat.testBit_succ]; exact hb _ (by omega))
      (by rw [← Nat.testBit_succ]; exact hj) (by omega)]
    omega

theorem ctz64_eq (x : Int) : Rust.ctz64 x = (BitVec.ofInt 64 x).ctz.toNat := by
  unfold Rust.ctz64 Rust.asU64
  generalize BitVec.ofInt 64 x = b
  simp only [Int.toNat_natCast]
  by_cases h0 : b = 0#64
  · subst h0
    have : (0#64).ctz = 64#64 := by
      rw [BitVec.ctz_eq_reverse_clz]; exact BitVec.clz_eq_iff_eq_zero.2 (by simp)
    simp [this]
  · have hn : b.toNat ≠ 0 := by intro h; exact h0 (BitVec.eq_of_toNat_eq (by simpa using h))
    have hlt : b.ctz.toNat < 64 := by
      have := BitVec.lt_def.1 (BitVec.ctz_lt_iff_ne_zero.2 h0); simpa using this
    simp only [hn, beq_iff_eq, ite_false]
    rw [ctz64_go b.ctz.toNat b.toNat 0 64 ?_ ?_ hlt]
    · omega
    · intro i hi
      have := BitVec.getLsbD_false_of_lt_ctz (x := b) hi
      simpa [BitVec.getLsbD] using this
    · have := BitVec.getLsbD_true_ctz_of_ne_zero h0
      simpa [BitVec.getLsbD] using this


theorem clz_aux {w : Nat} (hw : w ≤ 64) (b : BitVec w)
    (h1 : (b.setWidth 64).clz = b.clz.setWidth 64 + BitVec.ofNat 64 (64 - w)) :
    (b.setWidth 64).clz.toNat = b.clz.toNat + (64 - w) ∧ b.clz.toNat ≤ w := by
  have h2 : b.clz.toNat ≤ w := by
    have := BitVec.le_def.1 (BitVec.clz_le (x := b))
    have hlt : w < 2 ^ w := Nat.lt_two_pow_self
    simpa [Nat.mod_eq_of_lt hlt] using this
  have hc : b.clz.toNat < 2 ^ 64 := by omega
  refine ⟨?_, h2⟩
  rw [h1, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc,
    Nat.mod_eq_of_lt (a := 64 - w) (by omega), Nat.mod_eq_of_lt (by omega)]

theorem clz_setWidth_toNat {t : Ty} (ht : t ≠ .i128) (b : BitVec t.width) :
    (b.setWidth 64).clz.toNat = b.clz.toNat + (64 - t.width) ∧ b.clz.toNat ≤ t.width := by
  revert b
  cases t
  · intro b; exact clz_aux (by decide) b (by opt_widths; simp only [Ty.width, Nat.reduceSub]; bv_decide)
  · intro b; exact clz_aux (by decide) b (by opt_widths; simp only [Ty.width, Nat.reduceSub]; bv_decide)
  · intro b; exact clz_aux (by decide) b (by opt_widths; simp only [Ty.width, Nat.reduceSub]; bv_decide)
  · intro b; exact clz_aux (by decide) b (by opt_widths; simp only [Ty.width, Nat.reduceSub]; bv_decide)
  · exact absurd rfl ht

theorem imm64OfBits_of_lt {w : Nat} (b : BitVec w) (h : b.toNat < 2 ^ 63) :
    imm64OfBits b = b.toNat := by
  simp only [imm64OfBits, Rust.asI64, BitVec.toInt_ofInt]
  have h' : (b.toNat : Int) < 2 ^ 63 := by exact_mod_cast h
  simp only [Nat.reducePow, Int.reducePow] at h' ⊢
  rw [Int.bmod_eq_emod_of_lt] <;> rw [Int.emod_eq_of_lt] <;> omega

@[opt_imm] theorem imm64Clz_spec {t : Ty} (ht : t ≠ .i128) (b : BitVec t.width) :
    Rust.imm64Clz (CTy.ofClif t) (imm64OfBits b) = .ok (imm64OfBits (Sem.clz b)) := by
  imm_pre [Rust.imm64Clz]
  have hw : t.width ≤ 64 := by cases t <;> simp_all [Ty.width]
  have e : BitVec.ofInt 64 (imm64OfBits b) = b.setWidth 64 := by
    rw [imm64OfBits_eq hw, BitVec.ofInt_toInt]
  obtain ⟨h1, h2⟩ := clz_setWidth_toNat ht b
  rw [clz64_eq, e, h1, if_neg (show ¬ (b.clz.toNat + (64 - t.width) < 64 - t.width) by omega), Sem.clz, imm64OfBits_of_lt _ (by omega)]
  congr 1
  omega

theorem ctz_aux {w : Nat} (hw : w ≤ 64) (b : BitVec w)
    (h1 : b = 0#w ∨ (b.setWidth 64).ctz = b.ctz.setWidth 64) :
    b ≠ 0#w → (b.setWidth 64).ctz.toNat = b.ctz.toNat := by
  intro hb
  rcases h1 with h | h
  · exact absurd h hb
  · rw [h, BitVec.toNat_setWidth, Nat.mod_eq_of_lt]
    exact Nat.lt_of_lt_of_le b.ctz.isLt (Nat.pow_le_pow_right (by decide) hw)

theorem ctz_setWidth_toNat {t : Ty} (ht : t ≠ .i128) (b : BitVec t.width) :
    b ≠ 0#t.width → (b.setWidth 64).ctz.toNat = b.ctz.toNat := by
  revert b
  cases t
  · intro b; exact ctz_aux (by decide) b (by opt_widths; simp only [Ty.width]; bv_decide)
  · intro b; exact ctz_aux (by decide) b (by opt_widths; simp only [Ty.width]; bv_decide)
  · intro b; exact ctz_aux (by decide) b (by opt_widths; simp only [Ty.width]; bv_decide)
  · intro b; exact ctz_aux (by decide) b (by opt_widths; simp only [Ty.width]; bv_decide)
  · exact absurd rfl ht

theorem ctz_zero_toNat (w : Nat) : (0#w).ctz.toNat = w := by
  have : (0#w).ctz = BitVec.ofNat w w := by
    rw [BitVec.ctz_eq_reverse_clz]; exact BitVec.clz_eq_iff_eq_zero.2 (by simp)
  rw [this, BitVec.toNat_ofNat, Nat.mod_eq_of_lt Nat.lt_two_pow_self]

@[opt_imm] theorem imm64Ctz_spec {t : Ty} (ht : t ≠ .i128) (b : BitVec t.width) :
    Rust.imm64Ctz (CTy.ofClif t) (imm64OfBits b) = .ok (imm64OfBits (Sem.ctz b)) := by
  imm_pre [Rust.imm64Ctz]
  have hw : t.width ≤ 64 := by cases t <;> simp_all [Ty.width]
  have e : BitVec.ofInt 64 (imm64OfBits b) = b.setWidth 64 := by
    rw [imm64OfBits_eq hw, BitVec.ofInt_toInt]
  rw [asU64_imm64OfBits ht, ctz64_eq, e, Sem.ctz]
  by_cases hb : b = 0#t.width
  · subst hb
    rw [imm64OfBits_of_lt _ (by rw [ctz_zero_toNat]; omega), ctz_zero_toNat]
    simp
  · have hn : b.toNat ≠ 0 := fun h => hb (BitVec.eq_of_toNat_eq (by simpa using h))
    have hl := ctz_setWidth_toNat ht b hb
    have hlt : b.ctz.toNat < 2 ^ 63 := by
      have h1 := BitVec.lt_def.1 (BitVec.ctz_lt_iff_ne_zero.2 hb)
      simp only [BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt Nat.lt_two_pow_self] at h1
      omega
    rw [imm64OfBits_of_lt _ hlt, hl]
    simp [hn]

end Opt.Proof
