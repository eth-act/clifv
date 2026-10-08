import FV.Opt.Proof.RuleRestEmbed

/-!
# Constants made at a type variable (`iconst_u ty k`, `iconst_s ty k`, `iconst ty (imm64_neg ty c)`)

The right-hand sides of these rules evaluate once the rule's type variable is split on `= .i128`:
at `i128` the constructors take their `iconst_u_i128`/`iconst_s_i128` arm (`uextend`/`sextend.i128`
of an `i64` constant), elsewhere their `ty_int (fits_in_64 ty)` arm, whose if-lets the non-`i128`
specs (`tyUmax_ofClif`, `band64_umax`, `i64SextendU64_umax`, …) evaluate, and `toInst` of the made
`UnaryImm` reduces to `.iconst t (BitVec.ofInt t.width k)`. What remained was the bit-level finish:

- `rule_bits_tv`: `rule_bits_w` without the `Val` split, with contradictory `i128` cases closed after
  the type split, negations pulled out of products (`BitVec.neg_mul`/`mul_neg`: `bv_decide` does not
  finish symbolic 64-bit products), `bv_decide` (120 s SAT timeout) before `ac_rfl` (`ac_rfl` on a
  closed-width goal such as `allOnes 64 - x = ~~~x` hits the maximum recursion depth, which `first`
  does not catch).
- `rule_auto_tv`: left-hand side, `i128` split, if-lets, `rule_rhs_x`, `rule_finish_tv`.
- `imm64Neg_ofInt`: `imm64_neg` of an arbitrary immediate (not only a presented `imm64OfBits b`), with
  `asI64_asU64_cast`/`ofInt_asI64_low` for `imm64 (i64_cast_unsigned k)` (`cprop.isle` 269).
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt Clif

/-- `i64_cast_unsigned` then `imm64`: the round trip through `u64` is the identity on `i64`s. -/
theorem asI64_asU64_cast (x : Int) : Rust.asI64 (Rust.asU64 x) = Rust.asI64 x := by
  simp only [Rust.asI64, Rust.asU64, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- Reading an `i64` at a non-`i128` width only sees its low bits. -/
theorem ofInt_asI64_low {t : Ty} (ht : t ≠ .i128) (x : Int) :
    BitVec.ofInt t.width (Rust.asI64 x) = BitVec.ofInt t.width x := by
  imm_cases t <;> simp only [Rust.asI64, ofInt_toInt_signExtend] <;>
    (try simp (disch := decide) only [ofInt_eq_setWidth]) <;>
    generalize BitVec.ofInt 64 x = X <;> bv_decide

/-- `imm64_neg` of any immediate at a non-`i128` type (`imm64Neg_spec` needs a presented
immediate `imm64OfBits b`; `cprop.isle` 269 negates `imm64 (i64_cast_unsigned k)`). -/
theorem imm64Neg_ofInt {t : Ty} (ht : t ≠ .i128) (x : Int) :
    Rust.imm64Neg (CTy.ofClif t) x = .ok (imm64OfBits (-(BitVec.ofInt t.width x))) := by
  imm_pre [Rust.imm64Neg]
  imm_cases t <;> imm_solve

/-- The bit-level goal (see the module docstring). -/
macro "rule_bits_tv" : tactic => `(tactic| (
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
         | (simp only [Clif.Sem.binary, Clif.Sem.unary, Clif.Sem.imul, Clif.Sem.ineg,
              BitVec.neg_mul, BitVec.mul_neg, BitVec.neg_neg]; done)
         | (opt_cases_ty <;> (try contradiction) <;>
            (try simp (disch := decide) only [Rust.sext, ge_iff_le, Nat.reduceLeDiff, reduceIte,
              Bool.false_eq_true] at *) <;>
            opt_widths <;> sem_simp_b <;> (try int_bv) <;>
            (try simp only [BitVec.neg_mul, BitVec.mul_neg, BitVec.neg_neg]) <;>
            (try apply val_congr) <;>
            first | bv_decide (config := { timeout := 120 }) | ac_rfl))))

set_option hygiene false in
/-- `rule_finish_w` with `rule_bits_tv`. -/
macro "rule_finish_tv" : tactic => `(tactic| first
  | (try dsimp only
     apply Valuation.le_trans hle1 hle3
     opt_rw_lhs
     rule_bits_tv)
  | (try dsimp only
     apply GraphOk.make_val hG (by opt_P)
     opt_node_x
     all_goals (try (show _ < _; first | assumption | omega))
     all_goals rule_bits_tv))

/-- The template for rules making constants at their type variable (see the module docstring). -/
syntax "rule_auto_tv " ident ("[" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|> Lean.Parser.Tactic.simpLemma),* "]")? : tactic
set_option hygiene false in
macro_rules
  | `(tactic| rule_auto_tv $r:ident) => `(tactic| rule_auto_tv $r [])
  | `(tactic| rule_auto_tv $r:ident [$ts,*]) => `(tactic| (
      rule_intro $r
      rule_lhs hG
      all_goals opt_split_i128
      all_goals (first | rule_no_iflets | rule_iflets)
      all_goals (rule_rhs_x [$ts,*]; all_goals (opt_some_subst; (try opt_val_ty_subst); rule_finish_tv))))

end Opt.Proof
