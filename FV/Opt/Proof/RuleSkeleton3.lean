import FV.Opt.Proof.RuleSkelEmbed
import FV.Opt.Proof.RuleInfraDivConst

/-!
# `simplify_skeleton` rules: division by a constant via magic numbers

`arithmetic.isle` 114, 117, 122, 125, 157, 160, 165, 168 replace `udiv`/`urem`/`sdiv`/`srem` by a
non-power-of-two constant with Cranelift's `div_const` sequences (`apply_div_const_magic_*`,
`prelude_opt.isle`). The correctness of the magic numbers is `DivConst.magicU_spec` /
`DivConst.magicS_spec` (`FV/Opt/Proof/RuleInfraDivConst.lean`).

The template is `skel_auto_div_i` with three changes: the magic numbers are generalized (their
specification is rewritten into the right-hand side's evaluation, `skel_rhs_dc`, with the
range facts the `iconst` constructors check), the evaluation also unfolds `matchAll` (the
`and` pattern of `u32_extract_non_zero` in `apply_div_const_magic_*_maybe_shift`), and the made
`iconst` nodes are evaluated by `rfl` (`divc_den`: their immediates have type `BitVec 64`, not
`BitVec Ty.i64.width`, so `evalNode_iconst` does not rewrite). The bit-level goal is closed by the
`divc_*` sequence lemmas below.
-/

set_option linter.unusedSimpArgs false
set_option Elab.async false

namespace Opt.Proof

open Isle Isle.Opt Isle.Interp Clif

/-! ## Evaluation helpers -/

@[opt_monad] theorem divc_dcm_data (ty : TypeId) (fs : List V) : dcm ty fs = .data ty 0 fs := rfl

theorem divc_false_beq_true : ((false == true) = true) = False := by decide
theorem divc_true_beq_true : ((true == true) = true) = True := by decide

syntax "divc_den" : tactic
syntax "divc_node" : tactic

set_option hygiene false in
macro_rules
  | `(tactic| divc_den) => `(tactic| first
      | (apply Valuation.le_trans hle1 hle3; assumption)
      | (apply GraphOk.make_val hG (by opt_P); rfl)
      | (apply GraphOk.make_val hG (by opt_P); divc_node)
      | (apply GraphOk.make_le hG (by opt_P); divc_den))

set_option hygiene false in
macro_rules
  | `(tactic| divc_node) => `(tactic| (
      simp only [evalNode_binary_iff, evalNode_unary, evalNode_icmp, evalNode_iconst,
        evalNode_select, evalNode_bitselect, evalNode_bmask, evalNode_uextend, evalNode_sextend,
        evalNode_ireduce,
        Clif.BinaryOp.isShift, Bool.false_eq_true, ite_false, ite_true, Clif.Frame.regs]
      repeat (first | (apply Exists.intro) | (apply And.intro) | divc_den)
      all_goals (try rfl)))

/-- Phase 3 with extra rewrite facts (the magic numbers and their ranges); `matchAll` (the `and`
pattern) is unfolded too. -/
syntax "skel_rhs_dc" ("[" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|>
  Lean.Parser.Tactic.simpLemma),* "]")? : tactic

set_option hygiene false in
macro_rules
  | `(tactic| skel_rhs_dc [$ts,*]) => `(tactic| (
      opt_eval hev [$ts,*]
      repeat' (first
        | (rw [Isle.Interp.matchAll.eq_2] at hev; opt_eval hev [$ts,*])
        | (rw [Isle.Interp.matchAll.eq_1] at hev; opt_eval hev [$ts,*])
        | (split at hev <;> try opt_norm hev [$ts,*]))
      all_goals (try simp only [Option.map_eq_some_iff, Option.map_eq_none_iff] at *)
      opt_destruct
      all_goals subst_vars
      all_goals (
        simp only [Except.ok.injEq, Prod.mk.injEq] at hev
        obtain ⟨rfl, rfl, rfl⟩ := hev
        simp only [List.mem_singleton, List.mem_cons, List.not_mem_nil, or_false] at hw <;>
        subst hw)
      all_goals opt_types))

set_option hygiene false in
/-- Phase 4 for a `div` replaced by the magic sequence: no trap, then the value goal
`⟨t, divVal⟩ = ⟨t, sequence⟩` (the made nodes evaluated by `divc_node`), left to the caller. -/
macro "skel_div_dc" : tactic => `(tactic| (
  skel_good
  apply skel_div_rwv (hle4 _ _ (by opt_den)) (hle4 _ _ (by opt_den))
  intro a b ha hb
  opt_destruct
  all_goals subst_vars
  skel_imm
  refine ⟨?_, ?_⟩
  · simp only [divOk]
    first | exact ‹(_ != _) = true› | rule_bits
  simp only [divVal]
  apply hle4
  try dsimp only
  apply GraphOk.make_val hG (by opt_P)
  divc_node))

/-! ## The unsigned sequences -/

theorem divc_shift_amt {w s : Nat} (hs : s < w) : (BitVec.ofNat w s).toNat % w = s := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans hs (Nat.lt_pow_self (by omega))),
    Nat.mod_eq_of_lt hs]

/-- `umulhi x m >> s` (`apply_div_const_magic_*_maybe_add`, `do_add = false`). -/
theorem divc_udiv_noadd {w : Nat} (hw : w ≤ 64) {x b : BitVec w} {m s : Nat} (hm : m < 2 ^ w)
    (hs : s < w) (h : ∀ X < 2 ^ w, X * m / 2 ^ w / 2 ^ s = X / b.toNat) :
    x / b = Sem.ushr (Sem.binary BinaryOp.umulhi x (BitVec.ofInt w (Rust.asI64 (m : Int))))
      (BitVec.ofInt w (Rust.asI64 (s : Int))) := by
  rw [DivConst.divc_ofInt_asI64 hw, DivConst.divc_ofInt_asI64 hw, BitVec.ofInt_natCast,
    BitVec.ofInt_natCast]
  simp only [Sem.binary, Sem.ushr, Sem.shiftAmt]
  rw [divc_shift_amt hs]
  exact (DivConst.udiv_magic_noadd x b m s hm h).symm

/-- `(umulhi x m + ((x - umulhi x m) >> 1)) >> (s - 1)` (`do_add = true`). -/
theorem divc_udiv_add {w : Nat} (hw : w ≤ 64) (hw2 : 2 ≤ w) {x b : BitVec w} {m s : Nat}
    (hm : m < 2 ^ w) (hs1 : 1 ≤ s) (hs : s ≤ w)
    (h : ∀ X < 2 ^ w, ((X - X * m / 2 ^ w) / 2 + X * m / 2 ^ w) / 2 ^ (s - 1) = X / b.toNat) :
    x / b = Sem.ushr (Sem.binary BinaryOp.iadd
        (Sem.binary BinaryOp.umulhi x (BitVec.ofInt w (Rust.asI64 (m : Int))))
        (Sem.ushr (Sem.binary BinaryOp.isub x
          (Sem.binary BinaryOp.umulhi x (BitVec.ofInt w (Rust.asI64 (m : Int)))))
          (BitVec.ofInt w 1)))
      (BitVec.ofInt w (Rust.asI64 ((s : Int) - 1))) := by
  rw [DivConst.divc_ofInt_asI64 hw, DivConst.divc_ofInt_asI64 hw,
    show ((s : Int) - 1) = ((s - 1 : Nat) : Int) by omega, show (1 : Int) = ((1 : Nat) : Int) from rfl,
    BitVec.ofInt_natCast, BitVec.ofInt_natCast, BitVec.ofInt_natCast]
  simp only [Sem.binary, Sem.ushr, Sem.shiftAmt, Sem.iadd, Sem.isub]
  rw [divc_shift_amt (by omega), divc_shift_amt (by omega), BitVec.add_comm]
  exact (DivConst.udiv_magic_add x b m s hm h).symm

/-- `x - q * d` with `q = x / d` (`apply_div_const_magic_*_finish`, `urem`). -/
theorem divc_urem {w : Nat} (hw : w ≤ 64) {x b q : BitVec w} (hq : x / b = q) :
    x % b = Sem.binary BinaryOp.isub x
      (Sem.binary BinaryOp.imul q (BitVec.ofInt w (Rust.asI64 (b.toNat : Int)))) := by
  have hb : BitVec.ofNat w b.toNat = b := by
    apply BitVec.eq_of_toNat_eq; simp [Nat.mod_eq_of_lt b.isLt]
  rw [DivConst.divc_ofInt_asI64 hw, BitVec.ofInt_natCast, hb]
  simp only [Sem.binary, Sem.isub, Sem.imul]
  rw [← hq, DivConst.urem_of_udiv]

/-- The magic numbers of an unsigned divisor `b` (nonzero, not a power of two). -/
theorem divc_magicU {w : Nat} (hw : 1 ≤ w) {b : BitVec w} (hnz : (b != 0#w) = true)
    (hc : (Rust.isPow2 (b.toNat : Int) == false) = true) :
    (b.toNat : Int) ≤ 2 ^ w - 1 ∧ ∃ m s : Nat, m < 2 ^ w ∧
      ((Rust.magicU w ((b.toNat : Int)).toNat = (m, false, (s : Int)) ∧ s < w ∧
          ∀ X < 2 ^ w, X * m / 2 ^ w / 2 ^ s = X / b.toNat) ∨
       (Rust.magicU w ((b.toNat : Int)).toNat = (m, true, (s : Int)) ∧ 1 ≤ s ∧ s ≤ w ∧
          ∀ X < 2 ^ w, ((X - X * m / 2 ^ w) / 2 + X * m / 2 ^ w) / 2 ^ (s - 1) = X / b.toNat)) := by
  have hpow := DivConst.not_pow_of_isPow2 (by simpa using hc)
  have h0 : b.toNat ≠ 0 := by
    intro h; simp [BitVec.toNat_eq, h] at hnz
  have h1 := hpow 0
  rw [Int.toNat_natCast]
  have hb := b.isLt
  exact ⟨by rw [DivConst.two_pow_int]; omega, DivConst.magicU_spec hw (by simp at h1; omega) b.isLt hpow⟩

/-! ## Rules -/

set_option hygiene false in
/-- Phases 3-4 of the unsigned rules: `w` the width, `sub` the `u32_sub`/`u64_sub` name of the
shift decrement. The magic numbers come from `divc_magicU`; per `do_add` case the right-hand side
is evaluated with their facts and closed by `divc_udiv_noadd`/`divc_udiv_add` (`udiv`) or
`divc_urem` (`urem`). -/
macro "skel_dcu_rest " w:num sub:str : tactic => `(tactic| (
  all_goals (skel_rule_iflets; skel_iflets)
  all_goals skel_imm
  all_goals (
    obtain ⟨hb, m, s, hm, ⟨hmag, hs, hcorr⟩ | ⟨hmag, hs1, hs2, hcorr⟩⟩ :=
      divc_magicU (w := $w) (by decide) (by assumption) (by assumption)
    · have hm1 : (m : Int) ≤ 2 ^ $w - 1 := by omega
      have hs3 : (s : Int) ≤ 2 ^ $w - 1 := by omega
      have hsu : Rust.asU32 (s : Int) = (s : Int) := by
        simp only [Rust.asU32, BitVec.ofInt_natCast, BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt (by omega)]
      skel_rhs_dc [hmag, hm1, hs3, hsu, hb, Ty.width, divc_false_beq_true, Nat.reduceBEq]
      all_goals clear hmag hm1 hs3 hsu hb
      all_goals skel_div_dc
      all_goals (
        apply val_congr
        first
          | exact divc_udiv_noadd (by decide) hm hs hcorr
          | exact divc_urem (by decide) (divc_udiv_noadd (by decide) hm hs hcorr))
    · have hm1 : (m : Int) ≤ 2 ^ $w - 1 := by omega
      have hs3 : (s : Int) ≤ 2 ^ $w - 1 := by omega
      have hsu : Rust.asU32 (s : Int) = (s : Int) := by
        simp only [Rust.asU32, BitVec.ofInt_natCast, BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt (by omega)]
      have hs0 : ((s : Int) == 0) = false := by simp; omega
      have hs0' : ((s : Int) != 0) = true := by simp; omega
      have hs4 : (s : Int) ≥ 1 := by omega
      have hs5 : (s : Int) - 1 ≤ 2 ^ $w - 1 := by omega
      have hsub : Rust.checkedSubU $sub (s : Int) 1 = pure ((s : Int) - 1) := by
        unfold Rust.checkedSubU; split <;> first | rfl | (exfalso; omega)
      skel_rhs_dc [hmag, hm1, hs3, hsu, hs0, hs0', hs4, hs5, hsub, hb, Ty.width,
        divc_true_beq_true, Nat.reduceBEq]
      all_goals clear hmag hm1 hs3 hsu hs0 hs0' hs4 hs5 hsub hb
      all_goals skel_div_dc
      all_goals (
        apply val_congr
        first
          | exact divc_udiv_add (by decide) (by decide) hm hs1 hs2 hcorr
          | exact divc_urem (by decide) (divc_udiv_add (by decide) (by decide) hm hs1 hs2 hcorr)))))

set_option hygiene false in
/-- The unsigned template at width 64. -/
macro "skel_auto_dcu64 " r:ident : tactic => `(tactic| (
  skel_intro $r
  rule_lhs hG
  skel_reads
  rule_lhs hG
  skel_dcu_rest 64 "u64_sub"))

set_option hygiene false in
/-- The unsigned template at width 32. The left-hand side is unfolded by hand: `rule_lhs` reaches
the maximum recursion depth on the `u32_from_u64` fact `inU32 (asU64 imm)` before the immediate's
type is known; here the read values come first (`skel_reads`, `opt_model`), the type is
substituted, and the (redundant) `inU32` fact is dropped. -/
macro "skel_auto_dcu32 " r:ident : tactic => `(tactic| (
  skel_intro $r
  iterate 5 (any_goals (first
    | (opt_guard lhs_step; opt_destruct; all_goals subst_vars)
    | opt_model hG
    | (lhs_step'; opt_destruct; all_goals subst_vars)))
  skel_reads
  opt_model hG
  lhs_step'
  opt_destruct
  rename_i hl1 hnz hw hargs hin hr
  subst hr
  subst hl1
  lhs_step
  opt_destruct
  subst hargs
  rename_i hsem2 _ _ hsem1
  subst hsem1
  simp only [] at hsem2
  subst hsem2
  clear hin
  skel_dcu_rest 32 "u32_sub"))

set_option maxHeartbeats 16000000 in
theorem ok_rule_arithmetic_114 {p : Isle.Program} (hd : Data p) :
    SkelRuleOk p rule_arithmetic_114 := by
  skel_auto_dcu32 rule_arithmetic_114

set_option maxHeartbeats 16000000 in
theorem ok_rule_arithmetic_117 {p : Isle.Program} (hd : Data p) :
    SkelRuleOk p rule_arithmetic_117 := by
  skel_auto_dcu64 rule_arithmetic_117

set_option maxHeartbeats 16000000 in
theorem ok_rule_arithmetic_157 {p : Isle.Program} (hd : Data p) :
    SkelRuleOk p rule_arithmetic_157 := by
  skel_auto_dcu32 rule_arithmetic_157

set_option maxHeartbeats 16000000 in
theorem ok_rule_arithmetic_160 {p : Isle.Program} (hd : Data p) :
    SkelRuleOk p rule_arithmetic_160 := by
  skel_auto_dcu64 rule_arithmetic_160

end Opt.Proof
