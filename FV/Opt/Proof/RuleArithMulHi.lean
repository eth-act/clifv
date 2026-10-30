import FV.Opt.Proof.RuleRestEmbedSshr
import FV.Opt.Proof.RuleRestEmbedRotl
import FV.Opt.Proof.RuleRestEmbedRotr
import FV.Opt.Proof.RuleArithMulHiSem
import FV.Opt.Proof.RuleInfraIcmp

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option Elab.async false

namespace Opt.Proof

open Isle Isle.Opt Clif
attribute [local implicit_reducible] Ty.width

/-- The half-width guard splits only the wide type, preserving `ofClif` injectivity. -/
theorem mulhi_halfWidth_ofClif (t : Ty) :
    (CTy.ofClif t).halfWidth? =
      match t with
      | .i8 => none
      | .i16 => some (CTy.ofClif .i8)
      | .i32 => some (CTy.ofClif .i16)
      | .i64 => some (CTy.ofClif .i32)
      | .i128 => some (CTy.ofClif .i64)
      | .f32 => some (.float 16)
      | .f64 => some (CTy.ofClif .f32) := by
  cases t <;> rfl

-- Only the matched extensions' output type controls the half-width guard.
-- Splitting every type first repeats interpreter evaluation for irrelevant combinations.
open Lean Meta Elab Tactic in
elab "mulhi_cases_wide" : tactic => withMainContext do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if let some e := d.type.find? (fun e => e.isAppOfArity ``Clif.Inst.extend 3) then
      let t := e.appFn!.appArg!
      if t.isFVar then
        let goals ← (← getMainGoal).cases t.fvarId!
        replaceMainGoal (goals.toList.map (·.mvarId))
        return
  throwError "mulhi_cases_wide: no variable extension output type"

-- Resolve the original half-width and shift guards before constructing the nested RHS.
-- The graph model supplies the operand types; no additional typing premise is assumed.
set_option hygiene false in
local macro "mulhi_rule_prefix " r:ident : tactic => `(tactic| (
  rule_intro $r
  rule_lhs_g hG
  all_goals try opt_den_subst
  all_goals try opt_val_ty_subst
  opt_cases_val
  all_goals (try simp only [Val.ty, Val.bits] at *; subst_vars)
  all_goals simp (disch := assumption) only [asU64_imm64OfBits] at *
  all_goals mulhi_cases_wide
  all_goals rule_iflets_c [mulhi_halfWidth_ofClif, CTy.ofClif_beq,
    beq_iff_eq, Ty.width, Nat.reduceBEq, Nat.reduceLT, Nat.reduceMul,
    Int.reduceNatCast, Int.reduceNatCast', Option.map_some, Option.map_none]
  all_goals subst_vars
  opt_widths
  all_goals simp only [Ty.width, Nat.reduceLT] at *
  all_goals try contradiction
  all_goals simp (disch := assumption) only [asU64_imm64OfBits,
    Int.natCast_inj, natCast_eq_lit,
    Sem.shift, Option.some.injEq] at *
  opt_destruct
  all_goals subst_vars
  all_goals rule_rhs_c [Interp.matchAll.eq_1, Interp.matchAll.eq_2]
  all_goals opt_some_subst
  all_goals try opt_den_subst
  all_goals (apply GraphOk.make_val hG (by opt_P); opt_node_x)
  all_goals try decide
  all_goals apply val_congr
  all_goals simp [Sem.binary, Sem.imul, Sem.sshr, Sem.ushr, Sem.shiftAmt,
    Rust.asU64, Rust.asI64, Rust.band64, Ty.width, *]))

/-- `arithmetic.isle:200`: signed high product through the original half-width guards. -/
theorem ok_rule_arithmetic_200 {p : Isle.Program} (hd : Data p) :
    RuleOk p rule_arithmetic_200 := by
  mulhi_rule_prefix rule_arithmetic_200
  all_goals first
    | (apply mulhi_signed; decide)
    | (symm; apply mulhi_signed; decide)

/-- `arithmetic.isle:206`: unsigned high product through the original half-width guards. -/
theorem ok_rule_arithmetic_206 {p : Isle.Program} (hd : Data p) :
    RuleOk p rule_arithmetic_206 := by
  mulhi_rule_prefix rule_arithmetic_206
  all_goals first
    | exact mulhi_unsigned _ _
    | exact (mulhi_unsigned _ _).symm

-- All four valid integer half-width guards, including the i64 -> i128 boundary.
example :
    [(Ty.i16, Ty.i8), (.i32, .i16), (.i64, .i32), (.i128, .i64)].map
      (fun (wide, half) => ((CTy.ofClif wide).halfWidth?, Rust.tyBits (CTy.ofClif half))) =
    [(some (CTy.int 8), .ok 8), (some (.int 16), .ok 16),
      (some (.int 32), .ok 32), (some (.int 64), .ok 64)] := rfl
example : (CTy.ofClif .i128).halfWidth? = some (CTy.ofClif .i64) :=
  mulhi_halfWidth_ofClif .i128

-- Inhabited signed rule guards and extrema. These are ordinary computations, not SAT proofs.
example : (CTy.ofClif .i16).halfWidth? = some (CTy.ofClif .i8) ∧
    Rust.tyBits (CTy.ofClif .i8) = .ok 8 ∧
    Sem.sshr (Sem.imul (Sem.sextend 16 (128#8)) (Sem.sextend 16 (128#8))) (8#16) =
      Sem.sextend 16 (Sem.smulhi (128#8) (128#8)) := ⟨rfl, rfl, by decide⟩
example : (CTy.ofClif .i32).halfWidth? = some (CTy.ofClif .i16) ∧
    Rust.tyBits (CTy.ofClif .i16) = .ok 16 ∧
    Sem.sshr (Sem.imul (Sem.sextend 32 (0x8000#16)) (Sem.sextend 32 (0x7fff#16))) (16#32) =
      Sem.sextend 32 (Sem.smulhi (0x8000#16) (0x7fff#16)) := ⟨rfl, rfl, by decide⟩
example : (CTy.ofClif .i64).halfWidth? = some (CTy.ofClif .i32) ∧
    Rust.tyBits (CTy.ofClif .i32) = .ok 32 ∧
    Sem.sshr (Sem.imul (Sem.sextend 64 (0x80000000#32))
      (Sem.sextend 64 (0x80000000#32))) (32#64) =
      Sem.sextend 64 (Sem.smulhi (0x80000000#32) (0x80000000#32)) := ⟨rfl, rfl, by decide⟩
example : (CTy.ofClif .i128).halfWidth? = some (CTy.ofClif .i64) ∧
    Rust.tyBits (CTy.ofClif .i64) = .ok 64 ∧
    Sem.sshr (Sem.imul (Sem.sextend 128 (0x8000000000000000#64))
      (Sem.sextend 128 (0x7fffffffffffffff#64))) (64#64) =
      Sem.sextend 128 (Sem.smulhi (0x8000000000000000#64) (0x7fffffffffffffff#64)) :=
  ⟨rfl, rfl, by decide⟩

-- Inhabited unsigned rule guards with both input high bits set.
example : (CTy.ofClif .i16).halfWidth? = some (CTy.ofClif .i8) ∧
    Rust.tyBits (CTy.ofClif .i8) = .ok 8 ∧
    Sem.ushr (Sem.imul (Sem.uextend 16 (255#8)) (Sem.uextend 16 (128#8))) (8#16) =
      Sem.uextend 16 (Sem.umulhi (255#8) (128#8)) := ⟨rfl, rfl, by decide⟩
example : (CTy.ofClif .i32).halfWidth? = some (CTy.ofClif .i16) ∧
    Rust.tyBits (CTy.ofClif .i16) = .ok 16 ∧
    Sem.ushr (Sem.imul (Sem.uextend 32 (0xffff#16)) (Sem.uextend 32 (0x8000#16))) (16#32) =
      Sem.uextend 32 (Sem.umulhi (0xffff#16) (0x8000#16)) := ⟨rfl, rfl, by decide⟩
example : (CTy.ofClif .i64).halfWidth? = some (CTy.ofClif .i32) ∧
    Rust.tyBits (CTy.ofClif .i32) = .ok 32 ∧
    Sem.ushr (Sem.imul (Sem.uextend 64 (0xffffffff#32))
      (Sem.uextend 64 (0x80000000#32))) (32#64) =
      Sem.uextend 64 (Sem.umulhi (0xffffffff#32) (0x80000000#32)) := ⟨rfl, rfl, by decide⟩
example : (CTy.ofClif .i128).halfWidth? = some (CTy.ofClif .i64) ∧
    Rust.tyBits (CTy.ofClif .i64) = .ok 64 ∧
    Sem.ushr (Sem.imul (Sem.uextend 128 (0xffffffffffffffff#64))
      (Sem.uextend 128 (0x8000000000000000#64))) (64#64) =
      Sem.uextend 128 (Sem.umulhi (0xffffffffffffffff#64) (0x8000000000000000#64)) :=
  ⟨rfl, rfl, by decide⟩

end Opt.Proof
