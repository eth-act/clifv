import FV.Opt.Proof.RuleIcmpEmbed2

/-!
# Lean templates for the icmp/selects rules that ran out of memory

`selects.isle` 20 and `icmp.isle` 63, 70, 160, 175, 365, 368 passed with `rule_auto_f`
(`RuleIcmpEmbed2.lean`) in per-rule runs, but used more than 14G each. Here the left-hand side is
opened by `rule_lhs_g` (it also opens the model facts guarded by `P s0`), so each matched class
has its value fact. The right-hand side is evaluated by `rule_rhs_c`. `opt_den_subst` substitutes
the `Val` locals that `rule_lhs_g` leaves next to explicit values. The made node is then closed by
`GraphOk.make_val` with one of three finishers:

- `fin_bits_k`: split the remaining type, then `bv_decide` (`icmp.isle` 160, 175, 365, 368).
- `fin_icmp_not_k`: the comparison of a 0/1 `icmp` result (optionally `uextend`ed) against 0 or 1
  is its complement. These are the generic lemmas `icmp_eq_uext_icmp_zero` & co., with no type
  split of the compared values (`icmp.isle` 63, 70).
- `fin_sel_bmask_k`: `select c, -1, 0 = bmask c` at every width (`selects.isle` 20).

Each rule then runs in about 15 s and stays near 2.2G.
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Lean Meta Elab Tactic in
/-- `opt_den_subst`: for a fact `L = some x` (`x` a local) next to a fact `L = some e`,
substitute `x := e`. Repeats until no such pair is left; fails if there was none. -/
elab "opt_den_subst" : tactic => do
  let mut progress := true
  let mut any := false
  while progress do
    progress := false
    let g ← getMainGoal
    let found ← g.withContext do
      let mut hs : Array (FVarId × Lean.Expr × Lean.Expr) := #[]
      for d in ← getLCtx do
        if d.isImplementationDetail then continue
        let t ← instantiateMVars d.type
        if let some (_, l, r) := t.eq? then
          if r.isAppOfArity ``Option.some 2 && !l.hasLooseBVars then
            hs := hs.push (d.fvarId, l, r.appArg!)
      let mut res : Option (FVarId × FVarId) := none
      for (f1, l1, r1) in hs do
        if !r1.isFVar then continue
        for (f2, l2, r2) in hs do
          if f1 != f2 && l1 == l2 && r2 != r1 then
            res := some (f1, f2)
            break
        if res.isSome then break
      pure res
    if let some (f1, f2) := found then
      let n1 ← mkFreshUserName `hx
      let g ← (← getMainGoal).rename f1 n1
      replaceMainGoal [g]
      let h2 ← g.withContext do Lean.Elab.Term.exprToSyntax (mkFVar f2)
      let h1 := mkIdent n1
      evalTactic (← `(tactic| (rw [$h2:term] at $h1:ident; simp only [Option.some.injEq] at $h1:ident; subst $h1:ident)))
      progress := true
      any := true
  unless any do throwError "opt_den_subst: nothing to substitute"

end Opt.Proof

namespace Opt.Proof

open Isle Isle.Opt Clif

/-- The complement condition code negates the comparison. -/
theorem intcc_complement {w : Nat} (cc : IntCC) (x y : BitVec w) :
    Sem.intcc (Rust.intccComplement cc) x y = !(Sem.intcc cc x y) := by
  cases cc <;> simp only [Sem.intcc, Rust.intccComplement, bne, Bool.not_not, BitVec.slt, BitVec.sle,
    BitVec.ult, BitVec.ule] <;> simp only [decide_not.symm] <;> congr 1 <;> apply propext <;> omega

/-- `eq (uextend (icmp cc x y)) 0 = icmp (complement cc) x y` (`icmp.isle` 63). -/
theorem icmp_eq_uext_icmp_zero (t : Ty) (cc : IntCC) {w : Nat} (x y : BitVec w) :
    Sem.icmp .eq (Sem.uextend t.width (Sem.icmp cc x y)) (0#t.width) =
      Sem.icmp (Rust.intccComplement cc) x y := by
  simp only [Sem.icmp, intcc_complement]
  generalize Sem.intcc cc x y = b
  cases b <;> cases t <;> decide

/-- `ne (uextend (icmp cc x y)) 1 = icmp (complement cc) x y` (`icmp.isle` 70). -/
theorem icmp_ne_uext_icmp_one (t : Ty) (cc : IntCC) {w : Nat} (x y : BitVec w) :
    Sem.icmp .ne (Sem.uextend t.width (Sem.icmp cc x y)) (1#t.width) =
      Sem.icmp (Rust.intccComplement cc) x y := by
  simp only [Sem.icmp, intcc_complement]
  generalize Sem.intcc cc x y = b
  cases b <;> cases t <;> decide

/-- `eq (icmp cc x y) 0 = icmp (complement cc) x y` (`uextend_maybe` without an extend). -/
theorem icmp_eq_icmp_zero (cc : IntCC) {w : Nat} (x y : BitVec w) :
    Sem.icmp (w := Ty.i8.width) .eq (Sem.icmp cc x y) (0#Ty.i8.width) =
      Sem.icmp (Rust.intccComplement cc) x y := by
  simp only [Sem.icmp, intcc_complement]
  generalize Sem.intcc cc x y = b
  cases b <;> decide

/-- `ne (icmp cc x y) 1 = icmp (complement cc) x y` (`uextend_maybe` without an extend). -/
theorem icmp_ne_icmp_one (cc : IntCC) {w : Nat} (x y : BitVec w) :
    Sem.icmp (w := Ty.i8.width) .ne (Sem.icmp cc x y) (1#Ty.i8.width) =
      Sem.icmp (Rust.intccComplement cc) x y := by
  simp only [Sem.icmp, intcc_complement]
  generalize Sem.intcc cc x y = b
  cases b <;> decide

theorem toInt_eq_zero_iff' {w : Nat} (x : BitVec w) : x.toInt = 0 ↔ x = 0#w := by
  rw [← BitVec.toInt_zero, BitVec.toInt_inj]

/-- The shared phases: the left-hand side with `rule_lhs_g`, the if-lets (if any), the right-hand
side, `opt_den_subst`, then the made node through `GraphOk.make_val` down to a `BitVec` equation. -/
syntax "rule_pre_k " ident ("[" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|> Lean.Parser.Tactic.simpLemma),* "]")? : tactic
set_option hygiene false in
macro_rules
  | `(tactic| rule_pre_k $r:ident) => `(tactic| rule_pre_k $r [])
  | `(tactic| rule_pre_k $r:ident [$ts,*]) => `(tactic| (
      rule_intro $r
      rule_lhs_g hG
      all_goals (first | rule_no_iflets | rule_iflets_c [$ts,*])
      all_goals (rule_rhs_c [$ts,*]; opt_some_subst)
      all_goals (try opt_den_subst)
      all_goals (apply GraphOk.make_val hG (by opt_P); opt_node)
      all_goals (apply val_congr)))

/-- Split the types and decide (immediates are reduced by `sem_simp_b`'s `cond_simp`). -/
macro "fin_bits_k" : tactic => `(tactic| (
  opt_cases_ty <;> opt_widths <;> sem_simp_b <;>
    (try simp only [Int.reducePow, Int.reduceSub, Int.reduceToNat, Nat.reducePow,
      Nat.reduceSub] at *) <;>
    (try subst_vars) <;> bv_decide (config := { timeout := 120 })))

/-- An `icmp` result compared against the immediate 0 or 1: the immediate as a `BitVec`, then the
complement lemmas. -/
macro "fin_icmp_not_k" : tactic => `(tactic| (
  (try simp (disch := first | assumption | decide) only [asU64_imm64OfBits, Int.natCast_eq_zero,
    Int.natCast_inj, toNat_eq_iff_ofNat, toNat_eq_zero_iff, Int.reduceToNat, natCast_toNat_eq_int,
    Int.reduceLE, true_and] at *)
  (try opt_destruct)
  (try subst_vars)
  first
    | exact icmp_eq_uext_icmp_zero _ _ _ _
    | exact icmp_eq_icmp_zero _ _ _
    | exact icmp_ne_uext_icmp_one _ _ _ _
    | exact icmp_ne_icmp_one _ _ _))

/-- `select c, -1, 0 = bmask c` (the `0` immediate given by its `toInt`). -/
macro "fin_sel_bmask_k" : tactic => `(tactic| (
  simp only [toInt_eq_zero_iff'] at *
  subst_vars
  simp only [Clif.Sem.select, Clif.Sem.bmask]
  rfl))

end Opt.Proof
