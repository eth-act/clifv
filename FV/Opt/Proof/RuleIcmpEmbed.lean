import FV.Opt.Proof.RuleBitopsEmbed

/-!
# Template variants for `opts/icmp.isle` and `opts/selects.isle`

- `arr_step`: the environment lookups of a pattern variable bound twice (a value variable
  compared with `V.beq` against a later slot), which `lhs_step` leaves stuck.
- `opt_split_typeof h`: a made `icmp` reads its operand type from the graph
  (`Option.map _ (G.typeOf s x)`); when that `match` sits inside a constructor call (`subsume`),
  `split` picks the outer match. Case on the `typeOf` read directly.
- `rule_auto_c` / `rule_auto_ci`: `rule_auto_b` / `rule_auto_i` with both.
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt Isle.Interp Clif
open Lean Meta Elab Tactic

@[opt_monad] theorem ctorFn_subsume_poison {σ : Type} (G : EGraph σ) (t : CTy) (s : St σ) :
    ctorFn G "subsume" [.poison t] s = .ok (some (.poison t, s)) := rfl

theorem tySmin_ofClif {t : Ty} (ht : t ≠ .i128) :
    Rust.tySmin (CTy.ofClif t) = .ok (2 ^ (t.width - 1)) := by
  cases t <;> first | rfl | exact absurd rfl ht

theorem tySmax_ofClif {t : Ty} (ht : t ≠ .i128) :
    Rust.tySmax (CTy.ofClif t) = .ok (2 ^ (t.width - 1) - 1) := by
  cases t <;> first | rfl | exact absurd rfl ht

/-- The lookups of a repeated pattern variable. -/
macro "arr_step" : tactic => `(tactic| simp (config := {decide := true}) only
  [Array.getElem?_setIfInBounds, Array.size_setIfInBounds, Array.size_replicate, Nat.reduceEqDiff,
   Nat.reduceLT, ite_true, ite_false, reduceIte, Option.some.injEq, Array.getElem?_replicate,
   V.beq_value, V.beq_ty, beq_iff_eq, V.value.injEq, V.ty.injEq] at *)

/-- `rule_lhs` with `arr_step` as a last resort. -/
macro "rule_lhs_c " hG:ident : tactic => `(tactic|
  repeat (any_goals (first | (opt_guard lhs_step; opt_destruct; all_goals subst_vars) | opt_model $hG |
    (lhs_step'; opt_destruct; all_goals subst_vars) | (arr_step; opt_destruct; all_goals subst_vars))))

/-- Case on the first `G.typeOf s x` read in `h` (not already known). -/
elab "opt_split_typeof " h:ident : tactic => withMainContext do
  let some ld := (← getLCtx).findFromUserName? h.getId | throwError "opt_split_typeof: no {h}"
  let ty ← instantiateMVars ld.type
  let found? := ty.find? fun e => e.isAppOfArity ``Isle.Opt.EGraph.typeOf 4 && !e.hasLooseBVars
  let some e := found? | throwError "opt_split_typeof: no typeOf"
  let es ← Term.exprToSyntax e
  evalTactic (← `(tactic| (rcases hT : $es with _ | xt <;>
    simp only [hT, Option.map_some, Option.map_none] at $h:ident)))

set_option hygiene false in
/-- `rule_rhs` with `opt_split_typeof` before `split`. -/
syntax "rule_rhs_c" ("[" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|> Lean.Parser.Tactic.simpLemma),* "]")? : tactic
set_option hygiene false in
macro_rules
  | `(tactic| rule_rhs_c [$ts,*]) => `(tactic| (
      opt_eval hev [$ts,*]
      repeat' ((first | opt_split_typeof hev | split at hev) <;> try opt_norm hev [$ts,*])
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

/-- `rule_bits_b` with the `Int` literals of the if-let conditions (`2 ^ w - 1` at a literal
width) reduced before `bv_decide`. -/
macro "rule_bits_c" : tactic => `(tactic| (
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
         | (opt_cases_val <;> opt_cases_ty <;> opt_widths <;> sem_simp_b <;>
            (try simp only [Int.reducePow, Int.reduceSub, Int.reduceToNat, Nat.reducePow,
              Nat.reduceSub] at *) <;> first | ac_rfl | bv_decide))))

set_option hygiene false in
macro "rule_finish_c" : tactic => `(tactic| first
  | (try dsimp only
     apply Valuation.le_trans hle1 hle3
     opt_rw_lhs
     rule_bits_c)
  | (try dsimp only
     apply GraphOk.make_val hG (by opt_P)
     opt_node
     all_goals rule_bits_c))

syntax "rule_auto_c " ident ("[" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|> Lean.Parser.Tactic.simpLemma),* "]")? : tactic
set_option hygiene false in
macro_rules
  | `(tactic| rule_auto_c $r:ident) => `(tactic| rule_auto_c $r [])
  | `(tactic| rule_auto_c $r:ident [$ts,*]) => `(tactic| (
      rule_intro $r
      rule_no_iflets
      rule_lhs_c hG
      all_goals (rule_rhs_c [$ts,*]; opt_some_subst; rule_finish_b)))

syntax "rule_auto_ci " ident ("[" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|> Lean.Parser.Tactic.simpLemma),* "]")? : tactic
set_option hygiene false in
macro_rules
  | `(tactic| rule_auto_ci $r:ident) => `(tactic| rule_auto_ci $r [])
  | `(tactic| rule_auto_ci $r:ident [$ts,*]) => `(tactic| (
      rule_intro $r
      rule_lhs_c hG
      all_goals rule_iflets
      all_goals (rule_rhs_c [$ts,*]; opt_some_subst; rule_finish_b)))

/-- `rule_iflets` with extra evaluation lemmas. -/
syntax "rule_iflets_c" ("[" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|> Lean.Parser.Tactic.simpLemma),* "]")? : tactic
set_option hygiene false in
macro_rules
  | `(tactic| rule_iflets_c [$ts,*]) => `(tactic| (
      opt_eval hil [$ts,*]
      repeat' ((first | split at hil | opt_split_ite hil) <;> try opt_eval hil [$ts,*])
      all_goals (try (simp at hil; done))
      all_goals (
        simp only [Except.ok.injEq, Prod.mk.injEq] at hil
        obtain ⟨rfl, rfl, rfl⟩ := hil
        simp only [List.mem_singleton, List.mem_cons, List.not_mem_nil, or_false] at henv2)
      all_goals subst henv2))

/-- `rule_auto_c` / `rule_auto_ci` with `rule_finish_c`. -/
syntax "rule_auto_d " ident ("[" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|> Lean.Parser.Tactic.simpLemma),* "]")? : tactic
set_option hygiene false in
macro_rules
  | `(tactic| rule_auto_d $r:ident) => `(tactic| rule_auto_d $r [])
  | `(tactic| rule_auto_d $r:ident [$ts,*]) => `(tactic| (
      rule_intro $r
      rule_no_iflets
      rule_lhs_c hG
      all_goals (rule_rhs_c [$ts,*]; opt_some_subst; rule_finish_c)))

syntax "rule_auto_di " ident ("[" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|> Lean.Parser.Tactic.simpLemma),* "]")? : tactic
set_option hygiene false in
macro_rules
  | `(tactic| rule_auto_di $r:ident) => `(tactic| rule_auto_di $r [])
  | `(tactic| rule_auto_di $r:ident [$ts,*]) => `(tactic| (
      rule_intro $r
      rule_lhs_c hG
      all_goals rule_iflets_c [$ts,*]
      all_goals (rule_rhs_c [$ts,*]; opt_some_subst; rule_finish_c)))

end Opt.Proof
