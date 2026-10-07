import FV.Opt.Proof.RuleRestEmbed

/-!
# 128-bit comparisons rebuilt from 64-bit halves (`icmp.isle` 254–289)

`select ty (eq hi_a hi_b) (cc_lo lo_a lo_b) (cc hi_a hi_b)` → `cc (iconcat lo_a hi_a) (iconcat lo_b hi_b)`.
The earlier proofs (`rule_auto_f`, `RuleIcmpEmbed2.lean`) ran out of memory (16G/24G per module):

- `toInst` of the made `iconcat` unfolds `binaryOfIdx? 155`, whose `match` on a literal does not
  reduce under `simp`; the stuck term was copied into every later state (4 min per rule).
  `binaryOfIdx?_iconcat` rewrites it first (`↓`).
- the left-hand side's model facts are guarded by `P s0` (`rule_lhs_f`); `rule_lhs_g` opens them, so
  every class value and type is known before the right-hand side (no `Clif.Ty` variables left to split).
- the made `iconcat`s are evaluated by `evalNode_iconcat_i64` (`opt_node_cat`), so `opt_types_cat` can
  fix the operand type of the made `icmp` (`i128`), and the result is closed by one of the
  `cat128_*` lemmas (`bv_decide` once, on 64-bit halves, outside the rule's context) instead of
  bit-blasting 128-bit comparisons per type combination.

`rule_auto_i128cmp r`: the template. Rule modules using it set `Elab.async false`: theorems are
otherwise elaborated in parallel (beyond `LEAN_NUM_THREADS`) and eight of them at ~5G each exceed the
memory cap.
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt Clif

/-- `iconcat.i64 lo, hi` evaluates to the 128-bit `hi ++ lo`. -/
theorem evalNode_iconcat_i64 {fr : Frame} {mem : Mem} {lo hi : ValueId} {a : Val} :
    evalNode fr mem (.iconcat .i64 lo hi) = some a ↔
      ∃ l h : BitVec 64, fr.regs lo = some ⟨.i64, l⟩ ∧ fr.regs hi = some ⟨.i64, h⟩ ∧
        a = ⟨.i128, h ++ l⟩ := by
  simp only [evalNode_eq_some, evalInst, Ty.double?, Res.ofOption, Res.ok_bind, getAs_bind_ok, pure,
    Res.ok.injEq, Prod.mk.injEq, List.cons.injEq, and_true, Sem.iconcat]
  constructor
  · rintro ⟨m, l, hl, h, hh, rfl, -⟩; exact ⟨l, h, hl, hh, rfl⟩
  · rintro ⟨l, h, hl, hh, rfl⟩; exact ⟨mem, l, hl, h, hh, rfl, rfl⟩

/-! The 128-bit comparison as LLVM decomposes it (`icmp.isle` 254–289): equal high halves pick
the unsigned comparison of the low halves, otherwise the comparison of the high halves. -/

macro "cat_bits" : tactic => `(tactic| (
  simp only [select_bif, Sem.truthy, icmp_eq, icmp_ne, icmp_slt, icmp_sge, icmp_sgt, icmp_sle,
    icmp_ult, icmp_uge, icmp_ugt, icmp_ule]
  bv_decide (config := { timeout := 120 })))

theorem cat128_uge (ah bh al bl : BitVec 64) :
    Sem.select (Sem.icmp .eq ah bh) (Sem.icmp .uge al bl) (Sem.icmp .uge ah bh) =
      Sem.icmp .uge (ah ++ al) (bh ++ bl) := by cat_bits
theorem cat128_sge (ah bh al bl : BitVec 64) :
    Sem.select (Sem.icmp .eq ah bh) (Sem.icmp .uge al bl) (Sem.icmp .sge ah bh) =
      Sem.icmp .sge (ah ++ al) (bh ++ bl) := by cat_bits
theorem cat128_ugt (ah bh al bl : BitVec 64) :
    Sem.select (Sem.icmp .eq ah bh) (Sem.icmp .ugt al bl) (Sem.icmp .ugt ah bh) =
      Sem.icmp .ugt (ah ++ al) (bh ++ bl) := by cat_bits
theorem cat128_sgt (ah bh al bl : BitVec 64) :
    Sem.select (Sem.icmp .eq ah bh) (Sem.icmp .ugt al bl) (Sem.icmp .sgt ah bh) =
      Sem.icmp .sgt (ah ++ al) (bh ++ bl) := by cat_bits
theorem cat128_ule (ah bh al bl : BitVec 64) :
    Sem.select (Sem.icmp .eq ah bh) (Sem.icmp .ule al bl) (Sem.icmp .ule ah bh) =
      Sem.icmp .ule (ah ++ al) (bh ++ bl) := by cat_bits
theorem cat128_sle (ah bh al bl : BitVec 64) :
    Sem.select (Sem.icmp .eq ah bh) (Sem.icmp .ule al bl) (Sem.icmp .sle ah bh) =
      Sem.icmp .sle (ah ++ al) (bh ++ bl) := by cat_bits
theorem cat128_ult (ah bh al bl : BitVec 64) :
    Sem.select (Sem.icmp .eq ah bh) (Sem.icmp .ult al bl) (Sem.icmp .ult ah bh) =
      Sem.icmp .ult (ah ++ al) (bh ++ bl) := by cat_bits
theorem cat128_slt (ah bh al bl : BitVec 64) :
    Sem.select (Sem.icmp .eq ah bh) (Sem.icmp .ult al bl) (Sem.icmp .slt ah bh) =
      Sem.icmp .slt (ah ++ al) (bh ++ bl) := by cat_bits

/-- `toInst` of a made `iconcat`: the opcode is not a `Clif.BinaryOp` (rewritten before
`binaryOfIdx?` is unfolded: its `match` on the literal `155` does not reduce under `simp`, and the
stuck term is copied into every later state). -/
theorem binaryOfIdx?_iconcat : binaryOfIdx? 155 = none := rfl

/-- A `⟨.i8, select …⟩ = ⟨.i8, icmp cc (ah ++ al) (bh ++ bl)⟩` goal by `cat128_*`. -/
macro "cat_close" : tactic => `(tactic| (apply val_congr; first
  | exact cat128_uge _ _ _ _ | exact cat128_sge _ _ _ _
  | exact cat128_ugt _ _ _ _ | exact cat128_sgt _ _ _ _
  | exact cat128_ule _ _ _ _ | exact cat128_sle _ _ _ _
  | exact cat128_ult _ _ _ _ | exact cat128_slt _ _ _ _))

syntax "opt_den_cat" : tactic
syntax "opt_node_cat" : tactic

set_option hygiene false in
macro_rules
  | `(tactic| opt_den_cat) => `(tactic| first
      | (apply Valuation.le_trans hle1 hle3; assumption)
      | (apply GraphOk.make_val hG (by opt_P); opt_node_cat)
      | (apply GraphOk.make_le hG (by opt_P); opt_den_cat))

set_option hygiene false in
macro_rules
  | `(tactic| opt_node_cat) => `(tactic| (
      simp only [evalNode_icmp, evalNode_iconcat_i64, Clif.Frame.regs]
      repeat (first | (apply Exists.intro) | (apply And.intro) | opt_den_cat)
      all_goals (try (first | cat_close | rfl))))

open Lean Meta Elab Tactic in
set_option hygiene false in
/-- `opt_types` with `opt_den_cat` (made `iconcat` operands): substitute the type variable of
every `G.typeOf st x = some xt` read, oldest first, looking the hypotheses up again after every
`subst` (which renames the later ones). -/
elab "opt_types_cat" : tactic => do
  let mut failed : Array Name := #[]
  for _ in [0:16] do
    let g ← getMainGoal
    let cands ← g.withContext do
      let mut out := #[]
      for d in ← getLCtx do
        if d.isImplementationDetail then continue
        let t ← instantiateMVars d.type
        if let some (_, l, r) := t.eq? then
          if l.isAppOfArity `Isle.Opt.EGraph.typeOf 4 && r.isAppOfArity ``Option.some 2 &&
              r.appArg!.isFVar && !failed.contains d.userName then
            out := out.push d.userName
      pure out
    let mut progress := false
    for n in cands do
      let s ← saveState
      try
        let hs := mkIdent n
        evalTactic (← `(tactic| (
          have hty := GraphOk.typeOf_eq hG (by opt_P) $hs:ident (by opt_den_cat)
          try simp only at hty
          subst hty)))
        progress := true
        break
      catch _ =>
        s.restore
        failed := failed.push n
    unless progress do return

set_option hygiene false in
/-- `rule_rhs_c` with `binaryOfIdx?_iconcat` and `opt_types_cat`. -/
macro "rule_rhs_cat" : tactic => `(tactic| (
  opt_eval hev [↓binaryOfIdx?_iconcat]
  repeat' ((first | opt_split_typeof hev | split at hev) <;> try opt_norm hev [↓binaryOfIdx?_iconcat])
  all_goals (try simp only [Option.map_eq_some_iff, Option.map_eq_none_iff] at *)
  opt_destruct
  all_goals subst_vars
  all_goals (
    simp only [Except.ok.injEq, Prod.mk.injEq] at hev
    obtain ⟨rfl, rfl, rfl⟩ := hev
    simp only [List.mem_singleton, List.mem_cons, List.not_mem_nil, or_false, V.value.injEq,
      reduceCtorEq] at hm <;>
    subst hm)
  all_goals opt_types_cat))

set_option hygiene false in
/-- The candidate: the made `icmp` of the two made `iconcat`s evaluates to the decomposed
comparison (`cat128_*`, no bit-blasting of 128-bit comparisons in the rule's context). -/
macro "rule_finish_cat" : tactic => `(tactic| (
  try dsimp only
  apply GraphOk.make_val hG (by opt_P)
  opt_node_cat))

end Opt.Proof

namespace Opt.Proof

/-- The template (see the module docstring). -/
syntax "rule_auto_i128cmp " ident : tactic
set_option hygiene false in
macro_rules
  | `(tactic| rule_auto_i128cmp $r:ident) => `(tactic| (
      rule_intro $r
      rule_no_iflets
      rule_lhs_g hG
      all_goals rule_rhs_cat
      all_goals rule_finish_cat))

end Opt.Proof
