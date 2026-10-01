import FV.Opt.Proof.RuleExtEmbed

/-! # Templates for the remaining `simplify` roots (RulesRest)

`rule_auto_w`: `rule_auto_y` whose right-hand side also rewrites later `value_type` reads of a
class whose type an earlier read established (`opt_rw_typeof`; the rotate regrouping rules of
`shifts.isle` go through `iadd_uextend`/`isub_uextend`, whose rules read the type again). -/

namespace Opt.Proof

open Isle Isle.Opt Clif

open Lean Meta Elab Tactic in
/-- `opt_rw_typeof h`: rewrite `h` with every known `G.typeOf st x = some t` fact. -/
elab "opt_rw_typeof " h:ident : tactic => withMainContext do
  let mut ts : Array Lean.Term := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    if let some (_, l, r) := t.eq? then
      if l.isAppOfArity `Isle.Opt.EGraph.typeOf 4 && r.isAppOfArity ``Option.some 2 then
        ts := ts.push (← Term.exprToSyntax (mkFVar d.fvarId))
  if ts.isEmpty then throwError "opt_rw_typeof: no typeOf facts"
  let lemmas : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ←
    ts.mapM fun t => `(Lean.Parser.Tactic.simpLemma| $t:term)
  evalTactic (← `(tactic| simp only [$lemmas,*] at $h:ident))

open Lean Meta Elab Tactic in
/-- `opt_heq_typeof`: a `split` on an extractor call leaves `heq : toExt (… typeOf …) =
ExtResult.ok fs`; rewrite each such hypothesis with the known `typeOf` facts, evaluate it and
substitute `fs`. -/
elab "opt_heq_typeof" : tactic => withMainContext do
  let mut facts : Array Lean.Term := #[]
  let mut targets : Array FVarId := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    if let some (_, l, r) := t.eq? then
      if l.isAppOfArity `Isle.Opt.EGraph.typeOf 4 && r.isAppOfArity ``Option.some 2 then
        facts := facts.push (← Term.exprToSyntax (mkFVar d.fvarId))
      else if r.isAppOf `Isle.ExtResult.ok && (l.find? (·.isAppOf `Isle.Opt.EGraph.typeOf)).isSome then
        targets := targets.push d.fvarId
  if facts.isEmpty || targets.isEmpty then throwError "opt_heq_typeof: nothing to do"
  let lemmas : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ←
    facts.mapM fun t => `(Lean.Parser.Tactic.simpLemma| $t:term)
  for h in targets do
    let hn ← mkFreshUserName `hx
    let g ← (← getMainGoal).rename h hn
    replaceMainGoal [g]
    let hi := mkIdent hn
    try
      evalTactic (← `(tactic| (
        simp only [$lemmas,*] at $hi:ident
        opt_norm $hi:ident
        try simp only [ExtResult.ok.injEq] at $hi:ident
        try subst $hi:ident)))
    catch _ => pure ()

open Lean Meta Elab Tactic in
/-- `opt_beq_subst`: turn each `(a == b) = true` fact on types (a variable bound twice in a
constructor's rule, `iadd_uextend x@(value_type ty) y@(value_type ty)`) into `a = b` and
substitute it. -/
elab "opt_beq_subst" : tactic => withMainContext do
  let mut hs : Array FVarId := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    if let some (_, l, r) := t.eq? then
      if l.isAppOfArity ``BEq.beq 4 && r.isConstOf ``Bool.true &&
          (l.getArg! 0).isConstOf ``Clif.Ty then
        hs := hs.push d.fvarId
  if hs.isEmpty then throwError "opt_beq_subst: no type equality facts"
  for h in hs do
    let hn ← mkFreshUserName `hb
    let g ← (← getMainGoal).rename h hn
    replaceMainGoal [g]
    let hi := mkIdent hn
    evalTactic (← `(tactic| (
      simp only [beq_iff_eq] at $hi:ident
      try subst $hi:ident)))

open Lean Meta Elab Tactic in
/-- `opt_ty_facts`: the width comparisons of a constructor's if-lets (`u64_lt (ty_bits_u64 x)
(ty_bits_u64 y)`, kept as `(decide (↑(ofClif a).bits < ↑(ofClif b).bits) == true) = true`) as
`a.width < b.width`, for the width side conditions of made extends. -/
elab "opt_ty_facts" : tactic => withMainContext do
  let mut hs : Array FVarId := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    if t.isAppOfArity ``Eq 3 && (t.find? (·.isConstOf ``CTy.bits)).isSome &&
        !(t.find? (·.isConstOf ``Isle.Interp.evalExprN)).isSome then
      hs := hs.push d.fvarId
  if hs.isEmpty then throwError "opt_ty_facts: none"
  for h in hs do
    let hn ← mkFreshUserName `hw
    let g ← (← getMainGoal).rename h hn
    replaceMainGoal [g]
    let hi := mkIdent hn
    try
      evalTactic (← `(tactic| simp only [beq_true, beq_false, decide_eq_true_eq, decide_eq_false_iff_not,
        Bool.not_eq_true, ofClif_bits, Int.ofNat_lt, Int.ofNat_le, Nat.not_lt] at $hi:ident))
    catch _ => pure ()

open Lean Meta Elab Tactic in
/-- `opt_heq_ite`: a `split` on an internal constructor's rule match leaves `heq : (if c then
some e else none) = some e'`; keep the condition `c` as a fact. -/
elab "opt_heq_ite" : tactic => withMainContext do
  let mut hs : Array FVarId := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    if let some (_, l, r) := t.eq? then
      if l.isAppOfArity ``ite 5 && r.isAppOfArity ``Option.some 2 then
        hs := hs.push d.fvarId
  if hs.isEmpty then throwError "opt_heq_ite: none"
  for h in hs do
    let hn ← mkFreshUserName `hi
    let g ← (← getMainGoal).rename h hn
    replaceMainGoal [g]
    let hi := mkIdent hn
    try
      evalTactic (← `(tactic| (
        simp only [Option.ite_none_right_eq_some] at $hi:ident
        obtain ⟨_, _⟩ := $hi:ident)))
    catch _ => pure ()

theorem except_throw_eq_ok {ε α : Type} (e : ε) (a : α) :
    ((throw e : Except ε α) = .ok a) = False := by
  simp only [throw, throwThe, MonadExceptOf.throw, reduceCtorEq]

set_option hygiene false in
/-- `rule_rhs_y` plus `opt_rw_typeof` before unfolding a stuck read; a read the graph has no
type for (`none`) throws, which `except_throw_eq_ok` closes. -/
syntax "rule_rhs_w" ("[" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|> Lean.Parser.Tactic.simpLemma),* "]")? : tactic
set_option hygiene false in
macro_rules
  | `(tactic| rule_rhs_w) => `(tactic| rule_rhs_w [])
  | `(tactic| rule_rhs_w [$ts,*]) => `(tactic| (
      opt_norm hev [$ts,*]
      repeat' (first
        | (opt_rw_typeof hev; try opt_norm hev [except_throw_bind', except_error_bind', $ts,*])
        | (opt_split_typeof hev <;> (try opt_types_x) <;>
            try opt_norm hev [except_throw_bind', except_error_bind', $ts,*])
        | (opt_unfold hev; opt_norm hev [except_throw_bind', except_error_bind', $ts,*]))
      repeat' (split at hev <;>
        (try (rename_i hq; opt_split_ite hq <;>
           (try simp only [Option.some.injEq, reduceCtorEq, Bool.false_eq_true, ite_false,
             ↓reduceIte] at hq) <;> (try subst hq))) <;>
        (try opt_heq_typeof) <;> (try opt_rw_typeof hev) <;>
        try opt_eval hev [except_throw_bind', except_error_bind', $ts,*])
      all_goals (try (simp only [reduceCtorEq, except_throw_eq_ok] at hev; done))
      all_goals (try simp only [Option.map_eq_some_iff, Option.map_eq_none_iff] at *)
      opt_destruct
      all_goals subst_vars
      all_goals (try opt_beq_subst)
      all_goals (try opt_ty_facts)
      all_goals (
        simp only [Except.ok.injEq, Prod.mk.injEq] at hev
        obtain ⟨rfl, rfl, rfl⟩ := hev
        simp only [List.mem_singleton, List.mem_cons, List.not_mem_nil, or_false, V.value.injEq,
          reduceCtorEq] at hm <;>
        subst hm)
      all_goals (try opt_types_x)))

theorem bif_none_right_eq_some {α : Type} (c : Bool) (a b : α) :
    ((bif c then some a else none) = some b) ↔ (c = true ∧ a = b) := by
  cases c <;> simp

theorem natCast_toNat_bne_zero {w : Nat} (x : BitVec w) :
    (((x.toNat : Int) != 0) = true) ↔ x ≠ 0#w := by
  simp only [bne_iff_ne, ne_eq, Int.natCast_eq_zero, BitVec.toNat_eq, BitVec.toNat_ofNat, Nat.zero_mod]

theorem imm64Masked_i128 (x : Int) :
    Rust.imm64Masked (CTy.ofClif .i128) x = throw "ty_mask: unimplemented for > 64 bits" := rfl

/-- `i64_sextend_u64` below 128 bits (`iconst_s`'s re-extension check). -/
@[opt_imm] theorem i64SextendU64_spec {t : Ty} (ht : t ≠ .i128) (x : Int) :
    Rust.i64SextendU64 (CTy.ofClif t) x = .ok (Rust.sext t.width (Rust.asI64 x)) := by
  cases t <;> first | exact absurd rfl ht | rfl

/-- `rule_bits_xb` that also decides closed side facts once the types are split (`Ty.i16 ==
Ty.i8`, `decide (8 < 16)` from the rules of `iadd_uextend`/`isub_uextend`). -/
macro "rule_bits_w" : tactic => `(tactic| (
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
         | (simp only [Clif.Sem.unary, bswap_bswap, popcnt_bswap, bitrev_bitrev, popcnt_bitrev]; done)
         | (opt_cases_val <;> opt_cases_ty <;>
            (try simp only [bif_none_right_eq_some, Option.ite_none_right_eq_some, beq_true,
              natCast_toNat_bne_zero] at *) <;>
            (try simp (disch := decide) only [Rust.sext, ge_iff_le, Nat.reduceLeDiff, reduceIte,
              Bool.false_eq_true] at *) <;>
            (try (simp (config := { decide := true }) only [beq_true, decide_eq_true_eq,
              ofClif_bits, Ty.width, Int.ofNat_lt, Int.ofNat_le, Nat.reduceLT, Nat.reduceLeDiff,
              Bool.not_eq_true, Bool.false_eq_true] at *; done)) <;>
            opt_widths <;> sem_simp_b <;> (try int_bv) <;>
            (try simp only [bif_none_right_eq_some, Option.ite_none_right_eq_some] at *) <;>
            (try opt_destruct) <;>
            (try apply val_congr) <;>
            first | ac_rfl | bv_decide))))

set_option hygiene false in
macro "rule_finish_w" : tactic => `(tactic| first
  | (try dsimp only
     apply Valuation.le_trans hle1 hle3
     opt_rw_lhs
     rule_bits_w)
  | (try dsimp only
     apply GraphOk.make_val hG (by opt_P)
     opt_node_x
     all_goals (try (show _ < _; first | assumption | omega))
     all_goals rule_bits_w))

/-- `rule_auto_y` with `rule_rhs_w`. -/
syntax "rule_auto_w " ident ("[" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|> Lean.Parser.Tactic.simpLemma),* "]")? : tactic
set_option hygiene false in
macro_rules
  | `(tactic| rule_auto_w $r:ident) => `(tactic| rule_auto_w $r [])
  | `(tactic| rule_auto_w $r:ident [$ts,*]) => `(tactic| (
      rule_intro $r
      rule_lhs hG
      all_goals (first | rule_no_iflets | rule_iflets)
      all_goals (rule_rhs_w [$ts,*]; all_goals (opt_some_subst; (try opt_val_ty_subst); rule_finish_w))))

end Opt.Proof

/-! ## Helper specifications: `imm64_sshr`, `imm64_rotl`, `imm64_rotr` (cprop folds) -/

namespace Opt.Proof

open Isle Isle.Opt Clif

set_option linter.unusedSimpArgs false

@[opt_imm] theorem imm64Sshr_spec {t t' : Ty} (ht : t ≠ .i128) (ht' : t' ≠ .i128) (b : BitVec t.width)
    (c : BitVec t'.width) :
    Rust.imm64Sshr (CTy.ofClif t) (imm64OfBits b) (imm64OfBits c) = .ok (imm64OfBits (Sem.sshr b c)) := by
  imm_pre [Rust.imm64Sshr]
  rw [show 64 - (64 - (CTy.ofClif t).bits) = t.width by cases t <;> simp_all [ofClif_bits, Ty.width],
    ofInt_imm64OfBits ht]
  simp only [Rust.band64, int_toNat_natCast, toInt_div_two_pow, sshiftRight_toNat']
  imm_cases t b <;> imm_cases t' c <;> simp (disch := decide) only [sshr_mask, Nat.reduceBEq,
    Bool.false_eq_true, reduceIte, Int.reduceSub, Int.reducePow, Nat.reduceSub, Int.reduceNatCast,
    ge_iff_le, Nat.reduceLeDiff, toInt_div_two_pow, sshiftRight_toNat', int_toNat_natCast] <;>
    imm_solve

theorem toNat_beq_zero {w : Nat} (x : BitVec w) : (x.toNat == 0) = (x == 0#w) := by
  rw [Bool.eq_iff_iff]; simp only [beq_iff_eq, BitVec.toNat_eq, BitVec.toNat_ofNat, Nat.zero_mod]

theorem ushr_sub_and {w k : Nat} (m : BitVec 64) (hm : m.toNat < k) (hk : k < 2 ^ 64)
    (x : BitVec w) (v : BitVec 64) :
    x >>> (k - (v &&& m).toNat) = x >>> (BitVec.ofNat 64 k - (v &&& m)) := by
  have h : (v &&& m).toNat ≤ m.toNat := by rw [BitVec.toNat_and]; exact Nat.and_le_right
  rw [← ushiftRight_toNat' x (BitVec.ofNat 64 k - _), BitVec.toNat_sub_of_le]
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]
  · rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]; omega

theorem shl_sub_and {w k : Nat} (m : BitVec 64) (hm : m.toNat < k) (hk : k < 2 ^ 64)
    (x : BitVec w) (v : BitVec 64) :
    x <<< (k - (v &&& m).toNat) = x <<< (BitVec.ofNat 64 k - (v &&& m)) := by
  have h : (v &&& m).toNat ≤ m.toNat := by rw [BitVec.toNat_and]; exact Nat.and_le_right
  rw [← shiftLeft_toNat' x (BitVec.ofNat 64 k - _), BitVec.toNat_sub_of_le]
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]
  · rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]; omega

@[opt_imm] theorem imm64Rotl_spec {t t' : Ty} (ht : t ≠ .i128) (ht' : t' ≠ .i128) (b : BitVec t.width)
    (c : BitVec t'.width) :
    Rust.imm64Rotl (CTy.ofClif t) (imm64OfBits b) (imm64OfBits c) = .ok (imm64OfBits (Sem.rotl b c)) := by
  imm_pre [Rust.imm64Rotl]
  simp only [Rust.band64, Rust.bor64, Rust.asU64, int_toNat_natCast, ofInt_mul_two_pow,
    shiftLeft_toNat', natCast_div_two_pow, ushiftRight_toNat']
  imm_cases t b <;> imm_cases t' c <;> simp (disch := decide) only [rotl_mask, Nat.reduceBEq,
    Bool.false_eq_true, reduceIte, Int.reduceSub, Int.reducePow, Nat.reduceSub, Int.reduceNatCast,
    BitVec.ofInt_ofNat, ushr_sub_and, shl_sub_and, toNat_beq_zero] <;> imm_solve

@[opt_imm] theorem imm64Rotr_spec {t t' : Ty} (ht : t ≠ .i128) (ht' : t' ≠ .i128) (b : BitVec t.width)
    (c : BitVec t'.width) :
    Rust.imm64Rotr (CTy.ofClif t) (imm64OfBits b) (imm64OfBits c) = .ok (imm64OfBits (Sem.rotr b c)) := by
  imm_pre [Rust.imm64Rotr]
  simp only [Rust.band64, Rust.bor64, Rust.asU64, int_toNat_natCast, ofInt_mul_two_pow,
    shiftLeft_toNat', natCast_div_two_pow, ushiftRight_toNat']
  imm_cases t b <;> imm_cases t' c <;> simp (disch := decide) only [rotr_mask, Nat.reduceBEq,
    Bool.false_eq_true, reduceIte, Int.reduceSub, Int.reducePow, Nat.reduceSub, Int.reduceNatCast,
    BitVec.ofInt_ofNat, ushr_sub_and, shl_sub_and, toNat_beq_zero] <;> imm_solve

end Opt.Proof

namespace Opt.Proof

open Isle Isle.Opt Clif

/-- `rule_auto_xz` whose if-lets also unfold `matchAllN`/`bindAll` (an `and` pattern such as
`u64_extract_non_zero` in an if-let), keeping the conditions of internal constructors' rule
matches (`shift_amt_to_type`) as facts, with `rule_finish_w`. -/
syntax "rule_auto_v " ident ("[" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|> Lean.Parser.Tactic.simpLemma),* "]")? : tactic
set_option hygiene false in
macro_rules
  | `(tactic| rule_auto_v $r:ident) =>
    `(tactic| rule_auto_v $r [tyMask_ofClif, tyMask_ofClif_i128, Rust.tyUmax, panics_throw_bind,
      except_throw_bind, toExt_throw, Isle.Interp.bindAll, Isle.Interp.matchAllN.eq_1,
      Isle.Interp.matchAllN.eq_2, Isle.Interp.matchArgsN.eq_1, imm64Masked_i128])
  | `(tactic| rule_auto_v $r:ident [$ts,*]) => `(tactic| (
      rule_intro $r
      rule_lhs hG
      all_goals (try opt_val_ty_subst)
      opt_cases_val
      all_goals opt_split_i128
      all_goals (first | rule_no_iflets | rule_iflets_c [$ts,*])
      all_goals (rule_rhs_x [$ts,*]; all_goals (opt_some_subst; (try opt_heq_ite); rule_finish_w))))

end Opt.Proof
