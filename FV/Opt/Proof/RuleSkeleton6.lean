import FV.Opt.Proof.RuleSkelEmbed

/-!
# Branch conditions made from leading/trailing zero counts

The four `icmp.isle` skeleton rules replace a count's truthiness by a test of
its input.  The optional `ireduce` preserves this truthiness: every supported
integer type has at least eight bits, and a count is at most 128.

During interpreter evaluation, name each made graph node before evaluating
the next constructor.  In particular the i128 constant constructors make an
i64 constant followed by `uextend`; repeatedly substituting the resulting
state into both projections of the next `make` otherwise duplicates the
entire evaluation prefix.  Local definitions retain the ordinary `opt_den`
proof and do not add any assumptions about the graph.
-/

namespace Opt.Proof

open Isle Isle.Opt Isle.Interp Clif

/-- A leading-zero count vanishes exactly when the high bit is set. -/
theorem skel_count_clz_zero {w : Nat} (hw : 0 < w) (x : BitVec w) :
    x.clz = 0#w ↔ x.msb = true := by
  rw [← toNat_eq_zero_iff, BitVec.clz_eq_zero_iff hw]
  simp only [BitVec.msb_eq_decide, decide_eq_true_eq]

/-- A count cannot wrap when the destination can represent the source width. -/
theorem skel_count_clz_reduce_zero {w v : Nat} (hv : w < 2 ^ v) (x : BitVec w) :
    x.clz.setWidth v = 0#v ↔ x.clz = 0#w := by
  have hle : x.clz.toNat ≤ w := by
    have h := BitVec.le_def.mp (BitVec.clz_le (x := x))
    simpa only [BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt Nat.lt_two_pow_self] using h
  simp only [BitVec.toNat_eq, BitVec.toNat_setWidth, BitVec.toNat_zero,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hle hv)]

-- Both hypotheses hold at the widest source and narrowest destination.
example : 0 < 128 ∧ 128 < 2 ^ 8 := by decide
example : (BitVec.intMin 128).clz = 0#128 ↔ (BitVec.intMin 128).msb = true :=
  skel_count_clz_zero (by decide) _
example : (0#128).clz.setWidth 8 = 0#8 ↔ (0#128).clz = 0#128 :=
  skel_count_clz_reduce_zero (by decide) _

/-- Masking bit zero tests exactly the low bit, at every positive width. -/
theorem skel_count_low_zero {w : Nat} (hw : 0 < w) (x : BitVec w) :
    x &&& 1#w = 0#w ↔ x.getLsbD 0 = false := by
  rw [BitVec.and_one_eq_setWidth_ofBool_getLsbD]
  cases x.getLsbD 0 <;>
    simp [BitVec.ofBool,
      BitVec.setWidth_ofNat_one_eq_ofNat_one_of_lt (v := 1) (w := w) (by decide),
      Nat.ne_of_gt hw]

theorem skel_count_ctz_zero {w : Nat} (hw : 0 < w) (x : BitVec w) :
    x.ctz = 0#w ↔ x.getLsbD 0 = true := by
  rw [BitVec.ctz_eq_reverse_clz, skel_count_clz_zero hw, BitVec.msb_reverse]

/-- The replacement condition and the original count choose the same branch. -/
theorem skel_count_ctz_truthy {w : Nat} (hw : 0 < w) (x : BitVec w) :
    Sem.truthy (Sem.icmp .eq (x &&& 1#w) 0#w) = Sem.truthy x.ctz := by
  apply Bool.eq_iff_iff.mpr
  cases h : x.getLsbD 0 <;>
    simp [Sem.truthy, Sem.icmp, Sem.intcc, Sem.bool8, bne_iff_ne,
      skel_count_low_zero hw x, skel_count_ctz_zero hw x, h]

theorem skel_count_clz_truthy {w : Nat} (hw : 0 < w) (x : BitVec w) :
    Sem.truthy (Sem.icmp .sge x 0#w) = Sem.truthy x.clz := by
  apply Bool.eq_iff_iff.mpr
  cases h : x.msb <;>
    simp [Sem.truthy, Sem.icmp, Sem.intcc, Sem.bool8, bne_iff_ne,
      BitVec.zero_sle_eq_not_msb, skel_count_clz_zero hw x, h]

theorem skel_count_ctz_reduce_truthy {w v : Nat} (hw : 0 < w) (hv : w < 2 ^ v)
    (x : BitVec w) :
    Sem.truthy (Sem.icmp .eq (x &&& 1#w) 0#w) = Sem.truthy (x.ctz.setWidth v) := by
  rw [skel_count_ctz_truthy hw]
  apply Bool.eq_iff_iff.mpr
  simp only [Sem.truthy, bne_iff_ne, BitVec.ctz_eq_reverse_clz]
  exact not_congr (skel_count_clz_reduce_zero hv x.reverse).symm

theorem skel_count_clz_reduce_truthy {w v : Nat} (hw : 0 < w) (hv : w < 2 ^ v)
    (x : BitVec w) :
    Sem.truthy (Sem.icmp .sge x 0#w) = Sem.truthy (x.clz.setWidth v) := by
  rw [skel_count_clz_truthy hw]
  apply Bool.eq_iff_iff.mpr
  simp only [Sem.truthy, bne_iff_ne]
  exact not_congr (skel_count_clz_reduce_zero hv x).symm

example : (2#128 &&& 1#128 = 0#128) ↔ (2#128).getLsbD 0 = false :=
  skel_count_low_zero (by decide) _
example : (1#128).ctz = 0#128 ↔ (1#128).getLsbD 0 = true :=
  skel_count_ctz_zero (by decide) _
example : Sem.truthy (Sem.icmp .eq (2#128 &&& 1#128) 0#128) =
    Sem.truthy (2#128).ctz :=
  skel_count_ctz_truthy (by decide) _
example : Sem.truthy (Sem.icmp .sge (BitVec.intMin 128) 0#128) =
    Sem.truthy (BitVec.intMin 128).clz :=
  skel_count_clz_truthy (by decide) _
example : Sem.truthy (Sem.icmp .eq (0#128 &&& 1#128) 0#128) =
    Sem.truthy ((0#128).ctz.setWidth 8) :=
  skel_count_ctz_reduce_truthy (by decide) (by decide) _
example : Sem.truthy (Sem.icmp .sge 0#128 0#128) =
    Sem.truthy ((0#128).clz.setWidth 8) :=
  skel_count_clz_reduce_truthy (by decide) (by decide) _

open Lean Meta Elab Tactic in
/-- Share one graph-constructor result by a definition, not a new premise. -/
elab "skel_count_share_one " h:ident : tactic => withMainContext do
  let hyp ← getFVarId h
  let ty ← instantiateMVars (← hyp.getType)
  let some e := ty.find? (fun e =>
      !e.hasLooseBVars &&
        (e.isAppOfArity ``Isle.Opt.EGraph.make 4 ||
          match e.getAppFn with
          | .proj ``Isle.Opt.EGraph 2 _ => e.getAppNumArgs == 2
          | _ => false))
    | throwError "no graph constructor to share"
  let name ← mkFreshUserName `made
  let g ← (← getMainGoal).define name (← inferType e) e
  let (made, g) ← g.intro1P
  let ty' := ty.replace fun x => if x == e then some (mkFVar made) else none
  replaceMainGoal [← g.changeLocalDecl hyp ty']

macro "skel_count_share " h:ident : tactic =>
  `(tactic| repeat skel_count_share_one $h)

macro "skel_count_norm " h:ident : tactic => `(tactic| (
  opt_norm $h
  skel_count_share $h))

macro "skel_count_eval " h:ident : tactic => `(tactic| (
  skel_count_norm $h
  repeat (opt_unfold $h; skel_count_norm $h)))

open Lean Meta Elab Tactic in
set_option hygiene false in
/-- Reconcile a made operand's type, including extension width obligations. -/
elab "skel_count_type_one" : tactic => withMainContext do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    if let some (_, l, r) := t.eq? then
      if l.isAppOfArity ``Isle.Opt.EGraph.typeOf 4 &&
          r.isAppOfArity ``Option.some 2 && r.appArg!.isFVar then
        let saved ← saveState
        try
          let hs ← Term.exprToSyntax (mkFVar d.fvarId)
          evalTactic (← `(tactic| (
            have hty := GraphOk.typeOf_eq hG (by opt_P) $hs (by opt_den_x)
            try dsimp only at hty
            subst hty)))
          return
        catch _ => saved.restore
  throwError "no made operand type to reconcile"

set_option hygiene false in
/-- Instantiate the count identities directly, without reflecting graph-local expressions. -/
macro "skel_count_finish" : tactic => `(tactic| (
  apply skel_brif_cond (hle4 _ _ (by opt_den_x)) (hle4 _ _ (by opt_den_x))
  opt_cases_ty
  all_goals (
    dsimp only [Ty.width] at *
    first
      | (apply skel_count_ctz_truthy <;> decide)
      | (apply skel_count_clz_truthy <;> decide)
      | (apply skel_count_ctz_reduce_truthy <;> decide)
      | (apply skel_count_clz_reduce_truthy <;> decide))))

set_option hygiene false in
/-- The ordinary skeleton RHS phase, sharing each made node between steps. -/
macro "skel_count_rhs" : tactic => `(tactic| (
  skel_count_eval hev
  repeat' (split at hev <;> try skel_count_norm hev)
  all_goals (try simp only [Option.map_eq_some_iff, Option.map_eq_none_iff] at *)
  opt_destruct
  all_goals subst_vars
  all_goals (
    simp only [Except.ok.injEq, Prod.mk.injEq] at hev
    obtain ⟨rfl, rfl, rfl⟩ := hev
    simp only [List.mem_singleton, List.mem_cons, List.not_mem_nil, or_false] at hw <;>
    subst hw)
  all_goals (repeat skel_count_type_one)
  all_goals (try (exfalso; omega))))

set_option hygiene false in
/-- Discard unsuccessful constructor results before extracting the simplification. -/
macro "skel_count_good" : tactic => `(tactic| (
  intro c hc st hst hle4
  simp (config := {decide := true}) only [skelSimp?, toSkel, ite_false,
    Option.some.injEq, reduceCtorEq] at hc
  all_goals subst hc))

set_option hygiene false in
macro "skel_count_rule " r:ident : tactic => `(tactic| (
  skel_intro $r
  rule_lhs hG
  skel_reads
  rule_lhs hG
  all_goals rule_no_iflets
  all_goals opt_split_i128
  all_goals skel_count_rhs
  all_goals skel_count_good
  all_goals skel_count_finish))

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4096 in
theorem ok_rule_icmp_461 {p : Isle.Program} (hd : Data p) : SkelRuleOk p rule_icmp_461 := by
  skel_count_rule rule_icmp_461

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4096 in
theorem ok_rule_icmp_466 {p : Isle.Program} (hd : Data p) : SkelRuleOk p rule_icmp_466 := by
  skel_count_rule rule_icmp_466

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4096 in
theorem ok_rule_icmp_471 {p : Isle.Program} (hd : Data p) : SkelRuleOk p rule_icmp_471 := by
  skel_count_rule rule_icmp_471

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4096 in
theorem ok_rule_icmp_475 {p : Isle.Program} (hd : Data p) : SkelRuleOk p rule_icmp_475 := by
  skel_count_rule rule_icmp_475

/-! Concrete nonzero and zero branch conditions, including the maximal count
128 after reduction to i8.  The integration smoke additionally exercises the
actual rule matches and rewritten branch targets. -/
set_option maxRecDepth 4096
example : (2#128).ctz ≠ 0 ∧ (2#128 &&& 1#128) = 0 := by decide
example : (1#128).ctz = 0 ∧ (1#128 &&& 1#128) ≠ 0 := by decide
example : (0#128).ctz.setWidth 8 = 128#8 ∧ (0#128 &&& 1#128) = 0 := by decide
example : (1#128).clz ≠ 0 ∧ (1#128).slt 0 = false := by decide
example : (BitVec.intMin 128).clz = 0 ∧ (BitVec.intMin 128).slt 0 = true := by decide
example : (0#128).clz.setWidth 8 = 128#8 ∧ (0#128).slt 0 = false := by decide

end Opt.Proof
