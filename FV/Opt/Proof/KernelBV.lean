import Lean
import Std.Tactic.BVDecide
import FV.Clif.Sem

/-!
# Kernel-checked bit-vector decision (`kbv`)

`kbv` closes the concrete-width bit-vector goals of the optimizer rule proofs by kernel-checked
proof search: no SAT certificates and no `Lean.ofReduceBool`, so its proofs use only `propext`,
`Classical.choice` and `Quot.sound`. It restates the goal over its bit-vector context
(`isolate`) and tries, in order:

1. `bv_normalize` (a `simp` set) closing the goal;
2. `kbv_bits`: bit extensionality, then a Boolean tautology over the bits (`bool_tauto`:
   generalize the `Bool` atoms, `decide`);
3. `kbv_bitsh`: case split on the `if`/`bif` conditions, then per bit with the bit-vector
   equations of the context (`bits_hyps`), refuting a hypothesis `¬ a = b` where needed;
4. `kbv_nat`: case split, then the `toNat`/`toInt` arithmetic (`bitvec_to_nat`, masks `2^k - 1` as
   `% 2^k`) and `omega`;
5. `kbv_sext`: `==`/`slt`/`sle` as comparisons of the `toInt`s, through sign extensions;
6. `kbv_split`: case split on the `cond`/`ite` conditions of the goal and the context, innermost
   first, then one of the other methods per case;
7. sign masks: an arithmetic shift right by `w - 1` as `bif x.msb then allOnes else 0`, the sign
   bit of `x ||| -x` as `x != 0`;
8. `kbv_genshift`: variable shift amounts `t % n` normalised (masks, widths) and generalized, then
   `kbv_bitsc` with symbolic amounts;
9. `kbv_shift`: case split on a variable shift amount `t % n`, then `kbv_nat` or `kbv_bitsc`;
10. `kbv_modsplit`: shift-amount masks `x &&& (2^k - 1)` as `x.toNat % 2^k`, case split on it
   (everywhere, also outside shifts), then `kbv_bitsc` or `kbv_nat`;
11. `kbv_beq`: an equation of `==` tests as an `iff` of equations (zero tests of `cpop`, `reverse`
   and rotations by lemma), each direction by `kbv_bitschr`: per bit with the hypotheses at the
   same bit (`kbv_bitsch`) or at every bit (`kbv_bitscha`, for permuted bits), or by refuting a
   hypothesis `¬ a = b`;
12. `kbv_bitsch` alone: bit extensionality, every bit index tested together with the same bit of
   each bit-vector hypothesis;
13. `kbv_minterm`: linear combinations of bitwise terms (`x <<< k` as `x * 2^k`): every bitwise
   term as the sum of its (disjoint) minterms, then `grind`'s commutative-ring normalization;
14. `~~~x` as `-x - 1`, then `grind`; `grind`;
15. `kbv_bitsc`: bit extensionality at each concrete index, then `simp`.

Before the search, zero-extension equations `a.setWidth w = b.setWidth w` become `a.toNat = b.toNat`
(`setWidth_eq_iff_toNat`), and the shift-splitting methods rewrite shift amounts with such
hypotheses (`toNat_rw`).

Every alternative runs under `kbv_guard` (it must close the goal; runtime exceptions are failures;
a fresh heartbeat budget: 20M by default, more for the case-splitting methods), without error
recovery; the whole search is bounded by `searchHeartbeats`. The option `kbv.budgetScale`
multiplies all these budgets.

A search's heartbeats are not counted in the enclosing declaration's `maxHeartbeats` (`isolate`
resets the counter), so a proof can stay under its limit while its searches take an hour
(`ok_rule_icmp_84`: 2.6 G heartbeats charged, 93 G done). `-Dkbv.reportHeartbeats=<N>` prints every
search above `N` thousand heartbeats to standard error, failed ones included.
-/


namespace Opt.Proof.KernelBV
open Lean Meta Elab Tactic

theorem toNat_and_lowmask {w : Nat} (x : BitVec w) (k : Nat) (hk : k ≤ w) :
    (x &&& BitVec.ofNat w (2 ^ k - 1)).toNat = x.toNat % 2 ^ k := by
  rw [BitVec.toNat_and, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by have := Nat.pow_le_pow_right (n := 2) (by omega) hk; have := Nat.two_pow_pos k; omega),
    Nat.and_two_pow_sub_one_eq_mod]

example : ((0xABCD#16 &&& BitVec.ofNat 16 (2 ^ 8 - 1))).toNat = (0xABCD#16).toNat % 2 ^ 8 :=
  toNat_and_lowmask _ 8 (by decide)

theorem toNat_lowmask_and {w : Nat} (x : BitVec w) (k : Nat) (hk : k ≤ w) :
    (BitVec.ofNat w (2 ^ k - 1) &&& x).toNat = x.toNat % 2 ^ k := by
  rw [BitVec.and_comm, toNat_and_lowmask x k hk]

example : ((BitVec.ofNat 16 (2 ^ 8 - 1) &&& 0xABCD#16)).toNat = (0xABCD#16).toNat % 2 ^ 8 :=
  toNat_lowmask_and _ 8 (by decide)

/-- `(x &&& c).toNat` for a literal `c = 2^k - 1`. -/
simproc_decl reduceToNatAndMask (BitVec.toNat (_ &&& _)) := fun e => do
  let_expr BitVec.toNat _ a := e | return .continue
  let_expr HAnd.hAnd _ _ _ _ x c := a | return .continue
  let tryMask (x c : Expr) (lemma : Name) : SimpM (Option Simp.Step) := do
    let some ⟨w, v⟩ ← Lean.Meta.getBitVecValue? c | return none
    let k := (v.toNat + 1).log2
    if 2 ^ k != v.toNat + 1 || k > w then return none
    let wE := mkNatLit w
    let kE := mkNatLit k
    let hk ← mkDecideProof (← mkAppM ``LE.le #[kE, wE])
    let pf := mkApp4 (mkConst lemma) wE x kE hk
    let rhs := (← inferType pf).appArg!
    return some (.done { expr := rhs, proof? := some pf })
  if let some s ← tryMask x c ``toNat_and_lowmask then return s
  if let some s ← tryMask c x ``toNat_lowmask_and then return s
  return .continue

/-- Boolean atoms of `e`: maximal closed `Bool`-typed subterms that are not Boolean connectives. -/
partial def boolAtoms (e : Expr) (acc : Array Expr) : MetaM (Array Expr) := do
  let push (acc : Array Expr) (e : Expr) := if acc.contains e then acc else acc.push e
  if !e.hasLooseBVars then
    let isBool ← (do return (← whnfR (← inferType e)).isConstOf ``Bool) <|> pure false
    if isBool then
      if e.isConstOf ``Bool.true || e.isConstOf ``Bool.false then return acc
      match_expr e with
      | and a b => return (← boolAtoms b (← boolAtoms a acc))
      | or a b => return (← boolAtoms b (← boolAtoms a acc))
      | xor a b => return (← boolAtoms b (← boolAtoms a acc))
      | not a => return (← boolAtoms a acc)
      | bne α _ a b => if α.isConstOf ``Bool then return (← boolAtoms b (← boolAtoms a acc)) else return push acc e
      | BEq.beq α _ a b => if α.isConstOf ``Bool then return (← boolAtoms b (← boolAtoms a acc)) else return push acc e
      | cond _ c a b => return (← boolAtoms b (← boolAtoms a (← boolAtoms c acc)))
      | _ => return push acc e
  match e with
  | .app f a => boolAtoms a (← boolAtoms f acc)
  | .forallE _ d b _ => boolAtoms b (← boolAtoms d acc)
  | .lam _ d b _ => boolAtoms b (← boolAtoms d acc)
  | .mdata _ b => boolAtoms b acc
  | _ => return acc

/-- Close a goal that is a Boolean tautology in its `Bool` atoms: generalize them, decide. -/
elab "bool_tauto" : tactic => do
  let g ← getMainGoal
  let bhs ← g.withContext do
    let mut out := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      let ty' := if ty.isAppOfArity ``Not 1 then ty.appArg! else ty
      if let some (α, _, _) := ty'.eq? then
        if α.isConstOf ``Bool then out := out.push d.fvarId
    pure out
  let (_, g) ← g.revert bhs
  g.withContext do
    let t ← instantiateMVars (← g.getType)
    let atoms ← boolAtoms t #[]
    if atoms.size > 10 then throwError "bool_tauto: {atoms.size} atoms"
    let args := atoms.map fun a => ({ expr := a } : GeneralizeArg)
    let (fvs, g) ← g.generalize args
    let (_, g) ← g.revert fvs
    setGoals [g]
    evalTactic (← `(tactic| decide))

theorem forall_lt_succ {P : Nat → Prop} {n : Nat} (h0 : P n) (h : ∀ i, i < n → P i) :
    ∀ i, i < n + 1 → P i := fun i hi => by
  rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi | rfl
  · exact h i hi
  · exact h0
theorem forall_lt_zero {P : Nat → Prop} : ∀ i, i < 0 → P i := fun _ h => absurd h (Nat.not_lt_zero _)

example : ∀ i, i < 2 → i * i < 2 :=
  forall_lt_succ (P := fun i => i * i < 2) (by decide)
    (forall_lt_succ (P := fun i => i * i < 2) (by decide) forall_lt_zero)

def boundedForall (P : Expr) (k : Nat) : MetaM Expr :=
  withLocalDeclD `i (mkConst ``Nat) fun i => do
    let h ← mkAppM ``LT.lt #[i, mkNatLit k]
    mkForallFVars #[i] (← mkArrow h (P.beta #[i]))

/-- Goal `∀ i, i < n → P i` (`n` a literal): one goal `P k` per `k < n`. -/
elab "idx_split" : tactic => do
  let g ← getMainGoal
  let goals ← g.withContext do
    let t ← instantiateMVars (← g.getType)
    let .forallE nm ty body _ := t | throwError "idx_split: not ∀"
    let .forallE _ hty q _ := body | throwError "idx_split: not ∀ i, i < n → _"
    let some n := (hty.getArg! 3).nat? <|> (hty.getArg! 3).rawNatLit? | throwError "idx_split: bound"
    let P := Expr.lam nm ty (q.lowerLooseBVars 1 1) .default
    let mut goals := #[]
    let mut cur := g
    for j in [0:n] do
      let k := n - 1 - j
      let hk ← mkFreshExprSyntheticOpaqueMVar (P.beta #[mkNatLit k])
      goals := goals.push hk.mvarId!
      let rest ← mkFreshExprSyntheticOpaqueMVar
        (← boundedForall P k)
      cur.assign (mkApp4 (mkConst ``forall_lt_succ) P (mkNatLit k) hk rest)
      cur := rest.mvarId!
    cur.assign (mkApp (mkConst ``forall_lt_zero) P)
    pure goals
  setGoals goals.toList

register_option kbv.budgetScale : Nat := {
  defValue := 1
  descr := "multiplier of the heartbeat budgets of `kbv`'s methods and of its whole search"
}

/-- Run `t` with a fresh budget of `n` (default 20000) thousand heartbeats, times
`kbv.budgetScale`, and require it to close every goal; a runtime exception (heartbeats, recursion
depth) becomes an ordinary failure. -/
elab "kbv_guard " n?:(num)? t:tactic : tactic => do
  let n := (n?.map (·.getNat)).getD 20000 * kbv.budgetScale.get (← getOptions)
  let s ← saveState
  tryCatchRuntimeEx (withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := n * 1000 }) <|
    withCurrHeartbeats do
      evalTactic t
      unless (← getUnsolvedGoals).isEmpty do throwError "unsolved goals") fun e => do
    s.restore
    throwError "kbv_guard: {e.toMessageData}"

def isBVEq (t : Expr) : MetaM Bool := do
  let some (ty, _, _) := t.eq? | return false
  return (← whnfR ty).isAppOfArity ``BitVec 1

mutual
/-- Bit route with hypotheses: the goal (an equation of bit vectors, or `False` with a hypothesis
`¬ a = b`) per bit, the bit-vector equations of the context at the same bit, then `bool_tauto`. -/
partial def bitsHyps : TacticM Unit := do
  let g ← getMainGoal
  let t ← g.withContext do whnfR (← instantiateMVars (← g.getType))
  if t.isAppOfArity ``Not 1 then
    evalTactic (← `(tactic| intro))
    return ← bitsHyps
  if ← g.withContext (isBVEq t) then
    let s ← saveState
    try bitsExt; return
    catch _ => s.restore
  refute

partial def bitsExt : TacticM Unit := do
  evalTactic (← `(tactic| apply BitVec.eq_of_getLsbD_eq))
  let (ivs, g) ← (← getMainGoal).introN 2
  let g ← g.withContext do
    let idecl ← ivs[0]!.getDecl
    let mut g := g
    let mut hs := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      if ← isBVEq (← instantiateMVars d.type) then hs := hs.push d.toExpr
    for h in hs do
      let some (ty, _, _) := (← instantiateMVars (← inferType h)).eq? | continue
      let f ← withLocalDeclD `z ty fun z => do mkLambdaFVars #[z] (← mkAppM ``BitVec.getLsbD #[z, idecl.toExpr])
      let pf ← mkAppM ``congrArg #[f, h]
      let pty ← instantiateMVars (← inferType pf)
      let pty ← Core.betaReduce pty
      g ← g.assert `hb pty pf
    -- the bound as a `Bool` fact (`getLsbD_allOnes` gives `decide (i < w)`), for `bool_tauto`
    let hdec ← mkAppM ``decide_eq_true #[mkFVar ivs[1]!]
    g ← g.assert `hdec (← inferType hdec) hdec
    pure g
  replaceMainGoal [g]
  evalTactic (← `(tactic| simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_xor,
    BitVec.getLsbD_not, BitVec.getLsbD_zero, BitVec.getLsbD_allOnes, BitVec.getLsbD_one, Bool.true_and,
    Bool.and_true, Bool.false_and, Bool.and_false, Nat.reduceLT, Nat.reduceGT, Nat.reduceLeDiff, decide_true, decide_false] at *))
  evalTactic (← `(tactic| bool_tauto))

partial def refute : TacticM Unit := do
  evalTactic (← `(tactic| exfalso))
  let g ← getMainGoal
  let hs ← g.withContext do
    let mut hs := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let ty ← whnfR (← instantiateMVars d.type)
      if ty.isAppOfArity ``Not 1 then
        if ← isBVEq ty.appArg! then hs := hs.push d.toExpr
    pure hs
  for h in hs do
    let s ← saveState
    try
      let gs ← g.apply h
      replaceMainGoal gs
      bitsHyps
      return
    catch _ => s.restore
  throwError "bitsHyps: no refutable hypothesis"
end

elab "bits_hyps" : tactic => bitsHyps

theorem add_disj {w : Nat} {x y : BitVec w} (h : x &&& y = 0#w) : x + y = x ||| y :=
  BitVec.add_eq_or_of_and_eq_zero x y h

example : 0xF0#8 + 0x0F#8 = 0xF0#8 ||| 0x0F#8 := add_disj (by decide)

/-- The `toNat` of a concatenation as a sum (`BitVec.toNat_append` gives `<<<`/`|||`). -/
theorem shiftLeft_or_toNat {n : Nat} (a : Nat) (y : BitVec n) :
    (a <<< n ||| y.toNat) = a * 2 ^ n + y.toNat := by
  rw [← Nat.shiftLeft_add_eq_or_of_lt y.isLt, Nat.shiftLeft_eq]

example : (3 <<< 8 ||| (5#8).toNat) = 3 * 2 ^ 8 + (5#8).toNat := shiftLeft_or_toNat 3 5#8

/-- A goal `P a` with `a < n` (proof `h`) as the goals `P 0`, …, `P (n-1)`: the statement
`∀ k, k < n → P k` (the other occurrences of `a`'s variables are kept). -/
theorem forall_lt_of {P : Nat → Prop} {n a : Nat} (h : a < n) (hP : ∀ k, k < n → P k) : P a :=
  hP a h

example : (5 % 3) * 0 = 0 := forall_lt_of (P := fun k => k * 0 = 0) (Nat.mod_lt 5 (by decide))
  (fun k _ => Nat.mul_zero k)

/-- First non-literal shift amount `t % n` (`n` a literal) of a `Nat`-amount shift in `e`. -/
partial def findModAmount (e : Expr) : Option (Expr × Nat) :=
  let amt? : Option Expr :=
    if e.isAppOfArity ``HShiftLeft.hShiftLeft 6 || e.isAppOfArity ``HShiftRight.hShiftRight 6 then
      some e.appArg!
    else if e.isAppOfArity ``BitVec.sshiftRight 3 then some e.appArg! else none
  let here : Option (Expr × Nat) := match amt? with
    | some a =>
      if a.isAppOfArity ``HMod.hMod 6 && !a.hasLooseBVars then
        match a.appArg!.nat? <|> a.appArg!.rawNatLit? with
        | some n => if a.appFn!.appArg!.nat?.isNone then some (a, n) else none
        | none => none
      else none
    | none => none
  here.orElse fun _ => match e with
    | .app f a => (findModAmount f).orElse fun _ => findModAmount a
    | .forallE _ d b _ => (findModAmount d).orElse fun _ => findModAmount b
    | .mdata _ b => findModAmount b
    | _ => none

/-- Split the goal on its first variable shift amount `t % n` into `n` constant-amount goals. -/
elab "shift_split" : tactic => do
  let g ← getMainGoal
  let gs ← g.withContext do
    let t ← instantiateMVars (← g.getType)
    let some (a, n) := findModAmount t | throwError "shift_split: no variable shift amount"
    let h ← mkAppM ``Nat.mod_lt #[a.appFn!.appArg!, ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit 0, mkNatLit n])]
    let P ← withLocalDeclD `k (mkConst ``Nat) fun k => do
      mkLambdaFVars #[k] ((← kabstract t a).instantiate1 k)
    let hP ← mkFreshExprSyntheticOpaqueMVar (← boundedForall P n)
    g.assign (mkApp5 (mkConst ``forall_lt_of) P (mkNatLit n) a h hP)
    pure [hP.mvarId!]
  setGoals gs
  evalTactic (← `(tactic| idx_split))

theorem toNat_and_le_left {w : Nat} (x y : BitVec w) : (x &&& y).toNat ≤ x.toNat := by
  rw [BitVec.toNat_and]; exact Nat.and_le_left
theorem toNat_and_le_right {w : Nat} (x y : BitVec w) : (x &&& y).toNat ≤ y.toNat := by
  rw [BitVec.toNat_and]; exact Nat.and_le_right
theorem toNat_le_or_left {w : Nat} (x y : BitVec w) : x.toNat ≤ (x ||| y).toNat := by
  rw [BitVec.toNat_or]; exact Nat.left_le_or
theorem toNat_le_or_right {w : Nat} (x y : BitVec w) : y.toNat ≤ (x ||| y).toNat := by
  rw [BitVec.toNat_or]; exact Nat.right_le_or

example : (0xF0#8 &&& 0x3C#8).toNat ≤ (0x3C#8).toNat ∧ (0xF0#8 &&& 0x3C#8).toNat ≤ (0xF0#8).toNat ∧
    (0xF0#8).toNat ≤ (0xF0#8 ||| 0x3C#8).toNat ∧ (0x3C#8).toNat ≤ (0xF0#8 ||| 0x3C#8).toNat :=
  ⟨toNat_and_le_right _ _, toNat_and_le_left _ _, toNat_le_or_left _ _, toNat_le_or_right _ _⟩

/-- `clz x = 0` exactly when the sign bit is set. -/
theorem clz_beq_zero {w : Nat} (hw : 0 < w) (x : BitVec w) : (x.clz == 0#w) = x.msb := by
  have h := BitVec.clz_eq_zero_iff (x := x) hw
  rw [BitVec.msb_eq_decide]
  apply Bool.eq_iff_iff.2
  simp only [beq_iff_eq, decide_eq_true_eq, ← h, BitVec.toNat_eq, BitVec.toNat_ofNat, Nat.zero_mod]

example : ((0x80#8).clz == 0#8) = (0x80#8).msb := clz_beq_zero (by decide) _

/-- `ctz x = 0` exactly when the lowest bit is set. -/
theorem ctz_beq_zero {w : Nat} (hw : 0 < w) (x : BitVec w) : (x.ctz == 0#w) = x.getLsbD 0 := by
  rw [BitVec.ctz, clz_beq_zero hw, BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_reverse]
  simp only [BitVec.getMsbD, show w - 1 < w by omega, decide_true, Bool.true_and,
    show w - 1 - (w - 1) = 0 by omega]

example : ((0x81#8).ctz == 0#8) = (0x81#8).getLsbD 0 := ctz_beq_zero (by decide) _

theorem signExtend_allOnes {w v : Nat} (hw : 0 < w) :
    (BitVec.allOnes w).signExtend v = BitVec.allOnes v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_signExtend, BitVec.getLsbD_allOnes, BitVec.msb_allOnes hw, hi, decide_true]
  split <;> simp [*]

example : (BitVec.allOnes 64).signExtend 128 = BitVec.allOnes 128 := signExtend_allOnes (by decide)

/-- `Clif.Sem.select` as a `cond` on the truthiness of the condition. -/
theorem select_eq_cond {v w : Nat} (c : BitVec v) (x y : BitVec w) :
    Clif.Sem.select c x y = bif c != 0 then x else y := by
  rw [Bool.cond_eq_ite]; rfl

/-- Zero extensions to a common width agree exactly when the values do. -/
theorem setWidth_eq_iff_toNat {v₁ v₂ w : Nat} (h₁ : v₁ ≤ w) (h₂ : v₂ ≤ w) (a : BitVec v₁)
    (b : BitVec v₂) : a.setWidth w = b.setWidth w ↔ a.toNat = b.toNat := by
  have p₁ := Nat.pow_le_pow_right (n := 2) (by decide) h₁
  have p₂ := Nat.pow_le_pow_right (n := 2) (by decide) h₂
  have ha := a.isLt
  have hb := b.isLt
  rw [← BitVec.toNat_inj, BitVec.toNat_setWidth, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)]

example : (0x12#8).setWidth 64 = (0x12#16).setWidth 64 ↔ (0x12#8).toNat = (0x12#16).toNat :=
  setWidth_eq_iff_toNat (by decide) (by decide) _ _

/-- Rewrite the goal with the hypotheses `a.toNat = b.toNat` (where they apply). -/
elab "toNat_rw" : tactic => do
  let g ← getMainGoal
  let g ← g.withContext do
    let mut g := g
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let some (_, l, r) := (← instantiateMVars d.type).eq? | continue
      unless l.isAppOfArity ``BitVec.toNat 2 && r.isAppOfArity ``BitVec.toNat 2 do continue
      try
        let res ← g.rewrite (← g.getType) d.toExpr
        g ← g.replaceTargetEq res.eNew res.eqProof
      catch _ => pure ()
    pure g
  replaceMainGoal [g]

/-- A shift amount `y.toNat % n` survives sign extension when `n` divides both moduli. -/
theorem toNat_signExtend_mod {w v n : Nat} (x : BitVec w) (hw : n ∣ 2 ^ w) (hv : n ∣ 2 ^ v) :
    (x.signExtend v).toNat % n = x.toNat % n := by
  have hc : n ∣ (if x.msb then 2 ^ v - 2 ^ w else 0) := by
    split
    · exact Nat.dvd_sub hv hw
    · exact Nat.dvd_zero n
  rw [BitVec.toNat_signExtend, BitVec.toNat_setWidth, Nat.add_mod, Nat.mod_mod_of_dvd _ hv,
    Nat.mod_eq_zero_of_dvd hc, Nat.add_zero, Nat.mod_mod]

example : (BitVec.signExtend 64 (0x85#8)).toNat % 8 = (0x85#8).toNat % 8 :=
  toNat_signExtend_mod _ (by decide) (by decide)

/-- A shift amount `y.toNat % n` survives a change of width when `n` divides the new modulus. -/
theorem toNat_setWidth_mod {w v n : Nat} (x : BitVec w) (hv : n ∣ 2 ^ v) :
    (x.setWidth v).toNat % n = x.toNat % n := by
  rw [BitVec.toNat_setWidth, Nat.mod_mod_of_dvd _ hv]

example : (BitVec.setWidth 16 (0x85#8)).toNat % 8 = (0x85#8).toNat % 8 :=
  toNat_setWidth_mod _ (by decide)

example : Clif.Sem.select (1#8) (2#8) (3#8) = 2#8 := by rw [select_eq_cond]; decide

/-- An arithmetic shift right by `w - 1` is the sign mask. -/
theorem sshiftRight_pred_width {w n : Nat} (h : n + 1 = w) (x : BitVec w) :
    x.sshiftRight n = bif x.msb then BitVec.allOnes w else 0#w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_sshiftRight]
  cases hm : x.msb <;> simp only [Bool.cond_true, Bool.cond_false, BitVec.getLsbD_allOnes,
    BitVec.getLsbD_zero, hi, decide_true] <;>
  · by_cases hi0 : i = 0
    · subst hi0
      have : x.getLsbD n = x.msb := by rw [BitVec.msb_eq_getLsbD_last]; congr 1; omega
      simp [show ¬ w ≤ 0 by omega, this, hm]
    · simp [show ¬ w ≤ i by omega, show ¬ n + i < w by omega]

example : (0x80#8).sshiftRight 7 = 0xFF#8 := by rw [sshiftRight_pred_width (by decide)]; decide

/-- `x ||| -x` has its sign bit set exactly when `x` is nonzero. -/
theorem msb_or_neg {w : Nat} (x : BitVec w) : (x ||| -x).msb = (x != 0#w) := by
  rcases w with _ | w
  · simp [BitVec.eq_nil x]
  rw [BitVec.msb_or]
  by_cases hx : x = 0#(w+1)
  · subst hx; simp
  · have hx' : x.toNat ≠ 0 := fun h => hx (BitVec.eq_of_toNat_eq (by simp [h]))
    rw [BitVec.msb_eq_decide, BitVec.msb_eq_decide, BitVec.toNat_neg]
    have hlt := x.isLt
    have hp : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [Nat.pow_succ]; omega
    rw [show (x != 0#(w+1)) = true by simpa using hx, Nat.add_sub_cancel,
      Nat.mod_eq_of_lt (by omega)]
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    omega

theorem msb_neg_or {w : Nat} (x : BitVec w) : (-x ||| x).msb = (x != 0#w) := by
  rw [BitVec.or_comm, msb_or_neg]

example : (0x02#8 ||| -0x02#8).msb = true ∧ (-0#8 ||| 0#8).msb = false :=
  ⟨msb_or_neg _, msb_neg_or _⟩

/-- A logical shift right by `w - 1` as the sign bit. -/
theorem ushiftRight_pred_width {w n : Nat} (h : n + 1 = w) (x : BitVec w) :
    x >>> n = bif x.msb then 1#w else 0#w := by
  subst h
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  have hp : 2 ^ (n + 1) = 2 * 2 ^ n := Nat.pow_succ'
  have h1 : 1 < 2 ^ (n + 1) := by have := Nat.two_pow_pos n; omega
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.msb_eq_decide]
  by_cases hm : 2 ^ (n + 1 - 1) ≤ x.toNat
  · simp only [hm, decide_true, Bool.cond_true, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1]
    simp only [Nat.add_sub_cancel] at hm
    apply Nat.div_eq_of_lt_le <;> omega
  · simp only [hm, decide_false, Bool.cond_false, BitVec.toNat_ofNat, Nat.zero_mod]
    simp only [Nat.add_sub_cancel] at hm
    exact Nat.div_eq_of_lt (by omega)

example : (0x81#8) >>> 7 = bif (0x81#8).msb then 1#8 else 0#8 := ushiftRight_pred_width (by decide) _

/-- A rotation left written with shifts (`m = w - k`, `k < w`). -/
theorem shl_or_shr_eq_rotateLeft {w : Nat} (x : BitVec w) {k m : Nat} (hk : k < w)
    (hm : m = w - k) : x <<< k ||| x >>> m = x.rotateLeft k := by
  subst hm; rw [BitVec.rotateLeft_eq_rotateLeftAux_of_lt hk]; rfl

/-- A rotation right written with shifts (`m = w - k`, `k < w`). -/
theorem shr_or_shl_eq_rotateRight {w : Nat} (x : BitVec w) {k m : Nat} (hk : k < w)
    (hm : m = w - k) : x >>> k ||| x <<< m = x.rotateRight k := by
  subst hm; rw [BitVec.rotateRight_eq_rotateRightAux_of_lt hk]; rfl

example : 0x81#8 <<< 3 ||| 0x81#8 >>> 5 = (0x81#8).rotateLeft 3 ∧
    0x81#8 >>> 3 ||| 0x81#8 <<< 5 = (0x81#8).rotateRight 3 :=
  ⟨shl_or_shr_eq_rotateLeft _ (by decide) rfl, shr_or_shl_eq_rotateRight _ (by decide) rfl⟩

theorem rotateLeft_rotateRight_of_lt {w : Nat} (x : BitVec w) {k : Nat} (hk : k < w) :
    (x.rotateRight k).rotateLeft k = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_rotateLeft, BitVec.getLsbD_rotateRight, BitVec.getLsbD_rotateRight,
    Nat.mod_eq_of_lt hk]
  by_cases h : i < k
  · simp [h, show ¬ w - k + i < w - k by omega, show w - k + i < w by omega,
      show w - k + i - (w - k) = i by omega]
  · simp [h, hi, show i - k < w - k by omega, show k + (i - k) = i by omega]

theorem rotateRight_rotateLeft_of_lt {w : Nat} (x : BitVec w) {k : Nat} (hk : k < w) :
    (x.rotateLeft k).rotateRight k = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_rotateRight, BitVec.getLsbD_rotateLeft, BitVec.getLsbD_rotateLeft,
    Nat.mod_eq_of_lt hk]
  by_cases h : i < w - k
  · simp [h, show ¬ k + i < k by omega, show k + i < w by omega, show k + i - k = i by omega]
  · simp [h, hi, show i - (w - k) < k by omega, show w - k + (i - (w - k)) = i by omega]

example : ((0x81#8).rotateRight 3).rotateLeft 3 = 0x81#8 ∧
    ((0x81#8).rotateLeft 3).rotateRight 3 = 0x81#8 :=
  ⟨rotateLeft_rotateRight_of_lt _ (by decide), rotateRight_rotateLeft_of_lt _ (by decide)⟩

/-- Bounds of the `toNat` of the bitwise terms of `e` (`(x &&& y).toNat ≤ x.toNat`, …), and of
the `Nat` bitwise terms, as the facts `omega` lacks. -/
partial def bwToNat (e : Expr) (acc : Array Expr) : Array Expr :=
  let isBw (a : Expr) := a.isAppOfArity ``HAnd.hAnd 6 || a.isAppOfArity ``HOr.hOr 6
  let acc :=
    if e.hasLooseBVars then acc
    else if e.isAppOfArity ``BitVec.toNat 2 && isBw e.appArg! && !acc.contains e.appArg! then
      acc.push e.appArg!
    else if isBw e && (e.getArg! 0).isConstOf ``Nat && !acc.contains e then acc.push e
    else acc
  match e with
  | .app f a => bwToNat a (bwToNat f acc)
  | .forallE _ d b _ => bwToNat b (bwToNat d acc)
  | .lam _ d b _ => bwToNat b (bwToNat d acc)
  | .mdata _ b => bwToNat b acc
  | _ => acc

elab "kbv_facts" : tactic => do
  let g ← getMainGoal
  let g ← g.withContext do
    let mut ts := #[← instantiateMVars (← g.getType)]
    for d in ← getLCtx do
      unless d.isImplementationDetail do ts := ts.push (← instantiateMVars d.type)
    let bws := ts.foldl (fun acc t => bwToNat t acc) #[]
    let mut g := g
    for b in bws do
      let x := b.appFn!.appArg!
      let y := b.appArg!
      let isNat := (b.getArg! 0).isConstOf ``Nat
      let lemmas := if b.isAppOfArity ``HAnd.hAnd 6 then
          if isNat then #[``Nat.and_le_left, ``Nat.and_le_right] else #[``toNat_and_le_left, ``toNat_and_le_right]
        else if isNat then #[``Nat.left_le_or, ``Nat.right_le_or] else #[``toNat_le_or_left, ``toNat_le_or_right]
      for l in lemmas do
        let pf ← if isNat then mkAppOptM l #[some x, some y] else mkAppM l #[x, y]
        g ← g.assert `hbw (← inferType pf) pf
    pure g
  let (_, g) ← g.intros
  replaceMainGoal [g]

/-- The first closed `cond`/`ite` condition of `e` without conditions inside (a `Bool`
condition `c = true` as `c`). -/
partial def innerCond? (e : Expr) : Option Expr :=
  let here : Option Expr :=
    if e.isAppOfArity ``cond 4 || e.isAppOfArity ``ite 5 then
      let c := e.getArg! 1
      match innerCond? c with
      | some c' => some c'
      | none =>
        if c.hasLooseBVars then none
        else match c.eq? with
          | some (α, l, r) => if α.isConstOf ``Bool && r.isConstOf ``Bool.true then some l else some c
          | none => some c
    else none
  here.orElse fun _ => match e with
    | .app f a => (innerCond? f).orElse fun _ => innerCond? a
    | .forallE _ d b _ => (innerCond? d).orElse fun _ => innerCond? b
    | .lam _ d b _ => (innerCond? d).orElse fun _ => innerCond? b
    | .mdata _ b => innerCond? b
    | _ => none

/-- Case split on the `cond`/`ite` conditions of the goal and the hypotheses, innermost first,
evaluating the conditionals after each split (at most `fuel` nested splits). -/
partial def splitConds (fuel : Nat) : TacticM Unit := do
  let g ← getMainGoal
  let c? ← g.withContext do
    if let some c := innerCond? (← instantiateMVars (← g.getType)) then return some c
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      if let some c := innerCond? (← instantiateMVars d.type) then return some c
    return none
  let some c := c? | return
  if fuel == 0 then throwError "kbv_split: too many conditions"
  let simpS ← `(tactic| simp only [Bool.cond_true, Bool.cond_false, ite_true, ite_false, ↓reduceIte,
      Bool.not_true, Bool.not_false, Bool.true_and, Bool.false_and, Bool.and_true, Bool.and_false,
      Bool.true_or, Bool.false_or, Bool.or_true, Bool.or_false, BitVec.reduceBEq, BitVec.reduceBNe,
      BitVec.reduceEq, BitVec.reduceNe, BitVec.reduceAnd, BitVec.reduceOr, BitVec.reduceXOr,
      BitVec.reduceNot, BitVec.reduceSub, BitVec.reduceAdd, BitVec.reduceMul, BitVec.reduceNeg,
      beq_self_eq_true, bne_self_eq_false, Bool.true_eq_false, Bool.false_eq_true,
      not_true_eq_false, not_false_eq_true, eq_self_iff_true])
  -- the cases, each with its case hypothesis `h`
  let cases ← g.withContext do
    if (← whnfR (← inferType c)).isConstOf ``Bool then
      let (fvs, g') ← g.generalize #[{ expr := c, xName? := `b, hName? := `h }]
      let sub ← g'.cases fvs[0]!
      sub.toList.mapM fun s => do
        let h := (s.subst.get fvs[1]!).fvarId!
        return (s.mvarId, h)
    else
      let (s1, s2) ← g.byCases c
      return [(s1.mvarId, s1.fvarId), (s2.mvarId, s2.fvarId)]
  let mut out := #[]
  for (g, h) in cases do
    -- evaluate the conditionals everywhere but in the case hypothesis (the simp arguments are
    -- elaborated in the main goal's context)
    setGoals [g]
    let g? ← g.withContext do
      let { ctx, simprocs, .. } ← mkSimpContext simpS (eraseLocal := false)
      let thms ← ctx.simpTheorems.addTheorem (.fvar h) (mkFVar h)
      let ctx := ctx.setSimpTheorems thms
      let mut fvs := #[]
      for d in ← getLCtx do
        if d.isImplementationDetail || d.fvarId == h then continue
        if ← isProp d.type then fvs := fvs.push d.fvarId
      let (r, _) ← simpGoal g ctx simprocs (fvarIdsToSimp := fvs)
      return r.map (·.2)
    let some g := g? | continue
    setGoals [g]
    splitConds (fuel - 1)
    out := out ++ (← getGoals)
  setGoals out.toList

/-- `splitConds`, the `Bool` conditions first restated as `cond` (an `ite`'s `Decidable` instance
can make the generalization of its condition ill-typed); fails without conditions. -/
elab "kbv_split" : tactic => do
  evalTactic (← `(tactic| try simp only [← Bool.cond_eq_ite] at *))
  let g ← getMainGoal
  let found ← g.withContext do
    if (innerCond? (← instantiateMVars (← g.getType))).isSome then return true
    (← getLCtx).anyM fun d => do
      return !d.isImplementationDetail && (innerCond? (← instantiateMVars d.type)).isSome
  unless found do throwError "kbv_split: no condition"
  splitConds 8

/-- A literal `2 ^ w - 1` of `BitVec w` as `allOnes w`. -/
simproc_decl reduceLitAllOnes (BitVec.ofNat _ _) := fun e => do
  let some ⟨w, v⟩ ← Lean.Meta.getBitVecValue? e | return .continue
  if w == 0 || v.toNat + 1 != 2 ^ w then return .continue
  let rhs ← mkAppM ``BitVec.allOnes #[mkNatLit w]
  let pf ← mkDecideProof (← mkEq e rhs)
  return .done { expr := rhs, proof? := some pf }

/-- The closed `t % n` subterms (`t` not a literal, `n` a literal) of `e`. -/
partial def modTerms (e : Expr) (acc : Array Expr) : Array Expr :=
  let acc :=
    if !e.hasLooseBVars && e.isAppOfArity ``HMod.hMod 6 && (e.getArg! 0).isConstOf ``Nat &&
        (e.appArg!.nat? <|> e.appArg!.rawNatLit?).isSome && (e.appFn!.appArg!.nat?).isNone &&
        !acc.contains e then acc.push e else acc
  match e with
  | .app f a => modTerms a (modTerms f acc)
  | .forallE _ d b _ => modTerms b (modTerms d acc)
  | .mdata _ b => modTerms b acc
  | _ => acc

/-- Generalize the shift amounts `t % n` of the goal (now symbolic). -/
elab "kbv_genamt" : tactic => do
  let g ← getMainGoal
  let ts ← g.withContext do return modTerms (← instantiateMVars (← g.getType)) #[]
  if ts.isEmpty then throwError "kbv_genamt: no amount"
  let (_, g) ← g.generalize (ts.map fun t => ({ expr := t } : GeneralizeArg))
  replaceMainGoal [g]

theorem shiftLeft_eq_mul_ofNat {w : Nat} (x : BitVec w) (k : Nat) :
    x <<< k = x * BitVec.ofNat w (2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mul_mod_mod]

example : 0x0F#8 <<< 2 = 0x0F#8 * BitVec.ofNat 8 (2 ^ 2) := shiftLeft_eq_mul_ofNat _ 2

theorem and_lowmask_eq_ofNat {w : Nat} (x : BitVec w) (k : Nat) (hk : k ≤ w) :
    x &&& BitVec.ofNat w (2 ^ k - 1) = BitVec.ofNat w (x.toNat % 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_and_lowmask x k hk, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos k)) (Nat.pow_le_pow_right (by decide) hk))]

theorem lowmask_and_eq_ofNat {w : Nat} (x : BitVec w) (k : Nat) (hk : k ≤ w) :
    BitVec.ofNat w (2 ^ k - 1) &&& x = BitVec.ofNat w (x.toNat % 2 ^ k) := by
  rw [BitVec.and_comm, and_lowmask_eq_ofNat x k hk]

example : (0xAB#8 &&& BitVec.ofNat 8 (2 ^ 4 - 1)) = BitVec.ofNat 8 ((0xAB#8).toNat % 2 ^ 4) ∧
    (BitVec.ofNat 8 (2 ^ 4 - 1) &&& 0xAB#8) = BitVec.ofNat 8 ((0xAB#8).toNat % 2 ^ 4) :=
  ⟨and_lowmask_eq_ofNat _ 4 (by decide), lowmask_and_eq_ofNat _ 4 (by decide)⟩

/-- `x &&& c` for a literal `c = 2^k - 1`, `0 < k ≤ 7` (a shift-amount mask; `x` not a literal) as `BitVec.ofNat w (x.toNat % 2^k)`. -/
simproc_decl reduceAndMask (_ &&& _) := fun e => do
  let_expr HAnd.hAnd _ _ _ _ x c := e | return .continue
  let tryMask (x c : Expr) (lemma : Name) : SimpM (Option Simp.Step) := do
    if (← Lean.Meta.getBitVecValue? x).isSome then return none
    let some ⟨w, v⟩ ← Lean.Meta.getBitVecValue? c | return none
    let k := (v.toNat + 1).log2
    if 2 ^ k != v.toNat + 1 || k > w || k == 0 || k > 7 then return none
    let wE := mkNatLit w
    let kE := mkNatLit k
    let hk ← mkDecideProof (← mkAppM ``LE.le #[kE, wE])
    let pf := mkApp4 (mkConst lemma) wE x kE hk
    let rhs := (← inferType pf).appArg!
    return some (.done { expr := rhs, proof? := some pf })
  if let some s ← tryMask x c ``and_lowmask_eq_ofNat then return s
  if let some s ← tryMask c x ``lowmask_and_eq_ofNat then return s
  return .continue

/-- Split the goal on its first `t % n` (`n ≤ 64` a literal) into `n` goals with `t % n` a literal. -/
elab "mod_split" : tactic => do
  let g ← getMainGoal
  let gs ← g.withContext do
    let t ← instantiateMVars (← g.getType)
    let ts := (modTerms t #[]).filter fun a => match a.appArg!.nat? <|> a.appArg!.rawNatLit? with
      | some n => n ≤ 64 | none => false
    let some a := ts[0]? | throwError "mod_split: no t % n"
    let some n := a.appArg!.nat? <|> a.appArg!.rawNatLit? | throwError "mod_split"
    let h ← mkAppM ``Nat.mod_lt #[a.appFn!.appArg!, ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit 0, mkNatLit n])]
    let P ← withLocalDeclD `k (mkConst ``Nat) fun k => do
      mkLambdaFVars #[k] ((← kabstract t a).instantiate1 k)
    let hP ← mkFreshExprSyntheticOpaqueMVar (← boundedForall P n)
    g.assign (mkApp5 (mkConst ``forall_lt_of) P (mkNatLit n) a h hP)
    pure [hP.mvarId!]
  setGoals gs
  evalTactic (← `(tactic| idx_split))

theorem mod_mod_of_le {n m k : Nat} (hm : 0 < m) (h : m ≤ k) : n % m % k = n % m :=
  Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ hm) h)

example : 300 % 128 % 256 = 300 % 128 := mod_mod_of_le (by decide) (by decide)

/-- `mod_split` up to `n ≤ 128`, each goal `t % n = k → P k` (the case equation kept). -/
elab "mod_split2" : tactic => do
  let g ← getMainGoal
  let gs ← g.withContext do
    let t ← instantiateMVars (← g.getType)
    let ts := (modTerms t #[]).filter fun a => match a.appArg!.nat? <|> a.appArg!.rawNatLit? with
      | some n => n ≤ 128 | none => false
    let some a := ts[0]? | throwError "mod_split2: no t % n"
    let some n := a.appArg!.nat? <|> a.appArg!.rawNatLit? | throwError "mod_split2"
    let h ← mkAppM ``Nat.mod_lt #[a.appFn!.appArg!, ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit 0, mkNatLit n])]
    let P ← withLocalDeclD `k (mkConst ``Nat) fun k => do
      mkLambdaFVars #[k] (← mkArrow (← mkEq a k) ((← kabstract t a).instantiate1 k))
    let hP ← mkFreshExprSyntheticOpaqueMVar (← boundedForall P n)
    g.assign (mkApp (mkApp5 (mkConst ``forall_lt_of) P (mkNatLit n) a h hP) (← mkEqRefl a))
    pure [hP.mvarId!]
  setGoals gs
  evalTactic (← `(tactic| idx_split))

/-- A proof of `p` (in the context of `g`) by `omega` on the `toNat`s, if it finds one. -/
def omegaProof? (g : MVarId) (p : Expr) : TacticM (Option Expr) := g.withContext do
  let m ← mkFreshExprSyntheticOpaqueMVar p
  let s ← saveState
  try
    let gs ← Tactic.run m.mvarId! (evalTactic (← `(tactic| (
      (try simp (disch := decide) only [Opt.Proof.KernelBV.reduceToNatAndMask, BitVec.zeroExtend_eq_setWidth,
        Opt.Proof.KernelBV.toNat_signExtend_mod, Opt.Proof.KernelBV.toNat_setWidth_mod] at *)
      bv_omega))))
    if gs.isEmpty then return some (← instantiateMVars m)
    s.restore; return none
  catch _ => s.restore; return none

/-- Evaluate the amounts `t % n` (`n ≤ 128` a literal) of the goal that the context determines
(binary search with `omega`), rewriting each with its value. -/
elab "amt_eval" : tactic => do
  let mut changed := false
  let mut fuel := 8
  let mut skip : Array Expr := #[]
  while fuel > 0 do
    fuel := fuel - 1
    let g ← getMainGoal
    let t ← instantiateMVars (← g.getType)
    let ts := (modTerms t #[]).filter fun a => !skip.contains a && match a.appArg!.nat? <|> a.appArg!.rawNatLit? with
      | some n => n ≤ 128 | none => false
    let some a := ts[0]? | break
    let some n := a.appArg!.nat? <|> a.appArg!.rawNatLit? | break
    let mut lo := 0
    let mut hi := n
    let mut ok := true
    while ok && hi - lo > 1 do
      let mid := (lo + hi) / 2
      if (← omegaProof? g (← g.withContext (mkAppM ``LT.lt #[a, mkNatLit mid]))).isSome then hi := mid
      else if (← omegaProof? g (← g.withContext (mkAppM ``LE.le #[mkNatLit mid, a]))).isSome then lo := mid
      else ok := false
    let pf? ← if ok then omegaProof? g (← g.withContext (mkEq a (mkNatLit lo))) else pure none
    let some pf := pf? | skip := skip.push a; continue
    let r ← g.withContext (g.rewrite t pf)
    let g' ← g.replaceTargetEq r.eNew r.eqProof
    replaceMainGoal (g' :: r.mvarIds)
    changed := true
  unless changed do throwError "amt_eval: no amount determined"

/-- Bit route at concrete indices with the bit-vector equations of the context: each equation
`h : a = b` as `∀ i, a.getLsbD i = b.getLsbD i`, then per index of the goal (a literal after
`idx_split`) the instances at that index, `simp`, `bool_tauto`. -/
elab "kbv_bitsch" : tactic => do
  let g ← getMainGoal
  let (n, g) ← g.withContext do
    let mut g := g
    let mut n := 0
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      if !(← isBVEq ty) then continue
      let some (bty, _, _) := ty.eq? | continue
      let f ← withLocalDeclD `i (mkConst ``Nat) fun i => do
        let fz ← withLocalDeclD `z bty fun z => do mkLambdaFVars #[z] (← mkAppM ``BitVec.getLsbD #[z, i])
        mkLambdaFVars #[i] (← mkAppM ``congrArg #[fz, d.toExpr])
      g ← g.assert `hbits (← inferType f) f
      n := n + 1
    pure (n, g)
  let (fvs, g) ← g.introNP n
  replaceMainGoal [g]
  evalTactic (← `(tactic| apply BitVec.eq_of_getLsbD_eq))
  evalTactic (← `(tactic| idx_split))
  let gs ← getGoals
  let mut out := #[]
  for g in gs do
    let g ← g.withContext do
      let t ← instantiateMVars (← g.getType)
      let some (_, l, _) := t.eq? | return g
      let k := l.appArg!
      let mut g := g
      for fv in fvs do
        let pf := mkApp (mkFVar fv) k
        g ← g.assert `hb (← Core.betaReduce (← inferType pf)) pf
      let (_, g') ← g.intros
      pure g'
    out := out.push g
  setGoals out.toList
  evalTactic (← `(tactic| all_goals (
    simp [BitVec.msb_eq_getLsbD_last, BitVec.getElem_signExtend, BitVec.getElem_sshiftRight,
      BitVec.getElem_setWidth, BitVec.getElem_shiftLeft, BitVec.getElem_ushiftRight] at *
    first | done | bool_tauto)))

/-- `cpopNatRec` is zero exactly when the accumulator and the counted bits are. -/
theorem cpopNatRec_eq_zero_iff {w : Nat} (x : BitVec w) :
    ∀ n acc, x.cpopNatRec n acc = 0 ↔ acc = 0 ∧ ∀ i, i < n → x.getLsbD i = false
  | 0, acc => by simp [BitVec.cpopNatRec_zero_self]
  | n + 1, acc => by
    rw [BitVec.cpopNatRec_succ, cpopNatRec_eq_zero_iff x n]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨by omega, fun i hi => ?_⟩
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi | rfl
      · exact h2 i hi
      · cases h : x.getLsbD i <;> simp_all
    · rintro ⟨rfl, h⟩
      refine ⟨by simp [h n (by omega)], fun i hi => h i (by omega)⟩

example : (0#8).cpopNatRec 8 0 = 0 ↔ 0 = 0 ∧ ∀ i, i < 8 → (0#8).getLsbD i = false :=
  cpopNatRec_eq_zero_iff _ 8 0

/-- A population count is zero exactly when the value is. -/
theorem cpop_eq_zero_iff {w : Nat} (x : BitVec w) : x.cpop = 0#w ↔ x = 0#w := by
  rw [← BitVec.toNat_inj, BitVec.toNat_cpop, BitVec.toNat_ofNat, Nat.zero_mod, cpopNatRec_eq_zero_iff]
  constructor
  · rintro ⟨-, h⟩
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp [h i hi]
  · rintro rfl
    simp

example : (0x10#8).cpop = 0#8 ↔ 0x10#8 = 0#8 := cpop_eq_zero_iff _

/-- `cpop_eq_zero_iff` at the literal `0`. -/
theorem cpop_eq_zero_iff' {w : Nat} (x : BitVec w) : x.cpop = 0 ↔ x = 0 := cpop_eq_zero_iff x

example : (0x10#8).cpop = 0 ↔ 0x10#8 = 0 := cpop_eq_zero_iff' _

/-- `BitVec.reverse_eq_zero_iff` at the literal `0`. -/
theorem reverse_eq_zero_iff' {w : Nat} (x : BitVec w) : x.reverse = 0 ↔ x = 0 :=
  BitVec.reverse_eq_zero_iff

example : (0x10#8).reverse = 0 ↔ 0x10#8 = 0 := reverse_eq_zero_iff' _

/-- A rotation-like `x <<< a ||| x >>> b` (`a + b ≤ w`) is zero exactly when `x` is: every bit of
`x` survives one of the two shifts. -/
theorem shl_or_shr_eq_zero_iff {w : Nat} (x : BitVec w) {a b : Nat} (h : a + b ≤ w) :
    x <<< a ||| x >>> b = 0 ↔ x = 0 := by
  constructor
  · intro hx
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have h1 := congrArg (·.getLsbD (j + a)) hx
    have h2 := congrArg (·.getLsbD (j - b)) hx
    simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight] at h1 h2
    simp only [show ∀ i, (0 : BitVec w).getLsbD i = false from fun i => BitVec.getLsbD_zero, Bool.or_eq_false_iff] at h1 h2 ⊢
    by_cases hja : j + a < w
    · have := h1.1
      simp only [hja, decide_true, Bool.true_and, Nat.add_sub_cancel, Bool.and_eq_false_iff,
        Bool.not_eq_false', decide_eq_true_eq] at this
      rcases this with h3 | h3
      · omega
      · exact h3
    · have := h2.2
      rwa [show b + (j - b) = j by omega] at this
  · rintro rfl
    simp

/-- `shl_or_shr_eq_zero_iff` with the operands of `|||` swapped. -/
theorem shr_or_shl_eq_zero_iff {w : Nat} (x : BitVec w) {a b : Nat} (h : a + b ≤ w) :
    x >>> b ||| x <<< a = 0 ↔ x = 0 := by
  rw [BitVec.or_comm]; exact shl_or_shr_eq_zero_iff x h

example : (0x81#8 <<< 3 ||| 0x81#8 >>> 5 = 0) ↔ 0x81#8 = 0 := shl_or_shr_eq_zero_iff _ (by decide)

example : (0x81#8 >>> 5 ||| 0x81#8 <<< 3 = 0) ↔ 0x81#8 = 0 := shr_or_shl_eq_zero_iff _ (by decide)

/-- `BitVec.toInt_zero` at the literal `0`. -/
theorem toInt_zero' {w : Nat} : (0 : BitVec w).toInt = 0 := BitVec.toInt_zero

example : (0 : BitVec 8).toInt = 0 := toInt_zero'

/-- A bit-vector `==` as an equation of the `toInt`s. -/
theorem beq_eq_decide_toInt {w : Nat} (a b : BitVec w) : (a == b) = decide (a.toInt = b.toInt) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, BitVec.toInt_inj]

example : (3#4 == 3#4) = decide ((3#4).toInt = (3#4).toInt) := beq_eq_decide_toInt _ _

/-- Bit route for a goal `a = b` from bit-vector equations whose bits are permuted (rotations,
byte swaps): every bit-vector equation of the context (width at most 128) at every index, `simp`,
then per goal index `simp` and a matching hypothesis or `simp_all`. -/
elab "kbv_bitscha" : tactic => do
  let g ← getMainGoal
  let g ← g.withContext do
    let mut g := g
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      if !(← isBVEq ty) then continue
      let some (bty, _, _) := ty.eq? | continue
      let bw ← whnf bty.appArg!
      let some w := bw.rawNatLit? <|> bw.nat? | continue
      if w > 128 then continue
      for i in [0:w] do
        let fz ← withLocalDeclD `z bty fun z => do mkLambdaFVars #[z] (← mkAppM ``BitVec.getLsbD #[z, mkNatLit i])
        let pf ← mkAppM ``congrArg #[fz, d.toExpr]
        g ← g.assert `hb (← Core.betaReduce (← inferType pf)) pf
    pure g
  let (_, g) ← g.intros
  replaceMainGoal [g]
  evalTactic (← `(tactic| try simp [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight] at *))
  evalTactic (← `(tactic| apply BitVec.eq_of_getLsbD_eq))
  evalTactic (← `(tactic| idx_split))
  evalTactic (← `(tactic| all_goals (
    (try simp [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight])
    first | done | with_reducible assumption | (simp_all; done))))

/-- A goal `a = b` per bit (`kbv_bitsch`, `kbv_bitscha`), or `¬ a = b`/`False` (also a false
`a = b`) refuted by a hypothesis `¬ c = d`, proving `c = d` per bit from the others. -/
partial def bitschR : TacticM Unit := do
  evalTactic (← `(tactic| intros))
  evalTactic (← `(tactic| try subst_vars))
  let g ← getMainGoal
  let t ← g.withContext do whnfR (← instantiateMVars (← g.getType))
  if t.isAppOfArity ``Not 1 then
    evalTactic (← `(tactic| intro))
    return ← bitschR
  if ← g.withContext (isBVEq t) then
    let s ← saveState
    try evalTactic (← `(tactic| first | rfl | kbv_bitsch | kbv_bitscha)); return
    catch _ => s.restore
  evalTactic (← `(tactic| exfalso))
  let g ← getMainGoal
  let hs ← g.withContext do
    let mut hs := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let ty ← whnfR (← instantiateMVars d.type)
      if ty.isAppOfArity ``Not 1 then
        if ← isBVEq ty.appArg! then hs := hs.push d.toExpr
    pure hs
  for h in hs do
    let s ← saveState
    try
      let gs ← g.apply h
      replaceMainGoal gs
      evalTactic (← `(tactic| first | rfl | kbv_bitsch | kbv_bitscha))
      return
    catch _ => s.restore
  throwError "kbv_bitschr: no refutable hypothesis"
elab "kbv_bitschr" : tactic => bitschR

end Opt.Proof.KernelBV

macro "kbv_const" : tactic => `(tactic| (
  (try simp (disch := decide) only [Opt.Proof.KernelBV.clz_beq_zero, Opt.Proof.KernelBV.ctz_beq_zero,
    Opt.Proof.KernelBV.signExtend_allOnes] at *)
  (try simp only [BitVec.reduceSub, BitVec.reduceAdd, BitVec.reduceMul,
    BitVec.reduceOfNat, Nat.reducePow, Nat.reduceSub, Nat.reduceAdd, Nat.reduceMul, Nat.reduceMod,
    Nat.reduceDiv, Bool.cond_eq_ite, BitVec.reduceOfInt, BitVec.reduceSignExtend, BitVec.reduceZeroExtend,
    BitVec.natCast_eq_ofNat, Opt.Proof.KernelBV.select_eq_cond, Clif.Sem.ishl, Clif.Sem.ushr,
    Clif.Sem.sshr, Clif.Sem.shiftAmt, Option.some.injEq] at *)
  (try simp (disch := omega) only [BitVec.signExtend_eq_setWidth_of_le, BitVec.setWidth_and,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.reduceSetWidth, BitVec.and_assoc,
    BitVec.and_self] at *)))

macro "kbv_nat" : tactic => `(tactic| (
  (try kbv_const)
  (repeat' split) <;>
  (try simp only [BitVec.reduceOr, BitVec.reduceAnd, BitVec.reduceXOr, BitVec.reduceNot, BitVec.reduceNeg,
    BitVec.reduceAdd, BitVec.reduceSub, BitVec.reduceMul, BitVec.reduceBEq, BitVec.reduceBNe, BitVec.reduceEq,
    BitVec.reduceNe, BitVec.reduceAllOnes, BitVec.reduceSetWidth, beq_iff_eq, bne_iff_ne, Bool.not_eq_true',
    Bool.not_eq_false', beq_eq_false_iff_ne, bne_eq_false_iff_eq, Bool.not_not, Classical.not_not, ne_eq] at *) <;>
  (try simp -implicitDefEqProofs only [bitvec_to_nat, Opt.Proof.KernelBV.reduceToNatAndMask, BitVec.slt_iff_toInt_lt,
    decide_eq_false_iff_not, ← BitVec.testBit_toNat, Nat.testBit_eq_decide_div_mod_eq,
    BitVec.sle_iff_toInt_le, BitVec.toInt_eq_toNat_cond, BitVec.msb_eq_decide, BitVec.toNat_signExtend,
    BitVec.ule_eq_decide, BitVec.ult_eq_decide, BitVec.toNat_setWidth_of_le, decide_eq_true_eq,
    BitVec.slt_eq_decide, BitVec.sle_eq_decide] at *) <;>
  (try simp only [Opt.Proof.KernelBV.shiftLeft_or_toNat] at *) <;>
  (try simp (disch := decide) only [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.reducePow,
    Nat.mod_mod_of_dvd] at *) <;>
  kbv_facts <;> omega))

macro "kbv_bits" : tactic => `(tactic| (
  (try kbv_const)
  all_goals (
    apply BitVec.eq_of_getElem_eq; intro i hi
    simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_xor, BitVec.getElem_not, BitVec.getElem_zero, BitVec.getElem_allOnes]
    bool_tauto)))

macro "kbv_bitsc" : tactic => `(tactic| (
  (try kbv_const)
  all_goals (
    apply BitVec.eq_of_getLsbD_eq
    idx_split
    all_goals first
      | (simp [BitVec.msb_eq_getLsbD_last, BitVec.getElem_signExtend, BitVec.getElem_sshiftRight, BitVec.getElem_setWidth, BitVec.getElem_shiftLeft, BitVec.getElem_ushiftRight, BitVec.getElem_rotateLeft, BitVec.getElem_rotateRight]; done)
      | (simp [BitVec.msb_eq_getLsbD_last, BitVec.getElem_signExtend, BitVec.getElem_sshiftRight, BitVec.getElem_setWidth, BitVec.getElem_shiftLeft, BitVec.getElem_ushiftRight, BitVec.getElem_rotateLeft, BitVec.getElem_rotateRight]; bool_tauto))))

macro "kbv_shift" : tactic => `(tactic| (
  (try kbv_const)
  all_goals (
    simp only [BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', BitVec.sshiftRight_eq'] at *
    (try simp (disch := omega) only [Opt.Proof.KernelBV.reduceToNatAndMask, BitVec.toNat_setWidth_of_le,
      Nat.reducePow] at *)
    (try simp (disch := decide) only [BitVec.zeroExtend_eq_setWidth,
      Opt.Proof.KernelBV.toNat_signExtend_mod, Opt.Proof.KernelBV.toNat_setWidth_mod] at *)
    (try toNat_rw)
    all_goals (
      shift_split
      all_goals first | kbv_nat | kbv_bitsc))))

macro "kbv_genshift" : tactic => `(tactic| (
  (try kbv_const)
  all_goals (
    simp only [BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', BitVec.sshiftRight_eq'] at *
    (try simp (disch := omega) only [Opt.Proof.KernelBV.reduceToNatAndMask, BitVec.toNat_setWidth_of_le,
      Nat.reducePow] at *)
    (try simp (disch := decide) only [BitVec.zeroExtend_eq_setWidth,
      Opt.Proof.KernelBV.toNat_signExtend_mod, Opt.Proof.KernelBV.toNat_setWidth_mod] at *)
    (try toNat_rw)
    all_goals (
      kbv_genamt
      (try simp only [BitVec.neg_one_eq_allOnes, Opt.Proof.KernelBV.reduceLitAllOnes, BitVec.and_allOnes,
        BitVec.allOnes_and])
      first | rfl | kbv_bitsc))))

macro "kbv_modsplit" : tactic => `(tactic| (
  (try kbv_const)
  all_goals (
    (try simp only [BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', BitVec.sshiftRight_eq'] at *)
    (try simp (disch := omega) only [Opt.Proof.KernelBV.reduceAndMask, Opt.Proof.KernelBV.reduceToNatAndMask,
      BitVec.toNat_setWidth_of_le, Nat.reducePow] at *)
    (try simp (disch := decide) only [BitVec.zeroExtend_eq_setWidth, BitVec.toNat_ofNat, Nat.mod_mod_of_dvd,
      Opt.Proof.KernelBV.toNat_signExtend_mod, Opt.Proof.KernelBV.toNat_setWidth_mod] at *)
    (try toNat_rw)
    all_goals (
      mod_split
      all_goals (
        (try simp only [BitVec.reduceOfNat, BitVec.reduceSub, BitVec.reduceAdd, BitVec.reduceToNat,
          BitVec.reduceBEq, BitVec.reduceAnd, BitVec.reduceOr, Nat.reduceMod, Nat.reducePow, Nat.reduceSub,
          Nat.reduceAdd, ↓reduceIte, Bool.false_eq_true, beq_self_eq_true, BitVec.reduceShiftLeftShiftLeft] at *)
        first | rfl | kbv_bitsc | kbv_nat)))))

macro "kbv_beq" : tactic => `(tactic| (
  (try kbv_const)
  all_goals (
    apply Bool.eq_iff_iff.2
    simp only [beq_iff_eq, bne_iff_ne, ne_eq, Bool.not_eq_true', Bool.not_eq_false',
      Opt.Proof.KernelBV.cpop_eq_zero_iff, Opt.Proof.KernelBV.cpop_eq_zero_iff',
      BitVec.reverse_eq_zero_iff, Opt.Proof.KernelBV.reverse_eq_zero_iff']
    (try (simp (disch := ((try simp only [BitVec.toNat_sub, BitVec.toNat_ofNat,
        Opt.Proof.KernelBV.reduceToNatAndMask, Nat.reducePow, Nat.reduceMod]); omega)) only
      [BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', Opt.Proof.KernelBV.shl_or_shr_eq_zero_iff,
        Opt.Proof.KernelBV.shr_or_shl_eq_zero_iff]; done))
    all_goals (constructor <;> kbv_bitschr))))

/-- Comparisons through sign extensions: each `==`/`slt`/`sle` as one of the `toInt`s, a sign
extension's `toInt` as the operand's. -/
macro "kbv_sext" : tactic => `(tactic| (
  intros
  (try subst_vars)
  simp (disch := decide) only [Opt.Proof.KernelBV.beq_eq_decide_toInt, bne, BitVec.slt_eq_decide,
    BitVec.sle_eq_decide, BitVec.toInt_signExtend_of_le, BitVec.toInt_zero, Opt.Proof.KernelBV.toInt_zero'] at *
  done))

/-- Shift amounts as `toNat`s, masks `x &&& (2^k - 1)` as `% 2^k`, through zero and sign
extensions. -/
macro "kbv_amt_norm" : tactic => `(tactic| (
  (try simp only [BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', BitVec.sshiftRight_eq'] at *)
  (try simp (disch := omega) only [Opt.Proof.KernelBV.reduceAndMask, Opt.Proof.KernelBV.reduceToNatAndMask,
    BitVec.toNat_setWidth_of_le, Nat.reducePow] at *)
  (try simp (disch := decide) only [BitVec.zeroExtend_eq_setWidth, BitVec.toNat_ofNat, Nat.mod_mod_of_dvd,
    Opt.Proof.KernelBV.mod_mod_of_le, Opt.Proof.KernelBV.toNat_signExtend_mod,
    Opt.Proof.KernelBV.toNat_setWidth_mod] at *)))

/-- `omega` on the `toNat`s of bit vectors (masks as `% 2^k`), for side conditions on shift
amounts. -/
macro "kbv_amt_omega" : tactic => `(tactic| (
  (try simp (disch := decide) only [Opt.Proof.KernelBV.reduceToNatAndMask, BitVec.zeroExtend_eq_setWidth,
    Opt.Proof.KernelBV.toNat_signExtend_mod, Opt.Proof.KernelBV.toNat_setWidth_mod] at *)
  bv_omega))

/-- Rotations written with shifts as `rotateLeft`/`rotateRight` (amounts normalized, `m = w - k`
by `omega`), a rotation undone by the opposite one, then `rfl` or per bit. -/
macro "kbv_rot" : tactic => `(tactic| (
  (try kbv_const)
  all_goals (
    kbv_amt_norm
    simp (disch := kbv_amt_omega) only [Opt.Proof.KernelBV.shl_or_shr_eq_rotateLeft,
      Opt.Proof.KernelBV.shr_or_shl_eq_rotateRight] at *
    (try subst_vars)
    (try simp (disch := omega) only [Opt.Proof.KernelBV.rotateLeft_rotateRight_of_lt,
      Opt.Proof.KernelBV.rotateRight_rotateLeft_of_lt] at *)
    all_goals first | rfl | kbv_bitsc)))

/-- `kbv_modsplit` up to 128 cases, with the case equation `t % n = k` as a hypothesis (it
refutes impossible cases), the other amounts `t' % n'` evaluated by `omega` (`amt_eval`), a
second split where one is left. -/
macro "kbv_modsplit2" : tactic => `(tactic| (
  (try kbv_const)
  all_goals (
    kbv_amt_norm
    (try toNat_rw)
    all_goals (
      mod_split2
      all_goals (
        intro
        (try amt_eval)
        (try simp only [BitVec.reduceOfNat, BitVec.reduceSub, BitVec.reduceAdd, BitVec.reduceToNat,
          BitVec.reduceBEq, BitVec.reduceAnd, BitVec.reduceOr, Nat.reduceMod, Nat.reducePow, Nat.reduceSub,
          Nat.reduceAdd, ↓reduceIte, Bool.false_eq_true, beq_self_eq_true, BitVec.reduceShiftLeftShiftLeft] at *)
        first
        | rfl | kbv_bitsc | kbv_nat | kbv_beq
        | (mod_split2
           all_goals (
             intro
             (try amt_eval)
             (try simp only [BitVec.reduceOfNat, BitVec.reduceSub, BitVec.reduceAdd, BitVec.reduceToNat,
               BitVec.reduceBEq, BitVec.reduceAnd, BitVec.reduceOr, Nat.reduceMod, Nat.reducePow,
               Nat.reduceSub, Nat.reduceAdd, ↓reduceIte, Bool.false_eq_true, beq_self_eq_true,
               BitVec.reduceShiftLeftShiftLeft] at *)
             first | rfl | kbv_bitsc | kbv_nat)))))))

macro "kbv_bitsh" : tactic => `(tactic| (
  (try kbv_const)
  (repeat' split) <;> (try simp only [beq_iff_eq, bne_iff_ne, ne_eq, Bool.not_eq_true, Bool.not_eq_false,
     decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true', Bool.not_eq_false', beq_eq_false_iff_ne,
     bne_eq_false_iff_eq, Bool.not_not, Classical.not_not] at *) <;>
  first | rfl | bits_hyps))

/-- Sign masks, also of a logical shift right by `w - 1`. -/
macro "kbv_signmask" : tactic => `(tactic| (
  (try kbv_const)
  all_goals (
    simp (disch := decide) only [BitVec.sshiftRight', BitVec.ushiftRight_eq', BitVec.reduceAnd,
      BitVec.reduceToNat, Opt.Proof.KernelBV.sshiftRight_pred_width,
      Opt.Proof.KernelBV.ushiftRight_pred_width] at *
    first | rfl | kbv_bitsh)))

namespace Opt.Proof.KernelBV
open Lean Meta Elab Tactic
def bitwiseHead? (e : Expr) : Option Name :=
  if e.isAppOfArity ``HAnd.hAnd 6 then some ``HAnd.hAnd
  else if e.isAppOfArity ``HOr.hOr 6 then some ``HOr.hOr
  else if e.isAppOfArity ``HXor.hXor 6 then some ``HXor.hXor
  else if e.isAppOfArity ``Complement.complement 3 then some ``Complement.complement
  else none

/-- Leaves of a bitwise term. -/
partial def bwLeaves (e : Expr) (acc : Array Expr) : Array Expr :=
  match bitwiseHead? e with
  | some ``Complement.complement => bwLeaves e.appArg! acc
  | some _ => bwLeaves e.appArg! (bwLeaves e.appFn!.appArg! acc)
  | _ => if acc.contains e then acc else acc.push e

/-- Evaluate a bitwise term under an assignment of its leaves. -/
partial def bwEval (e : Expr) (leaves : Array Expr) (asg : Nat) : Bool :=
  match bitwiseHead? e with
  | some ``Complement.complement => !bwEval e.appArg! leaves asg
  | some ``HAnd.hAnd => bwEval e.appFn!.appArg! leaves asg && bwEval e.appArg! leaves asg
  | some ``HOr.hOr => bwEval e.appFn!.appArg! leaves asg || bwEval e.appArg! leaves asg
  | some ``HXor.hXor => xor (bwEval e.appFn!.appArg! leaves asg) (bwEval e.appArg! leaves asg)
  | _ => match leaves.idxOf? e with
    | some i => asg.testBit i
    | none => false

/-- Maximal bitwise subterms of `e` (of bit-vector type `BitVec w`). -/
partial def bwMax (e : Expr) (acc : Array Expr) : Array Expr :=
  if e.hasLooseBVars then acc else
  match bitwiseHead? e with
  | some _ => if acc.contains e then acc else acc.push e
  | none => match e with
    | .app f a => bwMax a (bwMax f acc)
    | _ => acc

def mintermCore (g : MVarId) : TacticM MVarId := g.withContext do
  let t ← instantiateMVars (← g.getType)
  let some (ty, l, r) := t.eq? | throwError "kbv_minterm: not an equation"
  let ty ← whnfR ty
  unless ty.isAppOfArity ``BitVec 1 do throwError "kbv_minterm: not bit vectors"
  let bws := bwMax r (bwMax l #[])
  if bws.isEmpty then throwError "kbv_minterm: no bitwise term"
  let leaves := bws.foldl (fun acc b => bwLeaves b acc) #[]
  let leaves := leaves.filter fun e => e.nat?.isNone
  if leaves.size > 3 then throwError "kbv_minterm: {leaves.size} leaves"
  let n := leaves.size
  -- minterm `S` (bitmask over leaves)
  let minterm (S : Nat) : MetaM Expr := do
    let mut m : Option Expr := none
    for i in [0:n] do
      let lit ← if S.testBit i then pure leaves[i]! else mkAppM ``Complement.complement #[leaves[i]!]
      m := some (← match m with | none => pure lit | some m0 => mkAppM ``HAnd.hAnd #[m0, lit])
    return m.get!
  let zero ← mkAppOptM ``BitVec.ofNat #[ty.appArg!, mkNatLit 0]
  let sumOf (ms : Array Nat) : MetaM Expr := do
    let mut s : Option Expr := none
    for S in ms do
      let m ← minterm S
      s := some (← match s with | none => pure m | some s0 => mkAppM ``HAdd.hAdd #[s0, m])
    return s.getD zero
  -- equalities `b = Σ` for the bitwise terms and the leaves
  let mut g := g
  let mut eqs := #[]
  for b in bws ++ leaves do
    let ms := (List.range (2 ^ n)).toArray.filter fun S => bwEval b leaves S
    let sum ← sumOf ms
    let eq ← mkEq sum b
    let pf ← mkFreshExprSyntheticOpaqueMVar eq
    let gs ← Tactic.run pf.mvarId! (evalTactic (← `(tactic| (
      (try simp (disch := kbv_guard kbv_bits) only [Opt.Proof.KernelBV.add_disj]) <;> kbv_bits))))
    unless gs.isEmpty do throwError "kbv_minterm: decomposition failed"
    eqs := eqs.push (b, ← instantiateMVars pf)
  -- rewrite the bitwise terms (maximal first), then generalize minterms, then the leaves
  for (_, pf) in eqs.extract 0 bws.size do
    let r ← g.rewrite (← g.getType) (← mkEqSymm pf)
    g ← g.replaceTargetEq r.eNew r.eqProof
  -- generalize minterms
  let mts ← (List.range (2 ^ n)).toArray.mapM fun S => (minterm S : MetaM Expr)
  let mut hyps := #[]
  for (_, pf) in eqs.extract bws.size eqs.size do
    hyps := hyps.push (← mkEqSymm pf)
  let (hfv, g') ← g.assertHypotheses (← hyps.mapM fun h => do return { userName := `hl, type := ← inferType h, value := h })
  g := g'
  let args := mts.map fun m => ({ expr := m } : GeneralizeArg)
  let (_, _, g'') ← g.withContext <| g.generalizeHyp args hfv
  return g''

elab "kbv_minterm" : tactic => do
  let g ← mintermCore (← getMainGoal)
  replaceMainGoal [g]
  evalTactic (← `(tactic| ((try simp only [*]) <;> grind)))

end Opt.Proof.KernelBV

macro "kbv_core" : tactic => `(tactic| (
  intros
  (try simp only [Option.some.injEq] at *)
  (try simp (disch := decide) only [Opt.Proof.KernelBV.setWidth_eq_iff_toNat, BitVec.toNat_inj] at *)
  (try subst_vars)
  first
  | (kbv_guard (bv_normalize; done))
  | kbv_guard kbv_bits
  | kbv_guard kbv_bitsh
  | kbv_guard kbv_nat
  | kbv_guard kbv_sext
  | kbv_guard 100000 ((try kbv_const); all_goals (kbv_split; all_goals first
      | rfl | kbv_guard kbv_nat | kbv_guard kbv_bitsh | kbv_guard kbv_bits | kbv_guard kbv_bitsc))
  | kbv_guard ((try kbv_const); simp (disch := decide) only [BitVec.sshiftRight', BitVec.reduceAnd,
      BitVec.reduceToNat, Opt.Proof.KernelBV.sshiftRight_pred_width, Opt.Proof.KernelBV.msb_or_neg,
      Opt.Proof.KernelBV.msb_neg_or] at *; first | rfl | kbv_bitsh)
  | kbv_guard 100000 kbv_genshift
  | kbv_guard 100000 kbv_shift
  | kbv_guard 400000 kbv_modsplit
  | kbv_guard 400000 kbv_beq
  | kbv_guard 100000 ((try kbv_const); all_goals kbv_bitsch)
  | kbv_guard (intros; (try simp only [BitVec.shiftLeft_eq', BitVec.reduceAnd, BitVec.reduceToNat,
      Opt.Proof.KernelBV.shiftLeft_eq_mul_ofNat, Nat.reducePow] at *); kbv_minterm)
  | kbv_guard (simp only [BitVec.not_eq_neg_add]; grind)
  | kbv_guard (set_option maxHeartbeats 200000 in grind)
  | kbv_guard 400000 kbv_bitsc
  | kbv_guard kbv_signmask
  | kbv_guard 100000 kbv_rot
  | kbv_guard 2000000 kbv_modsplit2
  ))

namespace Opt.Proof.KernelBV
open Lean Meta Elab Tactic

register_option kbv.reportHeartbeats : Nat := {
  defValue := 0
  descr := "if positive, print every `kbv` search that used at least this many thousand \
    heartbeats to standard error, with its position, declaration and outcome (the searches run \
    on their own budget, so their cost is not counted in the declaration's `maxHeartbeats`)"
}

/-- Heartbeat budget (raw) of a whole `kbv` search, times `kbv.budgetScale`: above the sum of its
methods' budgets in `kbv_core` (`kbv_guard`). -/
def searchHeartbeats : Nat := 4000000 * 1000

def isAtomTy (ty : Expr) : MetaM Bool := do
  let ty ← instantiateMVars ty
  return ty.isAppOfArity ``BitVec 1 || ty.isConstOf ``Bool || ty.isConstOf ``Nat || ty.isConstOf ``Int

/-- Closed `Nat` subterms that evaluate to a literal (`Ty.width .i8`, also inside instance
arguments, where `simp` lemmas would not see through them), as that literal. -/
def normNat (e : Expr) : MetaM Expr :=
  Meta.transform e (pre := fun e => do
    if e.hasLooseBVars || e.hasFVar || e.hasMVar || e.isRawNatLit || e.nat?.isSome then
      return .continue
    unless e.isApp || e.isConst do return .continue
    let ty ← (try inferType e catch _ => pure (mkConst ``Unit))
    unless ty.isConstOf ``Nat do return .continue
    let e' ← whnf e
    match e'.rawNatLit? <|> e'.nat? with
    | some k => return .done (mkNatLit k)
    | none => return .continue)

/-- The main goal restated over its bit-vector context only (the bit-vector, `Bool`, `Nat`, `Int`
locals, the propositions over them, the equations and comparisons at those types and their locals,
and the locals the goal depends on), with the locals it abstracts. -/
def bvStatement (g : MVarId) : MetaM (Expr × Array Expr) :=
  g.withContext do
    let tgt ← instantiateMVars (← g.getType)
    let lctx ← getLCtx
    let mut keep : FVarIdSet := {}
    for d in lctx do
      if d.isImplementationDetail then continue
      if ← isAtomTy d.type then keep := keep.insert d.fvarId
    for f in (collectFVars {} tgt).fvarIds do keep := keep.insert f
    -- the locals of the (negated) equations and comparisons at the atom types (`v.bits = x`,
    -- with `v` a `Val`: `v.bits` is an atom)
    for d in lctx do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      if ty.hasMVar || !(← isProp ty) then continue
      let ty' := if ty.isAppOfArity ``Not 1 then ty.appArg! else ty
      let α? := if ty'.isAppOfArity ``Eq 3 then some (ty'.getArg! 0)
        else if ty'.isAppOfArity ``LT.lt 4 || ty'.isAppOfArity ``LE.le 4 then some (ty'.getArg! 0)
        else none
      let some α := α? | continue
      if ← isAtomTy (← whnfR α) then
        for f in (collectFVars {} ty).fvarIds do keep := keep.insert f
    let mut changed := true
    while changed do
      changed := false
      for f in keep do
        let d ← f.getDecl
        let mut fs := (collectFVars {} (← instantiateMVars d.type)).fvarIds
        if let some v := d.value? then fs := fs ++ (collectFVars {} (← instantiateMVars v)).fvarIds
        for f' in fs do
          unless keep.contains f' do
            keep := keep.insert f'
            changed := true
    let mut sel : Array Expr := #[]
    for d in lctx do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      if keep.contains d.fvarId then
        sel := sel.push d.toExpr
      else if (← isProp ty) && !ty.hasMVar then
        let fs := (collectFVars {} ty).fvarIds
        if !fs.isEmpty && fs.all keep.contains then sel := sel.push d.toExpr
    return (← normNat (← mkForallFVars sel tgt), sel)

/-- Prove the main goal's `bvStatement` by `tac` in an empty context, and apply it. -/
def isolate (tac : TacticM Unit) : TacticM Unit := do
  let g ← getMainGoal
  let (stmt, sel) ← bvStatement g
  let m ← mkFreshExprMVarAt {} {} stmt .syntheticOpaque
  -- The search runs under its own budget and is not charged to the enclosing declaration; the
  -- kernel still checks the proof. No info trees are recorded for it: a rule proof can run
  -- thousands of searches, whose info trees (tens of MB each) would otherwise be kept until the
  -- end of the declaration. Error recovery is off: a failing method fails (instead of logging
  -- its error and admitting the goal), so that the search goes on with the next one.
  -- `kbv.reportHeartbeats`: the cost of the search, printed (not logged: a `first` that backtracks
  -- over a failed alternative also drops its messages) before the counter is reset.
  let threshold := kbv.reportHeartbeats.get (← getOptions) * 1000
  let report (outcome : String) (used : Nat) : TacticM Unit := do
    if threshold > 0 && used ≥ threshold then
      let pos := (← getFileMap).toPosition ((← getRef).getPos?.getD 0)
      let decl := (← Term.getDeclName?).getD .anonymous
      IO.eprintln s!"kbv: {← getFileName}:{pos.line}:{pos.column}: {decl}: {outcome}, \
        {used / 1000} thousand heartbeats"
  let hb0 ← IO.getNumHeartbeats
  let gs ← tryCatchRuntimeEx
      (withTheReader Core.Context (fun ctx => { ctx with
          maxHeartbeats := searchHeartbeats * kbv.budgetScale.get ctx.options }) <|
        withCurrHeartbeats <| withEnableInfoTree false <| Tactic.run m.mvarId! (withoutRecover tac))
      fun e => do
        let used := (← IO.getNumHeartbeats) - hb0
        IO.setNumHeartbeats hb0
        report "failed" used
        throw e
  let used := (← IO.getNumHeartbeats) - hb0
  IO.setNumHeartbeats hb0
  report (if gs.isEmpty then "closed" else "failed (unsolved goals)") used
  unless gs.isEmpty do throwError "kbv: unsolved goals"
  g.assign (mkAppN (← instantiateMVars m) sel)
  replaceMainGoal []

end Opt.Proof.KernelBV

open Lean Elab Tactic in
/-- Close a bit-vector goal by kernel-checked proof search (`kbv_core`), on the goal restated over
its bit-vector context only (`Opt.Proof.KernelBV.isolate`). -/
elab "kbv" : tactic => Opt.Proof.KernelBV.isolate (do evalTactic (← `(tactic| kbv_core)))

