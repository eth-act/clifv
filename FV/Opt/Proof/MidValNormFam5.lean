import FV.Opt.Proof.MidValNormFam4

/-!
# Family 5 is a sound normaliser under typing (#1119 stage 2, agent MidendNext3)

Three shapes of the `rewrite:operand` tail (#1119 issuecomment-7165335641), after Cranelift
0.135.0's `opts/arithmetic.isle` and `opts/extends.isle`, each proved against `Clif.evalInst`:

* `addNeg` — `iadd ty a (ineg ty y)` is `isub ty a y`, and `iadd ty (ineg ty y) b` is
  `isub ty b y` (`x + (-y) = x - y`); no typing: both sides read the same operands at `ty`;
* `mulNeg` — `imul ty (ineg ty x) k` with `k` a constant is `imul ty x (-k)` (`(-x) * k =
  x * (-k)`); no typing;
* `redRed` (typed) — `ireduce ty (ireduce ty2 x)` with `x` of static type `xt` (`tyAt`), `ty`
  narrower than `ty2` narrower than `xt`, is `ireduce ty x`: truncating twice is truncating once
  (`BitVec.setWidth_setWidth_of_le`); for an `x` of another width the two sides differ (the inner
  `ireduce` has no value for an `x` no wider than `ty2`), hence the typing.

None of them drops an operand, so a side has a value exactly when the other has one. (Rules that
drop one, `(x + y) - x = y` or `x * 0 = 0`, are false as `NormSoundT` rules: in a frame where `x`
has no value the node has none, the result has one.)

Main results: `ns_addNeg`, `ns_mulNeg`, `ruleSoundT_redRed`, `ruleSoundT_fam5Step`.
`normSoundT_base`, `normSoundT_narrowN` and `normSoundT_stdT` (the validator's default
normaliser, which now starts and ends with family 6) are in `FV/Opt/Proof/MidValNormFam6.lean`.
-/

namespace Opt.MidVal

open Clif

/-! ## `addNeg` -/

/-- The value of `u = ineg ty y` (a node whose operands are earlier) read at `ty`. -/
theorem regs_ineg {f : Function} {tms : Array Tm} {fr : Frame} {mem : Mem} {u y : Nat} {ty : Ty}
    (hn : nodeAt tms u = some (.unary .ineg ty y)) :
    ((tmFrame f tms fr mem).regs u).bind (·.as? ty) =
      (((tmFrame f tms fr mem).regs y).bind (·.as? ty)).map fun B => -B := by
  have : (tmFrame f tms fr mem).regs u = (((tmFrame f tms fr mem).regs y).bind (·.as? ty)).map
      fun B => ⟨ty, -B⟩ := by
    show tmVal f tms fr mem u = _
    rw [tmVal_node (nodeAt_spec hn).1 (nodeAt_spec hn).2, evalNode_unary]
    rfl
  rw [this]
  exact bind_as_map _ _

theorem addNeg_spec {tms : Array Tm} {ty : Ty} {a b : Nat} {x' : Tm}
    (h : addNeg tms ty a b = some x') :
    (∃ y, nodeAt tms b = some (.unary .ineg ty y) ∧ x' = .node (.binary .isub ty a y)) ∨
      (∃ y, nodeAt tms a = some (.unary .ineg ty y) ∧ x' = .node (.binary .isub ty b y)) := by
  unfold addNeg at h
  split at h
  · rename_i ty' y hb
    split at h
    · rename_i he
      simp only [beq_iff_eq] at he
      subst he
      cases h
      exact .inl ⟨y, hb, rfl⟩
    · cases h
  · split at h
    · rename_i ty' y ha
      split at h
      · rename_i he
        simp only [beq_iff_eq] at he
        subst he
        cases h
        exact .inr ⟨y, ha, rfl⟩
      · cases h
    · cases h

/-- **`x + (-y)` is `x - y`**, either order. -/
theorem ns_addNeg {tms : Array Tm} {ty : Ty} {a b : Nat} :
    NodeSound tms (.binary .iadd ty a b) (addNeg tms ty a b) := by
  intro x' h hord f fr mem t ht
  rcases addNeg_spec h with ⟨y, hb, rfl⟩ | ⟨y, ha, rfl⟩
  · rw [tmVal_res ht hord, evalNode_binary_nonShift (op := .isub) rfl,
      evalNode_binary_nonShift (op := .iadd) rfl, regs_ineg hb]
    rcases ((tmFrame f tms fr mem).regs a).bind (·.as? ty) with _ | A <;>
      rcases ((tmFrame f tms fr mem).regs y).bind (·.as? ty) with _ | B <;>
      simp [Sem.binary, Sem.iadd, Sem.isub, BitVec.sub_eq_add_neg]
  · rw [tmVal_res ht hord, evalNode_binary_nonShift (op := .isub) rfl,
      evalNode_binary_nonShift (op := .iadd) rfl, regs_ineg ha]
    rcases ((tmFrame f tms fr mem).regs b).bind (·.as? ty) with _ | B <;>
      rcases ((tmFrame f tms fr mem).regs y).bind (·.as? ty) with _ | Y <;>
      simp [Sem.binary, Sem.iadd, Sem.isub, BitVec.sub_eq_add_neg, BitVec.add_comm]

/-! ## `mulNeg` -/

theorem mulNegPlan_spec {tms : Array Tm} {ty : Ty} {a b x : Nat} {k : BitVec ty.width}
    (h : mulNegPlan tms ty a b = some (x, k)) :
    ∃ k0, nodeAt tms a = some (.unary .ineg ty x) ∧ constAt tms ty b = some k0 ∧ k = -k0 := by
  unfold mulNegPlan at h
  split at h
  · rename_i ty' x0 k0 ha hb
    split at h
    · rename_i he
      simp only [beq_iff_eq] at he
      subst he
      cases h
      exact ⟨k0, ha, hb, rfl⟩
    · cases h
  · cases h

/-- **`(-x) * k` is `x * (-k)`.** -/
theorem ns_mulNeg {tms : Array Tm} {ty : Ty} {a b : Nat} :
    NodeSound tms (.binary .imul ty a b) (mulNeg tms ty a b) := by
  intro x' h hord f fr mem t ht
  unfold mulNeg at h
  obtain ⟨⟨x, k⟩, hp, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨kc, hkc, rfl⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨hk1, hk2⟩ := findTm_spec hkc
  have hK : (tmFrame f tms fr mem).regs kc = some ⟨ty, k⟩ := by
    show tmVal f tms fr mem kc = _
    rw [tmVal_node hk1 hk2]
    rfl
  obtain ⟨k0, ha, hb, rfl⟩ := mulNegPlan_spec hp
  have hb' : (tmFrame f tms fr mem).regs b = some ⟨ty, k0⟩ := constAt_spec hb
  rw [tmVal_res ht hord, evalNode_binary_nonShift (op := .imul) rfl,
    evalNode_binary_nonShift (op := .imul) rfl, hK, hb', regs_ineg ha]
  rcases ((tmFrame f tms fr mem).regs x).bind (·.as? ty) with _ | X <;>
    simp [Sem.binary, Sem.imul]

/-! ## `redRed` -/

theorem redRed_spec {aty : Tm → Option Ty} {tms : Array Tm} {ty : Ty} {u : Nat} {x' : Tm}
    (h : redRed aty tms ty u = some x') :
    ∃ ty2 x xt, nodeAt tms u = some (.ireduce ty2 x) ∧ tyAt aty tms x = some xt ∧
      ty.width < ty2.width ∧ ty2.width < xt.width ∧ x' = .node (.ireduce ty x) := by
  unfold redRed at h
  split at h
  · rename_i ty2 x hu
    split at h
    · rename_i xt hx
      split at h
      · rename_i hc
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        cases h
        exact ⟨ty2, x, xt, hu, hx, hc.1, hc.2, rfl⟩
      · cases h
    · cases h
  · cases h

/-- **`ireduce` of an `ireduce` of a wider typed term is one `ireduce`** (typed). -/
theorem ruleSoundT_redRed {f : Function} {tms : Array Tm} {ty : Ty} {u : Nat} {x' : Tm}
    (h : redRed (atomTy f) tms ty u = some x')
    (hord : ∀ t, tms[t]? = some x' → ∀ o ∈ x'.ops, o < t) {fr : Frame} {mem : Mem} {t : Nat}
    (ht : tms[t]? = some x') (hA : AtomsTyped f tms fr mem (.ireduce ty u)) :
    tmVal f tms fr mem t = evalNode (tmFrame f tms fr mem) mem (.ireduce ty u) := by
  obtain ⟨ty2, x, xt, hu, hx, h1, h2, rfl⟩ := redRed_spec h
  have hna := nodeAt_spec hu
  have huv : (tmFrame f tms fr mem).regs u =
      evalNode (tmFrame f tms fr mem) mem (.ireduce ty2 x) := tmVal_node hna.1 hna.2
  have hru : TmReach tms (.ireduce ty u) u := .op (by simp [operands])
  have hrx : TmReach tms (.ireduce ty u) x := .sub hru hna.1 (by simp [operands])
  rw [tmVal_node ht (hord t ht), evalNode_ireduce, evalNode_ireduce, huv, evalNode_ireduce]
  rcases hv : (tmFrame f tms fr mem).regs x with _ | v
  · simp
  · have hvt : v.ty = xt := tyAt_val hA hrx hx hv
    obtain ⟨vt, vb⟩ := v
    simp only at hvt
    subst hvt
    simp [h1, h2, Nat.lt_trans h1 h2, BitVec.setWidth_setWidth_of_le _ (Nat.le_of_lt h1)]

/-! ## The family -/

/-- **Family 5 is sound under typing.** -/
theorem ruleSoundT_fam5Step {f : Function} : RuleSoundT f (fam5Step (atomTy f)) := by
  intro tms i x' h hord fr mem t ht hA
  cases i with
  | binary op ty a b =>
    cases op
    case iadd => exact ns_addNeg x' h hord f fr mem t ht
    case imul => exact ns_mulNeg x' h hord f fr mem t ht
    all_goals simp [fam5Step] at h
  | ireduce ty u => exact ruleSoundT_redRed h hord ht hA
  | _ => simp [fam5Step] at h

end Opt.MidVal
