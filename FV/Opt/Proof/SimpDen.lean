import FV.Opt.Proof.GvnEdit

/-!
# The graph valuation of the simplify pass (`Opt.den`)

The e-graph of `Opt.simplify` is a map `D` from values to pure nodes. Given values `ρ` for its
leaves (block parameters and skeleton results), `Opt.den D ρ fr mem` is the least valuation
that satisfies every node equation `x = evalNode n` (`den_node`) and agrees with `ρ` on the
leaves (`den_leaf`); cycles simply stay undefined. It is the `den` of the rule obligations
`Opt.SimplifySound`/`Opt.SkeletonSound` in the pass proof (`FV/Opt/Proof/SimpGraph.lean`).

* `evalInst_ops`, `evalInst_mono`, `evalNode_mono`: an instruction that does not get stuck has
  read all its operands, so it evaluates the same in larger registers.
* `den_le_of`: `den` is below every pre-model.
* `den_insert_fresh`: adding the node of a new value keeps `den` on the values whose nodes are
  closed under operands (the graph only grows by such insertions).
* `Twin`, `den_twin`, `den_overwrite`: a node replaced by a copy over equal-valued operands
  (`materialize`'s clones) keeps `den`.
-/

namespace Opt

open Clif

theorem ite_eq_iff' {α : Type} {c : Prop} [Decidable c] {a b x : α} :
    ((if c then a else b) = x) ↔ (c ∧ a = x) ∨ (¬c ∧ b = x) := by
  split <;> simp_all

/-! ## Monotonicity of evaluation in the registers -/

/-- An instruction that does not get stuck has read all its operands. -/
theorem evalInst_ops {fr : Frame} {mem : Mem} {i : Inst}
    (h : ∀ m, evalInst fr mem i ≠ .stuck m) : ∀ x ∈ operands i, ∃ a, fr.regs x = some a := by
  cases he : evalInst fr mem i with
  | stuck m => exact absurd he (h m)
  | ok r =>
    cases i <;> simp only [evalInst, Frame.getAs, Frame.get, Res.bind_eq_ok, Res.ofOption_eq_ok,
      Res.pure_eq_ok, ite_eq_iff'] at he <;> simp only [operands, List.mem_cons, or_false,
      forall_eq_or_imp, forall_eq, List.not_mem_nil, false_imp_iff, imp_true_iff]
    all_goals grind
  | trap c =>
    cases i <;> simp only [evalInst, Frame.getAs, Frame.get, Res.bind_eq_ok, Res.ofOption_eq_ok,
      Res.pure_eq_ok, Res.bind_eq_trap, Res.ofOption_ne_trap, Res.check_ne_trap, Res.pure_ne_trap,
      ite_eq_iff'] at he <;> simp only [operands, List.mem_cons, or_false,
      forall_eq_or_imp, forall_eq, List.not_mem_nil, false_imp_iff, imp_true_iff]
    all_goals grind

theorem evalInst_mono {fr fr' : Frame} {mem : Mem} {i : Inst}
    (hg : fr'.func.globals = fr.func.globals) (hx : fr'.func.externs = fr.func.externs)
    (hs : fr'.slots = fr.slots)
    (hle : Valuation.Le fr.regs fr'.regs) (h : ∀ m, evalInst fr mem i ≠ .stuck m) :
    evalInst fr' mem i = evalInst fr mem i := by
  apply evalInst_congr hg hx hs
  intro x hx
  obtain ⟨a, ha⟩ := evalInst_ops h x hx
  rw [ha, hle x a ha]

theorem evalNode_ok {fr : Frame} {mem : Mem} {n : Inst} {a : Val}
    (h : evalNode fr mem n = some a) : ∀ m, evalInst fr mem n ≠ .stuck m := by
  intro m hm; simp [evalNode, hm] at h

theorem evalNode_mono {fr fr' : Frame} {mem : Mem} {n : Inst} {a : Val}
    (hg : fr'.func.globals = fr.func.globals) (hx : fr'.func.externs = fr.func.externs)
    (hs : fr'.slots = fr.slots)
    (hle : Valuation.Le fr.regs fr'.regs) (h : evalNode fr mem n = some a) :
    evalNode fr' mem n = some a := by
  simpa [evalNode, evalInst_mono hg hx hs hle (evalNode_ok h)] using h

/-- Registers `R` in the frame `fr`. -/
abbrev withRegs (fr : Frame) (R : Valuation) : Frame := { fr with regs := R }

theorem evalNode_withRegs_mono {fr : Frame} {mem : Mem} {n : Inst} {R R' : Valuation} {a : Val}
    (hle : Valuation.Le R R') (h : evalNode (withRegs fr R) mem n = some a) :
    evalNode (withRegs fr R') mem n = some a :=
  evalNode_mono (fr := withRegs fr R) (fr' := withRegs fr R') rfl rfl rfl hle h

/-- Registers that agree with `R` on the operands of `n` can be found at a finite level of an
increasing chain whose limit is `R`. -/
theorem exists_level {E : Nat → Valuation} (hmono : ∀ k, Valuation.Le (E k) (E (k + 1)))
    {R : Valuation} (hR : ∀ x a, R x = some a → ∃ k, E k x = some a) (l : List ValueId)
    (hl : ∀ y ∈ l, ∃ a, R y = some a) : ∃ K, ∀ y ∈ l, E K y = R y := by
  have hle : ∀ k k', k ≤ k' → Valuation.Le (E k) (E k') := by
    intro k k' h
    induction h with
    | refl => exact fun _ _ h => h
    | step _ ih => exact fun x a h => hmono _ x a (ih x a h)
  induction l with
  | nil => exact ⟨0, by simp⟩
  | cons y ys ih =>
    obtain ⟨K1, hK1⟩ := ih (fun z hz => hl z (by simp [hz]))
    obtain ⟨a, ha⟩ := hl y (by simp)
    obtain ⟨K2, hK2⟩ := hR y a ha
    refine ⟨max K1 K2, fun z hz => ?_⟩
    simp only [List.mem_cons] at hz
    rcases hz with rfl | hz
    · rw [ha]; exact hle K2 _ (Nat.le_max_right _ _) _ _ hK2
    · obtain ⟨b, hb⟩ := hl z (by simp [hz])
      have h1 : E K1 z = some b := by rw [hK1 z hz]; exact hb
      rw [hb]
      exact hle K1 _ (Nat.le_max_left _ _) _ _ h1

/-! ## The least valuation of a graph -/

section Den

variable (D : ValueId → Option Inst) (ρ : Valuation) (fr : Frame) (mem : Mem)

/-- Evaluation of the graph to depth `k`. -/
def evalTree : Nat → Valuation
  | 0 => fun _ => none
  | k + 1 => fun x => match D x with
    | none => ρ x
    | some n => evalNode (withRegs fr (evalTree k)) mem n

open Classical in
/-- The least valuation satisfying the node equations of `D`, with leaves `ρ` (module doc). -/
noncomputable def den : Valuation := fun x =>
  if h : ∃ k, (evalTree D ρ fr mem k x).isSome then evalTree D ρ fr mem (Classical.choose h) x
  else none

variable {D ρ fr mem}

theorem evalTree_succ_mono (k : Nat) :
    Valuation.Le (evalTree D ρ fr mem k) (evalTree D ρ fr mem (k + 1)) := by
  induction k with
  | zero => intro x a h; simp [evalTree] at h
  | succ k ih =>
    intro x a h
    simp only [evalTree] at h ⊢
    cases hx : D x with
    | none => simp only [hx] at h ⊢; exact h
    | some n => simp only [hx] at h ⊢; exact evalNode_withRegs_mono ih h

theorem evalTree_le {k k' : Nat} (h : k ≤ k') :
    Valuation.Le (evalTree D ρ fr mem k) (evalTree D ρ fr mem k') := by
  induction h with
  | refl => exact fun _ _ h => h
  | step _ ih => exact fun x a h => evalTree_succ_mono _ x a (ih x a h)

theorem den_of_level {k : Nat} {x : ValueId} {a : Val} (h : evalTree D ρ fr mem k x = some a) :
    den D ρ fr mem x = some a := by
  have hex : ∃ k, (evalTree D ρ fr mem k x).isSome := ⟨k, by simp [h]⟩
  rw [den, dite_eq_left_of_eq_true (eq_true hex)]
  have hc := Classical.choose_spec hex
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hc
  rw [hb]
  rcases Nat.le_total k (Classical.choose hex) with hk | hk
  · have := evalTree_le hk x a h; rw [hb] at this; exact this
  · have := evalTree_le hk x b hb; rw [h] at this; exact this.symm

theorem level_of_den {x : ValueId} {a : Val} (h : den D ρ fr mem x = some a) :
    ∃ k, evalTree D ρ fr mem k x = some a := by
  rw [den] at h
  split at h
  · exact ⟨_, h⟩
  · cases h

theorem den_leaf {x : ValueId} (hx : D x = none) : den D ρ fr mem x = ρ x := by
  cases hρ : ρ x with
  | some a => exact den_of_level (k := 1) (by simp [evalTree, hx, hρ])
  | none =>
    cases hd : den D ρ fr mem x with
    | none => rfl
    | some a =>
      obtain ⟨k, hk⟩ := level_of_den hd
      cases k with
      | zero => simp [evalTree] at hk
      | succ k => simp [evalTree, hx, hρ] at hk

/-- The node equation. -/
theorem den_node {x : ValueId} {n : Inst} (hx : D x = some n) :
    den D ρ fr mem x = evalNode (withRegs fr (den D ρ fr mem)) mem n := by
  cases hd : den D ρ fr mem x with
  | some a =>
    obtain ⟨k, hk⟩ := level_of_den hd
    cases k with
    | zero => simp [evalTree] at hk
    | succ k =>
      simp only [evalTree, hx] at hk
      exact (evalNode_withRegs_mono (fun y b hy => den_of_level hy) hk).symm
  | none =>
    cases he : evalNode (withRegs fr (den D ρ fr mem)) mem n with
    | none => rfl
    | some a =>
      exfalso
      have hops := evalInst_ops (evalNode_ok he)
      obtain ⟨K, hK⟩ := exists_level (E := evalTree D ρ fr mem) evalTree_succ_mono
        (fun y b hy => level_of_den hy) (operands n) hops
      have h1 : evalNode (withRegs fr (evalTree D ρ fr mem K)) mem n = some a := by
        rw [evalNode_congr (fr := withRegs fr (den D ρ fr mem))
          (fr' := withRegs fr (evalTree D ρ fr mem K)) rfl rfl rfl (fun y hy => hK y hy)]; exact he
      have h2 : evalTree D ρ fr mem (K + 1) x = some a := by simp [evalTree, hx, h1]
      rw [den_of_level h2] at hd; cases hd

/-- `den` is below every valuation satisfying the node equations and the leaves forward. -/
theorem den_le_of {W : Valuation}
    (hn : ∀ x n a, D x = some n → evalNode (withRegs fr W) mem n = some a → W x = some a)
    (hl : ∀ x a, D x = none → ρ x = some a → W x = some a) :
    Valuation.Le (den D ρ fr mem) W := by
  have : ∀ k, Valuation.Le (evalTree D ρ fr mem k) W := by
    intro k
    induction k with
    | zero => intro x a h; simp [evalTree] at h
    | succ k ih =>
      intro x a h
      simp only [evalTree] at h
      split at h
      · exact hl x a ‹_› h
      · exact hn x _ a ‹_› (evalNode_withRegs_mono ih h)
  intro x a h
  obtain ⟨k, hk⟩ := level_of_den h
  exact this k x a hk

end Den

/-! ## Changes of the graph -/

/-- `D'` extends `D` by the node `n` of the new value `w`. -/
def graphInsert (D : ValueId → Option Inst) (w : ValueId) (n : Inst) : ValueId → Option Inst :=
  fun x => if x = w then some n else D x

/-- Inserting the node of a value outside a set `K` closed under the operands of its nodes
keeps `den` on `K`. -/
theorem den_insert_fresh {D : ValueId → Option Inst} {ρ : Valuation} {fr : Frame} {mem : Mem}
    {K : ValueId → Prop} {w : ValueId} {n : Inst} (hw : ¬K w)
    (hK : ∀ x m, K x → D x = some m → ∀ y ∈ operands m, K y) {x : ValueId} (hx : K x) :
    den (graphInsert D w n) ρ fr mem x = den D ρ fr mem x := by
  have hlev : ∀ k y, K y → evalTree (graphInsert D w n) ρ fr mem k y = evalTree D ρ fr mem k y := by
    intro k
    induction k with
    | zero => intro y _; rfl
    | succ k ih =>
      intro y hy
      have hyw : y ≠ w := fun h => hw (h ▸ hy)
      simp only [evalTree, graphInsert, hyw, ite_false]
      split
      · rfl
      · rename_i m hm
        exact evalNode_congr rfl rfl rfl (fun z hz => ih z (hK y m hy hm z hz))
  cases h : den D ρ fr mem x with
  | some a =>
    obtain ⟨k, hk⟩ := level_of_den h
    exact den_of_level (by rw [hlev k x hx]; exact hk)
  | none =>
    cases h' : den (graphInsert D w n) ρ fr mem x with
    | none => rfl
    | some a =>
      obtain ⟨k, hk⟩ := level_of_den h'
      rw [hlev k x hx] at hk
      rw [den_of_level hk] at h; cases h

/-- Values whose nodes are copies of each other over twin operands (`materialize`'s clones),
all within the set `S` (the values that are available in the output). -/
inductive Twin (D : ValueId → Option Inst) (S : ValueId → Prop) : ValueId → ValueId → Prop
  | refl (x : ValueId) : Twin D S x x
  | clone {y y' : ValueId} {m : Inst} (τ : ValueId → ValueId) :
      S y → S y' → D y = some m → D y' = some (mapOperands τ m) →
      (∀ u ∈ operands m, Twin D S u (τ u)) → Twin D S y y'

theorem Twin.mono {D D' : ValueId → Option Inst} {S S' : ValueId → Prop}
    (hS : ∀ x, S x → S' x) (hD : ∀ x, S x → D' x = D x) {y y' : ValueId}
    (h : Twin D S y y') : Twin D' S' y y' := by
  induction h with
  | refl x => exact .refl x
  | clone τ hy hy' hm hm' _ ih =>
    exact .clone τ (hS _ hy) (hS _ hy') (by rw [hD _ hy]; exact hm) (by rw [hD _ hy']; exact hm') ih

theorem den_twin {D : ValueId → Option Inst} {S : ValueId → Prop} {ρ : Valuation} {fr : Frame}
    {mem : Mem} {y y' : ValueId} (h : Twin D S y y') :
    den D ρ fr mem y' = den D ρ fr mem y := by
  induction h with
  | refl => rfl
  | clone τ _ _ hm hm' _ ih =>
    rw [den_node hm', den_node hm]
    exact evalNode_rename rfl rfl rfl (fun u hu => ih u hu)

/-- Replacing the node `m` of `x` by a copy over twin operands keeps `den`. -/
theorem den_overwrite {D : ValueId → Option Inst} {S : ValueId → Prop} {ρ : Valuation}
    {fr : Frame} {mem : Mem} {x : ValueId} {m : Inst} {τ : ValueId → ValueId}
    (hx : D x = some m) (hxS : ¬S x)
    (ht : ∀ u ∈ operands m, Twin D S u (τ u)) :
    den (graphInsert D x (mapOperands τ m)) ρ fr mem = den D ρ fr mem := by
  let D' := graphInsert D x (mapOperands τ m)
  have hSD : ∀ z, S z → D' z = D z := by
    intro z hz
    have : z ≠ x := fun h => hxS (h ▸ hz)
    simp [D', graphInsert, this]
  have ht' : ∀ u ∈ operands m, Twin D' S u (τ u) := fun u hu => (ht u hu).mono (fun _ h => h) hSD
  have h1 : Valuation.Le (den D' ρ fr mem) (den D ρ fr mem) := by
    apply den_le_of
    · intro z n a hz he
      by_cases hzx : z = x
      · subst hzx
        simp only [D', graphInsert, ite_true, Option.some.injEq] at hz
        subst hz
        rw [den_node hx, ← he]
        exact (evalNode_rename rfl rfl rfl (fun u hu => den_twin (ht u hu))).symm
      · have : D z = some n := by simpa [D', graphInsert, hzx] using hz
        rw [den_node this]; exact he
    · intro z a hz hρ
      have : D z = none := by
        by_cases hzx : z = x
        · subst hzx; simp [D', graphInsert] at hz
        · simpa [D', graphInsert, hzx] using hz
      rw [den_leaf this]; exact hρ
  have h2 : Valuation.Le (den D ρ fr mem) (den D' ρ fr mem) := by
    apply den_le_of
    · intro z n a hz he
      by_cases hzx : z = x
      · subst hzx
        rw [hx] at hz; cases hz
        have hD' : D' z = some (mapOperands τ m) := by simp [D', graphInsert]
        rw [den_node hD', ← he]
        exact evalNode_rename rfl rfl rfl (fun u hu => den_twin (ht' u hu))
      · have : D' z = some n := by simpa [D', graphInsert, hzx] using hz
        rw [den_node this]; exact he
    · intro z a hz hρ
      have : D' z = none := by
        by_cases hzx : z = x
        · subst hzx; rw [hx] at hz; cases hz
        · simpa [D', graphInsert, hzx] using hz
      rw [den_leaf this]; exact hρ
  funext z
  cases h : den D ρ fr mem z with
  | some a => exact h2 z a h
  | none =>
    cases h' : den D' ρ fr mem z with
    | none => rfl
    | some a => rw [h1 z a h'] at h; cases h

end Opt
