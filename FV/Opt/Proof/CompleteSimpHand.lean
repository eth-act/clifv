import FV.Opt.Proof.CompleteLicm
import FV.Opt.HandRules
import FV.Opt.Proof.RulesProv

/-!
# The hand rules pass values on (M1, #24)

`Opt.simpRulesProv_hand : SimpRulesProv HandRules.simplify`. Every candidate of
`Opt.HandRules.simplify` is an operand of a node of the root (or of a node of such an operand:
`double_negation`, `iadd_reassoc_const`), or the result of `make` on a node over such values and
made values (`iconst`, the operands swapped, `x + c`, `x << c`). The proof is a loop invariant of
the rule loop (`HandInv`, through `forIn_inv_mem`): the state satisfies `P`, `Q` has grown from
the start state, and every candidate so far is in `Q`.
-/

namespace Opt

open Clif

/-- `forIn_inv_mem` in a form `refine` can unify with a goal about the loop's result. -/
theorem forIn_inv_imp {α β : Type} (I Q : β → Prop) (l : List α) (b : β)
    (f : α → β → Id (ForInStep β)) (hQ : ∀ b, I b → Q b) (hb : I b)
    (hf : ∀ a ∈ l, ∀ b, I b → I (f a b).run.value) : Q (forIn l b f).run :=
  hQ _ (forIn_inv_mem l b f I hb hf)

section
variable {σ : Type} {make : σ → Inst → ValueId × σ} {P : σ → Prop} {Q : σ → ValueId → Prop}

/-- The loop invariant of `HandRules.simplify` (module doc). -/
def HandInv (P : σ → Prop) (Q : σ → ValueId → Prop) (st0 st : σ) (out : Array (ValueId × Bool)) :
    Prop :=
  P st ∧ QGrows Q st0 st ∧ ∀ c ∈ out, Q st c.1

theorem HandInv.push {st0 st : σ} {out : Array (ValueId × Bool)} (h : HandInv P Q st0 st out)
    {x : ValueId} (b : Bool) (hx : Q st x) : HandInv P Q st0 st (out.push (x, b)) := by
  refine ⟨h.1, h.2.1, fun c hc => ?_⟩
  rcases Array.mem_push.1 hc with hc | rfl
  · exact h.2.2 c hc
  · exact hx

theorem HandInv.grow {st0 st st' : σ} {out : Array (ValueId × Bool)} (h : HandInv P Q st0 st out)
    (hP : P st') (hg : QGrows Q st st') : HandInv P Q st0 st' out :=
  ⟨hP, fun x hx => hg x (h.2.1 x hx), fun c hc => hg _ (h.2.2 c hc)⟩

/-- One `make` of a node over `Q`, its value pushed. -/
theorem HandInv.mk1 (hM : MakeQ make P Q) {st0 st : σ} {out : Array (ValueId × Bool)}
    (h : HandInv P Q st0 st out) {n : Inst} (hn : ∀ y ∈ operands n, Q st y) (b : Bool) :
    HandInv P Q st0 (make st n).2 (out.push ((make st n).1, b)) := by
  obtain ⟨h1, h2, h3⟩ := hM st n h.1 hn
  exact (h.grow h1 h2).push b h3

/-- Two `make`s: a constant `c`, then a node `N c` over it. -/
theorem HandInv.mk2 (hM : MakeQ make P Q) {st0 st : σ} {out : Array (ValueId × Bool)}
    (h : HandInv P Q st0 st out) {t' : Ty} (k : BitVec t'.width) (N : ValueId → Inst)
    (hn : ∀ st1 c, QGrows Q st st1 → Q st1 c → ∀ y ∈ operands (N c), Q st1 y) (b : Bool) :
    HandInv P Q st0 (make (make st (.iconst t' k)).2 (N (make st (.iconst t' k)).1)).2
      (out.push ((make (make st (.iconst t' k)).2 (N (make st (.iconst t' k)).1)).1, b)) := by
  obtain ⟨h1, h2, h3⟩ := hM st (.iconst t' k) h.1 (by simp [operands])
  exact (h.grow h1 h2).mk1 hM (hn _ _ h2 h3) b

/-- The loop invariant of one step's result. -/
def HandStep (P : σ → Prop) (Q : σ → ValueId → Prop) (st0 : σ)
    (s : ForInStep (σ × Array (ValueId × Bool) × Array String)) : Prop :=
  HandInv P Q st0 s.value.1 s.value.2.1

theorem HandStep.ite {st0 : σ} {c : Prop} [Decidable c]
    {a b : ForInStep (σ × Array (ValueId × Bool) × Array String)}
    (ha : c → HandStep P Q st0 a) (hb : ¬c → HandStep P Q st0 b) :
    HandStep P Q st0 (if c then a else b) := by
  by_cases hc : c
  · rw [ite_eq_left hc]; exact ha hc
  · rw [ite_eq_right hc]; exact hb hc

end

/-- **The hand rules pass values on.** -/
theorem simpRulesProv_hand : SimpRulesProv HandRules.simplify := by
  intro σ enodes typeOf make P Q hE hM st0 v cands names st' hP0 hv h
  unfold HandRules.simplify at h
  simp only [Id.run, bind, pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -, rfl⟩ := h
  refine forIn_inv_imp (β := σ × Array (ValueId × Bool) × Array String)
    (fun b => HandInv P Q st0 b.1 b.2.1)
    (fun b => P b.1 ∧ QGrows Q st0 b.1 ∧ ∀ c ∈ b.2.1.toList, Q b.1 c.1)
    (enodes st0 v) (st0, #[], #[]) _ ?_ ?_ ?_
  · rintro ⟨st, out, nm⟩ ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun c hc => h3 c (by simpa using hc)⟩
  · exact ⟨hP0, fun _ h => h, by simp⟩
  rintro n hn ⟨st, out, nm⟩ hI
  change HandInv P Q st0 st out at hI
  have hops : ∀ y ∈ operands n, Q st y := fun y hy => hI.2.1 y (hE st0 v hP0 hv n hn y hy)
  simp only [Id.run]
  change HandStep P Q st0 _
  split
  · exact hI.mk1 hM (by simp [operands]) true
  split
  · rename_i op t x y _
    have hQx : Q st x := hops x (by simp [operands])
    have hQy : Q st y := hops y (by simp [operands])
    generalize List.findSome? (fun n : Inst => match n with
      | .iconst t i => some (Val.mk t i) | _ => none) (enodes st x) = cx
    generalize hcy : List.findSome? (fun n : Inst => match n with
      | .iconst t i => some (Val.mk t i) | _ => none) (enodes st y) = cy
    refine HandStep.ite (fun _ => hI.push _ hQx) (fun _ => ?_)
    refine HandStep.ite (fun _ => hI.push _ hQy) (fun _ => ?_)
    refine HandStep.ite (fun _ => hI.push _ hQx) (fun _ => ?_)
    refine HandStep.ite (fun _ => hI.push _ hQx) (fun _ => ?_)
    refine HandStep.ite (fun _ => hI.push _ hQx) (fun _ => ?_)
    refine HandStep.ite (fun _ => hI.mk1 hM (by simp [operands]) _) (fun _ => ?_)
    refine HandStep.ite (fun _ => hI.mk1 hM (by simp [operands]) _) (fun _ => ?_)
    refine HandStep.ite (fun _ => hI.mk1 hM (by simp [operands, hQx, hQy]) _) (fun _ => ?_)
    refine HandStep.ite (fun _ => ?_) (fun _ => ?_)
    · split
      · exact hI.mk2 hM _ (fun c => .binary .iadd t x c)
          (fun _ _ hg hc => by simp [operands, hg x hQx, hc]) _
      · exact hI
    refine HandStep.ite (fun _ => ?_) (fun _ => ?_)
    · split
      · split
        · rename_i a k1 heq
          obtain ⟨n', hn', hf⟩ := List.exists_of_findSome?_eq_some heq
          have hE' := hE st x hI.1 hQx n' hn'
          split at hf
          · rename_i t' a' b'
            simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hf
            obtain ⟨_, _, rfl, -⟩ := hf
            have hQa : Q st a' := hE' a' (by simp [operands])
            exact hI.mk2 hM _ (fun c => .binary .iadd t a' c)
              (fun _ _ hg hc => by simp [operands, hg a' hQa, hc]) _
          · cases hf
        · exact hI
      · exact hI
    refine HandStep.ite (fun _ => ?_) (fun _ => hI)
    split
    · split
      · exact hI.mk2 hM _ (fun c => .binary .ishl t x c)
          (fun _ _ hg hc => by simp [operands, hg x hQx, hc]) _
      · exact hI
    · exact hI
  · -- unary
    rename_i op t x _
    have hQx : Q st x := hops x (by simp [operands])
    refine HandStep.ite (fun _ => ?_) (fun _ => hI)
    split
    · rename_i a heq
      obtain ⟨n', hn', hf⟩ := List.exists_of_findSome?_eq_some heq
      have hE' := hE st x hI.1 hQx n' hn'
      split at hf
      · split at hf
        · cases hf
          exact hI.push _ (hE' _ (by simp [operands]))
        · cases hf
      · cases hf
    · exact hI
  · -- select
    rename_i t c x y _
    exact HandStep.ite (fun _ => hI.push _ (hops x (by simp [operands]))) (fun _ => hI)
  · -- icmp
    exact HandStep.ite (fun _ => hI.mk1 hM (by simp [operands]) _) (fun _ => hI)
  · exact hI

end Opt
