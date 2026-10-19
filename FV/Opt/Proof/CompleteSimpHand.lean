import FV.Opt.Proof.CompleteSimpHyp

/-!
# The hand rules meet the completeness obligation (M1, #24)

`Opt.simpRulesOk_hand : SimpRulesProv HandRules.simplify`. Every candidate of
`Opt.HandRules.simplify` is an operand of a node of the root (or of a node of such an operand:
`double_negation`, `iadd_reassoc_const`) of the root's type, or the result of `make` on a
well-typed pure node over such values (`iconst`, the operands swapped, `x + c`, `x << c`).
The proof is a loop invariant of the rule loop (`HandInv`, through `forIn_inv_mem`): the state
satisfies `P`, has grown from the start state, and every candidate so far is the root or a value
of `R` of the root's type.
-/

namespace Opt

open Clif

/-- `forIn_inv_mem` in a form `refine` can unify with a goal about the loop's result. -/
theorem forIn_inv_imp {α β : Type} (I Q : β → Prop) (l : List α) (b : β)
    (f : α → β → Id (ForInStep β)) (hQ : ∀ b, I b → Q b) (hb : I b)
    (hf : ∀ a ∈ l, ∀ b, I b → I (f a b).run.value) : Q (forIn l b f).run :=
  hQ _ (forIn_inv_mem l b f I hb hf)

theorem nodeIn_iconst {ty : ValueId → Option Ty} {fn : Function} {Rs : ValueId → Prop} (t : Ty)
    (k : BitVec t.width) : NodeIn ty fn Rs (SState.nodeTy (.iconst t k)) (.iconst t k) :=
  ⟨rfl, rfl, rfl, by simp [operands]⟩

theorem nodeIn_binary {ty : ValueId → Option Ty} {fn : Function} {Rs : ValueId → Prop}
    {op : BinaryOp} {t : Ty} {x y : ValueId} (hx : Rs x) (hy : Rs y) (htx : ty x = some t)
    (hty : ty y = some t ∨ (op.isShift = true ∧ (ty y).isSome = true)) :
    NodeIn ty fn Rs (SState.nodeTy (.binary op t x y)) (.binary op t x y) := by
  refine ⟨rfl, ?_, rfl, by simp [operands, hx, hy]⟩
  rcases hty with h | h
  · simp [pureTyped, htx, h]
  · simp [pureTyped, htx, h.1, h.2]

theorem RGrows.refl {σ : Type} {typeOf : σ → ValueId → Option Ty} {R : σ → ValueId → Prop}
    (st : σ) : RGrows typeOf R st st :=
  ⟨fun _ h => h, fun _ _ h => h⟩

theorem RGrows.trans {σ : Type} {typeOf : σ → ValueId → Option Ty} {R : σ → ValueId → Prop}
    {s1 s2 s3 : σ} (h1 : RGrows typeOf R s1 s2) (h2 : RGrows typeOf R s2 s3) :
    RGrows typeOf R s1 s3 :=
  ⟨fun x h => h2.1 x (h1.1 x h), fun x t h => h2.2 x t (h1.2 x t h)⟩

namespace HandRules

/-- The constant folded by `fold` has the node's result type. -/
theorem fold_ty {cst : ValueId → Option Val} {n : Inst} {r : Val} (h : fold cst n = some r) :
    SState.nodeTy n = some r.ty := by
  unfold fold at h
  split at h
  · cases h
  · cases h
  · cases h
  · split at h
    · cases h
    · split at h
      · rename_i r' m he
        split at h
        · cases h
        · cases h
          exact evalNode_ty (fr := constFrame cst) (mem := Mem.empty) (by simp [evalNode, he])
      · cases h

end HandRules

section
variable {σ : Type} {enodes : σ → ValueId → List Inst} {typeOf : σ → ValueId → Option Ty}
  {make : σ → Inst → ValueId × σ} {fn : Function} {P : σ → Prop} {R : σ → ValueId → Prop}

/-- `make` on a well-typed pure node over `R`. -/
theorem MakeIn.step (hM : MakeIn make typeOf fn P R (fun _ => False)) {st : σ} {n : Inst}
    (hP : P st) (hn : NodeIn (typeOf st) fn (R st) (SState.nodeTy n) n) :
    P (make st n).2 ∧ RGrows typeOf R st (make st n).2 ∧ R (make st n).2 (make st n).1 ∧
      typeOf (make st n).2 (make st n).1 = SState.nodeTy n := by
  obtain ⟨h1, h2, h3, h4⟩ := hM st n hP hn
  exact ⟨h1, h2, h3.resolve_right id, h4⟩

/-- The loop invariant of `HandRules.simplify` (module doc). -/
def HandInv (typeOf : σ → ValueId → Option Ty) (P : σ → Prop) (R : σ → ValueId → Prop) (st0 : σ)
    (v : ValueId) (st : σ) (out : Array (ValueId × Bool)) : Prop :=
  P st ∧ RGrows typeOf R st0 st ∧
    ∀ c ∈ out, c.1 = v ∨ (R st c.1 ∧ ∃ t, typeOf st0 v = some t ∧ typeOf st c.1 = some t)

theorem HandInv.push {st0 st : σ} {v : ValueId} {out : Array (ValueId × Bool)}
    (h : HandInv typeOf P R st0 v st out) {x : ValueId} (b : Bool) (hx : R st x) {t : Ty}
    (hv : typeOf st0 v = some t) (ht : typeOf st x = some t) :
    HandInv typeOf P R st0 v st (out.push (x, b)) := by
  refine ⟨h.1, h.2.1, fun c hc => ?_⟩
  rcases Array.mem_push.1 hc with hc | rfl
  · exact h.2.2 c hc
  · exact .inr ⟨hx, t, hv, ht⟩

theorem HandInv.grow {st0 st st' : σ} {v : ValueId} {out : Array (ValueId × Bool)}
    (h : HandInv typeOf P R st0 v st out) (hP : P st') (hg : RGrows typeOf R st st') :
    HandInv typeOf P R st0 v st' out := by
  refine ⟨hP, h.2.1.trans hg, fun c hc => ?_⟩
  rcases h.2.2 c hc with h1 | ⟨h1, t, h2, h3⟩
  · exact .inl h1
  · exact .inr ⟨hg.1 _ h1, t, h2, hg.2 _ _ h3⟩

/-- One `make` of a well-typed pure node over `R` of the root's type, its value pushed. -/
theorem HandInv.mk1 (hM : MakeIn make typeOf fn P R (fun _ => False)) {st0 st : σ}
    {v : ValueId} {out : Array (ValueId × Bool)} (h : HandInv typeOf P R st0 v st out) {n : Inst}
    {t : Ty} (hn : NodeIn (typeOf st) fn (R st) (SState.nodeTy n) n) (hv : typeOf st0 v = some t)
    (ht : SState.nodeTy n = some t) (b : Bool) :
    HandInv typeOf P R st0 v (make st n).2 (out.push ((make st n).1, b)) := by
  obtain ⟨h1, h2, h3, h4⟩ := MakeIn.step hM h.1 hn
  exact (h.grow h1 h2).push b h3 hv (h4.trans ht)

/-- Two `make`s: a constant `c`, then a node `N c` over it. -/
theorem HandInv.mk2 (hM : MakeIn make typeOf fn P R (fun _ => False)) {st0 st : σ}
    {v : ValueId} {out : Array (ValueId × Bool)} (h : HandInv typeOf P R st0 v st out)
    {t t' : Ty} (k : BitVec t'.width) (hv : typeOf st0 v = some t) (N : ValueId → Inst)
    (hn : ∀ st1 c, P st1 → RGrows typeOf R st st1 → R st1 c → typeOf st1 c = some t' →
      NodeIn (typeOf st1) fn (R st1) (SState.nodeTy (N c)) (N c))
    (ht : ∀ c, SState.nodeTy (N c) = some t) (b : Bool) :
    HandInv typeOf P R st0 v (make (make st (.iconst t' k)).2 (N (make st (.iconst t' k)).1)).2
      (out.push ((make (make st (.iconst t' k)).2 (N (make st (.iconst t' k)).1)).1, b)) := by
  obtain ⟨h1, h2, h3, h4⟩ := MakeIn.step hM h.1 (nodeIn_iconst t' k)
  exact (h.grow h1 h2).mk1 hM (hn _ _ h1 h2 h3 h4) hv (ht _) b

/-- The loop invariant of one step's result. -/
def HandStep (typeOf : σ → ValueId → Option Ty) (P : σ → Prop) (R : σ → ValueId → Prop) (st0 : σ)
    (v : ValueId) (s : ForInStep (σ × Array (ValueId × Bool) × Array String)) : Prop :=
  HandInv typeOf P R st0 v s.value.1 s.value.2.1

theorem HandStep.ite {st0 : σ} {v : ValueId} {c : Prop} [Decidable c]
    {a b : ForInStep (σ × Array (ValueId × Bool) × Array String)}
    (ha : c → HandStep typeOf P R st0 v a) (hb : ¬c → HandStep typeOf P R st0 v b) :
    HandStep typeOf P R st0 v (if c then a else b) := by
  by_cases hc : c
  · rw [ite_eq_left hc]; exact ha hc
  · rw [ite_eq_right hc]; exact hb hc

theorem isShift_of_comm {op : BinaryOp} (h : HandRules.isCommutative op = true) :
    op.isShift = false := by
  cases op <;> first | rfl | (simp [HandRules.isCommutative] at h)

end

/-- **The hand rules meet the completeness obligation.** -/
theorem simpRulesOk_hand : SimpRulesProv HandRules.simplify := by
  intro σ enodes typeOf make fn P R hG hM st0 v cands names st' hP0 hroot h
  unfold HandRules.simplify at h
  simp only [Id.run, bind, pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -, rfl⟩ := h
  refine forIn_inv_imp (β := σ × Array (ValueId × Bool) × Array String)
    (fun b => HandInv typeOf P R st0 v b.1 b.2.1)
    (fun b => P b.1 ∧ RGrows typeOf R st0 b.1 ∧
      ∀ c ∈ b.2.1.toList, c.1 = v ∨ (R b.1 c.1 ∧ typeOf b.1 c.1 = typeOf st0 v))
    (enodes st0 v) (st0, #[], #[]) _ ?_ ?_ ?_
  · rintro ⟨st, out, nm⟩ ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun c hc => ?_⟩
    rcases h3 c (by simpa using hc) with h | ⟨h, t, ht1, ht2⟩
    · exact .inl h
    · exact .inr ⟨h, by rw [ht1, ht2]⟩
  · exact ⟨hP0, RGrows.refl _, by simp⟩
  rintro n hn ⟨st, out, nm⟩ hI
  obtain ⟨hpure, hpt, hnty, hops⟩ := hroot n hn
  simp only [Id.run]
  change HandInv typeOf P R st0 v st out at hI
  change HandStep typeOf P R st0 v _
  have hg := hI.2.1
  split
  · rename_i r hr
    exact hI.mk1 hM (nodeIn_iconst _ _) (by rw [← hnty, HandRules.fold_ty hr]) rfl true
  split
  · rename_i op t x y _
    have hv : typeOf st0 v = some t := by rw [← hnty]; rfl
    simp only [pureTyped, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hpt
    obtain ⟨htx, hty⟩ := hpt
    have hRx : R st x := hg.1 _ (hops x (by simp [operands]))
    have hRy : R st y := hg.1 _ (hops y (by simp [operands]))
    have htx' : typeOf st x = some t := hg.2 _ _ htx
    have hty' : op.isShift = false → typeOf st y = some t := fun hs =>
      hg.2 _ _ (hty.resolve_left (by simp [hs]))
    generalize List.findSome? (fun n : Inst => match n with
      | .iconst t i => some (Val.mk t i) | _ => none) (enodes st x) = cx
    generalize hcy : List.findSome? (fun n : Inst => match n with
      | .iconst t i => some (Val.mk t i) | _ => none) (enodes st y) = cy
    refine HandStep.ite (fun _ => hI.push _ hRx hv htx') (fun _ => ?_)
    refine HandStep.ite (fun hc => ?_) (fun _ => ?_)
    · simp only [Bool.and_eq_true] at hc
      exact hI.push _ hRy hv (hty' (isShift_of_comm hc.1.1.1.1))
    refine HandStep.ite (fun _ => hI.push _ hRx hv htx') (fun _ => ?_)
    refine HandStep.ite (fun _ => hI.push _ hRx hv htx') (fun _ => ?_)
    refine HandStep.ite (fun _ => hI.push _ hRx hv htx') (fun _ => ?_)
    refine HandStep.ite (fun _ => hI.mk1 hM (nodeIn_iconst _ _) hv rfl _) (fun _ => ?_)
    refine HandStep.ite (fun _ => hI.mk1 hM (nodeIn_iconst _ _) hv rfl _) (fun _ => ?_)
    refine HandStep.ite (fun hc => ?_) (fun _ => ?_)
    · simp only [Bool.and_eq_true] at hc
      exact hI.mk1 hM (nodeIn_binary hRy hRx (hty' (isShift_of_comm hc.1.1)) (.inl htx')) hv rfl _
    refine HandStep.ite (fun _ => ?_) (fun _ => ?_)
    · split
      · exact hI.mk2 hM _ hv (fun c => .binary .iadd t x c)
          (fun _ _ _ hg1 hc htc => nodeIn_binary (hg1.1 _ hRx) hc (hg1.2 _ _ htx') (.inl htc))
          (fun _ => rfl) _
      · exact hI
    refine HandStep.ite (fun _ => ?_) (fun _ => ?_)
    · split
      · split
        · rename_i a k1 heq
          obtain ⟨n', hn', hf⟩ := List.exists_of_findSome?_eq_some heq
          have hG' := hG st x hI.1 hRx n' hn'
          split at hf
          · rename_i t' a' b'
            simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hf
            obtain ⟨_, _, rfl, -⟩ := hf
            obtain ⟨-, hpt', hnt', hops'⟩ := hG'
            simp only [pureTyped, Bool.and_eq_true, beq_iff_eq] at hpt'
            have ht' : t' = t := by
              have : SState.nodeTy (.binary .iadd t' a' b') = some t' := rfl
              rw [this, htx'] at hnt'; exact Option.some.inj hnt'
            subst ht'
            have hRa : R st a' := hops' a' (by simp [operands])
            exact hI.mk2 hM _ hv (fun c => .binary .iadd t' a' c)
              (fun _ _ _ hg1 hc htc => nodeIn_binary (hg1.1 _ hRa) hc (hg1.2 _ _ hpt'.1) (.inl htc))
              (fun _ => rfl) _
          · cases hf
        · exact hI
      · exact hI
    refine HandStep.ite (fun _ => ?_) (fun _ => hI)
    split
    · split
      · exact hI.mk2 hM _ hv (fun c => .binary .ishl t x c)
          (fun _ _ _ hg1 hc htc => nodeIn_binary (hg1.1 _ hRx) hc (hg1.2 _ _ htx')
            (.inr ⟨rfl, by simp [htc]⟩))
          (fun _ => rfl) _
      · exact hI
    · exact hI
  · -- unary
    rename_i op t x _
    have hv : typeOf st0 v = some t := by rw [← hnty]; rfl
    simp only [pureTyped, beq_iff_eq] at hpt
    have hRx : R st x := hg.1 _ (hops x (by simp [operands]))
    have htx' : typeOf st x = some t := hg.2 _ _ hpt
    refine HandStep.ite (fun _ => ?_) (fun _ => hI)
    split
    · rename_i a heq
      obtain ⟨n', hn', hf⟩ := List.exists_of_findSome?_eq_some heq
      have hG' := hG st x hI.1 hRx n' hn'
      split at hf
      · rename_i op' t' a'
        split at hf
        · cases hf
          obtain ⟨-, hpt', hnt', hops'⟩ := hG'
          simp only [pureTyped, beq_iff_eq] at hpt'
          have ht' : t' = t := by
            have : ∀ a, SState.nodeTy (.unary op' t' a) = some t' := fun _ => rfl
            rw [this, htx'] at hnt'; exact Option.some.inj hnt'
          subst ht'
          exact hI.push _ (hops' _ (by simp [operands])) hv hpt'
        · cases hf
      · cases hf
    · exact hI
  · -- select
    rename_i t c x y _
    have hv : typeOf st0 v = some t := by rw [← hnty]; rfl
    simp only [pureTyped, Bool.and_eq_true, beq_iff_eq] at hpt
    refine HandStep.ite (fun _ => hI.push _ (hg.1 _ (hops x (by simp [operands]))) hv
      (hg.2 _ _ hpt.1.2)) (fun _ => hI)
  · -- icmp
    rename_i cc t x y _
    have hv : typeOf st0 v = some .i8 := by rw [← hnty]; rfl
    exact HandStep.ite (fun _ => hI.mk1 hM (nodeIn_iconst _ _) hv rfl _) (fun _ => hI)
  · exact hI

end Opt


