import FV.Compile.Proof.Rel

/-!
# What the fragment checker guarantees about liveness

`ExprStep lim st st'` / `StmtStep lim st st'` summarize how a successful check moves the
per-variable state `(dead, mut)`:

* expressions only kill (move) variables, never frozen ones, and leave `mut` alone;
* statements may revive a variable only by updating it (which sets `mut`), keep `mut` once
  set, and leave frozen variables (bound outside the innermost loop body) alive and
  unchanged.
-/

set_option autoImplicit false

namespace Compile.Proof

open DSL (Ty CheckSt)
open DSL.Check

theorem except_bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β} :
    (x >>= f) = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp [bind, Except.bind]

theorem need_ok {b : Bool} {msg : String} {u : Unit} : need b msg = .ok u ↔ b = true := by
  cases b <;> simp [need]

theorem alive_set_ne {st : CheckSt} {i j : Nat} {p : Bool × Bool} (h : j ≠ i) :
    alive (st.set i p) j = alive st j := by
  simp [Proof.alive, isDead, List.getD_eq_getElem?_getD, Ne.symm h]

theorem mutd_set_ne {st : CheckSt} {i j : Nat} {p : Bool × Bool} (h : j ≠ i) :
    mutd (st.set i p) j = mutd st j := by
  simp [Proof.mutd, List.getD_eq_getElem?_getD, Ne.symm h]

theorem alive_set_eq {st : CheckSt} {i : Nat} {p : Bool × Bool} (h : i < st.length) :
    alive (st.set i p) i = !p.1 := by
  simp [Proof.alive, isDead, List.getD_eq_getElem?_getD, h]

theorem mutd_set_eq {st : CheckSt} {i : Nat} {p : Bool × Bool} (h : i < st.length) :
    mutd (st.set i p) i = p.2 := by
  simp [Proof.mutd, List.getD_eq_getElem?_getD, h]

/-- Effect of a successful expression check. -/
structure ExprStep (lim : Option Nat) (st st' : CheckSt) : Prop where
  len : st'.length = st.length
  al : ∀ i, alive st' i = true → alive st i = true
  mu : ∀ i, mutd st' i = mutd st i
  fr : ∀ i, frozen lim i = true → alive st i = true → alive st' i = true

/-- Effect of a successful statement check. -/
structure StmtStep (lim : Option Nat) (st st' : CheckSt) : Prop where
  len : st'.length = st.length
  al : ∀ i, alive st' i = true → (mutd st' i = false ∨ frozen lim i = true) →
    alive st i = true
  mu : ∀ i, mutd st i = true → mutd st' i = true
  fr : ∀ i, frozen lim i = true → alive st i = true →
    alive st' i = true ∧ mutd st' i = mutd st i

namespace ExprStep

theorem refl (lim : Option Nat) (st : CheckSt) : ExprStep lim st st :=
  ⟨rfl, fun _ h => h, fun _ => rfl, fun _ _ h => h⟩

theorem trans {lim : Option Nat} {a b c : CheckSt} (h₁ : ExprStep lim a b)
    (h₂ : ExprStep lim b c) : ExprStep lim a c :=
  ⟨h₂.len.trans h₁.len, fun i h => h₁.al i (h₂.al i h),
    fun i => (h₂.mu i).trans (h₁.mu i), fun i hf h => h₂.fr i hf (h₁.fr i hf h)⟩

theorem stmt {lim : Option Nat} {a b : CheckSt} (h : ExprStep lim a b) : StmtStep lim a b :=
  ⟨h.len, fun i ha _ => h.al i ha, fun i hm => by rw [h.mu i]; exact hm,
    fun i hf ha => ⟨h.fr i hf ha, h.mu i⟩⟩

end ExprStep

namespace StmtStep

theorem refl (lim : Option Nat) (st : CheckSt) : StmtStep lim st st :=
  (ExprStep.refl lim st).stmt

theorem trans {lim : Option Nat} {a b c : CheckSt} (h₁ : StmtStep lim a b)
    (h₂ : StmtStep lim b c) : StmtStep lim a c := by
  refine ⟨h₂.len.trans h₁.len, fun i ha hm => ?_, fun i hm => h₂.mu i (h₁.mu i hm),
    fun i hf ha => ?_⟩
  · have hb := h₂.al i ha hm
    refine h₁.al i hb ?_
    rcases hm with hm | hm
    · left
      cases hbm : Proof.mutd b i
      · rfl
      · have := h₂.mu i hbm; rw [hm] at this; cases this
    · exact .inr hm
  · obtain ⟨hb, hbm⟩ := h₁.fr i hf ha
    obtain ⟨hc, hcm⟩ := h₂.fr i hf hb
    exact ⟨hc, hcm.trans hbm⟩

end StmtStep

theorem frozen_succ (lim : Option Nat) (i : Nat) :
    frozen (lim.map (· + 1)) (i + 1) = frozen lim i := by
  cases lim <;> simp [frozen]

theorem frozen_succ2 (lim : Option Nat) (i : Nat) :
    frozen (lim.map (· + 2)) (i + 2) = frozen lim i := by
  cases lim <;> simp [frozen]

/-! ## `use` and `update` -/

theorem use_ok {lin move : Bool} {lim : Option Nat} {i : Nat} {st st' : CheckSt}
    (h : use lin move lim i st = .ok st') :
    alive st i = true ∧ ExprStep lim st st' ∧
      (lin = true → move = true → i < st.length → alive st' i = false) := by
  simp only [use, DSL.Check.alive] at h
  by_cases hd : isDead st i = true
  · simp [hd, bind, Except.bind] at h
  · simp only [hd, Bool.false_eq_true, ↓reduceIte] at h
    have ha : alive st i = true := by simp [Proof.alive, hd]
    refine ⟨ha, ?_⟩
    by_cases hlm : (move && lin) = true
    · simp only [hlm, ↓reduceIte] at h
      by_cases hf : frozen lim i = true
      · simp [hf, bind, Except.bind] at h
      · simp only [hf, Bool.false_eq_true, ↓reduceIte, bind, Except.bind, Except.ok.injEq] at h
        subst h
        refine ⟨⟨by simp, fun j hj => ?_, fun j => ?_, fun j hj hja => ?_⟩, fun _ _ hl => ?_⟩
        · by_cases hji : j = i
          · subst hji; exact ha
          · rwa [alive_set_ne hji] at hj
        · by_cases hji : j = i
          · subst hji
            by_cases hl : j < st.length
            · rw [mutd_set_eq hl]; rfl
            · rw [List.set_eq_of_length_le (Nat.le_of_not_lt hl)]
          · rw [mutd_set_ne hji]
        · have hji : j ≠ i := fun e => hf (e ▸ hj)
          rwa [alive_set_ne hji]
        · rw [alive_set_eq hl]; rfl
    · simp only [hlm, Bool.false_eq_true, ↓reduceIte, bind, Except.bind] at h
      cases h
      refine ⟨ExprStep.refl _ _, fun hl hm _ => ?_⟩
      simp [hl, hm] at hlm

theorem update_ok {lin : Bool} {lim : Option Nat} {i : Nat} {st st' : CheckSt}
    (h : update lin lim i st = .ok st') :
    StmtStep lim st st' ∧ (lin = true → i < st.length → alive st' i = true) := by
  simp only [update] at h
  by_cases hl : lin = true
  · simp only [hl, ↓reduceIte] at h
    by_cases hf : frozen lim i = true
    · simp [hf] at h
    · simp only [hf, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at h
      subst h
      refine ⟨⟨by simp, fun j ha hm => ?_, fun j hm => ?_, fun j hj ha => ?_⟩, fun _ hl => ?_⟩
      · by_cases hji : j = i
        · subst hji
          by_cases hlt : j < st.length
          · rw [mutd_set_eq hlt] at hm; simp at hm; exact absurd hm hf
          · rwa [List.set_eq_of_length_le (Nat.le_of_not_lt hlt)] at ha
        · rwa [alive_set_ne hji] at ha
      · by_cases hji : j = i
        · subst hji
          by_cases hlt : j < st.length
          · rw [mutd_set_eq hlt]
          · rwa [List.set_eq_of_length_le (Nat.le_of_not_lt hlt)]
        · rwa [mutd_set_ne hji]
      · have hji : j ≠ i := fun e => hf (e ▸ hj)
        rw [alive_set_ne hji, mutd_set_ne hji]; exact ⟨ha, rfl⟩
      · rw [alive_set_eq hl]; rfl
  · simp only [hl, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at h
    subst h
    exact ⟨StmtStep.refl _ _, fun h => absurd h hl⟩

/-! ## `join`, `clearMut`, `killUpdated`, `restoreMut` -/

theorem join_length : ∀ (a b : CheckSt), a.length = b.length → (join a b).length = a.length
  | [], [], _ => rfl
  | _ :: a, _ :: b, h => by simp [join, join_length a b (by simpa using h)]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem join_getD : ∀ (a b : CheckSt) (i : Nat), a.length = b.length →
    (join a b).getD i (false, false) =
      ((a.getD i (false, false)).1 || (b.getD i (false, false)).1,
       (a.getD i (false, false)).2 || (b.getD i (false, false)).2)
  | [], [], _, _ => rfl
  | (d₁, m₁) :: a, (d₂, m₂) :: b, 0, _ => rfl
  | _ :: a, _ :: b, i + 1, h => by
    simp only [join, List.getD_cons_succ]; exact join_getD a b i (by simpa using h)
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h

theorem alive_join {a b : CheckSt} (h : a.length = b.length) (i : Nat) :
    alive (join a b) i = (alive a i && alive b i) := by
  simp only [Proof.alive, isDead, join_getD a b i h, Bool.not_or]

theorem mutd_join {a b : CheckSt} (h : a.length = b.length) (i : Nat) :
    mutd (join a b) i = (mutd a i || mutd b i) := by
  simp only [Proof.mutd, join_getD a b i h]

theorem ExprStep.join {lim : Option Nat} {st a b : CheckSt} (ha : ExprStep lim st a)
    (hb : ExprStep lim st b) : ExprStep lim st (DSL.Check.join a b) := by
  have hl : a.length = b.length := ha.len.trans hb.len.symm
  refine ⟨(join_length a b hl).trans ha.len, fun i h => ?_, fun i => ?_, fun i hf h => ?_⟩
  · rw [alive_join hl] at h; simp at h; exact ha.al i h.1
  · rw [mutd_join hl, ha.mu, hb.mu]; simp
  · rw [alive_join hl, ha.fr i hf h, hb.fr i hf h]; rfl

theorem StmtStep.join {lim : Option Nat} {st a b : CheckSt} (ha : StmtStep lim st a)
    (hb : StmtStep lim st b) : StmtStep lim st (DSL.Check.join a b) := by
  have hl : a.length = b.length := ha.len.trans hb.len.symm
  refine ⟨(join_length a b hl).trans ha.len, fun i h hm => ?_, fun i hm => ?_, fun i hf h => ?_⟩
  · rw [alive_join hl] at h; simp at h
    rw [mutd_join hl] at hm; simp at hm
    exact ha.al i h.1 (hm.elim (fun h => .inl h.1) .inr)
  · rw [mutd_join hl, ha.mu i hm]; rfl
  · obtain ⟨h₁, m₁⟩ := ha.fr i hf h
    obtain ⟨h₂, m₂⟩ := hb.fr i hf h
    rw [alive_join hl, mutd_join hl, h₁, h₂, m₁, m₂]; simp

theorem clearMut_length (st : CheckSt) : (clearMut st).length = st.length := by simp [clearMut]

theorem alive_clearMut (st : CheckSt) (i : Nat) : alive (clearMut st) i = alive st i := by
  simp only [Proof.alive, isDead, clearMut, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases st[i]? <;> rfl

theorem mutd_clearMut (st : CheckSt) (i : Nat) : mutd (clearMut st) i = false := by
  simp only [Proof.mutd, clearMut, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases st[i]? <;> rfl

theorem killUpdated_length (st : CheckSt) : (killUpdated st).length = st.length := by
  simp [killUpdated]

theorem alive_killUpdated (st : CheckSt) (i : Nat) :
    alive (killUpdated st) i = (alive st i && !mutd st i) := by
  simp only [Proof.alive, Proof.mutd, isDead, killUpdated, List.getD_eq_getElem?_getD,
    List.getElem?_map]
  cases st[i]? <;> simp

theorem mutd_killUpdated (st : CheckSt) (i : Nat) : mutd (killUpdated st) i = mutd st i := by
  simp only [Proof.mutd, killUpdated, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases st[i]? <;> rfl

theorem restoreMut_length : ∀ (a b : CheckSt), a.length = b.length →
    (restoreMut a b).length = a.length
  | [], [], _ => rfl
  | _ :: a, _ :: b, h => by simp [restoreMut, restoreMut_length a b (by simpa using h)]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem restoreMut_getD : ∀ (a b : CheckSt) (i : Nat), a.length = b.length →
    (restoreMut a b).getD i (false, false) =
      ((b.getD i (false, false)).1,
       (a.getD i (false, false)).2 || (b.getD i (false, false)).2)
  | [], [], _, _ => rfl
  | (d₁, m₁) :: a, (d₂, m₂) :: b, 0, _ => rfl
  | _ :: a, _ :: b, i + 1, h => by
    simp only [restoreMut, List.getD_cons_succ]; exact restoreMut_getD a b i (by simpa using h)
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h

theorem alive_restoreMut {a b : CheckSt} (h : a.length = b.length) (i : Nat) :
    alive (restoreMut a b) i = alive b i := by
  simp only [Proof.alive, isDead, restoreMut_getD a b i h]

theorem mutd_restoreMut {a b : CheckSt} (h : a.length = b.length) (i : Nat) :
    mutd (restoreMut a b) i = (mutd a i || mutd b i) := by
  simp only [Proof.mutd, restoreMut_getD a b i h]

/-! ## Expressions -/

theorem Expr.chk_step {Γ : List Ty} {t : Ty} (e : DSL.Expr Γ t) :
    ∀ {lim : Option Nat} {st st' : CheckSt}, e.chk lim st = .ok st' → ExprStep lim st st' := by
  induction e with
  | var v => intro lim st st' h; exact (use_ok h).2.1
  | clone v => intro lim st st' h; exact (use_ok h).2.1
  | ilit | blit | unit | mapEmpty =>
    intro lim st st' h; simp [DSL.Expr.chk] at h; subst h; exact ExprStep.refl _ _
  | ibin _ a b iha ihb | icmp _ a b iha ihb | band a b iha ihb | bor a b iha ihb
  | pair a b iha ihb =>
    intro lim st st' h
    simp only [DSL.Expr.chk] at h
    obtain ⟨s₁, h₁, h₂⟩ := except_bind_ok.1 h
    exact (iha h₁).trans (ihb h₂)
  | inot a ih | bnot a ih | fst a ih | snd a ih | vrepl _ a ih =>
    intro lim st st' h; simp only [DSL.Expr.chk] at h; exact ih h
  | cast op w' a ih =>
    intro lim st st' h
    simp only [DSL.Expr.chk] at h
    obtain ⟨_, _, h₂⟩ := except_bind_ok.1 h
    exact ih h₂
  | cond c a b ihc iha ihb =>
    intro lim st st' h
    simp only [DSL.Expr.chk] at h
    obtain ⟨s₁, h₁, r₁⟩ := except_bind_ok.1 h
    obtain ⟨s₂, h₂, r₂⟩ := except_bind_ok.1 r₁
    obtain ⟨s₃, h₃, r₃⟩ := except_bind_ok.1 r₂
    simp only [pure, Except.pure, Except.ok.injEq] at r₃
    subst r₃
    exact (ihc h₁).trans ((iha h₂).join (ihb h₃))
  | mapContains m k ih =>
    intro lim st st' h
    simp only [DSL.Expr.chk] at h
    obtain ⟨s₁, h₁, h₂⟩ := except_bind_ok.1 h
    exact (use_ok h₁).2.1.trans (ih h₂)

theorem Exprs.chk_step {Γ σ : List Ty} (es : DSL.Exprs Γ σ) :
    ∀ {lim : Option Nat} {st st' : CheckSt}, es.chk lim st = .ok st' → ExprStep lim st st' := by
  induction es with
  | nil => intro lim st st' h; simp [DSL.Exprs.chk] at h; subst h; exact ExprStep.refl _ _
  | cons e es ih =>
    intro lim st st' h
    simp only [DSL.Exprs.chk] at h
    obtain ⟨s₁, h₁, h₂⟩ := except_bind_ok.1 h
    exact (Expr.chk_step e h₁).trans (ih h₂)

theorem Op.chk_step {Γ : List Ty} {t : Ty} (o : DSL.Op Γ t) {lim : Option Nat}
    {st st' : CheckSt} (h : o.chk lim st = .ok st') : ExprStep lim st st' := by
  cases o with
  | iop op a b =>
    simp only [DSL.Op.chk] at h
    obtain ⟨s₁, h₁, h₂⟩ := except_bind_ok.1 h
    exact (Expr.chk_step a h₁).trans (Expr.chk_step b h₂)
  | vget v i | mapGet v i =>
    simp only [DSL.Op.chk] at h
    obtain ⟨s₁, h₁, h₂⟩ := except_bind_ok.1 h
    exact (use_ok h₁).2.1.trans (Expr.chk_step i h₂)

end Compile.Proof

namespace Compile.Proof

open DSL (Ty CheckSt)
open DSL.Check

theorem StmtStep.tail {lim : Option Nat} {p : Bool × Bool} {a b : CheckSt}
    (h : StmtStep (lim.map (· + 1)) (p :: a) b) : StmtStep lim a b.tail := by
  refine ⟨by have := h.len; simp at this; simp [this], fun i ha hm => ?_, fun i hm => ?_,
    fun i hf ha => ?_⟩
  · rw [alive_tail] at ha; rw [mutd_tail] at hm
    have := h.al (i + 1) ha (by rwa [frozen_succ])
    rwa [alive_cons_succ] at this
  · rw [mutd_tail]; exact h.mu (i + 1) (by rwa [mutd_cons_succ])
  · have := h.fr (i + 1) (by rwa [frozen_succ]) (by rwa [alive_cons_succ])
    rw [alive_tail, mutd_tail, this.1, this.2, mutd_cons_succ]; exact ⟨rfl, rfl⟩

theorem StmtStep.tail2 {lim : Option Nat} {p q : Bool × Bool} {a b : CheckSt}
    (h : StmtStep (lim.map (· + 2)) (p :: q :: a) b) : StmtStep lim a b.tail.tail := by
  have he : (lim.map (· + 1)).map (· + 1) = lim.map (· + 2) := by cases lim <;> rfl
  have h' : StmtStep ((lim.map (· + 1)).map (· + 1)) (p :: q :: a) b := he ▸ h
  exact h'.tail.tail

theorem Stmt.chk_step {Γ : List Ty} {τ : Ty} (s : DSL.Stmt Γ τ) :
    ∀ {lim : Option Nat} {st st' : CheckSt}, s.chk lim st = .ok st' → StmtStep lim st st' := by
  induction s with
  | ret e => intro lim st st' h; exact (Expr.chk_step e h).stmt
  | throw => intro lim st st' h; simp [DSL.Stmt.chk] at h; subst h; exact StmtStep.refl _ _
  | op o => intro lim st st' h; exact (Op.chk_step o h).stmt
  | call name body args =>
    intro lim st st' h
    simp only [DSL.Stmt.chk] at h
    obtain ⟨_, _, h⟩ := except_bind_ok.1 h
    obtain ⟨_, _, h⟩ := except_bind_ok.1 h
    split at h
    · exact (Exprs.chk_step args h).stmt
    · simp [bind, Except.bind] at h
  | let_ e k ih =>
    intro lim st st' h
    simp only [DSL.Stmt.chk] at h
    obtain ⟨_, _, h⟩ := except_bind_ok.1 h
    obtain ⟨s₁, h₁, h⟩ := except_bind_ok.1 h
    obtain ⟨s₂, h₂, h⟩ := except_bind_ok.1 h
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    exact (Expr.chk_step e h₁).stmt.trans (ih h₂).tail
  | letPair e k ih =>
    intro lim st st' h
    simp only [DSL.Stmt.chk] at h
    obtain ⟨_, _, h⟩ := except_bind_ok.1 h
    obtain ⟨_, _, h⟩ := except_bind_ok.1 h
    obtain ⟨s₁, h₁, h⟩ := except_bind_ok.1 h
    obtain ⟨s₂, h₂, h⟩ := except_bind_ok.1 h
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    exact (Expr.chk_step e h₁).stmt.trans (ih h₂).tail2
  | bind s k ihs ihk =>
    intro lim st st' h
    simp only [DSL.Stmt.chk] at h
    obtain ⟨_, _, h⟩ := except_bind_ok.1 h
    obtain ⟨s₁, h₁, h⟩ := except_bind_ok.1 h
    obtain ⟨s₂, h₂, h⟩ := except_bind_ok.1 h
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    have hs := ihs h₁
    have hk := (ihk h₂).tail
    have l₁ : s₁.length = st.length := hs.len.trans (clearMut_length st)
    have l₂ : s₂.tail.length = st.length := hk.len.trans ((killUpdated_length s₁).trans l₁)
    have hl : st.length = s₂.tail.length := l₂.symm
    refine ⟨(restoreMut_length _ _ hl), fun i ha hm => ?_, fun i hm => ?_, fun i hf ha => ?_⟩
    · rw [alive_restoreMut hl] at ha
      rw [mutd_restoreMut hl] at hm
      have hk' := hk.al i ha (by
        rcases hm with hm | hm
        · simp at hm; exact .inl hm.2
        · exact .inr hm)
      rw [alive_killUpdated] at hk'
      simp at hk'
      have := hs.al i hk'.1 (by
        rcases hm with hm | hm
        · exact .inl hk'.2
        · exact .inr hm)
      rwa [alive_clearMut] at this
    · rw [mutd_restoreMut hl, hm]; rfl
    · obtain ⟨a₁, m₁⟩ := hs.fr i hf (by rwa [alive_clearMut])
      rw [mutd_clearMut] at m₁
      obtain ⟨a₂, m₂⟩ := hk.fr i hf (by rw [alive_killUpdated, a₁, m₁]; rfl)
      rw [mutd_killUpdated, m₁] at m₂
      rw [alive_restoreMut hl, mutd_restoreMut hl, a₂, m₂]; simp
  | set v e k ih =>
    intro lim st st' h
    simp only [DSL.Stmt.chk] at h
    obtain ⟨s₁, h₁, h⟩ := except_bind_ok.1 h
    obtain ⟨s₂, h₂, h⟩ := except_bind_ok.1 h
    exact (Expr.chk_step e h₁).stmt.trans ((update_ok h₂).1.trans (ih h))
  | vset v i e k ih =>
    intro lim st st' h
    simp only [DSL.Stmt.chk] at h
    obtain ⟨s₁, h₁, h⟩ := except_bind_ok.1 h
    obtain ⟨s₂, h₂, h⟩ := except_bind_ok.1 h
    obtain ⟨s₃, h₃, h⟩ := except_bind_ok.1 h
    obtain ⟨s₄, h₄, h⟩ := except_bind_ok.1 h
    exact (use_ok h₁).2.1.stmt.trans ((Expr.chk_step i h₂).stmt.trans
      ((Expr.chk_step e h₃).stmt.trans ((update_ok h₄).1.trans (ih h))))
  | mapInsert v key val k ih =>
    intro lim st st' h
    simp only [DSL.Stmt.chk] at h
    obtain ⟨s₁, h₁, h⟩ := except_bind_ok.1 h
    obtain ⟨s₂, h₂, h⟩ := except_bind_ok.1 h
    obtain ⟨s₃, h₃, h⟩ := except_bind_ok.1 h
    obtain ⟨s₄, h₄, h⟩ := except_bind_ok.1 h
    exact (use_ok h₁).2.1.stmt.trans ((Expr.chk_step key h₂).stmt.trans
      ((Expr.chk_step val h₃).stmt.trans ((update_ok h₄).1.trans (ih h))))
  | ite c t e iht ihe =>
    intro lim st st' h
    simp only [DSL.Stmt.chk] at h
    obtain ⟨s₁, h₁, h⟩ := except_bind_ok.1 h
    obtain ⟨s₂, h₂, h⟩ := except_bind_ok.1 h
    obtain ⟨s₃, h₃, h⟩ := except_bind_ok.1 h
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    exact (Expr.chk_step c h₁).stmt.trans ((iht h₂).join (ihe h₃))
  | forRange n init body _ =>
    intro lim st st' h
    simp only [DSL.Stmt.chk] at h
    obtain ⟨_, _, h⟩ := except_bind_ok.1 h
    obtain ⟨_, _, h⟩ := except_bind_ok.1 h
    obtain ⟨s₁, h₁, h⟩ := except_bind_ok.1 h
    obtain ⟨s₂, h₂, h⟩ := except_bind_ok.1 h
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    exact (Expr.chk_step init h₁).stmt

end Compile.Proof
