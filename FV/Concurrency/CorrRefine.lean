import FV.Concurrency.PrepThread

/-!
# Traces related step by step refine (T2h, #311, layer 2e)

`PrepThread.refines_of_thin` turns traces that are *equal* up to steps without events into
`ThreadRefine.Refines`. Layer 2 (CLIF → VCode) relates traces whose events differ in kind (the
mapping table `MK`, `Maps` for CLIF → Arm) and whose steps without events may sit on either side
(a pure CLIF statement, the event-free instructions of a segment). `Corr MK trS trT`: the traces
are, step by step, a source step without events, a target step without events, or a source and a
target step whose events correspond pairwise (`EvRel MK`: kinds related, the same direction,
location, size and value). **`refines_of_corr`**: such traces refine, with no private location
and the target's two-event steps as its atomic updates (`StepPair`), when source steps have at
most two events.
-/

namespace Concurrency.CorrRefine

open Prog ThreadRefine PrepThread

variable {K K' V : Type}

/-- Two events correspond: kinds related by `MK`, the same direction, location, size, value. -/
def EvRel (MK : K → K' → Prop) (x : Ev K V) (y : Ev K' V) : Prop :=
  MK x.k y.k ∧ y.dir = x.dir ∧ y.loc = x.loc ∧ y.n = x.n ∧ y.val = x.val

/-- `R` holds pairwise between two lists of the same length. -/
def PW {α β : Type} (R : α → β → Prop) (l : List α) (l' : List β) : Prop :=
  l.length = l'.length ∧ ∀ k (h : k < l.length) (h' : k < l'.length), R l[k] l'[k]

/-- **Traces related step by step** (module doc). -/
inductive Corr (MK : K → K' → Prop) : List (List (Ev K V)) → List (List (Ev K' V)) → Prop
  | nil : Corr MK [] []
  | src {trS trT} : Corr MK trS trT → Corr MK ([] :: trS) trT
  | tgt {trS trT} : Corr MK trS trT → Corr MK trS ([] :: trT)
  | both {e e' trS trT} : PW (EvRel MK) e e' → e ≠ [] → Corr MK trS trT →
      Corr MK (e :: trS) (e' :: trT)

theorem Corr.append {MK : K → K' → Prop} {a b : List (List (Ev K V))}
    {c d : List (List (Ev K' V))} (h1 : Corr MK a c) (h2 : Corr MK b d) :
    Corr MK (a ++ b) (c ++ d) := by
  induction h1 with
  | nil => simpa using h2
  | src _ ih => exact .src ih
  | tgt _ ih => exact .tgt ih
  | both hf hne _ ih => exact .both hf hne ih

/-- Target steps without events correspond to no source step. -/
theorem Corr.tgts {MK : K → K' → Prop} :
    ∀ {trT : List (List (Ev K' V))}, (∀ e ∈ trT, e = []) → Corr MK [] trT
  | [], _ => .nil
  | e :: tr, h => by
    rw [h e List.mem_cons_self]
    exact .tgt (Corr.tgts fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- The index map of `Corr`: nonempty source step `j` is target step `idx j` (events
corresponding pairwise), order-preserving, onto the nonempty target steps. -/
def CorrIdx (MK : K → K' → Prop) (trS : List (List (Ev K V))) (trT : List (List (Ev K' V)))
    (idx : Nat → Nat) : Prop :=
  (∀ j (h : j < trS.length), trS[j] ≠ [] →
    ∃ h' : idx j < trT.length, PW (EvRel MK) trS[j] trT[idx j]) ∧
  (∀ j j' (h : j < trS.length) (h' : j' < trS.length), trS[j] ≠ [] → trS[j'] ≠ [] → j < j' →
    idx j < idx j') ∧
  (∀ J (h : J < trT.length), trT[J] ≠ [] → ∃ j, ∃ h' : j < trS.length, idx j = J ∧ trS[j] ≠ [])

theorem corrIdx_of_corr {MK : K → K' → Prop} {trS : List (List (Ev K V))}
    {trT : List (List (Ev K' V))} (h : Corr MK trS trT) : ∃ idx, CorrIdx MK trS trT idx := by
  induction h with
  | nil =>
    exact ⟨id, fun j h => absurd h (Nat.not_lt_zero _), fun j _ h => absurd h (Nat.not_lt_zero _),
      fun J h => absurd h (Nat.not_lt_zero _)⟩
  | @src trS trT _ ih =>
    obtain ⟨idx, h1, h2, h3⟩ := ih
    refine ⟨fun j => idx (j - 1), ?_, ?_, ?_⟩
    · intro j hj hne
      rcases j with _ | j
      · simp at hne
      · simp only [List.length_cons, List.getElem_cons_succ] at hj hne ⊢
        exact h1 j (by omega) hne
    · intro j j' hj hj' hne hne' hlt
      rcases j with _ | j
      · simp at hne
      rcases j' with _ | j'
      · simp at hne'
      simp only [List.length_cons, List.getElem_cons_succ] at hj hj' hne hne'
      exact h2 j j' (by omega) (by omega) hne hne' (by omega)
    · intro J hJ hne
      obtain ⟨j, hj, hidx, hne'⟩ := h3 J hJ hne
      exact ⟨j + 1, by simp; omega, by simpa using hidx, by simpa using hne'⟩
  | @tgt trS trT _ ih =>
    obtain ⟨idx, h1, h2, h3⟩ := ih
    refine ⟨fun j => idx j + 1, ?_, ?_, ?_⟩
    · intro j hj hne
      obtain ⟨hl, he⟩ := h1 j hj hne
      exact ⟨by simp; omega, by simpa using he⟩
    · intro j j' hj hj' hne hne' hlt
      exact Nat.succ_lt_succ (h2 j j' hj hj' hne hne' hlt)
    · intro J hJ hne
      rcases J with _ | J
      · simp at hne
      · simp only [List.length_cons, List.getElem_cons_succ] at hJ hne
        obtain ⟨j, hj, hidx, hne'⟩ := h3 J (by omega) hne
        exact ⟨j, hj, by simp [hidx], hne'⟩
  | @both e e' trS trT hf hne0 _ ih =>
    obtain ⟨idx, h1, h2, h3⟩ := ih
    refine ⟨fun j => if j = 0 then 0 else idx (j - 1) + 1, ?_, ?_, ?_⟩
    · intro j hj hne
      rcases j with _ | j
      · exact ⟨by simp, by simpa using hf⟩
      · simp only [List.length_cons, List.getElem_cons_succ] at hj hne ⊢
        obtain ⟨hl, he⟩ := h1 j (by omega) hne
        simp only [Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel,
          List.getElem_cons_succ]
        exact ⟨by omega, he⟩
    · intro j j' hj hj' hne hne' hlt
      rcases j with _ | j <;> rcases j' with _ | j'
      · omega
      · simp
      · omega
      · simp only [List.length_cons, List.getElem_cons_succ] at hj hj' hne hne'
        simp only [Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]
        have := h2 j j' (by omega) (by omega) hne hne' (by omega)
        omega
    · intro J hJ hne
      rcases J with _ | J
      · exact ⟨0, by simp, rfl, by simpa using hne0⟩
      · simp only [List.length_cons, List.getElem_cons_succ] at hJ hne
        obtain ⟨j, hj, hidx, hne'⟩ := h3 J (by omega) hne
        exact ⟨j + 1, by simp; omega, by simp [hidx], by simpa using hne'⟩

/-- **Traces related step by step refine** (no private location, the target's two-event steps
its atomic updates; source steps of at most two events). -/
theorem refines_of_corr {MK : K → K' → Prop} {trS : List (List (Ev K V))}
    {trT : List (List (Ev K' V))} (h : Corr MK trS trT)
    (hlen : ∀ j (h : j < trS.length), trS[j].length ≤ 2) :
    ∃ ψ, Refines MK (fun _ => False) (StepPair trT) trS trT ψ := by
  obtain ⟨idx, h1, h2, h3⟩ := corrIdx_of_corr h
  have img : ∀ p x, evAt trS p = some x → ∃ y, evAt trT (idx p.1, p.2) = some y ∧ EvRel MK x y := by
    intro p x hx
    obtain ⟨hj, hk, rfl⟩ := evAt_some hx
    obtain ⟨hl, he⟩ := h1 p.1 hj (ne_nil_of_lt hk)
    have hk' : p.2 < trT[idx p.1].length := by rw [← he.1]; exact hk
    exact ⟨_, evAt_of hl hk', he.2 _ hk hk'⟩
  refine ⟨fun p => (idx p.1, p.2), ?_⟩
  exact
    { ev := fun p x hx => by
        obtain ⟨y, hy, hm, hd, hl, hn, hv⟩ := img p x hx
        exact ⟨y, hy, hm, hd, hl, hn, hv⟩
      mono := fun p q hp hq hl => by
        obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hp
        obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hq
        obtain ⟨hj, hk, -⟩ := evAt_some hx
        obtain ⟨hj', hk', -⟩ := evAt_some hy
        rcases hl with hl | ⟨he, hl⟩
        · exact .inl (h2 _ _ hj hj' (ne_nil_of_lt hk) (ne_nil_of_lt hk') hl)
        · exact .inr ⟨by simp only [he], hl⟩
      shared := fun _ _ _ h => h
      priv := fun p y hy _ hn => by
        obtain ⟨hj, hk, -⟩ := evAt_some hy
        obtain ⟨j, hj', hidx, hne⟩ := h3 p.1 hj (ne_nil_of_lt hk)
        obtain ⟨hl, he⟩ := h1 j hj' hne
        exfalso
        have hk2 : p.2 < trS[j].length := by
          rw [he.1]; simp only [hidx]; exact hk
        refine hn (j, p.2) ?_ (by simp only [hidx])
        rw [evAt_of hj' hk2]; rfl
      len := hlen
      pair := fun j hj h2' => by
        have hne : trS[j] ≠ [] := by intro e; rw [e] at h2'; simp at h2'
        obtain ⟨hl, he⟩ := h1 j hj hne
        exact ⟨idx j, rfl, rfl, hl, by rw [← he.1]; exact h2'⟩
      pair_inv := fun p q hp hq hpr => by
        obtain ⟨J, e1, e2, hJ, hJ2⟩ := hpr
        simp only [Prod.mk.injEq] at e1 e2
        obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hp
        obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hq
        obtain ⟨hj, hk, -⟩ := evAt_some hx
        obtain ⟨hj', hk', -⟩ := evAt_some hy
        have hpq : p.1 = q.1 := by
          refine Classical.byContradiction fun hne => ?_
          rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
          · have := h2 _ _ hj hj' (ne_nil_of_lt hk) (ne_nil_of_lt hk') hlt; omega
          · have := h2 _ _ hj' hj (ne_nil_of_lt hk') (ne_nil_of_lt hk) hlt; omega
        obtain ⟨a, b⟩ := p
        obtain ⟨c, d⟩ := q
        simp only at hpq e1 e2
        subst hpq
        exact ⟨a, by rw [e1.2], by rw [e2.2]⟩ }

end Concurrency.CorrRefine
