import FV.Backend.Proof.LowerSpec
import Std.Data.HashMap.Lemmas

/-!
# Completeness of `lowerCheck`: alias resolution

With unique keys below `lo` and well-founded chains (`AliasWF`), the validator's resolution
`gnAt (gnTable lo al)` (a hash map, each chain followed at most `al.length + 1` steps) reaches
the end of every alias chain (`gn_path`), is constant along an alias (`gn_step`), and agrees
with `lowerFunction`'s fuel-bounded array chase (`resolve_eq`).

Both chases follow a step function `s` faithful to `al` (`s n = some o` only for `(n, o) ∈ al`,
`s n = none` only for non-keys). Along a chain the rank of the keys decreases, so the number of
keys of rank at most the current one (counted over any list `K` holding all keys, `chainCount`)
decreases: a chase with at least that much fuel ends at a non-key (`chaseF_end`). With unique
keys the chain is deterministic, so its non-key end is unique (`path_end_unique`).
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof

/-! ## A generic chase -/

/-- Follow the step function `s` from `n`, at most `k` steps. -/
def chaseF (s : Nat → Option Nat) : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => match s n with
    | some o => chaseF s k o
    | none => n

/-- `s` follows the aliases `al`. -/
structure Faithful (al : List (Nat × Nat)) (s : Nat → Option Nat) : Prop where
  some : ∀ n o, s n = some o → (n, o) ∈ al
  none : ∀ n, s n = none → ∀ o, (n, o) ∉ al

/-- The keys of `K` of rank at most `rank n`. -/
def chainCount (al : List (Nat × Nat)) (rank : Nat → Nat) (K : List Nat) (n : Nat) : Nat :=
  K.countP fun q => al.any (fun p => p.1 == q) && decide (rank q ≤ rank n)

theorem countP_lt {K : List Nat} {p q : Nat → Bool} (hpq : ∀ x ∈ K, p x = true → q x = true)
    {y : Nat} (hy : y ∈ K) (hqy : q y = true) (hpy : p y = false) : K.countP p < K.countP q := by
  induction K with
  | nil => cases hy
  | cons a K ih =>
    simp only [List.countP_cons]
    have hle : K.countP p ≤ K.countP q :=
      List.countP_mono_left fun x hx hpx => hpq x (List.mem_cons_of_mem a hx) hpx
    rcases List.mem_cons.mp hy with rfl | hy
    · simp [hpy, hqy]; omega
    · have := ih (fun x hx hpx => hpq x (List.mem_cons_of_mem a hx) hpx) hy
      have ha := hpq a List.mem_cons_self
      cases hpa : p a <;> cases hqa : q a <;> simp_all <;> omega

theorem chaseF_none {s : Nat → Option Nat} {n : Nat} (h : s n = none) : ∀ k, chaseF s k n = n
  | 0 => rfl
  | k + 1 => by simp [chaseF, h]

/-- A chase with enough fuel follows the aliases to a non-key. -/
theorem chaseF_end {al : List (Nat × Nat)} {s : Nat → Option Nat} (hs : Faithful al s)
    {rank : Nat → Nat} (hr : ∀ p ∈ al, ∀ q ∈ al, q.1 = p.2 → rank p.2 < rank p.1)
    {K : List Nat} (hK : ∀ p ∈ al, p.1 ∈ K) :
    ∀ k n, chainCount al rank K n ≤ k → AliasPath al n (chaseF s k n) ∧ s (chaseF s k n) = none := by
  intro k
  induction k with
  | zero =>
    intro n hc
    cases hn : s n with
    | none => exact ⟨.refl n, hn⟩
    | some o =>
      have hm := hs.some n o hn
      have : 0 < chainCount al rank K n := by
        unfold chainCount
        refine List.countP_pos_iff.mpr ⟨n, hK _ hm, ?_⟩
        simp only [Bool.and_eq_true, List.any_eq_true, beq_iff_eq, decide_eq_true_eq, Nat.le_refl,
          and_true]
        exact ⟨(n, o), hm, rfl⟩
      omega
  | succ k ih =>
    intro n hc
    cases hn : s n with
    | none => rw [chaseF_none hn]; exact ⟨.refl n, hn⟩
    | some o =>
      simp only [chaseF, hn]
      have hm := hs.some n o hn
      cases ho : s o with
      | none => rw [chaseF_none ho]; exact ⟨.step hm (.refl o), ho⟩
      | some o' =>
        have hm' := hs.some o o' ho
        have hlt : rank o < rank n := hr (n, o) hm (o, o') hm' rfl
        have : chainCount al rank K o < chainCount al rank K n := by
          unfold chainCount
          refine countP_lt (fun x _ hx => ?_) (hK _ hm) ?_ ?_
          · simp only [Bool.and_eq_true, decide_eq_true_eq] at hx ⊢; exact ⟨hx.1, by omega⟩
          · simp only [Bool.and_eq_true, List.any_eq_true, beq_iff_eq, decide_eq_true_eq,
              Nat.le_refl, and_true]
            exact ⟨(n, o), hm, rfl⟩
          · simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; right; omega
        obtain ⟨hp, he⟩ := ih o (by omega)
        exact ⟨.step hm hp, he⟩

theorem chainCount_le (al : List (Nat × Nat)) (rank : Nat → Nat) (K : List Nat) (n : Nat) :
    chainCount al rank K n ≤ K.length := List.countP_le_length

/-! ## Unique keys: the chain is deterministic -/

theorem val_unique {al : List (Nat × Nat)} (hu : (al.map (·.1)).Nodup) :
    ∀ {x y y' : Nat}, (x, y) ∈ al → (x, y') ∈ al → y = y' := by
  induction al with
  | nil => intro _ _ _ h; cases h
  | cons p ps ih =>
    intro x y y' h h'
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hu
    rcases List.mem_cons.mp h with e1 | m1 <;> rcases List.mem_cons.mp h' with e2 | m2
    · rw [← e2] at e1; cases e1; rfl
    · subst e1; exact absurd ⟨_, m2, rfl⟩ hu.1
    · subst e2; exact absurd ⟨_, m1, rfl⟩ hu.1
    · exact ih hu.2 m1 m2

/-- With unique keys, the non-key end of a chain is unique. -/
theorem path_end_unique {al : List (Nat × Nat)} (hu : (al.map (·.1)).Nodup) {x e e' : Nat}
    (hp : AliasPath al x e) (he : ∀ q ∈ al, q.1 ≠ e) (hp' : AliasPath al x e')
    (he' : ∀ q ∈ al, q.1 ≠ e') : e = e' := by
  induction hp generalizing e' with
  | refl x =>
    cases hp' with
    | refl => rfl
    | step hm _ => exact absurd rfl (he _ hm)
  | step hm _ ih =>
    cases hp' with
    | refl => exact absurd rfl (he' _ hm)
    | step hm' hp' =>
      obtain rfl := val_unique hu hm hm'
      exact ih he hp' he'

/-! ## The two step functions -/

theorem aliasMap_get (al : List (Nat × Nat)) (n : Nat) :
    (aliasMap al)[n]? = some o → (n, o) ∈ al := by
  induction al generalizing o with
  | nil => simp [aliasMap]
  | cons p ps ih =>
    obtain ⟨a, b⟩ := p
    have : aliasMap ((a, b) :: ps) = (aliasMap ps).insert a b := rfl
    rw [this, Std.HashMap.getElem?_insert]
    by_cases ha : a = n
    · subst ha
      simp only [beq_self_eq_true, ite_true, Option.some.injEq]
      rintro rfl; exact List.mem_cons_self
    · simp only [beq_iff_eq, ha, ite_false]
      exact fun h => List.mem_cons_of_mem _ (ih h)

theorem aliasMap_none (al : List (Nat × Nat)) (n : Nat) :
    (aliasMap al)[n]? = none → ∀ o, (n, o) ∉ al := by
  induction al with
  | nil => simp
  | cons p ps ih =>
    obtain ⟨a, b⟩ := p
    have : aliasMap ((a, b) :: ps) = (aliasMap ps).insert a b := rfl
    rw [this, Std.HashMap.getElem?_insert]
    by_cases ha : a = n
    · subst ha; simp
    · simp only [beq_iff_eq, ha, ite_false]
      intro h o hm
      rcases List.mem_cons.mp hm with he | hm
      · cases he; exact ha rfl
      · exact ih h o hm

theorem faithful_map (al : List (Nat × Nat)) : Faithful al fun n => (aliasMap al)[n]? :=
  ⟨fun n _ h => aliasMap_get al n h, fun n h => aliasMap_none al n h⟩

/-- `aliasStep`'s growth keeps the entries. -/
theorem grow_get (a : Array (Option Nat)) (k n : Nat) :
    ((if a.size ≤ k then a ++ Array.replicate (k + 1 - a.size) none else a)[n]?).join =
      (a[n]?).join := by
  split
  · rw [Array.getElem?_append]
    split
    · rfl
    · rw [Array.getElem?_replicate, Array.getElem?_eq_none (show a.size ≤ n by omega)]
      split <;> rfl
  · rfl

theorem grow_size (a : Array (Option Nat)) (k : Nat) :
    a.size ≤ (if a.size ≤ k then a ++ Array.replicate (k + 1 - a.size) none else a).size ∧
      k < (if a.size ≤ k then a ++ Array.replicate (k + 1 - a.size) none else a).size := by
  split
  · simp only [Array.size_append, Array.size_replicate]; omega
  · omega

theorem aliasStep_get (a : Array (Option Nat)) (p : Nat × Nat) (n : Nat) :
    ((aliasStep a p)[n]?).join = if n = p.1 then some p.2 else (a[n]?).join := by
  unfold aliasStep
  simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  by_cases hn : n = p.1
  · subst hn
    simp only [ite_true, (grow_size a p.1).2, Option.join]; rfl
  · simp only [Ne.symm hn, hn, ite_false]
    exact grow_get a p.1 n

theorem aliasStep_size (a : Array (Option Nat)) (p : Nat × Nat) :
    a.size ≤ (aliasStep a p).size ∧ p.1 < (aliasStep a p).size := by
  unfold aliasStep
  simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
  split
  · simp only [Array.size_append, Array.size_replicate]; omega
  · omega

theorem foldl_aliasStep (al : List (Nat × Nat)) :
    ∀ (a : Array (Option Nat)), a.size ≤ (al.foldl aliasStep a).size ∧
      (∀ p ∈ al, p.1 < (al.foldl aliasStep a).size) ∧
      ∀ n, (((al.foldl aliasStep a)[n]?).join = none → ((a[n]?).join = none ∧ ∀ o, (n, o) ∉ al)) ∧
        ∀ o, ((al.foldl aliasStep a)[n]?).join = some o → (a[n]?).join = some o ∨ (n, o) ∈ al := by
  induction al with
  | nil => intro a; simp
  | cons p ps ih =>
    intro a
    obtain ⟨h1, h2, h3⟩ := ih (aliasStep a p)
    have hs := aliasStep_size a p
    simp only [List.foldl_cons]
    refine ⟨by omega, fun q hq => ?_, fun n => ⟨fun h => ?_, fun o h => ?_⟩⟩
    · rcases List.mem_cons.mp hq with rfl | hq
      · omega
      · exact h2 q hq
    · obtain ⟨ha, hn⟩ := (h3 n).1 h
      rw [aliasStep_get] at ha
      by_cases he : n = p.1
      · simp [he] at ha
      · simp only [he, ite_false] at ha
        refine ⟨ha, fun o hm => ?_⟩
        rcases List.mem_cons.mp hm with rfl | hm
        · exact he rfl
        · exact hn o hm
    · rcases (h3 n).2 o h with ha | hm
      · rw [aliasStep_get] at ha
        by_cases he : n = p.1
        · simp only [he, ite_true, Option.some.injEq] at ha
          subst ha; subst he; exact .inr List.mem_cons_self
        · simp only [he, ite_false] at ha; exact .inl ha
      · exact .inr (List.mem_cons_of_mem _ hm)

theorem faithful_arr (al : List (Nat × Nat)) : Faithful al fun n => ((aliasArr al)[n]?).join := by
  obtain ⟨-, -, h⟩ := foldl_aliasStep al #[]
  refine ⟨fun n o ho => ?_, fun n hn => ((h n).1 hn).2⟩
  rcases (h n).2 o ho with h' | h'
  · simp at h'
  · exact h'

theorem aliasArr_size (al : List (Nat × Nat)) : ∀ p ∈ al, p.1 < (aliasArr al).size :=
  (foldl_aliasStep al #[]).2.1

/-! ## The two chases -/

theorem chase_eq (m : Std.HashMap Nat Nat) : ∀ k n, chase m k n = chaseF (fun n => m[n]?) k n
  | 0, _ => rfl
  | k + 1, n => by
    show (match m[n]? with | some o => chase m k o | none => n) =
      (match m[n]? with | some o => chaseF (fun n => m[n]?) k o | none => n)
    cases m[n]? with
    | some o => exact chase_eq m k o
    | none => rfl

theorem resolve_vreg (a : Array (Option Nat)) :
    ∀ k n c, lowerFunction.resolve a k (.vreg n c) = .vreg (chaseF (fun n => (a[n]?).join) k n) c
  | 0, _, _ => by simp [lowerFunction.resolve, chaseF]
  | k + 1, n, c => by
    simp only [lowerFunction.resolve, chaseF]
    split <;> simp_all [resolve_vreg a k]

variable {al : List (Nat × Nat)} {lo : Nat}

theorem gnAt_eq (hk : ∀ p ∈ al, p.1 < lo) (x : Nat) :
    gnAt (gnTable lo al) x = chaseF (fun n => (aliasMap al)[n]?) (al.length + 1) x := by
  unfold gnAt
  split
  · rename_i h
    simp [gnTable, chase_eq]
  · rename_i h
    simp only [gnTable, Array.size_ofFn] at h
    cases hx : (aliasMap al)[x]? with
    | none => rw [chaseF_none hx]
    | some o => exact absurd (hk _ (aliasMap_get al x hx)) (by simpa using h)

/-- `gn x` is reached from `x` by aliases and is not aliased itself. -/
theorem gn_path (hu : (al.map (·.1)).Nodup) (hk : ∀ p ∈ al, p.1 < lo) (hwf : AliasWF al)
    (x : Nat) : AliasPath al x (gnAt (gnTable lo al) x) ∧ ∀ q ∈ al, q.1 ≠ gnAt (gnTable lo al) x := by
  obtain ⟨rank, hr⟩ := hwf
  rw [gnAt_eq hk]
  have hK : ∀ p ∈ al, p.1 ∈ al.map (·.1) := fun p hp => List.mem_map_of_mem hp
  have hc := chainCount_le al rank (al.map (·.1)) x
  rw [List.length_map] at hc
  obtain ⟨hp, he⟩ := chaseF_end (faithful_map al) hr hK (al.length + 1) x (by omega)
  refine ⟨hp, fun q hq hqe => ?_⟩
  exact (faithful_map al).none _ he q.2 (by rw [← hqe]; exact hq)

/-- `gn` is constant along an alias. -/
theorem gn_step (hu : (al.map (·.1)).Nodup) (hk : ∀ p ∈ al, p.1 < lo) (hwf : AliasWF al) :
    ∀ p ∈ al, gnAt (gnTable lo al) p.1 = gnAt (gnTable lo al) p.2 := by
  intro p hp
  obtain ⟨h1, e1⟩ := gn_path hu hk hwf p.1
  obtain ⟨h2, e2⟩ := gn_path hu hk hwf p.2
  exact path_end_unique hu h1 e1 (.step hp h2) e2

/-- `lowerFunction`'s resolution is the validator's class-preserving renaming. -/
theorem resolve_eq (hu : (al.map (·.1)).Nodup) (hk : ∀ p ∈ al, p.1 < lo) (hwf : AliasWF al) :
    lowerFunction.resolve (aliasArr al) ((aliasArr al).size + 1) = renOf (gnAt (gnTable lo al)) := by
  funext r
  cases r with
  | vreg n c =>
    rw [resolve_vreg]
    simp only [renOf, Reg.vreg.injEq, and_true]
    obtain ⟨h1, e1⟩ := gn_path hu hk hwf n
    obtain ⟨rank, hr⟩ := hwf
    have hK : ∀ p ∈ al, p.1 ∈ List.range (aliasArr al).size :=
      fun p hp => List.mem_range.mpr (aliasArr_size al p hp)
    have hc := chainCount_le al rank (List.range (aliasArr al).size) n
    rw [List.length_range] at hc
    obtain ⟨hp, he⟩ := chaseF_end (faithful_arr al) hr hK ((aliasArr al).size + 1) n (by omega)
    refine path_end_unique hu hp (fun q hq hqe => ?_) h1 e1
    exact (faithful_arr al).none _ he q.2 (by rw [← hqe]; exact hq)
  | _ => simp [lowerFunction.resolve, renOf]

end Backend.Proof.Driver
