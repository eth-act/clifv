import FV.Compile.Proof.Sim

/-!
# Lemmas about `EnvRel` and `selHdl`
-/

set_option autoImplicit false

namespace Compile.Proof

open Compile
open Clif (Val Regs ValueId Frame State Mem Program Function)
open DSL (Ty IntW)

theorem Var.idx_lt : ∀ {Γ : List Ty} {t : Ty} (v : DSL.Var Γ t), v.idx < Γ.length
  | _ :: _, _, .zero => by simp [DSL.Var.idx]
  | _ :: _, _, .succ v => by simp [DSL.Var.idx]; exact Var.idx_lt v

theorem Var.mem : ∀ {Γ : List Ty} {t : Ty} (v : DSL.Var Γ t), t ∈ Γ
  | _ :: _, _, .zero => List.mem_cons_self
  | _ :: _, _, .succ v => List.mem_cons_of_mem _ (Var.mem v)

/-! ## `selHdl` -/

theorem selHdl_congr {p q : Nat → Bool} (h : ∀ i, p i = q i) :
    ∀ (Γ : List Ty) (vals : List (List Val)), selHdl p Γ vals = selHdl q Γ vals
  | [], _ => rfl
  | _ :: _, [] => rfl
  | t :: Γ, vs :: vals => by
    simp only [selHdl, h 0]
    rw [selHdl_congr (fun i => h (i + 1)) Γ vals]

theorem mem_selHdl {p : Nat → Bool} : ∀ {Γ : List Ty} {vals : List (List Val)} {h : Nat},
    h ∈ selHdl p Γ vals ↔ ∃ i t vs, Γ[i]? = some t ∧ vals[i]? = some vs ∧ p i = true ∧ h ∈ hdl t vs
  | [], _, _ => by simp [selHdl]
  | _ :: _, [], _ => by simp [selHdl]
  | t :: Γ, vs :: vals, h => by
    simp only [selHdl, List.mem_append]
    rw [mem_selHdl]
    constructor
    · rintro (hm | ⟨i, t', vs', h1, h2, h3, h4⟩)
      · split at hm
        · exact ⟨0, t, vs, rfl, rfl, by assumption, hm⟩
        · simp at hm
      · exact ⟨i + 1, t', vs', h1, h2, h3, h4⟩
    · rintro ⟨i, t', vs', h1, h2, h3, h4⟩
      cases i with
      | zero =>
        simp at h1 h2; subst h1; subst h2
        left; simp [h3, h4]
      | succ i => right; exact ⟨i, t', vs', h1, h2, h3, h4⟩

theorem selHdl_sublist {p q : Nat → Bool} (h : ∀ i, p i = true → q i = true) :
    ∀ (Γ : List Ty) (vals : List (List Val)), (selHdl p Γ vals).Sublist (selHdl q Γ vals)
  | [], _ => by simp [selHdl]
  | _ :: _, [] => by simp [selHdl]
  | t :: Γ, vs :: vals => by
    simp only [selHdl]
    apply List.Sublist.append
    · by_cases hp : p 0 = true
      · simp [hp, h 0 hp]
      · simp [hp]
    · exact selHdl_sublist (fun i hi => h (i + 1) hi) Γ vals

/-- Distinct selected variables have disjoint handles. -/
theorem selHdl_disj {p : Nat → Bool} : ∀ {Γ : List Ty} {vals : List (List Val)},
    (selHdl p Γ vals).Nodup → ∀ {i j : Nat} {ti tj : Ty} {vi vj : List Val} {h : Nat},
    Γ[i]? = some ti → vals[i]? = some vi → Γ[j]? = some tj → vals[j]? = some vj →
    p i = true → p j = true → h ∈ hdl ti vi → h ∈ hdl tj vj → i = j
  | [], _, _, _, _, _, _, _, _, _, h1, _, _, _, _, _, _, _ => by simp at h1
  | _ :: _, [], _, _, _, _, _, _, _, _, _, h2, _, _, _, _, _, _ => by simp at h2
  | t :: Γ, vs :: vals, hnd, i, j, ti, tj, vi, vj, h, h1, h2, h3, h4, hpi, hpj, hi, hj => by
    simp only [selHdl, List.nodup_append] at hnd
    cases i <;> cases j
    · rfl
    · exfalso
      simp at h1 h2; subst h1; subst h2
      exact hnd.2.2 h (by simp [hpi, hi]) h (mem_selHdl.2 ⟨_, _, _, h3, h4, hpj, hj⟩) rfl
    · exfalso
      simp at h3 h4; subst h3; subst h4
      exact hnd.2.2 h (by simp [hpj, hj]) h (mem_selHdl.2 ⟨_, _, _, h1, h2, hpi, hi⟩) rfl
    · rename_i i j
      exact congrArg (· + 1) (selHdl_disj hnd.2.1 h1 h2 h3 h4 hpi hpj hi hj)

theorem selHdl_nodup_one {p : Nat → Bool} : ∀ {Γ : List Ty} {vals : List (List Val)},
    (selHdl p Γ vals).Nodup → ∀ {i : Nat} {t : Ty} {vs : List Val},
    Γ[i]? = some t → vals[i]? = some vs → p i = true → (hdl t vs).Nodup
  | [], _, _, _, _, _, h1, _, _ => by simp at h1
  | _ :: _, [], _, _, _, _, _, h2, _ => by simp at h2
  | t :: Γ, vs :: vals, hnd, i, t', vs', h1, h2, hp => by
    simp only [selHdl, List.nodup_append] at hnd
    cases i with
    | zero => simp at h1 h2; subst h1; subst h2; simpa [hp] using hnd.1
    | succ i => exact selHdl_nodup_one hnd.2.1 h1 h2 hp

theorem selHdl_cons (p : Nat → Bool) (t : Ty) (Γ : List Ty) (vs : List Val)
    (vals : List (List Val)) :
    selHdl p (t :: Γ) (vs :: vals) =
      (if p 0 then hdl t vs else []) ++ selHdl (fun i => p (i + 1)) Γ vals := rfl

/-! ## `EnvRel` -/

variable {H H' : Heap} {r r' : Regs}

theorem EnvRel.get : ∀ {Γ : List Ty} {t : Ty} (v : DSL.Var Γ t) {ρ : DSL.Env Γ}
    {env : List (List ValueId)} {vals : List (List Val)} {st : DSL.CheckSt},
    EnvRel H r Γ ρ env vals st → alive st v.idx = true →
    RegsHas r (env.getD v.idx []) (vals.getD v.idx []) ∧ Enc H t (v.get ρ) (vals.getD v.idx []) ∧
    Γ[v.idx]? = some t ∧ vals[v.idx]? = some (vals.getD v.idx [])
  | _ :: _, _, .zero, ρ, ids :: env, vs :: vals, st, h, ha => by
    simp only [EnvRel] at h
    exact ⟨(h.1 ha).1, (h.1 ha).2, rfl, rfl⟩
  | _ :: _, _, .succ v, ρ, ids :: env, vs :: vals, st, h, ha => by
    simp only [EnvRel] at h
    simp only [DSL.Var.idx] at ha ⊢
    rw [← alive_tail] at ha
    exact EnvRel.get v h.2 ha
  | _ :: _, _, _, _, [], _, _, h, _ => by simp [EnvRel] at h
  | _ :: _, _, _, _, _ :: _, [], _, h, _ => by simp [EnvRel] at h

theorem EnvRel.weaken : ∀ {Γ : List Ty} {ρ : DSL.Env Γ} {env : List (List ValueId)}
    {vals : List (List Val)} {st st' : DSL.CheckSt},
    EnvRel H r Γ ρ env vals st → (∀ i, alive st' i = true → alive st i = true) →
    EnvRel H r Γ ρ env vals st'
  | [], _, _, _, _, _, _, _ => trivial
  | _ :: _, _, ids :: env, vs :: vals, st, st', h, hs => by
    simp only [EnvRel] at h ⊢
    exact ⟨fun ha => h.1 (hs 0 ha), EnvRel.weaken h.2 fun i hi => by
      rw [alive_tail] at hi ⊢; exact hs _ hi⟩
  | _ :: _, _, [], _, _, _, h, _ => by simp [EnvRel] at h
  | _ :: _, _, _ :: _, [], _, _, h, _ => by simp [EnvRel] at h

theorem EnvRel.regs : ∀ {Γ : List Ty} {ρ : DSL.Env Γ} {env : List (List ValueId)}
    {vals : List (List Val)} {st : DSL.CheckSt},
    EnvRel H r Γ ρ env vals st → (∀ ids ∈ env, ∀ x ∈ ids, r' x = r x) →
    EnvRel H r' Γ ρ env vals st
  | [], _, _, _, _, _, _ => trivial
  | _ :: _, _, ids :: env, vs :: vals, st, h, hr => by
    simp only [EnvRel] at h ⊢
    refine ⟨fun ha => ⟨?_, (h.1 ha).2⟩, EnvRel.regs h.2 fun ids hi => hr ids (List.mem_cons_of_mem _ hi)⟩
    have := (h.1 ha).1
    unfold RegsHas at this ⊢
    rw [← this]
    exact List.map_congr_left fun x hx => hr ids List.mem_cons_self x hx
  | _ :: _, _, [], _, _, h, _ => by simp [EnvRel] at h
  | _ :: _, _, _ :: _, [], _, h, _ => by simp [EnvRel] at h

theorem EnvRel.agree {n : Nat} {Γ : List Ty} {ρ : DSL.Env Γ} {env : List (List ValueId)}
    {vals : List (List Val)} {st : DSL.CheckSt}
    (h : EnvRel H r Γ ρ env vals st) (ha : Agree r r' n) (hids : EnvIds env n) :
    EnvRel H r' Γ ρ env vals st :=
  h.regs fun ids hi x hx => ha x (hids ids hi x hx)

theorem EnvRel.ext : ∀ {Γ : List Ty} {ρ : DSL.Env Γ} {env : List (List ValueId)}
    {vals : List (List Val)} {st : DSL.CheckSt},
    EnvRel H r Γ ρ env vals st → Ext H H' → EnvRel H' r Γ ρ env vals st
  | [], _, _, _, _, _, _ => trivial
  | _ :: _, _, ids :: env, vs :: vals, st, h, hx => by
    simp only [EnvRel] at h ⊢
    exact ⟨fun ha => ⟨(h.1 ha).1, (h.1 ha).2.ext hx⟩, EnvRel.ext h.2 hx⟩
  | _ :: _, _, [], _, _, h, _ => by simp [EnvRel] at h
  | _ :: _, _, _ :: _, [], _, h, _ => by simp [EnvRel] at h

/-- Objects of the alive variables unchanged: the relation survives a heap change. -/
theorem EnvRel.frame : ∀ {Γ : List Ty} {ρ : DSL.Env Γ} {env : List (List ValueId)}
    {vals : List (List Val)} {st : DSL.CheckSt},
    EnvRel H r Γ ρ env vals st → (∀ t ∈ Γ, t.wf = true) →
    (∀ h ∈ selHdl (alive st) Γ vals, H' h = H h) → EnvRel H' r Γ ρ env vals st
  | [], _, _, _, _, _, _, _ => trivial
  | t :: Γ, _, ids :: env, vs :: vals, st, h, hwf, hf => by
    simp only [EnvRel] at h ⊢
    rw [selHdl_cons] at hf
    refine ⟨fun ha => ⟨(h.1 ha).1, (h.1 ha).2.frame (vecOk_of_wf (hwf t List.mem_cons_self))
      fun x hx => hf x (List.mem_append_left _ (by simp [ha, hx]))⟩,
      EnvRel.frame h.2 (fun t ht => hwf t (List.mem_cons_of_mem _ ht)) fun x hx => ?_⟩
    apply hf x (List.mem_append_right _ _)
    rw [selHdl_congr (fun i => (alive_tail st i).symm)]; exact hx
  | _ :: _, _, [], _, _, h, _, _ => by simp [EnvRel] at h
  | _ :: _, _, _ :: _, [], _, h, _, _ => by simp [EnvRel] at h

theorem selHdl_alive_dom : ∀ {Γ : List Ty} {ρ : DSL.Env Γ} {env : List (List ValueId)}
    {vals : List (List Val)} {st : DSL.CheckSt},
    EnvRel H r Γ ρ env vals st → ∀ h ∈ selHdl (alive st) Γ vals, H h ≠ none
  | [], _, _, _, _, _ => by simp [selHdl]
  | _ :: _, _, ids :: env, vs :: vals, st, h => by
    simp only [EnvRel] at h
    intro x hx
    rw [selHdl_cons, List.mem_append] at hx
    rcases hx with hx | hx
    · by_cases ha : alive st 0 = true
      · simp [ha] at hx; exact (h.1 ha).2.hdl_dom x hx
      · simp [ha] at hx
    · rw [selHdl_congr (fun i => (alive_tail st i).symm)] at hx
      exact selHdl_alive_dom h.2 x hx
  | _ :: _, _, [], _, _, h => by simp [EnvRel] at h
  | _ :: _, _, _ :: _, [], _, h => by simp [EnvRel] at h

end Compile.Proof
