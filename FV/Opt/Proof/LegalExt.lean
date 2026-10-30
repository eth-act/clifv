import FV.Opt.Legal
import FV.Opt.Proof.LegalMem

/-!
# The ABI expansion of values and the environment contracts

`ExpRel gs vs vs'`: the values `vs'` of the legalised ABI represent the values `vs` of the
original by the slot groups `gs` (`Opt.Legalize128.expandGroups`): a plain value as itself, an
`i128` value as its low/high `i64` halves, a pad as an `i64` of any contents.

The contracts of the environment (the callees outside the program) the refinement theorem
assumes, proven for `Clif.Rust.env` in `FV/Opt/Proof/LegalRust.lean`:

* `HelperOk`: the `__*ti3` helper of a `div` at `i128` computes `Clif.Sem.div` on the halves
  (and traps where it traps);
* `ExtLegal`: an extern called with the arguments expanded by the ABI groups of its declared
  signature returns the expanded results (and traps where the original call traps);
* `EnvKeepsAllocs`: an extern returns with the caller's allocations.
-/

namespace Opt.Legal

open Clif Opt.Legalize128

/-- The low/high `i64` halves `a`/`b` of the `i128` value `v`. -/
def Halves (v a b : Val) : Prop :=
  ∃ l h : BitVec 64, v = ⟨.i128, h ++ l⟩ ∧ a = ⟨.i64, l⟩ ∧ b = ⟨.i64, h⟩

/-- The values `vs'` represent `vs` by the slot groups `gs` (pads: any `i64`; `x7` placement:
the value of the parameter after the pair first). -/
def ExpRel : List (List SlotEl) → List Val → List Val → Prop
  | [], [], [] => True
  | [.val _, .lo, .hi] :: [] :: gs, v :: u :: vs, u' :: a :: b :: vs' =>
    Halves v a b ∧ u' = u ∧ ExpRel gs vs vs'
  | [.val _] :: gs, v :: vs, v' :: vs' => v' = v ∧ ExpRel gs vs vs'
  | [.lo, .hi] :: gs, v :: vs, a :: b :: vs' => Halves v a b ∧ ExpRel gs vs vs'
  | [.pad, .lo, .hi] :: gs, v :: vs, w :: a :: b :: vs' =>
    w.ty = .i64 ∧ Halves v a b ∧ ExpRel gs vs vs'
  | _, _, _ => False

/-- The group of one parameter (`expandGroups`). -/
def GroupOf (p : AbiParam) (g : List SlotEl) : Prop :=
  (g = [.val p] ∧ p.ty ≠ .i128) ∨ (p.ty = .i128 ∧ (g = [.lo, .hi] ∨ g = [.pad, .lo, .hi]))

/-- The groups of a parameter list (`x7` placement: an `i128` parameter `p` and the next one
`q`, groups `[.val q, .lo, .hi]` and `[]`). -/
def GroupsOf : List AbiParam → List (List SlotEl) → Prop
  | [], [] => True
  | p :: ps, g :: gs => (GroupOf p g ∧ GroupsOf ps gs) ∨
      (p.ty = .i128 ∧ match ps, gs with
        | q :: ps, [] :: gs => g = [.val q, .lo, .hi] ∧ q.ty ≠ .i128 ∧ GroupsOf ps gs
        | _, _ => False)
  | _, _ => False

theorem groupsOf_cons {p : AbiParam} {ps : List AbiParam} {g : List SlotEl}
    {gs : List (List SlotEl)} : GroupsOf (p :: ps) (g :: gs) ↔ ((GroupOf p g ∧ GroupsOf ps gs) ∨
      (p.ty = .i128 ∧ match ps, gs with
        | q :: ps, [] :: gs => g = [.val q, .lo, .hi] ∧ q.ty ≠ .i128 ∧ GroupsOf ps gs
        | _, _ => False)) := by
  rw [GroupsOf.eq_def]

theorem except_bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem groupsOf_go : ∀ (ps : List AbiParam) (k v st : Nat) (hole : Bool)
    (gs : List (List SlotEl)), expandGroups.go ps k v st hole = .ok gs → GroupsOf ps gs
  | [], k, v, st, hole, gs, h => by
    simp only [expandGroups.go] at h
    cases h; trivial
  | p :: ps, k, v, st, hole, gs, h => by
    rw [expandGroups.go.eq_def] at h
    dsimp only at h
    by_cases hp : (p.ty == .i128) = true
    · rw [if_pos hp] at h
      have hpt : p.ty = .i128 := by simpa using hp
      by_cases h1 : (p.ext != .none) = true
      · rw [if_pos h1] at h; cases h
      rw [if_neg h1] at h
      by_cases h2 : (p.purpose != .normal) = true
      · rw [if_pos h2] at h; cases h
      rw [if_neg h2] at h
      split at h
      · obtain ⟨rest, hr, h⟩ := except_bind_ok h
        cases h
        refine groupsOf_cons.2 (.inl ⟨.inr ⟨hpt, ?_⟩, groupsOf_go ps _ _ _ _ rest hr⟩)
        split <;> simp
      split at h
      · split at h
        · rcases ps with _ | ⟨q, qs⟩
          · obtain ⟨rest, hr, h⟩ := except_bind_ok h
            cases h
            exact groupsOf_cons.2 (.inl ⟨.inr ⟨hpt, .inr rfl⟩, groupsOf_go [] _ _ _ _ rest hr⟩)
          · dsimp only at h
            split at h
            · rename_i hq
              obtain ⟨rest, hr, h⟩ := except_bind_ok h
              cases h
              have hq' : q.ty ≠ .i128 := fun e => by simp [e] at hq
              exact groupsOf_cons.2 (.inr ⟨hpt, rfl, hq', groupsOf_go qs _ _ _ _ rest hr⟩)
            · obtain ⟨rest, hr, h⟩ := except_bind_ok h
              cases h
              exact groupsOf_cons.2
                (.inl ⟨.inr ⟨hpt, .inr rfl⟩, groupsOf_go (q :: qs) _ _ _ _ rest hr⟩)
        · cases h
      split at h
      · obtain ⟨rest, hr, h⟩ := except_bind_ok h
        cases h
        exact groupsOf_cons.2 (.inl ⟨.inr ⟨hpt, .inl rfl⟩, groupsOf_go ps _ _ _ _ rest hr⟩)
      · obtain ⟨rest, hr, h⟩ := except_bind_ok h
        cases h
        exact groupsOf_cons.2 (.inl ⟨.inr ⟨hpt, .inr rfl⟩, groupsOf_go ps _ _ _ _ rest hr⟩)
    · rw [if_neg hp] at h
      have hpt : p.ty ≠ .i128 := by simpa using hp
      split at h
      · obtain ⟨rest, hr, h⟩ := except_bind_ok h
        cases h
        exact groupsOf_cons.2 (.inl ⟨.inl ⟨rfl, hpt⟩, groupsOf_go ps _ _ _ _ rest hr⟩)
      split at h
      · obtain ⟨rest, hr, h⟩ := except_bind_ok h
        cases h
        exact groupsOf_cons.2 (.inl ⟨.inl ⟨rfl, hpt⟩, groupsOf_go ps _ _ _ _ rest hr⟩)
      split at h
      · obtain ⟨rest, hr, h⟩ := except_bind_ok h
        cases h
        exact groupsOf_cons.2 (.inl ⟨.inl ⟨rfl, hpt⟩, groupsOf_go ps _ _ _ _ rest hr⟩)
      split at h
      · cases h
      · obtain ⟨rest, hr, h⟩ := except_bind_ok h
        cases h
        exact groupsOf_cons.2 (.inl ⟨.inl ⟨rfl, hpt⟩, groupsOf_go ps _ _ _ _ rest hr⟩)

theorem groups_spec {ps : List AbiParam} {gs : List (List SlotEl)} (h : groups ps = some gs) :
    GroupsOf ps gs := by
  simp only [groups, expandGroups] at h
  cases hr : expandGroups.go ps 0 0 0 false with
  | error e => simp [hr, Except.toOption] at h
  | ok gs' =>
    simp [hr, Except.toOption] at h
    subst h
    exact groupsOf_go ps 0 0 0 false gs' hr

/-- The types of the expanded values are those of the expanded parameters. -/
theorem expRel_tys : ∀ {ps : List AbiParam} {gs : List (List SlotEl)} {vs vs' : List Val},
    GroupsOf ps gs → ExpRel gs vs vs' → vs.map (·.ty) = ps.map (·.ty) →
    vs'.map (·.ty) = (gs.flatMap (·.map elTy)).map (·.ty)
  | [], [], [], vs', _, he, _ => by
    cases vs' with
    | nil => rfl
    | cons => simp [ExpRel] at he
  | p :: ps, g :: gs, v :: vs, vs', hg, he, ht => by
    rcases groupsOf_cons.1 hg with ⟨hg1, hg2⟩ | ⟨hpt, hx⟩
    rotate_left
    · -- `x7` placement: the next value first, then the pair
      rcases ps with _ | ⟨q, qs⟩ <;> rcases gs with _ | ⟨g2, gs2⟩
      · cases hx
      · cases hx
      · cases hx
      rcases g2 with _ | ⟨e, es⟩
      rotate_left
      · cases hx
      obtain ⟨rfl, -, hg2⟩ := hx
      rcases vs with _ | ⟨u, vs2⟩
      · simp at ht
      rcases vs' with _ | ⟨u', _ | ⟨a, _ | ⟨b, vs3⟩⟩⟩
      · simp [ExpRel] at he
      · simp [ExpRel] at he
      · simp [ExpRel] at he
      simp only [ExpRel] at he
      obtain ⟨⟨l, h, -, rfl, rfl⟩, rfl, he⟩ := he
      simp only [List.map_cons, List.cons.injEq] at ht
      simp only [List.flatMap_cons, List.map_cons, List.map_nil, List.cons_append,
        List.nil_append, elTy, ht.2.1]
      rw [expRel_tys hg2 he ht.2.2]
    simp only [List.map_cons, List.cons.injEq] at ht
    rcases hg1 with ⟨rfl, -⟩ | ⟨hpt, rfl | rfl⟩
    · rcases vs' with _ | ⟨v', vs'⟩
      · simp [ExpRel] at he
      · simp only [ExpRel] at he
        obtain ⟨rfl, he⟩ := he
        simp only [List.flatMap_cons, List.map_cons, List.map_nil, List.cons_append,
          List.nil_append, elTy, ht.1]
        rw [expRel_tys hg2 he ht.2]
    · rcases vs' with _ | ⟨a, _ | ⟨b, vs'⟩⟩
      · simp [ExpRel] at he
      · simp [ExpRel] at he
      · simp only [ExpRel] at he
        obtain ⟨⟨l, h, -, rfl, rfl⟩, he⟩ := he
        simp only [List.flatMap_cons, List.map_cons, List.map_nil, List.cons_append,
          List.nil_append, elTy]
        rw [expRel_tys hg2 he ht.2]
    · rcases vs' with _ | ⟨w, _ | ⟨a, _ | ⟨b, vs'⟩⟩⟩
      · simp [ExpRel] at he
      · simp [ExpRel] at he
      · simp [ExpRel] at he
      · simp only [ExpRel] at he
        obtain ⟨hw, ⟨l, h, -, rfl, rfl⟩, he⟩ := he
        simp only [List.flatMap_cons, List.map_cons, List.map_nil, List.cons_append,
          List.nil_append, elTy, hw]
        rw [expRel_tys hg2 he ht.2]
  | [], _ :: _, _, _, hg, _, _ => by cases hg
  | _ :: _, [], _, _, hg, _, _ => by cases hg
  | [], [], _ :: _, _, _, he, _ => by simp [ExpRel] at he
  | _ :: _, _ :: _, [], _, _, _, ht => by cases ht

/-- Without `i128` values the expansion is the identity. -/
theorem expRel_val : ∀ {ps : List AbiParam} {gs : List (List SlotEl)} {vs vs' : List Val},
    GroupsOf ps gs → (∀ p ∈ ps, p.ty ≠ .i128) → ExpRel gs vs vs' → vs' = vs
  | [], [], [], vs', _, _, he => by
    cases vs' with
    | nil => rfl
    | cons => simp [ExpRel] at he
  | p :: ps, g :: gs, v :: vs, vs', hg, hn, he => by
    rcases groupsOf_cons.1 hg with ⟨hg1, hg2⟩ | ⟨hpt, -⟩
    rotate_left
    · exact absurd hpt (hn p (List.mem_cons_self ..))
    rcases hg1 with ⟨rfl, -⟩ | ⟨hpt, -⟩
    · rcases vs' with _ | ⟨v', vs'⟩
      · simp [ExpRel] at he
      · simp only [ExpRel] at he
        obtain ⟨rfl, he⟩ := he
        rw [expRel_val hg2 (fun q hq => hn q (List.mem_cons_of_mem _ hq)) he]
    · exact absurd hpt (hn p (List.mem_cons_self ..))
  | [], _ :: _, _, _, hg, _, _ => by cases hg
  | _ :: _, [], _, _, hg, _, _ => by cases hg
  | [], [], _ :: _, _, _, _, he => by simp [ExpRel] at he
  | _ :: _, g :: _, [], vs', _, _, he => by
    rcases g with _ | ⟨e, _ | ⟨e2, _ | ⟨e3, _ | _⟩⟩⟩ <;> (try cases e) <;> (try cases e2) <;>
      (try cases e3) <;> simp [ExpRel] at he

/-! ## The ABI expansion without `i128` -/

theorem expRel_refl_plain : ∀ {ps : List AbiParam} {gs : List (List SlotEl)} {vs : List Val},
    GroupsOf ps gs → (∀ p ∈ ps, p.ty ≠ .i128) → vs.length = ps.length → ExpRel gs vs vs
  | [], [], [], _, _, _ => trivial
  | p :: ps, g :: gs, v :: vs, hg, hn, hl => by
    rcases groupsOf_cons.1 hg with ⟨hg1, hg2⟩ | ⟨hpt, -⟩
    rotate_left
    · exact absurd hpt (hn p (List.mem_cons_self ..))
    rcases hg1 with ⟨rfl, -⟩ | ⟨hpt, -⟩
    · exact ⟨rfl, expRel_refl_plain hg2 (fun q hq => hn q (List.mem_cons_of_mem _ hq))
        (by simpa using hl)⟩
    · exact absurd hpt (hn p (List.mem_cons_self ..))
  | [], _ :: _, _, hg, _, _ => by cases hg
  | _ :: _, [], _, hg, _, _ => by cases hg
  | [], [], _ :: _, _, _, hl => by simp at hl
  | _ :: _, _ :: _, [], _, _, hl => by simp at hl

theorem sig128_params {s : Signature} (h : sig128 s = false) : ∀ p ∈ s.params, p.ty ≠ .i128 := by
  simp only [sig128, List.any_eq_false, beq_iff_eq, List.mem_append] at h
  exact fun p hp => h p (.inl hp)

theorem sig128_returns {s : Signature} (h : sig128 s = false) : ∀ p ∈ s.returns, p.ty ≠ .i128 := by
  simp only [sig128, List.any_eq_false, beq_iff_eq, List.mem_append] at h
  exact fun p hp => h p (.inr hp)

theorem groups_plain {ps : List AbiParam} (h : ∀ p ∈ ps, p.ty ≠ .i128) :
    ∃ gs, groups ps = some gs ∧ GroupsOf ps gs := by
  have hgs : groups ps = some (ps.map fun p => [SlotEl.val p]) := by
    simp [groups, expandGroups, Complete.go_plain ps 0 0 0 h, Except.toOption]
  exact ⟨_, hgs, groups_spec hgs⟩

/-- A signature without `i128` whose parameter and return types are another's: the other has no
`i128` either. -/
theorem sig128_of_tys {d s : Signature} (hd : sig128 d = false)
    (hp : AbiParam.tys d.params = AbiParam.tys s.params)
    (hr : AbiParam.tys d.returns = AbiParam.tys s.returns) : sig128 s = false := by
  simp only [sig128, List.any_eq_false, beq_iff_eq, List.mem_append] at hd ⊢
  intro p hp'
  rcases hp' with hp' | hp'
  · have : p.ty ∈ AbiParam.tys s.params := List.mem_map_of_mem hp'
    rw [← hp] at this
    obtain ⟨q, hq, he⟩ := List.mem_map.mp this
    rw [← he]; exact hd q (.inl hq)
  · have : p.ty ∈ AbiParam.tys s.returns := List.mem_map_of_mem hp'
    rw [← hr] at this
    obtain ⟨q, hq, he⟩ := List.mem_map.mp this
    rw [← he]; exact hd q (.inr hq)

/-! ## Environment contracts -/

/-- The `__*ti3` helpers compute `Sem.div` at `i128` on the halves. -/
def HelperOk (env : Env) : Prop :=
  ∀ op : DivOp, ∃ h, env.extern (divHelper op) = some h ∧ ∀ (xl xh yl yh : BitVec 64) (m : Mem),
    match Sem.div op (xh ++ xl) (yh ++ yl) with
    | .ok r => h [⟨.i64, xl⟩, ⟨.i64, xh⟩, ⟨.i64, yl⟩, ⟨.i64, yh⟩] m =
        .returned [⟨.i64, r.extractLsb' 0 64⟩, ⟨.i64, r.extractLsb' 64 64⟩] m
    | .error c => h [⟨.i64, xl⟩, ⟨.i64, xh⟩, ⟨.i64, yl⟩, ⟨.i64, yh⟩] m = .trapped c

/-- An extern called with the arguments expanded by the groups of its declared signature
returns the expanded results, and traps where the original call traps. -/
def ExtLegal (env : Env) : Prop :=
  ∀ name h, env.extern name = some h → ∀ (sig : Signature) gs rg,
    groups sig.params = some gs → groups sig.returns = some rg →
    ∀ vals vals' m, vals.map (·.ty) = AbiParam.tys sig.params → ExpRel gs vals vals' →
    (∀ rv m', h vals m = .returned rv m' → rv.map (·.ty) = AbiParam.tys sig.returns →
      ∃ rv', h vals' m = .returned rv' m' ∧ ExpRel rg rv rv') ∧
    (∀ c, h vals m = .trapped c → h vals' m = .trapped c)

/-- Externs return with the caller's allocations. -/
def EnvKeepsAllocs (env : Env) : Prop :=
  ∀ name h, env.extern name = some h → ∀ vals m rv m', h vals m = .returned rv m' →
    m'.allocs = m.allocs

theorem memBounded_of_allocs {m m' : Mem} (h : m'.allocs = m.allocs) (hm : MemBounded m) :
    MemBounded m' := by
  intro a n hv
  exact hm a n (by simpa [Mem.valid, h] using hv)

end Opt.Legal
