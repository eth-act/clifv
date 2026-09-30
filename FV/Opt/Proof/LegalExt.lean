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

/-- The values `vs'` represent `vs` by the slot groups `gs` (pads: any `i64`). -/
def ExpRel : List (List SlotEl) → List Val → List Val → Prop
  | [], [], [] => True
  | [.val _] :: gs, v :: vs, v' :: vs' => v' = v ∧ ExpRel gs vs vs'
  | [.lo, .hi] :: gs, v :: vs, a :: b :: vs' => Halves v a b ∧ ExpRel gs vs vs'
  | [.pad, .lo, .hi] :: gs, v :: vs, w :: a :: b :: vs' =>
    w.ty = .i64 ∧ Halves v a b ∧ ExpRel gs vs vs'
  | _, _, _ => False

/-- The group of one parameter (`expandGroups`). -/
def GroupOf (p : AbiParam) (g : List SlotEl) : Prop :=
  (g = [.val p] ∧ p.ty ≠ .i128) ∨ (p.ty = .i128 ∧ (g = [.lo, .hi] ∨ g = [.pad, .lo, .hi]))

/-- The groups of a parameter list. -/
def GroupsOf : List AbiParam → List (List SlotEl) → Prop
  | [], [] => True
  | p :: ps, g :: gs => GroupOf p g ∧ GroupsOf ps gs
  | _, _ => False

theorem except_bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem groupsOf_go : ∀ (ps : List AbiParam) (k : Nat) (gs : List (List SlotEl)),
    expandGroups.go ps k = .ok gs → GroupsOf ps gs
  | [], k, gs, h => by
    simp only [expandGroups.go] at h
    cases h; trivial
  | p :: ps, k, gs, h => by
    rw [expandGroups.go] at h
    by_cases hp : (p.ty == .i128) = true
    · rw [if_pos hp] at h
      by_cases h1 : (p.ext != .none) = true
      · rw [if_pos h1] at h; cases h
      rw [if_neg h1] at h
      by_cases h2 : (p.purpose != .normal) = true
      · rw [if_pos h2] at h; cases h
      rw [if_neg h2] at h
      by_cases h3 : 8 < k + 2
      · rw [if_pos h3] at h; cases h
      rw [if_neg h3] at h
      obtain ⟨rest, hr, h⟩ := except_bind_ok h
      cases h
      refine ⟨.inr ⟨by simpa using hp, ?_⟩, groupsOf_go ps _ rest hr⟩
      split <;> simp
    · rw [if_neg hp] at h
      obtain ⟨rest, hr, h⟩ := except_bind_ok h
      cases h
      exact ⟨.inl ⟨rfl, by simpa using hp⟩, groupsOf_go ps _ rest hr⟩

theorem groups_spec {ps : List AbiParam} {gs : List (List SlotEl)} (h : groups ps = some gs) :
    GroupsOf ps gs := by
  simp only [groups, expandGroups] at h
  cases hr : expandGroups.go ps 0 with
  | error e => simp [hr, Except.toOption] at h
  | ok gs' =>
    simp [hr, Except.toOption] at h
    subst h
    exact groupsOf_go ps 0 gs' hr

/-- The types of the expanded values are those of the expanded parameters. -/
theorem expRel_tys : ∀ {ps : List AbiParam} {gs : List (List SlotEl)} {vs vs' : List Val},
    GroupsOf ps gs → ExpRel gs vs vs' → vs.map (·.ty) = ps.map (·.ty) →
    vs'.map (·.ty) = (gs.flatMap (·.map elTy)).map (·.ty)
  | [], [], [], vs', _, he, _ => by
    cases vs' with
    | nil => rfl
    | cons => simp [ExpRel] at he
  | p :: ps, g :: gs, v :: vs, vs', hg, he, ht => by
    simp only [List.map_cons, List.cons.injEq] at ht
    obtain ⟨hg1, hg2⟩ := hg
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
    obtain ⟨hg1, hg2⟩ := hg
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
