import FV.DSL.Map

/-!
# DSL types, errors, and the effect monad

`Ty` is the object-language type grammar; `Ty.denote` maps it to Lean types.
Machine integers are width-indexed (`Ty.int w`) so that every integer operation is stated
once, generically in the width; `Ty.u8 … Ty.u64` are pattern-matchable abbreviations.
-/

namespace DSL

/-- Machine-integer widths (the CLIF emitter subset has `i8 i16 i32 i64`). -/
inductive IntW
  | w8 | w16 | w32 | w64
  deriving DecidableEq, Repr, Inhabited

@[reducible] def IntW.bits : IntW → Nat
  | .w8 => 8
  | .w16 => 16
  | .w32 => 32
  | .w64 => 64

theorem IntW.bits_pos (w : IntW) : 0 < w.bits := by cases w <;> decide

inductive Ty
  | int (w : IntW)
  | bool
  | unit
  /-- Fixed-size vector, denotes `Vector t.denote n`. -/
  | vec (n : Nat) (t : Ty)
  | prod (a b : Ty)
  /-- Abstract finite map (runtime collection), denotes `DSL.Map k.denote v.denote`. -/
  | map (k v : Ty)
  deriving DecidableEq, Repr, Inhabited

namespace Ty

@[match_pattern] abbrev u8 : Ty := .int .w8
@[match_pattern] abbrev u16 : Ty := .int .w16
@[match_pattern] abbrev u32 : Ty := .int .w32
@[match_pattern] abbrev u64 : Ty := .int .w64

@[reducible] def denote : Ty → Type
  | .int w => BitVec w.bits
  | .bool => Bool
  | .unit => Unit
  | .vec n t => Vector t.denote n
  | .prod a b => a.denote × b.denote
  | .map k v => Map k.denote v.denote

instance decEq : (t : Ty) → DecidableEq t.denote
  | .int w => inferInstanceAs (DecidableEq (BitVec w.bits))
  | .bool => inferInstanceAs (DecidableEq Bool)
  | .unit => inferInstanceAs (DecidableEq Unit)
  | .vec n t =>
    have := decEq t
    inferInstanceAs (DecidableEq (Vector t.denote n))
  | .prod a b =>
    have := decEq a; have := decEq b
    inferInstanceAs (DecidableEq (a.denote × b.denote))
  | .map k v =>
    have := decEq k; have := decEq v
    inferInstanceAs (DecidableEq (Map k.denote v.denote))

instance instRepr : (t : Ty) → Repr t.denote
  | .int w => inferInstanceAs (Repr (BitVec w.bits))
  | .bool => inferInstanceAs (Repr Bool)
  | .unit => inferInstanceAs (Repr Unit)
  | .vec n t =>
    have := instRepr t
    inferInstanceAs (Repr (Vector t.denote n))
  | .prod a b =>
    have := instRepr a; have := instRepr b
    inferInstanceAs (Repr (a.denote × b.denote))
  | .map k v =>
    have := instRepr k; have := instRepr v
    inferInstanceAs (Repr (Map k.denote v.denote))

/-- Default (zero) value of each type: zero integers, `false`, zero-filled vectors, the
empty map. The error-tag ABI zero-fills the payload on `throw`; this is its Lean shadow. -/
def default : (t : Ty) → t.denote
  | .int _ => 0
  | .bool => false
  | .unit => ()
  | .vec n t => Vector.replicate n t.default
  | .prod a b => (a.default, b.default)
  | .map _ _ => ⟨[]⟩

instance (t : Ty) : Inhabited t.denote := ⟨t.default⟩

/-- Scalar types live in SSA values; all others are memory-backed aggregates. -/
def isScalar : Ty → Bool
  | .int _ | .bool | .unit => true
  | _ => false

/-- Types subject to the affine rule: those containing a vector or a map (memory-backed,
updated in place). Scalars and tuples of scalars are freely copyable. -/
def linear : Ty → Bool
  | .int _ | .bool | .unit => false
  | .vec _ _ | .map _ _ => true
  | .prod a b => a.linear || b.linear

end Ty

/-! ## Errors and the error-tag ABI -/

/-- The single error type of the DSL. Built-ins plus 200 user codes. -/
inductive Err
  | overflow
  | divByZero
  | indexOutOfBounds
  | notFound
  | user (code : Fin 200)
  deriving DecidableEq, Repr, Inhabited

namespace Err

/-- First tag of the user range. Tags `5 … 55` are reserved for future built-ins. -/
def userBase : Nat := 56

/-- Error-tag ABI (docs/ARCHITECTURE.md): `0` is `ok`, `tag e ∈ [1, 255]` is `throw e`. -/
def tag : Err → Nat
  | overflow => 1
  | divByZero => 2
  | indexOutOfBounds => 3
  | notFound => 4
  | user c => userBase + c.val

def ofTag (k : Nat) : Option Err :=
  if k = 1 then some overflow
  else if k = 2 then some divByZero
  else if k = 3 then some indexOutOfBounds
  else if k = 4 then some notFound
  else if h : userBase ≤ k ∧ k < 256 then some (user ⟨k - userBase, by simp [userBase] at *; omega⟩)
  else none

theorem tag_pos (e : Err) : 0 < e.tag := by
  cases e <;> simp only [tag, userBase] <;> omega

theorem tag_lt (e : Err) : e.tag < 256 := by
  cases e with
  | user c => have := c.isLt; simp [tag, userBase]; omega
  | _ => simp [tag]

@[simp] theorem ofTag_tag (e : Err) : ofTag e.tag = some e := by
  cases e with
  | user c =>
    have := c.isLt
    have h1 : (user c).tag ≠ 1 := by simp only [tag, userBase]; omega
    have h2 : (user c).tag ≠ 2 := by simp only [tag, userBase]; omega
    have h3 : (user c).tag ≠ 3 := by simp only [tag, userBase]; omega
    have h4 : (user c).tag ≠ 4 := by simp only [tag, userBase]; omega
    have h5 : userBase ≤ (user c).tag ∧ (user c).tag < 256 := by
      simp only [tag, userBase]; omega
    simp only [ofTag, h1, h2, h3, h4, h5, ↓reduceIte, ↓reduceDIte, and_self]
    simp [tag, userBase]
  | _ => rfl

theorem tag_injective {e₁ e₂ : Err} (h : e₁.tag = e₂.tag) : e₁ = e₂ := by
  have := ofTag_tag e₁
  rw [h, ofTag_tag] at this
  exact (Option.some.inj this).symm

theorem tag_ofTag {k : Nat} {e : Err} (h : ofTag k = some e) : e.tag = k := by
  unfold ofTag at h
  split at h
  · cases h; subst_vars; rfl
  split at h
  · cases h; subst_vars; rfl
  split at h
  · cases h; subst_vars; rfl
  split at h
  · cases h; subst_vars; rfl
  split at h
  next hk => cases h; simp only [tag, userBase] at hk ⊢; omega
  · cases h

/-- The tag as the `i8` returned by compiled functions. -/
def tag8 (e : Err) : BitVec 8 := BitVec.ofNat 8 e.tag

theorem tag8_toNat (e : Err) : e.tag8.toNat = e.tag := by
  simp [tag8, Nat.mod_eq_of_lt (tag_lt e)]

end Err

/-- The only effect of the DSL. -/
abbrev M := Except Err

/-- `Except` has no core `DecidableEq`; needed for `#guard` on `M` results. -/
instance instDecidableEqExcept {ε α : Type} [DecidableEq ε] [DecidableEq α] :
    DecidableEq (Except ε α)
  | .ok a, .ok b => if h : a = b then isTrue (h ▸ rfl) else isFalse (by intro h'; cases h'; exact h rfl)
  | .error a, .error b => if h : a = b then isTrue (h ▸ rfl) else isFalse (by intro h'; cases h'; exact h rfl)
  | .ok _, .error _ => isFalse (by intro h; cases h)
  | .error _, .ok _ => isFalse (by intro h; cases h)

end DSL
