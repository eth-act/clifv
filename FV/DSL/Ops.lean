import FV.DSL.Ty

/-!
# Shallow operations

Ordinary Lean functions giving the meaning of every DSL primitive. `DSL.denote` is defined in
terms of these, and `flat def` generates shallow definitions that call exactly these, so
`denote_eq` holds by `rfl`. User proofs about shallow definitions use the lemmas here.

Notation (global, used both inside `flat def` bodies and in plain Lean):
`a +% b` `a -% b` `a *% b` (wrapping, `BitVec` `+ - *`), `a +? b` `a -? b` `a *? b`
(unsigned checked, `M`-valued).
-/

namespace DSL.Ops

variable {n : Nat}

/-! ## Arithmetic -/

/-- Unsigned checked add: throws `overflow` iff the mathematical sum is `≥ 2^n`. -/
def addC (a b : BitVec n) : M (BitVec n) :=
  if BitVec.uaddOverflow a b then throw .overflow else pure (a + b)

/-- Unsigned checked subtract: throws `overflow` iff `b > a`. -/
def subC (a b : BitVec n) : M (BitVec n) :=
  if BitVec.usubOverflow a b then throw .overflow else pure (a - b)

/-- Unsigned checked multiply: throws `overflow` iff the mathematical product is `≥ 2^n`. -/
def mulC (a b : BitVec n) : M (BitVec n) :=
  if BitVec.umulOverflow a b then throw .overflow else pure (a * b)

/-- Unsigned division; throws `divByZero` on a zero divisor. -/
def udiv (a b : BitVec n) : M (BitVec n) :=
  if b = 0 then throw .divByZero else pure (a / b)

/-- Unsigned remainder; throws `divByZero` on a zero divisor. -/
def urem (a b : BitVec n) : M (BitVec n) :=
  if b = 0 then throw .divByZero else pure (a % b)

/-- Shifts take the amount modulo the width (CLIF `ishl`/`ushr`/`sshr` semantics). -/
def shl (a b : BitVec n) : BitVec n := a <<< (b.toNat % n)
def lshr (a b : BitVec n) : BitVec n := a >>> (b.toNat % n)
def ashr (a b : BitVec n) : BitVec n := a.sshiftRight (b.toNat % n)

/-- Zero-extension (or truncation, when `w` is smaller) to width `w`. -/
def zext (w : Nat) (a : BitVec n) : BitVec w := a.setWidth w
def sext (w : Nat) (a : BitVec n) : BitVec w := a.signExtend w
def trunc (w : Nat) (a : BitVec n) : BitVec w := a.setWidth w

/-! ## Vectors -/

/-- Checked index (any index width); throws `indexOutOfBounds`. -/
def vget {α : Type} {len w : Nat} (v : Vector α len) (i : BitVec w) : M α :=
  if h : i.toNat < len then pure v[i.toNat] else throw .indexOutOfBounds

/-- Checked functional update; throws `indexOutOfBounds`. -/
def vset {α : Type} {len w : Nat} (v : Vector α len) (i : BitVec w) (x : α) : M (Vector α len) :=
  if h : i.toNat < len then pure (v.set i.toNat x h) else throw .indexOutOfBounds

/-! ## Maps -/

/-- Lookup; throws `notFound` on a missing key. -/
def mapGet {K V : Type} [DecidableEq K] (m : Map K V) (k : K) : M V :=
  match m.get? k with
  | some v => pure v
  | none => throw .notFound

/-! ## Loops -/

/-- Iteration `i, i+1, …` for `k` more steps. -/
def forRange.go {α : Type} (f : BitVec 64 → α → M α) : Nat → Nat → α → M α
  | 0, _, acc => pure acc
  | k + 1, i, acc => f (BitVec.ofNat 64 i) acc >>= go f k (i + 1)

/-- `for i in [0:n]` as a fold over an accumulator; stops at the first `throw`. -/
def forRange {α : Type} (n : Nat) (init : α) (f : BitVec 64 → α → M α) : M α :=
  forRange.go f n 0 init

end DSL.Ops

namespace DSL

infixl:65 " +% " => HAdd.hAdd (α := BitVec _) (β := BitVec _)
infixl:65 " -% " => HSub.hSub (α := BitVec _) (β := BitVec _)
infixl:70 " *% " => HMul.hMul (α := BitVec _) (β := BitVec _)
infixl:65 " +? " => DSL.Ops.addC
infixl:65 " -? " => DSL.Ops.subC
infixl:70 " *? " => DSL.Ops.mulC

/-! ## Lemmas for user proofs -/

namespace Ops

variable {α : Type}

@[simp] theorem ok_bind {β : Type} (a : α) (f : α → M β) : (Except.ok a >>= f : M β) = f a := rfl
@[simp] theorem error_bind {β : Type} (e : Err) (f : α → M β) :
    (Except.error e >>= f : M β) = Except.error e := rfl
@[simp] theorem pure_eq_ok (a : α) : (pure a : M α) = Except.ok a := rfl
@[simp] theorem throw_eq_error (e : Err) : (throw e : M α) = Except.error e := rfl

theorem addC_eq_ok {a b r : BitVec n} :
    addC a b = .ok r ↔ a.toNat + b.toNat < 2 ^ n ∧ r = a + b := by
  unfold addC BitVec.uaddOverflow
  by_cases h : a.toNat + b.toNat < 2 ^ n
  · have : ¬ (a.toNat + b.toNat ≥ 2 ^ n) := by omega
    simp [this, h, eq_comm]
  · have : a.toNat + b.toNat ≥ 2 ^ n := by omega
    simp [this, h]

theorem addC_ok {a b : BitVec n} (h : a.toNat + b.toNat < 2 ^ n) : addC a b = .ok (a + b) :=
  addC_eq_ok.2 ⟨h, rfl⟩

theorem addC_overflow {a b : BitVec n} (h : 2 ^ n ≤ a.toNat + b.toNat) :
    addC a b = .error .overflow := by
  simp [addC, BitVec.uaddOverflow, h]

theorem subC_ok {a b : BitVec n} (h : b.toNat ≤ a.toNat) : subC a b = .ok (a - b) := by
  simp [subC, BitVec.usubOverflow]; omega

theorem subC_overflow {a b : BitVec n} (h : a.toNat < b.toNat) :
    subC a b = .error .overflow := by
  simp [subC, BitVec.usubOverflow, h]

theorem mulC_ok {a b : BitVec n} (h : a.toNat * b.toNat < 2 ^ n) : mulC a b = .ok (a * b) := by
  simp [mulC, BitVec.umulOverflow]; omega

theorem vget_ok {len w : Nat} (v : Vector α len) (i : BitVec w) (h : i.toNat < len) :
    vget v i = .ok v[i.toNat] := by
  simp [vget, h]

theorem vget_oob {len w : Nat} (v : Vector α len) (i : BitVec w) (h : len ≤ i.toNat) :
    vget v i = .error .indexOutOfBounds := by
  simp [vget]; omega

theorem vset_ok {len w : Nat} (v : Vector α len) (i : BitVec w) (x : α) (h : i.toNat < len) :
    vset v i x = .ok (v.set i.toNat x h) := by
  simp [vset, h]

@[simp] theorem forRange_zero (init : α) (f : BitVec 64 → α → M α) :
    forRange 0 init f = pure init := rfl

theorem forRange.go_snoc (f : BitVec 64 → α → M α) :
    ∀ (k i : Nat) (acc : α),
      forRange.go f (k + 1) i acc = forRange.go f k i acc >>= f (BitVec.ofNat 64 (i + k))
  | 0, i, acc => by
    show (f (BitVec.ofNat 64 i) acc >>= fun a => pure a) = f (BitVec.ofNat 64 (i + 0)) acc
    cases f (BitVec.ofNat 64 i) acc <;> rfl
  | k + 1, i, acc => by
    rw [forRange.go]
    conv => rhs; rw [forRange.go]
    cases f (BitVec.ofNat 64 i) acc with
    | error e => rfl
    | ok a =>
      simp only [ok_bind]
      rw [forRange.go_snoc f k (i + 1) a]
      simp only [Nat.add_assoc, Nat.add_comm 1 k]

/-- Peel the last iteration. -/
theorem forRange_succ (n : Nat) (init : α) (f : BitVec 64 → α → M α) :
    forRange (n + 1) init f = forRange n init f >>= f (BitVec.ofNat 64 n) := by
  simp only [forRange, forRange.go_snoc, Nat.zero_add]

/-- Loop invariant rule (partial correctness): every successful result satisfies `P n`. -/
theorem forRange_inv (P : Nat → α → Prop) {n : Nat} {init : α} {f : BitVec 64 → α → M α}
    (h0 : P 0 init)
    (hstep : ∀ i, i < n → ∀ a b, P i a → f (BitVec.ofNat 64 i) a = .ok b → P (i + 1) b) :
    ∀ r, forRange n init f = .ok r → P n r := by
  induction n with
  | zero => intro r h; cases h; exact h0
  | succ n ih =>
    intro r h
    rw [forRange_succ] at h
    cases hm : forRange n init f with
    | error e => rw [hm] at h; cases h
    | ok a =>
      rw [hm] at h
      exact hstep n (by omega) a r (ih (fun i hi => hstep i (by omega)) a hm) h

/-- Loop invariant rule (total correctness): if each step succeeds and preserves `P`,
the loop succeeds with a result satisfying `P n`. -/
theorem forRange_ok (P : Nat → α → Prop) {n : Nat} {init : α} {f : BitVec 64 → α → M α}
    (h0 : P 0 init)
    (hstep : ∀ i, i < n → ∀ a, P i a → ∃ b, f (BitVec.ofNat 64 i) a = .ok b ∧ P (i + 1) b) :
    ∃ r, forRange n init f = .ok r ∧ P n r := by
  induction n with
  | zero => exact ⟨init, rfl, h0⟩
  | succ n ih =>
    obtain ⟨a, ha, hPa⟩ := ih (fun i hi => hstep i (by omega))
    obtain ⟨b, hb, hPb⟩ := hstep n (by omega) a hPa
    exact ⟨b, by rw [forRange_succ, ha]; exact hb, hPb⟩

end Ops
end DSL
