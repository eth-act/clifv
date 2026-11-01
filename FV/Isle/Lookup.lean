import FV.Isle.Interp

/-!
# Kernel-cheap lookups of a program's terms and rules

The abstract checkers behind the instruction-selection tables (`IselPrgCheck`, `IselCovTCheck`,
`IselSzTDefs`, `IselEmitTFns`) are decided by kernel evaluation (`decide +kernel`). They look up
the term `Interp.termOf p t` and the rules `p.rulesOf t` of a `TermId` at every pattern,
application and table entry. Both index an `Array` of about 2,500 entries, which the kernel
evaluates as a walk down its `List`: about 1,250 steps per lookup on average, which dominated the
`IselPrgTab*` checks.

`termOfT p t` and `rulesOfT p t` look the same values up through `strideGet?`: every 256th tail
of the list, then every 16th tail of that one, then at most 15 steps. The kernel caches the
reductions of these tails within one declaration, so a lookup costs at most 39 list steps once
the tails it passes are built (each tail is built once: a few thousand steps per declaration).
They equal `termOf`/`rulesOf` for every program (`termOfT_eq`, `rulesOfT_eq`), so the checkers'
soundness proofs carry over by rewriting.
-/

namespace Isle

namespace Lookup

variable {α : Type}

/-- The non-empty tails `xs.drop (k * i)` for `i < n`. -/
def strides (k : Nat) : Nat → List α → List (List α)
  | 0, _ => []
  | _ + 1, [] => []
  | n + 1, x :: xs => (x :: xs) :: strides k n ((x :: xs).drop k)

theorem strides_some (k : Nat) : ∀ (n : Nat) (xs : List α) (i : Nat), i < n → k * i < xs.length →
    (strides k n xs)[i]? = some (xs.drop (k * i))
  | 0, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | _ + 1, [], _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, x :: xs, 0, _, _ => by rw [Nat.mul_zero, List.drop_zero]; rfl
  | n + 1, x :: xs, i + 1, h1, h2 => by
    rw [Nat.mul_succ] at h2
    rw [strides, List.getElem?_cons_succ, strides_some k n _ i (Nat.lt_of_succ_lt_succ h1)
      (by rw [List.length_drop]; omega), List.drop_drop, Nat.mul_succ, Nat.add_comm (k * i) k]

theorem strides_none (k : Nat) : ∀ (n : Nat) (xs : List α) (i : Nat), n ≤ i ∨ xs.length ≤ k * i →
    (strides k n xs)[i]? = none
  | 0, _, _, _ => rfl
  | _ + 1, [], _, _ => rfl
  | n + 1, x :: xs, 0, h => h.elim (fun h => absurd h (Nat.not_succ_le_zero _))
    (fun h => absurd h (by rw [Nat.mul_zero]; exact Nat.not_succ_le_zero _))
  | n + 1, x :: xs, i + 1, h => by
    rw [strides, List.getElem?_cons_succ]
    exact strides_none k n _ i (h.elim (fun h => Or.inl (Nat.le_of_succ_le_succ h))
      fun h => Or.inr (by rw [List.length_drop]; rw [Nat.mul_succ] at h; omega))

/-- `xs[t]?` (`strideGet?_eq`), through every 256th tail of `xs`, then every 16th tail of
that one. -/
def strideGet? (xs : List α) (t : Nat) : Option α :=
  match (strides 256 xs.length xs)[t / 256]? with
  | none => none
  | some ys =>
    match (strides 16 16 ys)[t % 256 / 16]? with
    | none => none
    | some zs => zs[t % 16]?

theorem strideGet?_eq (xs : List α) (t : Nat) : strideGet? xs t = xs[t]? := by
  unfold strideGet?
  rcases Nat.lt_or_ge (256 * (t / 256)) xs.length with h1 | h1
  · rw [strides_some _ _ _ _ (by omega) h1]
    dsimp only
    rcases Nat.lt_or_ge (16 * (t % 256 / 16)) (xs.drop (256 * (t / 256))).length with h2 | h2
    · rw [strides_some _ _ _ _ (by omega) h2]
      dsimp only
      rw [List.getElem?_drop, List.getElem?_drop]
      congr 1
      omega
    · rw [strides_none _ _ _ _ (Or.inr h2)]
      rw [List.length_drop] at h2
      exact (List.getElem?_eq_none_iff.mpr (by omega)).symm
  · rw [strides_none _ _ _ _ (Or.inr h1)]
    exact (List.getElem?_eq_none_iff.mpr (by omega)).symm


end Lookup

/-- `Interp.termOf p t`, by `strideGet?` (`termOfT_eq`). -/
def termOfT (p : Program) (t : TermId) : Except Err Term :=
  match Lookup.strideGet? p.terms.toList t with
  | some term => pure term
  | none => throw (.malformed s!"unknown term {t}")

/-- `p.rulesOf t`, by `strideGet?` (`rulesOfT_eq`). -/
def rulesOfT (p : Program) (t : TermId) : List Rule :=
  (Lookup.strideGet? p.ruleLists.toList t).getD []

theorem termOfT_eq (p : Program) (t : TermId) : termOfT p t = Interp.termOf p t := by
  rw [termOfT, Lookup.strideGet?_eq, Array.getElem?_toList]
  rfl

theorem rulesOfT_eq (p : Program) (t : TermId) : rulesOfT p t = p.rulesOf t := by
  rw [rulesOfT, Lookup.strideGet?_eq, Array.getElem?_toList]
  rfl

end Isle
