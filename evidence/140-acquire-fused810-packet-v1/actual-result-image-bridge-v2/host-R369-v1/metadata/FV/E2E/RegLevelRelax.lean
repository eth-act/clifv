import FV.E2E.RegLevelEmit

/-!
# Branch relaxation on line lists (M6)

`emitFunc`'s lines are `relaxLines far` of the lines before relaxation (`emitFunc_ok`):
`relaxLines` maps each line on its own (`relaxLine`), so it distributes over `++`, keeps labels,
jump-table words and plain lines (`relaxLines_plain`), and rewrites only a relaxable branch to a
far label, into `b.!c .+8; b T` (`relaxLine_far`).
-/

namespace Backend

@[simp] theorem relaxLines_nil (f : Lbl → Bool) : relaxLines f [] = [] := rfl

theorem relaxLines_cons (f : Lbl → Bool) (ln : Line) (A : List Line) :
    relaxLines f (ln :: A) = relaxLine f ln ++ relaxLines f A := by
  simp [relaxLines]

theorem relaxLines_append (f : Lbl → Bool) (A B : List Line) :
    relaxLines f (A ++ B) = relaxLines f A ++ relaxLines f B := by
  simp [relaxLines]

@[simp] theorem relaxLine_label (f : Lbl → Bool) (l : Lbl) : relaxLine f (.label l) = [.label l] := rfl

@[simp] theorem relaxLine_word (f : Lbl → Bool) (t b : Lbl) :
    relaxLine f (.word t b) = [.word t b] := rfl

theorem relaxLine_of_none {f : Lbl → Bool} {ln : Line} (h : ln.relaxable? = none) :
    relaxLine f ln = [ln] := by
  simp [relaxLine, h]

theorem relaxable_of_condTarget {c : Insn} (h : c.condTarget? = none) :
    (Line.ins c none).relaxable? = none := by
  simp [Line.relaxable?, Insn.relaxTarget?, h]

theorem relaxable_of_plain {ln : Line} (h : ln.plain = true) : ln.relaxable? = none := by
  match ln, h with
  | .ins c none, h => exact relaxable_of_condTarget (Line.plain_ins h)
  | .ins c (some _), _ => rfl

theorem relaxLines_of_none {f : Lbl → Bool} :
    ∀ {A : List Line}, (∀ ln ∈ A, ln.relaxable? = none) → relaxLines f A = A
  | [], _ => rfl
  | ln :: A, h => by
    rw [relaxLines_cons, relaxLine_of_none (h ln (by simp)),
      relaxLines_of_none (fun x hx => h x (by simp [hx]))]
    rfl

theorem relaxLines_plain {f : Lbl → Bool} {A : List Line} (h : ∀ ln ∈ A, ln.plain = true) :
    relaxLines f A = A :=
  relaxLines_of_none fun ln hln => relaxable_of_plain (h ln hln)

/-- `ftList_plain_append` after relaxation. -/
theorem ftR_plain_append (f : Lbl → Bool) (P Z : List Line) (hP : ∀ ln ∈ P, ln.plain = true)
    (hZ : ∀ n, Z[1]? ≠ some (.label (.trap n))) :
    relaxLines f (ftList (P ++ Z)) = P ++ relaxLines f (ftList Z) := by
  rw [ftList_plain_append P Z hP hZ, relaxLines_append, relaxLines_plain hP]

/-- A relaxable branch to a far label is relaxed. -/
theorem relaxLine_far {f : Lbl → Bool} {c : Insn} {t : Lbl} (hc : c.relaxTarget? = some t)
    (hf : f t = true) :
    relaxLine f (.ins c none) = [.ins (c.invertTo .skip) none, .ins (.b t) none] := by
  simp [relaxLine, Line.relaxable?, hc, hf]

/-- Any other line is kept. -/
theorem relaxLine_near {f : Lbl → Bool} {c : Insn} {t : Lbl} (hc : c.relaxTarget? = some t)
    (hf : f t = false) : relaxLine f (.ins c none) = [.ins c none] := by
  simp [relaxLine, Line.relaxable?, hc, hf]

/-- The two shapes of a relaxed conditional branch line. -/
theorem relaxLine_cases (f : Lbl → Bool) (c : Insn) :
    relaxLine f (.ins c none) = [.ins c none] ∨
      ∃ t, c.relaxTarget? = some t ∧
        relaxLine f (.ins c none) = [.ins (c.invertTo .skip) none, .ins (.b t) none] := by
  cases hc : c.relaxTarget? with
  | none => exact .inl (relaxLine_of_none (by simp [Line.relaxable?, hc]))
  | some t =>
    cases hf : f t
    · exact .inl (relaxLine_near hc hf)
    · exact .inr ⟨t, rfl, relaxLine_far hc hf⟩

theorem relaxTarget_condTarget {c : Insn} {t : Lbl} (h : c.relaxTarget? = some t) :
    c.condTarget? = some t := by
  unfold Insn.relaxTarget? at h
  split at h <;> simp_all

theorem relaxable_none {ln : Line} (h : ∀ c, ln = .ins c none → c.condTarget? = none) :
    ln.relaxable? = none := by
  cases ln with
  | ins c t =>
    cases t with
    | none => exact relaxable_of_condTarget (h c rfl)
    | some _ => rfl
  | _ => rfl

/-- Lines whose conditional branches (if any) go to atomic-loop labels are not relaxed. -/
theorem relaxLines_loop {f : Lbl → Bool} {A : List Line}
    (h : ∀ ln ∈ A, ∀ c, ln = .ins c none → c.condTarget? = none ∨ ∃ n, c.condTarget? = some (.loop n)) :
    relaxLines f A = A :=
  relaxLines_of_none fun ln hln => by
    cases ln with
    | ins c t =>
      cases t with
      | none =>
        rcases h _ hln c rfl with h' | ⟨n, h'⟩ <;> simp [Line.relaxable?, Insn.relaxTarget?, h']
      | some _ => rfl
    | _ => rfl

theorem relaxLines_trapLines (f : Lbl → Bool) (ts : List (Lbl × Clif.TrapCode)) :
    relaxLines f (trapLines ts) = trapLines ts :=
  relaxLines_of_none fun ln hln => by
    simp only [trapLines, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hln
    obtain ⟨p, -, rfl | rfl⟩ := hln <;> rfl

end Backend
