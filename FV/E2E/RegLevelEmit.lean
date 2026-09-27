import FV.Backend.Asm

/-!
# `emitFunc`'s code structure (M6 proof, register level)

`fallthrough` (the `MachBuffer` branch simplification of `emitFunc`) is an imperative loop;
`fallthrough_eq` characterizes it as the structural `ftList` (one `ftStep` per position), and
`ftList_label_split` shows it never looks past a label: the code of each block is simplified
independently, with the next block's label as the only lookahead.
-/

namespace Backend

/-- One step of `fallthrough` at a line `ln` followed by `n1`, `n2`: the emitted lines and
the number of input lines consumed. -/
def ftStep (ln : Line) (n1 n2 : Option Line) : List Line × Nat :=
  let dflt : List Line × Nat := match ln, n1 with
    | .ins (.b x) none, some (.label l) => if x == l then ([], 1) else ([ln], 1)
    | _, _ => ([ln], 1)
  match ln, n1, n2 with
  | .ins c none, some (.ins (.b e) none), some (.label l) =>
    if c.condTarget? == some l then ([.ins (c.invertTo e) none], 2) else dflt
  | _, _, _ => dflt

theorem ftStep_pos (ln : Line) (n1 n2 : Option Line) :
    1 ≤ (ftStep ln n1 n2).2 ∧ ((ftStep ln n1 n2).2 = 2 → n1.isSome) := by
  unfold ftStep
  repeat' split
  all_goals simp_all

/-- `fallthrough` as a function on the line list. -/
def ftList : List Line → List Line
  | [] => []
  | ln :: rest =>
    (ftStep ln rest[0]? rest[1]?).1 ++ ftList ((ln :: rest).drop (ftStep ln rest[0]? rest[1]?).2)
termination_by L => L.length
decreasing_by
  have := ftStep_pos ln rest[0]? rest[1]?
  simp only [List.length_drop, List.length_cons]
  omega

/-- One iteration of `fallthrough`'s loop. -/
def ftBody (lines : Array Line) (st : Array Line × Nat) : ForInStep (Array Line × Nat) :=
  if st.2 ≥ lines.size then .done st
  else
    let dflt : ForInStep (Array Line × Nat) :=
      match lines[st.2]!, lines[st.2 + 1]? with
      | .ins (.b x) none, some (.label l) =>
        if x == l then .yield (st.1, st.2 + 1) else .yield (st.1.push lines[st.2]!, st.2 + 1)
      | _, _ => .yield (st.1.push lines[st.2]!, st.2 + 1)
    match lines[st.2]!, lines[st.2 + 1]?, lines[st.2 + 2]? with
    | .ins c none, some (.ins (.b e) none), some (.label l) =>
      if c.condTarget? == some l then .yield (st.1.push (.ins (c.invertTo e) none), st.2 + 2)
      else dflt
    | _, _, _ => dflt

theorem fallthrough_eq_forIn (lines : Array Line) :
    fallthrough lines = (forIn (m := Id) (List.range' 0 lines.size) (#[], 0)
      (fun _ st => pure (ftBody lines st))).1 := by
  unfold fallthrough ftBody
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  simp
  rfl

theorem ftBody_eq {lines : Array Line} {out : Array Line} {i : Nat} (hi : i < lines.size) :
    ftBody lines (out, i) = .yield (out ++ (ftStep lines[i]! lines[i + 1]? lines[i + 2]?).1.toArray,
      i + (ftStep lines[i]! lines[i + 1]? lines[i + 2]?).2) := by
  unfold ftBody ftStep
  simp only [show ¬ (i ≥ lines.size) from by omega, ite_false]
  generalize lines[i]! = ln
  generalize lines[i + 1]? = n1
  generalize lines[i + 2]? = n2
  split
  · split
    · simp
    · split
      · split <;> simp
      · simp
  · split
    · split <;> simp
    · simp

theorem ftList_cons (ln : Line) (rest : List Line) :
    ftList (ln :: rest) = (ftStep ln rest[0]? rest[1]?).1 ++
      ftList ((ln :: rest).drop (ftStep ln rest[0]? rest[1]?).2) := by
  rw [ftList]

theorem ftLoop (lines : Array Line) : ∀ k a (out : Array Line) i, lines.size - i ≤ k →
    (forIn (m := Id) (List.range' a k) (out, i) (fun _ st => pure (ftBody lines st))).1 =
      out ++ (ftList (lines.toList.drop i)).toArray := by
  intro k
  induction k with
  | zero =>
    intro a out i h
    have : lines.toList.drop i = [] := by simp; omega
    simp [this, ftList]; rfl
  | succ k ih =>
    intro a out i h
    simp only [List.range'_succ, List.forIn_cons]
    by_cases hi : i ≥ lines.size
    · have : lines.toList.drop i = [] := by simp; omega
      simp [ftBody, hi, this, ftList]; rfl
    · obtain ⟨ln, rest, hD⟩ : ∃ ln rest, lines.toList.drop i = ln :: rest := by
        cases h : lines.toList.drop i with
        | nil => simp at h; omega
        | cons ln rest => exact ⟨ln, rest, rfl⟩
      have hj : ∀ j, lines[i + j]? = (ln :: rest)[j]? := by
        intro j; rw [← hD, List.getElem?_drop, Array.getElem?_toList]
      have h0 : lines[i]! = ln := by
        have := hj 0; simp only [Nat.add_zero, List.getElem?_cons_zero] at this
        simp [getElem!_def, this]
      have h1 : lines[i + 1]? = rest[0]? := by simpa using hj 1
      have h2 : lines[i + 2]? = rest[1]? := by simpa using hj 2
      rw [ftBody_eq (by omega), h0, h1, h2]
      have hp := ftStep_pos ln rest[0]? rest[1]?
      have e := ih (a + 1) (out ++ (ftStep ln rest[0]? rest[1]?).1.toArray)
        (i + (ftStep ln rest[0]? rest[1]?).2) (by omega)
      simp only [pure, bind] at e ⊢
      rw [e, hD, ftList_cons, ← List.drop_drop, hD]
      simp

theorem fallthrough_eq (lines : Array Line) : fallthrough lines = (ftList lines.toList).toArray := by
  rw [fallthrough_eq_forIn, ftLoop lines lines.size 0 #[] 0 (by omega)]
  simp

/-- The step at a line followed by a label does not look further. -/
theorem ftStep_label (ln : Line) (l : Lbl) (n2 n2' : Option Line) :
    ftStep ln (some (.label l)) n2 = ftStep ln (some (.label l)) n2' := by
  cases ln with
  | ins c t => cases t <;> rfl
  | _ => rfl

theorem ftStep_two {ln : Line} {n1 n2 : Option Line} (h : (ftStep ln n1 n2).2 = 2) :
    ∃ c e l, ln = .ins c none ∧ n1 = some (.ins (.b e) none) ∧ n2 = some (.label l) := by
  revert h
  unfold ftStep
  repeat' split
  all_goals simp_all

theorem ftStep_le (ln : Line) (n1 n2 : Option Line) : (ftStep ln n1 n2).2 ≤ 2 := by
  unfold ftStep
  repeat' split
  all_goals simp_all

/-- **`fallthrough` splits at a label**: it never looks past the label that follows the
lines `X`. -/
theorem ftList_label_split (l : Lbl) (Y : List Line) :
    ∀ X : List Line, ftList (X ++ .label l :: Y) = ftList (X ++ [.label l]) ++ ftList Y
  | [] => by
      simp only [List.nil_append]
      rw [ftList_cons, ftList_cons]
      simp [ftStep, ftList]
  | [ln] => by
      simp only [List.cons_append, List.nil_append]
      rw [ftList_cons, ftList_cons]
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil]
      rw [ftStep_label ln l Y[0]? none]
      have h2 : (ftStep ln (some (.label l)) none).2 = 1 := by
        have h1 := ftStep_pos ln (some (.label l)) none
        have h3 := ftStep_le ln (some (.label l)) none
        rcases Nat.lt_or_ge (ftStep ln (some (.label l)) none).2 2 with h | h
        · omega
        · obtain ⟨c, e, l', -, h4, -⟩ :=
            ftStep_two (ln := ln) (n1 := some (.label l)) (n2 := none) (by omega)
          cases h4
      rw [h2]
      simp only [List.drop_succ_cons, List.drop_zero, List.append_assoc]
      rw [ftList_cons, ftList_cons]
      simp [ftStep, ftList]
  | ln :: ln2 :: X' => by
      simp only [List.cons_append]
      rw [ftList_cons, ftList_cons]
      have e1 : (ln2 :: (X' ++ .label l :: Y))[0]? = (ln2 :: (X' ++ [.label l]))[0]? := rfl
      have e2 : (ln2 :: (X' ++ .label l :: Y))[1]? = (ln2 :: (X' ++ [.label l]))[1]? := by
        cases X' <;> rfl
      rw [e1, e2]
      have hle := ftStep_le ln (ln2 :: (X' ++ [.label l]))[0]? (ln2 :: (X' ++ [.label l]))[1]?
      have hpos := (ftStep_pos ln (ln2 :: (X' ++ [.label l]))[0]? (ln2 :: (X' ++ [.label l]))[1]?).1
      generalize ftStep ln (ln2 :: (X' ++ [.label l]))[0]? (ln2 :: (X' ++ [.label l]))[1]? = st at *
      obtain ⟨out, k⟩ := st
      simp only at hle hpos ⊢
      have hk : k = 1 ∨ k = 2 := by omega
      rcases hk with rfl | rfl
      · simp only [List.drop_succ_cons, List.drop_zero, List.append_assoc]
        have := ftList_label_split l Y (ln2 :: X')
        simp only [List.cons_append] at this
        rw [this]
      · simp only [List.drop_succ_cons, List.drop_zero, List.append_assoc]
        rw [ftList_label_split l Y X']

/-! ## `emitFunc` as structural functions -/

/-- The lines of one `AInst` (`emitFunc`'s inner loop body). -/
def ainstLines (c : FnCtx) (af : AFunc) : AInst → PState → Except String (List Line × PState)
  | .prologue, ps => pure (if af.frame then prologueLines af.frameSize else [], ps)
  | .epilogueRet, ps => pure (if af.frame then epilogueLines else [.ins .ret], ps)
  | .inst m, ps => m.lines c ps

/-- The lines of a block's code. -/
def codeLinesE (c : FnCtx) (af : AFunc) : List AInst → PState → Except String (List Line × PState)
  | [], ps => pure ([], ps)
  | a :: as, ps => do
    let (l1, ps1) ← ainstLines c af a ps
    let (l2, ps2) ← codeLinesE c af as ps1
    pure (l1 ++ l2, ps2)

/-- The lines of the blocks (each introduced by its label), before `fallthrough`. -/
def blocksLinesE (c : FnCtx) (af : AFunc) :
    List (Label × Array AInst) → PState → Except String (List Line × PState)
  | [], ps => pure ([], ps)
  | (l, code) :: bs, ps => do
    let (l1, ps1) ← codeLinesE c af code.toList ps
    let (l2, ps2) ← blocksLinesE c af bs ps1
    pure (.label (.block l) :: l1 ++ l2, ps2)

theorem forIn_except_yield {ε σ α : Type} (l : List α) (s : σ)
    (f : α → σ → Except ε (ForInStep σ)) (g : α → σ → Except ε σ)
    (h : ∀ a s, f a s = ForInStep.yield <$> g a s) : forIn l s f = l.foldlM (fun s a => g a s) s := by
  induction l generalizing s with
  | nil => rfl
  | cons a l ih =>
    simp only [List.forIn_cons, List.foldlM_cons, h]
    cases g a s with
    | error e => rfl
    | ok s' => exact ih s'

theorem codeLinesE_foldl (c : FnCtx) (af : AFunc) :
    ∀ (code : List AInst) (ps : PState) (acc : Array Line),
      code.foldlM (fun s a => (fun r : List Line × PState => (r.2, s.2 ++ r.1.toArray)) <$>
          ainstLines c af a s.1) (ps, acc) =
        (fun r : List Line × PState => (r.2, acc ++ r.1.toArray)) <$> codeLinesE c af code ps
  | [], ps, acc => by simp [codeLinesE]
  | a :: as, ps, acc => by
    simp only [List.foldlM_cons, codeLinesE]
    cases ainstLines c af a ps with
    | error e => rfl
    | ok r =>
      have := codeLinesE_foldl c af as r.2 (acc ++ r.1.toArray)
      simp only [Functor.map, Except.map, bind, Except.bind] at this ⊢
      rw [this]
      cases codeLinesE c af as r.2 <;> simp [pure, Except.pure]

theorem blocksLinesE_foldl (c : FnCtx) (af : AFunc) :
    ∀ (bs : List (Label × Array AInst)) (ps : PState) (acc : Array Line),
      bs.foldlM (fun s a => (fun r : List Line × PState =>
          (r.2, s.2.push (.label (.block a.1)) ++ r.1.toArray)) <$> codeLinesE c af a.2.toList s.1)
          (ps, acc) =
        (fun r : List Line × PState => (r.2, acc ++ r.1.toArray)) <$> blocksLinesE c af bs ps
  | [], ps, acc => by simp [blocksLinesE]
  | (l, code) :: bs, ps, acc => by
    simp only [List.foldlM_cons, blocksLinesE]
    cases codeLinesE c af code.toList ps with
    | error e => rfl
    | ok r =>
      have := blocksLinesE_foldl c af bs r.2 (acc.push (.label (.block l)) ++ r.1.toArray)
      simp only [Functor.map, Except.map, bind, Except.bind] at this ⊢
      rw [this]
      cases blocksLinesE c af bs r.2 <;> simp [pure, Except.pure]

theorem traps_foldl (ts : List (Lbl × Clif.TrapCode)) (acc : Array Line) :
    forIn (m := Except String) ts acc (fun x s =>
      Except.ok (ForInStep.yield ((s.push (Line.label x.1)).push (Line.ins (.udf 49439) (some x.2))))) =
      .ok (acc ++ (ts.flatMap (fun p => [Line.label p.1, Line.ins (.udf 0xc11f) (some p.2)])).toArray) := by
  induction ts generalizing acc with
  | nil => simp; rfl
  | cons t ts ih =>
    simp only [List.forIn_cons]
    have := ih ((acc.push (Line.label t.1)).push (Line.ins (.udf 49439) (some t.2)))
    simp only [pure, Except.pure, bind, Except.bind] at this ⊢
    rw [this]
    simp

set_option pp.proofs false in
theorem emitFunc_ok {k : Nat} {af : AFunc} {fa : FnAsm} (h : emitFunc k af = .ok fa) :
    ∃ body ps, blocksLinesE ⟨k, af.slotBase⟩ af af.blocks.toList {} = .ok (body, ps) ∧
      fa.lines = (ftList body ++ ps.traps.toList.flatMap
        (fun p => [Line.label p.1, Line.ins (.udf 0xc11f) (some p.2)])).toArray ∧ fa.k = k := by
  unfold emitFunc at h
  simp only [← Array.forIn_toList] at h
  rw [forIn_except_yield _ _ _ (fun (x : Label × Array AInst) (s : PState × Array Line) =>
    (fun r : List Line × PState => (r.2, s.2.push (.label (.block x.1)) ++ r.1.toArray)) <$>
      codeLinesE ⟨k, af.slotBase⟩ af x.2.toList s.1)] at h
  · rw [blocksLinesE_foldl] at h
    cases hb : blocksLinesE ⟨k, af.slotBase⟩ af af.blocks.toList {} with
    | error e => rw [hb] at h; cases h
    | ok r =>
      rw [hb] at h
      obtain ⟨body, ps⟩ := r
      refine ⟨body, ps, rfl, ?_⟩
      simp only [Functor.map, Except.map, bind, Except.bind, pure, Except.pure] at h
      rw [traps_foldl] at h
      simp only at h
      split at h
      · cases h
      · rename_i v hv
        simp only [Except.ok.injEq] at h
        subst h
        simp [fallthrough_eq]
  · intro x s
    obtain ⟨l, code⟩ := x
    simp only
    rw [forIn_except_yield _ _ _ (fun (a : AInst) (s : PState × Array Line) =>
      (fun r : List Line × PState => (r.2, s.2 ++ r.1.toArray)) <$> ainstLines ⟨k, af.slotBase⟩ af a s.1)]
    · rw [codeLinesE_foldl]
      cases codeLinesE ⟨k, af.slotBase⟩ af code.toList s.1 <;> rfl
    · intro a s
      cases a <;> simp [ainstLines]
      · cases af.frame <;> simp
      · cases af.frame <;> simp
end Backend
