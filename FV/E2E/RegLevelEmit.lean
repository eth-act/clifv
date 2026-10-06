import FV.Backend.Asm
import FV.Backend.Regalloc

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

/-- `fallthrough` keeps a final label. -/
theorem ftList_snoc_label (l : Lbl) : ∀ X : List Line, ∃ Z, ftList (X ++ [.label l]) = Z ++ [.label l]
  | [] => ⟨[], by rw [List.nil_append, ftList_cons]; simp [ftStep, ftList]⟩
  | [ln] => by
      simp only [List.cons_append, List.nil_append]
      rw [ftList_cons]
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil]
      have h2 : (ftStep ln (some (.label l)) none).2 = 1 := by
        have h1 := ftStep_pos ln (some (.label l)) none
        have h3 := ftStep_le ln (some (.label l)) none
        rcases Nat.lt_or_ge (ftStep ln (some (.label l)) none).2 2 with h | h
        · omega
        · obtain ⟨c, e, l', -, h4, -⟩ :=
            ftStep_two (ln := ln) (n1 := some (.label l)) (n2 := none) (by omega)
          cases h4
      rw [h2]
      simp only [List.drop_succ_cons, List.drop_zero]
      rw [ftList_cons]
      exact ⟨(ftStep ln (some (.label l)) none).1, by simp [ftStep, ftList]⟩
  | ln :: ln2 :: X' => by
      simp only [List.cons_append]
      rw [ftList_cons]
      have hle := ftStep_le ln (ln2 :: (X' ++ [.label l]))[0]? (ln2 :: (X' ++ [.label l]))[1]?
      have hpos := (ftStep_pos ln (ln2 :: (X' ++ [.label l]))[0]? (ln2 :: (X' ++ [.label l]))[1]?).1
      generalize ftStep ln (ln2 :: (X' ++ [.label l]))[0]? (ln2 :: (X' ++ [.label l]))[1]? = st at *
      obtain ⟨out, k⟩ := st
      simp only at hle hpos ⊢
      have hk : k = 1 ∨ k = 2 := by omega
      rcases hk with rfl | rfl
      · simp only [List.drop_succ_cons, List.drop_zero]
        obtain ⟨Z, hZ⟩ := ftList_snoc_label l (ln2 :: X')
        simp only [List.cons_append] at hZ
        exact ⟨out ++ Z, by rw [hZ, List.append_assoc]⟩
      · simp only [List.drop_succ_cons, List.drop_zero]
        obtain ⟨Z, hZ⟩ := ftList_snoc_label l X'
        exact ⟨out ++ Z, by rw [hZ, List.append_assoc]⟩

/-! ## `emitFunc` as structural functions -/

/-- The lines of one `AInst` (`emitFunc`'s inner loop body). -/
def ainstLines (c : FnCtx) (af : AFunc) : AInst → PState → Except String (List Line × PState)
  | .prologue, ps => pure (if af.frame then prologueLines af.frameSize else [], ps)
  | .epilogueRet, ps => pure (if af.frame then epilogueLines af.frameSize else [.ins .ret], ps)
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
theorem emitPre_ok {k : Nat} {af : AFunc} {pre : Array Line} (h : emitPre k af = .ok pre) :
    ∃ body ps, blocksLinesE ⟨k, af.slotBase⟩ af af.blocks.toList {} = .ok (body, ps) ∧
      pre = (ftList body ++ ps.traps.toList.flatMap
        (fun p => [Line.label p.1, Line.ins (.udf 0xc11f) (some p.2)])).toArray := by
  unfold emitPre at h
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
/-! ## `lowerRFunc` as structural functions -/

/-- `lowerRFunc`'s loop body on one item (appending to `code`). -/
def itemStep (fr : RAFrame) (vb : VBlock) (code : Array AInst) : RItem → Except String (Array AInst)
  | .move src dst => do
    let l ← fr.moveInsts src dst
    pure (code ++ l.toArray)
  | .op k allocs => do
    let regs ← allocs.mapM (fun x => match x with
      | Loc.reg r => pure r
      | l => throw (toString "operand in " ++ toString (repr l)))
    match vb.insts[k]? with
    | some i => do
      match ← i.assign regs with
      | .args _ => pure code
      | .rets _ => pure (code.push .epilogueRet)
      | m => pure (code.push (.inst m))
    | none => throw "missing instruction"

/-- The code of one item. -/
def itemCode (fr : RAFrame) (vb : VBlock) (it : RItem) : Except String (List AInst) :=
  (·.toList) <$> itemStep fr vb #[] it

theorem itemStep_eq (fr : RAFrame) (vb : VBlock) (code : Array AInst) (it : RItem) :
    itemStep fr vb code it = (fun l => code ++ l.toArray) <$> itemCode fr vb it := by
  unfold itemCode
  cases it with
  | move src dst =>
    simp only [itemStep]
    cases fr.moveInsts src dst <;> simp [bind, Except.bind, pure, Except.pure, Functor.map, Except.map]
  | op k allocs =>
    simp only [itemStep, bind, Except.bind]
    split
    · rfl
    · split
      · split
        · rfl
        · rename_i m _
          cases m <;> simp [pure, Except.pure, Functor.map, Except.map]
      · rfl

/-- The code of an item list. -/
def itemsCode (fr : RAFrame) (vb : VBlock) : List RItem → Except String (List AInst)
  | [] => pure []
  | it :: its => do
    let c1 ← itemCode fr vb it
    let c2 ← itemsCode fr vb its
    pure (c1 ++ c2)

theorem itemsCode_foldl (fr : RAFrame) (vb : VBlock) :
    ∀ (its : List RItem) (code : Array AInst),
      its.foldlM (fun c it => itemStep fr vb c it) code =
        (fun l => code ++ l.toArray) <$> itemsCode fr vb its
  | [], code => by simp [itemsCode, pure, Except.pure, Functor.map, Except.map]
  | it :: its, code => by
    simp only [List.foldlM_cons, itemsCode]
    rw [itemStep_eq]
    cases itemCode fr vb it with
    | error e => rfl
    | ok c1 =>
      have := itemsCode_foldl fr vb its (code ++ c1.toArray)
      simp only [Functor.map, Except.map, bind, Except.bind] at this ⊢
      rw [this]
      cases itemsCode fr vb its <;> simp [pure, Except.pure]

theorem mapIdxM_go_ok {α β ε : Type} {f : Nat → α → Except ε β} :
    ∀ (l : List α) (acc : Array β) (out : List β), List.mapIdxM.go f l acc = .ok out →
      out.length = acc.size + l.length ∧ (∀ i < acc.size, out[i]? = acc[i]?) ∧
      ∀ j a, l[j]? = some a → ∃ b, f (acc.size + j) a = .ok b ∧ out[acc.size + j]? = some b
  | [], acc, out, h => by
    simp only [List.mapIdxM.go, pure, Except.pure, Except.ok.injEq] at h
    subst h
    refine ⟨by simp, fun i hi => by simp, fun j a hj => by simp at hj⟩
  | a :: l, acc, out, h => by
    simp only [List.mapIdxM.go, bind, Except.bind] at h
    cases hf : f acc.size a with
    | error e => rw [hf] at h; cases h
    | ok b =>
      rw [hf] at h
      obtain ⟨h1, h2, h3⟩ := mapIdxM_go_ok l (acc.push b) out h
      refine ⟨by simp at h1 ⊢; omega, fun i hi => by rw [h2 i (by simp; omega)]; simp [Array.getElem?_push, show i ≠ acc.size by omega], ?_⟩
      intro j a' hj
      cases j with
      | zero =>
        simp at hj
        subst hj
        refine ⟨b, hf, ?_⟩
        rw [Nat.add_zero, h2 acc.size (by simp)]
        simp
      | succ j =>
        simp at hj
        obtain ⟨b', hb', hout⟩ := h3 j a' hj
        simp only [Array.size_push] at hb' hout
        exact ⟨b', by rw [show acc.size + (j + 1) = acc.size + 1 + j by omega]; exact hb',
          by rw [show acc.size + (j + 1) = acc.size + 1 + j by omega]; exact hout⟩

theorem array_mapIdxM_ok {α β ε : Type} {f : Nat → α → Except ε β} {as : Array α} {bs : Array β}
    (h : as.mapIdxM f = .ok bs) :
    bs.size = as.size ∧ ∀ i a, as[i]? = some a → ∃ b, f i a = .ok b ∧ bs[i]? = some b := by
  have e := Array.toList_mapIdxM (xs := as) (f := f)
  rw [h] at e
  simp only [Functor.map, Except.map, List.mapIdxM] at e
  obtain ⟨h1, -, h3⟩ := mapIdxM_go_ok as.toList #[] bs.toList e.symm
  refine ⟨by simpa using h1, fun i a hi => ?_⟩
  obtain ⟨b, hb, hb'⟩ := h3 i a (by simpa using hi)
  exact ⟨b, by simpa using hb, by simpa using hb'⟩


/-- **`lowerRFunc` as a structural function**: block `b`'s code is the prologue (block 0) and
the items' code. -/
theorem lowerRFunc_ok {vc : VCode} {rf : RFunc} {af : AFunc} (h : lowerRFunc vc rf = .ok af) :
    (af.frameSize = (RAFrame.compute vc rf).total ∧ af.slotBase = (RAFrame.compute vc rf).size ∧
      af.blocks.size = (vc.blocks.zip rf.blocks).size ∧
      ∀ b vb items, vc.blocks[b]? = some vb → rf.blocks[b]? = some items →
        ∃ code, itemsCode (RAFrame.compute vc rf) vb items.toList = .ok code ∧
          af.blocks[b]? = some (vb.label, ((if b = 0 then [AInst.prologue] else []) ++ code).toArray)) ∧
      ((RAFrame.compute vc rf).total ≠ 0 → af.frame = true) ∧ ctlCheck vc rf = true := by
  unfold lowerRFunc at h
  simp only [bind, Except.bind] at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  rename_i harg
  split at h
  · cases h
  · rename_i blocks hb
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    refine And.intro ?_ ⟨fun _ => rfl, by simpa using harg⟩
    obtain ⟨hsz, hel⟩ := array_mapIdxM_ok hb
    refine ⟨rfl, rfl, hsz, fun b vb items hvb hit => ?_⟩
    have hz : (vc.blocks.zip rf.blocks)[b]? = some (vb, items) := by
      rw [Array.getElem?_zip_eq_some]; exact ⟨hvb, hit⟩
    obtain ⟨p, hp, hbp⟩ := hel b _ hz
    simp only at hp
    rw [← Array.forIn_toList, forIn_except_yield _ _ _ (fun it c => itemStep (RAFrame.compute vc rf) vb c it)] at hp
    · rw [itemsCode_foldl] at hp
      cases hc : itemsCode (RAFrame.compute vc rf) vb items.toList with
      | error e => rw [hc] at hp; cases hp
      | ok code =>
        rw [hc] at hp
        simp only [Functor.map, Except.map, pure, Except.pure, Except.ok.injEq] at hp
        subst hp
        refine ⟨code, rfl, ?_⟩
        rw [hbp]
        by_cases h0 : b = 0 <;> simp [h0]
    · intro it c
      cases it with
      | move src dst =>
        simp only [itemStep]
        cases (RAFrame.compute vc rf).moveInsts src dst <;> rfl
      | op k allocs =>
        simp only [itemStep, bind, Except.bind]
        generalize (Array.mapM (fun x => match x with
          | Loc.reg r => (pure r : Except String Reg)
          | l => throw (toString "operand in " ++ toString (repr l))) allocs) = M
        cases M with
        | error e => rfl
        | ok regs =>
          simp only
          cases vb.insts[k]? with
          | none => rfl
          | some i =>
            simp only
            cases i.assign regs with
            | error e => rfl
            | ok m => cases m <;> rfl


/-- Every lowered function keeps a frame (fp/lr on the stack). -/
theorem lowerRFunc_frame {vc : VCode} {rf : RFunc} {af : AFunc} (h : lowerRFunc vc rf = .ok af) :
    af.frame = true := by
  unfold lowerRFunc at h
  simp only [bind, Except.bind] at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  split at h
  · cases h
  · simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h; rfl

/-! ## Block decomposition -/

theorem lines_traps {c : FnCtx} {m : MInst} {ps ps' : PState} {ls : List Line}
    (h : m.lines c ps = .ok (ls, ps')) : ps.traps.toList <+: ps'.traps.toList := by
  unfold MInst.lines at h
  split at h <;> simp only [bind, Except.bind, pure, Except.pure] at h
  all_goals (repeat' (first | (split at h) | (simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h)))
  all_goals first | exact List.prefix_refl _ | simp | skip
  all_goals first | cases h | simp [throw, throwThe, MonadExceptOf.throw] at h


theorem ainstLines_traps {c : FnCtx} {af : AFunc} {a : AInst} {ps ps' : PState} {ls : List Line}
    (h : ainstLines c af a ps = .ok (ls, ps')) : ps.traps.toList <+: ps'.traps.toList := by
  cases a with
  | inst m => exact lines_traps h
  | _ => simp only [ainstLines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h; rw [h.2]; exact List.prefix_refl _

theorem codeLinesE_traps {c : FnCtx} {af : AFunc} :
    ∀ {code : List AInst} {ps ps' : PState} {ls : List Line},
      codeLinesE c af code ps = .ok (ls, ps') → ps.traps.toList <+: ps'.traps.toList
  | [], ps, ps', ls, h => by
    simp only [codeLinesE, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h; rw [h.2]; exact List.prefix_refl _
  | a :: as, ps, ps', ls, h => by
    simp only [codeLinesE, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i r hr
      split at h
      · cases h
      · rename_i r2 hr2
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        rw [← h.2]
        exact (ainstLines_traps hr).trans (codeLinesE_traps hr2)

theorem blocksLinesE_traps {c : FnCtx} {af : AFunc} :
    ∀ {bs : List (Label × Array AInst)} {ps ps' : PState} {ls : List Line},
      blocksLinesE c af bs ps = .ok (ls, ps') → ps.traps.toList <+: ps'.traps.toList
  | [], ps, ps', ls, h => by
    simp only [blocksLinesE, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h; rw [h.2]; exact List.prefix_refl _
  | (l, code) :: bs, ps, ps', ls, h => by
    simp only [blocksLinesE, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i r hr
      split at h
      · cases h
      · rename_i r2 hr2
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        rw [← h.2]
        exact (codeLinesE_traps hr).trans (blocksLinesE_traps hr2)

/-- Block `b` in the lines before `fallthrough`: its label, its code's lines, then the next
block's label (or the end). -/
theorem blocksLinesE_block {c : FnCtx} {af : AFunc} :
    ∀ {bs : List (Label × Array AInst)} {ps psF : PState} {body : List Line} {b : Nat}
      {l : Label} {code : Array AInst},
      blocksLinesE c af bs ps = .ok (body, psF) → bs[b]? = some (l, code) →
      ∃ pre ls ps1 ps2 post, body = pre ++ .label (.block l) :: (ls ++ post) ∧
        codeLinesE c af code.toList ps1 = .ok (ls, ps2) ∧
        ps.traps.toList <+: ps1.traps.toList ∧ ps2.traps.toList <+: psF.traps.toList ∧
        (∀ p, bs[b + 1]? = some p → ∃ post', post = .label (.block p.1) :: post') ∧
        (bs[b + 1]? = none → post = []) ∧ (b = 0 → pre = [])
  | [], _, _, _, _, _, _, _, hb => by simp at hb
  | (l0, code0) :: bs, ps, psF, body, b, l, code, h, hb => by
    simp only [blocksLinesE, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i r hr
      split at h
      · cases h
      · rename_i r2 hr2
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        cases b with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hb
          obtain ⟨rfl, rfl⟩ := hb
          refine ⟨[], r.1, ps, r.2, r2.1, by simp, hr, List.prefix_refl _,
            blocksLinesE_traps hr2, ?_, ?_⟩
          · intro p hp
            cases bs with
            | nil => simp at hp
            | cons p' bs =>
              simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hp
              subst hp
              obtain ⟨l', code'⟩ := p'
              simp only [blocksLinesE, bind, Except.bind] at hr2
              split at hr2
              · cases hr2
              · split at hr2
                · cases hr2
                · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hr2
                  exact ⟨_, by rw [← hr2]; rfl⟩
          · refine ⟨fun hp => ?_, fun _ => rfl⟩
            cases bs with
            | nil =>
              simp only [blocksLinesE, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hr2
              rw [← hr2]
            | cons _ _ => simp at hp
        | succ b =>
          simp only [List.getElem?_cons_succ] at hb
          obtain ⟨pre, ls, ps1, ps2, post, hbody, hc, hp1, hp2, hn, hn', -⟩ := blocksLinesE_block hr2 hb
          refine ⟨.label (.block l0) :: r.1 ++ pre, ls, ps1, ps2, post, ?_, hc,
            (codeLinesE_traps hr).trans hp1, hp2, ?_, ?_, fun h => by cases h⟩
          · rw [hbody]; simp
          · intro p hp; exact hn p (by simpa using hp)
          · intro hp; exact hn' (by simpa using hp)

/-! ## The final lines, block by block -/

/-- The label of the block after `b` (the lookahead of `fallthrough` at the end of `b`). -/
def nxtOf (af : AFunc) (b : Nat) : List Line :=
  match af.blocks[b + 1]? with
  | some p => [.label (.block p.1)]
  | none => []

/-- The trap section appended after the body. -/
def trapLines (ts : List (Lbl × Clif.TrapCode)) : List Line :=
  ts.flatMap (fun p => [Line.label p.1, Line.ins (.udf 0xc11f) (some p.2)])

/-- The far labels `emitFunc` relaxes the branches to (`relaxOf` of the lines before relaxation). -/
def emitFar (c : FnCtx) (af : AFunc) : Lbl → Bool :=
  match blocksLinesE c af af.blocks.toList {} with
  | .ok (body, ps) => relaxOf (ftList body ++ trapLines ps.traps.toList)
  | .error _ => fun _ => false

set_option pp.proofs false in
theorem emitFunc_ok {k : Nat} {af : AFunc} {fa : FnAsm} (h : emitFunc k af = .ok fa) :
    ∃ body ps, blocksLinesE ⟨k, af.slotBase⟩ af af.blocks.toList {} = .ok (body, ps) ∧
      fa.lines.toList = relaxLines (emitFar ⟨k, af.slotBase⟩ af)
        (ftList body ++ trapLines ps.traps.toList) ∧ fa.k = k := by
  unfold emitFunc at h
  cases hp : emitPre k af with
  | error e => rw [hp] at h; cases h
  | ok pre =>
    rw [hp] at h
    obtain ⟨body, ps, hb, rfl⟩ := emitPre_ok hp
    simp only [bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    · simp only [Except.ok.injEq] at h
      subst h
      refine ⟨body, ps, hb, ?_, rfl⟩
      simp [emitFar, hb, trapLines]

/-- **Block `b` in the final lines**: its label at line `j`, then the `fallthrough` of its code's
lines followed by the next block's label. -/
theorem emit_block {k : Nat} {af : AFunc} {fa : FnAsm} (h : emitFunc k af = .ok fa) :
    ∃ body psF, blocksLinesE ⟨k, af.slotBase⟩ af af.blocks.toList {} = .ok (body, psF) ∧
      fa.lines.toList = relaxLines (emitFar ⟨k, af.slotBase⟩ af)
        (ftList body ++ trapLines psF.traps.toList) ∧
      ∀ b l code, af.blocks[b]? = some (l, code) →
        ∃ j ls ps1 ps2 R, fa.lines.toList[j]? = some (.label (.block l)) ∧
          fa.lines.toList.drop (j + 1) =
            relaxLines (emitFar ⟨k, af.slotBase⟩ af) (ftList (ls ++ nxtOf af b)) ++ R ∧
          codeLinesE ⟨k, af.slotBase⟩ af code.toList ps1 = .ok (ls, ps2) ∧
          ps2.traps.toList <+: psF.traps.toList ∧ (b = 0 → j = 0) := by
  obtain ⟨body, psF, hb, hL', -⟩ := emitFunc_ok h
  generalize emitFar ⟨k, af.slotBase⟩ af = F at hL' ⊢
  refine ⟨body, psF, hb, hL', fun b l code hbc => ?_⟩
  obtain ⟨pre, ls, ps1, ps2, post, hbody, hc, -, hp2, hn, hn', hpre0⟩ :=
    blocksLinesE_block hb (by simpa using hbc)
  obtain ⟨Z, hZ⟩ := ftList_snoc_label (.block l) pre
  have hsplit := ftList_label_split (.block l) (ls ++ post) pre
  rw [← hbody, hZ] at hsplit
  have hpost : ∃ R0, ftList (ls ++ post) = ftList (ls ++ nxtOf af b) ++ R0 := by
    unfold nxtOf
    cases hb1 : af.blocks[b + 1]? with
    | none =>
      rw [hn' (by simpa using hb1)]
      exact ⟨[], by simp⟩
    | some p =>
      obtain ⟨post', rfl⟩ := hn p (by simpa using hb1)
      exact ⟨ftList post', ftList_label_split _ post' ls⟩
  obtain ⟨R0, hR0⟩ := hpost
  refine ⟨(relaxLines F Z).length, ls, ps1, ps2,
    relaxLines F R0 ++ relaxLines F (trapLines psF.traps.toList), ?_, ?_, hc, hp2, fun h0 => ?_⟩
  · rw [hL', hsplit]; simp [relaxLines, relaxLine, Line.relaxable?]
  · rw [hL', hsplit, hR0]
    simp [relaxLines, relaxLine, Line.relaxable?, List.drop_append]
  · subst h0
    rw [hpre0 rfl, List.nil_append, ftList_cons] at hZ
    have := congrArg List.length hZ
    simp [ftStep, ftList] at this
    simp [this, relaxLines]

/-! ## Lines `fallthrough` leaves alone -/

/-- A line neither `fallthrough` nor branch relaxation (`relaxLine`) rewrites: an instruction
that is neither `b` nor a conditional branch. -/
def Line.plain : Line → Bool
  | .ins (.b _) none => false
  | .ins c none => c.condTarget?.isNone
  | .ins _ (some _) => true
  | _ => false

theorem Line.plain_ins {c : Insn} (h : (Line.ins c none).plain = true) : c.condTarget? = none := by
  cases c <;> simp_all [Line.plain, Insn.condTarget?]

theorem ftStep_plain {ln : Line} {n1 n2 : Option Line} (hp : ln.plain = true)
    (h : ∀ c e l, ln = .ins c none → n1 = some (.ins (.b e) none) → n2 = some (.label l) →
      c.condTarget? ≠ some l) :
    ftStep ln n1 n2 = ([ln], 1) := by
  unfold ftStep
  repeat' split
  all_goals simp_all [Line.plain]

/-- Plain lines pass through `fallthrough` unchanged (the following code has no trap label in
second position). -/
theorem ftList_plain_append :
    ∀ (P Z : List Line), (∀ ln ∈ P, ln.plain = true) → (∀ n, Z[1]? ≠ some (.label (.trap n))) →
      ftList (P ++ Z) = P ++ ftList Z
  | [], Z, _, _ => by simp
  | ln :: P, Z, hP, hZ => by
    simp only [List.cons_append]
    rw [ftList_cons]
    have hln := hP ln (by simp)
    rw [ftStep_plain hln]
    · simp only [List.drop_succ_cons, List.drop_zero, List.singleton_append]
      rw [ftList_plain_append P Z (fun x hx => hP x (by simp [hx])) hZ]
    · intro c e l hc h1 h2 htgt
      subst hc
      cases P with
      | nil => exact absurd htgt (by rw [Line.plain_ins hln]; simp)
      | cons x P =>
        simp only [List.cons_append, List.getElem?_cons_zero, Option.some.injEq] at h1
        subst h1
        simp [Line.plain] at hP

end Backend
