import FV.E2E.RegLevelRelax

/-!
# The emission plan's branch check, as propositions (M6)

`segsOk` (the check every emission plan passes, `emitPlan_spec`) in a form the simulation uses:

* `segsOk_spec`: every segment's final lines pass `termOk` (`segTermOk`), but those of the
  forwarding blocks not trusted (`segsTrust`);
* `segNxts_get`: segment `i` in the plan's lines with the line `nxt` after its final lines;
* `blockLabelIdx_get`: the line `blockLabelIdx` names for a block label is that label's line;
* `RepL`: line `j` represents block `s` (`repAt` as a proposition, `repAt_repL`), kept by branch
  relaxation (`RepL.relax`, at the relaxed index `rix`);
* `termOk_jump`, `termOk_cond`, `termOk_tryCall`, `termOk_kept`: the final lines `termOk` accepts
  for each kind of last instruction.
-/

namespace Backend

/-! ## `segsOk` -/

theorem segsOk_spec {af : AFunc} {ss : List Seg} {os : List (List Line)} {L : List Line}
    (h : segsOk af ss os L = true) :
    os.length = ss.length ∧ ss.head?.map (·.idx) = some 0 ∧
      ∀ x ∈ segNxts ss os 0,
        ((af.fwd? x.1.label).isSome = true ∧ (segsTrust af ss os L).contains x.1.label = false) ∨
        segTermOk af (repOn af ((segsTrust af ss os L).contains ·) L) (blockLabelIdx L) x = true := by
  unfold segsOk at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true'] at h
  exact ⟨h.1.1.symm, h.1.2, h.2⟩

/-- **Segment `i` in `segLines`** with the line after its final lines (`segNxts`). -/
theorem segNxts_get : ∀ {ss : List Seg} {os : List (List Line)} {n i : Nat} {s : Seg}
    {o : List Line}, ss[i]? = some s → os[i]? = some o →
    ∃ A, segLines ss os =
        A ++ .label (.block s.label) :: (s.body ++ o) ++ segLines (ss.drop (i + 1)) (os.drop (i + 1)) ∧
      (s, o, n + A.length + 1 + s.body.length + o.length) ∈ segNxts ss os n
  | [], _, _, _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, _, _, _, h => by simp at h
  | s0 :: ss, o0 :: os, n, 0, s, o, h1, h2 => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h1 h2
    subst h1 h2
    refine ⟨[], by simp [segLines], ?_⟩
    simp only [segNxts, List.length_nil, Nat.add_zero]
    exact List.mem_cons_self
  | s0 :: ss, o0 :: os, n, i + 1, s, o, h1, h2 => by
    simp only [List.getElem?_cons_succ] at h1 h2
    obtain ⟨A, hA, hm⟩ := segNxts_get (n := n + 1 + s0.body.length + o0.length) h1 h2
    refine ⟨.label (.block s0.label) :: (s0.body ++ o0) ++ A, ?_, ?_⟩
    · simp only [segLines, hA, List.drop_succ_cons]
      simp
    · simp only [segNxts]
      refine List.mem_cons_of_mem _ ?_
      have e : n + (Line.label (.block s0.label) :: (s0.body ++ o0) ++ A).length + 1 +
          s.body.length + o.length =
          n + 1 + s0.body.length + o0.length + A.length + 1 + s.body.length + o.length := by
        simp; omega
      rw [e]
      exact hm

/-- The elements of `segNxts` are the segments with their final lines. -/
theorem segNxts_mem : ∀ {ss : List Seg} {os : List (List Line)} {n : Nat}
    {x : Seg × List Line × Nat}, x ∈ segNxts ss os n →
      ∃ i : Nat, ss[i]? = some x.1 ∧ os[i]? = some x.2.1
  | [], _, _, _, h => by simp [segNxts] at h
  | _ :: _, [], _, _, h => by simp [segNxts] at h
  | s :: ss, o :: os, n, x, h => by
    simp only [segNxts, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨0, rfl, rfl⟩
    · obtain ⟨i, h1, h2⟩ := segNxts_mem h
      exact ⟨i + 1, h1, h2⟩

/-! ## Block label lines -/

theorem blockLabelIdx_go : ∀ (L : List Line) (n : Nat) (l : Label) (j : Nat),
    ((L.zipIdx n).foldr (fun (x : Line × Nat) (m : Std.HashMap Label Nat) => match x.1 with
      | .label (.block l) => m.insert l x.2
      | _ => m) {})[l]? = some j → n ≤ j ∧ L[j - n]? = some (.label (.block l))
  | [], n, l, j, h => by simp at h
  | ln :: L, n, l, j, h => by
    simp only [List.zipIdx_cons, List.foldr_cons] at h
    split at h
    · rename_i _ l'
      rw [Std.HashMap.getElem?_insert] at h
      split at h
      · rename_i hl
        simp only [beq_iff_eq] at hl
        subst hl
        cases h
        simp
      · obtain ⟨h1, h2⟩ := blockLabelIdx_go L (n + 1) l j h
        refine ⟨by omega, ?_⟩
        rw [show j - n = (j - (n + 1)) + 1 by omega]
        simpa using h2
    · obtain ⟨h1, h2⟩ := blockLabelIdx_go L (n + 1) l j h
      refine ⟨by omega, ?_⟩
      rw [show j - n = (j - (n + 1)) + 1 by omega]
      simpa using h2

/-- The line `blockLabelIdx` names for block label `l` is `l`'s label line. -/
theorem blockLabelIdx_get {L : List Line} {l : Label} {j : Nat}
    (h : (blockLabelIdx L)[l]? = some j) : L[j]? = some (.label (.block l)) := by
  have := blockLabelIdx_go L 0 l j h
  simpa using this.2

/-! ## Representing a block -/

/-- Line `j` of `LL` represents block `s` (`repAt` as a proposition): the label lines from `j`
on include `s`'s own (only if `s` forwards nowhere or `own s`), or `s` forwards to a block `x`
line `j` represents. -/
inductive RepL (af : AFunc) (own : Label → Bool) (LL : List Line) : Label → Nat → Prop
  | here {s : Label} {j : Nat} : ((af.fwd? s).isNone = true ∨ own s = true) →
      LL[j]? = some (.label (.block s)) → RepL af own LL s j
  | skip {s : Label} {j : Nat} {l : Lbl} : ((af.fwd? s).isNone = true ∨ own s = true) →
      LL[j]? = some (.label l) → RepL af own LL s (j + 1) → RepL af own LL s j
  | fwd {s x : Label} {j : Nat} : af.fwd? s = some x → RepL af own LL x j → RepL af own LL s j

theorem repAt_repL {af : AFunc} {own : Label → Bool} {L : List Line} :
    ∀ (fuel : Nat) (s : Label) (j : Nat), repAt af own L.toArray fuel s j = true → RepL af own L s j
  | 0, _, _, h => by simp [repAt] at h
  | fuel + 1, s, j, h => by
    simp only [repAt, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with ⟨hown, hl⟩ | hf
    · have hown' : (af.fwd? s).isNone = true ∨ own s = true := by simpa using hown
      split at hl
      · rename_i l hL
        simp only [Bool.or_eq_true, beq_iff_eq] at hl
        have hL' : L[j]? = some (.label (.block l)) := by simpa using hL
        rcases hl with rfl | hr
        · exact .here hown' hL'
        · exact .skip hown' hL' (repAt_repL fuel s (j + 1) hr)
      · rename_i l _ hL
        exact .skip hown' (by simpa using hL) (repAt_repL fuel s (j + 1) hl)
      · cases hl
    · split at hf
      · rename_i x hx
        exact .fwd hx (repAt_repL fuel x j hf)
      · cases hf

theorem repOn_repL {af : AFunc} {own : Label → Bool} {L : List Line} {s : Label} {j : Nat}
    (h : repOn af own L s j = true) : RepL af own L s j :=
  repAt_repL _ s j h

/-! ## Branch relaxation keeps the representing lines -/

/-- The index in the relaxed lines of line `j`. -/
def rix (F : Lbl → Bool) (L : List Line) (j : Nat) : Nat := (relaxLines F (L.take j)).length

theorem relax_split (F : Lbl → Bool) (L : List Line) (j : Nat) :
    relaxLines F L = relaxLines F (L.take j) ++ relaxLines F (L.drop j) := by
  rw [← relaxLines_append, List.take_append_drop]

/-- The relaxed lines from line `j`'s index on are the relaxation of the lines from `j` on. -/
theorem relax_drop (F : Lbl → Bool) (L : List Line) (j : Nat) :
    (relaxLines F L).drop (rix F L j) = relaxLines F (L.drop j) := by
  rw [relax_split F L j, rix, List.drop_left]

theorem relax_label {F : Lbl → Bool} {L : List Line} {j : Nat} {l : Lbl}
    (h : L[j]? = some (.label l)) :
    (relaxLines F L)[rix F L j]? = some (.label l) ∧ rix F L (j + 1) = rix F L j + 1 := by
  have hd : L.drop j = .label l :: L.drop (j + 1) := by
    rw [List.drop_eq_getElem_cons (by have := (List.getElem?_eq_some_iff.mp h).1; omega)]
    congr 1
    exact (Option.some.inj ((List.getElem?_eq_getElem _).symm.trans h))
  constructor
  · have := congrArg (·[0]?) (relax_drop F L j)
    simp only [List.getElem?_drop, Nat.add_zero, hd, relaxLines_cons, relaxLine_label] at this
    simpa using this
  · unfold rix
    rw [List.take_add_one, h, relaxLines_append]
    simp [relaxLines]

/-- `RepL` on the relaxed lines. -/
theorem RepL.relax {af : AFunc} {own : Label → Bool} {L : List Line} (F : Lbl → Bool)
    {s : Label} {j : Nat} (h : RepL af own L s j) : RepL af own (relaxLines F L) s (rix F L j) := by
  induction h with
  | here ho hl => exact .here ho (relax_label hl).1
  | skip ho hl _ ih =>
    have := relax_label (F := F) hl
    exact .skip ho this.1 (by rw [← this.2]; exact ih)
  | fwd hx _ ih => exact .fwd hx ih

/-! ## What `termOk` accepts -/

/-- A branch target `l'` reaches block `s`: a block label whose line (`idx`) represents `s`. -/
def RepLbl (rep : Label → Nat → Bool) (idx : Std.HashMap Label Nat) (s : Label) (l' : Lbl) : Prop :=
  ∃ l j, l' = .block l ∧ idx[l]? = some j ∧ rep s j = true

theorem repLbl_of {rep : Label → Nat → Bool} {idx : Std.HashMap Label Nat} {s : Label} {l' : Lbl}
    (h : repLbl rep idx s l' = true) : RepLbl rep idx s l' := by
  unfold repLbl at h
  split at h
  · rename_i l
    split at h
    · rename_i j hj
      exact ⟨l, j, rfl, hj, h⟩
    · cases h
  · cases h

/-- **A `jump x`'s final lines**: `b l'` to a label representing `x`, or nothing when the next
line represents `x`. -/
theorem termOk_jump {rep : Label → Nat → Bool} {idx : Std.HashMap Label Nat} {x : Label}
    {t o : List Line} {nxt : Nat} (h : termOk rep idx (some (.inst (.jump x))) t o nxt = true) :
    (∃ l', o = [.ins (.b l') none] ∧ RepLbl rep idx x l') ∨ (o = [] ∧ rep x nxt = true) := by
  simp only [termOk] at h
  split at h
  · exact .inl ⟨_, rfl, repLbl_of h⟩
  · exact .inr ⟨rfl, h⟩
  · cases h

/-- **A conditional branch's final lines** (`ci` the branch to `s1`, else to `s2`): the
branch retargeted to a label representing `s1`, then `b` to one representing `s2`; or one
branch, retargeted (`s2` next) or inverted (`s1` next); or nothing (both next). -/
def CondOut (rep : Label → Nat → Bool) (idx : Std.HashMap Label Nat) (s1 s2 : Label) (ci : Insn)
    (o : List Line) (nxt : Nat) : Prop :=
  (∃ c t' e', o = [.ins c none, .ins (.b e') none] ∧ c.condTarget? = some t' ∧
      c = ci.setTarget t' ∧ RepLbl rep idx s1 t' ∧ RepLbl rep idx s2 e') ∨
  (∃ c t', o = [.ins c none] ∧ c.condTarget? = some t' ∧
      ((c = ci.setTarget t' ∧ RepLbl rep idx s1 t' ∧ rep s2 nxt = true) ∨
       (c = ci.invertTo t' ∧ RepLbl rep idx s2 t' ∧ rep s1 nxt = true))) ∨
  (o = [] ∧ rep s1 nxt = true ∧ rep s2 nxt = true)

theorem condOk_spec {rep : Label → Nat → Bool} {idx : Std.HashMap Label Nat} {s1 s2 : Label}
    {ci : Insn} {o : List Line} {nxt : Nat} (h : condOk rep idx s1 s2 ci o nxt = true) :
    CondOut rep idx s1 s2 ci o nxt := by
  unfold condOk at h
  split at h
  · rename_i c e'
    simp only [Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    split at h1
    · rename_i t' ht
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
      exact .inl ⟨c, t', e', rfl, ht, h1.1, repLbl_of h1.2, repLbl_of h2⟩
    · cases h1
  · rename_i c
    split at h
    · rename_i t' ht
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
      refine .inr (.inl ⟨c, t', rfl, ht, ?_⟩)
      rcases h with ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩
      · exact .inl ⟨h1, repLbl_of h2, h3⟩
      · exact .inr ⟨h1, repLbl_of h2, h3⟩
    · cases h
  · simp only [Bool.and_eq_true] at h
    exact .inr (.inr ⟨rfl, h.1, h.2⟩)
  · cases h

theorem termOk_condBr {rep : Label → Nat → Bool} {idx : Std.HashMap Label Nat} {tl el : Label}
    {k : CondBrKind} {t o : List Line} {nxt : Nat}
    (h : termOk rep idx (some (.inst (.condBr tl el k))) t o nxt = true) :
    CondOut rep idx tl el (k.insn (.block tl)) o nxt :=
  condOk_spec h

theorem termOk_tbz {rep : Label → Nat → Bool} {idx : Std.HashMap Label Nat} {tl el : Label}
    {k : TestBitAndBranchKind} {rn : Reg} {bit : Nat} {t o : List Line} {nxt : Nat}
    (h : termOk rep idx (some (.inst (.testBitAndBranch k tl el rn bit))) t o nxt = true) :
    CondOut rep idx tl el (.tbz (k == .nz) rn bit (.block tl)) o nxt :=
  condOk_spec h

/-- **A `try_call`'s final lines**: the call, then `b` to a label representing the
continuation, or the call alone when the next line represents it. -/
theorem termOk_tryCall {rep : Label → Nat → Bool} {idx : Std.HashMap Label Nat} {info : CallInfo}
    {ti : TryInfo} {t o : List Line} {nxt : Nat}
    (h : termOk rep idx (some (.inst (.tryCall info ti))) t o nxt = true) :
    ∃ call b0, t = [call, b0] ∧
      ((∃ l', o = [call, .ins (.b l') none] ∧ RepLbl rep idx ti.continuation l') ∨
       (o = [call] ∧ rep ti.continuation nxt = true)) := by
  simp only [termOk] at h
  split at h
  · rename_i call b0 call' l'
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h2⟩ := h
    exact ⟨call, b0, rfl, .inl ⟨l', rfl, repLbl_of h2⟩⟩
  · rename_i call b0 call'
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h2⟩ := h
    exact ⟨call, b0, rfl, .inr ⟨rfl, h2⟩⟩
  · cases h

/-- A final line for line `x` of the last instruction: `x` itself, or `x` retargeted to a block
label representing `x`'s block target. -/
def LineOut (rep : Label → Nat → Bool) (idx : Std.HashMap Label Nat) (x y : Line) : Prop :=
  y = x ∨ ∃ l l', x.target? = some (.block l) ∧ y.target? = some l' ∧ y = x.relabel (fun _ => l') ∧
    RepLbl rep idx l l'

theorem keptOk_spec {rep : Label → Nat → Bool} {idx : Std.HashMap Label Nat} {t o : List Line}
    (h : keptOk rep idx t o = true) :
    o.length = t.length ∧ ∀ (i : Nat) (x y : Line), t[i]? = some x → o[i]? = some y →
      LineOut rep idx x y := by
  unfold keptOk at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨hl, ha⟩ := h
  refine ⟨hl, fun i x y hx hy => ?_⟩
  have hm : (x, y) ∈ t.zip o := by
    rw [List.mem_iff_getElem?]
    exact ⟨i, by rw [List.getElem?_zip_eq_some]; exact ⟨hx, hy⟩⟩
  have := ha _ hm
  unfold lineOk at this
  simp only [Bool.or_eq_true, beq_iff_eq] at this
  rcases this with e | h2
  · exact .inl e.symm
  · right
    split at h2
    · rename_i l l' h1 h3
      simp only [Bool.and_eq_true, beq_iff_eq] at h2
      exact ⟨l, l', h1, h3, h2.1, repLbl_of h2.2⟩
    · cases h2

/-- **Any other last instruction**: its lines, each kept or retargeted (`LineOut`). -/
theorem termOk_kept {rep : Label → Nat → Bool} {idx : Std.HashMap Label Nat} {a : Option AInst}
    {t o : List Line} {nxt : Nat}
    (hj : ∀ x, a ≠ some (.inst (.jump x)))
    (hc : ∀ tl el k, a ≠ some (.inst (.condBr tl el k)))
    (hb : ∀ k tl el rn bit, a ≠ some (.inst (.testBitAndBranch k tl el rn bit)))
    (ht : ∀ info ti, a ≠ some (.inst (.tryCall info ti)))
    (h : termOk rep idx a t o nxt = true) :
    o.length = t.length ∧ ∀ (i : Nat) (x y : Line), t[i]? = some x → o[i]? = some y →
      LineOut rep idx x y := by
  unfold termOk at h
  split at h
  · exact (hj _ rfl).elim
  · exact (hc _ _ _ rfl).elim
  · exact (hb _ _ _ _ _ rfl).elim
  · exact (ht _ _ rfl).elim
  · exact keptOk_spec h

end Backend
