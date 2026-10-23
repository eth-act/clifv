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
  (∃ c t' e', o = [.ins c none, .ins (.b e') none] ∧ (Line.ins c none).target? = some t' ∧
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

/-- A final line for line `x` of the last instruction: `x` itself if it has no block target,
else `x` retargeted to a block label representing `x`'s block target. -/
def LineOut (rep : Label → Nat → Bool) (idx : Std.HashMap Label Nat) (x y : Line) : Prop :=
  (y = x ∧ ∀ l, x.target? ≠ some (.block l)) ∨
    ∃ l l', x.target? = some (.block l) ∧ y.target? = some l' ∧ y = x.relabel (fun _ => l') ∧
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
  split at this
  · rename_i l hxt
    split at this
    · rename_i l' hyt
      simp only [Bool.and_eq_true, beq_iff_eq] at this
      exact .inr ⟨l, l', hxt, hyt, this.1, repLbl_of this.2⟩
    · cases this
  · rename_i hxt
    simp only [beq_iff_eq] at this
    exact .inl ⟨this.symm, fun l e => hxt l e⟩

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

/-! ## A block's segment in the emission plan -/

theorem segNxts_fst : ∀ (ss : List Seg) (os : List (List Line)) (n : Nat),
    os.length = ss.length → (segNxts ss os n).map (·.1) = ss
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | s :: ss, o :: os, n, h => by
    simp only [segNxts, List.map_cons]
    rw [segNxts_fst ss os _ (by simpa using h)]

theorem nodup_map_inj {α β : Type} {f : α → β} : ∀ {l : List α}, (l.map f).Nodup →
    ∀ {x y : α}, x ∈ l → y ∈ l → f x = f y → x = y
  | [], _, _, _, hx, _, _ => by simp at hx
  | a :: l, h, x, y, hx, hy, he => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at h
    simp only [List.mem_cons] at hx hy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · rfl
    · exact absurd he.symm (h.1 y hy)
    · exact absurd he (h.1 x hx)
    · exact nodup_map_inj h.2 hx hy he

/-- Block `b`'s segment in the emission plan of `emitFunc k af`, with its final lines and the
line after them (`segNxts`). -/
def segX (k : Nat) (af : AFunc) (b : Nat) : Option (Seg × List Line × Nat) :=
  match emitPlan k af with
  | .ok p => (segNxts p.segs p.outs 0).find? (·.1.idx == b)
  | .error _ => none

/-- The lines of the emission plan (before relaxation). -/
def planLines (k : Nat) (af : AFunc) : List Line :=
  match emitPlan k af with
  | .ok p => p.lines
  | .error _ => []

/-- The trusted forwarding blocks of the emission plan (`segsTrust`). -/
def planOwn (k : Nat) (af : AFunc) : Label → Bool :=
  match emitPlan k af with
  | .ok p => fun l => (segsTrust af p.segs p.outs p.lines).contains l
  | .error _ => fun _ => false

/-- The representation of blocks by the plan's lines (`repOn` with the trusted blocks). -/
def planRep (k : Nat) (af : AFunc) : Label → Nat → Bool := repOn af (planOwn k af) (planLines k af)

/-- Block `b`'s segment passes `termOk` (with the plan's trusted forwarding blocks). -/
def SegChecked (k : Nat) (af : AFunc) (b : Nat) : Prop :=
  ∃ x, segX k af b = some x ∧
    segTermOk af (planRep k af) (blockLabelIdx (planLines k af)) x = true

theorem segX_mem {k : Nat} {af : AFunc} {p : Plan} (hp : emitPlan k af = .ok p) {b : Nat}
    {x : Seg × List Line × Nat} (h : segX k af b = some x) :
    x ∈ segNxts p.segs p.outs 0 ∧ x.1.idx = b := by
  unfold segX at h
  rw [hp] at h
  simp only at h
  have := List.find?_some h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using this⟩

/-- **Segment `i` of the plan** is block `s.idx`'s (`segX`), with the line after it. -/
theorem segX_get {k : Nat} {af : AFunc} {p : Plan} (hp : emitPlan k af = .ok p) {i : Nat}
    {s : Seg} {o : List Line} (hs : p.segs[i]? = some s) (ho : p.outs[i]? = some o) :
    ∃ A, p.lines = A ++ .label (.block s.label) :: (s.body ++ o) ++
        (segLines (p.segs.drop (i + 1)) (p.outs.drop (i + 1)) ++ trapLines p.ps) ∧
      segX k af s.idx = some (s, o, A.length + 1 + s.body.length + o.length) := by
  obtain ⟨hseg, hlen, -⟩ := emitPlan_spec hp
  obtain ⟨hl, -, hss⟩ := segsOf_spec hseg
  have hidx : p.segs.map (·.idx) = (emitOrder af).map (·.2) := by
    apply List.ext_getElem?
    intro n
    simp only [List.getElem?_map]
    cases hn : p.segs[n]? with
    | none =>
      have : (emitOrder af).length ≤ n := by
        rw [← hl]; exact List.getElem?_eq_none_iff.mp hn
      simp [List.getElem?_eq_none_iff.mpr this]
    | some s' =>
      obtain ⟨code, -, -, -, hb, -⟩ := hss n s' hn
      simp [hb]
  have hnd : ((segNxts p.segs p.outs 0).map (·.1.idx)).Nodup := by
    have e : (segNxts p.segs p.outs 0).map (·.1.idx) = p.segs.map (·.idx) := by
      conv => rhs; rw [← segNxts_fst p.segs p.outs 0 hlen]
      rw [List.map_map]; rfl
    rw [e, hidx]; exact emitOrder_nodup af
  obtain ⟨A, hA, hm⟩ := segNxts_get (n := 0) hs ho
  refine ⟨A, by rw [Plan.lines, hA]; simp, ?_⟩
  unfold segX
  rw [hp]
  simp only
  cases hf : (segNxts p.segs p.outs 0).find? (·.1.idx == s.idx) with
  | none =>
    have := List.find?_eq_none.mp hf _ hm
    simp at this
  | some y =>
    have hy := List.mem_of_find?_eq_some hf
    have hyi : y.1.idx = s.idx := by simpa using List.find?_some hf
    have := nodup_map_inj hnd hy hm hyi
    rw [this]
    simp

/-- **Segment `x` of block `b` was checked** unless `b` forwards and is not trusted. -/
theorem segChecked_of {k : Nat} {af : AFunc} {p : Plan} (hp : emitPlan k af = .ok p) {b : Nat}
    {x : Seg × List Line × Nat} (h : segX k af b = some x)
    (hown : (af.fwd? x.1.label).isNone = true ∨ planOwn k af x.1.label = true) :
    SegChecked k af b := by
  obtain ⟨-, -, hok, -⟩ := emitPlan_spec hp
  obtain ⟨-, -, hall⟩ := segsOk_spec hok
  obtain ⟨hm, -⟩ := segX_mem hp h
  refine ⟨x, h, ?_⟩
  have hpl : planLines k af = p.lines := by simp [planLines, hp]
  have hpo : planOwn k af = fun l => (segsTrust af p.segs p.outs p.lines).contains l := by
    simp [planOwn, hp]
  rcases hall x hm with ⟨hf, hn⟩ | hc
  · exfalso
    rcases hown with h1 | h1
    · simp_all
    · rw [hpo] at h1; simp_all
  · unfold planRep
    rw [hpl, hpo]
    exact hc

/-! ## The unsimplified lines pass the branch check (`segsOk_raw`)

`emitPlan` falls back to the segments' own lines when `MachBuffer`'s simplification is not
accepted; `segsOk_raw` shows the check accepts that fallback whenever each segment's last
instruction has its unsimplified lines (`RawTerm`) and every block target among them is a
segment's label: so `emitPlan` fails only if `segsOf` does. -/

/-- The unsimplified lines `t` of a block's last instruction `a` (`MInst.lines`). -/
def RawTerm : Option AInst → List Line → Prop
  | some (.inst (.jump x)), t => t = [.ins (.b (.block x)) none]
  | some (.inst (.condBr tl el k)), t =>
    t = [.ins (k.insn (.block tl)) none, .ins (.b (.block el)) none]
  | some (.inst (.testBitAndBranch k tl el rn bit)), t =>
    t = [.ins (.tbz (k == .nz) rn bit (.block tl)) none, .ins (.b (.block el)) none]
  | some (.inst (.tryCall _ ti)), t => ∃ call, t = [.ins call none, .ins (.b (.block ti.continuation)) none]
  | _, _ => True

theorem Line.relabel_self {x : Line} {t : Lbl} (h : x.target? = some t) :
    x.relabel (fun _ => t) = x := by
  cases x with
  | ins i tc =>
    simp only [Line.relabel, h]
    cases i <;> simp_all [Line.target?, Insn.setTarget]
  | word a b => simp_all [Line.target?, Line.relabel]
  | label l => simp [Line.target?] at h

theorem lineOk_self {rep : Label → Nat → Bool} {idx : Std.HashMap Label Nat} {x : Line}
    (h : ∀ l, x.target? = some (.block l) → repLbl rep idx l (.block l) = true) :
    lineOk rep idx x x = true := by
  unfold lineOk
  split
  · rename_i l hxt
    rw [hxt]
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨(Line.relabel_self hxt).symm, h l hxt⟩
  · simp

theorem keptOk_self {rep : Label → Nat → Bool} {idx : Std.HashMap Label Nat} :
    ∀ {t : List Line}, (∀ ln ∈ t, ∀ l, ln.target? = some (.block l) →
      repLbl rep idx l (.block l) = true) → keptOk rep idx t t = true
  | [], _ => by simp [keptOk]
  | x :: t, h => by
    have ih := keptOk_self (rep := rep) (idx := idx) (t := t)
      (fun ln hl => h ln (List.mem_cons_of_mem _ hl))
    simp only [keptOk, Bool.and_eq_true, beq_iff_eq, List.zip_cons_cons, List.all_cons,
      List.length_cons] at ih ⊢
    exact ⟨trivial, lineOk_self (h x List.mem_cons_self), ih.2⟩

/-- `termOk` accepts a last instruction's unsimplified lines, kept as they are. -/
theorem termOk_raw {rep : Label → Nat → Bool} {idx : Std.HashMap Label Nat} {a : Option AInst}
    {t : List Line} {nxt : Nat} (hraw : RawTerm a t)
    (hrep : ∀ ln ∈ t, ∀ l, ln.target? = some (.block l) → repLbl rep idx l (.block l) = true) :
    termOk rep idx a t t nxt = true := by
  unfold termOk
  split
  · rename_i x
    simp only [RawTerm] at hraw
    subst hraw
    exact hrep _ List.mem_cons_self x rfl
  · rename_i tl el k
    simp only [RawTerm] at hraw
    subst hraw
    have h1 : (Line.ins (k.insn (.block tl)) none).target? = some (.block tl) := by
      cases k <;> rfl
    have hs : Insn.setTarget (.block tl) (k.insn (.block tl)) = k.insn (.block tl) := by
      cases k <;> rfl
    have hA := hrep _ List.mem_cons_self tl h1
    have hB := hrep (.ins (.b (.block el)) none) (by simp) el rfl
    simp [condOk, h1, hs, hA, hB]
  · rename_i k tl el rn bit
    simp only [RawTerm] at hraw
    subst hraw
    have h1 : (Line.ins (.tbz (k == .nz) rn bit (.block tl)) none).target? = some (.block tl) := rfl
    have hs : Insn.setTarget (.block tl) (.tbz (k == .nz) rn bit (.block tl)) =
        .tbz (k == .nz) rn bit (.block tl) := rfl
    have hA := hrep _ List.mem_cons_self tl h1
    have hB := hrep (.ins (.b (.block el)) none) (by simp) el rfl
    simp [condOk, h1, hs, hA, hB]
  · rename_i ti
    simp only [RawTerm] at hraw
    obtain ⟨call, rfl⟩ := hraw
    have hB := hrep (.ins (.b (.block ti.continuation)) none) (by simp) ti.continuation rfl
    simp [hB]
  · exact keptOk_self hrep

theorem blockLabelIdx_go_some : ∀ (L : List Line) (n : Nat) (l : Label),
    Line.label (.block l) ∈ L → ∃ j,
      ((L.zipIdx n).foldr (fun (x : Line × Nat) (m : Std.HashMap Label Nat) => match x.1 with
        | .label (.block l) => m.insert l x.2
        | _ => m) {})[l]? = some j
  | [], n, l, h => by simp at h
  | ln :: L, n, l, h => by
    simp only [List.zipIdx_cons, List.foldr_cons]
    split
    · rename_i _ l'
      rw [Std.HashMap.getElem?_insert]
      split
      · exact ⟨_, rfl⟩
      · rename_i hne
        rcases List.mem_cons.1 h with e | hm
        · simp only [Line.label.injEq, Lbl.block.injEq] at e
          subst e
          simp at hne
        · exact blockLabelIdx_go_some L (n + 1) l hm
    · rename_i hn
      rcases List.mem_cons.1 h with e | hm
      · exact (hn l e.symm).elim
      · exact blockLabelIdx_go_some L (n + 1) l hm

theorem blockLabelIdx_some {L : List Line} {l : Label} (h : Line.label (.block l) ∈ L) :
    ∃ j, (blockLabelIdx L)[l]? = some j :=
  blockLabelIdx_go_some L 0 l h

/-- A block label's own line represents it, unless it forwards and is not `own`. -/
theorem repLbl_self {af : AFunc} {own : Label → Bool} {L : List Line} {l : Label}
    (hm : Line.label (.block l) ∈ L) (hown : (af.fwd? l).isSome = true → own l = true) :
    repLbl (repOn af own L) (blockLabelIdx L) l (.block l) = true := by
  obtain ⟨j, hj⟩ := blockLabelIdx_some hm
  have hL : L.toArray[j]? = some (.label (.block l)) := by
    simpa using blockLabelIdx_get hj
  simp only [repLbl, hj, repOn]
  unfold repAt
  rw [hL]
  cases hf : af.fwd? l <;> simp_all

theorem trustFwd_all {af : AFunc} {L : List Line} {idx : Std.HashMap Label Nat}
    {ts : List (Seg × List Line × Nat)} : ∀ (n : Nat) (S : List Label),
    (∀ l ∈ S, ts.any (fun x => x.1.label == l &&
      segTermOk af (repOn af (S.contains ·) L) idx x) = true) → trustFwd af L idx ts n S = S
  | 0, _, _ => rfl
  | n + 1, S, h => by
    simp only [trustFwd]
    rw [List.filter_eq_self.2 h]
    simp

theorem segLines_label_mem : ∀ {ss : List Seg} {os : List (List Line)} {s : Seg},
    os.length = ss.length → s ∈ ss → Line.label (.block s.label) ∈ segLines ss os
  | [], _, _, _, h => by simp at h
  | _ :: _, [], _, h, _ => by simp at h
  | s0 :: ss, o :: os, s, hl, h => by
    simp only [segLines]
    rcases List.mem_cons.1 h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_append_right _
        (segLines_label_mem (by simpa using hl) h))

/-- **The unsimplified lines pass `segsOk`** (the fallback of `emitPlan`): entry first, every
last instruction with its unsimplified lines (`RawTerm`), every block target among them a
segment's label. -/
theorem segsOk_raw {af : AFunc} {ss : List Seg} {ps : PState}
    (h0 : ss.head?.map (·.idx) = some 0)
    (hraw : ∀ s ∈ ss, RawTerm (af.blocks[s.idx]?.bind (·.2.back?)) s.term)
    (hlab : ∀ s ∈ ss, ∀ ln ∈ s.term, ∀ l, ln.target? = some (.block l) → ∃ s' ∈ ss, s'.label = l) :
    segsOk af ss (ss.map (·.term)) (segLines ss (ss.map (·.term)) ++ trapLines ps) = true := by
  have hlen : (ss.map (·.term)).length = ss.length := by simp
  have hmem : ∀ s ∈ ss, Line.label (.block s.label) ∈
      segLines ss (ss.map (·.term)) ++ trapLines ps := fun s hs =>
    List.mem_append_left _ (segLines_label_mem hlen hs)
  have hx : ∀ x ∈ segNxts ss (ss.map (·.term)) 0, x.1 ∈ ss ∧ x.2.1 = x.1.term := by
    intro x hxm
    obtain ⟨i, h1, h2⟩ := segNxts_mem hxm
    rw [List.getElem?_map, h1] at h2
    simp only [Option.map_some, Option.some.injEq] at h2
    exact ⟨List.mem_of_getElem? h1, h2.symm⟩
  have hok : ∀ own : Label → Bool,
      (∀ s ∈ ss, (af.fwd? s.label).isSome = true → own s.label = true) →
      ∀ x ∈ segNxts ss (ss.map (·.term)) 0, segTermOk af
        (repOn af own (segLines ss (ss.map (·.term)) ++ trapLines ps))
        (blockLabelIdx (segLines ss (ss.map (·.term)) ++ trapLines ps)) x = true := by
    intro own hown x hxm
    obtain ⟨hs, ho⟩ := hx x hxm
    unfold segTermOk
    rw [ho]
    refine termOk_raw (hraw _ hs) fun ln hln l ht => ?_
    obtain ⟨s', hs', rfl⟩ := hlab _ hs ln hln l ht
    exact repLbl_self (hmem s' hs') (hown s' hs')
  -- every forwarding segment stays trusted
  have hfw : ∀ s ∈ ss, (af.fwd? s.label).isSome = true →
      (((segNxts ss (ss.map (·.term)) 0).filter fun x => (af.fwd? x.1.label).isSome).map
        (·.1.label)).contains s.label = true := by
    intro s hs hf
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hs
    have ho : (ss.map (·.term))[i]? = some s.term := by simp [hi]
    obtain ⟨A, -, hm⟩ := segNxts_get (n := 0) hi ho
    simp only [List.contains_iff_mem, List.mem_map, List.mem_filter]
    exact ⟨_, ⟨hm, hf⟩, rfl⟩
  have hS : segsTrust af ss (ss.map (·.term)) (segLines ss (ss.map (·.term)) ++ trapLines ps) =
      ((segNxts ss (ss.map (·.term)) 0).filter fun x => (af.fwd? x.1.label).isSome).map
        (·.1.label) := by
    unfold segsTrust
    apply trustFwd_all
    intro l hl
    obtain ⟨x, hxf, rfl⟩ := List.mem_map.1 hl
    have hxm := (List.mem_filter.1 hxf).1
    rw [List.any_eq_true]
    exact ⟨x, hxm, by
      simp only [beq_self_eq_true, Bool.true_and]
      exact hok _ (fun s hs hf => hfw s hs hf) x hxm⟩
  unfold segsOk
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true]
  refine ⟨⟨hlen.symm, h0⟩, fun x hxm => .inr ?_⟩
  rw [hS]
  exact hok _ (fun s hs hf => hfw s hs hf) x hxm

end Backend
