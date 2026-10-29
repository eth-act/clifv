import FV.E2E.RegLevelEmit

/-!
# `MachBuffer`'s simplification never grows the code (#553)

`machBuf` only removes branch lines, inverts a conditional branch in place, aliases labels and
retargets references (`MBuf.step`, `Line.relabel`): its lines are at most as many bytes as its
input (`machBuf_bytes`). With `splitSegs_lines` this bounds the emission plan's lines by the
unsimplified segments' (`emitPlan_bytes`).
-/

namespace Backend

/-! ## Generic facts about `MBuf` -/

/-- `lastCode` names an index before `n` holding a line. -/
theorem lastCode_spec (out : Array Line) : ∀ (n k : Nat), lastCode out n = some k →
    k < n ∧ ∃ ln, out[k]? = some ln
  | 0, _, h => by simp [lastCode] at h
  | n + 1, k, h => by
    unfold lastCode at h
    cases hx : out[n]? with
    | none => simp only [hx] at h; cases h
    | some ln =>
      simp only [hx] at h
      cases ln with
      | label _ =>
        obtain ⟨hlt, hk⟩ := lastCode_spec out n k h
        exact ⟨by omega, hk⟩
      | _ => simp only [Option.some.injEq] at h; subst h; exact ⟨by omega, _, hx⟩

theorem lastCode_lt (out : Array Line) (k p : Nat) (h : lastCode out k = some p) : p < k :=
  (lastCode_spec out k p h).1

/-- An invariant of a `forIn` in `Id`. -/
theorem mbForIn_inv {α σ : Type} (l : List α) (init : σ) (f : α → σ → Id (ForInStep σ))
    (P : σ → Prop) (h0 : P init) (hf : ∀ a s, P s → P (f a s).run.value) :
    P (forIn l init f).run := by
  induction l generalizing init with
  | nil => simpa using h0
  | cons a l ih =>
    rw [List.forIn_cons]
    have := hf a init h0
    cases hfa : f a init with
    | done b => rw [hfa] at this; simp only [Id.run_bind]; exact this
    | yield b => rw [hfa] at this; simp only [Id.run_bind]; exact ih b this

theorem dropWhile_eq_drop {α : Type} (p : α → Bool) (l : List α) :
    l.dropWhile p = l.drop (l.takeWhile p).length := by
  induction l with
  | nil => rfl
  | cons a l ih => by_cases hp : p a <;> simp [hp, ih]

/-- `splitSegs` re-splits the lines it was given. -/
theorem splitSegs_lines : ∀ (ss : List Seg) (L : List Line) (os : List (List Line)),
    splitSegs ss L = some os → segLines ss os = L
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp [splitSegs] at h
  | s :: ss, .label (.block l) :: rest, os, h => by
    unfold splitSegs at h
    split at h
    · simp at h
    · split at h
      · simp at h
      · rename_i hl hbody
        simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hl hbody
        subst hl
        rw [Option.map_eq_some_iff] at h
        obtain ⟨os', hm, rfl⟩ := h
        have ih := splitSegs_lines ss _ os' hm
        simp only [segLines]
        rw [ih, ← dropWhile_eq_drop, List.cons_append, List.append_assoc,
          List.takeWhile_append_dropWhile]
        conv => rhs; rw [← List.take_append_drop s.body.length rest, hbody]
  | _ :: _, [], _, h => by simp [splitSegs] at h
  | _ :: _, .ins _ _ :: _, _, h => by simp [splitSegs] at h
  | _ :: _, .word _ _ :: _, _, h => by simp [splitSegs] at h

/-! ## Byte sizes -/

/-- The byte size of a line list (`E2E.linesBytes`). -/
abbrev lineBytes (L : List Line) : Nat := (L.map Line.size).sum

theorem lineBytes_eraseIdx : ∀ (L : List Line) (k : Nat), lineBytes (L.eraseIdx k) ≤ lineBytes L
  | [], _ => by simp
  | a :: L, 0 => by simp only [lineBytes, List.eraseIdx_cons_zero, List.map_cons, List.sum_cons]; omega
  | a :: L, k + 1 => by
    have := lineBytes_eraseIdx L k
    simp only [lineBytes, List.eraseIdx_cons_succ, List.map_cons, List.sum_cons] at this ⊢
    omega

theorem lineBytes_set : ∀ (L : List Line) (p : Nat) (y : Line),
    (∀ x, L[p]? = some x → x.size = y.size) → lineBytes (L.set p y) = lineBytes L
  | [], _, _, _ => by simp
  | a :: L, 0, y, h => by
    have := h a rfl
    simp only [lineBytes, List.set_cons_zero, List.map_cons, List.sum_cons, this]
  | a :: L, p + 1, y, h => by
    have := lineBytes_set L p y (fun x hx => h x (by simpa using hx))
    simp only [lineBytes, List.set_cons_succ, List.map_cons, List.sum_cons] at this ⊢
    rw [this]

theorem lineBytes_relabel (f : Lbl → Lbl) : ∀ L : List Line, lineBytes (L.map (Line.relabel f)) = lineBytes L
  | [] => rfl
  | ln :: L => by
    have ih := lineBytes_relabel f L
    have h1 : (ln.relabel f).size = ln.size := by
      cases ln with
      | ins i tc =>
        simp only [Line.relabel]
        split <;> rfl
      | word _ _ => rfl
      | label _ => rfl
    simp only [lineBytes, List.map_map, List.map_cons, List.sum_cons] at ih ⊢
    rw [← ih, Function.comp_def]
    simp only [h1]

/-- A conditional branch is one instruction line. -/
theorem size_of_cbr {ln : Line} {ct : Lbl} (h : ln.cbr? = some ct) : ln.size = 4 := by
  cases ln with
  | ins _ _ => rfl
  | _ => simp [Line.cbr?] at h

/-- **One round of `optimize_branches` never grows the lines.** -/
theorem step_bytes (allLabels : Bool) (m m' : MBuf) (h : MBuf.step allLabels m = some m') :
    lineBytes m'.out.toList ≤ lineBytes m.out.toList := by
  have hE : ∀ k, lineBytes (m.erase k).toList ≤ lineBytes m.out.toList := fun k => by
    simp only [MBuf.erase, List.toList_toArray]; exact lineBytes_eraseIdx _ k
  unfold MBuf.step at h
  rcases hlc : lastCode m.out m.out.size with - | k
  · simp [hlc] at h
  obtain ⟨-, ln, hkln⟩ := lastCode_spec m.out m.out.size k hlc
  have hln : m.out[k]! = ln := by simp [getElem!_def, hkln]
  rcases ht : (ln.ubr?).orElse (fun _ => ln.cbr?) with - | t
  · simp only [hlc, hln, ht, Option.bind_eq_bind, Option.bind_some, Option.bind_none] at h
    cases h
  simp only [hlc, hln, ht, Option.bind_eq_bind, Option.bind_some, Option.bind_none] at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (cases h; exact hE k)
    | (cases h; exact Nat.le_refl _)
    | skip
  all_goals
    rcases hpp : lastCode m.out k with - | p
    · simp only [hpp, Option.bind_none] at h; cases h
    obtain ⟨hpk, lp, hlp⟩ := lastCode_spec _ _ _ hpp
    have hlp' : m.out[p]! = lp := by simp [getElem!_def, hlp]
    simp only [hpp, hlp', Option.bind_some] at h
    split at h
    · cases h; exact hE k
    rcases hct : lp.cbr? with - | ct
    · simp only [hct, Option.bind_none] at h; cases h
    simp only [hct, Option.bind_some] at h
    split at h
    · cases h
    split at h
    · rename_i c tc _
      cases h
      show lineBytes ((m.erase k).set! p _).toList ≤ _
      rw [Array.set!, Array.toList_setIfInBounds, lineBytes_set]
      · exact hE k
      · intro x hx
        simp only [MBuf.erase, List.toList_toArray, List.getElem?_eraseIdx_of_lt hpk,
          Array.getElem?_toList, hlp, Option.some.injEq] at hx
        subst hx
        rw [size_of_cbr hct]
        rfl
    · cases h

theorem optimize_bytes (allLabels : Bool) (m : MBuf) :
    lineBytes (MBuf.optimize allLabels m).out.toList ≤ lineBytes m.out.toList := by
  unfold MBuf.optimize
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range']
  refine mbForIn_inv (P := fun m' : MBuf => lineBytes m'.out.toList ≤ lineBytes m.out.toList)
    _ _ _ (Nat.le_refl _) ?_
  intro _ s hs
  split
  · rename_i m' h; exact Nat.le_trans (step_bytes _ _ _ h) hs
  · exact hs

theorem fold_bytes (g : MBuf → Line → MBuf)
    (hg : ∀ m ln, lineBytes (g m ln).out.toList ≤ lineBytes m.out.toList + ln.size) :
    ∀ (ls : List Line) (m : MBuf),
      lineBytes (ls.foldl g m).out.toList ≤ lineBytes m.out.toList + lineBytes ls
  | [], m => by simp
  | ln :: ls, m => by
    rw [List.foldl_cons]
    have := fold_bytes g hg ls (g m ln)
    have := hg m ln
    simp only [lineBytes, List.map_cons, List.sum_cons] at *
    omega

/-- **`MachBuffer`'s simplification never grows the code.** -/
theorem machBuf_bytes (allLabels : Bool) (ls : List Line) :
    lineBytes (machBuf allLabels ls).1 ≤ lineBytes ls := by
  unfold machBuf
  dsimp only
  rw [lineBytes_relabel]
  refine Nat.le_trans (optimize_bytes _ _) ?_
  refine Nat.le_trans (fold_bytes _ ?_ ls {}) (by simp [lineBytes])
  intro m ln
  have hp : lineBytes (m.out.push ln).toList = lineBytes m.out.toList + ln.size := by
    simp [lineBytes, Array.toList_push]
  split <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;>
    first
    | exact Nat.le_trans (optimize_bytes _ _) (Nat.le_of_eq hp)
    | exact Nat.le_of_eq hp

/-- `machPlan`'s final lines are `machBuf`'s split into the segments. -/
theorem machPlan_split {af : AFunc} {a : Bool} {ss : List Seg} {ps : PState} {p : Plan}
    (h : machPlan af a ss ps = some p) :
    p.segs = ss ∧ splitSegs ss (machBuf a (segLines ss (ss.map (·.term)))).1 = some p.outs := by
  unfold machPlan at h
  simp only [bind, Option.bind] at h
  split at h
  · cases h
  rename_i os hos
  dsimp only at h
  split at h
  · cases h
    exact ⟨rfl, hos⟩
  · cases h

/-- **The emission plan's lines are at most as many bytes as the unsimplified segments'.** -/
theorem emitPlan_bytes {k : Nat} {af : AFunc} {p : Plan} (h : emitPlan k af = .ok p) :
    lineBytes (segLines p.segs p.outs) ≤ lineBytes (segLines p.segs (p.segs.map (·.term))) := by
  unfold emitPlan at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  rename_i r hr
  obtain ⟨ss, ps⟩ := r
  dsimp only at h
  split at h
  · rename_i p1 h1
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    have h1' : machPlan af true ss ps = some p1 ∨ machPlan af false ss ps = some p1 := by
      cases e : machPlan af true ss ps with
      | some q => rw [e] at h1; simp only [Option.orElse] at h1; exact .inl h1
      | none => rw [e] at h1; simp only [Option.orElse] at h1; exact .inr h1
    rcases h1' with h1' | h1' <;>
    · obtain ⟨hs, hsp⟩ := machPlan_split h1'
      rw [hs, splitSegs_lines _ _ _ hsp]
      exact machBuf_bytes _ _
  · split at h
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact Nat.le_refl _
    · cases h

end Backend
