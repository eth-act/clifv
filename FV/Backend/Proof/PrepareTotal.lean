module

public import FV.Backend.Proof.PrepareTotalIsel
public import FV.Backend.Proof.SpillEdgesLow
public import FV.Backend.Proof.LowerDecide

@[expose] public section

/-!
# `prepare` never fails on `lowerFunction`'s VCode

`prepare` (`FV/Backend/RegallocOps.lean`) fails when a `VCode.cfg` fails (an empty block, a
block not ending in a terminator, a branch to an unknown label), when the entry block is a branch
target or has parameters, or when a terminator cannot be retargeted (`setTargets`). None of these
happens on `lowerFunction`'s VCode for input in scope (`prepare_ok`); no new input condition is
needed.

* `PrepIn vc`: what `prepare` needs of its input — `PrepDomain`, a parameterless entry, and every
  block ending in a terminator whose targets are labels of blocks other than the entry.
* `prepare_ok_of`: `PrepIn vc` ⇒ `prepare` succeeds. The kept blocks inherit `PrepIn`'s CFG facts
  (the targets of a reachable block are reachable); the entry has no predecessor; the
  critical-edge-splitting loop never throws (a block with two successor edges ends in a branch
  whose `setTargets` accepts one label per target) and establishes `SInv` (as `prepare_facts`)
  plus `EdgeT` (every edge block jumps to a kept label), so the split blocks have a CFG.
* `prepIn_of_lower`: `lowerFunction`'s VCode meets `PrepIn` on `Dominated`, `LowerScope` input
  (labels are block indices; a raw block ends in its terminator's lowering — a `return`/`trap`'s
  ends in `rets`/`udf`, `PrepareTotalIsel` —, an edge block in a `jump` to a non-entry CLIF block;
  no CLIF successor is the entry).
-/

namespace Backend.Proof.Prep

open Backend Backend.Proof Backend.Proof.Driver Backend.Proof.Spill

/-! ## Generic facts -/

/-- A `forIn` in `Except` whose every step yields, with an invariant. -/
theorem forIn_ok_inv {ε α β : Type} (f : α → β → Except ε (ForInStep β)) :
    ∀ (l : List α) (P : Nat → β → Prop),
    (∀ k x b, l[k]? = some x → P k b → ∃ b', f x b = .ok (.yield b') ∧ P (k + 1) b') →
    ∀ b, P 0 b → ∃ r, forIn l b f = .ok r ∧ P l.length r
  | [], _, _, b, h0 => ⟨b, rfl, h0⟩
  | a :: l, P, hs, b, h0 => by
    obtain ⟨b', hb', hP⟩ := hs 0 a b rfl h0
    obtain ⟨r, hr, hPr⟩ := forIn_ok_inv f l (fun k => P (k + 1))
      (fun k x c hx hc => hs (k + 1) x c (by simpa using hx) hc) b' hP
    refine ⟨r, ?_, by simpa using hPr⟩
    rw [List.forIn_cons, hb']
    exact hr

theorem isTerminator_of_targets {i : MInst} (h : i.targets ≠ []) : i.isTerminator = true := by
  cases i <;> simp_all [MInst.targets, MInst.isTerminator, MInst.isBranch, MInst.isRet]

theorem isTerminator_mapRegs (g : Reg → Reg) (i : MInst) :
    (i.mapRegs g).isTerminator = i.isTerminator := by
  cases i <;> rfl

/-- `setTargets` accepts one label per target. -/
theorem setTargets_some {i : MInst} {ls : List Label} (hne : i.targets ≠ [])
    (hl : ls.length = i.targets.length) : ∃ i', i.setTargets ls = some i' := by
  cases i
  case jump l =>
    obtain ⟨a, rfl⟩ : ∃ a, ls = [a] := List.length_eq_one_iff.mp (by simpa [MInst.targets] using hl)
    exact ⟨_, rfl⟩
  case condBr tl el k =>
    rcases ls with _ | ⟨a, _ | ⟨b, _ | ⟨c, ls⟩⟩⟩ <;> simp [MInst.targets] at hl
    exact ⟨_, rfl⟩
  case testBitAndBranch k tl el rn bit =>
    rcases ls with _ | ⟨a, _ | ⟨b, _ | ⟨c, ls⟩⟩⟩ <;> simp [MInst.targets] at hl
    exact ⟨_, rfl⟩
  case jtSequence d ts ridx t1 t2 =>
    cases ls with
    | nil => simp [MInst.targets] at hl
    | cons a ls =>
      simp only [MInst.targets, List.length_cons, Nat.add_right_cancel_iff] at hl
      exact ⟨_, by simp [MInst.setTargets, hl]; rfl⟩
  case tryCall info ti =>
    simp only [MInst.targets, List.length_append, List.length_map, List.length_cons,
      List.length_nil, Nat.zero_add] at hl
    exact ⟨_, by simp [MInst.setTargets, hl]; rfl⟩
  all_goals simp [MInst.targets] at hne

theorem setTargets_term {i i' : MInst} {ls : List Label} (h : i.setTargets ls = some i') :
    i'.isTerminator = true := by
  unfold MInst.setTargets at h
  split at h
  all_goals (try split at h)
  all_goals (try (cases h; done))
  all_goals (cases h; rfl)

/-! ## What `prepare` needs -/

/-- **What `prepare` needs of its input**: `PrepDomain` (at least one block, distinct labels),
a parameterless entry block, and every block ending in a terminator whose targets are labels of
blocks other than the entry. -/
structure PrepIn (vc : VCode) : Prop where
  dom : PrepDomain vc
  entry : ∀ vb : VBlock, vc.blocks[0]? = some vb → vb.params = #[]
  term : ∀ (b : Nat) (vb : VBlock), vc.blocks[b]? = some vb → ∃ t : MInst,
    vb.insts.back? = some t ∧ t.isTerminator = true ∧
    ∀ l ∈ t.targets, ∃ k, lab vc.blocks l = some k ∧ k ≠ 0

section prep
variable {vc : VCode} (hp : PrepIn vc)
include hp

theorem PrepIn.cfg0 : ∃ ss ps, vc.cfg = .ok (ss, ps) :=
  cfg_of fun i vb h => by
    obtain ⟨t, h1, h2, h3⟩ := hp.term i vb h
    exact ⟨t, h1, h2, fun l hl => let ⟨k, hk, _⟩ := h3 l hl; ⟨k, hk⟩⟩

/-- The kept blocks have a CFG: the targets of a reachable block are reachable. -/
theorem PrepIn.cfg1 {ss0 : Array (Array Nat)} (cs0 : CfgSpec vc.blocks ss0) :
    ∃ ss ps, ({ vc with blocks := keep vc.blocks (reachable ss0) } : VCode).cfg = .ok (ss, ps) := by
  have hs0 : ss0.size ≠ 0 := by rw [cs0.size]; have := hp.dom.nonempty; omega
  have hR := reachable_spec (succsIn_of cs0) hs0
  apply cfg_of
  intro i vb hvb
  change (keep vc.blocks (reachable ss0))[i]? = some vb at hvb
  have hi : i < (keep vc.blocks (reachable ss0)).size := (Array.getElem?_eq_some_iff.mp hvb).1
  obtain ⟨b, hb, e, hlive⟩ := keep_src hi
  have hvbe : vb = vc.blocks[b] := by
    rw [← e]; exact (Option.some.inj (by rw [← hvb, Array.getElem?_eq_getElem hi])).symm
  subst hvbe
  obtain ⟨t, h1, h2, h3⟩ := hp.term b vc.blocks[b] (Array.getElem?_eq_getElem hb)
  refine ⟨t, h1, h2, fun l hl => ?_⟩
  obtain ⟨k, hk, -⟩ := h3 l hl
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hl
  have hmk := hR.2.2.1 b hlive k (succ_mem cs0 hb h1 hj hk)
  obtain ⟨hkV, hlab⟩ := lab_some hk
  obtain ⟨k', hk', e'⟩ := keep_dst hkV hmk
  exact ⟨k', lab_of (keep_lbls hp.dom.labels _) hk' (by rw [e', hlab])⟩

/-- No kept block branches to the entry. -/
theorem PrepIn.preds0 {ss0 ss1 ps1 : Array (Array Nat)} (cs0 : CfgSpec vc.blocks ss0)
    (hc1 : ({ vc with blocks := keep vc.blocks (reachable ss0) } : VCode).cfg = .ok (ss1, ps1)) :
    ps1[0]? = some #[] := by
  have hs0 : ss0.size ≠ 0 := by rw [cs0.size]; have := hp.dom.nonempty; omega
  have hl0 := (reachable_spec (succsIn_of cs0) hs0).2.1
  obtain ⟨h10, hk0⟩ := keep_zero hp.dom.nonempty hl0
  have cs1 := cfg_spec hc1
  refine preds_nil hc1 h10 fun q sq j hq hj => ?_
  have hqV : q < (keep vc.blocks (reachable ss0)).size := by
    have := (Array.getElem?_eq_some_iff.mp hq).1; rw [cs1.size] at this; exact this
  obtain ⟨t, ts, ht, -, hts, htsz, hl⟩ := cs1.blk q _ (Array.getElem?_eq_getElem hqV)
  rw [hq] at hts; cases hts
  have hjl : j < t.targets.length := by rw [← htsz]; exact (Array.getElem?_eq_some_iff.mp hj).1
  obtain ⟨k, hk, hlab⟩ := hl j t.targets[j] (List.getElem?_eq_getElem hjl)
  rw [hj] at hk; cases hk
  obtain ⟨_, hlab0⟩ := lab_some hlab
  obtain ⟨b, hb, e, -⟩ := keep_src hqV
  obtain ⟨t', h1, -, h3⟩ := hp.term b vc.blocks[b] (Array.getElem?_eq_getElem hb)
  rw [e, h1] at ht; cases ht
  obtain ⟨k0, hk0', hne⟩ := h3 _ (List.getElem_mem hjl)
  rw [lab_zero hp.dom.nonempty (by rw [← hk0]; exact hlab0)] at hk0'
  cases hk0'
  exact hne rfl

end prep

/-! ## The splitting loop -/

/-- Every edge block jumps to a label satisfying `Q`. -/
def EdgeT (Q : Label → Prop) (E : Array VBlock) : Prop :=
  ∀ e ∈ E.toList, ∃ l, e.insts = #[.jump l] ∧ Q l

theorem innerFoldT (ps : Array (Array Nat)) (Q : Label → Prop) : ∀ (xs : List (Nat × Label))
    (next : Nat) (E : Array VBlock) (ls : Array Label), (∀ x ∈ xs, Q x.2) → EdgeT Q E →
    EdgeT Q (xs.foldl (innerStep ps) (next, E, ls)).2.1
  | [], _, _, _, _, hE => hE
  | x :: xs, next, E, ls, hx, hE => by
    simp only [List.foldl_cons]
    have hx' : ∀ y ∈ xs, Q y.2 := fun y hy => hx y (List.mem_cons_of_mem _ hy)
    by_cases hc : (ps[x.1]! : Array Nat).size > 1
    · rw [show innerStep ps (next, E, ls) x =
          (next + 1, E.push { label := next, insts := #[.jump x.2] }, ls.push next) by
        simp only [innerStep, hc, ↓reduceIte]]
      refine innerFoldT ps Q xs _ _ _ hx' fun e he => ?_
      rw [Array.toList_push, List.mem_append, List.mem_singleton] at he
      rcases he with he | rfl
      · exact hE e he
      · exact ⟨x.2, rfl, hx x List.mem_cons_self⟩
    · rw [show innerStep ps (next, E, ls) x = (next, E, ls.push x.2) by
        simp only [innerStep, hc, ↓reduceIte]]
      exact innerFoldT ps Q xs _ _ _ hx' hE

/-- The labels of `V`. -/
abbrev InV (V : Array VBlock) (l : Label) : Prop := ∃ k, lab V l = some k

/-- The loop body's two outcomes `prepare` takes. -/
structure BodyOk (ss ps : Array (Array Nat))
    (F : VBlock × Nat → Nat × Array VBlock × Array VBlock →
      Except String (ForInStep (Nat × Array VBlock × Array VBlock))) : Prop where
  keep : ∀ vb i s, (ss[i]! : Array Nat).size < 2 →
    F (vb, i) s = .ok (.yield (s.1, s.2.1.push vb, s.2.2))
  split : ∀ vb i s t t', ¬ (ss[i]! : Array Nat).size < 2 → vb.insts.back? = some t →
    t.setTargets ((((ss[i]! : Array Nat).zip t.targets.toArray).toList.foldl (innerStep ps)
      (s.1, s.2.2, #[])).2.2.toList) = some t' →
    F (vb, i) s = .ok (.yield
      ((((ss[i]! : Array Nat).zip t.targets.toArray).toList.foldl (innerStep ps) (s.1, s.2.2, #[])).1,
        s.2.1.push { vb with insts := vb.insts.pop.push t' },
        (((ss[i]! : Array Nat).zip t.targets.toArray).toList.foldl (innerStep ps) (s.1, s.2.2, #[])).2.1))

/-- **The critical-edge-splitting loop never throws** and establishes `SInv` and `EdgeT`. -/
theorem split_loop {V : Array VBlock} {ss ps : Array (Array Nat)} (cs : CfgSpec V ss)
    {F : VBlock × Nat → Nat × Array VBlock × Array VBlock →
      Except String (ForInStep (Nat × Array VBlock × Array VBlock))} (hF : BodyOk ss ps F) :
    ∃ r, forIn V.zipIdx (next0Of V, #[], #[]) F = .ok r ∧ SInv V (next0Of V) V.size r ∧
      EdgeT (InV V) r.2.2 := by
  rw [← Array.forIn_toList]
  have := forIn_ok_inv F V.zipIdx.toList
    (fun k st => SInv V (next0Of V) k st ∧ EdgeT (InV V) st.2.2) ?_ (next0Of V, #[], #[]) ?_
  · rw [Array.length_toList, Array.size_zipIdx] at this; exact this
  · intro k x b hx ⟨hb, hbE⟩
    rw [Array.toList_zipIdx, List.getElem?_zipIdx] at hx
    obtain ⟨vb, hvb, rfl⟩ : ∃ vb, V.toList[k]? = some vb ∧ x = (vb, 0 + k) := by
      cases e : V.toList[k]? with
      | none => rw [e] at hx; cases hx
      | some vb => rw [e] at hx; simp only [Option.map_some, Option.some.injEq] at hx
                   exact ⟨vb, rfl, hx.symm⟩
    simp only [Nat.zero_add]
    obtain ⟨hk, hvb'⟩ := List.getElem?_eq_some_iff.mp hvb
    rw [Array.length_toList] at hk
    have hvbk : V[k] = vb := by rw [← hvb', Array.getElem_toList]
    by_cases hsz : (ss[k]! : Array Nat).size < 2
    · -- no splitting
      refine ⟨_, hF.keep vb k b hsz, ⟨hb.next, hb.edges, by simp [hb.size], fun j h1 h2 => ?_⟩, hbE⟩
      simp only [Array.size_push] at h2
      by_cases hj : j < b.2.1.size
      · simp only [Array.getElem_push, hj, dite_true]
        exact hb.rw j h1 hj
      · have : j = k := by have := hb.size; omega
        subst this
        simp only [Array.getElem_push, hj, dite_false]
        exact .inl hvbk.symm
    · -- the successors of the block
      obtain ⟨t, ts, ht, -, hts, htsz, hl⟩ := cs.blk k vb (by rw [← Array.getElem?_toList]; exact hvb)
      have hts' : (ss[k]! : Array Nat) = ts := by simp only [getElem!_def, hts]
      have h2 : 2 ≤ t.targets.length := by rw [hts'] at hsz; omega
      obtain ⟨r1', r2', r3', r4', -, r6'⟩ := innerFold ps (next0Of V)
        ((ss[k]! : Array Nat).zip t.targets.toArray).toList b.1 b.2.2 #[] hb.next hb.edges
      obtain ⟨t', ht'⟩ := setTargets_some (i := t)
        (ls := (List.foldl (innerStep ps) (b.1, b.2.2, #[])
          ((ss[k]! : Array Nat).zip t.targets.toArray).toList).2.2.toList)
        (by intro h; rw [h] at h2; simp at h2)
        (by rw [Array.length_toList, r4']; simp [hts', htsz])
      refine ⟨_, hF.split vb k b t t' hsz ht ht', ⟨r1', r2', by simp [hb.size], fun j h1 h2' => ?_⟩, ?_⟩
      · simp only [Array.size_push] at h2'
        by_cases hj : j < b.2.1.size
        · simp only [Array.getElem_push, hj, dite_true]
          exact rwOk_ext r3' (hb.rw j h1 hj)
        · have : j = k := by have := hb.size; omega
          subst this
          simp only [Array.getElem_push, hj, dite_false]
          rw [hvbk]
          refine .inr ⟨t, t', _, ht, h2, ht', rfl, fun m l' hm => ?_⟩
          rw [Array.getElem?_toList] at hm
          have hmlt := (Array.getElem?_eq_some_iff.mp hm).1
          rw [r4'] at hmlt
          simp only [Array.size_empty, Nat.zero_add] at hmlt
          obtain ⟨y, hy⟩ : ∃ y, (((ss[j]! : Array Nat).zip t.targets.toArray).toList)[m]? = some y :=
            ⟨_, List.getElem?_eq_getElem hmlt⟩
          obtain ⟨l'', hl1, hl2⟩ := r6' m y hy
          simp only [Array.size_empty, Nat.zero_add] at hl1
          rw [hm] at hl1
          cases hl1
          have hty : t.targets[m]? = some y.2 := by
            rw [Array.toList_zip] at hy
            have := (List.getElem?_zip_eq_some.mp hy).2
            simpa using this
          rcases hl2 with e | ⟨e, he⟩
          · exact .inl (by rw [hty, e])
          · exact .inr ⟨e, y.2, he, hty⟩
      · refine innerFoldT ps (InV V) _ b.1 b.2.2 #[] (fun y hy => ?_) hbE
        rw [Array.toList_zip] at hy
        have hy2 := (List.of_mem_zip hy).2
        simp only at hy2
        obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hy2
        obtain ⟨k', -, hk'⟩ := hl j _ hj
        exact ⟨k', hk'⟩
  · refine ⟨⟨?_, fun e he => by simp at he, rfl, fun j _ h => by simp at h⟩, fun e he => by simp at he⟩
    simp only [Array.size_empty, Nat.zero_add]

/-- **The split blocks have a CFG.** -/
theorem cfg2_ok {V B E : Array VBlock} {next : Nat} {ss : Array (Array Nat)} (cs : CfgSpec V ss)
    (hn : Lbls V) (hS : SInv V (next0Of V) V.size (next, B, E)) (hE : EdgeT (InV V) E) (vc : VCode) :
    ∃ ss2 ps2, ({ vc with blocks := B ++ E } : VCode).cfg = .ok (ss2, ps2) := by
  have hn2 := lbls2 hS hn
  -- a kept label is a label of the split blocks
  have labB : ∀ l, InV V l → ∃ k, lab (B ++ E) l = some k := by
    intro l ⟨k, hk⟩
    obtain ⟨hkV, hlk⟩ := lab_some hk
    obtain ⟨hkB, e⟩ := v2_B hS hkV
    have hk2 : k < (B ++ E).size := (Array.getElem?_eq_some_iff.mp e).1
    refine ⟨k, lab_of hn2 hk2 ?_⟩
    have : (B ++ E)[k] = B[k] := Option.some.inj (by rw [← Array.getElem?_eq_getElem hk2, e])
    rw [this, ← hlk]
    exact (rw_fields (hS.rw k hkV hkB)).1
  apply cfg_of
  intro i vb hvb
  change (B ++ E)[i]? = some vb at hvb
  rcases Nat.lt_or_ge i V.size with hi | hi
  · obtain ⟨hkB, e⟩ := v2_B hS hi
    rw [e] at hvb; cases hvb
    obtain ⟨_, t, t', ht, ht', -, -, -, -, -, hor, -, hrel⟩ := blk2 hS cs hi
    obtain ⟨t0, ts, ht0, hterm, -, -, hl⟩ := cs.blk i V[i] (Array.getElem?_eq_getElem hi)
    rw [ht] at ht0; cases ht0
    refine ⟨t', ht', ?_, fun l' hl' => ?_⟩
    · rcases hor with rfl | h
      · exact hterm
      · exact setTargets_term h
    · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hl'
      obtain ⟨l, hl0, hcase⟩ := hrel j l' hj
      rcases hcase with rfl | ⟨-, e, he⟩
      · obtain ⟨k, -, hk⟩ := hl j l' hl0
        exact labB l' ⟨k, hk⟩
      · have he2 : (B ++ E)[V.size + e]? = some { label := l', insts := #[.jump l] } := by
          rw [v2_E hS, he]
        have hu : V.size + e < (B ++ E).size := (Array.getElem?_eq_some_iff.mp he2).1
        exact ⟨_, lab_of hn2 hu (by
          rw [Option.some.inj (by rw [← Array.getElem?_eq_getElem hu, he2] :
            some (B ++ E)[V.size + e] = some { label := l', insts := #[.jump l] })])⟩
  · obtain ⟨e, rfl⟩ : ∃ e, i = V.size + e := ⟨i - V.size, by omega⟩
    rw [v2_E hS] at hvb
    obtain ⟨l, hins, hQ⟩ := hE vb (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hvb))
    refine ⟨.jump l, by rw [hins]; rfl, rfl, fun l' hl' => ?_⟩
    simp only [MInst.targets, List.mem_singleton] at hl'
    subst hl'
    exact labB _ hQ

theorem split_loop_ne {V : Array VBlock} {ss ps : Array (Array Nat)} (cs : CfgSpec V ss)
    {F : VBlock × Nat → Nat × Array VBlock × Array VBlock →
      Except String (ForInStep (Nat × Array VBlock × Array VBlock))} (hF : BodyOk ss ps F)
    (e : String) : forIn V.zipIdx (next0Of V, #[], #[]) F ≠ .error e := by
  obtain ⟨r, hr, -⟩ := split_loop cs hF
  rw [hr]; intro h; cases h

theorem split_loop_ok {V : Array VBlock} {ss ps : Array (Array Nat)} (cs : CfgSpec V ss)
    {F : VBlock × Nat → Nat × Array VBlock × Array VBlock →
      Except String (ForInStep (Nat × Array VBlock × Array VBlock))} (hF : BodyOk ss ps F)
    {st : Nat × Array VBlock × Array VBlock} (h : forIn V.zipIdx (next0Of V, #[], #[]) F = .ok st) :
    SInv V (next0Of V) V.size st ∧ EdgeT (InV V) st.2.2 := by
  obtain ⟨r, hr, h1, h2⟩ := split_loop cs hF
  rw [hr] at h; cases h
  exact ⟨h1, h2⟩

/-! ## `prepare` succeeds -/

/-- **`prepare` succeeds on `PrepIn` input.** -/
theorem prepare_ok_of {vc : VCode} (hp : PrepIn vc) : ∃ vcp, prepare vc = .ok vcp := by
  obtain ⟨ss0, ps0, hc0'⟩ := hp.cfg0
  have cs0 := cfg_spec hc0'
  obtain ⟨ss1, ps1, hc1'⟩ := hp.cfg1 cs0
  have cs1 := cfg_spec hc1'
  have hpre := hp.preds0 cs0 hc1'
  have hv0 : 0 < vc.blocks.size := hp.dom.nonempty
  have hs0 : ss0.size ≠ 0 := by rw [cs0.size]; omega
  obtain ⟨h10, hk0⟩ := keep_zero hp.dom.nonempty (reachable_spec (succsIn_of cs0) hs0).2.1
  have hn1 := keep_lbls hp.dom.labels (reachable ss0)
  unfold prepare
  simp only [bind, Except.bind]
  split
  · rename_i e he; have := he.symm.trans hc0'; cases this
  rename_i r0 hc0
  obtain rfl : r0 = (ss0, ps0) := Except.ok.inj (hc0.symm.trans hc0')
  split
  · rename_i e he; have := he.symm.trans hc1'; cases this
  rename_i r1 hc1
  obtain rfl : r1 = (ss1, ps1) := Except.ok.inj (hc1.symm.trans hc1')
  split
  · rename_i h; simp [hpre] at h
  split
  · rename_i h
    exfalso
    have e0 : (keep vc.blocks (reachable ss0))[0]? = some vc.blocks[0] := by
      rw [Array.getElem?_eq_getElem h10, hk0]
    have := hp.entry vc.blocks[0] (Array.getElem?_eq_getElem hp.dom.nonempty)
    change (!(Option.map (fun b : VBlock => b.params.isEmpty)
      (keep vc.blocks (reachable ss0))[0]?).getD true) = true at h
    rw [e0] at h
    simp [this] at h
  split
  · rename_i e he
    exact absurd he (split_loop_ne cs1 (ps := ps1) ⟨by
      intro vb i s h; simp only [h, ↓reduceIte]; rfl, by
      intro vb i s t t' h ht hst
      simp only [h, ↓reduceIte, ht]
      rw [← Array.forIn_toList, forIn_yield_foldl _ _ (innerStep ps1) _
        (fun a c => by simp only [innerStep]; split <;> rfl)]
      simp only [pure, Except.pure, hst]⟩ e)
  rename_i st hfor
  obtain ⟨hS, hE⟩ := split_loop_ok cs1 (ps := ps1) ⟨by
    intro vb i s h; simp only [h, ↓reduceIte]; rfl, by
    intro vb i s t t' h ht hst
    simp only [h, ↓reduceIte, ht]
    rw [← Array.forIn_toList, forIn_yield_foldl _ _ (innerStep ps1) _
      (fun a c => by simp only [innerStep]; split <;> rfl)]
    simp only [pure, Except.pure, hst]⟩ hfor
  obtain ⟨next, B, E⟩ := st
  obtain ⟨ss2, ps2, hc2⟩ := cfg2_ok cs1 hn1 hS hE vc
  split
  · rename_i e he; have := he.symm.trans hc2; cases this
  exact ⟨_, rfl⟩

/-! ## `lowerFunction`'s VCode -/

section low
variable {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState} {bl : List BLow}
  {RR : Reg → Reg} (H : Low f vc ctx st0 bl RR)
include H

/-- **CLIF block `x`'s code ends in a terminator**: a `jump`, a branch with at least one target,
`rets`/`udf` for a `return`/`trap` (`termShapeR_runTerm`), the `tryCall` of a `try_call`. -/
theorem raw_term (hs : LowerScope f) (hbt : ∀ B ∈ f.blocks, BrIdxTyped ctx B.term) {x : Nat}
    {B : Clif.Block} {L : BLow} (hB : f.blocks[x]? = some B) (hL : bl[x]? = some L) :
    ∃ t, (fixBlock RR (rawBlock f bl x B)).insts.back? = some t ∧ t.isTerminator = true := by
  obtain ⟨t, hb', hjump, hnt, htry⟩ := H.raw_back hs hbt hB hL
  obtain ⟨-, -, hem, nl0, nl1, hlt⟩ := (lowBlocks_spec H.hbl).2 x B L hB hL
  rcases try_or B.term with ht | ⟨et, het⟩
  · obtain ⟨ranges, hb⟩ := H.hb
    have sp := ctxSpec_of hb
    have hctx : CtxInv f ctx := ctxOk_sound (ctxOk_complete hs hb)
    have hst : L.start = blockStart f x := (lowBlocks_start H.hbl).2 x L hL
    have hph := sp.facts.term x B hB
    rw [← hst] at hph
    obtain ⟨htl, hd, out, tr, hrun⟩ := (lowTerm_spec hlt).1 ht
    obtain ⟨hctx', hi'⟩ := termCtx_facts hctx hph L.data
    have hval : ValsBelow ctx L.tst := by
      intro y r hy
      have h1 : y < ctx.valReg.size := by
        simp only [Ctx.valueReg?] at hy
        cases hh : ctx.valReg[y]? with
        | none => rw [hh] at hy; cases hy
        | some _ => exact (Array.getElem?_eq_some_iff.mp hh).1
      have h2 := sp.facts.size
      obtain ⟨stE, nlE, hr⟩ := H.low
      have h3 := lowB_mono _ _ _ _ _ _ _ hr x L hL
      omega
    have hvb' : ValsBelow (termCtx ctx (L.start + B.body.length) L.data) L.tst := hval
    have hfix : fixTry L.tl L.tst'.emitted.toList = L.tst'.emitted.toList := by rw [htl]; rfl
    have last : ∀ (ms : List MInst) (i : MInst), L.tst'.emitted = L.tst.emitted ++ (ms ++ [i]).toArray →
        (fixBlock RR (rawBlock f bl x B)).insts.back? = some (i.mapRegs RR) := by
      intro ms i he
      apply raw_back_of hL
      rw [hfix, he, hem]
      simp
    -- a branch has as many targets as successors
    have hlen : (∀ bc, B.term ≠ .jump bc) → L.targets.length = (dests B.term).length := by
      intro hj'
      have htg := lowTerm_targets ht hlt
      rw [shape_targetsOf_other hj'] at htg
      exact (edgeTargets_spec htg).1
    unfold termCallF termCall at hrun
    cases hT : B.term with
    | jump bc =>
      obtain ⟨tl, rfl, -⟩ := hjump bc hT
      exact ⟨_, hb', rfl⟩
    | brif c tb eb =>
      refine ⟨t, hb', isTerminator_of_targets ?_⟩
      rw [(hnt ht).1]
      intro h0
      have := hlen (fun bc e => by rw [hT] at e; cases e)
      rw [h0, hT] at this
      simp [dests] at this
    | brTable y d tbl =>
      refine ⟨t, hb', isTerminator_of_targets ?_⟩
      rw [(hnt ht).1]
      intro h0
      have := hlen (fun bc e => by rw [hT] at e; cases e)
      rw [h0, hT] at this
      simp [dests] at this
    | ret xs =>
      rw [hT] at hrun hd
      obtain ⟨ms, i, he, hit⟩ := termShapeR_runTerm (t := .ret (xs ++ sretRet f)) hctx' rfl hd hi'
        hvb' hrun
      exact ⟨_, last _ _ he, by rw [isTerminator_mapRegs]; exact hit⟩
    | trap c =>
      rw [hT] at hrun hd
      obtain ⟨ms, i, he, hit⟩ := termShapeR_runTerm (t := .trap c) hctx' rfl hd hi' hvb' hrun
      exact ⟨_, last _ _ he, by rw [isTerminator_mapRegs]; exact hit⟩
    | returnCall fn args =>
      rw [hT] at hd
      simp [abiTerm, termData, throw, throwThe, MonadExceptOf.throw] at hd
    | tryCall => rw [hT] at ht; cases ht
    | tryCallIndirect => rw [hT] at ht; cases ht
  · obtain ⟨c, ti, rfl, -⟩ := htry et het
    exact ⟨_, hb', rfl⟩

end low

/-- **`lowerFunction`'s VCode meets `PrepIn`** on `Dominated`, `LowerScope` input: labels are
block indices; a CLIF block's code ends in a terminator whose targets are CLIF blocks other than
the entry (`LowerScope.noEntryPred`) or its edge blocks (labelled from the number of CLIF
blocks on); an edge block is a `jump` to a CLIF block other than the entry. -/
theorem prepIn_of_lower {f : Clif.Function} {vc : VCode} (hd : Dominated f) (hs : LowerScope f)
    (h : lowerFunction f = .ok vc) : PrepIn vc := by
  obtain ⟨ctx, st0, bl, RR, H⟩ := low_of hs.subsetE h
  have hbt : ∀ B ∈ f.blocks, BrIdxTyped ctx B.term := by
    obtain ⟨ctx', st0', R', gn', bl', A', hshape, -, hbt'⟩ :=
      lowering_of_check (lowerCheck_complete hd hs h)
    obtain ⟨ranges', hb'⟩ := hshape.hctx
    obtain ⟨ranges, hb⟩ := H.hb
    rw [hb] at hb'
    cases hb'
    exact hbt'
  have hn : 0 < f.blocks.length := List.length_pos_iff.mpr hs.nonempty
  obtain ⟨B0, hB0⟩ : ∃ B0, f.blocks[0]? = some B0 := ⟨_, List.getElem?_eq_getElem hn⟩
  have dom := Driver.prepDomain_of hs h
  -- a block's label is its index
  have tgt : ∀ (l : Nat) (vb : VBlock), vc.blocks[l]? = some vb → l ≠ 0 →
      ∃ k, lab vc.blocks l = some k ∧ k ≠ 0 := by
    intro l vb hvb h0
    obtain ⟨hl, e⟩ := Array.getElem?_eq_some_iff.mp hvb
    refine ⟨l, lab_of dom.labels hl ?_, h0⟩
    rw [e]
    rcases H.cases hvb with ⟨B, L, -, -, -, rfl⟩ | ⟨bi, B, L, e', -, -, -, hel, -, rfl⟩
    · rfl
    · exact hel
  refine ⟨dom, fun vb hvb => ?_, fun b vb hvb => ?_⟩
  · rw [H.raw_at hB0] at hvb
    cases hvb
    rfl
  rcases H.cases hvb with ⟨B, L, -, hB, hL, rfl⟩ | ⟨bi, B, L, e, hB, hL, he, -, -, rfl⟩
  · obtain ⟨t, hb', -, hnt, htry⟩ := H.raw_back hs hbt hB hL
    obtain ⟨t2, hb2, hterm⟩ := raw_term H hs hbt hB hL
    rw [hb'] at hb2
    cases hb2
    refine ⟨t, hb', hterm, fun l hl => ?_⟩
    have hBm := List.mem_of_getElem? hB
    -- an edge block of `B`: labelled from the number of CLIF blocks on
    have viaE : ∀ e ∈ edgeBlocks f B L, e.label = l → ∃ k, lab vc.blocks l = some k ∧ k ≠ 0 := by
      intro e he hel
      obtain ⟨hge, hat⟩ := H.edge_at hB hL he
      rw [hel] at hge hat
      exact tgt l _ hat (by omega)
    rcases try_or B.term with ht | ⟨et, het⟩
    · rw [(hnt ht).1] at hl
      rcases (H.raw_tgt hB hL).1 ht l hl with ⟨bc, hbc, hidx, -⟩ | ⟨e, he, hel⟩
      · obtain ⟨TB, -, hTBi⟩ := block?_of_idx hidx
        exact tgt l _ (H.raw_at hTBi) fun h0 => hs.noEntryPred B hBm bc.block
          (by rw [succIds_of ht]; exact List.mem_map_of_mem hbc) (h0 ▸ hidx)
      · exact viaE e he hel
    · obtain ⟨c, ti, rfl, htg⟩ := htry et het
      rw [htg] at hl
      obtain ⟨e, he, hel⟩ := ((H.raw_tgt hB hL).2 et het).2 l hl
      exact viaE e he hel
  · obtain ⟨tl, TB, hins, -, hTB, htl0, -⟩ := H.edge_facts hs hB hL he
    refine ⟨.jump tl, by simp [fixBlock, hins]; rfl, rfl, fun l hl => ?_⟩
    simp only [MInst.targets, List.mem_singleton] at hl
    subst hl
    exact tgt _ _ (H.raw_at hTB) htl0

/-! ## The input conditions -/

/-- **`prepare` never fails on `lowerFunction`'s output** for input in scope (`dominatedB`,
`lowerScopeB`, both conditions of `fnScopeB`). -/
theorem prepare_ok {f : Clif.Function} {vc : VCode} (hd : dominatedB f = true)
    (hs : lowerScopeB f = true) (hl : lowerFunction f = .ok vc) : ∃ vcp, prepare vc = .ok vcp :=
  prepare_ok_of (prepIn_of_lower (dominated_of hd) (lowerScope_of hs) hl)

/-- `prepare_ok`, with the CFG of `prepare`'s output (`cfg3`). -/
theorem prepare_ok_cfg {f : Clif.Function} {vc : VCode} (hd : dominatedB f = true)
    (hs : lowerScopeB f = true) (hl : lowerFunction f = .ok vc) :
    ∃ vcp, prepare vc = .ok vcp ∧ ∃ ss ps, vcp.cfg = .ok (ss, ps) := by
  obtain ⟨vcp, h⟩ := prepare_ok hd hs hl
  refine ⟨vcp, h, ?_⟩
  obtain ⟨ss0, ps0, ss1, ps1, ss2, ps2, next, B, E, hc0, -, hS, hc2, rfl⟩ := prepare_facts h
  exact cfg3 (Driver.prepDomain_of (lowerScope_of hs) hl) (cfg_spec hc0) (cfg_spec hc2) hS

end Backend.Proof.Prep
