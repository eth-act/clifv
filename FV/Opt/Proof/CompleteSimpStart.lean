import FV.Opt.Proof.CompleteSimpFold

/-!
# Completeness of simplify: entering a block

`binv_start`: between two blocks (`RunBInv`), entering an unprocessed block `bi` whose dominators are
processed gives the invariant inside `bi` before its first statement (`RunXInv`). The view gains
block `bi` with its parameters and no statement; the parameters of `bi` become done, so they leave the
bad values (they are leaves: available in `bi`, without node or e-class, never renamed).
-/

namespace Opt

open Clif

section Start

variable {f : Function} {info : Info} {allowed skelOk : Inst → Bool} {st : SState} {S : Subst}
  {out : Array Block} {logs : Array (Option BlockLog)} {bi : Nat} {b0 : Block}

theorem V0_start (hn : logs[bi]? = some none) (hb0 : f.blocks[bi]? = some b0) (d : Nat) :
    V0 f logs bi d = if d = bi then some { b0 with body := [] } else V0 f logs f.blocks.length d := by
  have hnl : f.blocks[f.blocks.length]? = none := List.getElem?_eq_none (Nat.le_refl _)
  by_cases hd : d = bi
  · subst hd
    simp [V0, hn, hb0]
  · simp only [hd, ↓reduceIte]
    unfold V0
    split
    · rfl
    · simp only [hd, ↓reduceIte]
      split
      · rename_i he; subst he; rw [hnl]; rfl
      · rfl

theorem V0_end_bi (hn : logs[bi]? = some none) (hbi : bi < f.blocks.length) :
    V0 f logs f.blocks.length bi = none := by
  simp [V0, hn, Nat.ne_of_lt hbi]

theorem done_start (hc : Checked f info) (hn : logs[bi]? = some none) (y : ValueId) :
    Done f logs bi 0 y ↔ Done f logs f.blocks.length 0 y ∨ (defMap f).get? y = some (bi, 0) := by
  constructor
  · rintro ⟨d, t, hd, h | ⟨rfl, ht⟩⟩
    · exact .inl ⟨d, t, hd, .inl h⟩
    · obtain rfl : t = 0 := by omega
      exact .inr hd
  · rintro (⟨d, t, hd, h | ⟨rfl, -⟩⟩ | h)
    · exact ⟨d, t, hd, .inl h⟩
    · exact absurd (hc.def_lt hd) (Nat.lt_irrefl _)
    · exact ⟨bi, 0, h, .inr ⟨rfl, Nat.le_refl _⟩⟩

theorem param_site (hc : Checked f info) (hb0 : f.blocks[bi]? = some b0) {y : ValueId} :
    (defMap f).get? y = some (bi, 0) ↔ ∃ p ∈ b0.params, p.1 = y := by
  constructor
  · intro h
    obtain ⟨i, b, hb, ⟨p, hp, rfl, he⟩ | ⟨j, s, -, -, he⟩⟩ := mem_defSites.1 (hc.wf.sitesRev y _ h)
    · simp only [Prod.mk.injEq] at he; obtain ⟨rfl, -⟩ := he
      rw [hb0] at hb; cases hb
      exact ⟨p, hp, rfl⟩
    · simp at he
  · rintro ⟨p, hp, rfl⟩
    exact hc.site_param hb0 hp

/-- **Entering block `bi`** (module doc). -/
theorem binv_start (hc : Checked f info) (h : RunBInv f info allowed skelOk st S out logs)
    (hbi : bi < f.blocks.length) (hn : logs[bi]? = some none)
    (hpreds : ∀ d, d ≠ bi → Anc info.cfg.idom d bi → ∃ lg, logs[d]? = some (some lg)) :
    RunXInv f info allowed skelOk logs bi 0 [] st S := by
  obtain ⟨b0, hb0⟩ : ∃ b0, f.blocks[bi]? = some b0 := ⟨_, List.getElem?_eq_getElem hbi⟩
  -- the views
  have hV1 : CurV f logs f.blocks.length [] = V0 f logs f.blocks.length := CurV_end _ _ _
  have hV2 : CurV f logs bi [] = fun d =>
      if d = bi then some { b0 with body := [] } else V0 f logs f.blocks.length d := by
    rw [CurV_end]; funext d; exact V0_start hn hb0 d
  have hV1bi := V0_end_bi (f := f) hn hbi
  -- the bad values
  have hB21 : ∀ y, Bad f logs bi 0 S y → Bad f logs f.blocks.length 0 S y := by
    rintro y (⟨hy, hnd⟩ | hy)
    · exact .inl ⟨hy, fun hd => hnd ((done_start hc hn y).2 (.inl hd))⟩
    · exact .inr hy
  -- the parameters of `bi`
  have hpAv : ∀ y, (∃ p ∈ b0.params, p.1 = y) → st.avail.get? y = some bi := fun y hy =>
    h.leafAv y bi ((initAvail_get hc.unique y bi).2 (mem_leafList.2 ⟨b0, hb0, .inl hy⟩))
  have hpL : ∀ y, (∃ p ∈ b0.params, p.1 = y) → (initAvail f).contains y = true := fun y hy =>
    (hm_contains_iff _ _).2 (by
      rw [(initAvail_get hc.unique y bi).2 (mem_leafList.2 ⟨b0, hb0, .inl hy⟩)]; rfl)
  have hpS : ∀ y, (∃ p ∈ b0.params, p.1 = y) → S.contains y = false := by
    intro y hy
    cases hk : S.contains y with
    | false => rfl
    | true =>
      obtain ⟨d, k, hdk⟩ := h.keysRes y hk
      rw [(param_site hc hb0).2 hy] at hdk; simp at hdk
  have hpB1 : ∀ y, (∃ p ∈ b0.params, p.1 = y) → Bad f logs f.blocks.length 0 S y := by
    intro y hy
    have hs := (param_site hc hb0).2 hy
    refine .inl ⟨hc.def_le hs, ?_⟩
    rintro ⟨d, t, hd, ⟨lg, hlg⟩ | ⟨rfl, -⟩⟩
    · rw [hs] at hd; cases hd; rw [hn] at hlg; cases hlg
    · rw [hs] at hd; cases hd; exact Nat.lt_irrefl _ hbi
  have hpB2 : ∀ y, (∃ p ∈ b0.params, p.1 = y) → ¬ Bad f logs bi 0 S y := by
    intro y hy hb
    rcases hb with ⟨-, hnd⟩ | hk
    · exact hnd ((done_start hc hn y).2 (.inr ((param_site hc hb0).2 hy)))
    · rw [hpS y hy] at hk; cases hk
  have hB12 : ∀ y, Bad f logs f.blocks.length 0 S y → ¬ Bad f logs bi 0 S y →
      ∃ p ∈ b0.params, p.1 = y := by
    rintro y (⟨hy, hnd⟩ | hk) hb2
    · refine (param_site hc hb0).1 ?_
      have hd : Done f logs bi 0 y := Classical.byContradiction fun hnd' => hb2 (.inl ⟨hy, hnd'⟩)
      rcases (done_start hc hn y).1 hd with hd | hd
      · exact absurd hd hnd
      · exact hd
    · exact absurd (.inr hk) hb2
  have hPl : ∀ y, Placed st (Bad f logs f.blocks.length 0 S) y → Placed st (Bad f logs bi 0 S) y :=
    fun y hy z hz => ⟨fun hb => (hy z hz).1 (hB21 z hb), (hy z hz).2⟩
  have hpPl : ∀ y, (∃ p ∈ b0.params, p.1 = y) → Placed st (Bad f logs bi 0 S) y := by
    intro y hy
    refine Placed.mk (hpB2 y hy) (known_iff.2 (.inr ((hm_contains_iff _ _).2 (by rw [hpAv y hy]; rfl))))
      (fun n hn' => ?_) (fun ms hms => ?_)
    · rw [h.defsLeaf y (hpL y hy)] at hn'; cases hn'
    · exact absurd (hpB1 y hy) (h.altsNB y ms hms)
  -- definitions in the new view
  have hDef : ∀ {x d t}, DefAt (CurV f logs bi []) x d t ↔
      DefAt (CurV f logs f.blocks.length []) x d t ∨ (d = bi ∧ t = 0 ∧ ∃ p ∈ b0.params, p.1 = x) := by
    intro x d t
    rw [hV1, hV2]
    constructor
    · rintro ⟨b, hb, hx⟩
      by_cases hd : d = bi
      · subst hd
        simp only [↓reduceIte, Option.some.injEq] at hb
        subst hb
        rcases hx with ⟨rfl, p, hp, rfl⟩ | ⟨j, s, -, hs, -⟩
        · exact .inr ⟨rfl, rfl, p, hp, rfl⟩
        · simp at hs
      · simp only [hd, ↓reduceIte] at hb
        exact .inl ⟨b, hb, hx⟩
    · rintro (⟨b, hb, hx⟩ | ⟨rfl, rfl, hp⟩)
      · have hd : d ≠ bi := by rintro rfl; rw [hV1bi] at hb; cases hb
        exact ⟨b, by simp only [hd, ↓reduceIte]; exact hb, hx⟩
      · exact ⟨({ b0 with body := [] } : Block), by simp, .inl ⟨rfl, hp⟩⟩
  have hext : VExt (CurV f logs f.blocks.length []) (CurV f logs bi []) := by
    intro d b hb
    have hd : d ≠ bi := by rintro rfl; rw [hV1, hV1bi] at hb; cases hb
    refine ⟨b, ?_, rfl, rfl, [], by simp⟩
    rw [hV2]; simp only [hd, ↓reduceIte]; rw [← hV1]; exact hb
  have hP : Prog (CurV f logs f.blocks.length []) (CurV f logs bi []) (Bad f logs f.blocks.length 0 S)
      (Bad f logs bi 0 S) st st S S :=
    ⟨hext, hPl, hB21, fun _ _ h => h, fun _ _ h _ => h, fun _ h _ => h, fun _ _ h => h,
     fun _ h => .inl h⟩
  have hkB : ∀ y, S.contains y = true → Bad f logs f.blocks.length 0 S y := fun _ hy => .inr hy
  have hm := h.rinv.m
  refine { rinv := ?_, srcTy := h.srcTy, leafAv := h.leafAv, availSrc := ?_, defsSrc := ?_,
           defsLeaf := h.defsLeaf, doneAv := ?_, substOk := ?_, outs := ?_, done := ?_,
           size := h.size, altsNB := ?_, keysRes := h.keysRes, availBig := h.availBig,
           ciDone := h.ciDone, defNB := ?_, cur := ?_, notbi := hn, preds := hpreds,
           ciCur := ?_ }
  · refine { m := ?_, noPartial := h.rinv.noPartial, memo := ?_, alts := h.rinv.alts }
    · refine { fn := hm.fn, maxLt := hm.maxLt, knownLt := hm.knownLt, typesFresh := hm.typesFresh,
               defsTy := hm.defsTy, altsKnown := hm.altsKnown, availDef := ?_, defAvail := ?_,
               newBig := ?_, badLe := fun x hx => hm.badLe x (hB21 x hx), uniq := ?_ }
      · intro x d hx hb
        by_cases hb1 : Bad f logs f.blocks.length 0 S x
        · have hp := hB12 x hb1 hb
          rw [hpAv x hp] at hx; cases hx
          obtain ⟨p, hp', rfl⟩ := hp
          exact ⟨0, hDef.2 (.inr ⟨rfl, rfl, p, hp', rfl⟩)⟩
        · obtain ⟨t, ht⟩ := hm.availDef x d hx hb1
          exact ⟨t, hDef.2 (.inl ht)⟩
      · intro x d t hx
        rcases hDef.1 hx with hx | ⟨rfl, -, hp⟩
        · exact hm.defAvail x d t hx
        · exact hpAv x hp
      · intro x n hx hav hb
        by_cases hb1 : Bad f logs f.blocks.length 0 S x
        · have hp := hB12 x hb1 hb
          have : st.avail.contains x = true := (hm_contains_iff _ _).2 (by rw [hpAv x hp]; rfl)
          rw [this] at hav; cases hav
        · exact hm.newBig x n hx hav hb1
      · intro x d t d' t' h1 h2
        rcases hDef.1 h1 with h1' | ⟨hd1, ht1, hp1⟩ <;> rcases hDef.1 h2 with h2' | ⟨hd2, ht2, hp2⟩
        · exact hm.uniq x d t d' t' h1' h2'
        · exfalso
          have := hm.defAvail x d t h1'
          rw [hpAv x hp2] at this
          have hdb : d = bi := (Option.some.inj this).symm
          rw [hV1] at h1'; obtain ⟨b, hb, -⟩ := h1'; rw [hdb, hV1bi] at hb; cases hb
        · exfalso
          have := hm.defAvail x d' t' h2'
          rw [hpAv x hp1] at this
          have hdb : d' = bi := (Option.some.inj this).symm
          rw [hV1] at h2'; obtain ⟨b, hb, -⟩ := h2'; rw [hdb, hV1bi] at hb; cases hb
        · exact ⟨hd1.trans hd2.symm, ht1.trans ht2.symm⟩
    · intro n w hw
      obtain ⟨e1, e2, e3⟩ := h.rinv.memo n w hw
      refine ⟨?_, e2, e3⟩
      rcases e1 with e | e
      · exact .inl (hPl w e)
      · exact .inr e
  · intro y d hy hle
    rcases h.availSrc y d hy hle with e | ⟨t, ht, hd⟩
    · exact .inl e
    · exact .inr ⟨t, ht, (done_start hc hn y).2 (.inl hd)⟩
  · intro y n hy hle
    exact (done_start hc hn y).2 (.inl (h.defsSrc y n hy hle))
  · intro y hd hk
    rcases (done_start hc hn y).1 hd with hd | hs
    · obtain ⟨e1, e2⟩ := h.doneAv y hd hk
      exact ⟨hPl y e1, e2⟩
    · have hp := (param_site hc hb0).1 hs
      exact ⟨hpPl y hp, bi, 0, hs, hpAv y hp⟩
  · intro y w hw
    obtain ⟨e1, e2, ⟨d', t', e3, e4⟩, e5⟩ := h.substOk y w hw
    exact ⟨(done_start hc hn y).2 (.inl e1), hPl w e2, ⟨d', t', hDef.2 (.inl e3), e4⟩, e5⟩
  · intro d b hb
    by_cases hd : d = bi
    · subst hd
      rw [hV2] at hb
      simp only [↓reduceIte, Option.some.injEq] at hb
      subst hb
      refine ⟨⟨b0, hb0, rfl, rfl⟩, fun k t ht => ?_⟩
      simp at ht
    · have hb' : CurV f logs f.blocks.length [] d = some b := by
        rw [hV2] at hb; simp only [hd, ↓reduceIte] at hb; rw [hV1]; exact hb
      obtain ⟨e1, e2⟩ := h.outs d b hb'
      exact ⟨e1, fun k t ht => (e2 k t ht).mono hP hm.defAvail ⟨b, hb', ht⟩⟩
  · intro d lg hlg
    obtain ⟨b1, bo, e1, e2, e3, e4, ⟨t1, t2, t3, t4, t5⟩⟩ := h.done d lg hlg
    exact ⟨b1, bo, e1, e2, e3.mono hP hkB _ _ _, e4.mono hP hkB,
      ⟨fun y hy => ⟨(t1 y hy).1.ext hext, hPl y (t1 y hy).2⟩, t2, t3, t4, t5⟩⟩
  · intro x ms hx hb
    exact h.altsNB x ms hx (hB21 x hb)
  · intro y d t hy
    rcases hDef.1 hy with hy | ⟨-, -, hp⟩
    · exact fun hb => h.defNB y d t hy (hB21 y hb)
    · exact hpB2 y hp
  · exact ⟨b0, hb0, Nat.zero_le _, by simp [StmtsFact]⟩
  · intro b hb
    intro i s lg hs _ _
    simp at hs

end Start

end Opt
