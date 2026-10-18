import FV.Opt.Proof.CompleteSimpInv

/-!
# Completeness of simplify: the run

Every statement keeps the invariant `Opt.RunXInv` (`step_gen`, instantiated by `step_pure` and
`step_skel`), the terminator of a block turns it into the invariant between blocks `Opt.RunBInv`
(`block_end`), which gives back `RunXInv` at the next block of the reverse postorder
(`block_start`); `stepBlock_inv` is one block, and `simplify_run_inv` the whole run.
-/

namespace Opt

open Clif

section Step

variable {f : Function} {info : Info} {allowed skelOk : Inst → Bool}
  {logs : Array (Option BlockLog)} {bi j : Nat} {lgs : List StmtLog} {st : SState} {S : Subst}

theorem typed_of_map {l1 l2 : List ValueId} {g h : ValueId → Option Ty}
    (he : l1.map g = l2.map h) (h2 : ∀ x ∈ l2, (h x).isSome) : ∀ y ∈ l1, ∃ u, g y = some u := by
  intro y hy
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hy
  have h1 : (l1.map g)[i]? = some (g y) := by rw [List.getElem?_map, hi]; rfl
  rw [he, List.getElem?_map] at h1
  cases hx : l2[i]? with
  | none => rw [hx] at h1; cases h1
  | some x =>
    rw [hx] at h1; simp only [Option.map_some, Option.some.injEq] at h1
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 (h2 x (List.mem_of_getElem? hx))
    exact ⟨u, by rw [← h1, hu]⟩

theorem Checked.termTyped (hc : Checked f info) {d : Nat} {b0 : Block} (hb : f.blocks[d]? = some b0)
    {y : ValueId} (hy : y ∈ termOperands b0.term) : ∃ t, info.types.get? y = some t := by
  obtain ⟨d', t', hd, -⟩ := hc.wf.termUses d b0 hb y hy
  exact Checked.typed (hc := hc) hd

theorem TermOut.mono' (hc : Checked f info) {idom : Array (Option Nat)}
    {V V' : Nat → Option Block} {B B' : ValueId → Prop} {st st' : SState} {S S' : Subst}
    {d blen : Nat} {b0 : Block} {t : Terminator}
    (h : TermOut info idom V B st d blen b0 t) (hb : f.blocks[d]? = some b0)
    (hp : Prog V V' B B' st st' S S') : TermOut info idom V' B' st' d blen b0 t :=
  h.mono hp (fun bc hbc y hy => by
      obtain ⟨bc0, hbc0, -, ha⟩ := h.calls bc hbc
      exact typed_of_map ha (fun x hx => Option.isSome_iff_exists.2
        (hc.termTyped hb (args_sub_termOperands hbc0 hx))) y hy)
    (fun x d' tb he => by have := h.brt; rw [he] at this; exact ⟨_, this⟩)

/-- **One statement** (generic form): the facts a processed statement provides keep the
invariant. `s` is statement `j` of block `bi`, `lg` its record, `st'`/`S'` the new state and
renaming. -/
theorem step_gen (hc : Checked f info) (h : RunXInv f info allowed skelOk logs bi j lgs st S)
    {b0 : Block} {s : Stmt} (hb0 : f.blocks[bi]? = some b0) (hs : b0.body[j]? = some s)
    {st' : SState} {S' : Subst} {lg : StmtLog}
    (hRI : RInv f (emitV (CurV f logs bi lgs) bi lg.out.toList) (Bad f logs bi (j + 1) S')
      (fun _ => False) (fun _ => False) st')
    (hgood : ∀ y, Placed st (Bad f logs bi j S) y → Placed st' (Bad f logs bi (j + 1) S') y)
    (htypes : ∀ y t, st.types.get? y = some t → st'.types.get? y = some t)
    (havail : ∀ y d, st.avail.get? y = some d → st'.avail.get? y = some d)
    (havailNew : ∀ y d, st'.avail.get? y = some d →
      st.avail.get? y = some d ∨ (d = bi ∧ ∃ t ∈ lg.out.toList, y ∈ t.results))
    (hdefsKeep : ∀ y n, st.defs.get? y = some n → st.avail.contains y = true →
      st'.defs.get? y = some n)
    (hfresh : ∀ y n, st'.defs.get? y = some n → st.defs.get? y = some n ∨ maxValue f < y ∨
      (y ∈ s.results ∧ skeletonStmt s = false ∧ st.known y = false))
    (halts : ∀ x ms, st'.alts.get? x = some ms →
      st.alts.get? x = some ms ∨ ¬ Bad f logs bi (j + 1) S' x)
    (hS : ∀ y w, S.get? y = some w → S'.get? y = some w)
    (hSnew : ∀ y w, S'.get? y = some w → S.get? y = some w ∨ (y ∈ s.results ∧
      Placed st' (Bad f logs bi (j + 1) S') w ∧
      AvailHere info.cfg.idom (emitV (CurV f logs bi lgs) bi lg.out.toList) bi w ∧
      st'.types.get? w = st'.types.get? y))
    (hnewOut : ∀ k t, lg.out.toList[k]? = some t →
      OutStmt f allowed skelOk info.cfg.idom (emitV (CurV f logs bi lgs) bi lg.out.toList)
        (Bad f logs bi (j + 1) S') st' bi ((outsOf lgs).length + k) t)
    (hnewRes : ∀ t ∈ lg.out.toList, ∀ y ∈ t.results, ¬ Bad f logs bi (j + 1) S' y)
    (hlog : SLogFact info.cfg.idom (emitV (CurV f logs bi lgs) bi lg.out.toList)
      (Bad f logs bi (j + 1) S') st' S' bi s (outsOf lgs).length lg)
    (hresDone : ∀ r ∈ s.results, S'.contains r = false →
      Placed st' (Bad f logs bi (j + 1) S') r ∧ st'.avail.get? r = some bi)
    (hci : isCallInd s.inst = true → ∃ s', lg = StmtLog.skel s' .keep #[s']) :
    RunXInv f info allowed skelOk logs bi (j + 1) (lgs ++ [lg]) st' S' := by
  have hn := h.notbi
  have hres : ∀ y ∈ s.results, (defMap f).get? y = some (bi, j + 1) :=
    fun y hy => hc.site_res hb0 hs hy
  have hcontains : ∀ y, S'.contains y = true → S.contains y = true ∨ y ∈ s.results := by
    intro y hy
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 ((hm_contains_iff _ _).1 hy)
    rcases hSnew y w hw with h1 | ⟨h1, -⟩
    · exact .inl ((hm_contains_iff _ _).2 (by rw [h1]; rfl))
    · exact .inr h1
  have hSc : ∀ y, S.contains y = true → S'.contains y = true := by
    intro y hy
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 ((hm_contains_iff _ _).1 hy)
    exact (hm_contains_iff _ _).2 (by rw [hS y w hw]; rfl)
  have hSc' : ∀ y, S'.contains y = false → S.contains y = false := by
    intro y hy
    cases hk : S.contains y with
    | false => rfl
    | true => rw [hSc y hk] at hy; cases hy
  have hbadRes : ∀ y ∈ s.results, Bad f logs bi j S y := fun y hy =>
    .inl ⟨hc.def_le (hres y hy), not_done_site hn (hres y hy)⟩
  have hbad : ∀ y, Bad f logs bi (j + 1) S' y → Bad f logs bi j S y := by
    rintro y (⟨hy1, hy2⟩ | hy)
    · exact .inl ⟨hy1, fun hd => hy2 hd.succ⟩
    · rcases hcontains y hy with hy | hy
      · exact .inr hy
      · exact hbadRes y hy
  have hVa := CurV_append f logs bi lgs lg
  have hprog : Prog (CurV f logs bi lgs) (emitV (CurV f logs bi lgs) bi lg.out.toList)
      (Bad f logs bi j S) (Bad f logs bi (j + 1) S') st st' S S' := by
    refine ⟨VExt.emit _ _ _, hgood, hbad, htypes, hdefsKeep, fun x hx hk => ?_, hS, fun y hy => ?_⟩
    · cases hd : st'.defs.get? x with
      | none => rfl
      | some n =>
        rcases hfresh x n hd with h1 | h1 | ⟨-, -, h1⟩
        · rw [hx] at h1; cases h1
        · rcases known_iff.1 hk with h2 | h2
          · rw [hx] at h2; cases h2
          · obtain ⟨d, hd2⟩ := Option.isSome_iff_exists.1 ((hm_contains_iff _ _).1 h2)
            have := h.availBig x d hd2 h1; rw [hx] at this; cases this
        · rw [hk] at h1; cases h1
    · rcases hcontains y hy with hy | hy
      · exact .inl hy
      · exact .inr (hbadRes y hy)
  have hkB : ∀ y, S.contains y = true → Bad f logs bi j S y := fun y hy => .inr hy
  have hav : ∀ x d t, DefAt (CurV f logs bi lgs) x d t → st.avail.get? x = some d :=
    h.rinv.m.defAvail
  have hcurbi := CurV_bi (lgs := lgs) hn hb0
  obtain ⟨b0', hb0', hjle, hcur⟩ := h.cur
  rw [hb0] at hb0'; cases hb0'
  refine ⟨⟨by rw [hVa]; exact hRI, fun y t hy => htypes y t (h.srcTy y t hy), fun y d hy => havail y d (h.leafAv y d hy),
    ?availSrc, ?defsSrc, ?defsLeaf, ?doneAv, ?substOk, ?outs, ?done, h.size, ?altsNB, ?keysRes,
    ?availBig, h.ciDone, ?defNB⟩, ?cur, hn, h.preds, ?ciCur⟩
  case availSrc =>
    intro y d hy hle
    rcases havailNew y d hy with hy' | ⟨hdb, t, ht, hyt⟩
    · rcases h.availSrc y d hy' hle with h1 | ⟨t, ht, hd⟩
      · exact .inl h1
      · exact .inr ⟨t, ht, hd.succ⟩
    · rw [hdb] at hy ⊢
      have hnb := hnewRes t ht y hyt
      have hdone : Done f logs bi (j + 1) y := by
        refine Classical.byContradiction fun hnd => hnb (.inl ⟨hle, hnd⟩)
      have hnS : S'.contains y = false := by
        cases hk : S'.contains y with
        | false => rfl
        | true => exact absurd (.inr hk) hnb
      rcases hdone.cases_succ with hd | hd
      · obtain ⟨-, d', t', hd', hav'⟩ := h.doneAv y hd (hSc' y hnS)
        have := havail y d' hav'
        rw [hy] at this; cases this
        exact .inr ⟨t', hd', hdone⟩
      · exact .inr ⟨j + 1, hd, hdone⟩
  case defsSrc =>
    intro y n hy hle
    rcases hfresh y n hy with h1 | h1 | ⟨h1, -, -⟩
    · exact (h.defsSrc y n h1 hle).succ
    · exact absurd hle (Nat.not_le.2 h1)
    · exact done_site (hres y h1)
  case defsLeaf =>
    intro y hy
    cases hd : st'.defs.get? y with
    | none => rfl
    | some n =>
      rcases hfresh y n hd with h1 | h1 | ⟨h1, h2, -⟩
      · rw [h.defsLeaf y hy] at h1; cases h1
      · exact absurd (hc.leaf_le hy) (Nat.not_le.2 h1)
      · rw [hc.not_leaf' hb0 hs h1 h2] at hy; cases hy
  case doneAv =>
    intro y hy hyS
    rcases hy.cases_succ with hd | hd
    · obtain ⟨hp, d, t, hdt, hav'⟩ := h.doneAv y hd (hSc' y hyS)
      exact ⟨hgood y hp, d, t, hdt, havail y d hav'⟩
    · obtain ⟨b, s2, hb, hs2, hy2⟩ := hc.site_stmt hd
      rw [hb0] at hb; cases hb; rw [hs] at hs2; cases hs2
      obtain ⟨hp, hav'⟩ := hresDone y hy2 hyS
      exact ⟨hp, bi, j + 1, hd, hav'⟩
  case substOk =>
    rw [hVa]
    intro y w hyw
    rcases hSnew y w hyw with h1 | ⟨h1, hp, ⟨d', t', hd', hrel⟩, hty⟩
    · obtain ⟨e1, e2, ⟨d', t', hd', d, t, hdt, hrel⟩, e4⟩ := h.substOk y w h1
      refine ⟨e1.succ, hgood w e2, ⟨d', t', hd'.ext (VExt.emit _ _ _), d, t, hdt, hrel⟩, ?_⟩
      obtain ⟨T, hT⟩ := Checked.typed (hc := hc) hdt
      have h3 := h.srcTy y T hT
      rw [htypes y T h3, htypes w T (by rw [e4]; exact h3)]
    · exact ⟨done_site (hres y h1), hp, ⟨d', t', hd', bi, j + 1, hres y h1, hrel⟩, hty⟩
  case outs =>
    rw [hVa]
    intro d b hb
    by_cases hdb : d = bi
    · rw [hdb] at hb ⊢
      have hb' : emitV (CurV f logs bi lgs) bi lg.out.toList bi =
          some { b0 with body := outsOf lgs ++ lg.out.toList } := by simp [emitV, hcurbi]
      rw [hb'] at hb; cases hb
      refine ⟨⟨b0, hb0, rfl, rfl⟩, fun k t hk => ?_⟩
      rcases Nat.lt_or_ge k (outsOf lgs).length with hkl | hkl
      · rw [List.getElem?_append_left hkl] at hk
        exact ((h.outs bi _ hcurbi).2 k t hk).mono hprog hav ⟨_, hcurbi, hk⟩
      · rw [List.getElem?_append_right hkl] at hk
        have := hnewOut (k - (outsOf lgs).length) t hk
        rwa [Nat.add_sub_cancel' hkl] at this
    · have hb' : emitV (CurV f logs bi lgs) bi lg.out.toList d = CurV f logs bi lgs d := by
        simp [emitV, hdb]
      rw [hb'] at hb
      obtain ⟨e1, e2⟩ := h.outs d b hb
      exact ⟨e1, fun k t hk => (e2 k t hk).mono hprog hav ⟨b, hb, hk⟩⟩
  case done =>
    rw [hVa]
    intro d lg' hlg
    obtain ⟨b1, bo, hb1, hbo, e1, e2, e3⟩ := h.done d lg' hlg
    exact ⟨b1, bo, hb1, hbo, StmtsFact.mono hprog hkB _ _ _ e1, e2.mono hprog hkB,
      e3.mono' hc hb1 hprog⟩
  case altsNB =>
    intro x ms hx
    rcases halts x ms hx with h1 | h1
    · exact fun hb => h.altsNB x ms h1 (hbad x hb)
    · exact h1
  case keysRes =>
    intro y hy
    rcases hcontains y hy with h1 | h1
    · exact h.keysRes y h1
    · exact ⟨bi, j, hres y h1⟩
  case availBig =>
    intro x d hx hlt
    rcases havailNew x d hx with h1 | ⟨-, t, ht, hxt⟩
    · obtain ⟨n, hn'⟩ := Option.isSome_iff_exists.1 (h.availBig x d h1 hlt)
      rw [hdefsKeep x n hn' ((hm_contains_iff _ _).2 (by rw [h1]; rfl))]; rfl
    · obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 ht
      have ho := hnewOut k t hk
      by_cases hsk : skeletonStmt t = true
      · exact absurd (hc.leaf_le (ho.leaf hsk x hxt).2) (Nat.not_le.2 hlt)
      · have hsk' : isPure t.inst = true ∧ t.results.length = 1 := by
          simpa [skeletonStmt] using hsk
        obtain ⟨x', hx'⟩ := List.length_eq_one_iff.1 hsk'.2
        rw [hx', List.mem_singleton] at hxt; subst hxt
        rw [ho.node _ hx' hsk'.1]; rfl
  case defNB =>
    rw [hVa]
    intro y d t hy
    rcases hy.of_emit with hy | ⟨b, hb, -, k, t1, -, ht1, hyt⟩
    · exact fun hb => h.defNB y d t hy (hbad y hb)
    · exact hnewRes t1 (List.mem_of_getElem? ht1) y hyt
  case cur =>
    rw [hVa]
    refine ⟨b0, hb0, ?_, ?_⟩
    · have := (List.getElem?_eq_some_iff.1 hs).1; omega
    · rw [take_succ_of_getElem? hs]
      refine StmtsFact.snoc (StmtsFact.mono hprog hkB _ _ _ hcur) ?_
      simpa using hlog
  case ciCur =>
    intro b hb
    rw [hb0] at hb; cases hb
    rw [take_succ_of_getElem? hs]
    exact (h.ciCur b0 hb0).snoc hcur.length hci

end Step

end Opt
