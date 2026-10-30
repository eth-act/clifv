import FV.Opt.Proof.CompleteSimpStmt
import FV.Opt.Proof.CompleteSimpInv

/-!
# Completeness of simplify: one statement

Every statement keeps the invariant `Opt.RunXInv`: `step_gen` is the generic form (the facts a
processed statement provides), instantiated by `step_pure` (a pure statement, kept or replaced)
and `step_skel` (a skeleton statement, by its outcome). `NewOk.outStmt`/`TrapOk.outStmt`/`src_out`:
emitted nodes, emitted conditional traps and renamed source statements are output statements.
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

/-! ## Output statements -/

section Out

variable {f : Function} {info : Info} {allowed skelOk : Inst → Bool}

theorem resultTypes_pure {i : Inst} (hp : isPure i = true) (a a' : FnRef → Option Signature)
    (b b' : Nat → Option Signature) : i.resultTypes a b = i.resultTypes a' b' := by
  cases i <;> first | rfl | simp [isPure] at hp

theorem isCallInd_of_pure {i : Inst} (hp : isPure i = true) : isCallInd i = false := by
  cases i <;> first | rfl | simp [isPure] at hp

theorem notCall_of_pure {i : Inst} (hp : isPure i = true) : notCall i = true := by
  cases i <;> first | rfl | simp [isPure] at hp

theorem pure_res {i : Inst} {ty : ValueId → Option Ty} {fn : Function} (hp : isPure i = true)
    (ht : pureTyped ty fn i = true) (a : FnRef → Option Signature) (b : Nat → Option Signature) :
    ∃ T, i.resultTypes a b = some [T] ∧ SState.nodeTy i = some T := by
  rw [resultTypes_pure hp a (fun _ => none) b (fun _ => none)]
  cases i <;> simp_all [isPure, SState.nodeTy, Inst.resultTypes, pureTyped]
  rename_i t _ _
  cases h : t.double? <;> simp_all

/-- An emitted node is an inserted statement (`allowed` never admits `symbol_value`). -/
theorem insOk_of {n : Inst} {τ : ValueId → ValueId} {r : ValueId} (hal : allowed n = true)
    (hsym : ∀ ty gv, allowed (.symbolValue ty gv) = false) (hp : isPure (mapOperands τ n) = true) :
    insOk { results := [r], inst := mapOperands τ n } = true := by
  cases n <;> simp_all [insOk, mapOperands, isPure]

/-- Result types without signature lookups are the result types. -/
theorem resultTypes_none {i : Inst} {ts : List Ty}
    (h : i.resultTypes (fun _ => none) (fun _ => none) = some ts)
    (a : FnRef → Option Signature) (b : Nat → Option Signature) : i.resultTypes a b = some ts := by
  cases i <;> simp_all [Inst.resultTypes]
  rename_i op _ _
  cases op <;> simp_all

theorem notCall_of_none {i : Inst} {ts : List Ty}
    (h : i.resultTypes (fun _ => none) (fun _ => none) = some ts) :
    notCall i = true ∧ isCallInd i = false := by
  cases i <;> simp_all [Inst.resultTypes, notCall, isCallInd]

theorem trap_res {i : Inst} (h : isTrapLike i = true) (a : FnRef → Option Signature)
    (b : Nat → Option Signature) :
    i.resultTypes a b = some [] ∧ isPure i = false ∧ notCall i = true ∧ isCallInd i = false := by
  cases i <;> simp_all [isTrapLike, Inst.resultTypes, isPure, notCall, isCallInd]

/-- An emitted node is an output statement. -/
theorem NewOk.outStmt {idom : Array (Option Nat)} {V : Nat → Option Block} {B : ValueId → Prop}
    {st : SState} {bi k : Nat} {s : Stmt}
    (hdt : ∀ x n, st.defs.get? x = some n → isPure n = true ∧
      pureTyped (fun y => st.types.get? y) f n = true ∧ st.types.get? x = SState.nodeTy n)
    (h : NewOk idom V bi k allowed B st s) : OutStmt f allowed skelOk idom V B st bi k s := by
  obtain ⟨r, n', rfl, hd, -, -, ⟨n, τ, hal, rfl⟩, hops⟩ := h
  obtain ⟨hp, hpt, hty⟩ := hdt r _ hd
  obtain ⟨T, hT, hN⟩ := pure_res hp hpt (sigOf f) (fun _ => none)
  have hpn : isPure n = true := by rwa [isPure_mapOperands] at hp
  refine ⟨fun y hy => hops y hy, ⟨[T], hT, rfl, fun m x hx => ?_⟩, fun _ => hpt,
    fun x hx _ => ?_, fun hs => ?_, by simp,
    .inr ⟨n, τ, .inl hal, rfl, notCall_of_pure hpn, isCallInd_of_pure hpn⟩⟩
  · rcases m with _ | m
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at hx; subst hx; rw [hty, hN]; rfl
    · simp at hx
  · simp only [List.cons.injEq, and_true] at hx; subst hx; exact hd
  · simp [skeletonStmt, hp] at hs

/-- An emitted conditional trap is an output statement. -/
theorem TrapOk.outStmt {idom : Array (Option Nat)} {V : Nat → Option Block} {B : ValueId → Prop}
    {st : SState} {bi k : Nat} {s : Stmt} (h : TrapOk idom V bi k skelOk B st s) :
    OutStmt f allowed skelOk idom V B st bi k s := by
  obtain ⟨hr, htl, ⟨n, τ, hsk, he⟩, hops⟩ := h
  obtain ⟨hrt, hpure, -, -⟩ := trap_res htl (sigOf f) (fun _ => none)
  have htn : isTrapLike n = true := by rw [he, isTrapLike_mapOperands] at htl; exact htl
  obtain ⟨-, -, hcn, hin⟩ := trap_res htn (sigOf f) (fun _ => none)
  refine ⟨fun y hy => ⟨(hops y hy).2, (hops y hy).1⟩, ⟨[], hrt, by simp [hr], fun m x hx => ?_⟩,
    fun hp => ?_, fun x hx => ?_, fun _ r hr' => ?_, by simp [hr],
    .inr ⟨n, τ, .inr hsk, he, hcn, hin⟩⟩
  · rw [hr] at hx; simp at hx
  · rw [hpure] at hp; cases hp
  · rw [hr] at hx; cases hx
  · rw [hr] at hr'; cases hr'

theorem Checked.res_leaf (hc : Checked f info) {d k : Nat} {b : Block} {s : Stmt} {r : ValueId}
    (hb : f.blocks[d]? = some b) (hs : b.body[k]? = some s) (hsk : skeletonStmt s = true)
    (hr : r ∈ s.results) : (initAvail f).get? r = some d :=
  (initAvail_get hc.unique r d).2 (mem_leafList.2 ⟨b, hb, .inr ⟨s, List.mem_of_getElem? hs, hsk, hr⟩⟩)

/-- A source statement with renamed operands is an output statement. -/
theorem src_out (hc : Checked f info) {idom : Array (Option Nat)} {V : Nat → Option Block}
    {B : ValueId → Prop} {st : SState} {bi j k : Nat} {b0 : Block} {s : Stmt}
    {σ : ValueId → ValueId} (hb0 : f.blocks[bi]? = some b0) (hs : b0.body[j]? = some s)
    (hops : ∀ y ∈ operands (mapOperands σ s.inst), AvailAt idom V bi k y ∧ Placed st B y)
    (hty : ∀ y t, info.types.get? y = some t → st.types.get? y = some t)
    (hpt : isPure s.inst = true → pureTyped (fun y => st.types.get? y) f (mapOperands σ s.inst) = true)
    (hnode : ∀ x, s.results = [x] → isPure s.inst = true →
      st.defs.get? x = some (mapOperands σ s.inst))
    (hleaf : skeletonStmt s = true → ∀ r ∈ s.results, st.defs.get? r = none) :
    OutStmt f allowed skelOk idom V B st bi k { s with inst := mapOperands σ s.inst } := by
  obtain ⟨ts, hts, hlen, htys⟩ := hc.wf.results bi b0 hb0 j s hs
  have hsk : skeletonStmt { s with inst := mapOperands σ s.inst } = skeletonStmt s := by
    simp [skeletonStmt, isPure_mapOperands]
  refine ⟨hops, ⟨ts, by rw [resultTypes_mapOperands]; exact hts, hlen, fun m r hr => ?_⟩,
    fun hp => hpt (by rwa [isPure_mapOperands] at hp), fun x hx hp => hnode x hx (by rwa [isPure_mapOperands] at hp),
    fun hs' r hr => ⟨hleaf (by rwa [hsk] at hs') r hr, ?_⟩, (hc.res_nodup hb0 hs :),
    .inl ⟨b0, hb0, s, List.mem_of_getElem? hs, σ, rfl⟩⟩
  · have h1 := htys m r hr
    have hml : m < ts.length := by rw [hlen]; exact (List.getElem?_eq_some_iff.1 hr).1
    rw [List.getElem?_eq_getElem hml] at h1 ⊢
    exact hty r _ h1
  · rw [hm_contains_iff, hc.res_leaf hb0 hs (by rwa [hsk] at hs') hr]; rfl

end Out

/-! ## Pure statements -/

section PureStep

variable {f : Function} {info : Info} {allowed skelOk : Inst → Bool}
  {logs : Array (Option BlockLog)} {bi j : Nat} {lgs : List StmtLog} {st : SState} {S : Subst}

/-- The operands of statement `j` of block `bi`: renamed to placeable values available here. -/
theorem RunXInv.ops (hc : Checked f info) (h : RunXInv f info allowed skelOk logs bi j lgs st S)
    {b0 : Block} {s : Stmt} (hb0 : f.blocks[bi]? = some b0) (hs : b0.body[j]? = some s) {y : ValueId}
    (hy : y ∈ operands s.inst) :
    (S.contains y = true ∨ ¬ Bad f logs bi j S y) ∧ Placed st (Bad f logs bi j S) (S.step y) ∧
      AvailHere info.cfg.idom (CurV f logs bi lgs) bi (S.step y) ∧
      st.types.get? (S.step y) = info.types.get? y := by
  obtain ⟨-, h1, h2, h3, h4⟩ := h.simp.renOp hc (hc.wf.uses bi b0 hb0 j s hs y hy)
  exact ⟨h1, h2, h3, h4⟩

theorem mem_ops_map {σ : ValueId → ValueId} {i : Inst} {y : ValueId}
    (hy : y ∈ operands (mapOperands σ i)) : ∃ x ∈ operands i, y = σ x := by
  rw [operands_mapOperands, List.mem_map] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact ⟨x, hx, rfl⟩

/-- The renamed operands, at the end of the current output block. -/
theorem RunXInv.opsAt (hc : Checked f info) (h : RunXInv f info allowed skelOk logs bi j lgs st S)
    {b0 : Block} {s : Stmt} (hb0 : f.blocks[bi]? = some b0) (hs : b0.body[j]? = some s)
    (new : List Stmt) :
    ∀ y ∈ operands (mapOperands S.step s.inst),
      AvailAt info.cfg.idom (emitV (CurV f logs bi lgs) bi new) bi (outsOf lgs).length y ∧
        Placed st (Bad f logs bi j S) y := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := mem_ops_map hy
  obtain ⟨-, h2, h3, -⟩ := h.ops hc hb0 hs hx
  exact ⟨(h3.at_end (CurV_bi h.notbi hb0)).emit bi new, h2⟩

theorem stepStmt_pure {rules : SimplifyFn} {skel : SkeletonFn} {cfg : Cfg} {s : Stmt} {v : ValueId}
    (hres : s.results = [v]) (hpi : isPure (mapOperands S.find s.inst) = true)
    (hchk : (st.inGraph v || decide (st.next ≤ v) ||
      !(operands (mapOperands S.find s.inst)).all st.avail.contains ||
      !st.typedNode (mapOperands S.find s.inst) ||
      st.types.get? v != SState.nodeTy (mapOperands S.find s.inst)) = false) :
    stepStmt rules skel allowed skelOk cfg bi (st, S) s =
      pureStep rules allowed cfg bi st S s (mapOperands S.find s.inst) v := by
  simp only [stepStmt, hres, hpi, hchk]
  rfl

/-- **A pure statement** keeps the invariant. -/
theorem step_pure {rules : SimplifyFn} {skel : SkeletonFn} (hc : Checked f info)
    (hR : SimpRulesProv rules) (hsym : ∀ ty gv, allowed (.symbolValue ty gv) = false)
    (h : RunXInv f info allowed skelOk logs bi j lgs st S) {b0 : Block} {s : Stmt} {v : ValueId}
    (hb0 : f.blocks[bi]? = some b0) (hs : b0.body[j]? = some s) (hres : s.results = [v])
    (hpure : isPure s.inst = true) :
    RunXInv f info allowed skelOk logs bi (j + 1)
      (lgs ++ [(stepStmt rules skel allowed skelOk info.cfg bi (st, S) s).2.2])
      (stepStmt rules skel allowed skelOk info.cfg bi (st, S) s).1
      (stepStmt rules skel allowed skelOk info.cfg bi (st, S) s).2.1 := by
  have hfind : mapOperands S.find s.inst = mapOperands S.step s.inst :=
    mapOperands_congr (fun y _ => h.simp.find_eq y)
  have hpi : isPure (mapOperands S.step s.inst) = true := by rw [isPure_mapOperands]; exact hpure
  have hvs : (defMap f).get? v = some (bi, j + 1) := hc.site_res hb0 hs (by rw [hres]; simp)
  have hvle := hc.def_le hvs
  have hvnd : ¬ Done f logs bi j v := not_done_site h.notbi hvs
  have hvB : Bad f logs bi j S v := .inl ⟨hvle, hvnd⟩
  have hskf : skeletonStmt s = false := by simp [skeletonStmt, hpure, hres]
  have hvS : S.contains v = false := by
    cases hk : S.contains v with
    | false => rfl
    | true =>
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 ((hm_contains_iff _ _).1 hk)
      exact absurd (h.substOk v w hw).1 hvnd
  have hvk : st.known v = false := by
    cases hk : st.known v with
    | false => rfl
    | true =>
      exfalso
      rcases known_iff.1 hk with h1 | h1
      · obtain ⟨n, hn⟩ := Option.isSome_iff_exists.1 h1
        exact hvnd (h.defsSrc v n hn hvle)
      · obtain ⟨d, hd⟩ := Option.isSome_iff_exists.1 ((hm_contains_iff _ _).1 h1)
        rcases h.availSrc v d hd hvle with h2 | ⟨-, -, h2⟩
        · rw [hc.not_leaf hb0 hs (by rw [hres]; simp) hskf] at h2; cases h2
        · exact hvnd h2
  have hvn : v < st.next := Nat.lt_of_le_of_lt hvle h.rinv.m.maxLt
  have hpt0 : pureTyped (fun y => info.types.get? y) f s.inst = true :=
    hc.wf.pure bi b0 hb0 j s hs hpure
  have hpt : pureTyped (fun y => st.types.get? y) f (mapOperands S.step s.inst) = true := by
    rw [pureTyped_mapOperands, ← hpt0]
    exact pureTyped_congr (fun y hy => (h.ops hc hb0 hs hy).2.2.2) rfl rfl
  have hty : st.types.get? v = SState.nodeTy (mapOperands S.step s.inst) := by
    obtain ⟨ts, hts, -, htys⟩ := hc.wf.results bi b0 hb0 j s hs
    obtain ⟨T, hT, hN⟩ := pure_res hpure hpt0 (sigOf f) (fun _ => none)
    rw [hT] at hts; cases hts
    have h1 := htys 0 v (by rw [hres]; rfl)
    rw [nodeTy_mapOperands, hN]
    exact h.srcTy v T h1
  have hplaced : ∀ y ∈ operands (mapOperands S.step s.inst), Placed st (Bad f logs bi j S) y :=
    fun y hy => (h.opsAt hc hb0 hs [] y hy).2
  have havc : ∀ y ∈ operands (mapOperands S.step s.inst), st.avail.contains y = true := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_ops_map hy
    obtain ⟨d, t, hd, -⟩ := (h.ops hc hb0 hs hx).2.2.1
    exact (hm_contains_iff _ _).2 (by rw [h.rinv.m.defAvail _ d t hd]; rfl)
  have hvg : st.inGraph v = false := by
    simp only [SState.inGraph, hvk, Bool.false_or]
    cases hp : st.partials.contains v with
    | false => rfl
    | true => exact absurd (h.rinv.partialsBig v hp) (Nat.not_lt.2 hvle)
  have hchk : (st.inGraph v || decide (st.next ≤ v) ||
      !(operands (mapOperands S.find s.inst)).all st.avail.contains ||
      !st.typedNode (mapOperands S.find s.inst) ||
      st.types.get? v != SState.nodeTy (mapOperands S.find s.inst)) = false := by
    rw [hfind]
    have e1 : (operands (mapOperands S.step s.inst)).all st.avail.contains = true :=
      List.all_eq_true.2 havc
    have e2 : st.typedNode (mapOperands S.step s.inst) = true := by
      simp only [SState.typedNode, hpi, h.rinv.m.fn, hpt, Bool.and_self]
    have e3 : (st.types.get? v != SState.nodeTy (mapOperands S.step s.inst)) = false := by
      rw [hty]; simp
    simp only [hvg, decide_eq_false (Nat.not_le.2 hvn), e1, e2, e3, Bool.not_true, Bool.or_self]
  rw [stepStmt_pure hres (by rw [hfind]; exact hpi) hchk, hfind]
  have hbV := CurV_bi (lgs := lgs) h.notbi hb0
  have hP0 := pure_ok (V := CurV f logs bi lgs) (B := Bad f logs bi j S)
    (b := { b0 with body := outsOf lgs }) hR allowed info.cfg bi (subst := S) (s := s)
    h.rinv hbV hres hpi hpt hty hplaced hvk hvn hvB
  generalize pureStep rules allowed info.cfg bi st S s (mapOperands S.step s.inst) v = r at hP0 ⊢
  obtain ⟨stF, S', lg⟩ := r
  have hvres : v ∈ s.results := by rw [hres]; simp
  have hfr : ∀ y n, stF.defs.get? y = some n → st.defs.get? y = some n ∨ maxValue f < y ∨ y = v →
      st.defs.get? y = some n ∨ maxValue f < y ∨
        (y ∈ s.results ∧ skeletonStmt s = false ∧ st.known y = false) := by
    rintro y n - (h1 | h1 | rfl)
    · exact .inl h1
    · exact .inr (.inl h1)
    · exact .inr (.inr ⟨hvres, hskf, hvk⟩)
  have hci : isCallInd s.inst = true → ∃ s', lg = StmtLog.skel s' .keep #[s'] := by
    intro hci; rw [isCallInd_of_pure hpure] at hci; cases hci
  rcases hP0 with ⟨hlg, hP⟩ | ⟨⟨w0, o0, hlg⟩, hP⟩
  · -- kept
    simp only at hlg hP ⊢
    obtain ⟨-, hS', havv, hplv, hdv⟩ : lg = .keep { s with inst := mapOperands S.step s.inst } ∧
        S' = S ∧ stF.avail.get? v = some bi ∧ Placed stF (fun y => Bad f logs bi j S y ∧ y ≠ v) v ∧
        stF.defs.get? v = some (mapOperands S.step s.inst) := by
      rcases hP.kind with h1 | ⟨w, h1, -⟩
      · exact h1
      · rw [hlg] at h1; cases h1
    subst S'
    have hBe : Bad f logs bi (j + 1) S = fun y => Bad f logs bi j S y ∧ y ≠ v := by
      funext y
      apply propext
      constructor
      · rintro (⟨hy1, hy2⟩ | hy)
        · refine ⟨.inl ⟨hy1, fun hd => hy2 hd.succ⟩, ?_⟩
          rintro rfl; exact hy2 (done_site hvs)
        · refine ⟨.inr hy, ?_⟩
          rintro rfl; rw [hvS] at hy; cases hy
      · rintro ⟨hy1 | hy1, hy2⟩
        · refine .inl ⟨hy1.1, fun hd => ?_⟩
          rcases hd.cases_succ with hd | hd
          · exact hy1.2 hd
          · obtain ⟨b, s2, hb, hs2, hy3⟩ := hc.site_stmt hd
            exact hy2 (by
              rw [hb0] at hb; cases hb; rw [hs] at hs2; cases hs2
              rw [hres] at hy3; simpa using hy3)
        · exact .inr hy1
    rw [← hBe] at hP hplv
    have hout : lg.out.toList = [{ s with inst := mapOperands S.step s.inst }] := by
      rw [hlg]; rfl
    refine step_gen hc h hb0 hs hP.inv hP.good hP.types hP.avail hP.availNew hP.defsKeep
      (fun y n hy => hfr y n hy (hP.fresh y n hy)) hP.alts (fun _ _ h => h) (fun _ _ h => .inl h)
      ?_ ?_ ?_ ?_ hci
    · intro k t hk
      rw [hout] at hk
      rcases k with _ | k
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
        subst hk
        refine src_out hc hb0 hs (fun y hy => ?_) (fun y t hy => hP.types y t (h.srcTy y t hy))
          (fun _ => pureTyped_grow hpi hpt hP.types) (fun x hx _ => ?_) (fun hsk => ?_)
        · obtain ⟨e1, e2⟩ := h.opsAt hc hb0 hs lg.out.toList y hy
          exact ⟨by simpa using e1, hP.good y e2⟩
        · rw [hres] at hx; cases hx; exact hdv
        · rw [hskf] at hsk; cases hsk
      · simp at hk
    · intro t ht y hy
      rw [hout, List.mem_singleton] at ht
      subst ht
      simp only [hres, List.mem_singleton] at hy
      subst hy
      rw [hBe]; exact fun h => h.2 rfl
    · refine ⟨fun y hy => ?_, ?_⟩
      · rcases (h.ops hc hb0 hs hy).1 with h1 | h1
        · exact .inl h1
        · exact .inr (by rw [hBe]; exact fun h2 => h1 h2.1)
      · rw [hlg]
        refine ⟨rfl, fun r hr => ?_⟩
        rw [hres, List.mem_singleton] at hr; subst hr; exact hplv
    · intro r hr _
      rw [hres, List.mem_singleton] at hr; subst hr
      exact ⟨hplv, havv⟩
  · -- replaced
    simp only at hlg hP ⊢
    obtain ⟨w, hlgw, hS', hnew, hpw, havw, htw, -⟩ : ∃ w, lg = .repl { s with inst := mapOperands S.step s.inst } w lg.out ∧
        S' = S.insert v w ∧
        (∀ k t, lg.out.toList[k]? = some t →
          NewOk info.cfg.idom (emitV (CurV f logs bi lgs) bi lg.out.toList) bi
            (({ b0 with body := outsOf lgs } : Block).body.length + k) allowed
            (Bad f logs bi j S) stF t) ∧
        Placed stF (Bad f logs bi j S) w ∧
        AvailAt info.cfg.idom (emitV (CurV f logs bi lgs) bi lg.out.toList) bi
          (({ b0 with body := outsOf lgs } : Block).body.length + lg.out.size) w ∧
        stF.types.get? w = stF.types.get? v ∧ stF.avail.contains v = false := by
      rcases hP.kind with ⟨h1, -⟩ | h1
      · rw [hlg] at h1; cases h1
      · exact h1
    subst S'
    have hSv : ∀ y, (S.insert v w).contains y = true ↔ y = v ∨ S.contains y = true := by
      intro y; rw [hm_contains_insert']; exact ⟨fun h => h.imp Eq.symm id, fun h => h.imp Eq.symm id⟩
    have hBe : Bad f logs bi (j + 1) (S.insert v w) = Bad f logs bi j S := by
      funext y
      apply propext
      constructor
      · rintro (⟨hy1, hy2⟩ | hy)
        · exact .inl ⟨hy1, fun hd => hy2 hd.succ⟩
        · rcases (hSv y).1 hy with rfl | hy
          · exact hvB
          · exact .inr hy
      · rintro (⟨hy1, hy2⟩ | hy)
        · by_cases hyv : y = v
          · exact .inr ((hSv y).2 (.inl hyv))
          · refine .inl ⟨hy1, fun hd => ?_⟩
            rcases hd.cases_succ with hd | hd
            · exact hy2 hd
            · obtain ⟨b, s2, hb, hs2, hy3⟩ := hc.site_stmt hd
              rw [hb0] at hb; cases hb; rw [hs] at hs2; cases hs2
              rw [hres] at hy3; exact hyv (by simpa using hy3)
        · exact .inr ((hSv y).2 (.inr hy))
    have hdt := hP.inv.m.defsTy
    have hstep_eq : ∀ y ∈ operands s.inst, Subst.step (S.insert v w) y = S.step y := by
      intro y hy
      have hyv : y ≠ v := by
        rintro rfl
        rcases (h.ops hc hb0 hs hy).1 with h1 | h1
        · rw [hvS] at h1; cases h1
        · exact h1 hvB
      have hvy : ¬ v = y := Ne.symm hyv
      simp only [Subst.step, hm_get?_insert, hvy, ite_false]
    rw [← hBe] at hP hpw hnew
    refine step_gen hc h hb0 hs hP.inv (fun y hy => hP.good y (by rw [hBe]; exact hy)) hP.types
      hP.avail hP.availNew hP.defsKeep
      (fun y n hy => hfr y n hy (hP.fresh y n hy)) hP.alts ?_ ?_ ?_ ?_ ?_ (fun r hr hk => ?_) hci
    · intro y w' hy
      have hyv : y ≠ v := by
        rintro rfl
        rw [(hm_contains_iff _ _).2 (by rw [hy]; rfl)] at hvS; cases hvS
      have hvy : ¬ v = y := Ne.symm hyv
      simp only [hm_get?_insert, hvy, ite_false]; exact hy
    · intro y w' hy
      rw [hm_get?_insert] at hy
      split at hy
      · rename_i hvy
        cases hy; subst hvy
        exact .inr ⟨hvres, hpw, havw.here, htw⟩
      · exact .inl hy
    · intro k t hk
      have := (hnew k t hk).outStmt (skelOk := skelOk) hdt
      simpa using this
    · intro t ht y hy
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 ht
      obtain ⟨r, n', rfl, -, -, hrb, -⟩ := hnew k _ hk
      simp only [List.mem_singleton] at hy; subst hy; exact hrb
    · refine ⟨fun y hy => ?_, ?_⟩
      · rcases (h.ops hc hb0 hs hy).1 with h1 | h1
        · exact .inl ((hSv y).2 (.inr h1))
        · exact .inr (by rw [hBe]; exact h1)
      · rw [hlgw]
        refine ⟨?_, hpure, fun t ht => ?_, ⟨v, hres, by simp only [hm_get?_insert, ite_true]⟩, ?_⟩
        · simp only [renStmt]; rw [mapOperands_congr hstep_eq]
        · obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 ht
          obtain ⟨r, n', rfl, hd, -, -, ⟨n, τ, hal, rfl⟩, -⟩ := hnew k _ hk
          exact insOk_of hal hsym (hdt r _ hd).1
        · exact havw
    · exact absurd ((hSv r).2 (.inl (by rw [hres] at hr; simpa using hr))) (by rw [hk]; simp)

end PureStep

/-! ## Skeleton statements -/

section SkelStep

variable {f : Function} {info : Info} {allowed skelOk : Inst → Bool}
  {logs : Array (Option BlockLog)} {bi j : Nat} {lgs : List StmtLog} {st : SState} {S : Subst}

theorem skelCandidate_map (σ : ValueId → ValueId) (i : Inst) :
    skelCandidate (.inst (mapOperands σ i)) = skelCandidate (.inst i) := by
  cases i <;> rfl

theorem cand_facts {i : Inst} (h : skelCandidate (.inst i) = true) :
    notCall i = true ∧ notSym i = true ∧ isCallInd i = false ∧
      ∃ ts, i.resultTypes (fun _ => none) (fun _ => none) = some ts := by
  cases i <;> simp_all [skelCandidate, notCall, notSym, isCallInd, Inst.resultTypes]

theorem not_pure_of_nil {a : Inst} (h : a.resultTypes (fun _ => none) (fun _ => none) = some []) :
    isPure a = false := by
  cases a <;> simp_all [isPure, Inst.resultTypes]

theorem Placed.weaken {st : SState} {B B' : ValueId → Prop} {y : ValueId} (h : Placed st B y)
    (hB : ∀ y, B' y → B y) : Placed st B' y :=
  Placed.mono (fun _ h => h) (fun y hy hb => hy.not_bad (hB y hb)) (fun _ _ h => .inl h)
    (fun _ _ h => .inl h) y h

theorem array_eq_of_toList {a : Array Stmt} {l : List Stmt} (h : a.toList = l) : a = l.toArray := by
  rcases a with ⟨l'⟩; simp only at h; subst h; rfl

/-- Statement `j` of `bi` keeps its results: they leave the bad values. -/
theorem bad_kept (hc : Checked f info) (h : RunXInv f info allowed skelOk logs bi j lgs st S)
    {b0 : Block} {s : Stmt} (hb0 : f.blocks[bi]? = some b0) (hs : b0.body[j]? = some s) :
    Bad f logs bi (j + 1) S = fun y => Bad f logs bi j S y ∧ y ∉ s.results := by
  funext y; apply propext; constructor
  · rintro (⟨hy1, hy2⟩ | hy)
    · exact ⟨.inl ⟨hy1, fun hd => hy2 hd.succ⟩, fun hm => hy2 (done_site (hc.site_res hb0 hs hm))⟩
    · refine ⟨.inr hy, fun hm => ?_⟩
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 ((hm_contains_iff _ _).1 hy)
      exact not_done_site h.notbi (hc.site_res hb0 hs hm) (h.substOk y w hw).1
  · rintro ⟨hy1 | hy1, hy2⟩
    · refine .inl ⟨hy1.1, fun hd => ?_⟩
      rcases hd.cases_succ with hd | hd
      · exact hy1.2 hd
      · obtain ⟨b, s2, hb, hs2, hy3⟩ := hc.site_stmt hd
        rw [hb0] at hb; cases hb; rw [hs] at hs2; cases hs2
        exact hy2 hy3
    · exact .inr hy1

/-- Statement `j` of `bi` loses its results (removed, or renamed by `S'`). -/
theorem bad_gone (hc : Checked f info) (h : RunXInv f info allowed skelOk logs bi j lgs st S)
    {b0 : Block} {s : Stmt} (hb0 : f.blocks[bi]? = some b0) (hs : b0.body[j]? = some s)
    {S' : Subst} (hS' : ∀ y, S'.contains y = true ↔ S.contains y = true ∨ y ∈ s.results) :
    Bad f logs bi (j + 1) S' = Bad f logs bi j S := by
  funext y; apply propext; constructor
  · rintro (⟨hy1, hy2⟩ | hy)
    · exact .inl ⟨hy1, fun hd => hy2 hd.succ⟩
    · rcases (hS' y).1 hy with hy | hy
      · exact .inr hy
      · exact .inl ⟨hc.def_le (hc.site_res hb0 hs hy), not_done_site h.notbi (hc.site_res hb0 hs hy)⟩
  · rintro (⟨hy1, hy2⟩ | hy)
    · by_cases hm : y ∈ s.results
      · exact .inr ((hS' y).2 (.inr hm))
      · refine .inl ⟨hy1, fun hd => ?_⟩
        rcases hd.cases_succ with hd | hd
        · exact hy2 hd
        · obtain ⟨b, s2, hb, hs2, hy3⟩ := hc.site_stmt hd
          rw [hb0] at hb; cases hb; rw [hs] at hs2; cases hs2
          exact hm hy3
    · exact .inr ((hS' y).2 (.inl hy))

/-- Emitting a statement whose results are available here and not yet defined in the view. -/
theorem MInv.emitRes {V : Nat → Option Block} {B : ValueId → Prop} {st : SState} {b : Block}
    (h : MInv f V B st) (hb : V bi = some b) {t : Stmt}
    (ht : ∀ y ∈ t.results, st.avail.get? y = some bi ∧ ∀ d k, ¬ DefAt V y d k) :
    MInv f (emitV V bi [t]) B st := by
  have hdef : ∀ y d k, DefAt (emitV V bi [t]) y d k →
      DefAt V y d k ∨ (y ∈ t.results ∧ d = bi ∧ k = b.body.length + 1) := by
    intro y d k hy
    rcases hy.of_emit with hy | ⟨b1, hb1, hd, m, s1, hk, hs1, hy1⟩
    · exact .inl hy
    · rw [hb] at hb1; cases hb1
      rcases m with _ | m
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at hs1; subst hs1
        exact .inr ⟨hy1, hd, by rw [hk]⟩
      · simp at hs1
  refine ⟨h.fn, h.maxLt, h.knownLt, h.typesFresh, h.defsTy, h.altsKnown, fun y d hy hb' => ?_,
    fun y d k hy => ?_, h.newBig, h.badLe, fun y d k d' k' h1 h2 => ?_⟩
  · obtain ⟨k, hk⟩ := h.availDef y d hy hb'
    exact ⟨k, hk.emit bi [t]⟩
  · rcases hdef y d k hy with hy | ⟨hy2, hd, -⟩
    · exact h.defAvail y d k hy
    · rw [hd]; exact (ht y hy2).1
  · rcases hdef y d k h1 with h1 | ⟨hy1, e1, e2⟩ <;> rcases hdef y d' k' h2 with h2 | ⟨hy2, e3, e4⟩
    · exact h.uniq _ _ _ _ _ h1 h2
    · exact absurd h1 ((ht y hy2).2 _ _)
    · exact absurd h2 ((ht y hy1).2 _ _)
    · exact ⟨e1.trans e3.symm, e2.trans e4.symm⟩

/-- A kept skeleton statement (results `R`, available here and still bad) is emitted: its results
leave the bad values. -/
theorem rinv_kept {V : Nat → Option Block} {B : ValueId → Prop} {st : SState} {b : Block}
    {t : Stmt} {R : List ValueId}
    (h : RInv f V B (fun _ => False) (fun _ => False) st) (hb : V bi = some b) (htr : t.results = R)
    (hav : ∀ y ∈ R, st.avail.get? y = some bi) (hbad : ∀ y ∈ R, B y)
    (hnd : ∀ y d k, DefAt V y d k → ¬ B y) :
    RInv f (emitV V bi [t]) (fun y => B y ∧ y ∉ R) (fun _ => False) (fun _ => False) st := by
  have hm : MInv f (emitV V bi [t]) B st :=
    h.m.emitRes hb fun y hy => ⟨hav y (htr ▸ hy), fun d k hk => hnd y d k hk (hbad y (htr ▸ hy))⟩
  refine RInv.weakenB ⟨hm, h.partialsBig, h.memo, h.alts⟩ (fun y hy => hy.1) (fun y d hy hb1 hb2 => ?_)
    (fun y n _ ha hb1 hb2 => ?_)
  · have hyR : y ∈ R := Classical.byContradiction fun hn => hb2 ⟨hb1, hn⟩
    rw [hav y hyR] at hy; cases hy
    refine ⟨b.body.length + 1, { b with body := b.body ++ [t] }, by simp [emitV, hb], .inr ⟨b.body.length, t, rfl, by simp, by rw [htr]; exact hyR⟩⟩
  · have hyR : y ∈ R := Classical.byContradiction fun hn => hb2 ⟨hb1, hn⟩
    rw [← Bool.not_eq_true, hm_contains_iff, hav y hyR] at ha; simp at ha

theorem stepStmt_skel {rules : SimplifyFn} {skel : SkeletonFn} {cfg : Cfg} {s : Stmt}
    (hsk : skeletonStmt s = true)
    (hk : (operands (mapOperands S.find s.inst)).all st.known = true) :
    ∃ stmts sub st' o, skelStmt skel rules allowed skelOk cfg bi rewriteLimit st
        { s with inst := mapOperands S.find s.inst } = (stmts, sub, st', o) ∧
      stepStmt rules skel allowed skelOk cfg bi (st, S) s =
        (st', sub.foldl (fun m (x : ValueId × ValueId) => m.insert x.1 x.2) S,
          .skel { s with inst := mapOperands S.find s.inst } o stmts) := by
  refine ⟨_, _, _, _, rfl, ?_⟩
  have hk' : (!(operands (mapOperands S.find s.inst)).all st.known) = false := by simp [hk]
  unfold stepStmt
  cases hr : s.results with
  | nil => simp only [hk', Bool.false_eq_true, ↓reduceIte]; rfl
  | cons v rest =>
    cases rest with
    | nil =>
      have hp : isPure (mapOperands S.find s.inst) = false := by
        rw [isPure_mapOperands]; simpa [skeletonStmt, hr] using hsk
      simp only [hp, hk', Bool.false_eq_true, ↓reduceIte]; rfl
    | cons w rest => simp only [hk', Bool.false_eq_true, ↓reduceIte]; rfl

theorem extract_last {stmts : Array Stmt} {pre fin : List Stmt} (h : stmts.toList = pre ++ fin) :
    (stmts.extract 0 (stmts.size - fin.length)).toList = pre ∧ stmts.size = pre.length + fin.length ∧
      ∀ k, stmts[pre.length + k]? = fin[k]? := by
  have hs : stmts.size = pre.length + fin.length := by rw [← Array.length_toList, h, List.length_append]
  refine ⟨?_, hs, fun k => ?_⟩
  · rw [Array.toList_extract, h, hs, Nat.add_sub_cancel]; simp [List.extract]
  · rw [← Array.getElem?_toList, h, List.getElem?_append_right (Nat.le_add_right _ _),
      Nat.add_sub_cancel_left]

theorem TwoInst.emit {idom : Array (Option Nat)} {V : Nat → Option Block} {B : ValueId → Prop}
    {st : SState} {k : Nat} {a : Inst} (h : TwoInst idom V bi k skelOk B st a) (new : List Stmt)
    {k' : Nat} (hk : k ≤ k') : TwoInst idom (emitV V bi new) bi k' skelOk B st a := by
  obtain ⟨hops, h2⟩ := h
  exact ⟨fun y hy => ⟨(hops y hy).1, ((hops y hy).2.emit bi new).le hk⟩, h2⟩

/-- A result-free instruction of a `two` outcome is an output statement. -/
theorem TwoInst.outStmt {idom : Array (Option Nat)} {V : Nat → Option Block} {B : ValueId → Prop}
    {st : SState} {k : Nat} {a : Inst} (h : TwoInst idom V bi k skelOk B st a) :
    OutStmt f allowed skelOk idom V B st bi k { inst := a } := by
  obtain ⟨hops, hrt, -, n, τ, hsk, rfl⟩ := h
  have hpa := not_pure_of_nil hrt
  obtain ⟨hcn, hin⟩ := notCall_of_none (by rw [resultTypes_mapOperands] at hrt; exact hrt)
  refine ⟨fun y hy => ⟨(hops y hy).2, (hops y hy).1⟩,
    ⟨[], resultTypes_none hrt _ _, rfl, fun m x hx => (by simp at hx)⟩,
    fun hp => (by rw [hpa] at hp; cases hp), fun x hx _ => (by simp at hx),
    fun _ r hr => (by simp at hr), (by simp), .inr ⟨n, τ, .inr hsk, rfl, hcn, hin⟩⟩

/-- The replacement `i` of a skeleton statement `s` is an output statement. -/
theorem rep_out (hc : Checked f info) {idom : Array (Option Nat)} {V : Nat → Option Block}
    {B : ValueId → Prop} {st : SState} {j k : Nat} {b0 : Block} {s : Stmt} {σ : ValueId → ValueId}
    {i : Inst} (hb0 : f.blocks[bi]? = some b0) (hs : b0.body[j]? = some s)
    (hsk : skeletonStmt s = true) (hcand : skelCandidate (.inst s.inst) = true)
    (hrep : RepInst idom V bi k skelOk B st (mapOperands σ s.inst) i)
    (hty : ∀ y t, info.types.get? y = some t → st.types.get? y = some t)
    (hleaf : ∀ r ∈ s.results, st.defs.get? r = none) :
    OutStmt f allowed skelOk idom V B st bi k { results := s.results, inst := i } := by
  obtain ⟨hops, hrt, hpi, -, hg⟩ := hrep
  obtain ⟨ts, hts, hlen, htys⟩ := hc.wf.results bi b0 hb0 j s hs
  obtain ⟨-, -, -, ts0, hts0⟩ := cand_facts hcand
  rw [resultTypes_none hts0] at hts
  have hi : i.resultTypes (fun _ => none) (fun _ => none) = some ts := by
    rw [hrt, resultTypes_mapOperands, hts0]; exact hts
  refine ⟨fun y hy => ⟨(hops y hy).2, (hops y hy).1⟩, ⟨ts, resultTypes_none hi _ _, hlen, fun m r hr => ?_⟩,
    fun hp => (by rw [hpi] at hp; cases hp), fun x _ hp => (by rw [hpi] at hp; cases hp),
    fun _ r hr => ⟨hleaf r hr, ?_⟩, (hc.res_nodup hb0 hs :), ?_⟩
  · have h1 := htys m r hr
    have hml : m < ts.length := by rw [hlen]; exact (List.getElem?_eq_some_iff.1 hr).1
    rw [List.getElem?_eq_getElem hml] at h1 ⊢
    exact hty r _ h1
  · rw [hm_contains_iff, hc.res_leaf hb0 hs hsk hr]; rfl
  · rcases hg with ⟨n, τ, hskn, rfl⟩ | ⟨τ, rfl⟩
    · obtain ⟨hcn, hin⟩ := notCall_of_none (by rw [resultTypes_mapOperands] at hi; exact hi)
      exact .inr ⟨n, τ, .inr hskn, rfl, hcn, hin⟩
    · exact .inl ⟨b0, hb0, s, List.mem_of_getElem? hs, τ ∘ σ, mapOperands_comp _ _ _⟩

/-- **A skeleton statement** keeps the invariant. -/
theorem step_skel {rules : SimplifyFn} {skel : SkeletonFn} (hc : Checked f info)
    (hR : SimpRulesProv rules) (hK : SkelRulesProv skel)
    (hsym : ∀ ty gv, allowed (.symbolValue ty gv) = false)
    (h : RunXInv f info allowed skelOk logs bi j lgs st S) {b0 : Block} {s : Stmt}
    (hb0 : f.blocks[bi]? = some b0) (hs : b0.body[j]? = some s) (hsk : skeletonStmt s = true) :
    RunXInv f info allowed skelOk logs bi (j + 1)
      (lgs ++ [(stepStmt rules skel allowed skelOk info.cfg bi (st, S) s).2.2])
      (stepStmt rules skel allowed skelOk info.cfg bi (st, S) s).1
      (stepStmt rules skel allowed skelOk info.cfg bi (st, S) s).2.1 := by
  have hfind : mapOperands S.find s.inst = mapOperands S.step s.inst :=
    mapOperands_congr (fun y _ => h.simp.find_eq y)
  have hplaced : ∀ y ∈ operands (mapOperands S.step s.inst), Placed st (Bad f logs bi j S) y :=
    fun y hy => (h.opsAt hc hb0 hs [] y hy).2
  have hk : (operands (mapOperands S.find s.inst)).all st.known = true := by
    rw [hfind]; exact List.all_eq_true.2 fun y hy => (hplaced y hy).known
  obtain ⟨stmts, sub, st', o, hsk_eq, hstep⟩ := stepStmt_skel (rules := rules) (skel := skel)
    (cfg := info.cfg) (allowed := allowed) (skelOk := skelOk) (bi := bi) hsk hk
  rw [hstep]
  rw [hfind] at hsk_eq ⊢
  have hbV := CurV_bi (lgs := lgs) h.notbi hb0
  have hleaf : ∀ r ∈ s.results, (initAvail f).get? r = some bi :=
    fun r hr => hc.res_leaf hb0 hs hsk hr
  have hRav : ∀ r ∈ s.results, st.avail.get? r = some bi := fun r hr => h.leafAv r bi (hleaf r hr)
  have hRres : ∀ r ∈ s.results, (defMap f).get? r = some (bi, j + 1) :=
    fun r hr => hc.site_res hb0 hs hr
  have hRbad : ∀ r ∈ s.results, Bad f logs bi j S r := fun r hr =>
    .inl ⟨hc.def_le (hRres r hr), not_done_site h.notbi (hRres r hr)⟩
  have hRS : ∀ r ∈ s.results, S.contains r = false := by
    intro r hr
    cases hk' : S.contains r with
    | false => rfl
    | true =>
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 ((hm_contains_iff _ _).1 hk')
      exact absurd (h.substOk r w hw).1 (not_done_site h.notbi (hRres r hr))
  obtain ⟨pre, fin, hstm, hrun, hne, hkp, hres2⟩ := skelStmt_ok (f := f) (B := Bad f logs bi j S)
    (allowed := allowed) (skelOk := skelOk) hR hK rewriteLimit st
    { s with inst := mapOperands S.step s.inst } stmts sub st' o (CurV f logs bi lgs)
    { b0 with body := outsOf lgs } h.rinv hbV hplaced
    (fun r hr => known_iff.2 (.inr ((hm_contains_iff _ _).2 (by rw [hRav r hr]; rfl)))) hsk_eq
  have hRav' : ∀ r ∈ s.results, st'.avail.get? r = some bi :=
    fun r hr => hrun.avail r bi (hRav r hr)
  have hRdefs' : ∀ r ∈ s.results, st'.defs.get? r = none := by
    intro r hr
    cases hd : st'.defs.get? r with
    | none => rfl
    | some n =>
      rcases hrun.fresh r n hd with h1 | h1
      · rw [h.defsLeaf r ((hm_contains_iff _ _).2 (by rw [hleaf r hr]; rfl))] at h1; cases h1
      · exact absurd (hc.def_le (hRres r hr)) (Nat.not_le.2 h1)
  have hRalts : ∀ r ∈ s.results, st'.alts.get? r = none := by
    intro r hr
    rw [hrun.alts]
    cases ha : st.alts.get? r with
    | none => rfl
    | some ms => exact absurd (hRbad r hr) (h.altsNB r ms ha)
  have hpreNew : ∀ k t, pre[k]? = some t → NewOk info.cfg.idom (emitV (CurV f logs bi lgs) bi pre) bi
      ((outsOf lgs).length + k) allowed (Bad f logs bi j S) st' t := by
    intro k t hk'
    rcases hrun.stmts _ hbV k t hk' with h1 | ⟨h1, -⟩
    · simpa using h1
    · exact absurd h1 (hne t (List.mem_of_getElem? hk'))
  have hdt := hrun.inv.m.defsTy
  have hinsPre : ∀ t ∈ pre, insOk t = true := by
    intro t ht
    obtain ⟨k, hk'⟩ := List.mem_iff_getElem?.1 ht
    obtain ⟨r, n', rfl, hd, -, -, ⟨n, τ, hal, rfl⟩, -⟩ := hpreNew k _ hk'
    exact insOk_of hal hsym (hdt r _ hd).1
  have hops1 : ∀ y ∈ operands s.inst, S.contains y = true ∨ ¬ Bad f logs bi j S y :=
    fun y hy => (h.ops hc hb0 hs hy).1
  have hpt : isPure s.inst = true →
      pureTyped (fun y => st'.types.get? y) f (mapOperands S.step s.inst) = true := by
    intro hp
    refine pureTyped_grow (by rw [isPure_mapOperands]; exact hp) ?_ hrun.types
    rw [pureTyped_mapOperands, ← hc.wf.pure bi b0 hb0 j s hs hp]
    exact pureTyped_congr (fun y hy => (h.ops hc hb0 hs hy).2.2.2) rfl rfl
  have hnode : ∀ x, s.results = [x] → isPure s.inst = true → False := by
    intro x hx hp; simp [skeletonStmt, hx, hp] at hsk
  have hRplaced : ∀ (B' : ValueId → Prop), (∀ r ∈ s.results, ¬ B' r) →
      ∀ r ∈ s.results, Placed st' B' r := by
    intro B' hB' r hr
    exact Placed.mk (hB' r hr) (known_iff.2 (.inr ((hm_contains_iff _ _).2 (by rw [hRav' r hr]; rfl))))
      (fun n hn => by rw [hRdefs' r hr] at hn; cases hn)
      (fun ms hms => by rw [hRalts r hr] at hms; cases hms)
  have hnd : ∀ y d k, DefAt (emitV (CurV f logs bi lgs) bi pre) y d k → ¬ Bad f logs bi j S y := by
    intro y d k hy
    rcases hy.of_emit with hy | ⟨b, -, -, m, t, -, ht, hyt⟩
    · exact h.defNB y d k hy
    · obtain ⟨r, n', rfl, -, -, hrb, -⟩ := hpreNew m t ht
      simp only [List.mem_singleton] at hyt; subst hyt; exact hrb
  have hbpre : emitV (CurV f logs bi lgs) bi pre bi = some { b0 with body := outsOf lgs ++ pre } := by
    simp [emitV, hbV]
  have hcand : ∀ (hcd : skelCandidate (.inst (mapOperands S.step s.inst)) = true),
      notCall s.inst = true ∧ notSym s.inst = true ∧ isCallInd s.inst = false ∧
        ∃ ts, s.inst.resultTypes (fun _ => none) (fun _ => none) = some ts := by
    intro hcd; rw [skelCandidate_map] at hcd; exact cand_facts hcd
  have hpreOut : ∀ (B' : ValueId → Prop), (∀ y, B' y → Bad f logs bi j S y) → ∀ (fin' : List Stmt) k t,
      pre[k]? = some t → OutStmt f allowed skelOk info.cfg.idom
        (emitV (CurV f logs bi lgs) bi (pre ++ fin')) B' st' bi ((outsOf lgs).length + k) t := by
    intro B' hB' fin' k t hk'
    have h1 := (hpreNew k t hk').mono' (more := fin') (fun _ _ h _ => h) (fun _ _ h => h) (fun _ h => h)
    rw [emitV_append] at h1
    exact (h1.weakenB hB').outStmt hdt
  rcases o with _ | _ | v' | i | ⟨a, c⟩
  · -- kept
    obtain ⟨rfl, rfl⟩ := hres2
    have hpre : pre = [] := hkp rfl
    subst hpre
    have hstms : stmts = #[{ s with inst := mapOperands S.step s.inst }] :=
      array_eq_of_toList (by simpa using hstm)
    subst hstms
    have hBe := bad_kept hc h hb0 hs
    have hinv := hrun.inv
    rw [emitV_nil] at hinv
    have hRI := rinv_kept (t := { s with inst := mapOperands S.step s.inst }) (R := s.results) hinv hbV
      rfl hRav' hRbad (fun y d k hy => hnd y d k (by rw [emitV_nil]; exact hy))
    rw [← hBe] at hRI
    simp only [List.foldl]
    refine step_gen hc h hb0 hs hRI
      (fun y hy => by rw [hBe]; exact (hrun.good y hy).weaken (fun y h => h.1)) hrun.types
      hrun.avail (fun y d hy => (hrun.availNew y d hy).imp id (fun ⟨_, t, ht, _⟩ => by simp at ht))
      hrun.defsKeep (fun y n hy => (hrun.fresh y n hy).imp id .inl)
      (fun x ms hx => .inl (by rw [← hrun.alts]; exact hx)) (fun _ _ h => h) (fun _ _ h => .inl h)
      (fun k t hk' => ?_) (fun t ht y hy => ?_) ?_ (fun r hr _ => ⟨hRplaced _ (fun r hr h2 => by
        rw [hBe] at h2; exact h2.2 hr) r hr, hRav' r hr⟩) (fun _ => ⟨_, rfl⟩)
    · change [{ s with inst := mapOperands S.step s.inst }][k]? = some t at hk'
      rcases k with _ | k
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at hk'
        subst hk'
        refine src_out hc hb0 hs (fun y hy => ?_) (fun y t hy => hrun.types y t (h.srcTy y t hy)) hpt
          (fun x hx hp => (hnode x hx hp).elim) (fun _ r hr => hRdefs' r hr)
        obtain ⟨e1, e2⟩ := h.opsAt hc hb0 hs [{ s with inst := mapOperands S.step s.inst }] y hy
        exact ⟨e1, by rw [hBe]; exact (hrun.good y e2).weaken (fun y h => h.1)⟩
      · simp at hk'
    · change t ∈ [{ s with inst := mapOperands S.step s.inst }] at ht
      rw [List.mem_singleton] at ht
      subst ht
      rw [hBe]; exact fun h2 => h2.2 hy
    · refine ⟨fun y hy => (hops1 y hy).imp id (fun hnb => by rw [hBe]; exact fun h2 => hnb h2.1),
        rfl, hsk, rfl, hRplaced _ (fun r hr h2 => by rw [hBe] at h2; exact h2.2 hr)⟩
  · -- removed
    obtain ⟨rfl, rfl, hres0, hcd⟩ := hres2
    have hres0' : s.results = [] := hres0
    have hstm' : stmts.toList = pre := by simpa using hstm
    have hBe : Bad f logs bi (j + 1) S = Bad f logs bi j S :=
      bad_gone hc h hb0 hs (fun y => by simp [hres0'])
    obtain ⟨hcn, hcs, hci, -⟩ := hcand hcd
    simp only [List.foldl]
    have hinv := hrun.inv
    rw [← hstm', ← hBe] at hinv
    refine step_gen hc h hb0 hs hinv
      (fun y hy => by rw [hBe]; exact hrun.good y hy) hrun.types hrun.avail
      (fun y d hy => (hrun.availNew y d hy).imp id (fun ⟨hd, t, ht, hyt⟩ => ⟨hd, t, by
        simp only [StmtLog.out]; rw [hstm']; exact ht, hyt⟩))
      hrun.defsKeep (fun y n hy => (hrun.fresh y n hy).imp id .inl)
      (fun x ms hx => .inl (by rw [← hrun.alts]; exact hx)) (fun _ _ h => h) (fun _ _ h => .inl h)
      (fun k t hk' => ?_) (fun t ht y hy => ?_) ?_ (fun r hr _ => by rw [hres0'] at hr; cases hr)
      (fun hc' => by rw [hci] at hc'; cases hc')
    · change stmts.toList[k]? = some t at hk'
      change OutStmt f allowed skelOk _ (emitV _ bi stmts.toList) _ _ _ _ _
      rw [hstm'] at hk' ⊢
      have := hpreOut (Bad f logs bi j S) (fun _ h => h) [] k t hk'
      rw [List.append_nil] at this
      rw [hBe]; exact this
    · change t ∈ stmts.toList at ht
      rw [hstm'] at ht
      obtain ⟨k, hk'⟩ := List.mem_iff_getElem?.1 ht
      obtain ⟨r, n', rfl, -, -, hrb, -⟩ := hpreNew k _ hk'
      simp only [List.mem_singleton] at hy; subst hy; rw [hBe]; exact hrb
    · refine ⟨fun y hy => (hops1 y hy).imp id (fun hnb => by rw [hBe]; exact hnb), rfl, hsk,
        hcn, hcs, hres0', fun t ht => hinsPre t (by rw [← hstm']; exact ht)⟩
  · -- removed, its result renamed
    obtain ⟨rfl, hcd, r, hr, rfl, hpv, havv, htv⟩ := hres2
    have hr' : s.results = [r] := hr
    have hrm : r ∈ s.results := by rw [hr']; simp
    have hstm' : stmts.toList = pre := by simpa using hstm
    have hSv : ∀ y, (S.insert r v').contains y = true ↔ S.contains y = true ∨ y ∈ s.results := by
      intro y; rw [hm_contains_insert', hr', List.mem_singleton]
      constructor
      · rintro (h1 | h1)
        · exact .inr h1.symm
        · exact .inl h1
      · rintro (h1 | h1)
        · exact .inr h1
        · exact .inl h1.symm
    have hBe : Bad f logs bi (j + 1) (S.insert r v') = Bad f logs bi j S := bad_gone hc h hb0 hs hSv
    obtain ⟨hcn, hcs, hci, -⟩ := hcand hcd
    simp only [List.foldl]
    have hinv := hrun.inv
    rw [← hstm', ← hBe] at hinv
    have hstep_eq : ∀ y ∈ operands s.inst, Subst.step (S.insert r v') y = S.step y := by
      intro y hy
      have hyr : ¬ r = y := by
        rintro rfl
        rcases hops1 _ hy with h1 | h1
        · rw [hRS r hrm] at h1; cases h1
        · exact h1 (hRbad r hrm)
      simp only [Subst.step, hm_get?_insert, hyr, ite_false]
    refine step_gen hc h hb0 hs hinv
      (fun y hy => by rw [hBe]; exact hrun.good y hy) hrun.types hrun.avail
      (fun y d hy => (hrun.availNew y d hy).imp id (fun ⟨hd, t, ht, hyt⟩ => ⟨hd, t, by
        simp only [StmtLog.out]; rw [hstm']; exact ht, hyt⟩))
      hrun.defsKeep (fun y n hy => (hrun.fresh y n hy).imp id .inl)
      (fun x ms hx => .inl (by rw [← hrun.alts]; exact hx)) (fun y w hy => ?_) (fun y w hy => ?_)
      (fun k t hk' => ?_) (fun t ht y hy => ?_) ?_ (fun r1 hr1 hk1 => ?_)
      (fun hc' => by rw [hci] at hc'; cases hc')
    · have hyr : ¬ r = y := by
        rintro rfl
        have h3 := (hm_contains_iff S r).2 (by rw [hy]; rfl)
        rw [hRS r hrm] at h3; cases h3
      simp only [hm_get?_insert, hyr, ite_false]; exact hy
    · rw [hm_get?_insert] at hy
      split at hy
      · rename_i hry
        cases hy; subst hry
        refine .inr ⟨hrm, by rw [hBe]; exact hpv, ?_, htv⟩
        change AvailHere _ (emitV _ bi stmts.toList) _ _
        rw [hstm']
        exact havv.here
      · exact .inl hy
    · change stmts.toList[k]? = some t at hk'
      change OutStmt f allowed skelOk _ (emitV _ bi stmts.toList) _ _ _ _ _
      rw [hstm'] at hk' ⊢
      have := hpreOut (Bad f logs bi j S) (fun _ h => h) [] k t hk'
      rw [List.append_nil] at this
      rw [hBe]; exact this
    · change t ∈ stmts.toList at ht
      rw [hstm'] at ht
      obtain ⟨k, hk'⟩ := List.mem_iff_getElem?.1 ht
      obtain ⟨r2, n', rfl, -, -, hrb, -⟩ := hpreNew k _ hk'
      simp only [List.mem_singleton] at hy; subst hy; rw [hBe]; exact hrb
    · refine ⟨fun y hy => (hops1 y hy).imp (fun h1 => (hSv y).2 (.inl h1))
        (fun hnb => by rw [hBe]; exact hnb), ?_, hsk, hcn, hcs,
        fun t ht => hinsPre t (by rw [← hstm']; exact ht), ?_, r, hr', by simp⟩
      · simp only [renStmt]; rw [mapOperands_congr hstep_eq]
      · have hsz : stmts.size = pre.length := by rw [← Array.length_toList, hstm']
        change AvailAt _ (emitV _ bi stmts.toList) _ _ _
        rw [hsz, hstm']; exact havv
    · exact absurd ((hSv r1).2 (.inr hr1)) (by rw [hk1]; simp)
  · -- replaced by `i`
    obtain ⟨rfl, rfl, hcd, hrep⟩ := hres2
    obtain ⟨hcn, hcs, hci, ts0, hts0⟩ := hcand hcd
    have hBe := bad_kept hc h hb0 hs
    obtain ⟨hext, hsz, hlast⟩ := extract_last hstm
    have hRI := rinv_kept (t := { results := s.results, inst := i }) (R := s.results) hrun.inv hbpre
      rfl hRav' hRbad hnd
    rw [← hBe, emitV_append] at hRI
    obtain ⟨hrops, hrt, hrpi, hrsym, hrg⟩ := hrep
    have hi : i.resultTypes (fun _ => none) (fun _ => none) = some ts0 := by
      rw [hrt, resultTypes_mapOperands]; exact hts0
    simp only [List.foldl]
    refine step_gen hc h hb0 hs (by
        change RInv f (emitV _ bi stmts.toList) _ _ _ _; rw [hstm]; exact hRI)
      (fun y hy => by rw [hBe]; exact (hrun.good y hy).weaken (fun y h => h.1)) hrun.types
      hrun.avail
      (fun y d hy => (hrun.availNew y d hy).imp id (fun ⟨hd, t, ht, hyt⟩ => ⟨hd, t, by
        change t ∈ stmts.toList; rw [hstm]; exact List.mem_append_left _ ht, hyt⟩))
      hrun.defsKeep (fun y n hy => (hrun.fresh y n hy).imp id .inl)
      (fun x ms hx => .inl (by rw [← hrun.alts]; exact hx)) (fun _ _ h => h) (fun _ _ h => .inl h)
      (fun k t hk' => ?_) (fun t ht y hy => ?_) ?_
      (fun r hr _ => ⟨hRplaced _ (fun r hr h2 => by rw [hBe] at h2; exact h2.2 hr) r hr, hRav' r hr⟩)
      (fun hc' => by rw [hci] at hc'; cases hc')
    · change stmts.toList[k]? = some t at hk'
      change OutStmt f allowed skelOk _ (emitV _ bi stmts.toList) _ _ _ _ _
      rw [hstm] at hk' ⊢
      rw [hBe]
      rcases Nat.lt_or_ge k pre.length with hkl | hkl
      · rw [List.getElem?_append_left hkl] at hk'
        exact hpreOut _ (fun y h => h.1) _ k t hk'
      · rw [List.getElem?_append_right hkl] at hk'
        obtain ⟨m, rfl⟩ : ∃ m, k = pre.length + m := ⟨k - pre.length, by omega⟩
        rw [Nat.add_sub_cancel_left] at hk'
        rcases m with _ | m
        · simp only [List.getElem?_cons_zero, Option.some.injEq] at hk'
          subst hk'
          refine rep_out hc hb0 hs hsk (by rw [← skelCandidate_map S.step]; exact hcd)
            ⟨fun y hy => ⟨((hrops y hy).1).weaken (fun y h => h.1), ?_⟩, hrt, hrpi, hrsym, hrg⟩
            (fun y t hy => hrun.types y t (h.srcTy y t hy)) hRdefs'
          have := ((hrops y hy).2).emit bi [{ results := s.results, inst := i }]
          rw [emitV_append] at this
          simpa using this
        · simp at hk'
    · change t ∈ stmts.toList at ht
      rw [hstm] at ht
      rw [hBe]
      rcases List.mem_append.1 ht with ht | ht
      · obtain ⟨k, hk'⟩ := List.mem_iff_getElem?.1 ht
        obtain ⟨r, n', rfl, -, -, hrb, -⟩ := hpreNew k _ hk'
        simp only [List.mem_singleton] at hy; subst hy; exact fun h2 => hrb h2.1
      · rw [List.mem_singleton] at ht; subst ht
        exact fun h2 => h2.2 hy
    · refine ⟨fun y hy => (hops1 y hy).imp id (fun hnb => by rw [hBe]; exact fun h2 => hnb h2.1),
        rfl, hsk, hcn, hcs, hRplaced _ (fun r hr h2 => by rw [hBe] at h2; exact h2.2 hr),
        fun y hy => by rw [hBe]; exact ((hrops y hy).1).weaken (fun y h => h.1), ?_, ?_, ?_,
        (notCall_of_none hi).1, hrsym⟩
      · simp [hsz]
      · intro t ht
        simp only [List.length_singleton] at hext
        rw [hext] at ht
        exact hinsPre t ht
      · have := hlast 0
        simp only [List.length_singleton] at hsz
        rw [hsz, Nat.add_sub_cancel]
        simpa using this
  · -- replaced by two result-free instructions
    obtain ⟨rfl, rfl, hres0, hcd, hta, htc⟩ := hres2
    have hres0' : s.results = [] := hres0
    obtain ⟨hcn, hcs, hci, -⟩ := hcand hcd
    have hBe : Bad f logs bi (j + 1) S = Bad f logs bi j S :=
      bad_gone hc h hb0 hs (fun y => by simp [hres0'])
    obtain ⟨hext, hsz, hlast⟩ := extract_last hstm
    have hRI : RInv f (emitV (CurV f logs bi lgs) bi (pre ++ [{ inst := a }, { inst := c }]))
        (Bad f logs bi j S) (fun _ => False) (fun _ => False) st' := by
      have h1 := hrun.inv
      have h2 := ((h1.m.noResult (bi := bi) (s := { inst := a }) rfl).noResult (bi := bi)
        (s := { inst := c }) rfl)
      rw [emitV_append, emitV_append] at h2
      exact ⟨by simpa using h2, h1.partialsBig, h1.memo, h1.alts⟩
    simp only [List.foldl]
    refine step_gen hc h hb0 hs (by
        change RInv f (emitV _ bi stmts.toList) _ _ _ _; rw [hstm, hBe]; exact hRI)
      (fun y hy => by rw [hBe]; exact hrun.good y hy) hrun.types hrun.avail
      (fun y d hy => (hrun.availNew y d hy).imp id (fun ⟨hd, t, ht, hyt⟩ => ⟨hd, t, by
        change t ∈ stmts.toList; rw [hstm]; exact List.mem_append_left _ ht, hyt⟩))
      hrun.defsKeep (fun y n hy => (hrun.fresh y n hy).imp id .inl)
      (fun x ms hx => .inl (by rw [← hrun.alts]; exact hx)) (fun _ _ h => h) (fun _ _ h => .inl h)
      (fun k t hk' => ?_) (fun t ht y hy => ?_) ?_ (fun r hr _ => by rw [hres0'] at hr; cases hr)
      (fun hc' => by rw [hci] at hc'; cases hc')
    · change stmts.toList[k]? = some t at hk'
      change OutStmt f allowed skelOk _ (emitV _ bi stmts.toList) _ _ _ _ _
      rw [hstm] at hk' ⊢
      rw [hBe]
      rcases Nat.lt_or_ge k pre.length with hkl | hkl
      · rw [List.getElem?_append_left hkl] at hk'
        exact hpreOut _ (fun y h => h) _ k t hk'
      · rw [List.getElem?_append_right hkl] at hk'
        obtain ⟨m, rfl⟩ : ∃ m, k = pre.length + m := ⟨k - pre.length, by omega⟩
        rw [Nat.add_sub_cancel_left] at hk'
        rcases m with _ | _ | m
        · simp only [List.getElem?_cons_zero, Option.some.injEq] at hk'
          subst hk'
          have := (hta.emit [{ inst := a }, { inst := c }] (Nat.le_refl _)).outStmt (f := f)
            (allowed := allowed)
          rw [emitV_append] at this
          simpa [Nat.add_assoc] using this
        · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hk'
          subst hk'
          have := (htc.emit [{ inst := a }, { inst := c }] (Nat.le_succ _)).outStmt (f := f)
            (allowed := allowed)
          rw [emitV_append] at this
          simpa [Nat.add_assoc] using this
        · simp at hk'
    · change t ∈ stmts.toList at ht
      rw [hstm] at ht
      rw [hBe]
      rcases List.mem_append.1 ht with ht | ht
      · obtain ⟨k, hk'⟩ := List.mem_iff_getElem?.1 ht
        obtain ⟨r, n', rfl, -, -, hrb, -⟩ := hpreNew k _ hk'
        simp only [List.mem_singleton] at hy; subst hy; exact hrb
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl <;> simp at hy
    · obtain ⟨hopa, hrta, hsa, -⟩ := hta
      obtain ⟨hopc, hrtc, hsc, -⟩ := htc
      refine ⟨fun y hy => (hops1 y hy).imp id (fun hnb => by rw [hBe]; exact hnb), rfl, hsk, hcn,
        hcs, fun y hy => ?_, hres0', ?_, ?_, ?_, ?_, (notCall_of_none hrta).1,
        (notCall_of_none hrtc).1, hsa, hsc⟩
      · rw [hBe]
        rcases List.mem_append.1 hy with hy | hy
        · exact (hopa y hy).1
        · exact (hopc y hy).1
      · simp [hsz]
      · intro t ht
        simp only [List.length_cons, List.length_nil] at hext
        rw [hext] at ht
        exact hinsPre t ht
      · have := hlast 0
        simp only [List.length_cons, List.length_nil] at hsz
        rw [hsz, show pre.length + (0 + 1 + 1) - 2 = pre.length + 0 by omega]
        simpa using this
      · have := hlast 1
        simp only [List.length_cons, List.length_nil] at hsz
        rw [hsz, show pre.length + (0 + 1 + 1) - 1 = pre.length + 1 by omega]
        simpa using this

end SkelStep

/-! ## The statements of a block -/

section Body

variable {f : Function} {info : Info} {allowed skelOk : Inst → Bool}
  {logs : Array (Option BlockLog)} {bi : Nat}

/-- **One statement** keeps the invariant. -/
theorem step_stmt {rules : SimplifyFn} {skel : SkeletonFn} (hc : Checked f info)
    (hR : SimpRulesProv rules) (hK : SkelRulesProv skel)
    (hsym : ∀ ty gv, allowed (.symbolValue ty gv) = false) {j : Nat} {lgs : List StmtLog}
    {st : SState} {S : Subst} (h : RunXInv f info allowed skelOk logs bi j lgs st S) {b0 : Block}
    {s : Stmt} (hb0 : f.blocks[bi]? = some b0) (hs : b0.body[j]? = some s) :
    RunXInv f info allowed skelOk logs bi (j + 1)
      (lgs ++ [(stepStmt rules skel allowed skelOk info.cfg bi (st, S) s).2.2])
      (stepStmt rules skel allowed skelOk info.cfg bi (st, S) s).1
      (stepStmt rules skel allowed skelOk info.cfg bi (st, S) s).2.1 := by
  by_cases hsk : skeletonStmt s = true
  · exact step_skel hc hR hK hsym h hb0 hs hsk
  · have h1 : isPure s.inst = true ∧ s.results.length = 1 := by simpa [skeletonStmt] using hsk
    obtain ⟨v, hv⟩ := List.length_eq_one_iff.1 h1.2
    exact step_pure hc hR hsym h hb0 hs hv h1.1

/-- The statements of block `bi` from statement `k` on (the fold of `Opt.stepBlock`). -/
theorem stmts_fold {rules : SimplifyFn} {skel : SkeletonFn} (hc : Checked f info)
    (hR : SimpRulesProv rules) (hK : SkelRulesProv skel)
    (hsym : ∀ ty gv, allowed (.symbolValue ty gv) = false) {b0 : Block}
    (hb0 : f.blocks[bi]? = some b0) :
    ∀ (rest : List Stmt) (k : Nat) (st : SState) (S : Subst) (lgs : Array StmtLog),
      b0.body.drop k = rest → RunXInv f info allowed skelOk logs bi k lgs.toList st S →
      RunXInv f info allowed skelOk logs bi b0.body.length
        (rest.foldl (fun (acc : SState × Subst × Array StmtLog) s =>
          let (st, subst, lg) := stepStmt rules skel allowed skelOk info.cfg bi (acc.1, acc.2.1) s
          (st, subst, acc.2.2.push lg)) (st, S, lgs)).2.2.toList
        (rest.foldl (fun (acc : SState × Subst × Array StmtLog) s =>
          let (st, subst, lg) := stepStmt rules skel allowed skelOk info.cfg bi (acc.1, acc.2.1) s
          (st, subst, acc.2.2.push lg)) (st, S, lgs)).1
        (rest.foldl (fun (acc : SState × Subst × Array StmtLog) s =>
          let (st, subst, lg) := stepStmt rules skel allowed skelOk info.cfg bi (acc.1, acc.2.1) s
          (st, subst, acc.2.2.push lg)) (st, S, lgs)).2.1
  | [], k, st, S, lgs, hd, h => by
    have hk : b0.body.length ≤ k := List.drop_eq_nil_iff.1 hd
    obtain ⟨b1, hb1, hkl, -⟩ := h.cur
    rw [hb0] at hb1; cases hb1
    rw [show k = b0.body.length by omega] at h
    exact h
  | s :: rest, k, st, S, lgs, hd, h => by
    have hs : b0.body[k]? = some s := by
      rw [← List.head?_drop, hd]; rfl
    have h1 := step_stmt hc hR hK hsym h hb0 hs
    have hd' : b0.body.drop (k + 1) = rest := by
      rw [← List.drop_drop, hd]; rfl
    rw [List.foldl_cons]
    dsimp only
    generalize stepStmt rules skel allowed skelOk info.cfg bi (st, S) s = r at h1 ⊢
    obtain ⟨st', S', lg⟩ := r
    dsimp only at h1 ⊢
    refine stmts_fold hc hR hK hsym hb0 rest (k + 1) st' S' (lgs.push lg) hd' ?_
    rw [Array.toList_push]; exact h1

end Body

end Opt
