import FV.Opt.Proof.SimpLoop
import FV.Opt.Proof.DomComplete
import FV.Opt.Proof.CompleteSimpLoop

/-!
# Completeness of simplify: the invariants of the run

Facts of a checked function (definition sites, leaves, typing), and the invariants the run of
`Opt.simplify` keeps:

* `RunCore`: the part of `Opt.SimpInv` that does not mention the current block, with five more facts
  the run needs: output definitions are never bad (`defNB`), e-class keys are never bad
  (`altsNB`), only statement results are renamed (`keysRes`), available fresh values have a node
  (`availBig`), and `call_indirect` statements are kept (`ciDone`, `CIKeep`);
* `RunXInv`: `RunCore` inside block `bi` before its statement `j` (the rest of `SimpInv`);
* `RunBInv`: `RunCore` between two blocks (the current block index `f.blocks.length` is past the last
  block), and the output blocks so far.
-/

namespace Opt

open Clif

/-! ## Facts of a checked function -/

section Facts

variable {f : Function} {info : Info}

theorem Checked.site_res (hc : Checked f info) {d k : Nat} {b : Block} {s : Stmt} {r : ValueId}
    (hb : f.blocks[d]? = some b) (hs : b.body[k]? = some s) (hr : r ∈ s.results) :
    (defMap f).get? r = some (d, k + 1) :=
  hc.wf.sites _ _ (mem_defSites.2 ⟨d, b, hb, .inr ⟨k, s, hs, hr, rfl⟩⟩)

theorem Checked.site_param (hc : Checked f info) {d : Nat} {b : Block} {p : ValueId × Ty}
    (hb : f.blocks[d]? = some b) (hp : p ∈ b.params) : (defMap f).get? p.1 = some (d, 0) :=
  hc.wf.sites _ _ (mem_defSites.2 ⟨d, b, hb, .inl ⟨p, hp, rfl, rfl⟩⟩)

theorem Checked.def_le (hc : Checked f info) {y : ValueId} {s : Nat × Nat}
    (h : (defMap f).get? y = some s) : y ≤ maxValue f := by
  obtain ⟨i, b, hb, ⟨p, hp, rfl, -⟩ | ⟨k, st, hst, hy, -⟩⟩ := mem_defSites.1 (hc.wf.sitesRev y s h)
  · exact le_maxValue (List.mem_of_getElem? hb) (.inl ⟨p, hp, rfl⟩)
  · exact le_maxValue (List.mem_of_getElem? hb) (.inr ⟨st, List.mem_of_getElem? hst, hy⟩)

theorem Checked.def_blk (hc : Checked f info) {y : ValueId} {d t : Nat}
    (h : (defMap f).get? y = some (d, t)) : ∃ b, f.blocks[d]? = some b ∧ t ≤ b.body.length := by
  obtain ⟨i, b, hb, ⟨p, hp, -, he⟩ | ⟨k, st, hst, hy, he⟩⟩ := mem_defSites.1 (hc.wf.sitesRev y _ h)
  · simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he; exact ⟨b, hb, Nat.zero_le _⟩
  · simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    exact ⟨b, hb, (List.getElem?_eq_some_iff.1 hst).1⟩

theorem Checked.def_lt (hc : Checked f info) {y : ValueId} {d t : Nat}
    (h : (defMap f).get? y = some (d, t)) : d < f.blocks.length := by
  obtain ⟨b, hb, -⟩ := hc.def_blk h
  exact (List.getElem?_eq_some_iff.1 hb).1

/-- The statement defining a value at `(d, k + 1)`. -/
theorem Checked.site_stmt (hc : Checked f info) {y : ValueId} {d k : Nat}
    (h : (defMap f).get? y = some (d, k + 1)) :
    ∃ b s, f.blocks[d]? = some b ∧ b.body[k]? = some s ∧ y ∈ s.results := by
  obtain ⟨i, b, hb, ⟨p, hp, -, he⟩ | ⟨k', st, hst, hy, he⟩⟩ := mem_defSites.1 (hc.wf.sitesRev y _ h)
  · cases he
  · simp only [Prod.mk.injEq, Nat.add_right_cancel_iff] at he; obtain ⟨rfl, rfl⟩ := he
    exact ⟨b, st, hb, hst, hy⟩

theorem Checked.leaf_site (hc : Checked f info) {y : ValueId} {d : Nat}
    (h : (initAvail f).get? y = some d) :
    (defMap f).get? y = some (d, 0) ∨ ∃ k b s, f.blocks[d]? = some b ∧ b.body[k]? = some s ∧
      skeletonStmt s = true ∧ y ∈ s.results ∧ (defMap f).get? y = some (d, k + 1) := by
  obtain ⟨b, hb, ⟨p, hp, rfl⟩ | ⟨s, hs, hsk, hy⟩⟩ := mem_leafList.1 ((initAvail_get hc.unique y d).1 h)
  · exact .inl (hc.site_param hb hp)
  · obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hs
    exact .inr ⟨k, b, s, hb, hk, hsk, hy, hc.site_res hb hk hy⟩

theorem Checked.leaf_def (hc : Checked f info) {y : ValueId} {d : Nat}
    (h : (initAvail f).get? y = some d) : ∃ t, (defMap f).get? y = some (d, t) := by
  rcases hc.leaf_site h with h | ⟨k, -, -, -, -, -, -, h⟩
  · exact ⟨0, h⟩
  · exact ⟨k + 1, h⟩

theorem Checked.leaf_le (hc : Checked f info) {y : ValueId} (h : (initAvail f).contains y = true) :
    y ≤ maxValue f := by
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.1 ((hm_contains_iff _ _).1 h)
  obtain ⟨t, ht⟩ := hc.leaf_def hd
  exact hc.def_le ht

/-- A result of a statement that is not a skeleton statement is not a leaf. -/
theorem Checked.not_leaf (hc : Checked f info) {d k : Nat} {b : Block} {s : Stmt} {y : ValueId}
    (hb : f.blocks[d]? = some b) (hs : b.body[k]? = some s) (hy : y ∈ s.results)
    (hsk : skeletonStmt s = false) : (initAvail f).get? y = none := by
  cases h : (initAvail f).get? y with
  | none => rfl
  | some d' =>
    have hy' := hc.site_res hb hs hy
    rcases hc.leaf_site h with h1 | ⟨k', b', s', hb', hs', hsk', -, h1⟩
    · rw [hy'] at h1; cases h1
    · rw [hy'] at h1
      simp only [Option.some.injEq, Prod.mk.injEq, Nat.add_right_cancel_iff] at h1
      obtain ⟨rfl, rfl⟩ := h1
      rw [hb] at hb'; cases hb'; rw [hs] at hs'; cases hs'
      rw [hsk] at hsk'; cases hsk'

theorem Checked.not_leaf' (hc : Checked f info) {d k : Nat} {b : Block} {s : Stmt} {y : ValueId}
    (hb : f.blocks[d]? = some b) (hs : b.body[k]? = some s) (hy : y ∈ s.results)
    (hsk : skeletonStmt s = false) : (initAvail f).contains y = false := by
  cases h : (initAvail f).contains y with
  | false => rfl
  | true =>
    rw [hm_contains_iff, hc.not_leaf hb hs hy hsk] at h; cases h

/-- The results of a statement are distinct. -/
theorem Checked.res_nodup (hc : Checked f info) {d k : Nat} {b : Block} {s : Stmt}
    (hb : f.blocks[d]? = some b) (hs : b.body[k]? = some s) : s.results.Nodup := by
  have hsub : (s.results.map fun r => (r, d, k + 1)).Sublist (defSites f) := by
    unfold defSites
    have hm : (b, d) ∈ f.blocks.zipIdx := List.mem_zipIdx_iff_getElem?.2 hb
    refine List.Sublist.trans ?_ (sublist_flatMap_of_mem _ hm)
    refine List.Sublist.trans ?_ (List.sublist_append_right _ _)
    have hm' : (s, k) ∈ b.body.zipIdx := List.mem_zipIdx_iff_getElem?.2 hs
    exact sublist_flatMap_of_mem (fun (x : Stmt × Nat) => x.1.results.map fun r => (r, d, x.2 + 1)) hm'
  have hu : ((defSites f).map (·.1)).Nodup := hc.unique
  have := (hsub.map (·.1)).nodup hu
  simpa [List.map_map, Function.comp_def] using this

/-- `info.types` only types values of `f`. -/
theorem Checked.types_le (hc : Checked f info) {y : ValueId} {t : Ty}
    (h : info.types.get? y = some t) : y ≤ maxValue f := by
  rw [hc.info_eq] at h
  by_cases hy : y ∈ (defList f).map (·.1)
  · rw [← defSites_map_fst hc.arity, List.mem_map] at hy
    obtain ⟨⟨y', s⟩, hs, rfl⟩ := hy
    exact hc.def_le ((hc.wf.sites _ _ hs))
  · have := ((defsState_get f hc.nodup).2 y hy).1
    simp only [coreInfo] at h
    rw [Std.HashMap.get?_eq_getElem?, this] at h; cases h

/-- The terminator of a block of a checked function types its `br_table` index. -/
theorem Checked.brt (hc : Checked f info) {d : Nat} {b : Block} (hb : f.blocks[d]? = some b) :
    brTableOk info.types b.term := by
  have := (hc.core.2.2.2.2.2 (b, d) (List.mem_zipIdx_iff_getElem?.2 hb)).2.2.2
  rw [hc.info_eq]; exact this

end Facts

/-! ## The invariant of the run -/

/-- `call_indirect` statements are kept by their records. -/
def CIKeep (ss : List Stmt) (lgs : List StmtLog) : Prop :=
  ∀ (i : Nat) (s : Stmt) (lg : StmtLog), ss[i]? = some s → lgs[i]? = some lg →
    isCallInd s.inst = true → ∃ s', lg = StmtLog.skel s' .keep #[s']

/-- The part of `SimpInv` that does not mention the current block, and five more facts (module
doc). -/
structure RunCore (f : Function) (info : Info) (allowed skelOk : Inst → Bool)
    (logs : Array (Option BlockLog)) (bi j : Nat) (lgs : List StmtLog) (st : SState) (S : Subst) :
    Prop where
  rinv : RInv f (CurV f logs bi lgs) (Bad f logs bi j S) (fun _ => False) (fun _ => False) st
  srcTy : ∀ y t, info.types.get? y = some t → st.types.get? y = some t
  leafAv : ∀ y d, (initAvail f).get? y = some d → st.avail.get? y = some d
  availSrc : ∀ y d, st.avail.get? y = some d → y ≤ maxValue f →
    (initAvail f).get? y = some d ∨ ∃ t, (defMap f).get? y = some (d, t) ∧ Done f logs bi j y
  defsSrc : ∀ y n, st.defs.get? y = some n → y ≤ maxValue f → Done f logs bi j y
  defsLeaf : ∀ y, (initAvail f).contains y = true → st.defs.get? y = none
  doneAv : ∀ y, Done f logs bi j y → S.contains y = false →
    Placed st (Bad f logs bi j S) y ∧ ∃ d t, (defMap f).get? y = some (d, t) ∧ st.avail.get? y = some d
  substOk : ∀ y w, S.get? y = some w → Done f logs bi j y ∧ Placed st (Bad f logs bi j S) w ∧
    (∃ d' t', DefAt (CurV f logs bi lgs) w d' t' ∧ ∃ d t, (defMap f).get? y = some (d, t) ∧
      (d' = d ∨ Anc info.cfg.idom d' d)) ∧ st.types.get? w = st.types.get? y
  outs : ∀ d b, CurV f logs bi lgs d = some b →
    (∃ b0, f.blocks[d]? = some b0 ∧ b.params = b0.params ∧ b.id = b0.id) ∧
    ∀ k t, b.body[k]? = some t →
      OutStmt f allowed skelOk info.cfg.idom (CurV f logs bi lgs) (Bad f logs bi j S) st d k t
  done : ∀ d lg, logs[d]? = some (some lg) → ∃ b0 bo, f.blocks[d]? = some b0 ∧
    blockOf f d lg = some bo ∧
    StmtsFact info.cfg.idom (CurV f logs bi lgs) (Bad f logs bi j S) st S d b0.body lg.stmts 0 ∧
    TermLogFact (Bad f logs bi j S) st S b0 lg ∧
    TermOut info info.cfg.idom (CurV f logs bi lgs) (Bad f logs bi j S) st d bo.body.length b0 lg.term'
  size : logs.size = f.blocks.length
  altsNB : ∀ x ms, st.alts.get? x = some ms → ¬ Bad f logs bi j S x
  keysRes : ∀ y, S.contains y = true → ∃ d k, (defMap f).get? y = some (d, k + 1)
  availBig : ∀ x d, st.avail.get? x = some d → maxValue f < x → (st.defs.get? x).isSome
  ciDone : ∀ (d : Nat) (lg : BlockLog) (b0 : Block), logs[d]? = some (some lg) →
    f.blocks[d]? = some b0 → CIKeep b0.body lg.stmts
  defNB : ∀ y d t, DefAt (CurV f logs bi lgs) y d t → ¬ Bad f logs bi j S y

/-- The invariant inside block `bi`, before its statement `j`. -/
structure RunXInv (f : Function) (info : Info) (allowed skelOk : Inst → Bool)
    (logs : Array (Option BlockLog)) (bi j : Nat) (lgs : List StmtLog) (st : SState) (S : Subst) :
    Prop extends RunCore f info allowed skelOk logs bi j lgs st S where
  cur : ∃ b0, f.blocks[bi]? = some b0 ∧ j ≤ b0.body.length ∧
    StmtsFact info.cfg.idom (CurV f logs bi lgs) (Bad f logs bi j S) st S bi (b0.body.take j) lgs 0
  notbi : logs[bi]? = some none
  preds : ∀ d, d ≠ bi → Anc info.cfg.idom d bi → ∃ lg, logs[d]? = some (some lg)
  ciCur : ∀ b0, f.blocks[bi]? = some b0 → CIKeep (b0.body.take j) lgs

/-- The invariant between two blocks: `RunCore` with no current block, and the output blocks. -/
structure RunBInv (f : Function) (info : Info) (allowed skelOk : Inst → Bool) (st : SState)
    (S : Subst) (out : Array Block) (logs : Array (Option BlockLog)) : Prop extends
    RunCore f info allowed skelOk logs f.blocks.length 0 [] st S where
  outSize : out.size = f.blocks.length
  outEq : ∀ d lg, logs[d]? = some (some lg) → out[d]? = blockOf f d lg

section Inv

variable {f : Function} {info : Info} {allowed skelOk : Inst → Bool}
  {logs : Array (Option BlockLog)} {bi j : Nat} {lgs : List StmtLog} {st : SState} {S : Subst}

theorem RunXInv.simp (h : RunXInv f info allowed skelOk logs bi j lgs st S) :
    SimpInv f info allowed skelOk logs bi j lgs st S :=
  ⟨h.rinv, h.srcTy, h.leafAv, h.availSrc, h.defsSrc, h.defsLeaf, h.doneAv, h.substOk, h.outs, h.done,
   h.cur, h.size, h.notbi, h.preds⟩

theorem CurV_append (f : Function) (logs : Array (Option BlockLog)) (bi : Nat) (lgs : List StmtLog)
    (lg : StmtLog) : CurV f logs bi (lgs ++ [lg]) = emitV (CurV f logs bi lgs) bi lg.out.toList := by
  simp only [CurV, outsOf, List.flatMap_append, emitV_append]
  simp

theorem CurV_bi {b0 : Block} (hl : logs[bi]? = some none) (hb : f.blocks[bi]? = some b0) :
    CurV f logs bi lgs bi = some { b0 with body := outsOf lgs } := by
  simp [CurV, emitV, V0, hl, hb]

theorem CurV_ne {d : Nat} (hd : d ≠ bi) : CurV f logs bi lgs d = V0 f logs bi d := by
  simp [CurV, emitV, hd]

theorem Done.succ {y : ValueId} (h : Done f logs bi j y) : Done f logs bi (j + 1) y := by
  obtain ⟨d, t, hd, h | ⟨rfl, ht⟩⟩ := h
  · exact ⟨d, t, hd, .inl h⟩
  · exact ⟨d, t, hd, .inr ⟨rfl, Nat.le_succ_of_le ht⟩⟩

theorem Done.cases_succ {y : ValueId} (h : Done f logs bi (j + 1) y) :
    Done f logs bi j y ∨ (defMap f).get? y = some (bi, j + 1) := by
  obtain ⟨d, t, hd, h | ⟨rfl, ht⟩⟩ := h
  · exact .inl ⟨d, t, hd, .inl h⟩
  · rcases Nat.lt_or_ge t (j + 1) with h | h
    · exact .inl ⟨d, t, hd, .inr ⟨rfl, by omega⟩⟩
    · rw [show t = j + 1 by omega] at hd; exact .inr hd

theorem not_done_site (hn : logs[bi]? = some none) {y : ValueId}
    (hy : (defMap f).get? y = some (bi, j + 1)) : ¬ Done f logs bi j y := by
  rintro ⟨d, t, hd, ⟨lg, hlg⟩ | ⟨rfl, ht⟩⟩
  · rw [hy] at hd; cases hd; rw [hn] at hlg; cases hlg
  · rw [hy] at hd; cases hd; omega

theorem done_site {y : ValueId} (hy : (defMap f).get? y = some (bi, j + 1)) :
    Done f logs bi (j + 1) y :=
  ⟨bi, j + 1, hy, .inr ⟨rfl, Nat.le_refl _⟩⟩

theorem StmtsFact.length {idom : Array (Option Nat)} {V : Nat → Option Block} {B : ValueId → Prop}
    {d : Nat} : ∀ {ss : List Stmt} {lgs : List StmtLog} {k : Nat},
      StmtsFact idom V B st S d ss lgs k → ss.length = lgs.length
  | [], [], _, _ => rfl
  | _ :: _, _ :: _, _, ⟨_, h⟩ => by simp [h.length]
  | [], _ :: _, _, h => h.elim
  | _ :: _, [], _, h => h.elim

theorem outsOf_cons (lg : StmtLog) (lgs : List StmtLog) :
    (outsOf (lg :: lgs)).length = lg.out.size + (outsOf lgs).length := by
  simp [outsOf]

theorem StmtsFact.snoc {idom : Array (Option Nat)} {V : Nat → Option Block} {B : ValueId → Prop}
    {d : Nat} {s : Stmt} {lg : StmtLog} :
    ∀ {ss : List Stmt} {lgs : List StmtLog} {k : Nat}, StmtsFact idom V B st S d ss lgs k →
      SLogFact idom V B st S d s (k + (outsOf lgs).length) lg →
      StmtsFact idom V B st S d (ss ++ [s]) (lgs ++ [lg]) k
  | [], [], k, _, h2 => ⟨by simpa [outsOf] using h2, trivial⟩
  | _ :: _, lg1 :: lgs1, k, ⟨h1, h⟩, h2 =>
    ⟨h1, StmtsFact.snoc h (by rw [outsOf_cons] at h2; rwa [Nat.add_assoc])⟩
  | [], _ :: _, _, h, _ => h.elim
  | _ :: _, [], _, h, _ => h.elim

theorem CIKeep.snoc {ss : List Stmt} {lgs : List StmtLog} {s : Stmt} {lg : StmtLog}
    (h : CIKeep ss lgs) (hl : ss.length = lgs.length)
    (hs : isCallInd s.inst = true → ∃ s', lg = .skel s' .keep #[s']) :
    CIKeep (ss ++ [s]) (lgs ++ [lg]) := by
  intro i s1 lg1 h1 h2 h3
  rcases Nat.lt_or_ge i ss.length with hi | hi
  · rw [List.getElem?_append_left hi] at h1
    rw [List.getElem?_append_left (by omega)] at h2
    exact h i s1 lg1 h1 h2 h3
  · rw [List.getElem?_append_right hi] at h1
    rw [List.getElem?_append_right (by omega)] at h2
    have hi' : i - ss.length = 0 := by
      rcases Nat.lt_or_ge (i - ss.length) 1 with h | h
      · omega
      · rw [List.getElem?_eq_none (by simp; omega)] at h1; cases h1
    rw [hi'] at h1; rw [hl] at hi'; rw [hi'] at h2
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h1 h2
    subst h1; subst h2; exact hs h3

end Inv

end Opt
