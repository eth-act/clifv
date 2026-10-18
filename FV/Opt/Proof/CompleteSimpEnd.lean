import FV.Opt.Proof.CompleteSimpStep
import FV.Opt.Proof.CompleteSimpStart

/-!
# Completeness of simplify: the end of a block

`endBlock` is the end of `Opt.stepBlock` once the statements are processed (`stepBlock_eq`): the
terminator goes through the skeleton rules, and the block and its record are stored. `block_end`:
from the invariant inside block `bi` after its last statement (`RunXInv`), this gives the invariant
between blocks (`RunBInv`). The renamed terminator's operands are placeable and available
(`SimpInv.renOp`), so the skeleton rules run (`skelTerm_ok`); the emitted statements are output
statements, the record satisfies `TermLogFact`/`TermOut`; the new view is the old one with the
emitted statements (only the stored terminator differs, which no fact reads), and the bad values do
not change (every definition of `bi` is before its terminator).
-/

namespace Opt

open Clif

/-- The end of `stepBlock` after the statements of block `b` (index `bi`). -/
def endBlock (rules : SimplifyFn) (skel : SkeletonFn) (allowed skelOk : Inst → Bool) (cfg : Cfg)
    (b : Block) (bi : Nat) (out : Array Block) (logs : Array (Option BlockLog))
    (acc : SState × Subst × Array StmtLog) : SState × Subst × Array Block × Array (Option BlockLog) :=
  let (st, subst, lgs) := acc
  let t := mapTerm subst.find b.term
  let (extra, term, st, changed) :=
    if (termOperands t).all st.known then skelTerm skel rules allowed skelOk cfg bi rewriteLimit st t
    else (#[], t, st, false)
  let body := lgs.foldl (fun acc lg => acc ++ lg.out) #[] ++ extra
  (st, subst, out.set! bi { b with body := body.toList, term },
   logs.set! bi (some { stmts := lgs.toList, term := t, extra, term' := term, changed }))

theorem stepBlock_eq (rules : SimplifyFn) (skel : SkeletonFn) (allowed skelOk : Inst → Bool)
    (cfg : Cfg) (blocks : Array Block) (st : SState) (S : Subst) (out : Array Block)
    (logs : Array (Option BlockLog)) (bi : Nat) :
    stepBlock rules skel allowed skelOk cfg blocks (st, S, out, logs) bi =
      endBlock rules skel allowed skelOk cfg blocks[bi]! bi out logs
        (blocks[bi]!.body.foldl (fun (acc : SState × Subst × Array StmtLog) s =>
          let (st, subst, lg) := stepStmt rules skel allowed skelOk cfg bi (acc.1, acc.2.1) s
          (st, subst, acc.2.2.push lg)) (st, S, #[])) := by
  simp only [stepBlock, endBlock]

theorem MInv.view {f : Function} {V V' : Nat → Option Block} {B : ValueId → Prop} {st : SState}
    (h : MInv f V B st) (h1 : VExt V V') (h2 : VExt V' V) : MInv f V' B st :=
  { h with
    availDef := fun x d hx hb => by obtain ⟨t, ht⟩ := h.availDef x d hx hb; exact ⟨t, ht.ext h1⟩
    defAvail := fun x d t hx => h.defAvail x d t (hx.ext h2)
    uniq := fun x d t d' t' a c => h.uniq x d t d' t' (a.ext h2) (c.ext h2) }

theorem RInv.view {f : Function} {V V' : Nat → Option Block} {B X : ValueId → Prop}
    {XN : Inst → Prop} {st : SState} (h : RInv f V B X XN st) (h1 : VExt V V') (h2 : VExt V' V) :
    RInv f V' B X XN st :=
  ⟨h.m.view h1 h2, h.noPartial, h.memo, h.alts⟩

theorem foldl_out_toList (l : List StmtLog) (acc : Array Stmt) :
    (l.foldl (fun acc lg => acc ++ lg.out) acc).toList = acc.toList ++ outsOf l := by
  induction l generalizing acc with
  | nil => simp [outsOf]
  | cons lg l ih => simp [List.foldl_cons, ih, outsOf, List.append_assoc]

theorem termSuccs_branch {t : Terminator} (h : isBranch t = true) :
    termSuccs t = (termCalls t).map (·.block) := by
  cases t <;> simp_all [isBranch, termSuccs, termCalls]

theorem isBranch_of_cand {t : Terminator} (h : skelCandidate (.term t) = true) : isBranch t = true := by
  cases t <;> simp_all [skelCandidate, isBranch]

theorem trapOk_of {s : Stmt} (hr : s.results = []) (ht : isTrapLike s.inst = true) : trapOk s = true := by
  obtain ⟨res, i⟩ := s
  simp only at hr ht
  subst hr
  cases i <;> simp_all [trapOk, isTrapLike]

theorem setB_ne {α : Type} (a : Array α) (x : α) {i d : Nat} (h : d ≠ i) :
    (a.set! i x)[d]? = a[d]? := by
  simp [Array.set!_eq_setIfInBounds, Ne.symm h]

theorem setB_eq {α : Type} (a : Array α) (x : α) {i : Nat} (h : i < a.size) :
    (a.set! i x)[i]? = some x := by
  simp [Array.set!_eq_setIfInBounds, h]

section End

variable {f : Function} {info : Info} {allowed skelOk : Inst → Bool} {rules : SimplifyFn}
  {skel : SkeletonFn} {logs : Array (Option BlockLog)} {bi : Nat} {st : SState} {S : Subst}
  {out : Array Block}

/-- **The end of a block** (module doc). -/
theorem block_end (hc : Checked f info) (hR : SimpRulesOk rules) (hK : SkelRulesOk skel)
    (hsym : ∀ ty gv, allowed (.symbolValue ty gv) = false) {b0 : Block}
    (hb0 : f.blocks[bi]? = some b0) {lgs : Array StmtLog}
    (h : RunXInv f info allowed skelOk logs bi b0.body.length lgs.toList st S)
    (hos : out.size = f.blocks.length)
    (hoe : ∀ d lg, logs[d]? = some (some lg) → out[d]? = blockOf f d lg) :
    RunBInv f info allowed skelOk
      (endBlock rules skel allowed skelOk info.cfg b0 bi out logs (st, S, lgs)).1
      (endBlock rules skel allowed skelOk info.cfg b0 bi out logs (st, S, lgs)).2.1
      (endBlock rules skel allowed skelOk info.cfg b0 bi out logs (st, S, lgs)).2.2.1
      (endBlock rules skel allowed skelOk info.cfg b0 bi out logs (st, S, lgs)).2.2.2 := by
  have hn := h.notbi
  have hbi : bi < f.blocks.length := (List.getElem?_eq_some_iff.1 hb0).1
  have hsi := h.simp
  -- the renamed terminator
  have hto : ∀ x ∈ termOperands b0.term,
      (S.contains x = true ∨ ¬ Bad f logs bi b0.body.length S x) ∧
      Placed st (Bad f logs bi b0.body.length S) (S.step x) ∧
      AvailHere info.cfg.idom (CurV f logs bi lgs.toList) bi (S.step x) ∧
      st.types.get? (S.step x) = info.types.get? x := by
    intro x hx
    obtain ⟨-, h1, h2, h3, h4⟩ := hsi.renOp hc (hc.wf.termUses bi b0 hb0 x hx)
    exact ⟨h1, h2, h3, h4⟩
  have ht : mapTerm S.find b0.term = mapTerm S.step b0.term :=
    mapTerm_congr fun x _ => hsi.find_eq x
  have htops : ∀ y ∈ termOperands (mapTerm S.step b0.term),
      Placed st (Bad f logs bi b0.body.length S) y ∧
        AvailHere info.cfg.idom (CurV f logs bi lgs.toList) bi y := by
    intro y hy
    rw [termOperands_mapTerm, List.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨(hto x hx).2.1, (hto x hx).2.2.1⟩
  have hall : (termOperands (mapTerm S.step b0.term)).all st.known = true :=
    List.all_eq_true.2 fun y hy => (htops y hy).1.known
  obtain ⟨⟨extra, term, st', ch⟩, hsk⟩ :
      ∃ r, skelTerm skel rules allowed skelOk info.cfg bi rewriteLimit st (mapTerm S.step b0.term) = r :=
    ⟨_, rfl⟩
  have hE : endBlock rules skel allowed skelOk info.cfg b0 bi out logs (st, S, lgs) =
      (st', S, out.set! bi { b0 with body := (lgs.foldl (fun (acc : Array Stmt) (lg : StmtLog) =>
                                       acc ++ lg.out) #[] ++ extra).toList, term },
       logs.set! bi (some { stmts := lgs.toList, term := mapTerm S.step b0.term, extra,
                            term' := term, changed := ch })) := by
    simp only [endBlock, ht, hall, ↓reduceIte, hsk]
  rw [hE]
  simp only
  -- the skeleton rules on the terminator
  have hb : CurV f logs bi lgs.toList bi = some { b0 with body := outsOf lgs.toList } := CurV_bi hn hb0
  obtain ⟨sr, tr⟩ := skelTerm_ok (cfg := info.cfg) hR hK rewriteLimit st _ extra term st' ch _ _
    h.rinv hb htops hsk
  simp only at tr
  -- names
  have hrinv := h.rinv
  have hdoneAv := h.doneAv
  have hsubstOk := h.substOk
  have houts := h.outs
  have hdone := h.done
  have hcur := h.cur
  have hdefNB := h.defNB
  have haltsNB := h.altsNB
  have hciCur := h.ciCur
  generalize hBdef : Bad f logs bi b0.body.length S = B at *
  generalize hVdef : CurV f logs bi lgs.toList = V at *
  generalize hLdef : lgs.toList = L at *
  generalize hEdef : extra.toList = E at *
  have hbody : (lgs.foldl (fun (acc : Array Stmt) (lg : StmtLog) => acc ++ lg.out) #[] ++ extra).toList =
      outsOf L ++ E := by
    rw [Array.toList_append, ← Array.foldl_toList, foldl_out_toList, hLdef, hEdef]; simp
  -- the new view and bad values
  have hblockOf : ∀ lgB : BlockLog, lgB.stmts = L → lgB.extra = extra → lgB.term' = term →
      blockOf f bi lgB = some { b0 with body := outsOf L ++ E, term := term } := by
    intro lgB e1 e2 e3
    simp only [blockOf, hb0, Option.map_some, Option.some.injEq, e1, e2, e3]
    rw [← hEdef]; simp [outsOf]
  obtain ⟨lgB, hlgB⟩ : ∃ lgB : BlockLog, lgB =
      { stmts := L, term := mapTerm S.step b0.term, extra := extra, term' := term, changed := ch } :=
    ⟨_, rfl⟩
  rw [hbody, ← hlgB]
  have hl' : ∀ d, d ≠ bi → (logs.set! bi (some lgB))[d]? = logs[d]? := fun d hd => setB_ne _ _ hd
  have hlbi : (logs.set! bi (some lgB))[bi]? = some (some lgB) :=
    setB_eq _ _ (by rw [h.size]; exact hbi)
  have hBO := hblockOf lgB (by rw [hlgB]) (by rw [hlgB]) (by rw [hlgB])
  have hV' : ∀ d, CurV f (logs.set! bi (some lgB)) f.blocks.length [] d =
      if d = bi then some { b0 with body := outsOf L ++ E, term := term } else V d := by
    intro d
    rw [CurV_end]
    by_cases hd : d = bi
    · rw [ite_eq_left hd, hd]; simp only [V0, hlbi]; exact hBO
    · rw [ite_eq_right hd, ← hVdef, CurV_ne hd, V0_start hn hb0 d, ite_eq_right hd]
      simp only [V0, hl' d hd]
  have hV2 : ∀ d, emitV V bi E d = if d = bi then some { b0 with body := outsOf L ++ E } else V d := by
    intro d
    unfold emitV
    by_cases hd : d = bi
    · rw [ite_eq_left hd, ite_eq_left hd, hd, hb]; rfl
    · rw [ite_eq_right hd, ite_eq_right hd]
  have hext2 : VExt (emitV V bi E) (CurV f (logs.set! bi (some lgB)) f.blocks.length []) := by
    intro d b hbd
    rw [hV2] at hbd; rw [hV']
    by_cases hd : d = bi
    · rw [ite_eq_left hd] at hbd ⊢; cases hbd; exact ⟨_, rfl, rfl, rfl, [], by simp⟩
    · rw [ite_eq_right hd] at hbd ⊢; exact ⟨b, hbd, rfl, rfl, [], by simp⟩
  have hext2' : VExt (CurV f (logs.set! bi (some lgB)) f.blocks.length []) (emitV V bi E) := by
    intro d b hbd
    rw [hV'] at hbd; rw [hV2]
    by_cases hd : d = bi
    · rw [ite_eq_left hd] at hbd ⊢; cases hbd; exact ⟨_, rfl, rfl, rfl, [], by simp⟩
    · rw [ite_eq_right hd] at hbd ⊢; exact ⟨b, hbd, rfl, rfl, [], by simp⟩
  have hext : VExt V (CurV f (logs.set! bi (some lgB)) f.blocks.length []) :=
    (VExt.emit V bi E).trans hext2
  have hDoneEq : ∀ y, Done f (logs.set! bi (some lgB)) f.blocks.length 0 y ↔
      Done f logs bi b0.body.length y := by
    intro y
    constructor
    · rintro ⟨d, t, hd, ⟨lg, hlg⟩ | ⟨hdn, -⟩⟩
      · by_cases hdb : d = bi
        · obtain ⟨b, hb', hle⟩ := hc.def_blk hd
          rw [hdb, hb0] at hb'; cases hb'
          exact ⟨d, t, hd, .inr ⟨hdb, hle⟩⟩
        · rw [hl' d hdb] at hlg; exact ⟨d, t, hd, .inl ⟨lg, hlg⟩⟩
      · exact absurd (hc.def_lt hd) (by rw [hdn]; exact Nat.lt_irrefl _)
    · rintro ⟨d, t, hd, ⟨lg, hlg⟩ | ⟨hdb, -⟩⟩
      · have hdb : d ≠ bi := by intro e; rw [e, hn] at hlg; cases hlg
        exact ⟨d, t, hd, .inl ⟨lg, by rw [hl' d hdb]; exact hlg⟩⟩
      · exact ⟨d, t, hd, .inl ⟨lgB, by rw [hdb]; exact hlbi⟩⟩
  have hBeq : Bad f (logs.set! bi (some lgB)) f.blocks.length 0 S = B := by
    rw [← hBdef]; funext y; simp only [Bad]; rw [hDoneEq y]
  have hkB : ∀ y, S.contains y = true → B y := fun y hy => by rw [← hBdef]; exact .inr hy
  have hP1 : Prog V (CurV f (logs.set! bi (some lgB)) f.blocks.length []) B B st st' S S := by
    refine ⟨hext, sr.good, fun _ h => h, sr.types, sr.defsKeep, fun x hx hk => ?_, fun _ _ h => h,
      fun _ h => .inl h⟩
    cases hd : st'.defs.get? x with
    | none => rfl
    | some n =>
      rcases sr.fresh x n hd with h1 | h1
      · rw [hx] at h1; cases h1
      · rcases known_iff.1 hk with h2 | h2
        · rw [hx] at h2; cases h2
        · obtain ⟨d, hd2⟩ := Option.isSome_iff_exists.1 ((hm_contains_iff _ _).1 h2)
          have := h.availBig x d hd2 h1; rw [hx] at this; cases this
  have hP2 : Prog (emitV V bi E) (CurV f (logs.set! bi (some lgB)) f.blocks.length []) B B st' st'
      S S :=
    ⟨hext2, fun _ h => h, fun _ h => h, fun _ _ h => h, fun _ _ h _ => h, fun _ h _ => h,
     fun _ _ h => h, fun _ h => .inl h⟩
  have hnew : ∀ j s, E[j]? = some s →
      NewOk info.cfg.idom (emitV V bi E) bi ((outsOf L).length + j) allowed B st' s ∨
        TrapOk info.cfg.idom (emitV V bi E) bi ((outsOf L).length + j) skelOk B st' s :=
    fun j s hs => sr.stmts _ hb j s hs
  have hnewRes : ∀ s ∈ E, ∀ y ∈ s.results, ¬ B y ∧ st'.avail.get? y = some bi ∧
      (st'.defs.get? y).isSome := by
    intro s hs y hy
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hs
    rcases hnew j s hj with ⟨r, n', rfl, hd, hav, hnb, -, -⟩ | ⟨hr, -⟩
    · simp only [List.mem_singleton] at hy; subst hy; exact ⟨hnb, hav, by rw [hd]; rfl⟩
    · rw [hr] at hy; cases hy
  have hcallT : ∀ bc ∈ termCalls (mapTerm S.step b0.term), ∃ bc0 ∈ termCalls b0.term,
      bc.block = bc0.block ∧
        bc.args.map (fun x => st'.types.get? x) = bc0.args.map (fun x => info.types.get? x) := by
    intro bc hbc
    rw [termCalls_mapTerm, List.mem_map] at hbc
    obtain ⟨bc0, hbc0, rfl⟩ := hbc
    refine ⟨bc0, hbc0, rfl, ?_⟩
    simp only [mapBlockCall, List.map_map]
    refine List.map_congr_left fun x hx => ?_
    have hx' := args_sub_termOperands hbc0 hx
    simp only [Function.comp]
    rw [sr.typesKnown _ (hto x hx').2.1.known, (hto x hx').2.2.2]
  have hbrB : isBranch (mapTerm S.step b0.term) = true → isBranch b0.term = true := by
    rw [isBranch_mapTerm]; exact id
  refine { rinv := ?_, srcTy := fun y t hy => sr.types y t (h.srcTy y t hy),
           leafAv := fun y d hy => sr.avail y d (h.leafAv y d hy), availSrc := ?_, defsSrc := ?_,
           defsLeaf := ?_, doneAv := ?_, substOk := ?_, outs := ?_, done := ?_, size := ?_,
           altsNB := ?_, keysRes := h.keysRes, availBig := ?_, ciDone := ?_, defNB := ?_,
           outSize := ?_, outEq := ?_ }
  · rw [hBeq]; exact sr.inv.view hext2 hext2'
  · intro y d hy hle
    rcases sr.availNew y d hy with h1 | ⟨hdb, s, hs, hys⟩
    · rcases h.availSrc y d h1 hle with e | ⟨t', ht', hd'⟩
      · exact .inl e
      · exact .inr ⟨t', ht', (hDoneEq y).2 hd'⟩
    · obtain ⟨hnb, hav, -⟩ := hnewRes s hs y hys
      have hdone : Done f logs bi b0.body.length y :=
        Classical.byContradiction fun hnd => hnb (by rw [← hBdef]; exact .inl ⟨hle, hnd⟩)
      have hnS : S.contains y = false := by
        cases hk : S.contains y with
        | false => rfl
        | true => exact absurd (hkB y hk) hnb
      obtain ⟨-, d', t', hd', hav'⟩ := hdoneAv y hdone hnS
      have := sr.avail y d' hav'
      rw [hav] at this
      have hd'bi : d' = bi := (Option.some.inj this).symm
      rw [hdb]
      exact .inr ⟨t', by rw [← hd'bi]; exact hd', (hDoneEq y).2 hdone⟩
  · intro y n hy hle
    rcases sr.fresh y n hy with h1 | h1
    · exact (hDoneEq y).2 (h.defsSrc y n h1 hle)
    · exact absurd hle (Nat.not_le.2 h1)
  · intro y hy
    cases hd : st'.defs.get? y with
    | none => rfl
    | some n =>
      rcases sr.fresh y n hd with h1 | h1
      · rw [h.defsLeaf y hy] at h1; cases h1
      · exact absurd (hc.leaf_le hy) (Nat.not_le.2 h1)
  · intro y hd hS
    rw [hBeq]
    obtain ⟨hp, d, t, hdt, hav⟩ := hdoneAv y ((hDoneEq y).1 hd) hS
    exact ⟨sr.good y hp, d, t, hdt, sr.avail y d hav⟩
  · intro y w hyw
    rw [hBeq]
    obtain ⟨e1, e2, ⟨d', t', hd', e3⟩, e4⟩ := hsubstOk y w hyw
    refine ⟨(hDoneEq y).2 e1, sr.good w e2, ⟨d', t', hd'.ext hext, e3⟩, ?_⟩
    obtain ⟨d0, t0, hdt0, -⟩ := e3
    obtain ⟨T, hT⟩ := Checked.typed (hc := hc) hdt0
    have h3 := h.srcTy y T hT
    rw [sr.types y T h3, sr.types w T (by rw [e4]; exact h3)]
  · intro d b hbd
    rw [hBeq]
    rw [hV'] at hbd
    by_cases hd : d = bi
    · rw [ite_eq_left hd] at hbd
      cases hbd
      rw [hd]
      refine ⟨⟨b0, hb0, rfl, rfl⟩, fun k s hk => ?_⟩
      simp only at hk
      rcases Nat.lt_or_ge k (outsOf L).length with hkl | hkl
      · have hk' : (outsOf L)[k]? = some s := by rw [← hk]; exact (List.getElem?_append_left hkl).symm
        exact ((houts bi _ hb).2 k s hk').mono hP1 hrinv.m.defAvail ⟨_, hb, hk'⟩
      · have hk' : E[k - (outsOf L).length]? = some s := by
          rw [← hk, List.getElem?_append_right hkl]
        have ho : OutStmt f allowed skelOk info.cfg.idom (emitV V bi E) B st' bi
            ((outsOf L).length + (k - (outsOf L).length)) s := by
          rcases hnew _ s hk' with e | e
          · exact NewOk.outStmt sr.inv.m.defsTy e
          · exact TrapOk.outStmt e
        rw [Nat.add_sub_cancel' hkl] at ho
        exact ho.mono hP2 sr.inv.m.defAvail ⟨_, by rw [hV2, ite_eq_left rfl], hk⟩
    · rw [ite_eq_right hd] at hbd
      obtain ⟨e1, e2⟩ := houts d b hbd
      exact ⟨e1, fun k s hk => (e2 k s hk).mono hP1 hrinv.m.defAvail ⟨b, hbd, hk⟩⟩
  · intro d lg' hlg'
    rw [hBeq]
    by_cases hd : d = bi
    · rw [hd] at hlg' ⊢
      rw [hlbi] at hlg'
      simp only [Option.some.injEq] at hlg'
      subst hlg'
      refine ⟨b0, _, hb0, hBO, ?_, ?_, ?_⟩
      · obtain ⟨b0', hb0', -, hcur⟩ := hcur
        rw [hb0] at hb0'; cases hb0'
        rw [List.take_of_length_le (Nat.le_refl _)] at hcur
        rw [show lgB.stmts = L by rw [hlgB]]
        exact StmtsFact.mono hP1 hkB _ _ _ hcur
      · rw [hlgB]
        refine ⟨fun y hy => (hto y hy).1, rfl, ?_⟩
        cases ch with
        | false =>
          obtain ⟨e1, e2⟩ := tr.1 rfl
          simp only [Bool.false_eq_true, ↓reduceIte]
          refine ⟨?_, e2⟩
          apply Array.toList_inj.1
          rw [hEdef, e1]
        | true =>
          obtain ⟨c1, c2, c3, -, -⟩ := tr.2 rfl
          simp only [↓reduceIte]
          refine ⟨isBranch_of_cand c1, fun y hy => (c3 y hy).1, fun s hs => ?_⟩
          rw [hEdef] at hs
          obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hs
          rcases hnew j s hj with ⟨r, n', hsr, hd, -, -, ⟨n, τ, hal, hn'⟩, -⟩ | ⟨hr, htl, -, hops⟩
          · refine .inl ?_
            rw [hsr, hn']
            exact insOk_of hal hsym (by rw [← hn']; exact (sr.inv.m.defsTy r n' hd).1)
          · exact .inr ⟨trapOk_of hr htl, fun y hy => (hops y hy).1⟩
      · rw [show lgB.term' = term by rw [hlgB]]
        cases ch with
        | false =>
          obtain ⟨e1, e2⟩ := tr.1 rfl
          subst e2
          refine ⟨fun y hy => ⟨?_, sr.good y (htops y hy).1⟩, fun id hid => ?_, hcallT, ?_,
            .inl ⟨S.step, rfl⟩⟩
          · have := ((htops y hy).2.at_end hb).ext hext
            simpa [e1] using this
          · rw [termSuccs_mapTerm] at hid; exact hid
          · have hbt := hc.brt hb0
            cases hbt' : b0.term <;> simp only [hbt', mapTerm, brTableOk] at hbt ⊢
            rename_i x _ _
            have hx : x ∈ termOperands b0.term := by simp [hbt', termOperands]
            rw [sr.typesKnown _ (hto x hx).2.1.known, (hto x hx).2.2.2]
            exact hbt
        | true =>
          obtain ⟨c1, c2, c3, c4, c5⟩ := tr.2 rfl
          refine ⟨fun y hy => ⟨?_, (c3 y hy).1⟩, fun id hid => ?_, fun bc hbc => ?_, ?_,
            .inr ⟨hbrB (isBranch_of_cand c1), c2⟩⟩
          · have := (c3 y hy).2.ext hext2
            simpa using this
          · rw [termSuccs_branch c2] at hid
            obtain ⟨bc', hbc', rfl⟩ := List.mem_map.1 hid
            obtain ⟨bc, hbc, hbl, -⟩ := c4 bc' hbc'
            obtain ⟨bc0, hbc0, hbl0, -⟩ := hcallT bc hbc
            rw [hbl, hbl0, termSuccs_branch (hbrB (isBranch_of_cand c1))]
            exact List.mem_map_of_mem hbc0
          · obtain ⟨bc1, hbc1, hb1, ha1⟩ := c4 bc hbc
            obtain ⟨bc0, hbc0, hb0', ha0⟩ := hcallT bc1 hbc1
            exact ⟨bc0, hbc0, hb1.trans hb0', ha1.trans ha0⟩
          · cases term <;> simp only [brTableOk]
            exact c5 _ _ _ rfl
    · rw [hl' d hd] at hlg'
      obtain ⟨b1, bo, e1, e2, e3, e4, e5⟩ := hdone d lg' hlg'
      exact ⟨b1, bo, e1, e2, StmtsFact.mono hP1 hkB _ _ _ e3, e4.mono hP1 hkB, e5.mono' hc e1 hP1⟩
  · simp [h.size]
  · intro x ms hx
    rw [hBeq]
    rw [sr.alts] at hx
    exact haltsNB x ms hx
  · intro x d hx hlt
    rcases sr.availNew x d hx with h1 | ⟨-, s, hs, hxs⟩
    · obtain ⟨n, hn'⟩ := Option.isSome_iff_exists.1 (h.availBig x d h1 hlt)
      rw [sr.defsKeep x n hn' ((hm_contains_iff _ _).2 (by rw [h1]; rfl))]; rfl
    · exact (hnewRes s hs x hxs).2.2
  · intro d lg' b1 hlg' hb1
    by_cases hd : d = bi
    · rw [hd] at hlg' hb1
      rw [hlbi] at hlg'
      simp only [Option.some.injEq] at hlg'
      subst hlg'
      rw [hb0] at hb1; cases hb1
      have := hciCur b0 hb0
      rw [List.take_of_length_le (Nat.le_refl _)] at this
      rw [show lgB.stmts = L by rw [hlgB]]
      exact this
    · rw [hl' d hd] at hlg'
      exact h.ciDone d lg' b1 hlg' hb1
  · intro y d t hy
    rw [hBeq]
    rcases (hy.ext hext2').of_emit with hy' | ⟨b, -, -, k, s, -, hks, hys⟩
    · exact hdefNB y d t hy'
    · exact (hnewRes s (List.mem_of_getElem? hks) y hys).1
  · simp [hos]
  · intro d lg' hlg'
    by_cases hd : d = bi
    · rw [hd] at hlg' ⊢
      rw [hlbi] at hlg'
      simp only [Option.some.injEq] at hlg'
      subst hlg'
      rw [hBO, setB_eq _ _ (by rw [hos]; exact hbi)]
    · rw [hl' d hd] at hlg'
      rw [setB_ne _ _ hd]
      exact hoe d lg' hlg'

end End

end Opt
