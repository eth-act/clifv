import FV.Opt.Proof.CompleteSimpRunDef
import FV.Opt.Proof.CompleteOptimize

/-!
# Completeness of simplify: from the end of the run to the validator
-/

namespace Opt

open Clif

section Assemble

variable {f : Function} {info : Info} {allowed skelOk : Inst → Bool} {st : SState} {S : Subst}
  {out : Array Block} {logs : Array (Option BlockLog)}

/-- A placeable value is not renamed. -/
theorem RunDone.fixed (_h : RunDone f info allowed skelOk st S out logs) {y : ValueId}
    (hy : Placed st (Bad f logs f.blocks.length 0 S) y) : S.contains y = false := by
  cases hc : S.contains y with
  | false => rfl
  | true => exact absurd (.inr hc) hy.not_bad

theorem RunDone.chainFree (h : RunDone f info allowed skelOk st S out logs) : ChainFree S := by
  intro k w hk
  have hw := h.fixed (h.substOk k w (by rw [Std.HashMap.get?_eq_getElem?]; exact hk)).2.1
  exact Std.HashMap.getElem?_eq_none_of_contains_eq_false hw

/-- The view at the end of the run is the output blocks. -/
theorem RunDone.view (h : RunDone f info allowed skelOk st S out logs) (d : Nat) :
    V0 f logs f.blocks.length d = out.toList[d]? := by
  rw [Array.getElem?_toList]
  by_cases hd : d < f.blocks.length
  · obtain ⟨lg, hlg⟩ := h.all d hd
    simp only [V0, hlg]
    rw [h.outEq.2 d lg hlg]
  · have h1 : logs[d]? = none := Array.getElem?_eq_none (by rw [h.size]; omega)
    have h2 : out[d]? = none := Array.getElem?_eq_none (by rw [h.outEq.1]; omega)
    have h3 : f.blocks[d]? = none := List.getElem?_eq_none (by omega)
    simp only [V0, h1, h2, h3, Option.map_none]
    split <;> rfl

/-- The output block `d` and its record. -/
theorem RunDone.block (h : RunDone f info allowed skelOk st S out logs) {d : Nat} {b : Block}
    (hb : out.toList[d]? = some b) :
    ∃ lg b0, logs[d]? = some (some lg) ∧ f.blocks[d]? = some b0 ∧ blockOf f d lg = some b ∧
      b = { b0 with body := ((lg.stmts.toArray.flatMap (·.out)) ++ lg.extra).toList,
                    term := lg.term' } := by
  have hd : d < f.blocks.length := by
    rw [← h.outEq.1]; have := (List.getElem?_eq_some_iff.1 hb).1; simpa using this
  obtain ⟨lg, hlg⟩ := h.all d hd
  obtain ⟨b0, hb0⟩ : ∃ b0, f.blocks[d]? = some b0 := ⟨_, List.getElem?_eq_getElem hd⟩
  have hbo := h.outEq.2 d lg hlg
  rw [Array.getElem?_toList] at hb
  rw [hb] at hbo
  refine ⟨lg, b0, hlg, hb0, hbo.symm, ?_⟩
  simp only [blockOf, hb0, Option.map_some, Option.some.injEq] at hbo
  exact hbo

/-- The output's statement operands and terminator operands are not renamed. -/
theorem RunDone.outFixed (h : RunDone f info allowed skelOk st S out logs) {b : Block}
    (hb : b ∈ out.toList) :
    (∀ s ∈ b.body, ∀ y ∈ operands s.inst, S.contains y = false) ∧
      ∀ y ∈ termOperands b.term, S.contains y = false := by
  obtain ⟨d, hd⟩ := List.mem_iff_getElem?.1 hb
  have hV := (h.view d).trans hd
  obtain ⟨-, hst⟩ := h.outs d b hV
  refine ⟨fun s hs y hy => ?_, fun y hy => ?_⟩
  · obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hs
    exact h.fixed ((hst k s hk).uses y hy).2
  · obtain ⟨lg, b0, hlg, hb0, hbo, rfl⟩ := h.block hd
    obtain ⟨b0', bo, hb0', hbo', -, -, hto⟩ := h.done d lg hlg
    exact h.fixed (hto.uses y hy).2

theorem find_of_not_contains {S : Subst} (hc : ChainFree S) {x : ValueId}
    (hx : S.contains x = false) : S.find x = x := by
  rw [find_chainFree hc, Std.HashMap.getElem?_eq_none_of_contains_eq_false hx]; rfl

/-- **The output function** is the output blocks: the final renaming touches no operand. -/
theorem RunDone.apply_eq (h : RunDone f info allowed skelOk st S out logs) :
    S.apply { f with blocks := out.toList } = { f with blocks := out.toList } := by
  unfold Subst.apply
  split
  · rfl
  · have hcf := h.chainFree
    simp only [Function.mk.injEq, and_true, true_and]
    conv => rhs; rw [← List.map_id out.toList]
    refine List.map_congr_left fun b hb => ?_
    obtain ⟨h1, h2⟩ := h.outFixed hb
    have hbody : b.body.map (fun st => { st with inst := mapOperands S.find st.inst }) = b.body := by
      conv => rhs; rw [← List.map_id b.body]
      refine List.map_congr_left fun s hs => ?_
      have : mapOperands S.find s.inst = s.inst := by
        conv => rhs; rw [← mapOperands_id s.inst]
        exact mapOperands_congr fun y hy => find_of_not_contains hcf (h1 s hs y hy)
      simp [this]
    have hterm : mapTerm S.find b.term = b.term := by
      conv => rhs; rw [← mapTerm_id b.term]
      exact mapTerm_congr fun y hy => find_of_not_contains hcf (h2 y hy)
    simp [hbody, hterm]

/-! ## Definition sites of the output -/

/-- The output function. -/
abbrev outFn (f : Function) (out : Array Block) : Function := { f with blocks := out.toList }

theorem nodup_map_on {α β : Type} {g : α → β} {l : List α}
    (hi : ∀ x ∈ l, ∀ y ∈ l, g x = g y → x = y) (hn : l.Nodup) : (l.map g).Nodup := by
  rw [List.Nodup, List.pairwise_map]
  exact hn.imp_of_mem fun hx hy hne he => hne (hi _ hx _ hy he)

theorem sublist_flatMap_mem {α β : Type} {g : α → List β} :
    ∀ {l : List α} {a : α}, a ∈ l → (g a).Sublist (l.flatMap g)
  | x :: l, a, h => by
    simp only [List.flatMap_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact List.sublist_append_left _ _
    · exact (sublist_flatMap_mem h).trans (List.sublist_append_right _ _)

theorem nodup_flatMap_zipIdx {α β : Type} (key : β → Nat) (G : α × Nat → List β)
    (hG : ∀ a k, ∀ y ∈ G (a, k), key y = k) :
    ∀ (l : List α) (k : Nat), (∀ a ∈ l, ∀ k, (G (a, k)).Nodup) → ((l.zipIdx k).flatMap G).Nodup
  | [], _, _ => List.nodup_nil
  | a :: l, k, hN => by
    rw [List.zipIdx_cons, List.flatMap_cons, List.nodup_append]
    refine ⟨hN a (by simp) k,
      nodup_flatMap_zipIdx key G hG l (k + 1) (fun a' ha' => hN a' (by simp [ha'])), ?_⟩
    intro x hx y hy hxy
    obtain ⟨⟨a', k'⟩, hm, hy'⟩ := List.mem_flatMap.1 hy
    have h1 := hG a k x hx
    have h2 := hG a' k' y hy'
    have h3 := (List.mem_zipIdx hm).1
    subst hxy; omega

/-- The definition sites of a function whose block parameters and statement results have no
repetition have no repetition. -/
theorem defSites_nodup_of {g : Function} (hp : ∀ b ∈ g.blocks, (b.params.map (·.1)).Nodup)
    (hr : ∀ b ∈ g.blocks, ∀ s ∈ b.body, s.results.Nodup) : (defSites g).Nodup := by
  unfold defSites
  refine nodup_flatMap_zipIdx (fun y => y.2.1) _ ?_ g.blocks 0 ?_
  · intro b k y hy
    simp only [List.mem_append, List.mem_map, List.mem_flatMap] at hy
    rcases hy with ⟨p, -, rfl⟩ | ⟨⟨s, j⟩, -, r, -, rfl⟩ <;> rfl
  · intro b hb k
    simp only
    rw [List.nodup_append]
    refine ⟨?_, ?_, ?_⟩
    · have := hp b hb
      rw [List.Nodup, List.pairwise_map] at this ⊢
      exact this.imp fun hne he => hne (by simpa using congrArg Prod.fst he)
    · refine nodup_flatMap_zipIdx (fun y => y.2.2 - 1) _ ?_ b.body 0 ?_
      · intro s j y hy
        simp only [List.mem_map] at hy
        obtain ⟨r, -, rfl⟩ := hy
        simp
      · intro s hs j
        simp only
        exact (hr b hb s hs).map _ fun a c hne he => hne (by simpa using congrArg Prod.fst he)
    · intro x hx y hy hxy
      simp only [List.mem_map, List.mem_flatMap] at hx hy
      obtain ⟨p, -, rfl⟩ := hx
      obtain ⟨⟨s, j⟩, -, r, -, rfl⟩ := hy
      simp at hxy

theorem params_nodup {g : Function} (hu : UniqueDefs g) {b : Block} (hb : b ∈ g.blocks) :
    (b.params.map (·.1)).Nodup := by
  unfold UniqueDefs at hu
  rw [defSites_fst] at hu
  exact List.Nodup.sublist ((List.sublist_append_left _ _).trans
    (sublist_flatMap_mem (g := fun b : Block => b.params.map (·.1) ++ b.body.flatMap (·.results))
      hb)) hu

theorem RunDone.defAt_iff (h : RunDone f info allowed skelOk st S out logs) {x : ValueId}
    {d t : Nat} :
    DefAt (V0 f logs f.blocks.length) x d t ↔ (x, (d, t)) ∈ defSites (outFn f out) := by
  rw [mem_defSites]
  simp only [DefAt, h.view d]
  constructor
  · rintro ⟨b, hb, ⟨rfl, p, hp, rfl⟩ | ⟨j, s, rfl, hs, hx⟩⟩
    · exact ⟨d, b, hb, .inl ⟨p, hp, rfl, rfl⟩⟩
    · exact ⟨d, b, hb, .inr ⟨j, s, hs, hx, rfl⟩⟩
  · rintro ⟨i, b, hb, ⟨p, hp, rfl, he⟩ | ⟨j, s, hs, hx, he⟩⟩
    · simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
      exact ⟨b, hb, .inl ⟨rfl, p, hp, rfl⟩⟩
    · simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
      exact ⟨b, hb, .inr ⟨j, s, rfl, hs, hx⟩⟩

/-- **Values are defined once in the output.** -/
theorem RunDone.unique (hc : Checked f info) (h : RunDone f info allowed skelOk st S out logs) :
    UniqueDefs (outFn f out) := by
  unfold UniqueDefs
  refine nodup_map_on ?_ (defSites_nodup_of ?_ ?_)
  · rintro ⟨v, d, t⟩ hx ⟨v', d', t'⟩ hy (rfl : v = v')
    obtain ⟨e1, e2⟩ := h.rinv.m.uniq v d t d' t' (h.defAt_iff.2 hx) (h.defAt_iff.2 hy)
    subst e1; subst e2; rfl
  · intro b hb
    obtain ⟨d, hd⟩ := List.mem_iff_getElem?.1 hb
    obtain ⟨lg, b0, -, hb0, -, rfl⟩ := h.block hd
    have := params_nodup hc.unique (List.mem_of_getElem? hb0)
    exact this
  · intro b hb s hs
    obtain ⟨d, hd⟩ := List.mem_iff_getElem?.1 hb
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hs
    exact ((h.outs d b ((h.view d).trans hd)).2 k s hk).nodup

theorem RunDone.dm (hc : Checked f info) (h : RunDone f info allowed skelOk st S out logs)
    {x : ValueId} {d t : Nat} (hx : DefAt (V0 f logs f.blocks.length) x d t) :
    (defMap (outFn f out)).get? x = some (d, t) :=
  (defMap_get_iff (h.unique hc) x (d, t)).2 (h.defAt_iff.1 hx)

theorem RunDone.avail (hc : Checked f info) (h : RunDone f info allowed skelOk st S out logs)
    {W : WfData} (hW : W.dm = (defMap (outFn f out)).get?) (hi : W.idom = info.cfg.idom)
    {i k : Nat} {x : ValueId} (hx : AvailAt info.cfg.idom (V0 f logs f.blocks.length) i k x) :
    Avail W i k x := by
  obtain ⟨d, t, hd, hr⟩ := hx
  exact ⟨d, t, by rw [hW]; exact h.dm hc hd, by rw [hi]; exact hr⟩

/-- The certificate data of the output: `f`'s dominator tree, the final graph's types. -/
abbrev outInfo (info : Info) (st : SState) : Info := { info with types := st.types }

/-- **The output is well formed** over `f`'s dominator tree with the final graph's types. -/
theorem RunDone.wf (hc : Checked f info) (h : RunDone f info allowed skelOk st S out logs) :
    Wf (outFn f out) (wfData (outFn f out) (outInfo info st)) where
  ids i b hb := by
    obtain ⟨lg, b0, -, hb0, -, rfl⟩ := h.block hb
    exact hc.wf.ids i b0 hb0
  sites v s hv := (defMap_get_iff (h.unique hc) v s).2 hv
  sitesRev v s hv := (defMap_get_iff (h.unique hc) v s).1 hv
  root := hc.wf.root
  rank := hc.wf.rank
  params i b hb p hp := by
    obtain ⟨lg, b0, -, hb0, -, rfl⟩ := h.block hb
    exact h.srcTy _ _ (hc.wf.params i b0 hb0 p hp)
  uses i b hb j s hs v hv :=
    h.avail hc rfl rfl ((((h.outs i b ((h.view i).trans hb)).2 j s hs).uses v hv).1)
  results i b hb j s hs := ((h.outs i b ((h.view i).trans hb)).2 j s hs).results
  pure i b hb j s hs hp := by
    have := ((h.outs i b ((h.view i).trans hb)).2 j s hs).pure hp
    rw [← this]
    exact pureTyped_congr (fun _ _ => rfl) rfl rfl
  termUses i b hb v hv := by
    obtain ⟨lg, b0, hlg, hb0, hbo, rfl⟩ := h.block hb
    obtain ⟨b0', bo, hb0', hbo', -, -, hto⟩ := h.done i lg hlg
    rw [hbo] at hbo'; cases hbo'
    exact h.avail hc rfl rfl (hto.uses v hv).1
  edges i b hb id hid := by
    obtain ⟨lg, b0, hlg, hb0, hbo, rfl⟩ := h.block hb
    obtain ⟨b0', bo, hb0', hbo', -, -, hto⟩ := h.done i lg hlg
    rw [hb0] at hb0'; cases hb0'
    obtain ⟨j, b'', hj, hb'', hid', hanc⟩ := hc.wf.edges i b0 hb0 id (hto.succs id hid)
    have hjl : j < f.blocks.length := (List.getElem?_eq_some_iff.1 hb'').1
    obtain ⟨lg', hlg'⟩ := h.all j hjl
    have hoj := h.outEq.2 j lg' hlg'
    simp only [blockOf, hb'', Option.map_some] at hoj
    obtain ⟨bj, hbj, hbjid⟩ : ∃ bj, out[j]? = some bj ∧ bj.id = id := ⟨_, hoj, hid'⟩
    exact ⟨j, bj, hj, by rw [Array.getElem?_toList]; exact hbj, hbjid, hanc⟩

/-! ## The validator from its facts (the converse of `simpOk_facts`) -/

section Check

variable {idom : Array (Option Nat)} {V : Nat → Option Block} {B : ValueId → Prop}
  {A : Nat → ValueId → Bool}

theorem fixed_of {xs : List ValueId} (h : ∀ y ∈ xs, S.contains y = false) :
    SimpCtx.fixed { subst := S, avail := A } xs = true := by
  simp only [SimpCtx.fixed, List.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
  exact h

theorem all_of_mem {α : Type} {p : α → Bool} {a : Array α} (h : ∀ t ∈ a.toList, p t = true) :
    a.all p = true := by
  rw [Array.all_eq_true_iff_forall_mem]
  exact fun t ht => h t (Array.mem_toList_iff.2 ht)

theorem stmtOk_of {d k' : Nat} {s : Stmt} {lg : StmtLog}
    (hA : ∀ k w, AvailAt idom V d k w → A k w = true)
    (hfix : ∀ y, Placed st B y → S.contains y = false)
    (h : SLogFact idom V B st S d s k' lg) :
    SimpCtx.stmtOk { subst := S, avail := A } s k' lg = true := by
  obtain ⟨-, h⟩ := h
  cases lg with
  | keep s' =>
    obtain ⟨rfl, hr⟩ := h
    simp [SimpCtx.stmtOk, SimpCtx.σ, fixed_of (A := A) fun r hr' => hfix r (hr r hr')]
  | repl s' w out =>
    obtain ⟨rfl, hp, hins, ⟨v, hv, hS⟩, hav⟩ := h
    rw [Std.HashMap.get?_eq_getElem?] at hS
    simp [SimpCtx.stmtOk, SimpCtx.σ, hv, hp, hS, all_of_mem hins, hA _ _ hav]
  | skel s' o out =>
    obtain ⟨rfl, hsk, hl⟩ := h
    cases o with
    | keep =>
      obtain ⟨rfl, hr⟩ := hl
      simp [SimpCtx.stmtOk, SimpCtx.σ, hsk, fixed_of (A := A) fun r hr' => hfix r (hr r hr')]
    | remove =>
      obtain ⟨e1, e2, e3, e4⟩ := hl
      simp [SimpCtx.stmtOk, SimpCtx.σ, hsk, e1, e2, e3, all_of_mem e4]
    | removeWithVal v' =>
      obtain ⟨e1, e2, e3, e4, r, e5, e6⟩ := hl
      rw [Std.HashMap.get?_eq_getElem?] at e6
      simp [SimpCtx.stmtOk, SimpCtx.σ, hsk, e1, e2, e5, e6, all_of_mem e3, hA _ _ e4]
    | replace i =>
      obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := hl
      simp only [SimpCtx.stmtOk, all_of_mem e6]
      simp [SimpCtx.σ, hsk, e1, e2, e5, e7, e8, e9,
        fixed_of (A := A) fun r hr => hfix r (e3 r hr), fixed_of (A := A) fun y hy => hfix y (e4 y hy)]
    | two a c =>
      obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12⟩ := hl
      simp only [SimpCtx.stmtOk, all_of_mem e6]
      simp [SimpCtx.σ, hsk, e1, e2, e4, e5, e7, e8, e9, e10, e11, e12,
        fixed_of (A := A) fun y hy => hfix y (e3 y hy)]

theorem stmtsOk_of {d : Nat} (hA : ∀ k w, AvailAt idom V d k w → A k w = true)
    (hfix : ∀ y, Placed st B y → S.contains y = false) :
    ∀ (ss : List Stmt) (lgs : List StmtLog) (k' : Nat), StmtsFact idom V B st S d ss lgs k' →
      SimpCtx.stmtsOk { subst := S, avail := A } ss lgs k' = true
  | [], [], _, _ => rfl
  | s :: ss, lg :: lgs, k', ⟨h1, h2⟩ => by
    simp only [SimpCtx.stmtsOk, Bool.and_eq_true]
    exact ⟨stmtOk_of hA hfix h1, stmtsOk_of hA hfix ss lgs _ h2⟩
  | [], _ :: _, _, h => h.elim
  | _ :: _, [], _, h => h.elim

theorem termOk_of {b0 : Block} {lg : BlockLog} (hfix : ∀ y, Placed st B y → S.contains y = false)
    (h : TermLogFact B st S b0 lg) : SimpCtx.termOk { subst := S, avail := A } lg = true := by
  obtain ⟨-, -, h⟩ := h
  unfold SimpCtx.termOk
  split
  · rename_i hc
    simp only [hc, ↓reduceIte] at h
    obtain ⟨e1, e2, e3⟩ := h
    simp only [Bool.and_eq_true, e1, true_and]
    refine ⟨fixed_of fun y hy => hfix y (e2 y hy), all_of_mem fun t ht => ?_⟩
    rcases e3 t ht with e | ⟨e, e'⟩
    · simp [e]
    · simp [e, fixed_of fun y hy => hfix y (e' y hy)]
  · rename_i hc
    simp only [hc] at h
    obtain ⟨e1, e2⟩ := h
    simp [e1, e2]

end Check

/-- **The validator from its facts** (the converse of `simpOk_facts`, without the facts of `f`). -/
theorem simpOk_of {f g : Function} {fi : Info} {cert : SimpCert} (hhdr : SameHdr f g)
    (hlen : g.blocks.length = f.blocks.length) (hch : cert.subst.chainFree = true)
    (hwf : Wf g (wfData g (gInfo fi cert)))
    (hleaf : ∀ x, (initAvail f).contains x = true → cert.types.get? x = fi.types.get? x)
    (hbl : ∀ (i : Nat) (b : Block), f.blocks[i]? = some b → ∃ (b' : Block) (lg : BlockLog),
      g.blocks[i]? = some b' ∧ cert.logs[i]? = some (some lg) ∧ b'.id = b.id ∧
      b'.params = b.params ∧
      b'.body = (outs lg.stmts ++ lg.extra.toList).map (renStmt cert.subst.step) ∧
      b'.term = mapTerm cert.subst.step lg.term' ∧ lg.term = mapTerm cert.subst.step b.term ∧
      (sctx g fi cert i).termOk lg = true ∧ (sctx g fi cert i).stmtsOk b.body lg.stmts 0 = true ∧
      (∀ p ∈ b.params, cert.defs.contains p.1 = false ∧ (initAvail f).contains p.1 = true ∧
        cert.subst.contains p.1 = false) ∧
      (∀ s ∈ b.body, skeletonStmt s = true → ∀ r ∈ s.results, cert.defs.contains r = false) ∧
      (∀ t ∈ b'.body, ∀ x, t.results = [x] → isPure t.inst = true →
        cert.defs.get? x = some t.inst) ∧
      (∀ t ∈ b'.body, skeletonStmt t = true → ∀ r ∈ t.results,
        cert.defs.contains r = false ∧ (initAvail f).contains r = true)) :
    simpOk f g fi cert = true := by
  simp only [simpOk, sameHeader, Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨hhdr.name, hhdr.sig⟩, hhdr.slots⟩, hhdr.globals⟩, hhdr.externs⟩, hlen⟩, hch⟩,
    wfCert_complete hwf⟩, ?_⟩, ?_⟩
  · rintro ⟨x, d⟩ hx
    have hx' : (initAvail f).get? x = some d := by
      rw [Std.HashMap.mem_toList_iff_getElem?_eq_some] at hx
      simpa [Std.HashMap.get?_eq_getElem?] using hx
    simpa using hleaf x ((hm_contains_iff _ _).2 (by rw [hx']; rfl))
  · rintro ⟨⟨b, b'⟩, i⟩ hz
    rw [List.mem_zipIdx_iff_getElem?, List.getElem?_zip_eq_some] at hz
    obtain ⟨hb, hb'⟩ := hz
    obtain ⟨b'', lg, hb'', hlg, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hbl i b hb
    rw [hb'] at hb''; cases hb''
    simp only [hlg, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true,
      Bool.not_eq_eq_eq_not, Bool.not_true]
    refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, ?_⟩, h4⟩, h5⟩, h6⟩, h7⟩, fun p hp => ?_⟩, fun s hs => ?_⟩,
      fun t ht => ?_⟩, fun t ht => ?_⟩
    · rw [h3]; simp [outs]
    · obtain ⟨e1, e2, e3⟩ := h8 p hp
      exact ⟨⟨e1, e2⟩, e3⟩
    · cases hsk : skeletonStmt s
      · exact .inl rfl
      · exact .inr (h9 s hs hsk)
    · split
      · rename_i x hx
        cases hp : isPure t.inst
        · simp
        · have := h10 t ht x hx hp
          rw [Std.HashMap.get?_eq_getElem?] at this
          simp [this]
      · trivial
    · cases hsk : skeletonStmt t
      · exact .inl rfl
      · exact .inr (h11 t ht hsk)

/-! ## The facts of the output -/

theorem contains_false_of_get {β : Type} {m : Std.HashMap ValueId β} {x : ValueId}
    (h : m.get? x = none) : m.contains x = false := by
  cases hc : m.contains x with
  | false => rfl
  | true => rw [hm_contains_iff, h] at hc; cases hc

theorem renStmt_fixed {S : Subst} {t : Stmt} (h : ∀ y ∈ operands t.inst, S.contains y = false) :
    renStmt S.step t = t := by
  have : mapOperands S.step t.inst = t.inst := by
    conv => rhs; rw [← mapOperands_id t.inst]
    exact mapOperands_congr fun y hy => step_of_not_contains (h y hy)
  simp [renStmt, this]

theorem mapTerm_fixed {S : Subst} {t : Terminator} (h : ∀ y ∈ termOperands t, S.contains y = false) :
    mapTerm S.step t = t := by
  conv => rhs; rw [← mapTerm_id t]
  exact mapTerm_congr fun y hy => step_of_not_contains (h y hy)

theorem RunDone.blockAt (h : RunDone f info allowed skelOk st S out logs) {i : Nat} {b0 : Block}
    (hb0 : f.blocks[i]? = some b0) : ∃ lg, logs[i]? = some (some lg) ∧
      out.toList[i]? = some
        { b0 with body := ((lg.stmts.toArray.flatMap (·.out)) ++ lg.extra).toList, term := lg.term' } := by
  obtain ⟨lg, hlg⟩ := h.all i (List.getElem?_eq_some_iff.1 hb0).1
  have := h.outEq.2 i lg hlg
  simp only [blockOf, hb0, Option.map_some] at this
  exact ⟨lg, hlg, by rw [Array.getElem?_toList]; exact this⟩

theorem RunDone.leafTy (hc : Checked f info) (h : RunDone f info allowed skelOk st S out logs)
    {x : ValueId} (hx : (initAvail f).contains x = true) : st.types.get? x = info.types.get? x := by
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.1 ((hm_contains_iff _ _).1 hx)
  obtain ⟨b, hb, hm⟩ := mem_leafList.1 ((initAvail_get hc.unique x d).1 hd)
  have hs : ∃ s, (x, s) ∈ defSites f := by
    rcases hm with ⟨p, hp, rfl⟩ | ⟨s, hs, -, hr⟩
    · exact ⟨(d, 0), mem_defSites.2 ⟨d, b, hb, .inl ⟨p, hp, rfl, rfl⟩⟩⟩
    · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hs
      exact ⟨(d, j + 1), mem_defSites.2 ⟨d, b, hb, .inr ⟨j, s, hj, hr, rfl⟩⟩⟩
  obtain ⟨s, hs⟩ := hs
  obtain ⟨t, ht⟩ := Checked.typed (hc := hc) ((defMap_get_iff hc.unique x s).2 hs)
  rw [h.srcTy x t ht, ht]

theorem RunDone.chainFreeB (h : RunDone f info allowed skelOk st S out logs) :
    S.chainFree = true := by
  simp only [Subst.chainFree, List.all_eq_true]
  rintro ⟨k, w⟩ hkw
  rw [Std.HashMap.mem_toList_iff_getElem?_eq_some] at hkw
  have := h.fixed (h.substOk k w (by rw [Std.HashMap.get?_eq_getElem?]; exact hkw)).2.1
  simp [this]

theorem RunDone.leafIn (hc : Checked f info) {i : Nat} {b : Block} (hb : f.blocks[i]? = some b)
    {x : ValueId} (hx : (∃ p ∈ b.params, p.1 = x) ∨ ∃ s ∈ b.body, skeletonStmt s = true ∧ x ∈ s.results) :
    (initAvail f).contains x = true :=
  (hm_contains_iff _ _).2 (by rw [(initAvail_get hc.unique x i).2 (mem_leafList.2 ⟨b, hb, hx⟩)]; rfl)

/-- **The validator accepts the output.** -/
theorem RunDone.simpOk (hc : Checked f info) (h : RunDone f info allowed skelOk st S out logs) :
    simpOk f (outFn f out) info { defs := st.defs, types := st.types, subst := S, logs } = true := by
  refine simpOk_of ⟨rfl, rfl, rfl, rfl, rfl⟩ (by simp [h.outEq.1]) h.chainFreeB (h.wf hc)
    (fun x hx => h.leafTy hc hx) ?_
  intro i b hb
  obtain ⟨lg, hlg, hbo⟩ := h.blockAt hb
  obtain ⟨b0', bo, hb0', hbo', hsf, htl, hto⟩ := h.done i lg hlg
  rw [hb] at hb0'; cases hb0'
  obtain ⟨-, hos⟩ := h.outs i _ ((h.view i).trans hbo)
  obtain ⟨hof1, hof2⟩ := h.outFixed (List.mem_of_getElem? hbo)
  have e : ((lg.stmts.toArray.flatMap (·.out)) ++ lg.extra).toList = Opt.outs lg.stmts ++ lg.extra.toList := by
    simp [Opt.outs]
  refine ⟨_, lg, hbo, hlg, rfl, rfl, ?_, (mapTerm_fixed hof2).symm, htl.2.1,
    termOk_of (fun y hy => h.fixed hy) htl,
    stmtsOk_of (fun k w hw => availB_complete (W := wfData (outFn f out) (outInfo info st))
      hc.wf.rank (h.avail hc rfl rfl hw)) (fun y hy => h.fixed hy) _ _ _ hsf,
    fun p hp => ?_, fun s hs hsk r hr => ?_, fun t ht x hx hp => ?_, fun t ht hsk r hr => ?_⟩
  · show ((lg.stmts.toArray.flatMap (·.out)) ++ lg.extra).toList = _
    rw [← e]
    conv => lhs; rw [← List.map_id ((lg.stmts.toArray.flatMap (·.out)) ++ lg.extra).toList]
    exact List.map_congr_left fun t ht => (renStmt_fixed (hof1 t ht)).symm
  · have hL := RunDone.leafIn hc hb (.inl ⟨p, hp, rfl⟩)
    refine ⟨contains_false_of_get (h.defsLeaf p.1 hL), hL, ?_⟩
    cases hk : S.contains p.1 with
    | false => rfl
    | true =>
      obtain ⟨d, j, hdj⟩ := h.keysRes _ hk
      rw [(defMap_get_iff hc.unique p.1 (i, 0)).2 (mem_defSites.2 ⟨i, b, hb, .inl ⟨p, hp, rfl, rfl⟩⟩)]
        at hdj
      simp at hdj
  · exact contains_false_of_get (h.defsLeaf r (RunDone.leafIn hc hb (.inr ⟨s, hs, hsk, hr⟩)))
  · obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 ht
    exact (hos k t hk).node x hx hp
  · obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 ht
    obtain ⟨e1, e2⟩ := (hos k t hk).leaf hsk r hr
    exact ⟨contains_false_of_get e1, e2⟩

theorem zip_all_congr {ps : List (ValueId × Ty)} {F G : ValueId → Option Ty} :
    ∀ {as bs : List ValueId}, as.map F = bs.map G →
      ((ps.zip as).all fun x => F x.2 == some x.1.2) = ((ps.zip bs).all fun x => G x.2 == some x.1.2)
  | [], [], _ => by simp
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: as, b :: bs, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    cases ps with
    | nil => rfl
    | cons p ps =>
      simp only [List.zip_cons_cons, List.all_cons, h.1]
      rw [zip_all_congr (ps := ps) h.2]

/-- **`check` accepts the output once its unreachable blocks are removed.** -/
theorem RunDone.recheck (hc : Checked f info) (h : RunDone f info allowed skelOk st S out logs) :
    check (removeUnreachable (outFn f out)) = .ok (coreInfo (removeUnreachable (outFn f out))) := by
  have hpos : 0 < f.blocks.length := by simpa [Cfg.size, Cfg.build] using hc.core.1
  refine check_removeUnreachable_of_wfCert' (cfg := info.cfg) (types := st.types)
    (wfCert_complete (h.wf hc)) (h.unique hc) ?_ ?_ ?_ ?_
  · apply List.ne_nil_of_length_pos
    simp [h.outEq.1, hpos]
  · intro b hb
    rw [List.head?_eq_getElem?] at hb
    obtain ⟨lg, b0, -, hb0, -, rfl⟩ := h.block hb
    have e : f.blocks.toArray[0]! = b0 := by simp [getElem!_def, hb0]
    have := hc.core.2.2.2.2.1
    rw [e] at this
    exact this
  · intro b hb bc hbc b' hb' hid
    obtain ⟨d, hd⟩ := List.mem_iff_getElem?.1 hb
    obtain ⟨lg, b0, hlg, hb0, -, rfl⟩ := h.block hd
    obtain ⟨b0', bo, hb0', -, -, -, hto⟩ := h.done d lg hlg
    rw [hb0] at hb0'; cases hb0'
    obtain ⟨bc0, hbc0, hbl, hargs⟩ := hto.calls bc hbc
    obtain ⟨d', hd'⟩ := List.mem_iff_getElem?.1 hb'
    obtain ⟨lg', b1, -, hb1, -, rfl⟩ := h.block hd'
    obtain ⟨-, -, hcalls0, -⟩ := hc.core.2.2.2.2.2 _
      ((List.mem_zipIdx_iff_getElem? (x := (b0, d))).2 hb0)
    obtain ⟨j, hj, hok⟩ := hcalls0 bc0 hbc0
    have hidx : (Cfg.build f).index.get? bc0.block = some d' := by
      have := hc.wf.ids d' b1 hb1
      rw [hc.info_eq] at this
      simp only at hid
      rw [← hbl, ← hid]
      exact this
    rw [hidx] at hj; cases hj
    have e : f.blocks.toArray[d']! = b1 := by simp [getElem!_def, hb1]
    rw [e] at hok
    have ht : (defsState f).1 = info.types := by rw [hc.info_eq]; rfl
    rw [ht] at hok
    simp only [Bool.and_eq_true, beq_iff_eq] at hok ⊢
    have hl : bc.args.length = bc0.args.length := by simpa using congrArg List.length hargs
    exact ⟨by rw [hl]; exact hok.1, by rw [zip_all_congr hargs]; exact hok.2⟩
  · intro b hb
    obtain ⟨d, hd⟩ := List.mem_iff_getElem?.1 hb
    obtain ⟨lg, b0, hlg, hb0, -, rfl⟩ := h.block hd
    obtain ⟨b0', bo, hb0', -, -, -, hto⟩ := h.done d lg hlg
    exact hto.brt

/-- **The guard facts of the simplify stage** (`F0`: the pipeline's input). -/
theorem RunDone.guard {F0 : Function}
    (h : RunDone f info (allowedIn F0) (skelAllowedIn F0) st S out logs) :
    SimpGuard F0 f (outFn f out) where
  hdr := ⟨rfl, rfl, rfl, rfl, rfl⟩
  len := by simp [h.outEq.1]
  blk i b b' hb hb' := by
    obtain ⟨lg, b0, hlg, hb0, -, rfl⟩ := h.block hb'
    rw [hb] at hb0; cases hb0
    obtain ⟨b0', bo, hb0', -, -, -, hto⟩ := h.done i lg hlg
    rw [hb] at hb0'; cases hb0'
    obtain ⟨-, hos⟩ := h.outs i _ ((h.view i).trans hb')
    refine ⟨rfl, hto.guard, fun s hs => ?_, fun s0 hs0 hci => ?_⟩
    · obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hs
      rcases (hos k s hk).guard with ⟨b1, hb1, s0, hs0, τ, he⟩ | hn
      · rw [hb] at hb1; cases hb1; exact .inl ⟨s0, hs0, τ, he⟩
      · exact .inr hn
    · obtain ⟨t, ht, he⟩ := h.callInd i lg b hlg hb s0 hs0 hci
      refine ⟨t, ?_, S.step, he⟩
      simp only [outsOf] at ht
      simp [ht]

/-- **Completeness of simplify from the end of its run**: the validator accepts the output, `check`
accepts it once its unreachable blocks are removed, and the guard facts hold. -/
theorem simp_complete_of_run {F0 : Function} (hc : Checked f info)
    (hRun : RunDone f info (allowedIn F0) (skelAllowedIn F0) st S out logs) :
    simpOk f (S.apply (outFn f out)) info
        { defs := st.defs, types := st.types, subst := S, logs } = true ∧
      (∃ i, check (removeUnreachable (S.apply (outFn f out))) = .ok i) ∧
      SimpGuard F0 f (S.apply (outFn f out)) := by
  rw [hRun.apply_eq]
  exact ⟨hRun.simpOk hc, ⟨_, hRun.recheck hc⟩, hRun.guard⟩

end Assemble

end Opt
