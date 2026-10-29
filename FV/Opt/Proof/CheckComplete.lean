module

public import FV.Opt.Proof.CompleteDce

@[expose] public section

/-!
# `checkCore` from the certificate facts, and facts of `Cfg.build` (M1)

`Opt.coreOk_of_wf`: on a function whose CFG facts, definitions, entry parameters, branch argument
types and `br_table` index types are right, the certificate facts `Wf f (wfData f (coreInfo f))`
make the imperative part of `check` accept. Its core is the completeness of `Cfg.dominates`
(`Opt.dominates_complete`: the walk up `idom` finds every tree ancestor within its fuel).

CFG facts the completeness proofs of the passes use: `Cfg.postorder` lists every block at most
once (`Opt.postorder_nodup`), so the dominator-tree children lists `Cfg.domChildren` are distinct
blocks whose `idom` is the parent (`Opt.domChildren_spec`); the dominator array has one entry per
block (`Opt.build_idom_size`).
-/

namespace Opt

open Clif

theorem getElem!_opt (arr : Array (Option Nat)) (x : Nat) : arr[x]! = arr[x]?.join := by
  by_cases h : x < arr.size
  · simp [getElem!_def, h]
  · simp [getElem!_def, h]; rfl

/-- The loop of `Cfg.dominates`: a chain of `l.length` steps from `x` up to `a` is found. -/
theorem dominates_loop (idom : Array (Option Nat)) (a : Nat) :
    ∀ (n : List Nat) (chain : List Nat) (x : Nat), ChainTo idom chain a x → chain.length < n.length →
      (forIn (m := Id) n ((none : Option Bool), x) fun _ s =>
        if (s.snd == a) = true then pure (ForInStep.done (some true, s.snd))
        else match idom[s.snd]! with
          | some y => pure (ForInStep.yield (none, y))
          | none => pure (ForInStep.done (some false, s.snd))).run.fst = some true
  | [], _, _, _, h => by simp at h
  | _ :: n, [], x, hc, _ => by
    simp only [ChainTo] at hc; subst hc
    simp [List.forIn_cons]
  | _ :: n, y :: chain, x, hc, hl => by
    obtain ⟨rfl, c, hcx, hch⟩ := hc
    rw [List.forIn_cons]
    by_cases hxa : y = a
    · subst hxa; simp
    · have hne : (y == a) = false := by simpa using hxa
      have hcx' : idom[y]! = some c := by rw [getElem!_opt]; exact hcx
      simp only [hne, Bool.false_eq_true, ite_false, hcx', pure_bind]
      exact dominates_loop idom a n chain c hch (by simp at hl ⊢; omega)

/-- **`Cfg.dominates` is complete**: a tree ancestor dominates (both blocks reachable, ranks
decreasing along `idom`). -/
theorem dominates_complete {c : Cfg} {rank : Nat → Nat}
    (hr : ∀ b x, c.idom[b]?.join = some x → rank x < rank b) (hsz : c.idom.size ≤ c.size)
    {a b : Nat} (ha : c.reachable a = true) (hb : c.reachable b = true) (h : Anc c.idom a b) :
    c.dominates a b = true := by
  unfold Cfg.dominates
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', ha, hb, Bool.not_true, Bool.or_false,
    Bool.false_eq_true, ite_false]
  obtain ⟨l, hl⟩ := h.chain
  have hlen : l.length ≤ c.idom.size := by
    have := (ChainTo.nodup hr l hl).length_le_of_subset (l₂ := List.range c.idom.size)
      (fun x hx => List.mem_range.2 (ChainTo.lt l hl x hx))
    simpa using this
  have := dominates_loop c.idom a (List.range' 0 [:c.size + 1].size) l b hl
    (by simp [Std.Legacy.Range.size]; omega)
  simp only [Id.run] at this
  generalize hF : forIn (m := Id) (List.range' 0 [:c.size + 1].size) ((none : Option Bool), b) _ = F at this
  rcases F with ⟨o, n⟩
  simp only at this
  subst this
  rfl

theorem paramSeen_contains (b : Block) (v : ValueId) :
    (paramSeen b).contains v = true ↔ v ∈ b.params.map (·.1) := by
  unfold paramSeen
  suffices ∀ (l : List (ValueId × Ty)) (s : Std.HashSet ValueId),
      (l.foldl (fun s p => s.insert p.1) s).contains v = true ↔ s.contains v = true ∨ v ∈ l.map (·.1) by
    simpa using this b.params ∅
  intro l
  induction l with
  | nil => simp
  | cons p l ih =>
    intro s
    rw [List.foldl_cons, ih]
    simp only [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq, List.map_cons, List.mem_cons]
    constructor
    · rintro ((h | h) | h)
      · exact .inr (.inl h.symm)
      · exact .inl h
      · exact .inr (.inr h)
    · rintro (h | h | h)
      · exact .inl (.inr h)
      · exact .inl (.inl h.symm)
      · exact .inr h

theorem seen_take (b : Block) (v : ValueId) : ∀ j,
    ((b.body.take j).foldl seenStep (paramSeen b)).contains v = true ↔
      v ∈ b.params.map (·.1) ∨ ∃ j0 st0, j0 < j ∧ b.body[j0]? = some st0 ∧ v ∈ st0.results := by
  intro j
  generalize b.body = body
  suffices ∀ (s : Std.HashSet ValueId), ((body.take j).foldl seenStep s).contains v = true ↔
      s.contains v = true ∨ ∃ j0 st0, j0 < j ∧ body[j0]? = some st0 ∧ v ∈ st0.results by
    rw [this, paramSeen_contains]
  induction body generalizing j with
  | nil => intro s; simp
  | cons st body ih =>
    intro s
    cases j with
    | zero => simp
    | succ j =>
      rw [List.take_succ_cons, List.foldl_cons, ih j, seenStep_contains]
      constructor
      · rintro ((h | h) | ⟨j0, st0, hj, h0, hv⟩)
        · exact .inl h
        · exact .inr ⟨0, st, by omega, rfl, h⟩
        · exact .inr ⟨j0 + 1, st0, by omega, by simpa using h0, hv⟩
      · rintro (h | ⟨j0, st0, hj, h0, hv⟩)
        · exact .inl (.inl h)
        · cases j0 with
          | zero => simp at h0; subst h0; exact .inl (.inr hv)
          | succ j0 => exact .inr ⟨j0, st0, by omega, by simpa using h0, hv⟩

/-- `checkCore`'s defining block of a defined value. -/
theorem defBlock_of_site {f : Function} (ha : Arity f) (hn : ((defList f).map (·.1)).Nodup)
    {v : ValueId} {d t : Nat} (hs : (v, (d, t)) ∈ defSites f) : (defsState f).2.1[v]? = some d := by
  obtain ⟨i, b, hb, ⟨p, hp, rfl, he⟩ | ⟨j, st, hj, hv, he⟩⟩ := mem_defSites.1 hs
  · simp only [Prod.mk.injEq] at he; obtain ⟨hdi, -⟩ := he
    subst hdi
    exact ((defsState_get f hn).1 (p.1, p.2, d) (mem_defList.2 ⟨d, b, hb, .inl ⟨p, hp, rfl⟩⟩)).2
  · simp only [Prod.mk.injEq] at he; obtain ⟨hdi, -⟩ := he
    subst hdi
    have hst := List.mem_of_getElem? hj
    obtain ⟨ts, hts, hlen⟩ := ha b (List.mem_of_getElem? hb) st hst
    have hm : v ∈ (stmtEvs f d st).map (·.1) := by rw [stmtEvs_map_fst hts hlen]; exact hv
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hm
    have hb' : e.2.2 = d := by
      unfold stmtEvs at he; rw [hts] at he
      obtain ⟨_, _, rfl⟩ := List.mem_map.1 he; rfl
    rw [← hb']
    exact ((defsState_get f hn).1 e (mem_defList.2 ⟨d, b, hb, .inr ⟨st, hst, he⟩⟩)).2

theorem forIn_inv {α σ : Type} (l : List α) (init : σ) (f : α → σ → Id (ForInStep σ)) (P : σ → Prop)
    (h0 : P init) (hf : ∀ a s, P s → P (f a s).run.value) : P (forIn l init f).run := by
  induction l generalizing init with
  | nil => simpa using h0
  | cons a l ih =>
    rw [List.forIn_cons]
    have := hf a init h0
    cases hfa : f a init with
    | done b => rw [hfa] at this; simp only [Id.run_bind]; exact this
    | yield b => rw [hfa] at this; simp only [Id.run_bind]; exact ih b this

theorem dominators_size (preds : Array (List Nat)) rpo rpoNum : (Cfg.dominators preds rpo rpoNum).size = preds.size := by
  unfold Cfg.dominators
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range']
  split
  · rename_i h; simp only [beq_iff_eq] at h; simp [h]; rfl
  · rw [bind_pure_comp]
    simp only [Functor.map, Array.size_set!]
    refine forIn_inv (P := fun s : Array (Option Nat) => s.size = preds.size) _ _ _ (by simp) ?_
    intro a s hs
    simp only [Id.run_bind]
    split <;> simp only [Id.run_pure, ForInStep.value] <;>
    · rw [← Array.forIn_toList]
      refine forIn_inv (P := fun p : Array (Option Nat) × Bool => p.1.size = preds.size) _ _ _ ?_ ?_
      · exact hs
      intro b p hp
      split
      · simpa using hp
      · simp only [Id.run_bind]
        split <;> simp [hp]
theorem build_idom_eq (f : Function) : (Cfg.build f).idom =
    Cfg.dominators (Cfg.build f).preds (Cfg.build f).rpo (Cfg.build f).rpoNum := rfl

theorem build_preds_size (f : Function) : (Cfg.build f).preds.size = f.blocks.length := by
  unfold Cfg.build
  simp only [Id.run_bind, pure_bind, Array.forIn_pure_yield_eq_foldl, List.forIn_pure_yield_eq_foldl,
    Id.run_pure]
  rw [← Array.foldl_toList]
  have inner : ∀ (ss : List Nat) (i : Nat) (p : Array (List Nat)),
      (ss.foldl (fun b a => b.modify a fun y => y ++ [i]) p).size = p.size := by
    intro ss i
    induction ss with
    | nil => intro p; rfl
    | cons s ss ih => intro p; rw [List.foldl_cons, ih, Array.size_modify]
  have key : ∀ (l : List (List Nat × Nat)) (p : Array (List Nat)),
      (l.foldl (fun p x => x.1.foldl (fun b a => b.modify a fun y => y ++ [x.2]) p) p).size = p.size := by
    intro l
    induction l with
    | nil => intro p; rfl
    | cons x l ih => intro p; rw [List.foldl_cons, ih, inner]
  rw [key]
  simp
theorem build_idom_size (f : Function) : (Cfg.build f).idom.size ≤ (Cfg.build f).size := by
  rw [build_idom_eq, dominators_size, build_preds_size]
  simp [Cfg.size, Cfg.build]

/-- **`checkCore` from the certificate facts** (module doc). -/
theorem coreOk_of_wf {f : Function}
    (hsz : 0 < (Cfg.build f).size) (hidx : (Cfg.build f).index.size = (Cfg.build f).size)
    (hreach : ∀ i < (Cfg.build f).size, (Cfg.build f).reachable i = true)
    (hdefs : DefsOk f)
    (hentry : f.blocks.toArray[0]!.params.map (·.2) = f.sig.params.map (·.ty))
    (hW : Wf f (wfData f (coreInfo f)))
    (hcalls : ∀ (i : Nat) (b : Block), f.blocks[i]? = some b → ∀ bc ∈ termCalls b.term, callOk f (defsState f).1 bc)
    (hbr : ∀ b ∈ f.blocks, brTableOk (defsState f).1 b.term) : CoreOk f := by
  obtain ⟨ha, hd⟩ := (defsOk_iff f).1 hdefs
  have hn := ((allAlong_evC_iff _ _).1 hd).2
  have hsizeB : (Cfg.build f).size = f.blocks.length := by simp [Cfg.size, Cfg.build]
  -- availability as `checkCore` checks it
  have hav : ∀ i b, f.blocks[i]? = some b → ∀ j v, j ≤ b.body.length →
      Avail (wfData f (coreInfo f)) i j v →
      availCk f (defsState f).2.1 i ((b.body.take j).foldl seenStep (paramSeen b)) v = true := by
    intro i b hb j v hj hA
    obtain ⟨d, t, hdm, h⟩ := hA
    have hs := hW.sitesRev v (d, t) hdm
    unfold availCk
    simp only [Bool.or_eq_true]
    rcases h with ⟨hdi, ht⟩ | ⟨hne, hanc⟩
    · left
      rw [seen_take]
      obtain ⟨i', b', hb', ⟨p, hp, hpv, he⟩ | ⟨j0, st0, h0, hv, he⟩⟩ := mem_defSites.1 hs
      · simp only [Prod.mk.injEq] at he
        rw [← he.1, hdi, hb] at hb'; cases hb'
        exact .inl (List.mem_map.2 ⟨p, hp, hpv⟩)
      · simp only [Prod.mk.injEq] at he
        rw [← he.1, hdi, hb] at hb'; cases hb'
        exact .inr ⟨j0, st0, by omega, h0, hv⟩
    · right
      rw [Std.HashMap.get?_eq_getElem?, defBlock_of_site ha hn hs]
      rw [Bool.and_eq_true, bne_iff_ne]
      refine ⟨hne, ?_⟩
      have hdl : d < f.blocks.length := by
        obtain ⟨i'', b'', hb'', h⟩ := mem_defSites.1 hs
        rcases h with ⟨_, _, _, he⟩ | ⟨_, _, _, _, he⟩ <;>
        · simp only [Prod.mk.injEq] at he; obtain ⟨rfl, -⟩ := he
          exact (List.getElem?_eq_some_iff.1 hb'').1
      have hil : i < f.blocks.length := (List.getElem?_eq_some_iff.1 hb).1
      exact dominates_complete hW.rank (build_idom_size f) (hreach d (by omega)) (hreach i (by omega))
        hanc
  refine ⟨hsz, hidx, hreach, hdefs, hentry, fun x hx => ?_⟩
  obtain ⟨b, i⟩ := x
  have hb : f.blocks[i]? = some b := List.mem_zipIdx_iff_getElem?.1 hx
  refine ⟨?_, fun v hv => ?_, hcalls i b hb, hbr b (List.mem_of_getElem? hb)⟩
  · rw [allAlong_iff]
    intro j st hst
    have hjl : j < b.body.length := (List.getElem?_eq_some_iff.1 hst).1
    refine ⟨fun v hv => hav i b hb j v (by omega) (hW.uses i b hb j st hst v hv), fun hp => ?_⟩
    have := hW.pure i b hb j st hst hp
    simpa [wfData, coreInfo] using this
  · have := hav i b hb b.body.length v (Nat.le_refl _) (hW.termUses i b hb v hv)
    rwa [List.take_length] at this

theorem forIn_inv' {α σ : Type} (l : List α) (init : σ) (f : α → σ → Id (ForInStep σ)) (P Q : σ → Prop)
    (h0 : P init) (hf : ∀ a s, P s → P (f a s).run.value) (hPQ : ∀ s, P s → Q s) :
    Q (forIn l init f).run := hPQ _ (forIn_inv l init f P h0 hf)

/-- The blocks of a DFS state: finished, then on the stack. -/
def dfsBlocks (s : DfsSt) : List Nat := s.2.2.toList ++ s.2.1.toList.map (·.1)

/-- The postorder lists every block at most once. -/
theorem postorder_nodup (succs : Array (List Nat))
    (hS : ∀ i < succs.size, ∀ x ∈ succs[i]!, x < succs.size) : (Cfg.postorder succs).toList.Nodup := by
  unfold Cfg.postorder
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range']
  split
  · exact List.nodup_nil
  · rename_i hn
    rw [bind_pure_comp]
    simp only [Functor.map]
    refine forIn_inv' _ _ _
      (P := fun s : DfsSt => (dfsBlocks s).Nodup ∧ (∀ x ∈ dfsBlocks s, s.1[x]! = true) ∧
        s.1.size = succs.size ∧ ∀ fr ∈ s.2.1.toList, ∀ y ∈ fr.2, y < succs.size)
      (Q := fun s : DfsSt => s.2.2.toList.Nodup) ?_ ?_ ?_
    · have h0 : 0 < (Array.replicate succs.size false).size := by
        simp only [Array.size_replicate]
        exact Nat.pos_of_ne_zero (by intro h; simp [h] at hn)
      refine ⟨by simp [dfsBlocks], fun x hx => ?_, by simp, fun fr hfr y hy => ?_⟩
      · simp [dfsBlocks] at hx; subst hx
        rw [getElem!_set_true h0]; simp
      · simp at hfr; subst hfr
        exact hS 0 (by simp at h0; omega) y hy
    · rintro - ⟨vis, st, post⟩ ⟨hnd, hvis, hsz, hfr⟩
      simp only [dfsBlocks] at hnd hvis hsz hfr
      cases hb : st.back? with
      | none => simpa [hb, dfsBlocks] using And.intro hnd (And.intro hvis (And.intro hsz hfr))
      | some fr =>
        obtain ⟨b, ss⟩ := fr
        have hst := back?_toList hb
        rw [hst] at hnd hvis hfr
        have hfr' : ∀ fr ∈ st.pop.toList, ∀ y ∈ fr.2, y < succs.size :=
          fun fr h => hfr fr (List.mem_append_left _ h)
        have hbs : ∀ y ∈ ss, y < succs.size := hfr (b, ss) (by simp)
        cases ss with
        | nil =>
          simp only [hb, Id.run_pure, ForInStep.value, dfsBlocks, Array.toList_push]
          have hperm : (post.toList ++ [b] ++ st.pop.toList.map (fun p : Nat × List Nat => p.1)).Perm
              (post.toList ++ (st.pop.toList ++ [(b, [])]).map (fun p : Nat × List Nat => p.1)) := by
            simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc]
            exact List.Perm.append_left _ (List.perm_append_comm)
          exact ⟨hperm.nodup_iff.2 hnd, fun x hx => hvis x (hperm.subset hx), hsz, hfr'⟩
        | cons x rest =>
          simp only [hb]
          by_cases hvx : vis[x]! = true
          · simp only [hvx, Bool.not_true, Bool.false_eq_true, ite_false, Id.run_pure,
              ForInStep.value, dfsBlocks, Array.toList_push]
            simp only [List.map_append, List.map_cons, List.map_nil] at hnd hvis ⊢
            refine ⟨hnd, hvis, hsz, fun fr h y hy => ?_⟩
            simp only [List.mem_append, List.mem_singleton] at h
            rcases h with h | rfl
            · exact hfr' fr h y hy
            · exact hbs y (List.mem_cons_of_mem _ hy)
          · have hvf : vis[x]! = false := by simpa using hvx
            simp only [hvf, Bool.not_false, ite_true, Id.run_pure, ForInStep.value, dfsBlocks,
              Array.toList_push]
            simp only [List.map_append, List.map_cons, List.map_nil] at hnd hvis ⊢
            have hxL : x ∉ post.toList ++ (st.pop.toList.map (·.1) ++ [b]) := by
              intro hx; have := hvis x hx; rw [hvf] at this; cases this
            have hxs : x < vis.size := hsz ▸ hbs x (List.mem_cons_self ..)
            refine ⟨?_, fun y hy => ?_, by simp [hsz], fun fr h y hy => ?_⟩
            · have : (post.toList ++ (st.pop.toList.map (·.1) ++ [b] ++ [x])) =
                  (post.toList ++ (st.pop.toList.map (·.1) ++ [b])) ++ [x] := by simp
              rw [this, List.nodup_append]
              exact ⟨hnd, by simp, fun a ha c hc => by
                simp at hc; subst hc; exact fun h => hxL (h ▸ ha)⟩
            · have hy' : y = x ∨ y ∈ post.toList ++ (st.pop.toList.map (fun p : Nat × List Nat => p.1) ++ [b]) := by
                rcases List.mem_append.1 hy with h | h
                · exact .inr (List.mem_append.2 (.inl h))
                · rcases List.mem_append.1 h with h | h
                  · exact .inr (List.mem_append.2 (.inr h))
                  · exact .inl (by simpa using h)
              rw [getElem!_set_true hxs]
              rcases hy' with rfl | hy'
              · simp
              · simp [hvis y hy']
            · simp only [List.mem_append, List.mem_singleton] at h
              rcases h with (h | rfl) | rfl
              · exact hfr' fr h y hy
              · exact hbs y (List.mem_cons_of_mem _ hy)
              · exact hS x (hsz ▸ hxs) y hy
    · exact fun s h => h.1.sublist (List.sublist_append_left _ _)


theorem getElem!_modify_list (ch : Array (List Nat)) (d0 d : Nat) (g : List Nat → List Nat) :
    (ch.modify d0 g)[d]! = if d0 = d ∧ d0 < ch.size then g ch[d]! else ch[d]! := by
  simp only [getElem!_def, Array.getElem?_modify]
  by_cases h1 : d0 = d
  · subst h1
    by_cases h2 : d0 < ch.size
    · simp [h2]
    · simp [h2, Array.getElem?_eq_none (Nat.le_of_not_lt h2)]
  · simp [h1]

/-- The children lists of the dominator tree: distinct blocks of `rpo` whose `idom` is the
parent. -/
theorem domChildren_spec (c : Cfg) (hn : c.rpo.toList.Nodup) (d : Nat) :
    (c.domChildren[d]!).Nodup ∧ ∀ x ∈ c.domChildren[d]!, x ∈ c.rpo.toList ∧ c.idom[x]! = some d := by
  unfold Cfg.domChildren
  simp only [Id.run]
  rw [← Array.forIn_toList]
  have hn' : c.rpo.reverse.toList.Nodup := by
    rw [Array.toList_reverse]; exact (List.reverse_perm _).nodup_iff.2 hn
  have hsub : ∀ x ∈ c.rpo.reverse.toList, x ∈ c.rpo.toList := by simp
  generalize c.rpo.reverse.toList = L at hn' hsub
  have key : ∀ (B : Nat → Array (List Nat) → Id (ForInStep (Array (List Nat)))),
      (∀ b r, B b r = pure (ForInStep.yield (match c.idom[b]! with
        | some d => r.modify d (b :: ·)
        | none => r))) →
      ∀ (L : List Nat) (ch : Array (List Nat)), L.Nodup → (∀ x ∈ L, x ∈ c.rpo.toList) →
      (∀ d, (ch[d]!).Nodup ∧ (∀ x ∈ ch[d]!, x ∈ c.rpo.toList ∧ c.idom[x]! = some d) ∧
        ∀ x ∈ ch[d]!, x ∉ L) →
      ∀ d, ((forIn (m := Id) L ch B).run[d]!).Nodup ∧
        ∀ x ∈ (forIn (m := Id) L ch B).run[d]!, x ∈ c.rpo.toList ∧ c.idom[x]! = some d := by
    intro B hB
    intro L
    induction L with
    | nil => intro ch _ _ h d; exact ⟨(h d).1, (h d).2.1⟩
    | cons b L ih =>
      intro ch hn hs h d
      have hbL := (List.nodup_cons.1 hn).1
      rw [List.forIn_cons, hB]
      cases hb : c.idom[b]! with
      | none =>
        simp only [hb, pure_bind]
        exact ih ch (List.nodup_cons.1 hn).2 (fun x hx => hs x (List.mem_cons_of_mem _ hx))
          (fun d => ⟨(h d).1, (h d).2.1, fun x hx hxL => (h d).2.2 x hx (List.mem_cons_of_mem _ hxL)⟩) d
      | some d0 =>
        simp only [hb, pure_bind]
        refine ih _ (List.nodup_cons.1 hn).2 (fun x hx => hs x (List.mem_cons_of_mem _ hx)) ?_ d
        intro d'
        rw [getElem!_modify_list]
        split
        · rename_i hd
          obtain ⟨rfl, -⟩ := hd
          refine ⟨List.nodup_cons.2 ⟨fun hb' => (h d0).2.2 b hb' (List.mem_cons_self ..), (h d0).1⟩,
            fun x hx => ?_, fun x hx hxL => ?_⟩
          · rcases List.mem_cons.1 hx with rfl | hx
            · exact ⟨hs x (List.mem_cons_self ..), hb⟩
            · exact (h d0).2.1 x hx
          · rcases List.mem_cons.1 hx with rfl | hx
            · exact hbL hxL
            · exact (h d0).2.2 x hx (List.mem_cons_of_mem _ hxL)
        · exact ⟨(h d').1, (h d').2.1, fun x hx hxL => (h d').2.2 x hx (List.mem_cons_of_mem _ hxL)⟩
  simp only [bind_pure]
  refine key _ (fun b r => ?_) L _ hn' hsub ?_ d
  · cases h : c.idom[b]! <;> simp [h]
  intro d
  have : (Array.replicate c.size ([] : List Nat))[d]! = [] := by
    by_cases hd : d < c.size
    · simp [getElem!_def, Array.getElem?_replicate, hd]
    · simp [getElem!_def, Array.getElem?_replicate, hd]; rfl
  rw [this]; simp

theorem build_succs_size (f : Function) : (Cfg.build f).succs.size = f.blocks.length := by
  simp [build_succs]

/-- Successors are blocks. -/
theorem build_succs_lt (f : Function) : ∀ i < (Cfg.build f).succs.size, ∀ x ∈ (Cfg.build f).succs[i]!,
    x < (Cfg.build f).succs.size := by
  intro i hi x hx
  rw [build_succs_size] at hi ⊢
  rw [build_succs] at hx
  simp only [getElem!_def, Array.getElem?_map, List.getElem?_toArray] at hx
  rw [List.getElem?_eq_getElem hi] at hx
  simp only [Option.map_some] at hx
  have hx := List.mem_eraseDups.1 hx
  obtain ⟨id, _, hid⟩ := List.mem_filterMap.1 hx
  exact (build_index_lt hid).1

theorem build_rpo_nodup (f : Function) : (Cfg.build f).rpo.toList.Nodup := by
  rw [build_rpo, Array.toList_reverse]
  exact (List.reverse_perm _).nodup_iff.2 (postorder_nodup _ (build_succs_lt f))

theorem build_rpo_lt (f : Function) {x : Nat} (hx : x ∈ (Cfg.build f).rpo.toList) :
    x < f.blocks.length := by
  rw [build_rpo, Array.toList_reverse, List.mem_reverse] at hx
  by_cases hn : (Cfg.build f).succs.size = 0
  · unfold Cfg.postorder at hx
    simp [hn, Id.run] at hx
    exact absurd hx (by simp [pure])
  · have := (postorder_closed _ (build_succs_lt f) hn).2 x hx
    rw [build_succs_size] at this
    exact this.1

end Opt
