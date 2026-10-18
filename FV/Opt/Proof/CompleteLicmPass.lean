import FV.Opt.Proof.CompleteLicm

/-!
# Completeness of the LICM stage: the pass (M1)

`Opt.licm_complete`: on a well-formed function (`check g = .ok info`), the output of `Opt.licm`
passes `check` and the edit validator `editOk id`, so `Opt.optimizeReport` never stops at the
LICM stage.

The proof views every loop of `Opt.licmRound` as a sequence of single moves (`Opt.moveF`: a pure
single-result statement goes to the end of the hoist block `idom header`), each with the
preconditions of `Opt.MoveOk` (`FV/Opt/Proof/CompleteLicm.lean`): an operand that is not defined
inside the loop (the pass's `inside` set) is defined in a strict tree ancestor of the header
(`Opt.loop_between`), hence available at the end of the hoist block; an operand defined by a
statement hoisted earlier in the same loop sits earlier in the hoist block. During a loop the
state is `hoistF F0 hb H`: the loop's start function with the hoisted statements `H` filtered out
of every body and appended to `hb`; one more hoisted statement is one more move
(`Opt.hoistF_snoc`).

The moves keep `Opt.Good` (the certificate facts, unique definitions, arities: `MoveOk.wf'`,
`MoveOk.unique'`, `MoveOk.arity'`) and the relation `Opt.LRel g F` to the input `g` across moves,
loops and rounds: the blocks keep their ids, parameters and terminators, the types of the values
are unchanged, and each body is the input body without the moved statements `M`, followed by moved
statements; every moved statement sits in a strict tree ancestor of its original block. This is
what `editOk id` checks (`Opt.align_filter_append`); `check` follows from `Good` by
`Opt.coreOk_of_wf`.
-/

namespace Opt

open Clif

/-! ## The dominator tree records blocks -/

/-- `Cfg.dominators` only records blocks. -/
theorem dominators_lt (preds : Array (List Nat)) (rpo : Array Nat) (rpoNum : Array (Option Nat))
    (hpr : ∀ b : Nat, ∀ p ∈ preds[b]!, p < preds.size) :
    ∀ b x : Nat, (Cfg.dominators preds rpo rpoNum)[b]?.join = some x → x < preds.size := by
  let Inv := fun a : Array (Option Nat) => ∀ b x : Nat, a[b]?.join = some x → x < preds.size
  have hset : ∀ a b o, Inv a → (∀ x, o = some x → x < preds.size) → Inv (a.set! b o) := by
    intro a b o ha ho c x hc
    simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds] at hc
    split at hc
    · split at hc
      · exact ho x (by simpa using hc)
      · simp at hc
    · exact ha c x hc
  have hgetD : ∀ (a : Array (Option Nat)) (y : Nat), Inv a → 0 < preds.size →
      a[y]!.getD 0 < preds.size := by
    intro a y ha hn
    rw [getElem!_opt]
    cases h : a[y]?.join with
    | none => exact hn
    | some z => exact ha y z h
  unfold Cfg.dominators
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range']
  split
  · intro b x h; change (#[] : Array (Option Nat))[b]?.join = some x at h; simp at h
  · rename_i hn
    have hn0 : 0 < preds.size := by
      rcases Nat.eq_zero_or_pos preds.size with h | h
      · simp [h] at hn
      · exact h
    rw [bind_pure_comp]
    simp only [Functor.map]
    show Inv _
    refine hset _ _ _ ?_ (by simp)
    refine forIn_inv (P := Inv) _ _ _ (hset _ _ _ (by
      intro b x h; simp only [Array.getElem?_replicate] at h; split at h <;> simp at h)
      (by simpa using hn0)) ?_
    intro _ s hs
    simp only [Id.run_bind]
    split
    all_goals
      simp only [Id.run_pure, ForInStep.value]
      rw [← Array.forIn_toList]
      refine forIn_inv (P := fun p : Array (Option Nat) × Bool => Inv p.1) _ _ _ hs ?_
      intro b p hp
      split
      · exact hp
      · simp only [Id.run_bind]
        split
        · refine hset _ _ _ hp ?_
          refine forIn_inv_mem (P := fun o : Option Nat => ∀ x, o = some x → x < preds.size) _ _ _
            (by simp) ?_
          intro q hq o ho
          split
          · exact ho
          · split
            · intro x hx; simp at hx; subst hx; exact hpr b q hq
            · simp only [Id.run_bind, Id.run_pure, ForInStep.value]
              intro x hx
              simp only [Option.some.injEq] at hx
              subst hx
              refine (forIn_inv (P := fun c : Nat × Nat => c.1 < preds.size ∧ c.2 < preds.size)
                _ _ _ ⟨hpr b q hq, ho _ rfl⟩ ?_).1
              intro _ c hc
              split
              · exact hc
              · split
                · exact ⟨hgetD _ _ hp hn0, hc.2⟩
                · exact ⟨hc.1, hgetD _ _ hp hn0⟩
        · exact hp

/-- The immediate dominator of a block is a block. -/
theorem build_idom_lt (f : Function) {b x : Nat} (h : (Cfg.build f).idom[b]?.join = some x) :
    x < f.blocks.length := by
  rw [build_idom_eq] at h
  have := dominators_lt _ _ _ (fun b p hp => by
    rw [build_preds_size]
    by_cases hb : b < f.blocks.length
    · exact ((build_preds_mem f hb).1 hp).1
    · have : (Cfg.build f).preds[b]! = [] := by
        have hs := build_preds_size f
        simp [getElem!_def, Array.getElem?_eq_none (by omega : (Cfg.build f).preds.size ≤ b)]; rfl
      rw [this] at hp; cases hp) b x h
  rwa [build_preds_size] at this

/-! ## Unique statements -/

/-- A statement with a result occurs once in a function whose values are defined once. -/
theorem stmt_unique {F : Function} (hu : UniqueDefs F) {i j k k' : Nat} {b b' : Block} {s : Stmt}
    (hb : F.blocks[i]? = some b) (hb' : F.blocks[j]? = some b') (hk : b.body[k]? = some s)
    (hk' : b'.body[k']? = some s) (hr : s.results ≠ []) : i = j ∧ k = k' := by
  obtain ⟨r, hr'⟩ := List.exists_mem_of_ne_nil _ hr
  have := site_unique hu (mem_defSites.2 ⟨i, b, hb, .inr ⟨k, s, hk, hr', rfl⟩⟩)
    (mem_defSites.2 ⟨j, b', hb', .inr ⟨k', s, hk', hr', rfl⟩⟩)
  simpa using this

theorem stmt_unique_mem {F : Function} (hu : UniqueDefs F) {i j : Nat} {b b' : Block} {s : Stmt}
    (hb : F.blocks[i]? = some b) (hb' : F.blocks[j]? = some b') (hk : s ∈ b.body)
    (hk' : s ∈ b'.body) (hr : s.results ≠ []) : i = j := by
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hk
  obtain ⟨k', hk'⟩ := List.mem_iff_getElem?.1 hk'
  exact (stmt_unique hu hb hb' hk hk' hr).1

/-! ## The state of a loop: hoisted statements filtered out and appended to the hoist block -/

/-- Filter `H` out of a body and append it to block `hb`. -/
def hoistB (hb : Nat) (H : List Stmt) (x : Block × Nat) : Block :=
  { x.1 with body := x.1.body.filter (· ∉ H) ++ (if x.2 = hb then H else []) }

def hoistF (F : Function) (hb : Nat) (H : List Stmt) : Function :=
  { F with blocks := F.blocks.zipIdx.map (hoistB hb H) }

theorem hoistF_get (F : Function) (hb : Nat) (H : List Stmt) (i : Nat) :
    (hoistF F hb H).blocks[i]? = (F.blocks[i]?).map fun b => hoistB hb H (b, i) := by
  simp only [hoistF, List.getElem?_map, List.getElem?_zipIdx]
  cases F.blocks[i]? <;> simp

theorem hoistF_nil (F : Function) (hb : Nat) : hoistF F hb [] = F := by
  have : F.blocks.zipIdx.map (hoistB hb []) = F.blocks := by
    apply List.ext_getElem?
    intro i
    simp only [List.getElem?_map, List.getElem?_zipIdx]
    cases F.blocks[i]? with
    | none => rfl
    | some b =>
      have : b.body.filter (· ∉ ([] : List Stmt)) = b.body := List.filter_eq_self.2 (by simp)
      simp only [Option.map_some, hoistB, this, List.append_nil, ite_self]
  show { F with blocks := _ } = F
  rw [this]

/-- One more hoisted statement is one more move. -/
theorem hoistF_snoc (F : Function) (hb : Nat) (H : List Stmt) (t : Stmt) (ht : t ∉ H) :
    moveF (hoistF F hb H) hb t = hoistF F hb (H ++ [t]) := by
  have hH : H.filter (· != t) = H := List.filter_eq_self.2 fun s hs => by
    simp only [bne_iff_ne, ne_eq]; rintro rfl; exact ht hs
  have hf : (fun a => (a != t) && decide (a ∉ H)) = fun a => decide (a ∉ H ++ [t]) := by
    funext a
    by_cases hat : a = t
    · subst hat; simp
    · simp [hat]
  have : (hoistF F hb H).blocks.zipIdx.map (moveB hb t) = F.blocks.zipIdx.map (hoistB hb (H ++ [t])) := by
    apply List.ext_getElem?
    intro i
    simp only [List.getElem?_map, List.getElem?_zipIdx]
    rw [show (hoistF F hb H).blocks[i]? = _ from hoistF_get F hb H i]
    cases F.blocks[i]? with
    | none => simp
    | some b =>
      simp only [Option.map_some, Option.some.injEq, moveB, hoistB]
      congr 1
      rw [List.filter_append, List.filter_filter, hf]
      split
      · rename_i h; simp [h, hH]
      · rename_i h; simp [h]
  unfold moveF
  rw [this]
  rfl

theorem align_nil (c : EditCtx) : ∀ (T : List Stmt), (∀ t ∈ T, insOk t = true) → ∀ k, c.align [] T k = true
  | [], _, k => by simp [EditCtx.align]
  | t :: T, hT, k => by
    rw [EditCtx.align, hT t (List.mem_cons_self ..), Bool.true_and]
    exact align_nil c T (fun t ht => hT t (List.mem_cons_of_mem _ ht)) _

/-! ## The alignment of a filtered body followed by inserted statements -/

/-- Alignment of a body with its filtered copy followed by inserted statements (`σ = id`). -/
theorem align_filter_append (c : EditCtx) (hσ : c.σ = id) (p : Stmt → Bool) (T : List Stmt)
    (hT : ∀ t ∈ T, insOk t = true) :
    ∀ (l : List Stmt), (∀ s ∈ l, p s = false → s ∉ T ∧ ∀ k, c.delOk s k = true) →
      ∀ k, c.align l (l.filter p ++ T) k = true
  | [], _, k => by
    simp only [List.filter_nil, List.nil_append]
    exact align_nil c T hT k
  | s :: l, hd, k => by
    have ih := align_filter_append c hσ p T hT l (fun s' hs' => hd s' (List.mem_cons_of_mem _ hs'))
    have hkeep : ∀ t, c.keepOk s t = true ↔ t = s := by
      intro t; simp [EditCtx.keepOk, hσ, renStmt_id]
    by_cases hp : p s = true
    · simp only [List.filter_cons, hp, ite_true, List.cons_append]
      rw [EditCtx.align]
      simp only [(hkeep s).2 rfl, ite_true]
      exact ih _
    · have hpf : p s = false := by simpa using hp
      simp only [List.filter_cons, hpf, Bool.false_eq_true, ite_false]
      obtain ⟨hsT, hdel⟩ := hd s (List.mem_cons_self ..) hpf
      cases hf : l.filter p ++ T with
      | nil => rw [EditCtx.align, hdel k, Bool.true_and, ← hf]; exact ih k
      | cons t ts =>
        have hne : c.keepOk s t = false := by
          cases hk : c.keepOk s t
          · rfl
          · rw [(hkeep t).1 hk] at hf
            have hm : s ∈ l.filter p ++ T := by rw [hf]; exact List.mem_cons_self ..
            rcases List.mem_append.1 hm with h | h
            · rw [(List.mem_filter.1 h).2] at hpf; cases hpf
            · exact absurd h hsT
        rw [EditCtx.align]
        simp only [hne, Bool.false_eq_true, ite_false, hdel k, ite_true]
        rw [← hf]
        exact ih k

/-! ## The invariants of the moves -/

/-- What `check` provides of a function, without the `CoreOk` part. -/
structure Good (F : Function) : Prop where
  unique : UniqueDefs F
  arity : Arity F
  nodup : ((defList F).map (·.1)).Nodup
  wf : Wf F (wfData F (coreInfo F))

theorem Checked.good {g : Function} {info : Info} (hc : Checked g info) : Good g :=
  ⟨hc.unique, hc.arity, hc.nodup, by have := hc.wf; rwa [hc.info_eq] at this⟩

/-- The relation of a state `F` of LICM to its input `g` (module doc): the same header and blocks
up to the bodies, the same types, and moved statements `M`. -/
structure LRel (g F : Function) : Prop where
  hdr : F = { g with blocks := F.blocks }
  len : F.blocks.length = g.blocks.length
  blk : ∀ (i : Nat) (b b' : Block), g.blocks[i]? = some b → F.blocks[i]? = some b' → b' = { b with body := b'.body }
  types : ∀ x : ValueId, (defsState F).1[x]? = (defsState g).1[x]?
  moved : ∃ M : List Stmt, (∀ t ∈ M, insOk t = true) ∧
    (∀ (i : Nat) (b b' : Block), g.blocks[i]? = some b → F.blocks[i]? = some b' →
      ∃ T : List Stmt, b'.body = b.body.filter (· ∉ M) ++ T ∧ ∀ t ∈ T, t ∈ M) ∧
    (∀ t ∈ M, ∃ (i0 : Nat) (b0 : Block) (d : Nat) (bd : Block), g.blocks[i0]? = some b0 ∧ t ∈ b0.body ∧ F.blocks[d]? = some bd ∧
      t ∈ bd.body ∧ d ≠ i0 ∧ Anc (Cfg.build g).idom d i0)

theorem LRel.refl (g : Function) : LRel g g := by
  refine ⟨rfl, rfl, fun i b b' hb hb' => ?_, fun _ => rfl, ⟨[], by simp, fun i b b' hb hb' => ?_, by simp⟩⟩
  · rw [hb] at hb'; cases hb'; rfl
  · rw [hb] at hb'; cases hb'
    exact ⟨[], by simp [List.filter_eq_self.2], by simp⟩

theorem LRel.get {g F : Function} (h : LRel g F) {i : Nat} {b' : Block} (hb' : F.blocks[i]? = some b') :
    ∃ b, g.blocks[i]? = some b ∧ b' = { b with body := b'.body } := by
  have hil : i < g.blocks.length := by rw [← h.len]; exact (List.getElem?_eq_some_iff.1 hb').1
  obtain ⟨b, hb⟩ : ∃ b, g.blocks[i]? = some b := ⟨_, List.getElem?_eq_getElem hil⟩
  exact ⟨b, hb, h.blk i b b' hb hb'⟩

theorem LRel.build {g F : Function} (h : LRel g F) : Cfg.build F = Cfg.build g := by
  apply build_congr
  apply List.ext_getElem?
  intro i
  simp only [cfgShape, List.getElem?_map]
  cases hb' : F.blocks[i]? with
  | none =>
    have : g.blocks[i]? = none := by
      rw [List.getElem?_eq_none_iff] at hb' ⊢; rw [← h.len]; exact hb'
    rw [this]
  | some b' =>
    obtain ⟨b, hb, he⟩ := h.get hb'
    rw [hb, he]; rfl

section MoveRel

variable {g F : Function} {hb : Nat} {t : Stmt} {bi : Nat} {b : Block} {jt : Nat} {v : ValueId}

theorem moveB_body (x : Block × Nat) :
    (moveB hb t x).body = x.1.body.filter (· != t) ++ (if x.2 = hb then [t] else []) := rfl

/-- **A move keeps `Good`** when the operands are available at the end of the target block. -/
theorem MoveOk.good (hm : MoveOk F hb t bi b jt v) {bh : Block} (hbh : F.blocks[hb]? = some bh)
    (hops : ∀ x ∈ operands t.inst, Avail (wfData F (coreInfo F)) hb bh.body.length x) :
    Good (moveF F hb t) :=
  ⟨hm.unique', hm.arity', hm.nodup', hm.wf' hbh hops⟩

/-- **A move keeps the relation to the input.** -/
theorem LRel.move (hg : Good g) (h : LRel g F) (hm : MoveOk F hb t bi b jt v) (hins : insOk t = true) :
    LRel g (moveF F hb t) := by
  have hbld := h.build
  have hrank := hg.wf.rank
  have hanc : Anc (Cfg.build g).idom hb bi := by rw [← hbld]; exact hm.hanc
  have htr : t.results ≠ [] := by rw [hm.hres]; simp
  obtain ⟨M, hMins, hMbody, hMloc⟩ := h.moved
  refine ⟨?_, by simp [moveF, h.len], fun i b0 b' hb0 hb' => ?_, fun x => ?_, ?_⟩
  · rw [moveF]; conv => lhs; rw [h.hdr]
  · rw [moveF_get, Option.map_eq_some_iff] at hb'
    obtain ⟨bF, hbF, rfl⟩ := hb'
    have := h.blk i b0 bF hb0 hbF
    rw [this]; rfl
  · have := hm.tm x
    simpa [wfData, coreInfo, Std.HashMap.get?_eq_getElem?, h.types x] using this
  -- the location of `t` before the move: block `bi`
  have htF : t ∈ b.body := List.mem_of_getElem? hm.ht
  have hloc : ∀ (d : Nat) (bd : Block), F.blocks[d]? = some bd → t ∈ bd.body → d = bi :=
    fun d bd hd ht => stmt_unique_mem hm.unique hd hm.hb_b ht htF htr
  -- after the move, a statement other than `t` stays where it was, and `t` is in `hb`
  have hstay : ∀ (d : Nat) (bd : Block) (s : Stmt), F.blocks[d]? = some bd → s ∈ bd.body → s ≠ t →
      ∃ bd', (moveF F hb t).blocks[d]? = some bd' ∧ s ∈ bd'.body := by
    intro d bd s hd hs hst
    refine ⟨_, by rw [moveF_get, hd]; rfl, ?_⟩
    rw [moveB_body]
    exact List.mem_append_left _ (List.mem_filter.2 ⟨hs, by simpa using hst⟩)
  obtain ⟨bh, hbh⟩ : ∃ bh, F.blocks[hb]? = some bh := ⟨_, List.getElem?_eq_getElem hm.hbl⟩
  have hthb : ∃ bd' : Block, (moveF F hb t).blocks[hb]? = some bd' ∧ t ∈ bd'.body :=
    ⟨_, by rw [moveF_get, hbh]; rfl, by rw [moveB_body]; simp⟩
  by_cases htM : t ∈ M
  · -- `t` was moved before: it goes further up
    refine ⟨M, hMins, fun i b0 b' hb0 hb' => ?_, fun s hs => ?_⟩
    · rw [moveF_get, Option.map_eq_some_iff] at hb'
      obtain ⟨bF, hbF, rfl⟩ := hb'
      obtain ⟨T, hT, hTM⟩ := hMbody i b0 bF hb0 hbF
      refine ⟨T.filter (· != t) ++ (if i = hb then [t] else []), ?_, fun x hx => ?_⟩
      · rw [moveB_body, hT, List.filter_append]
        have : (b0.body.filter (· ∉ M)).filter (· != t) = b0.body.filter (· ∉ M) :=
          List.filter_eq_self.2 fun x hx => by
            simp only [bne_iff_ne, ne_eq]; rintro rfl
            have := (List.mem_filter.1 hx).2; simp [htM] at this
        simp only [this, List.append_assoc]
      · rcases List.mem_append.1 hx with hx | hx
        · exact hTM x (List.mem_filter.1 hx).1
        · split at hx
          · simp at hx; subst hx; exact htM
          · simp at hx
    · obtain ⟨i0, b0, d, bd, hb0, hs0, hbd, hsd, hne, ha⟩ := hMloc s hs
      by_cases hst : s = t
      · subst hst
        have hdb := hloc d bd hbd hsd
        subst hdb
        obtain ⟨bd', hbd', hsd'⟩ := hthb
        refine ⟨i0, b0, hb, bd', hb0, hs0, hbd', hsd', fun he => ?_, hanc.trans ha⟩
        subst he
        exact hne (Anc.antisymm hrank ha hanc)
      · obtain ⟨bd', hbd', hsd'⟩ := hstay d bd s hbd hsd hst
        exact ⟨i0, b0, d, bd', hb0, hs0, hbd', hsd', hne, ha⟩
  · -- `t` moves for the first time
    refine ⟨M ++ [t], fun s hs => ?_, fun i b0 b' hb0 hb' => ?_, fun s hs => ?_⟩
    · rcases List.mem_append.1 hs with hs | hs
      · exact hMins s hs
      · simp at hs; subst hs; exact hins
    · rw [moveF_get, Option.map_eq_some_iff] at hb'
      obtain ⟨bF, hbF, rfl⟩ := hb'
      obtain ⟨T, hT, hTM⟩ := hMbody i b0 bF hb0 hbF
      refine ⟨T ++ (if i = hb then [t] else []), ?_, fun x hx => ?_⟩
      · rw [moveB_body, hT, List.filter_append, List.filter_filter]
        have hTt : T.filter (· != t) = T := List.filter_eq_self.2 fun x hx => by
          simp only [bne_iff_ne, ne_eq]; rintro rfl; exact htM (hTM _ hx)
        have hf : (fun a => (a != t) && decide (a ∉ M)) = fun a => decide (a ∉ M ++ [t]) := by
          funext a
          by_cases hat : a = t
          · subst hat; simp
          · simp [hat]
        rw [hTt, hf, List.append_assoc]
      · rcases List.mem_append.1 hx with hx | hx
        · exact List.mem_append_left _ (hTM x hx)
        · split at hx
          · simp at hx; subst hx; simp
          · simp at hx
    · rcases List.mem_append.1 hs with hs1 | hs1
      · obtain ⟨i0, b0, d, bd, hb0, hs0, hbd, hsd, hne, ha⟩ := hMloc s hs1
        have hst : s ≠ t := by rintro rfl; exact htM hs1
        obtain ⟨bd', hbd', hsd'⟩ := hstay d bd s hbd hsd hst
        exact ⟨i0, b0, d, bd', hb0, hs0, hbd', hsd', hne, ha⟩
      · simp at hs1; subst hs1
        obtain ⟨b0, hb0, -⟩ := h.get hm.hb_b
        obtain ⟨T, hT, hTM⟩ := hMbody bi b0 b hb0 hm.hb_b
        have ht0 : s ∈ b0.body := by
          rw [hT] at htF
          rcases List.mem_append.1 htF with h1 | h1
          · exact (List.mem_filter.1 h1).1
          · exact absurd (hTM _ h1) htM
        obtain ⟨bd', hbd', hsd'⟩ := hthb
        exact ⟨bi, b0, hb, bd', hb0, ht0, hbd', hsd', hm.hne, hanc⟩

end MoveRel

/-! ## `check` and `editOk id` from the invariants -/

/-- The definition site in `F` of a result of a statement of block `d`. -/
theorem site_of_mem {F : Function} (hu : UniqueDefs F) {d : Nat} {bd : Block} (hbd : F.blocks[d]? = some bd)
    {s : Stmt} (hs : s ∈ bd.body) {x : ValueId} (hx : x ∈ s.results) :
    ∃ j, bd.body[j]? = some s ∧ (defMap F).get? x = some (d, j + 1) := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hs
  exact ⟨j, hj, (defMap_get_iff hu x _).2 (mem_defSites.2 ⟨d, bd, hbd, .inr ⟨j, s, hj, hx, rfl⟩⟩)⟩

section Final

variable {g F : Function} {info : Info} (hc : Checked g info) (hG : Good F) (h : LRel g F)
include hc hG h

omit hc hG in
theorem LRel.params (i : Nat) : F.blocks.toArray[i]!.params = g.blocks.toArray[i]!.params := by
  simp only [getElem!_def, List.getElem?_toArray]
  cases hb' : F.blocks[i]? with
  | none =>
    have : g.blocks[i]? = none := by
      rw [List.getElem?_eq_none_iff] at hb' ⊢; rw [← h.len]; exact hb'
    rw [this]
  | some b' =>
    obtain ⟨b, hb, he⟩ := h.get hb'
    rw [hb, he]

omit hc hG in
theorem LRel.sig : F.sig = g.sig := by
  have := congrArg Function.sig h.hdr; simpa using this

omit hc hG in
theorem LRel.types' (x : ValueId) : (defsState F).1.get? x = (defsState g).1.get? x := by
  simp only [Std.HashMap.get?_eq_getElem?]; exact h.types x

/-- **`check` accepts the state.** -/
theorem LRel.check : check F = .ok (coreInfo F) := by
  have hbld := h.build
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hc.core
  have hcore : CoreOk F := by
    refine coreOk_of_wf (by rw [hbld]; exact h1) (by rw [hbld]; exact h2) (by rw [hbld]; exact h3)
      ?_ ?_ hG.wf ?_ ?_
    · rw [defsOk_iff]
      exact ⟨hG.arity, (allAlong_evC_iff _ _).2 ⟨fun e _ => by simp, hG.nodup⟩⟩
    · rw [h.params, h.sig]; exact h5
    · intro i b' hb' bc hbc
      obtain ⟨b, hb, he⟩ := h.get hb'
      rw [he] at hbc
      obtain ⟨-, -, hcalls, -⟩ := h6 (b, i) (List.mem_zipIdx_iff_getElem?.2 hb)
      obtain ⟨j, hj, hok⟩ := hcalls bc hbc
      refine ⟨j, by rw [hbld]; exact hj, ?_⟩
      rw [h.params]
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hok ⊢
      refine ⟨hok.1, fun x hx => ?_⟩
      rw [h.types']; exact hok.2 x hx
    · intro b' hb'
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hb'
      obtain ⟨b, hb, he⟩ := h.get hi
      obtain ⟨-, -, -, hbr⟩ := h6 (b, i) (List.mem_zipIdx_iff_getElem?.2 hb)
      rw [he]
      revert hbr
      cases b.term <;> simp only [brTableOk, imp_self]
      rw [h.types']; exact id
  have hw : wfCert F (coreInfo F).cfg (coreInfo F).types = true := wfCert_complete hG.wf
  exact (check_ok_iff F (coreInfo F)).2 ⟨hcore, rfl, hw⟩

/-- **The edit validator accepts the state** (renaming `id`). -/
theorem LRel.editOk : editOk id g F info (coreInfo F) = true := by
  have hbld := h.build
  have hgG := hc.good
  have hidom : (coreInfo F).cfg.idom = info.cfg.idom := by
    simp [coreInfo, hbld, hc.info_eq]
  obtain ⟨M, hMins, hMbody, hMloc⟩ := h.moved
  have hres : ∀ s ∈ M, ∃ v, s.results = [v] := by
    intro s hs
    have := hMins s hs
    simp only [insOk, Bool.and_eq_true, beq_iff_eq] at this
    exact List.length_eq_one_iff.1 this.1.2
  simp only [Opt.editOk, Bool.and_eq_true, List.all_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨?_, hidom⟩, by rw [h.len]⟩, ?_⟩, ?_⟩
  · have := h.hdr
    simp only [sameHeader, Bool.and_eq_true, beq_iff_eq]
    rw [this]; simp
  · rintro ⟨⟨b, b'⟩, i⟩ hx
    have hx' := List.mem_zipIdx_iff_getElem?.1 hx
    simp only [List.getElem?_zip_eq_some] at hx'
    obtain ⟨hb, hb'⟩ := hx'
    have he := h.blk i b b' hb hb'
    obtain ⟨T, hT, hTM⟩ := hMbody i b b' hb hb'
    rw [he]
    simp only [id, mapTerm_id, implies_true, and_true, true_and]
    rw [hT]
    refine align_filter_append _ rfl _ T (fun t ht => hMins t (hTM t ht)) b.body (fun s hs hp => ?_) 0
    have hsM : s ∈ M := by simpa using hp
    obtain ⟨v, hv⟩ := hres s hsM
    have hsr : s.results ≠ [] := by rw [hv]; simp
    obtain ⟨i0, b0, d, bd, hb0, hs0, hbd, hsd, hne, ha⟩ := hMloc s hsM
    have hi0 : i = i0 := stmt_unique_mem hgG.unique hb hb0 hs hs0 hsr
    subst hi0
    refine ⟨fun hsT => hne ?_, fun k => ?_⟩
    · have : s ∈ b'.body := by rw [hT]; exact List.mem_append_right _ hsT
      exact stmt_unique_mem hG.unique hbd hb' hsd this hsr
    · obtain ⟨j, hj, hdm⟩ := site_of_mem hG.unique hbd hsd (show v ∈ s.results by simp [hv])
      have hins := hMins s hsM
      simp only [insOk, Bool.and_eq_true] at hins
      simp only [EditCtx.delOk, id, Bool.or_eq_true, Bool.and_eq_true, hv]
      right
      refine ⟨hins.1.1, ?_, ?_⟩
      · simp only [availB, hdm, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
        right
        refine ⟨hne, ?_⟩
        have := ancB_complete hG.wf.rank (a := d) (b := i) (by
          simpa [wfData, coreInfo, hbld] using ha)
        simpa [wfData, coreInfo] using this
      · simp only [EditCtx.pureAt, hdm, mapOperands_id]
        have hgb : F.blocks.toArray[d]? = some bd := by simp [hbd]
        simp only [hgb, hj, hv, beq_self_eq_true, Bool.and_self, Bool.true_and]
        exact hins.1.1
  · rintro ⟨x, d, t⟩ hx
    rw [Std.HashMap.mem_toList_iff_getElem?_eq_some] at hx
    have hs : (x, (d, t)) ∈ defSites g :=
      (defMap_get_iff hgG.unique x _).1 (by rw [Std.HashMap.get?_eq_getElem?]; exact hx)
    simp only [id]
    split
    · rename_i d' t' hg'
      have hs' := (defMap_get_iff hG.unique x _).1 hg'
      -- the site of `x` in `F` is in `d` or in a tree ancestor of `d`
      suffices hloc : ∃ e u, (x, (e, u)) ∈ defSites F ∧ Anc (Cfg.build g).idom e d by
        obtain ⟨e, u, he, ha⟩ := hloc
        have := site_unique hG.unique hs' he
        simp only [Prod.mk.injEq] at this
        rw [this.1, hidom, hc.info_eq]
        have := ancB_complete hgG.wf.rank (a := e) (b := d) (by simpa [wfData, coreInfo] using ha)
        simpa [wfData, coreInfo] using this
      obtain ⟨i, b, hb, ⟨p, hp, hpx, he⟩ | ⟨j, st, hj, hxs, he⟩⟩ := mem_defSites.1 hs
      · simp only [Prod.mk.injEq] at he; obtain ⟨hd, -⟩ := he; subst hd
        have hil : d < F.blocks.length := by rw [h.len]; exact (List.getElem?_eq_some_iff.1 hb).1
        obtain ⟨b', hb'⟩ : ∃ b', F.blocks[d]? = some b' := ⟨_, List.getElem?_eq_getElem hil⟩
        have hpar : b'.params = b.params := by rw [h.blk d b b' hb hb']
        exact ⟨d, 0, mem_defSites.2 ⟨d, b', hb', .inl ⟨p, by rw [hpar]; exact hp, hpx, rfl⟩⟩, .refl _⟩
      · simp only [Prod.mk.injEq] at he; obtain ⟨hd, -⟩ := he; subst hd
        have hst := List.mem_of_getElem? hj
        by_cases hsM : st ∈ M
        · obtain ⟨i0, b0, e, bd, hb0, hs0, hbd, hsd, -, ha⟩ := hMloc st hsM
          have hsr : st.results ≠ [] := List.ne_nil_of_mem hxs
          have := stmt_unique_mem hgG.unique hb hb0 hst hs0 hsr
          subst this
          obtain ⟨j', -, hdm⟩ := site_of_mem hG.unique hbd hsd hxs
          exact ⟨e, j' + 1, (defMap_get_iff hG.unique x _).1 hdm, ha⟩
        · have hil : d < F.blocks.length := by rw [h.len]; exact (List.getElem?_eq_some_iff.1 hb).1
          obtain ⟨b', hb'⟩ : ∃ b', F.blocks[d]? = some b' := ⟨_, List.getElem?_eq_getElem hil⟩
          obtain ⟨T, hT, -⟩ := hMbody d b b' hb hb'
          have : st ∈ b'.body := by
            rw [hT]; exact List.mem_append_left _ (List.mem_filter.2 ⟨hst, by simpa using hsM⟩)
          obtain ⟨j', -, hdm⟩ := site_of_mem hG.unique hb' this hxs
          exact ⟨d, j' + 1, (defMap_get_iff hG.unique x _).1 hdm, .refl _⟩
    · rfl

end Final

/-! ## `licmRound` as folds -/

/-- The `inside` set at the start of a loop. -/
def insideF (lp : Cfg.Loop) (bs : Array Block) : Std.HashSet ValueId :=
  lp.body.toList.foldl (fun s bi => bs[bi]!.body.foldl (fun s st => st.results.foldl (fun b a => b.insert a) s)
    (bs[bi]!.params.foldl (fun b a => b.insert a.1) s)) ∅

/-- One statement of a loop block. -/
def blkStep (hc : Bool) (s : Std.HashSet ValueId × Array Stmt × Array Stmt) (st : Stmt) :
    Std.HashSet ValueId × Array Stmt × Array Stmt :=
  if (licmHoistable hc st.inst && st.results.length == 1 &&
      (operands st.inst).all fun x => !s.1.contains x) = true then
    (st.results.foldl (fun x1 x2 => x1.erase x2) s.1, s.2.1.push st, s.2.2)
  else (s.1, s.2.1, s.2.2.push st)

/-- One block (in RPO) of a loop. -/
def rpoStep (hc : Bool) (lp : Cfg.Loop) (s : Array Block × Std.HashSet ValueId × Array Stmt) (bi : Nat) :
    Array Block × Std.HashSet ValueId × Array Stmt :=
  if lp.body.contains bi then
    let r := s.1[bi]!.body.foldl (blkStep hc) (s.2.1, s.2.2, #[])
    (s.1.set! bi { s.1[bi]! with body := r.2.2.toList }, r.1, r.2.1)
  else s

/-- One loop. -/
def loopStep (hc : Bool) (cfg : Cfg) (st : Array Block × Nat) (x : {lp // lp ∈ cfg.loops}) : Array Block × Nat :=
  match cfg.idom[x.1.header]! with
  | some hb =>
    let r := cfg.rpo.toList.foldl (rpoStep hc x.1) (st.1, insideF x.1 st.1, #[])
    if !r.2.2.isEmpty then
      (r.1.modify hb (fun b => { b with body := b.body ++ r.2.2.toList }), st.2 + r.2.2.size)
    else (r.1, st.2)
  | none => st

theorem licmRound_eq (hc : Bool) (F : Function) (cfg : Cfg) :
    (licmRound hc F cfg).1 = { F with blocks := ((cfg.loops.attach.qsort
      (fun a b => a.1.body.size < b.1.body.size)).toList.foldl (loopStep hc cfg) (F.blocks.toArray, 0)).1.toList } := by
  unfold licmRound
  simp only [Id.run, List.forIn_pure_yield_eq_foldl, bind_pure_comp, map_pure, pure_bind]
  rw [← Array.forIn_toList, forIn_yield_foldl _ (loopStep hc cfg)]
  · rfl
  intro x s
  unfold loopStep
  cases h : cfg.idom[x.1.header]! with
  | none => rfl
  | some hb =>
    simp only []
    rw [← Array.forIn_toList, forIn_yield_foldl _ (rpoStep hc x.1)]
    · simp only [pure_bind]
      unfold insideF
      split <;> rfl
    intro bi s'
    unfold rpoStep
    by_cases hbi : x.1.body.contains bi = true
    · simp only [hbi, Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
      rw [forIn_yield_foldl _ (blkStep hc)]
      · rfl
      intro st s''
      unfold blkStep
      split <;> rfl
    · simp only [hbi, Bool.not_false, ite_true, Bool.false_eq_true, ite_false]
      skip

/-! ## One hoisted statement -/

/-- `x` is not defined in a block of the loop `lp` of `F0`. -/
def NotIn (lp : Cfg.Loop) (F0 : Function) (x : ValueId) : Prop :=
  ∀ (bi : Nat) (b : Block), lp.body.contains bi = true → F0.blocks[bi]? = some b →
    (∀ p ∈ b.params, p.1 ≠ x) ∧ ∀ st ∈ b.body, x ∉ st.results

/-- The invariant of a loop of `licmRound` (`F0`: the function at the start of the loop, `H`: the
statements hoisted so far, `ins`: the pass's `inside` set). -/
structure LInv (g F0 : Function) (lp : Cfg.Loop) (hb : Nat) (H : List Stmt) (ins : Std.HashSet ValueId) :
    Prop where
  good : Good (hoistF F0 hb H)
  rel : LRel g (hoistF F0 hb H)
  ins : ∀ x, ins.contains x = false → NotIn lp F0 x ∨ ∃ t ∈ H, x ∈ t.results
  hoisted : ∀ t ∈ H, t.results.length = 1 ∧
    ∃ (bi : Nat) (b : Block), lp.body.contains bi = true ∧ F0.blocks[bi]? = some b ∧ t ∈ b.body

theorem insOk_of_hoistable {hk : Bool} {s : Stmt} (h1 : licmHoistable hk s.inst = true)
    (h2 : s.results.length = 1) : insOk s = true := by
  unfold insOk
  rw [h2]
  revert h1
  cases s.inst <;> simp [licmHoistable, isPure]

theorem erase_fold_contains (l : List ValueId) (S : Std.HashSet ValueId) (x : ValueId)
    (h : (l.foldl (fun x1 x2 => x1.erase x2) S).contains x = false) : S.contains x = false ∨ x ∈ l := by
  induction l generalizing S with
  | nil => exact .inl h
  | cons y l ih =>
    rcases ih _ h with h1 | h1
    · by_cases hxy : y = x
      · exact .inr (by simp [hxy])
      · left
        rw [Std.HashSet.contains_erase] at h1
        simpa [hxy] using h1
    · exact .inr (List.mem_cons_of_mem _ h1)

theorem hoistF_get_some {F0 : Function} {hb i : Nat} {b : Block} (h : F0.blocks[i]? = some b) (H : List Stmt) :
    (hoistF F0 hb H).blocks[i]? = some (hoistB hb H (b, i)) := by
  rw [hoistF_get, h]; rfl

section Hoist

variable {g : Function} {info : Info} (hc : Checked g info) {lp : Cfg.Loop}
  (hlp : LoopOk (Cfg.build g) lp) {hb : Nat} (hhb : (Cfg.build g).idom[lp.header]?.join = some hb)
  {F0 : Function} (hG0 : Good F0) (h0 : LRel g F0)
include hc hlp hhb hG0 h0

/-- **Hoisting one more statement keeps the loop invariant.** -/
theorem hoist_step {H : List Stmt} {ins : Std.HashSet ValueId} (hI : LInv g F0 lp hb H ins)
    {hk : Bool} {bi : Nat} {b0 : Block} (hbi : lp.body.contains bi = true)
    (hb0 : F0.blocks[bi]? = some b0) {s : Stmt} (hs : s ∈ b0.body) (hsH : s ∉ H)
    (hh : (licmHoistable hk s.inst && s.results.length == 1 &&
      (operands s.inst).all fun x => !ins.contains x) = true) :
    LInv g F0 lp hb (H ++ [s]) (s.results.foldl (fun x1 x2 => x1.erase x2) ins) := by
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.not_eq_true'] at hh
  obtain ⟨⟨hpure, hlen⟩, hops⟩ := hh
  obtain ⟨v, hv⟩ := List.length_eq_one_iff.1 hlen
  have hins := insOk_of_hoistable hpure hlen
  have hgG := hc.good
  have hrank := hgG.wf.rank
  have hbld0 := h0.build
  have hbldk := hI.rel.build
  have hlen0 : F0.blocks.length = g.blocks.length := h0.len
  -- the hoist block
  have hhbl : hb < g.blocks.length := build_idom_lt g hhb
  have hhanc : Anc (Cfg.build g).idom hb lp.header := .up hhb (.refl _)
  have hbianc : Anc (Cfg.build g).idom lp.header bi := hlp.2.1 bi hbi
  have hne : hb ≠ bi := by
    rintro rfl
    have := Anc.antisymm hrank hhanc hbianc
    have hr := hrank lp.header hb (by simpa [wfData, coreInfo] using hhb)
    rw [this] at hr; omega
  -- `s` in the current state
  have hkb : (hoistF F0 hb H).blocks[bi]? = some (hoistB hb H (b0, bi)) := hoistF_get_some hb0 H
  have hsk : s ∈ (hoistB hb H (b0, bi)).body := by
    simp only [hoistB, Ne.symm hne, ite_false, List.append_nil, hne]
    exact List.mem_filter.2 ⟨hs, by simpa using hsH⟩
  obtain ⟨jt, hjt⟩ := List.mem_iff_getElem?.1 hsk
  obtain ⟨bh0, hbh0⟩ : ∃ bh0, F0.blocks[hb]? = some bh0 :=
    ⟨_, List.getElem?_eq_getElem (by rw [hlen0]; exact hhbl)⟩
  have hkh : (hoistF F0 hb H).blocks[hb]? = some (hoistB hb H (bh0, hb)) := hoistF_get_some hbh0 H
  have hm : MoveOk (hoistF F0 hb H) hb s bi (hoistB hb H (b0, bi)) jt v :=
    ⟨hI.good.unique, hI.good.arity, hI.good.nodup, hI.good.wf, hkb, hjt, hv, hne,
      by rw [hbldk]; exact hhanc.trans hbianc, by simp [hoistF, hlen0, hhbl]⟩
  -- the operands are available at the end of the hoist block
  have havail : ∀ x ∈ operands s.inst,
      Avail (wfData (hoistF F0 hb H) (coreInfo (hoistF F0 hb H))) hb (hoistB hb H (bh0, hb)).body.length x := by
    intro x hx
    rcases hI.ins x (hops x hx) with hni | ⟨t, htH, hxt⟩
    · -- defined outside the loop: in a strict tree ancestor of the header
      obtain ⟨j0, hj0⟩ := List.mem_iff_getElem?.1 hs
      obtain ⟨d, t0, hdm0, hcase⟩ := hG0.wf.uses bi b0 hb0 j0 s hj0 x hx
      have hsite := hG0.wf.sitesRev x (d, t0) hdm0
      obtain ⟨i, bd, hbd, hdef⟩ := mem_defSites.1 hsite
      have hdi : i = d := by
        rcases hdef with ⟨_, _, _, he⟩ | ⟨_, _, _, _, he⟩ <;>
        · simp only [Prod.mk.injEq] at he; exact he.1.symm
      subst hdi
      have hdout : lp.body.contains i = false := by
        cases hcd : lp.body.contains i
        · rfl
        · exfalso
          obtain ⟨h1, h2⟩ := hni i bd hcd hbd
          rcases hdef with ⟨p, hp, hpx, -⟩ | ⟨j, st, hj, hxs, -⟩
          · exact h1 p hp hpx
          · exact h2 st (List.mem_of_getElem? hj) hxs
      have hdbi : i ≠ bi := by rintro rfl; rw [hbi] at hdout; cases hdout
      have hanc : Anc (Cfg.build g).idom i bi := by
        rcases hcase with ⟨h1, -⟩ | ⟨-, h2⟩
        · exact absurd h1 hdbi
        · simpa [wfData, coreInfo, hbld0] using h2
      have hdh : Anc (Cfg.build g).idom i hb := by
        rcases Anc.total hanc hbianc with h1 | h1
        · have hih : i ≠ lp.header := by rintro rfl; rw [hlp.1] at hdout; cases hdout
          obtain ⟨c, hc1, hc2⟩ := h1.strict hih
          rw [hhb] at hc1; cases hc1; exact hc2
        · have hih : lp.header ≠ i := by rintro rfl; rw [hlp.1] at hdout; cases hdout
          have := loop_between hc hlp hbi h1 (Ne.symm hih) hanc
          rw [this] at hdout; cases hdout
      -- the definition site in the current state is in block `i`
      have hki : (hoistF F0 hb H).blocks[i]? = some (hoistB hb H (bd, i)) := hoistF_get_some hbd H
      obtain ⟨u, hu, hul⟩ : ∃ u, (defMap (hoistF F0 hb H)).get? x = some (i, u) ∧
          u ≤ (hoistB hb H (bd, i)).body.length := by
        rcases hdef with ⟨p, hp, hpx, -⟩ | ⟨j, st, hj, hxs, -⟩
        · exact ⟨0, (defMap_get_iff hI.good.unique x _).2
            (mem_defSites.2 ⟨i, _, hki, .inl ⟨p, by simpa [hoistB] using hp, hpx, rfl⟩⟩), Nat.zero_le _⟩
        · have hstH : st ∉ H := by
            intro hst
            obtain ⟨-, bi', b', hbi', hb', hst'⟩ := hI.hoisted st hst
            have := stmt_unique_mem hG0.unique hbd hb' (List.mem_of_getElem? hj) hst'
              (List.ne_nil_of_mem hxs)
            subst this; rw [hbi'] at hdout; cases hdout
          have hstk : st ∈ (hoistB hb H (bd, i)).body := by
            simp only [hoistB]
            exact List.mem_append_left _ (List.mem_filter.2 ⟨List.mem_of_getElem? hj, by simpa using hstH⟩)
          obtain ⟨j', hj', hdm⟩ := site_of_mem hI.good.unique hki hstk hxs
          exact ⟨j' + 1, hdm, (List.getElem?_eq_some_iff.1 hj').1⟩
      refine ⟨i, u, hu, ?_⟩
      by_cases hih : i = hb
      · subst hih
        rw [hbd] at hbh0; cases hbh0
        exact .inl ⟨rfl, hul⟩
      · exact .inr ⟨hih, by simpa [wfData, coreInfo, hbldk] using hdh⟩
    · -- defined by a statement hoisted earlier: earlier in the hoist block
      have htk : t ∈ (hoistB hb H (bh0, hb)).body := by simp [hoistB, htH]
      obtain ⟨j', hj', hdm⟩ := site_of_mem hI.good.unique hkh htk hxt
      exact ⟨hb, j' + 1, hdm, .inl ⟨rfl, (List.getElem?_eq_some_iff.1 hj').1⟩⟩
  have hsnoc := hoistF_snoc F0 hb H s hsH
  refine ⟨?_, ?_, fun x hx => ?_, fun t ht => ?_⟩
  · rw [← hsnoc]; exact hm.good hkh havail
  · rw [← hsnoc]; exact hI.rel.move hgG hm hins
  · rcases erase_fold_contains _ _ _ hx with h1 | h1
    · rcases hI.ins x h1 with h2 | ⟨t, htH, hxt⟩
      · exact .inl h2
      · exact .inr ⟨t, List.mem_append_left _ htH, hxt⟩
    · exact .inr ⟨s, by simp, h1⟩
  · rcases List.mem_append.1 ht with ht | ht
    · exact hI.hoisted t ht
    · simp at ht; subst ht
      exact ⟨hlen, bi, b0, hbi, hb0, hs⟩

end Hoist

end Opt
