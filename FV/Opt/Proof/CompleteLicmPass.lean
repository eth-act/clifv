import FV.Opt.Licm
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
    simp only [hoistB, Ne.symm hne, ite_false, List.append_nil]
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

/-! ## A block, a loop, a round, the pass -/

theorem foldl_inv {α σ : Type} (P : σ → Prop) (f : σ → α → σ) :
    ∀ (l : List α) (s : σ), P s → (∀ s a, a ∈ l → P s → P (f s a)) → P (l.foldl f s)
  | [], _, h, _ => h
  | a :: l, s, h, hf => foldl_inv P f l _ (hf s a (List.mem_cons_self ..) h)
      (fun s b hb => hf s b (List.mem_cons_of_mem _ hb))

theorem foldl_contains_mono {α : Type} (step : Std.HashSet ValueId → α → Std.HashSet ValueId)
    (hstep : ∀ s a x, s.contains x = true → (step s a).contains x = true) :
    ∀ (l : List α) (s : Std.HashSet ValueId) (x : ValueId), s.contains x = true →
      (l.foldl step s).contains x = true
  | [], _, _, h => h
  | a :: l, s, x, h => foldl_contains_mono step hstep l _ x (hstep s a x h)

theorem foldl_contains_mem {α : Type} (step : Std.HashSet ValueId → α → Std.HashSet ValueId)
    (hstep : ∀ s a x, s.contains x = true → (step s a).contains x = true) (Q : α → ValueId → Prop)
    (hQ : ∀ s a x, Q a x → (step s a).contains x = true) :
    ∀ (l : List α) (s : Std.HashSet ValueId) (a : α) (x : ValueId), a ∈ l → Q a x →
      (l.foldl step s).contains x = true
  | [], _, _, _, h, _ => by simp at h
  | b :: l, s, a, x, h, hq => by
    rcases List.mem_cons.1 h with rfl | h
    · exact foldl_contains_mono step hstep l _ x (hQ s a x hq)
    · exact foldl_contains_mem step hstep Q hQ l _ a x h hq

theorem insert_contains_mono (s : Std.HashSet ValueId) (y z : ValueId) (hy : s.contains y = true) :
    (s.insert z).contains y = true := by
  simp [Std.HashSet.contains_insert, hy]

theorem insert_contains_self (s : Std.HashSet ValueId) (y z : ValueId) (hy : z = y) :
    (s.insert z).contains y = true := by
  simp [Std.HashSet.contains_insert, hy]

/-- The pass's `inside` set contains every value defined in a loop block. -/
theorem insideF_notIn {lp : Cfg.Loop} {F : Function} {bs : Array Block} {x : ValueId}
    (h : (insideF lp bs).contains x = false) : NotIn lp { F with blocks := bs.toList } x := by
  intro bi b hbi hb
  have hbs : bs[bi]! = b := by
    have : bs.toList[bi]? = some b := hb
    simp only [getElem!_def, ← Array.getElem?_toList, this]
  have hres : ∀ (l : List Stmt) (s : Std.HashSet ValueId) (y : ValueId), s.contains y = true →
      (l.foldl (fun s st => st.results.foldl (fun b a => b.insert a) s) s).contains y = true :=
    foldl_contains_mono _ (fun s st y hy =>
      foldl_contains_mono _ (fun s a y h => insert_contains_mono s y a h) _ _ _ hy)
  have hmono : ∀ (s : Std.HashSet ValueId) (bi : Nat) (y : ValueId), s.contains y = true →
      (bs[bi]!.body.foldl (fun s st => st.results.foldl (fun b a => b.insert a) s)
        (bs[bi]!.params.foldl (fun b a => b.insert a.1) s)).contains y = true :=
    fun s bi y hy => hres _ _ _
      (foldl_contains_mono _ (fun s a y h => insert_contains_mono s y a.1 h) _ _ _ hy)
  have hmem : bi ∈ lp.body.toList := by simpa [Std.HashSet.mem_toList] using hbi
  constructor
  · intro p hp hpx
    have : (insideF lp bs).contains x = true := by
      unfold insideF
      refine foldl_contains_mem _ (fun s a y hy => hmono s a y hy)
        (fun bi y => ∃ p ∈ bs[bi]!.params, p.1 = y) ?_ _ _ bi x hmem ⟨p, by rw [hbs]; exact hp, hpx⟩
      rintro s a y ⟨q, hq, rfl⟩
      exact hres _ _ _ (foldl_contains_mem _ (fun s a y h => insert_contains_mono s y a.1 h)
        (fun a y => a.1 = y) (fun s a y h => insert_contains_self s y a.1 h) _ _ q q.1 hq rfl)
    rw [h] at this; cases this
  · intro st hst hx
    have : (insideF lp bs).contains x = true := by
      unfold insideF
      refine foldl_contains_mem _ (fun s a y hy => hmono s a y hy)
        (fun bi y => ∃ st ∈ bs[bi]!.body, y ∈ st.results) ?_ _ _ bi x hmem
        ⟨st, by rw [hbs]; exact hst, hx⟩
      rintro s a y ⟨st, hst, hy⟩
      exact foldl_contains_mem _ (fun s st y hy =>
          foldl_contains_mono _ (fun s a y h => insert_contains_mono s y a h) _ _ _ hy)
        (fun st y => y ∈ st.results)
        (fun s st y hy => foldl_contains_mem _ (fun s a y h => insert_contains_mono s y a h)
          (fun a y => a = y) (fun s a y h => insert_contains_self s y a h) _ _ y y hy rfl) _ _ st y hst hy
    rw [h] at this; cases this

theorem sublist_flatMap_of_mem {α β : Type} (F : α → List β) {a : α} :
    ∀ {l : List α}, a ∈ l → (F a).Sublist (l.flatMap F)
  | x :: l, h => by
    rw [List.flatMap_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact List.sublist_append_left _ _
    · exact (sublist_flatMap_of_mem F h).trans (List.sublist_append_right _ _)

/-- The results of a block's statements are distinct. -/
theorem body_results_nodup {F : Function} (hu : UniqueDefs F) {i : Nat} {b : Block}
    (hb : F.blocks[i]? = some b) : (b.body.flatMap (·.results)).Nodup := by
  have h1 : (b.body.flatMap (·.results)).Sublist ((defSites F).map (·.1)) := by
    rw [defSites_fst]
    exact (List.sublist_append_right _ _).trans
      (sublist_flatMap_of_mem (fun b => b.params.map (·.1) ++ b.body.flatMap (·.results))
        (List.mem_of_getElem? hb))
  exact h1.nodup hu

theorem not_mem_prefix {L pre suf : List Stmt} {s : Stmt} (hL : (L.flatMap (·.results)).Nodup)
    (he : pre ++ s :: suf = L) (hr : s.results ≠ []) : s ∉ pre := by
  have h1 := count_one_of_nodup_flatMap (·.results) L s hL (by rw [← he]; simp) hr
  rw [← he, List.count_append, List.count_cons_self] at h1
  intro hs
  have := List.count_pos_iff.2 hs
  omega

section Block

variable {g : Function} {info : Info} (hc : Checked g info) {lp : Cfg.Loop}
  (hlp : LoopOk (Cfg.build g) lp) {hb : Nat} (hhb : (Cfg.build g).idom[lp.header]?.join = some hb)
  {F0 : Function} (hG0 : Good F0) (h0 : LRel g F0) (hk : Bool)
include hc hlp hhb hG0 h0

/-- **A loop block**: the hoisted statements grow by statements of the block, and the kept ones are
the block's statements without the hoisted ones. -/
theorem blk_fold {H0 : List Stmt} {ins0 : Std.HashSet ValueId} (hI : LInv g F0 lp hb H0 ins0)
    {bi : Nat} {b0 : Block} (hbi : lp.body.contains bi = true) (hb0 : F0.blocks[bi]? = some b0)
    (Ha : Array Stmt) (hHa : Ha.toList = H0) :
    LInv g F0 lp hb ((b0.body.filter (· ∉ H0)).foldl (blkStep hk) (ins0, Ha, #[])).2.1.toList
        ((b0.body.filter (· ∉ H0)).foldl (blkStep hk) (ins0, Ha, #[])).1 ∧
      (∃ Hn, ((b0.body.filter (· ∉ H0)).foldl (blkStep hk) (ins0, Ha, #[])).2.1.toList = H0 ++ Hn ∧
        ∀ t ∈ Hn, t ∈ b0.body) ∧
      ((b0.body.filter (· ∉ H0)).foldl (blkStep hk) (ins0, Ha, #[])).2.2.toList =
        b0.body.filter (· ∉ ((b0.body.filter (· ∉ H0)).foldl (blkStep hk) (ins0, Ha, #[])).2.1.toList) := by
  have hLsub : (b0.body.filter (· ∉ H0)).Sublist b0.body := List.filter_sublist
  have hLnd : ((b0.body.filter (· ∉ H0)).flatMap (·.results)).Nodup :=
    (Sublist.flatMap' hLsub _).nodup (body_results_nodup hG0.unique hb0)
  have hLH : ∀ s ∈ b0.body.filter (· ∉ H0), s ∉ H0 := fun s hs => by
    simpa using (List.mem_filter.1 hs).2
  have hfin : ∀ Hn : List Stmt, ((b0.body.filter (· ∉ H0)).filter (· ∉ H0 ++ Hn)) =
      b0.body.filter (· ∉ H0 ++ Hn) := by
    intro Hn
    rw [List.filter_filter]
    apply List.filter_congr
    intro a _
    by_cases ha : a ∈ H0 <;> simp [ha]
  generalize b0.body.filter (· ∉ H0) = L at hLsub hLnd hLH hfin ⊢
  -- the invariant along the body
  let KI : List Stmt → Std.HashSet ValueId × Array Stmt × Array Stmt → Prop := fun pre st =>
    LInv g F0 lp hb st.2.1.toList st.1 ∧ (∃ Hn, st.2.1.toList = H0 ++ Hn ∧ ∀ t ∈ Hn, t ∈ pre) ∧
      st.2.2.toList = pre.filter (· ∉ st.2.1.toList)
  have key : ∀ (suf pre : List Stmt) st, pre ++ suf = L → KI pre st →
      KI L (suf.foldl (blkStep hk) st) := by
    intro suf
    induction suf with
    | nil => intro pre st he h; simp only [List.append_nil] at he; subst he; exact h
    | cons s suf ih =>
      intro pre st he h
      rw [List.foldl_cons]
      refine ih (pre ++ [s]) _ (by simpa using he) ?_
      obtain ⟨hI', ⟨Hn, hHn, hHnpre⟩, hkeep⟩ := h
      have hsL : s ∈ L := by rw [← he]; simp
      have hsb : s ∈ b0.body := hLsub.subset hsL
      have hnp : s.results ≠ [] → s ∉ pre := fun hr => not_mem_prefix hLnd he hr
      unfold blkStep
      split
      · rename_i hh
        have hlen : s.results.length = 1 := by
          simp only [Bool.and_eq_true, beq_iff_eq] at hh; exact hh.1.2
        have hsr : s.results ≠ [] := by intro h; rw [h] at hlen; cases hlen
        have hspre := hnp hsr
        have hsH : s ∉ st.2.1.toList := by
          rw [hHn]; intro hm
          rcases List.mem_append.1 hm with hm | hm
          · exact hLH s hsL hm
          · exact hspre (hHnpre s hm)
        refine ⟨?_, ⟨Hn ++ [s], by simp [hHn], fun t ht => ?_⟩, ?_⟩
        · have := hoist_step hc hlp hhb hG0 h0 hI' hbi hb0 hsb hsH hh
          simpa using this
        · rcases List.mem_append.1 ht with ht | ht
          · exact List.mem_append_left _ (hHnpre t ht)
          · simp at ht; subst ht; simp
        · simp only [Array.toList_push, List.filter_append]
          rw [hkeep]
          have : (pre.filter (· ∉ st.2.1.toList ++ [s])) = pre.filter (· ∉ st.2.1.toList) := by
            apply List.filter_congr
            intro a ha
            have has : a ≠ s := by rintro rfl; exact hspre ha
            simp [has]
          rw [this]; simp
      · have hsH : s ∉ st.2.1.toList := by
          rw [hHn]; intro hm
          rcases List.mem_append.1 hm with hm | hm
          · exact hLH s hsL hm
          · have h1 := (hI'.hoisted s (by rw [hHn]; exact List.mem_append_right _ hm)).1
            exact hnp (by intro h; rw [h] at h1; cases h1) (hHnpre s hm)
        refine ⟨hI', ⟨Hn, hHn, fun t ht => List.mem_append_left _ (hHnpre t ht)⟩, ?_⟩
        simp only [Array.toList_push, List.filter_append, hkeep]
        have hsH' : s ∉ st.2.1 := fun h => hsH (Array.mem_toList_iff.2 h)
        simp [hsH']
  have hK := key L [] (ins0, Ha, #[]) rfl ⟨by simpa [hHa] using hI, ⟨[], by simp [hHa], by simp⟩, by simp⟩
  obtain ⟨hK1, ⟨Hn, hHn, hHnL⟩, hK3⟩ := hK
  refine ⟨hK1, ⟨Hn, hHn, fun t ht => hLsub.subset (hHnL t ht)⟩, ?_⟩
  rw [hK3, hHn, hfin]

end Block

/-- A body without the hoisted statements. -/
def filtB (H : List Stmt) (b : Block) : Block := { b with body := b.body.filter (· ∉ H) }

section Loop

variable {g : Function} {info : Info} (hc : Checked g info) (hk : Bool)
include hc

/-- The invariant of the RPO walk of a loop. -/
def RI (g F0 : Function) (lp : Cfg.Loop) (hb : Nat) (st : Array Block × Std.HashSet ValueId × Array Stmt) :
    Prop :=
  st.1.toList = F0.blocks.map (filtB st.2.2.toList) ∧ LInv g F0 lp hb st.2.2.toList st.2.1

theorem rpo_fold {lp : Cfg.Loop} (hlp : LoopOk (Cfg.build g) lp) {hb : Nat}
    (hhb : (Cfg.build g).idom[lp.header]?.join = some hb) {F0 : Function} (hG0 : Good F0)
    (h0 : LRel g F0) (l : List Nat) (st : Array Block × Std.HashSet ValueId × Array Stmt)
    (hst : RI g F0 lp hb st) : RI g F0 lp hb (l.foldl (rpoStep hk lp) st) := by
  refine foldl_inv _ _ l st hst fun st bi _ ⟨hbs, hI⟩ => ?_
  unfold rpoStep
  split
  · rename_i hbi
    have hbil : bi < F0.blocks.length := by
      rw [h0.len, ← build_size_eq hc]; exact hlp.2.2.2 bi hbi
    obtain ⟨b0, hb0⟩ : ∃ b0, F0.blocks[bi]? = some b0 := ⟨_, List.getElem?_eq_getElem hbil⟩
    have hget : st.1[bi]! = filtB st.2.2.toList b0 := by
      have : st.1.toList[bi]? = some (filtB st.2.2.toList b0) := by
        rw [hbs, List.getElem?_map, hb0]; rfl
      simp only [getElem!_def, ← Array.getElem?_toList, this]
    rw [hget]
    obtain ⟨hI', ⟨Hn, hHn, hHnb⟩, hkeep⟩ := blk_fold hc hlp hhb hG0 h0 hk hI hbi hb0 st.2.2 rfl
    simp only [filtB] at hI' hHn hkeep ⊢
    refine ⟨?_, hI'⟩
    apply List.ext_getElem?
    intro j
    simp only [Array.getElem?_toList, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds,
      List.getElem?_map]
    by_cases hj : bi = j
    · subst hj
      have hsz : bi < st.1.size := by
        have := congrArg List.length hbs
        simp only [Array.length_toList, List.length_map] at this; omega
      simp only [hsz, ite_true, hb0, Option.map_some, Option.some.injEq]
      rw [hkeep]; rfl
    · simp only [hj, ite_false]
      rw [← Array.getElem?_toList, hbs, List.getElem?_map]
      cases hbj : F0.blocks[j]? with
      | none => rfl
      | some bj =>
        simp only [Option.map_some, Option.some.injEq, filtB]
        congr 1
        rw [hHn]
        apply List.filter_congr
        intro a ha
        by_cases haH : a ∈ Hn
        · exfalso
          have h1 := (hI'.hoisted a (by rw [hHn]; exact List.mem_append_right _ haH)).1
          have hr : a.results ≠ [] := by intro h; rw [h] at h1; cases h1
          exact hj (stmt_unique_mem hG0.unique hb0 hbj (hHnb a haH) ha hr)
        · simp [haH]
  · exact ⟨hbs, hI⟩

/-- **One loop of `licmRound` keeps the invariants.** -/
theorem loop_ok {F : Function} {bs : Array Block} (hG : Good { F with blocks := bs.toList })
    (hR : LRel g { F with blocks := bs.toList }) (m : Nat) (x : {lp // lp ∈ (Cfg.build g).loops})
    (hlp : LoopOk (Cfg.build g) x.1) :
    Good { F with blocks := (loopStep hk (Cfg.build g) (bs, m) x).1.toList } ∧
      LRel g { F with blocks := (loopStep hk (Cfg.build g) (bs, m) x).1.toList } := by
  unfold loopStep
  cases h : (Cfg.build g).idom[x.1.header]! with
  | none => exact ⟨hG, hR⟩
  | some hb =>
    have hhb : (Cfg.build g).idom[x.1.header]?.join = some hb := by rw [← getElem!_opt]; exact h
    simp only []
    have hfilt0 : ∀ b : Block, filtB [] b = b := fun b => by
      simp [filtB, List.filter_eq_self.2]
    have h0 : RI g { F with blocks := bs.toList } x.1 hb (bs, insideF x.1 bs, #[]) := by
      refine ⟨((List.map_congr_left (fun b _ => hfilt0 b)).trans (List.map_id _)).symm, ?_⟩
      simp only [Array.toList_empty]
      refine ⟨by rw [hoistF_nil]; exact hG, by rw [hoistF_nil]; exact hR,
        fun y hy => .inl (insideF_notIn hy), by simp⟩
    have hr := rpo_fold hc hk hlp hhb hG hR (Cfg.build g).rpo.toList _ h0
    generalize (Cfg.build g).rpo.toList.foldl (rpoStep hk x.1) (bs, insideF x.1 bs, #[]) = r at hr
    obtain ⟨hbs, hI⟩ := hr
    have hbl : hb < bs.toList.length := by
      have := hR.len; simp only at this; rw [this]; exact build_idom_lt g hhb
    split
    · simp only []
      have : ({ F with blocks := (r.1.modify hb fun b => { b with body := b.body ++ r.2.2.toList }).toList } :
          Function) = hoistF { F with blocks := bs.toList } hb r.2.2.toList := by
        simp only [hoistF]
        congr 1
        apply List.ext_getElem?
        intro j
        simp only [Array.getElem?_toList, Array.getElem?_modify, List.getElem?_map, List.getElem?_zipIdx]
        rw [← Array.getElem?_toList, hbs, List.getElem?_map]
        have e2 : bs[j]? = bs.toList[j]? := by rw [Array.getElem?_toList]
        rw [e2]
        cases hj : bs.toList[j]? with
        | none => simp
        | some bj =>
          by_cases hjb : hb = j
          · subst hjb; simp [hoistB, filtB]
          · simp [hoistB, filtB, hjb, Ne.symm hjb]
      rw [this]; exact ⟨hI.good, hI.rel⟩
    · rename_i hE
      have hH : r.2.2.toList = [] := by simpa using hE
      have : ({ F with blocks := r.1.toList } : Function) = hoistF { F with blocks := bs.toList } hb [] := by
        rw [hoistF_nil, hbs, hH]
        simp only [(List.map_congr_left (fun b _ => hfilt0 b)).trans (List.map_id _)]
      rw [this, ← hH]; exact ⟨hI.good, hI.rel⟩

/-- **A round of LICM keeps the invariants.** -/
theorem licmRound_ok {F : Function} (hG : Good F) (hR : LRel g F) :
    Good (licmRound hk F info.cfg).1 ∧ LRel g (licmRound hk F info.cfg).1 := by
  have hcfg : info.cfg = Cfg.build g := by rw [hc.info_eq]; rfl
  rw [licmRound_eq, hcfg]
  refine foldl_inv (fun st : Array Block × Nat =>
      Good { F with blocks := st.1.toList } ∧ LRel g { F with blocks := st.1.toList }) _ _ _
    (by simpa using And.intro hG hR) ?_
  rintro ⟨bs, m⟩ x - ⟨hG', hR'⟩
  exact loop_ok hc hk hG' hR' m x (build_loops_ok hc x.1 (Array.mem_toList_iff.2 x.2))

/-- **LICM keeps the invariants.** -/
theorem licm_ok : Good (licm hk g info).1 ∧ LRel g (licm hk g info).1 := by
  unfold licm
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range']
  refine forIn_inv (P := fun s : Function × Nat => Good s.1 ∧ LRel g s.1) _ _ _
    ⟨hc.good, LRel.refl g⟩ ?_
  intro _ s ⟨hG, hR⟩
  have := licmRound_ok hc hk hG hR
  split <;> exact this

end Loop

/-- **Completeness of the LICM stage**: on a well-formed function, LICM's output passes `check` and
the edit validator, so `Opt.optimizeReport` never stops at the LICM stage. -/
theorem licm_complete {g : Function} {info : Info} (h : check g = .ok info) (hk : Bool) :
    check (licm hk g info).1 = .ok (coreInfo (licm hk g info).1) ∧
      editOk id g (licm hk g info).1 info (coreInfo (licm hk g info).1) = true := by
  have hc := checked_of_check h
  obtain ⟨hG, hR⟩ := licm_ok hc hk
  exact ⟨hR.check hc hG, hR.editOk hc hG⟩

end Opt

namespace Opt.CompleteLicmWitness

open Clif

/-- A loop `block1` whose `v2 = iconst 7` is invariant: LICM moves it to `block0`. -/
def fn : Function where
  name := "w"
  sig := {}
  blocks := [
    { id := 0, body := [{ results := [0], inst := .iconst .i32 5 }],
      term := .jump { block := 1, args := [0] } },
    { id := 1, params := [(1, .i32)],
      body := [{ results := [2], inst := .iconst .i32 7 }, { results := [3], inst := .binary .iadd .i32 1 2 }],
      term := .brif 3 { block := 1, args := [3] } { block := 2 } },
    { id := 2, term := .ret [] }]

theorem checks : (match check fn with
    | .ok i => (licm true fn i).2 == 1 && ((licm true fn i).1.blocks.head?.map (·.body.length)) == some 2
    | .error _ => false) = true := by native_decide

/-- Non-vacuity of `licm_complete`: `fn` is well-formed, LICM hoists `v2` out of the loop into
`block0`, and the stage is accepted. -/
theorem witness : ∃ i i', check fn = .ok i ∧ (licm true fn i).2 = 1 ∧
    check (licm true fn i).1 = .ok i' ∧ editOk id fn (licm true fn i).1 i i' = true := by
  have h := checks
  split at h
  · rename_i i hi
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨i, _, hi, h.1, (licm_complete hi true).1, (licm_complete hi true).2⟩
  · cases h

end Opt.CompleteLicmWitness

