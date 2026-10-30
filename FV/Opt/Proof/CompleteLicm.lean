import FV.Opt.Proof.CompleteGvn

/-!
# Completeness of the LICM stage: graph facts and single moves (M1)

The graph facts and the single move of the LICM completeness proof (`Opt.licm_complete`,
`FV/Opt/Proof/CompleteLicmPass.lean`).

CFG facts: the depth-first search is sound (`Opt.postorder_reach`: every block of the postorder is
reachable along `succs`), `preds` is the converse of `succs` (`Opt.build_preds_mem`),
`Cfg.dominates` is sound (`Opt.dominates_sound`), and every loop of `Cfg.loops` has the facts LICM
needs (`Opt.loops_ok`, `Opt.LoopOk`: the header is in the body, every body block is a tree
descendant of the header, the body is closed under predecessors of its non-header blocks; the
search's fuel suffices). Hence a block between the header and a loop block in the dominator tree
is in the loop (`Opt.loop_between`), which is why an operand defined outside the loop is available
at the end of the header's immediate dominator.

A move (`Opt.moveF`) takes a pure single-result statement to the end of a strict tree ancestor of
its block; it keeps the certificate facts, unique definitions, arities and types when the operands
are available there (`Opt.MoveOk`).
-/

namespace Opt

open Clif

/-- Reachability from the entry block along `succs`. -/
inductive CfgReach (succs : Array (List Nat)) : Nat → Prop
  | entry : CfgReach succs 0
  | step {a x : Nat} : CfgReach succs a → x ∈ succs[a]! → CfgReach succs x

/-- **The depth-first search is sound**: every block of the postorder is reachable. -/
theorem postorder_reach (succs : Array (List Nat)) :
    ∀ x ∈ (Cfg.postorder succs).toList, CfgReach succs x := by
  unfold Cfg.postorder
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range']
  split
  · intro x hx; exact absurd hx (by simp [pure])
  · rename_i hn
    rw [bind_pure_comp]
    simp only [Functor.map]
    refine forIn_inv' _ _ _
      (P := fun s : DfsSt => (∀ x ∈ dfsBlocks s, CfgReach succs x) ∧
        ∀ fr ∈ s.2.1.toList, ∀ y ∈ fr.2, y ∈ succs[fr.1]!)
      (Q := fun s : DfsSt => ∀ x ∈ s.2.2.toList, CfgReach succs x) ?_ ?_ ?_
    · refine ⟨fun x hx => ?_, fun fr hfr y hy => ?_⟩
      · simp [dfsBlocks] at hx; subst hx; exact .entry
      · simp at hfr; subst hfr; exact hy
    · rintro - ⟨vis, st, post⟩ ⟨hreach, hfr⟩
      simp only [dfsBlocks] at hfr hreach
      cases hb : st.back? with
      | none => simpa [hb, dfsBlocks] using And.intro hreach hfr
      | some fr =>
        obtain ⟨b, ss⟩ := fr
        have hst := back?_toList hb
        rw [hst] at hreach hfr
        simp only [List.map_append, List.mem_append, List.map_cons, List.map_nil, List.mem_cons,
          List.not_mem_nil, or_false] at hreach
        have hbr : CfgReach succs b := hreach b (.inr (.inr rfl))
        have hfr' : ∀ fr ∈ st.pop.toList, ∀ y ∈ fr.2, y ∈ succs[fr.1]! :=
          fun fr h => hfr fr (List.mem_append_left _ h)
        have hbs : ∀ y ∈ ss, y ∈ succs[b]! := hfr (b, ss) (by simp)
        cases ss with
        | nil =>
          simp only [hb, Id.run_pure, ForInStep.value, dfsBlocks, Array.toList_push, List.mem_append,
            List.mem_cons, List.not_mem_nil, or_false]
          refine ⟨fun x hx => ?_, hfr'⟩
          rcases hx with (h | rfl) | h
          · exact hreach x (.inl h)
          · exact hbr
          · exact hreach x (.inr (.inl h))
        | cons x rest =>
          simp only [hb]
          have hrx : CfgReach succs x := .step hbr (hbs x (List.mem_cons_self ..))
          split <;>
          · simp only [Id.run_pure, ForInStep.value, dfsBlocks, Array.toList_push, List.map_append,
              List.mem_append, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
            first
            | (refine ⟨fun y hy => ?_, fun fr h y hy => ?_⟩
               · rcases hy with h | (h | h) | h
                 · exact hreach y (.inl h)
                 · exact hreach y (.inr (.inl h))
                 · subst h; exact hbr
                 · subst h; exact hrx
               · rcases h with (h | rfl) | rfl
                 · exact hfr' fr h y hy
                 · exact hbs y (List.mem_cons_of_mem _ hy)
                 · exact hy)
            | (refine ⟨fun y hy => ?_, fun fr h y hy => ?_⟩
               · rcases hy with h | h | h
                 · exact hreach y (.inl h)
                 · exact hreach y (.inr (.inl h))
                 · subst h; exact hbr
               · rcases h with h | rfl
                 · exact hfr' fr h y hy
                 · exact hbs y (List.mem_cons_of_mem _ hy))
    · intro s hs x hx
      exact hs.1 x (List.mem_append_left _ hx)

end Opt

namespace Opt
open Clif

theorem build_preds_eq (f : Function) : (Cfg.build f).preds =
    (Cfg.build f).succs.toList.zipIdx.foldl (fun p x => x.1.foldl (fun b a => b.modify a (· ++ [x.2])) p)
      (Array.replicate f.blocks.length []) := by
  unfold Cfg.build
  simp only [pure_bind, Array.forIn_pure_yield_eq_foldl, List.forIn_pure_yield_eq_foldl, Id.run_pure,
    Id.run_bind]
  rw [← Array.foldl_toList, Array.toList_zipIdx]
  simp

theorem preds_fold_mem (b x : Nat) : ∀ (L : List (List Nat × Nat)) (p : Array (List Nat)), b < p.size →
    (x ∈ (L.foldl (fun p y => y.1.foldl (fun c a => c.modify a (· ++ [y.2])) p) p)[b]! ↔
      x ∈ p[b]! ∨ ∃ y ∈ L, y.2 = x ∧ b ∈ y.1) := by
  intro L
  induction L with
  | nil => intro p _; simp
  | cons y L ih =>
    intro p hb
    have inner : ∀ (ss : List Nat) (q : Array (List Nat)), b < q.size →
        (q.size = (ss.foldl (fun c a => c.modify a (· ++ [y.2])) q).size) ∧
        (x ∈ (ss.foldl (fun c a => c.modify a (· ++ [y.2])) q)[b]! ↔ x ∈ q[b]! ∨ (y.2 = x ∧ b ∈ ss)) := by
      intro ss
      induction ss with
      | nil => intro q _; simp
      | cons a ss ih2 =>
        intro q hq
        rw [List.foldl_cons]
        have hq' : b < (q.modify a (· ++ [y.2])).size := by simpa using hq
        obtain ⟨h1, h2⟩ := ih2 _ hq'
        refine ⟨by rw [← h1]; simp, ?_⟩
        rw [h2, getElem!_modify_list]
        by_cases hab : a = b
        · subst hab
          simp [hq, List.mem_append]
          constructor
          · rintro ((h | h) | h) <;> simp_all
          · rintro (h | ⟨h1, h2⟩) <;> simp_all
        · simp only [hab, false_and, ite_false, List.mem_cons]
          constructor
          · rintro (h | ⟨h1, h2⟩)
            · exact .inl h
            · exact .inr ⟨h1, .inr h2⟩
          · rintro (h | ⟨h1, h2 | h2⟩)
            · exact .inl h
            · exact absurd h2.symm hab
            · exact .inr ⟨h1, h2⟩
    rw [List.foldl_cons, ih _ (by rw [← (inner y.1 p hb).1]; exact hb), (inner y.1 p hb).2]
    simp only [List.mem_cons]
    constructor
    · rintro ((h | ⟨h1, h2⟩) | ⟨z, hz, h3, h4⟩)
      · exact .inl h
      · exact .inr ⟨y, .inl rfl, h1, h2⟩
      · exact .inr ⟨z, .inr hz, h3, h4⟩
    · rintro (h | ⟨z, rfl | hz, h3, h4⟩)
      · exact .inl (.inl h)
      · exact .inl (.inr ⟨h3, h4⟩)
      · exact .inr ⟨z, hz, h3, h4⟩

/-- `preds` is the converse of `succs`. -/
theorem build_preds_mem (f : Function) {b x : Nat} (hb : b < f.blocks.length) :
    x ∈ (Cfg.build f).preds[b]! ↔ x < f.blocks.length ∧ b ∈ (Cfg.build f).succs[x]! := by
  rw [build_preds_eq, preds_fold_mem b x _ _ (by simpa using hb)]
  have h0 : (Array.replicate f.blocks.length ([] : List Nat))[b]! = [] := by
    simp [getElem!_def, Array.getElem?_replicate, hb]
  rw [h0]
  simp only [List.not_mem_nil, false_or, List.mem_zipIdx_iff_getElem?]
  constructor
  · rintro ⟨⟨ss, i⟩, hi, rfl, hss⟩
    simp only [Array.getElem?_toList] at hi
    have hil : i < (Cfg.build f).succs.size := (Array.getElem?_eq_some_iff.1 hi).1
    rw [build_succs_size] at hil
    refine ⟨hil, ?_⟩
    simp only [getElem!_def, hi]; exact hss
  · rintro ⟨hx, hbs⟩
    have hx' : x < (Cfg.build f).succs.size := by rw [build_succs_size]; exact hx
    refine ⟨((Cfg.build f).succs[x], x), by simp [Array.getElem?_toList, hx'], rfl, ?_⟩
    simpa [getElem!_def, hx'] using hbs

/-- The successors of a block are its branch targets. -/
theorem build_succs_mem (f : Function) {a x : Nat} {b : Block} (hb : f.blocks[a]? = some b) :
    x ∈ (Cfg.build f).succs[a]! ↔ ∃ id ∈ termSuccs b.term, (Cfg.build f).index.get? id = some x := by
  have hal : a < f.blocks.length := (List.getElem?_eq_some_iff.1 hb).1
  rw [build_succs]
  simp only [getElem!_def, Array.getElem?_map, List.getElem?_toArray, hb, Option.map_some]
  rw [List.mem_eraseDups, List.mem_filterMap]

theorem dominates_sound_loop (idom : Array (Option Nat)) (a : Nat) :
    ∀ (n : List Nat) (x : Nat),
      (forIn (m := Id) n ((none : Option Bool), x) fun _ s =>
        if (s.snd == a) = true then pure (ForInStep.done (some true, s.snd))
        else match idom[s.snd]! with
          | some y => pure (ForInStep.yield (none, y))
          | none => pure (ForInStep.done (some false, s.snd))).run.fst = some true → Anc idom a x
  | [], x, h => by simp at h
  | _ :: n, x, h => by
    rw [List.forIn_cons] at h
    by_cases hxa : x = a
    · subst hxa; exact .refl _
    · have hne : (x == a) = false := by simpa using hxa
      simp only [hne, Bool.false_eq_true, ite_false] at h
      cases hc : idom[x]! with
      | none => simp [hc] at h
      | some c =>
        simp only [hc, pure_bind] at h
        exact .up (by rw [← getElem!_opt]; exact hc) (dominates_sound_loop idom a n c h)

/-- **`Cfg.dominates` is sound**: it finds a tree ancestor. -/
theorem dominates_sound {c : Cfg} {a b : Nat} (h : c.dominates a b = true) : Anc c.idom a b := by
  unfold Cfg.dominates at h
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range'] at h
  split at h
  · simp [pure] at h
  · have key := dominates_sound_loop c.idom a (List.range' 0 [:c.size + 1].size) b
    generalize forIn (m := Id) (List.range' 0 [:c.size + 1].size) ((none : Option Bool), b) _ = F at key h
    rcases F with ⟨o, n⟩
    cases o with
    | none => simp [bind, pure] at h
    | some r =>
      cases r with
      | false => simp [bind, pure] at h
      | true => exact key rfl

/-- Tree ancestors of a block are comparable. -/
theorem Anc.total {idom : Array (Option Nat)} {a b x : Nat} (ha : Anc idom a x) (hb : Anc idom b x) :
    Anc idom a b ∨ Anc idom b a := by
  induction ha generalizing b with
  | refl => exact .inr hb
  | up hc ha ih =>
    cases hb with
    | refl => exact .inl (.up hc ha)
    | up hc' hb' => rw [hc] at hc'; cases hc'; exact ih hb'

end Opt

namespace Opt
open Clif

theorem forIn_inv_mem {α σ : Type} (l : List α) (init : σ) (f : α → σ → Id (ForInStep σ)) (P : σ → Prop)
    (h0 : P init) (hf : ∀ a ∈ l, ∀ s, P s → P (f a s).run.value) : P (forIn l init f).run := by
  induction l generalizing init with
  | nil => simpa using h0
  | cons a l ih =>
    rw [List.forIn_cons]
    have := hf a (List.mem_cons_self ..) init h0
    cases hfa : f a init with
    | done b => rw [hfa] at this; simp only [Id.run_bind]; exact this
    | yield b =>
      rw [hfa] at this; simp only [Id.run_bind]
      exact ih b this fun a ha => hf a (List.mem_cons_of_mem _ ha)

/-- The facts of a natural loop that LICM uses: the header is in the body, every body block is a
tree descendant of the header, and the body is closed under (reachable) predecessors of its
non-header blocks. -/
def LoopOk (c : Cfg) (lp : Cfg.Loop) : Prop :=
  lp.body.contains lp.header = true ∧ (∀ b, lp.body.contains b = true → Anc c.idom lp.header b) ∧
    (∀ b, lp.body.contains b = true → b ≠ lp.header → ∀ p ∈ c.preds[b]!, c.reachable p = true →
      lp.body.contains p = true) ∧ ∀ b, lp.body.contains b = true → b < c.size

section Loops

variable {c : Cfg} {h : Nat}
  (hpl : ∀ b : Nat, ∀ p ∈ c.preds[b]!, p < c.size)
  (hedge : ∀ b p : Nat, p ∈ c.preds[b]! → c.reachable p = true → ∀ x : Nat, c.idom[b]?.join = some x →
    Anc c.idom x p)

/-- The invariant of the body search of header `h`. -/
def LJ (c : Cfg) (h : Nat) (s : Std.HashSet Nat × Array Nat) : Prop :=
  (∀ x, s.1.contains x = true → x < c.size ∧ Anc c.idom h x) ∧ s.1.contains h = true ∧
    (∀ x ∈ s.2.toList, x < c.size ∧ (c.reachable x = true → Anc c.idom h x)) ∧
    (∀ b, s.1.contains b = true → b ≠ h → ∀ p ∈ c.preds[b]!, c.reachable p = true →
      s.1.contains p = true ∨ p ∈ s.2.toList)

theorem filter_length_le {α : Type} {l : List α} {p q : α → Bool}
    (hpq : ∀ k ∈ l, q k = true → p k = true) : (l.filter q).length ≤ (l.filter p).length := by
  induction l with
  | nil => simp
  | cons b l ih =>
    simp only [List.filter_cons]
    have := ih fun k hk => hpq k (List.mem_cons_of_mem _ hk)
    by_cases hqb : q b = true
    · simp [hqb, hpq b (List.mem_cons_self ..)]; omega
    · simp only [hqb, Bool.false_eq_true, ite_false]
      split <;> simp <;> omega

/-- The potential of the search: blocks not in the body, plus one while work is left. -/
def lpot (c : Cfg) (s : Std.HashSet Nat × Array Nat) : Nat :=
  ((List.range c.size).filter fun x => !s.1.contains x).length + (if s.2.isEmpty then 0 else 1)

/-- The body of one round (processing the work list). -/
def lbStep (c : Cfg) (s : Std.HashSet Nat × Array Nat) (b : Nat) : Std.HashSet Nat × Array Nat :=
  if (s.1.contains b || !c.reachable b) = true then (s.1, s.2) else (s.1.insert b, s.2 ++ c.preds[b]!.toArray)

include hpl hedge in
/-- One round keeps the invariant (and lowers the potential). -/
theorem lround {body0 : Std.HashSet Nat} {W : Array Nat} (hJ : LJ c h (body0, W)) (hW : W.isEmpty = false) :
    LJ c h (W.toList.foldl (lbStep c) (body0, #[])) ∧ lpot c (W.toList.foldl (lbStep c) (body0, #[])) < lpot c (body0, W) := by
  obtain ⟨hJ1, hJ2, hJ3, hJ4⟩ := hJ
  simp only at hJ1 hJ2 hJ3 hJ4
  -- the invariant of the fold over a prefix
  let IJ : List Nat → Std.HashSet Nat × Array Nat → Prop := fun pre s =>
    (∀ x, s.1.contains x = true → x < c.size ∧ Anc c.idom h x) ∧
    (∀ x, body0.contains x = true → s.1.contains x = true) ∧
    (∀ x ∈ s.2.toList, x < c.size ∧ (c.reachable x = true → Anc c.idom h x)) ∧
    (∀ b, s.1.contains b = true → body0.contains b = false → ∀ p ∈ c.preds[b]!,
      c.reachable p = true → p ∈ s.2.toList) ∧
    (∀ x ∈ pre, s.1.contains x = true ∨ c.reachable x = false) ∧
    (s.2.toList = [] ∨ ∃ x, x < c.size ∧ s.1.contains x = true ∧ body0.contains x = false)
  have key : ∀ (pre post : List Nat), pre ++ post = W.toList → ∀ s, IJ pre s → IJ W.toList (post.foldl (lbStep c) s) := by
    intro pre post
    induction post generalizing pre with
    | nil => intro he s hs; simpa [← he] using hs
    | cons x post ih =>
      intro he s hs
      rw [List.foldl_cons]
      refine ih (pre ++ [x]) (by simpa using he) _ ?_
      obtain ⟨i1, i2, i3, i4, i5, i6⟩ := hs
      have hxW : x ∈ W.toList := by rw [← he]; simp
      unfold lbStep
      split
      · rename_i hc
        refine ⟨i1, i2, i3, i4, fun y hy => ?_, i6⟩
        simp only [List.mem_append, List.mem_singleton] at hy
        rcases hy with hy | rfl
        · exact i5 y hy
        · simp only [Bool.or_eq_true, Bool.not_eq_true'] at hc
          rcases hc with hc | hc
          · exact .inl hc
          · exact .inr hc
      · rename_i hc
        simp only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_false] at hc
        obtain ⟨hcx, hrx⟩ := hc
        have hcx' : s.1.contains x = false := by simpa using hcx
        obtain ⟨hxN, hxA⟩ := hJ3 x hxW
        have hxA := hxA hrx
        have hxh : x ≠ h := by
          rintro rfl; rw [i2 _ hJ2] at hcx'; cases hcx'
        have hb0x : body0.contains x = false := by
          cases hb : body0.contains x
          · rfl
          · rw [i2 x hb] at hcx'; cases hcx'
        obtain ⟨cx, hcx2, hacx⟩ := hxA.strict (Ne.symm hxh)
        refine ⟨fun y hy => ?_, fun y hy => ?_, fun y hy => ?_, fun b hb hb0 p hp hrp => ?_,
          fun y hy => ?_, .inr ⟨x, hxN, by simp, hb0x⟩⟩
        · simp only [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq] at hy
          rcases hy with rfl | hy
          · exact ⟨hxN, hxA⟩
          · exact i1 y hy
        · simp [i2 y hy]
        · simp only [Array.toList_append, List.mem_append, Array.mem_toList_iff, List.mem_toArray] at hy
          rcases hy with hy | hy
          · exact i3 y (by simpa using hy)
          · exact ⟨hpl x y hy, fun hr => hacx.trans (hedge x y hy hr cx hcx2)⟩
        · simp only [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq] at hb
          simp only [Array.toList_append, List.mem_append]
          rcases hb with rfl | hb
          · exact .inr (by simpa using hp)
          · exact .inl (i4 b hb hb0 p hp hrp)
        · simp only [List.mem_append, List.mem_singleton] at hy
          rcases hy with hy | rfl
          · rcases i5 y hy with h1 | h1
            · exact .inl (by simp [h1])
            · exact .inr h1
          · exact .inl (by simp)
  have hI := key [] W.toList rfl (body0, #[]) ⟨hJ1, fun _ h => h, (by simp),
    (fun b hb hb0 => by simp only at hb; rw [hb] at hb0; cases hb0), (by simp), .inl (by simp)⟩
  obtain ⟨i1, i2, i3, i4, i5, i6⟩ := hI
  generalize W.toList.foldl (lbStep c) (body0, #[]) = s at i1 i2 i3 i4 i5 i6
  refine ⟨⟨i1, i2 h hJ2, i3, fun b hb hbh p hp hrp => ?_⟩, ?_⟩
  · cases hb0 : body0.contains b
    · exact .inr (i4 b hb hb0 p hp hrp)
    · rcases hJ4 b hb0 hbh p hp hrp with h1 | h1
      · exact .inl (i2 p h1)
      · rcases i5 p h1 with h2 | h2
        · exact .inl h2
        · rw [hrp] at h2; cases h2
  · have hle : ((List.range c.size).filter fun x => !s.1.contains x).length ≤
        ((List.range c.size).filter fun x => !body0.contains x).length := by
      apply filter_length_le
      intro x _ hx
      cases hb : body0.contains x
      · rfl
      · simp [i2 x hb] at hx
    simp only [lpot, hW, Bool.false_eq_true, ite_false]
    rcases i6 with h6 | ⟨x, hxN, hx1, hx0⟩
    · have : s.2.isEmpty = true := by simp [Array.isEmpty_iff, ← Array.toList_eq_nil_iff, h6]
      simp only [this, ite_true]; omega
    · have hlt : ((List.range c.size).filter fun x => !s.1.contains x).length <
          ((List.range c.size).filter fun x => !body0.contains x).length := by
        refine filter_length_lt (fun y _ hy => ?_) (List.mem_range.2 hxN) (by simp [hx0]) (by simp [hx1])
        cases hb : body0.contains y
        · rfl
        · simp [i2 y hb] at hy
      split <;> omega

include hpl hedge in
/-- The body search of header `h` yields a natural loop with the facts of `LoopOk`. -/
theorem loopBody_ok (hh : h < c.size) :
    LoopOk c { header := h, body := (forIn (m := Id) (List.range' 0 [:c.size + 1].size)
      ((∅ : Std.HashSet Nat).insert h, (c.preds[h]!.filter fun b => c.dominates h b).toArray)
      fun _ s =>
        if s.2.isEmpty = true then pure (ForInStep.done (s.1, s.2))
        else do
          let s' ← forIn s.2 (s.1, (#[] : Array Nat)) fun b s =>
            if (s.1.contains b || !c.reachable b) = true then pure (ForInStep.yield (s.1, s.2))
            else pure (ForInStep.yield (s.1.insert b, s.2 ++ c.preds[b]!.toArray))
          pure (ForInStep.yield (s'.1, s'.2))).run.1 } := by
  have key : ∀ X : Std.HashSet Nat × Array Nat, LJ c h X ∧ X.2.isEmpty = true →
      LoopOk c { header := h, body := X.1 } := by
    rintro X ⟨⟨j1, j2, -, j4⟩, hE⟩
    refine ⟨j2, fun b hb => (j1 b hb).2, fun b hb hbh p hp hrp => ?_, fun b hb => (j1 b hb).1⟩
    rcases j4 b hb hbh p hp hrp with h1 | h1
    · exact h1
    · simp [Array.isEmpty_iff] at hE; simp [hE] at h1
  apply key
  refine forIn_pot _ _ _ (LJ c h) (fun s => LJ c h s ∧ s.2.isEmpty = true) (lpot c) ?_ ?_ ?_
  · refine ⟨fun x hx => ?_, by simp, fun x hx => ?_, fun b hb hbh => ?_⟩
    · simp only [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq] at hx
      rcases hx with rfl | hx
      · exact ⟨hh, .refl _⟩
      · simp at hx
    · simp only [List.mem_filter, List.toList_toArray] at hx
      exact ⟨hpl h x hx.1, fun _ => dominates_sound hx.2⟩
    · simp only [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq] at hb
      rcases hb with rfl | hb
      · exact absurd rfl hbh
      · simp at hb
  · simp only [lpot, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one,
      List.length_range']
    have : ((List.range c.size).filter fun x => !((∅ : Std.HashSet Nat).insert h).contains x).length <
        ((List.range c.size).filter fun _ => true).length :=
      filter_length_lt (fun _ _ _ => rfl) (List.mem_range.2 hh) rfl (by simp)
    have hall : ((List.range c.size).filter fun _ => true) = List.range c.size :=
      List.filter_eq_self.2 (by simp)
    rw [hall, List.length_range] at this
    split <;> omega
  · intro a s hs
    by_cases hE : s.2.isEmpty = true
    · simp only [hE, ite_true, Id.run_pure]
      exact ⟨hs, by simpa using hE⟩
    · simp only [hE, Bool.false_eq_true, ite_false]
      rw [← Array.forIn_toList, forIn_yield_foldl _ (lbStep c) (fun b s => by
        unfold lbStep; split <;> rfl)]
      simp only [pure_bind, Id.run_pure]
      exact lround hpl hedge hs (by simpa using hE)

include hpl hedge in
/-- **Every loop of `Cfg.loops` has the facts of `LoopOk`.** -/
theorem loops_ok (hr : ∀ x ∈ c.rpo.toList, x < c.size) : ∀ lp ∈ c.loops.toList, LoopOk c lp := by
  unfold Cfg.loops
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure]
  rw [← Array.forIn_toList]
  refine forIn_inv_mem _ _ _ (P := fun out : Array Cfg.Loop => ∀ lp ∈ out.toList, LoopOk c lp)
    (by simp) ?_
  intro h' hmem out hout
  have hh := hr h' hmem
  by_cases hE : (c.preds[h']!.filter fun b => c.dominates h' b).isEmpty = true
  · simp only [hE, ite_true, Id.run_pure, ForInStep.value]; exact hout
  · simp only [hE, Bool.false_eq_true, ite_false, Id.run_bind, Id.run_pure, ForInStep.value]
    intro lp hlp
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hlp
    rcases hlp with hlp | rfl
    · exact hout lp hlp
    · exact loopBody_ok hpl hedge hh

end Loops

end Opt

namespace Opt
open Clif

section BuildLoops

variable {f : Function} {info : Info} (hc : Checked f info)
include hc

theorem checked_cfg : info.cfg = Cfg.build f := by rw [hc.info_eq]; rfl

theorem build_size_eq : (Cfg.build f).size = f.blocks.length := by simp [Cfg.size, Cfg.build]

theorem build_preds_lt : ∀ b : Nat, ∀ p ∈ (Cfg.build f).preds[b]!, p < (Cfg.build f).size := by
  intro b p hp
  rw [build_size_eq hc]
  by_cases hb : b < f.blocks.length
  · exact ((build_preds_mem f hb).1 hp).1
  · have : (Cfg.build f).preds[b]! = [] := by
      have hs := build_preds_size f
      simp [getElem!_def, Array.getElem?_eq_none (by omega : (Cfg.build f).preds.size ≤ b)]; rfl
    rw [this] at hp; cases hp

/-- An edge `a → x` (`x ∈ succs a`): `idom x` is a tree ancestor of `a`. -/
theorem build_edge {a x : Nat} (hx : x ∈ (Cfg.build f).succs[a]!) :
    a < f.blocks.length ∧ x < f.blocks.length ∧
      ∀ cx, (Cfg.build f).idom[x]?.join = some cx → Anc (Cfg.build f).idom cx a := by
  have hal : a < f.blocks.length := by
    rcases Nat.lt_or_ge a f.blocks.length with hal | hal
    · exact hal
    · have : (Cfg.build f).succs[a]! = [] := by
        simp [getElem!_def, Array.getElem?_eq_none (by rw [build_succs_size]; omega)]; rfl
      rw [this] at hx; cases hx
  obtain ⟨b, hb⟩ : ∃ b, f.blocks[a]? = some b := ⟨_, List.getElem?_eq_getElem hal⟩
  obtain ⟨id, hid, hix⟩ := (build_succs_mem f hb).1 hx
  have hxl : x < f.blocks.length := (build_index_lt (by rwa [Std.HashMap.get?_eq_getElem?] at hix)).1
  obtain ⟨j, b', hj, hbj, -, hanc⟩ := hc.wf.edges a b hb id hid
  have hjx : j = x := by
    simp only [wfData, Std.HashMap.get?_eq_getElem?] at hj hix
    rw [checked_cfg hc] at hj
    rw [hj] at hix; exact Option.some.inj hix
  subst hjx
  refine ⟨hal, hxl, fun cx hcx => ?_⟩
  have := hanc cx (by simp only [wfData]; rw [checked_cfg hc]; exact hcx)
  simpa [wfData, checked_cfg hc] using this

theorem build_hedge : ∀ b p : Nat, p ∈ (Cfg.build f).preds[b]! → (Cfg.build f).reachable p = true →
    ∀ x : Nat, (Cfg.build f).idom[b]?.join = some x → Anc (Cfg.build f).idom x p := by
  intro b p hp _ x hx
  have hb : b < f.blocks.length := by
    rcases Nat.lt_or_ge b f.blocks.length with hb | hb
    · exact hb
    · have : (Cfg.build f).preds[b]! = [] := by
        have hs := build_preds_size f
        simp [getElem!_def, Array.getElem?_eq_none (by omega : (Cfg.build f).preds.size ≤ b)]; rfl
      rw [this] at hp; cases hp
  exact (build_edge hc ((build_preds_mem f hb).1 hp).2).2.2 x hx

/-- **The loops of a checked function have the facts of `LoopOk`.** -/
theorem build_loops_ok : ∀ lp ∈ (Cfg.build f).loops.toList, LoopOk (Cfg.build f) lp :=
  loops_ok (build_preds_lt hc) (build_hedge hc) fun x hx => by
    rw [build_size_eq hc]; exact build_rpo_lt f hx

theorem build_reach_lt {z : Nat} (h : CfgReach (Cfg.build f).succs z) : z < f.blocks.length := by
  cases h with
  | entry => have := hc.core.1; rwa [build_size_eq hc] at this
  | step _ hx => exact (build_edge hc hx).2.1

theorem build_reach_reachable {z : Nat} (h : CfgReach (Cfg.build f).succs z) :
    (Cfg.build f).reachable z = true := by
  have hn : (Cfg.build f).succs.size ≠ 0 := by
    rw [build_succs_size]; have := hc.core.1; rw [build_size_eq hc] at this; omega
  obtain ⟨h0, hcl⟩ := postorder_closed _ (build_succs_lt f) hn
  have : z ∈ (Cfg.postorder (Cfg.build f).succs).toList := by
    induction h with
    | entry => exact h0
    | step ha hx ih => exact (hcl _ ih).2 _ hx
  exact (build_reachable_iff f (build_reach_lt hc h)).2 this

theorem build_reachable_reach {z : Nat} (hz : z < f.blocks.length) :
    CfgReach (Cfg.build f).succs z := by
  have := hc.core.2.2.1 z (by rw [build_size_eq hc]; exact hz)
  exact postorder_reach _ z ((build_reachable_iff f hz).1 this)

/-- **A block between the header and a loop block in the dominator tree is in the loop.** -/
theorem loop_between {lp : Cfg.Loop} (hlp : LoopOk (Cfg.build f) lp) {y bi : Nat}
    (hbi : lp.body.contains bi = true) (hy1 : Anc (Cfg.build f).idom lp.header y)
    (hy2 : y ≠ lp.header) (hy3 : Anc (Cfg.build f).idom y bi) : lp.body.contains y = true := by
  have hrank : ∀ b c, (Cfg.build f).idom[b]?.join = some c → (wfData f info).rank c < (wfData f info).rank b := by
    have := hc.wf.rank; simpa [wfData, checked_cfg hc] using this
  have hroot : (Cfg.build f).idom[0]?.join = none := by
    have := hc.wf.root; simpa [wfData, checked_cfg hc] using this
  refine Classical.byContradiction fun hyn => ?_
  have hyb : bi ≠ y := by rintro rfl; exact hyn hbi
  suffices ∀ z, CfgReach (Cfg.build f).succs z →
      ¬ (lp.body.contains z = true ∧ Anc (Cfg.build f).idom y z ∧ z ≠ y) by
    have hbl : bi < f.blocks.length := by
      have := hlp.2.2.2 bi hbi; rwa [build_size_eq hc] at this
    exact this bi (build_reachable_reach hc hbl) ⟨hbi, hy3, hyb⟩
  intro z hz
  induction hz with
  | entry =>
    rintro ⟨-, ha, hne⟩
    cases ha with
    | refl => exact hne rfl
    | up hc0 _ => rw [hroot] at hc0; cases hc0
  | step ha hx ih =>
    rename_i a x
    rintro ⟨hxb, hyx, hxy⟩
    have hxh : x ≠ lp.header := by
      rintro rfl; exact hy2 (Anc.antisymm hrank hy1 hyx).symm
    obtain ⟨cx, hcx, hycx⟩ := hyx.strict (Ne.symm hxy)
    obtain ⟨hal, hxl, hanc⟩ := build_edge hc hx
    have hpa : a ∈ (Cfg.build f).preds[x]! := (build_preds_mem f hxl).2 ⟨hal, hx⟩
    have hab : lp.body.contains a = true :=
      hlp.2.2.1 x hxb hxh a hpa (build_reach_reachable hc ha)
    exact ih ⟨hab, hycx.trans (hanc cx hcx), fun he => by subst he; exact hyn hab⟩

end BuildLoops

end Opt

namespace Opt
open Clif

/-! ## Moving one statement to the end of a block -/

/-- Remove `t` from every body and append it to block `hb`. -/
def moveB (hb : Nat) (t : Stmt) (x : Block × Nat) : Block :=
  { x.1 with body := x.1.body.filter (· != t) ++ (if x.2 = hb then [t] else []) }

def moveF (g : Function) (hb : Nat) (t : Stmt) : Function :=
  { g with blocks := g.blocks.zipIdx.map (moveB hb t) }

theorem moveF_get (g : Function) (hb : Nat) (t : Stmt) (i : Nat) :
    (moveF g hb t).blocks[i]? = (g.blocks[i]?).map fun b => moveB hb t (b, i) := by
  simp only [moveF, List.getElem?_map, List.getElem?_zipIdx]
  cases g.blocks[i]? <;> simp

theorem moveF_build (g : Function) (hb : Nat) (t : Stmt) : Cfg.build (moveF g hb t) = Cfg.build g := by
  apply build_congr
  apply List.ext_getElem?
  intro i
  simp only [cfgShape, List.getElem?_map]
  rw [moveF_get]
  cases g.blocks[i]? <;> simp [moveB]

theorem perm_flatMap_congr {α β : Type} (l : List α) {F G : α → List β} (h : ∀ a ∈ l, (F a).Perm (G a)) :
    (l.flatMap F).Perm (l.flatMap G) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons]
    exact (h a (List.mem_cons_self ..)).append (ih fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem perm_flatMap_append {α β : Type} (l : List α) (F G : α → List β) :
    (l.flatMap fun x => F x ++ G x).Perm (l.flatMap F ++ l.flatMap G) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.append_assoc]
    refine List.Perm.append_left _ ?_
    refine (List.Perm.append_left _ ih).trans ?_
    simp only [← List.append_assoc]
    exact List.Perm.append_right _ List.perm_append_comm

/-- The data of a move: `t` (`v = …`, pure) is statement `jt` of block `bi`; it goes to the end
of `hb`, a strict tree ancestor of `bi`. -/
structure MoveOk (g : Function) (hb : Nat) (t : Stmt) (bi : Nat) (b : Block) (jt : Nat) (v : ValueId) :
    Prop where
  unique : UniqueDefs g
  arity : Arity g
  nodup : ((defList g).map (·.1)).Nodup
  wf : Wf g (wfData g (coreInfo g))
  hb_b : g.blocks[bi]? = some b
  ht : b.body[jt]? = some t
  hres : t.results = [v]
  hne : hb ≠ bi
  hanc : Anc (Cfg.build g).idom hb bi
  hbl : hb < g.blocks.length

section Move

variable {g : Function} {hb : Nat} {t : Stmt} {bi : Nat} {b : Block} {jt : Nat} {v : ValueId}
  (hm : MoveOk g hb t bi b jt v)
include hm

/-- `t` occurs only at its position. -/
theorem MoveOk.only {i j : Nat} {b' : Block} (hb' : g.blocks[i]? = some b') (hj : b'.body[j]? = some t) :
    i = bi ∧ j = jt := by
  have := site_unique hm.unique (mem_defSites.2 ⟨i, b', hb', .inr ⟨j, t, hj, by simp [hm.hres], rfl⟩⟩)
    (show (v, (bi, jt + 1)) ∈ defSites g from
      mem_defSites.2 ⟨bi, b, hm.hb_b, .inr ⟨jt, t, hm.ht, by simp [hm.hres], rfl⟩⟩)
  simpa using this

theorem MoveOk.not_mem {i : Nat} {b' : Block} (hb' : g.blocks[i]? = some b') (hi : i ≠ bi) :
    t ∉ b'.body := by
  intro h
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 h
  exact hi (hm.only hb' hj).1

theorem MoveOk.filter_id {i : Nat} {b' : Block} (hb' : g.blocks[i]? = some b') (hi : i ≠ bi) :
    b'.body.filter (· != t) = b'.body :=
  List.filter_eq_self.2 fun st hst => by
    simp only [bne_iff_ne, ne_eq]; rintro rfl; exact hm.not_mem hb' hi hst

theorem MoveOk.mem_defSites {x : ValueId} {s : Nat × Nat} :
    (x, s) ∈ defSites (moveF g hb t) ↔ ∃ i b, g.blocks[i]? = some b ∧
      ((∃ p ∈ b.params, p.1 = x ∧ s = (i, 0)) ∨
        (∃ j st, b.body[j]? = some st ∧ st ≠ t ∧ x ∈ st.results ∧
          s = (i, fidx (· != t) b.body j + 1)) ∨
        (i = hb ∧ x ∈ t.results ∧ s = (i, b.body.length + 1))) := by
  rw [Opt.mem_defSites]
  simp only [moveF_get, Option.map_eq_some_iff]
  constructor
  · rintro ⟨i, b', ⟨b, hb', rfl⟩, h | ⟨j', st, hst, hx, rfl⟩⟩
    · exact ⟨i, b, hb', .inl h⟩
    · simp only [moveB] at hst
      rcases Nat.lt_or_ge j' (b.body.filter (· != t)).length with hj | hj
      · rw [List.getElem?_append_left hj] at hst
        obtain ⟨j, hj', hp, rfl⟩ := exists_fidx _ b.body j' st hst
        refine ⟨i, b, hb', .inr (.inl ⟨j, st, hj', by simpa using hp, hx, rfl⟩)⟩
      · rw [List.getElem?_append_right hj] at hst
        split at hst
        · rename_i hih
          have hj0 : j' - (b.body.filter (· != t)).length = 0 := by
            rcases Nat.eq_zero_or_pos (j' - (b.body.filter (· != t)).length) with h | h
            · exact h
            · have : [t][j' - (b.body.filter (· != t)).length]? = none :=
                List.getElem?_eq_none (by simp only [List.length_singleton]; omega)
              rw [this] at hst; cases hst
          rw [hj0] at hst
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hst
          subst hst
          have hfl : (b.body.filter (· != t)).length = b.body.length := by
            rw [hm.filter_id hb' (by rw [hih]; exact hm.hne)]
          refine ⟨i, b, hb', .inr (.inr ⟨hih, hx, ?_⟩)⟩
          congr 1; omega
        · simp at hst
  · rintro ⟨i, b, hb', h | ⟨j, st, hj, hne, hx, rfl⟩ | ⟨hih, hx, rfl⟩⟩
    · exact ⟨i, _, ⟨b, hb', rfl⟩, .inl h⟩
    · refine ⟨i, _, ⟨b, hb', rfl⟩, .inr ⟨_, st, ?_, hx, rfl⟩⟩
      simp only [moveB]
      rw [List.getElem?_append_left (fidx_le_length _ b.body hj (by simpa using hne))]
      exact getElem?_filter_fidx _ b.body j st hj (by simpa using hne)
    · refine ⟨i, _, ⟨b, hb', rfl⟩, .inr ⟨b.body.length, t, ?_, hx, rfl⟩⟩
      simp only [moveB, hih, ite_true]
      rw [hm.filter_id hb' (by rw [hih]; exact hm.hne)]
      simp

omit hm in
theorem count_one_of_nodup_flatMap {α β : Type} [DecidableEq α] (F : α → List β) :
    ∀ (l : List α) (a : α), (l.flatMap F).Nodup → a ∈ l → F a ≠ [] → l.count a = 1
  | [], a, _, h, _ => by simp at h
  | x :: l, a, hn, ha, hF => by
    rw [List.flatMap_cons, List.nodup_append] at hn
    by_cases hxa : x = a
    · subst hxa
      have : l.count x = 0 := by
        rw [List.count_eq_zero]
        intro hx
        obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil _ hF
        exact hn.2.2 y hy y (List.mem_flatMap.2 ⟨x, hx, hy⟩) rfl
      simp [List.count_cons, this]
    · rw [List.count_cons]
      simp only [beq_iff_eq, hxa, ite_false, Nat.add_zero]
      exact count_one_of_nodup_flatMap F l a hn.2.1 (by simpa [Ne.symm hxa] using ha) hF

omit hm in
theorem flatMap_zipIdx_single {α β : Type} (L : List β) (k : Nat) :
    ∀ (l : List α) (n : Nat), ((l.zipIdx n).flatMap fun x => if x.2 = k then L else []) =
      if n ≤ k ∧ k < n + l.length then L else []
  | [], n => by simp; omega
  | a :: l, n => by
    rw [List.zipIdx_cons, List.flatMap_cons, flatMap_zipIdx_single L k l (n + 1)]
    simp only [List.length_cons]
    by_cases h : n = k
    · subst h; simp; intro h; omega
    · simp only [h, ite_false, List.nil_append]
      congr 1
      apply propext; omega

/-- The defined values are the same (as a multiset). -/
theorem MoveOk.perm : ((defSites (moveF g hb t)).map (·.1)).Perm ((defSites g).map (·.1)) := by
  rw [defSites_fst, defSites_fst]
  simp only [moveF, List.flatMap_map, moveB, Function.comp_def, List.flatMap_append]
  -- the values defined by `t`'s occurrences
  have hcnt : (g.blocks.flatMap (·.body)).count t = 1 := by
    refine count_one_of_nodup_flatMap (·.results) _ t ?_ ?_ (by simp [hm.hres])
    · have hs : ((g.blocks.flatMap (·.body)).flatMap (·.results)).Sublist ((defSites g).map (·.1)) := by
        rw [defSites_fst, List.flatMap_assoc]
        exact flatMap_sublist fun b _ => List.sublist_append_right _ _
      exact hs.nodup hm.unique
    · exact List.mem_flatMap.2 ⟨b, List.mem_of_getElem? hm.hb_b, List.mem_of_getElem? hm.ht⟩
  have hD : (g.blocks.flatMap fun b => (b.body.filter (· == t)).flatMap (·.results)) = t.results := by
    rw [← List.flatMap_assoc, ← List.filter_flatMap, List.filter_beq, hcnt]
    simp
  have hC : (g.blocks.zipIdx.flatMap fun x => (if x.2 = hb then [t] else []).flatMap (·.results)) =
      t.results := by
    have : (fun x : Block × Nat => (if x.2 = hb then [t] else []).flatMap (·.results)) =
        fun x => if x.2 = hb then t.results else [] := by
      funext x; split <;> simp
    rw [this, flatMap_zipIdx_single]
    simp [hm.hbl]
  -- split both sides into parameters, kept results, and `t`'s results
  have hR : (g.blocks.flatMap fun b => b.params.map (·.1) ++ b.body.flatMap (·.results)) =
      (g.blocks.zipIdx.flatMap fun x => x.1.params.map (·.1) ++ x.1.body.flatMap (·.results)) := by
    conv => lhs; rw [← List.zipIdx_map_fst 0 g.blocks]
    rw [List.flatMap_map]
  rw [hR]
  have hbody : ∀ (l : List Stmt), (l.flatMap (·.results)).Perm
      ((l.filter (· != t)).flatMap (·.results) ++ (l.filter (· == t)).flatMap (·.results)) := by
    intro l
    rw [← List.flatMap_append]
    refine List.Perm.flatMap_right _ ?_
    have := List.filter_append_perm (· != t) l
    have e : (fun x : Stmt => !(x != t)) = (· == t) := by funext x; simp [bne]
    rw [e] at this
    exact this.symm
  refine (perm_flatMap_append _ _ _).trans ?_
  refine List.Perm.trans ?_ (perm_flatMap_append _ _ _).symm
  refine List.Perm.append_left _ ?_
  refine (perm_flatMap_append _ _ _).trans ?_
  refine List.Perm.trans ?_ (perm_flatMap_congr _ (fun (x : Block × Nat) _ => (hbody x.1.body).symm))
  refine List.Perm.trans ?_ (perm_flatMap_append _ _ _).symm
  refine List.Perm.append_left _ ?_
  rw [hC]
  have : (g.blocks.zipIdx.flatMap fun x => (x.1.body.filter (· == t)).flatMap (·.results)) =
      (g.blocks.flatMap fun b => (b.body.filter (· == t)).flatMap (·.results)) := by
    conv => rhs; rw [← List.zipIdx_map_fst 0 g.blocks]
    rw [List.flatMap_map]
  rw [this, hD]

theorem MoveOk.mem_body {i : Nat} {b' : Block} (hb' : g.blocks[i]? = some b') {st : Stmt}
    (hst : st ∈ (moveB hb t (b', i)).body) : st ∈ b'.body ∨ st = t := by
  simp only [moveB, List.mem_append, List.mem_filter] at hst
  rcases hst with ⟨h, -⟩ | h
  · exact .inl h
  · split at h
    · simp at h; exact .inr h
    · simp at h

theorem MoveOk.arity' : Arity (moveF g hb t) := by
  intro b' hb' st hst
  simp only [moveF, List.mem_map] at hb'
  obtain ⟨⟨b0, i⟩, hi, rfl⟩ := hb'
  have hb0 : g.blocks[i]? = some b0 := List.mem_zipIdx_iff_getElem?.1 hi
  have : stmtTys (moveF g hb t) st = stmtTys g st := rfl
  rw [this]
  rcases hm.mem_body hb0 hst with h | rfl
  · exact hm.arity b0 (List.mem_of_getElem? hb0) st h
  · exact hm.arity b (List.mem_of_getElem? hm.hb_b) _ (List.mem_of_getElem? hm.ht)

theorem MoveOk.unique' : UniqueDefs (moveF g hb t) := hm.perm.nodup_iff.2 hm.unique

theorem MoveOk.nodup' : ((defList (moveF g hb t)).map (·.1)).Nodup := by
  rw [← defSites_map_fst hm.arity']; exact hm.unique'

/-- Every definition event of `g` has one in the output with the same value and type. -/
theorem MoveOk.event {e : DefEv} (he : e ∈ defList g) :
    ∃ e' ∈ defList (moveF g hb t), e'.1 = e.1 ∧ e'.2.1 = e.2.1 := by
  obtain ⟨i, b', hb', h⟩ := mem_defList.1 he
  have hb'' : (moveF g hb t).blocks[i]? = some (moveB hb t (b', i)) := by rw [moveF_get, hb']; rfl
  rcases h with ⟨p, hp, rfl⟩ | ⟨st, hst, hes⟩
  · exact ⟨_, mem_defList.2 ⟨i, _, hb'', .inl ⟨p, hp, rfl⟩⟩, rfl, rfl⟩
  · by_cases hst' : st = t
    · subst hst'
      obtain ⟨bh, hbh⟩ : ∃ bh, g.blocks[hb]? = some bh := ⟨_, List.getElem?_eq_getElem hm.hbl⟩
      have hbh' : (moveF g hb st).blocks[hb]? = some (moveB hb st (bh, hb)) := by
        rw [moveF_get, hbh]; rfl
      refine ⟨(e.1, e.2.1, hb), mem_defList.2 ⟨hb, _, hbh', .inr ⟨st, by simp [moveB], ?_⟩⟩, rfl, rfl⟩
      unfold stmtEvs at hes ⊢
      have : stmtTys (moveF g hb st) st = stmtTys g st := rfl
      rw [this]
      split at hes
      · obtain ⟨⟨r, ty⟩, hz, rfl⟩ := List.mem_map.1 hes
        exact List.mem_map.2 ⟨(r, ty), hz, rfl⟩
      · simp at hes
    · refine ⟨e, mem_defList.2 ⟨i, _, hb'', .inr ⟨st, ?_, hes⟩⟩, rfl, rfl⟩
      simp [moveB, hst, hst']

theorem MoveOk.event' {e : DefEv} (he : e ∈ defList (moveF g hb t)) :
    ∃ e0 ∈ defList g, e0.1 = e.1 ∧ e0.2.1 = e.2.1 := by
  obtain ⟨i, b', hb', h⟩ := mem_defList.1 he
  rw [moveF_get, Option.map_eq_some_iff] at hb'
  obtain ⟨b0, hb0, rfl⟩ := hb'
  rcases h with ⟨p, hp, rfl⟩ | ⟨st, hst, hes⟩
  · exact ⟨_, mem_defList.2 ⟨i, b0, hb0, .inl ⟨p, hp, rfl⟩⟩, rfl, rfl⟩
  · have hev : ∀ {f1 f2 : Function} (j : Nat), f1.externs = f2.externs → ∀ e ∈ stmtEvs f1 i st,
        (e.1, e.2.1, j) ∈ stmtEvs f2 j st := by
      intro f1 f2 j hx e he
      unfold stmtEvs stmtTys at he ⊢
      rw [← hx]
      split at he
      · obtain ⟨⟨r, ty⟩, hz, rfl⟩ := List.mem_map.1 he
        exact List.mem_map.2 ⟨(r, ty), hz, rfl⟩
      · simp at he
    rcases hm.mem_body hb0 hst with h | rfl
    · exact ⟨_, mem_defList.2 ⟨i, b0, hb0, .inr ⟨st, h, hev i rfl e hes⟩⟩, rfl, rfl⟩
    · exact ⟨_, mem_defList.2 ⟨bi, b, hm.hb_b, .inr ⟨_, List.mem_of_getElem? hm.ht, hev bi rfl e hes⟩⟩,
        rfl, rfl⟩

/-- **Types are kept.** -/
theorem MoveOk.tm (x : ValueId) :
    (wfData (moveF g hb t) (coreInfo (moveF g hb t))).tm x = (wfData g (coreInfo g)).tm x := by
  simp only [wfData, coreInfo, Std.HashMap.get?_eq_getElem?]
  have hn' := hm.nodup'
  by_cases hx : x ∈ (defList g).map (·.1)
  · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
    obtain ⟨e', he', h1, h2⟩ := hm.event he
    rw [((defsState_get g hm.nodup).1 e he).1, ← h1, ((defsState_get _ hn').1 e' he').1, h2]
  · have hx' : x ∉ (defList (moveF g hb t)).map (·.1) := by
      intro h
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 h
      obtain ⟨e0, he0, h1, -⟩ := hm.event' he
      exact hx (List.mem_map.2 ⟨e0, he0, h1⟩)
    rw [((defsState_get g hm.nodup).2 x hx).1, ((defsState_get _ hn').2 x hx').1]

theorem MoveOk.dm' {x : ValueId} {s : Nat × Nat} (h : (x, s) ∈ defSites (moveF g hb t)) :
    (wfData (moveF g hb t) (coreInfo (moveF g hb t))).dm x = some s :=
  (defMap_get_iff hm.unique' x s).2 h

theorem MoveOk.idom' : (wfData (moveF g hb t) (coreInfo (moveF g hb t))).idom =
    (wfData g (coreInfo g)).idom := by
  simp [wfData, coreInfo, moveF_build]

theorem MoveOk.rank' : (wfData (moveF g hb t) (coreInfo (moveF g hb t))).rank =
    (wfData g (coreInfo g)).rank := by
  simp [wfData, coreInfo, moveF_build]

theorem MoveOk.index' : (wfData (moveF g hb t) (coreInfo (moveF g hb t))).index =
    (wfData g (coreInfo g)).index := by
  simp [wfData, coreInfo, moveF_build]

/-- **Availability moves to the output position.** -/
theorem MoveOk.avail {i : Nat} {b' : Block} (hb' : g.blocks[i]? = some b') {k : Nat} {x : ValueId}
    (hA : Avail (wfData g (coreInfo g)) i k x) :
    Avail (wfData (moveF g hb t) (coreInfo (moveF g hb t))) i (fidx (· != t) b'.body k) x := by
  have hrank := hm.wf.rank
  obtain ⟨d, s, hd, h⟩ := hA
  have hs := hm.wf.sitesRev x (d, s) hd
  by_cases hxv : x = v
  · subst hxv
    have hsv : (x, (bi, jt + 1)) ∈ defSites g :=
      Opt.mem_defSites.2 ⟨bi, b, hm.hb_b, .inr ⟨jt, t, hm.ht, by simp [hm.hres], rfl⟩⟩
    have := site_unique hm.unique hs hsv
    simp only [Prod.mk.injEq] at this
    obtain ⟨rfl, rfl⟩ := this
    obtain ⟨bh, hbh⟩ : ∃ bh, g.blocks[hb]? = some bh := ⟨_, List.getElem?_eq_getElem hm.hbl⟩
    refine ⟨hb, bh.body.length + 1, hm.dm' (hm.mem_defSites.2 ⟨hb, bh, hbh, .inr (.inr ⟨rfl, by simp [hm.hres], rfl⟩)⟩), .inr ?_⟩
    have hdi : Anc (wfData g (coreInfo g)).idom d i := by
      rcases h with ⟨rfl, -⟩ | ⟨-, ha⟩
      · exact .refl _
      · exact ha
    have hhi : Anc (wfData g (coreInfo g)).idom hb i := hm.hanc.trans hdi
    refine ⟨fun he => ?_, by rw [hm.idom']; exact hhi⟩
    subst he
    exact hm.hne (Anc.antisymm hrank hm.hanc hdi)
  · obtain ⟨i0, b0, hb0, ⟨p, hp, hpx, he⟩ | ⟨j0, st, hj0, hx, he⟩⟩ := Opt.mem_defSites.1 hs
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      refine ⟨d, 0, hm.dm' (hm.mem_defSites.2 ⟨d, b0, hb0, .inl ⟨p, hp, hpx, rfl⟩⟩), ?_⟩
      rcases h with ⟨rfl, -⟩ | ⟨hne, ha⟩
      · exact .inl ⟨rfl, Nat.zero_le _⟩
      · exact .inr ⟨hne, by rw [hm.idom']; exact ha⟩
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have hst : st ≠ t := by
        rintro rfl; rw [hm.hres] at hx; simp at hx; exact hxv hx
      refine ⟨d, fidx (· != t) b0.body j0 + 1,
        hm.dm' (hm.mem_defSites.2 ⟨d, b0, hb0, .inr (.inl ⟨j0, st, hj0, hst, hx, rfl⟩)⟩), ?_⟩
      rcases h with ⟨rfl, hle⟩ | ⟨hne, ha⟩
      · left
        refine ⟨rfl, ?_⟩
        rw [hb'] at hb0; cases hb0
        exact fidx_lt _ b'.body (by omega) hj0 (by simpa using hst)
      · exact .inr ⟨hne, by rw [hm.idom']; exact ha⟩

theorem fidx_le {α : Type} (p : α → Bool) (l : List α) (k : Nat) : fidx p l k ≤ k := by
  unfold fidx
  exact Nat.le_trans (List.length_filter_le _ _) (List.length_take_le _ _)

/-- **A move keeps the certificate facts** when `t`'s operands are available at the end of
`hb`. -/
theorem MoveOk.wf' {bh : Block} (hbh : g.blocks[hb]? = some bh)
    (hops : ∀ x ∈ operands t.inst, Avail (wfData g (coreInfo g)) hb bh.body.length x) :
    Wf (moveF g hb t) (wfData (moveF g hb t) (coreInfo (moveF g hb t))) := by
  have hW := hm.wf
  have hn' := hm.nodup'
  have hgetm : ∀ i b', (moveF g hb t).blocks[i]? = some b' →
      ∃ b0, g.blocks[i]? = some b0 ∧ b' = moveB hb t (b0, i) := by
    intro i b' h
    rw [moveF_get, Option.map_eq_some_iff] at h
    obtain ⟨b0, hb0, rfl⟩ := h
    exact ⟨b0, hb0, rfl⟩
  have hlenh : (bh.body.filter (· != t)).length = bh.body.length := by
    rw [hm.filter_id hbh hm.hne]
  refine { ids := ?_, sites := ?_, sitesRev := ?_, root := ?_, rank := ?_, params := ?_,
           uses := ?_, results := ?_, pure := ?_, termUses := ?_, edges := ?_ }
  · intro i b' hb'
    obtain ⟨b0, hb0, rfl⟩ := hgetm i b' hb'
    rw [hm.index']; exact hW.ids i b0 hb0
  · exact fun x s hs => (defMap_get_iff hm.unique' x s).2 hs
  · exact fun x s hs => (defMap_get_iff hm.unique' x s).1 hs
  · rw [hm.idom']; exact hW.root
  · rw [hm.idom', hm.rank']; exact hW.rank
  · exact fun i b' hb' p hp => tm_param hn' hb' hp
  · intro i b' hb' j' st hst x hx
    obtain ⟨b0, hb0, rfl⟩ := hgetm i b' hb'
    simp only [moveB] at hst
    rcases Nat.lt_or_ge j' (b0.body.filter (· != t)).length with hj | hj
    · rw [List.getElem?_append_left hj] at hst
      obtain ⟨j, hj', -, rfl⟩ := exists_fidx _ b0.body j' st hst
      exact hm.avail hb0 (hW.uses i b0 hb0 j st hj' x hx)
    · rw [List.getElem?_append_right hj] at hst
      split at hst
      · rename_i hih
        subst hih
        rw [hbh] at hb0; cases hb0
        have hj0 : j' - (bh.body.filter (· != t)).length = 0 := by
          rcases Nat.eq_zero_or_pos (j' - (bh.body.filter (· != t)).length) with h | h
          · exact h
          · have : [t][j' - (bh.body.filter (· != t)).length]? = none :=
              List.getElem?_eq_none (by simp only [List.length_singleton]; omega)
            rw [this] at hst; cases hst
        rw [hj0] at hst
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hst
        subst hst
        have := hm.avail hbh (hops x hx)
        rw [show fidx (· != t) bh.body bh.body.length = (bh.body.filter (· != t)).length from
          fidx_length _ _] at this
        exact this.mono (by omega)
      · simp at hst
  · intro i b' hb' j' st hst
    have hb'' := hb'
    obtain ⟨b0, hb0, rfl⟩ := hgetm i b' hb'
    have hsm : st ∈ (moveB hb t (b0, i)).body := List.mem_of_getElem? hst
    have hsig : sigOf (moveF g hb t) = sigOf g := rfl
    obtain ⟨ts, hts, hlen⟩ : ∃ ts, st.inst.resultTypes (sigOf g) (fun _ => none) = some ts ∧
        ts.length = st.results.length := by
      rcases hm.mem_body hb0 hsm with h | rfl
      · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 h
        obtain ⟨ts, hts, hlen, -⟩ := hW.results i b0 hb0 j st hj
        exact ⟨ts, hts, hlen⟩
      · obtain ⟨ts, hts, hlen, -⟩ := hW.results bi b hm.hb_b jt _ hm.ht
        exact ⟨ts, hts, hlen⟩
    refine ⟨ts, by rw [hsig]; exact hts, hlen, fun n r hr => ?_⟩
    exact tm_result hn' hb'' hsm (by rw [hsig]; exact hts) hlen hr
  · intro i b' hb' j' st hst hp
    obtain ⟨b0, hb0, rfl⟩ := hgetm i b' hb'
    have hsm : st ∈ (moveB hb t (b0, i)).body := List.mem_of_getElem? hst
    have hpt : pureTyped (wfData g (coreInfo g)).tm g st.inst = true := by
      rcases hm.mem_body hb0 hsm with h | rfl
      · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 h
        exact hW.pure i b0 hb0 j st hj hp
      · exact hW.pure bi b hm.hb_b jt _ hm.ht hp
    rw [← hpt]
    exact pureTyped_congr (fun x _ => hm.tm x) rfl rfl
  · intro i b' hb' x hx
    obtain ⟨b0, hb0, rfl⟩ := hgetm i b' hb'
    have := hm.avail hb0 (hW.termUses i b0 hb0 x hx)
    rw [fidx_length] at this
    exact this.mono (by simp [moveB])
  · intro i b' hb' id hid
    obtain ⟨b0, hb0, rfl⟩ := hgetm i b' hb'
    obtain ⟨j, b1, hj, hb1, hid1, hanc⟩ := hW.edges i b0 hb0 id hid
    refine ⟨j, moveB hb t (b1, j), by rw [hm.index']; exact hj, by rw [moveF_get, hb1]; rfl, hid1, ?_⟩
    rw [hm.idom']; exact hanc

end Move

end Opt
