import FV.Opt.Proof.CompleteGvn
import FV.Opt.Licm
import Lean

/-!
# Completeness of the LICM stage (M1)

On a well-formed function (`check g = .ok info`), the output of `Opt.licm` passes `check` and the
edit validator `editOk id` (`licm_complete`), so `Opt.optimizeReport` never stops at the LICM
stage.

CFG facts: the depth-first search is sound (`Opt.postorder_reach`: every block of the postorder is
reachable along `succs`), `preds` is the converse of `succs` (`Opt.build_preds_mem`),
`Cfg.dominates` is sound (`Opt.dominates_sound`), and every loop of `Cfg.loops` has the facts LICM
needs (`Opt.loops_ok`, `Opt.LoopOk`: the header is in the body, every body block is a tree
descendant of the header, the body is closed under predecessors of its non-header blocks; the
search's fuel suffices). Hence a block between the header and a loop block in the dominator tree
is in the loop (`Opt.loop_between`), which is why an operand defined outside the loop is available
at the end of the header's immediate dominator. `Array.qsort` only permutes (`Opt.mem_qsort`).
-/

namespace Opt

open Lean Elab Term Meta in
/-- A declaration private to `Init.Data.Array.QSort.Basic` (the internals of `Array.qsort`). -/
elab "qsortPriv% " id:ident : term => do
  let n := ((`_private.Init.Data.Array.QSort.Basic).num 0) ++ id.getId
  let some ci := (← getEnv).find? n | throwError "not found {n}"
  let us ← ci.levelParams.mapM fun _ => mkFreshLevelMVar
  return mkConst n us

theorem swap_all {α : Type} {n : Nat} (P : α → Prop) (v : Vector α n) (i j : Nat) (hi : i < n) (hj : j < n)
    (h : ∀ k (hk : k < n), P v[k]) : ∀ k (hk : k < n), P (v.swap i j hi hj)[k] := by
  intro k hk
  rw [Vector.getElem_swap]
  split
  · exact h j hj
  · split
    · exact h i hi
    · exact h k hk

theorem qpartition_loop_all {α : Type} {n : Nat} (P : α → Prop) (lt : α → α → Bool) (lo hi : Nat)
    (hhi : hi < n) (pivot : α) : ∀ (m : Nat) (as : Vector α n) (i k : Nat) (ilo : lo ≤ i) (ik : i ≤ k)
      (w : k ≤ hi), hi - k = m → (∀ k (hk : k < n), P as[k]) →
      ∀ k' (hk' : k' < n), P ((qsortPriv% Array.qpartition.loop) lt lo hi hhi pivot as i k ilo ik w).2[k'] := by
  intro m
  induction m with
  | zero =>
    intro as i k ilo ik w hm h
    rw [qsortPriv% Array.qpartition.loop.eq_def]
    simp only [show ¬ k < hi by omega, dite_false]
    exact swap_all P as i hi _ hhi h
  | succ m ih =>
    intro as i k ilo ik w hm h
    rw [qsortPriv% Array.qpartition.loop.eq_def]
    have hkh : k < hi := by omega
    simp only [hkh, dite_true]
    split
    · exact ih _ (i + 1) (k + 1) (by omega) (by omega) (by omega) (by omega) (swap_all P as i k _ _ h)
    · exact ih as i (k + 1) ilo (by omega) (by omega) (by omega) h

theorem qpartition_all {α : Type} {n : Nat} (P : α → Prop) (as : Vector α n) (lt : α → α → Bool)
    (lo hi : Nat) (w : lo ≤ hi) (hlo : lo < n) (hhi : hi < n) (h : ∀ k (hk : k < n), P as[k]) :
    ∀ k (hk : k < n), P (Array.qpartition as lt lo hi w hlo hhi).2[k] := by
  unfold Array.qpartition
  simp only
  refine qpartition_loop_all P lt lo hi hhi _ _ _ _ _ _ _ _ rfl ?_
  have h1 : ∀ (v : Vector α n) (c : Bool) (i j : Nat) (hi : i < n) (hj : j < n),
      (∀ k (hk : k < n), P v[k]) → ∀ k (hk : k < n), P (if c = true then v.swap i j hi hj else v)[k] := by
    intro v c i j hi hj hv
    split
    · exact swap_all P v i j hi hj hv
    · exact hv
  exact h1 _ _ _ _ _ _ (h1 _ _ _ _ _ _ (h1 _ _ _ _ _ _ h))

theorem qsort_sort_all {α : Type} (P : α → Prop) (lt : α → α → Bool) {n : Nat} :
    ∀ (B : Nat) (as : Vector α n) (lo hi : Nat) (w : lo ≤ hi) (hlo : lo < n) (hhi : hi < n),
      hi - lo < B → (∀ k (hk : k < n), P as[k]) →
      ∀ k (hk : k < n), P ((qsortPriv% Array.qsort.sort) lt as lo hi w hlo hhi)[k] := by
  intro B
  induction B with
  | zero => intro _ _ _ _ _ _ hB; omega
  | succ B ih =>
    intro as lo hi w hlo hhi hB h
    rw [qsortPriv% Array.qsort.sort.eq_def]
    split
    · rename_i h₁
      have hq := qpartition_all P as lt lo hi w hlo hhi h
      generalize Array.qpartition as lt lo hi w hlo hhi = q at hq
      obtain ⟨⟨mid, hmid⟩, as'⟩ := q
      simp only at hq ⊢
      split
      · exact hq
      · rename_i h₂
        exact ih _ _ _ _ _ _ (by omega) (ih _ _ _ _ _ _ (by omega) hq)
    · exact h

/-- Every element of `Array.qsort as lt` is an element of `as`. -/
theorem mem_qsort {α : Type} (as : Array α) (lt : α → α → Bool) :
    ∀ x ∈ (as.qsort lt).toList, x ∈ as.toList := by
  unfold Array.qsort
  split
  · exact fun x hx => hx
  · rename_i h0
    intro x hx
    simp only at hx
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
    simp only [Array.length_toList, Vector.size_toArray] at hk
    have := qsort_sort_all (fun y => y ∈ as.toList) lt _ as.toVector (min 0 (as.size - 1))
      (max (min 0 (as.size - 1)) (min (as.size - 1) (as.size - 1))) (by omega) (by omega) (by omega)
      (Nat.lt_succ_self _) (fun k hk => by simp) k hk
    simpa using this

end Opt

namespace Opt

open Clif

/-- Reachability from the entry block along `succs`. -/
inductive Reach (succs : Array (List Nat)) : Nat → Prop
  | entry : Reach succs 0
  | step {a x : Nat} : Reach succs a → x ∈ succs[a]! → Reach succs x

/-- **The depth-first search is sound**: every block of the postorder is reachable. -/
theorem postorder_reach (succs : Array (List Nat)) :
    ∀ x ∈ (Cfg.postorder succs).toList, Reach succs x := by
  unfold Cfg.postorder
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range']
  split
  · intro x hx; exact absurd hx (by simp [pure])
  · rename_i hn
    rw [bind_pure_comp]
    simp only [Functor.map]
    refine forIn_inv' _ _ _
      (P := fun s : DfsSt => (∀ x ∈ dfsBlocks s, Reach succs x) ∧
        ∀ fr ∈ s.2.1.toList, ∀ y ∈ fr.2, y ∈ succs[fr.1]!)
      (Q := fun s : DfsSt => ∀ x ∈ s.2.2.toList, Reach succs x) ?_ ?_ ?_
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
        have hbr : Reach succs b := hreach b (.inr (.inr rfl))
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
          have hrx : Reach succs x := .step hbr (hbs x (List.mem_cons_self ..))
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

theorem build_reach_lt {z : Nat} (h : Reach (Cfg.build f).succs z) : z < f.blocks.length := by
  cases h with
  | entry => have := hc.core.1; rwa [build_size_eq hc] at this
  | step _ hx => exact (build_edge hc hx).2.1

theorem build_reach_reachable {z : Nat} (h : Reach (Cfg.build f).succs z) :
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
    Reach (Cfg.build f).succs z := by
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
  suffices ∀ z, Reach (Cfg.build f).succs z →
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
