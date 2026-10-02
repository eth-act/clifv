import FV.Backend.Proof.PrepareCheck

/-!
# Completeness of the `prepare` validator (M7)

`prepCheck_complete`: on VCode in `PrepDomain` (at least one block, distinct labels, branch
arguments only on blocks with at most one successor), `prepCheck` accepts every output of
`prepare`. With `PrepareSound.prep_sound` this makes `prepare` correct outright
(`PrepareDirect.prepare_correct`), the check being a runtime double-check.

The proof follows `prepare` step by step:

* `reachable` (the worklist) marks exactly a set of blocks containing the entry, closed under
  successors, every one reachable from the entry (`reachable_spec`);
* the kept blocks (`filterMap` of the live ones) keep their labels, and the entry first;
* critical-edge splitting rewrites a kept block's terminator to targets that are either the old
  label or a fresh edge-block label (`> ` every kept label) whose block jumps to the old label
  (`splitInv`);
* `rpo` (a depth-first search) lists every block reachable from the entry once, the entry first,
  and is closed under successors (`rpo_spec`);

so every live block of `vc` has a counterpart in `vcp` (by label) that `keptOk` accepts.
-/

namespace Backend.Proof.Prep

open Backend Backend.Proof.Driver

/-! ## Arrays of booleans -/

/-- `a[i]!` of a boolean array. -/
theorem getElem!_bool (a : Array Bool) (i : Nat) : a[i]! = a[i]?.getD false := by
  simp only [getElem!_def]
  split <;> simp_all

theorem getD_set (a : Array Bool) (x i : Nat) :
    (a.set! x true)[i]?.getD false = (decide (x = i ∧ x < a.size) || a[i]?.getD false) := by
  simp only [Array.set!, Array.getElem?_setIfInBounds]
  by_cases h : x = i
  · subst h
    by_cases hx : x < a.size
    · simp [hx]
    · simp [hx]
  · simp [h]

theorem size_set (a : Array Bool) (x : Nat) : (a.set! x true).size = a.size := by
  simp [Array.set!]

/-- The weight of the unmarked indices below `n`. -/
def wsum (a : Array Bool) (w : Nat → Nat) (n : Nat) : Nat :=
  ((List.range n).map fun b => if a[b]?.getD false then 0 else w b).sum

theorem wsum_set (a : Array Bool) (w : Nat → Nat) (x : Nat) (hx : x < a.size)
    (hf : a[x]?.getD false = false) : ∀ n, x < n → wsum (a.set! x true) w n + w x = wsum a w n
  | 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, h => by
    simp only [wsum, List.range_succ, List.map_append, List.sum_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, getD_set] at *
    by_cases hn : x = n
    · subst hn
      have e : ∀ b ∈ List.range x, (decide (x = b ∧ x < a.size) || a[b]?.getD false) =
          a[b]?.getD false := by
        intro b hb
        have : x ≠ b := by simp at hb; omega
        simp [this]
      rw [List.map_congr_left (fun b hb => by rw [e b hb])]
      have hf' : a[x] = false := by simpa [Array.getElem?_eq_getElem hx] using hf
      simp [hx, hf']
    · have h' : x < n := by omega
      have := wsum_set a w x hx hf n h'
      simp only [wsum, getD_set] at this
      simp only [hn, false_and, decide_false, Bool.false_or]
      omega

theorem wsum_le (a : Array Bool) (w : Nat → Nat) :
    ∀ n, wsum a w n ≤ ((List.range n).map w).sum
  | 0 => by simp [wsum]
  | n + 1 => by
    have := wsum_le a w n
    simp only [wsum, List.range_succ, List.map_append, List.sum_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil] at *
    split <;> omega

/-! ## Reachability -/

/-- Block `b` is reachable from the entry along `succs`. -/
inductive Reach (succs : Array (Array Nat)) : Nat → Prop
  | entry : Reach succs 0
  | step {b s : Nat} : Reach succs b → s ∈ (succs[b]! : Array Nat).toList → Reach succs s

/-- Successor indices are blocks. -/
def SuccsIn (succs : Array (Array Nat)) : Prop := ∀ b s : Nat, s ∈ (succs[b]! : Array Nat).toList → s < succs.size

/-! ## A worklist loop, unrolled -/

/-- `n` iterations of a worklist loop that stops on an empty worklist. -/
def iterW {σ ι : Type} (work : σ → List ι) (F : σ → ι → List ι → σ) : Nat → σ → σ
  | 0, st => st
  | m + 1, st => match work st with
    | [] => st
    | b :: rest => iterW work F m (F st b rest)

theorem forIn_iterW {σ ι : Type} (work : σ → List ι) (F : σ → ι → List ι → σ)
    (body : Nat → σ → Id (ForInStep σ))
    (hb : ∀ x st, body x st = match work st with
      | [] => pure (.done st)
      | b :: rest => pure (.yield (F st b rest))) :
    ∀ m a st, forIn (List.range' a m) st body = pure (iterW work F m st)
  | 0, a, st => by simp [iterW]
  | m + 1, a, st => by
    rw [List.range'_succ, List.forIn_cons, hb]
    simp only [iterW]
    split <;> simp [forIn_iterW work F body hb m]

theorem forIn_yield_foldl {m : Type → Type} [Monad m] [LawfulMonad m] {α β : Type}
    (l : List α) (init : β) (g : β → α → β) (f : α → β → m (ForInStep β))
    (hf : ∀ a b, f a b = pure (.yield (g b a))) : forIn l init f = pure (l.foldl g init) := by
  have : f = fun a b => pure (.yield (g b a)) := funext fun a => funext fun b => hf a b
  subst this
  exact List.forIn_pure_yield_eq_foldl ..

/-! ## `reachable` -/

/-- Mark `s`, queueing it if new (`reachable`'s inner loop). -/
def rIn (st : Array Bool × List Nat) (s : Nat) : Array Bool × List Nat :=
  if (!st.1[s]!) = true then (st.1.set! s true, s :: st.2) else st

/-- Pop `b`, mark and queue its successors (`reachable`'s outer loop). -/
def rStep (succs : Array (Array Nat)) (st : Array Bool × List Nat) (b : Nat) (rest : List Nat) :
    Array Bool × List Nat :=
  (succs[b]! : Array Nat).toList.foldl rIn (st.1, rest)

theorem reachable_eq (succs : Array (Array Nat)) (h : succs.size ≠ 0) :
    reachable succs = (iterW Prod.snd (rStep succs) (succs.size + 1)
      ((Array.replicate succs.size false).set! 0 true, [0])).1 := by
  unfold reachable
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Id.run, h, beq_iff_eq, ite_false]
  rw [forIn_iterW Prod.snd (rStep succs)]
  · simp [Std.Legacy.Range.size]; rfl
  · intro x st
    rcases st with ⟨seen, work⟩
    cases work with
    | nil => rfl
    | cons b rest =>
      simp only []
      rw [forIn_yield_foldl _ _ rIn]
      · rfl
      · intro a st
        simp only [rIn]
        split <;> rfl

/-- Marked: `a[x]` is `true`. -/
abbrev mk (a : Array Bool) (x : Nat) : Prop := a[x]?.getD false = true

theorem mk_set {a : Array Bool} {x i : Nat} : mk (a.set! x true) i ↔ (x = i ∧ x < a.size) ∨ mk a i := by
  simp only [mk]; rw [getD_set]; simp

theorem mk_lt {a : Array Bool} {x : Nat} (h : mk a x) : x < a.size := by
  rcases Nat.lt_or_ge x a.size with h' | h'
  · exact h'
  · simp [mk, Array.getElem?_eq_none h'] at h

theorem not_mk_replicate (n b : Nat) : ¬ mk (Array.replicate n false) b := by
  simp only [mk, Array.getElem?_replicate]
  split <;> simp

theorem sum_ones : ∀ n, ((List.range n).map fun _ => 1).sum = n
  | 0 => rfl
  | n + 1 => by simp [List.range_succ, sum_ones n]

theorem rFold (n : Nat) : ∀ (l : List Nat), (∀ s ∈ l, s < n) → ∀ (seen : Array Bool) (work : List Nat),
    seen.size = n →
    (l.foldl rIn (seen, work)).1.size = n ∧
    (∀ x, mk seen x → mk (l.foldl rIn (seen, work)).1 x) ∧
    (∀ s ∈ l, mk (l.foldl rIn (seen, work)).1 s) ∧
    ∃ new, (l.foldl rIn (seen, work)).2 = new ++ work ∧
      (∀ x ∈ new, x ∈ l ∧ mk (l.foldl rIn (seen, work)).1 x) ∧
      (∀ x, mk (l.foldl rIn (seen, work)).1 x → ¬ mk seen x → x ∈ new) ∧
      new.length + wsum (l.foldl rIn (seen, work)).1 (fun _ => 1) n = wsum seen (fun _ => 1) n
  | [], _, seen, work, hs => by
    refine ⟨hs, fun x h => h, by simp, [], by simp, by simp, fun x h1 h2 => absurd h1 h2, by simp⟩
  | s :: l, hl, seen, work, hs => by
    have hsn : s < n := hl s (by simp)
    have hl' : ∀ s ∈ l, s < n := fun s h => hl s (by simp [h])
    simp only [List.foldl_cons]
    by_cases hm : mk seen s
    · have e : rIn (seen, work) s = (seen, work) := by
        simp only [rIn, mk] at *; simp [getElem!_bool, hm]
      rw [e]
      obtain ⟨h1, h2, h3, new, h4, h5, h6, h7⟩ := rFold n l hl' seen work hs
      refine ⟨h1, h2, ?_, new, h4, fun x hx => ⟨by simp [(h5 x hx).1], (h5 x hx).2⟩, h6, h7⟩
      intro t ht
      simp only [List.mem_cons] at ht
      rcases ht with rfl | ht
      · exact h2 _ hm
      · exact h3 t ht
    · have e : rIn (seen, work) s = (seen.set! s true, s :: work) := by
        simp only [rIn, mk] at *; simp [getElem!_bool, hm]
      rw [e]
      have hs' : (seen.set! s true).size = n := by rw [size_set]; exact hs
      obtain ⟨h1, h2, h3, new, h4, h5, h6, h7⟩ := rFold n l hl' (seen.set! s true) (s :: work) hs'
      have hw := wsum_set seen (fun _ => 1) s (by omega) (by simpa [mk] using hm) n hsn
      refine ⟨h1, fun x hx => h2 x (mk_set.mpr (.inr hx)), ?_, new ++ [s], by rw [h4]; simp,
        ?_, ?_, ?_⟩
      · intro t ht
        simp only [List.mem_cons] at ht
        rcases ht with rfl | ht
        · exact h2 _ (mk_set.mpr (.inl ⟨rfl, by omega⟩))
        · exact h3 t ht
      · intro x hx
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact ⟨by simp [(h5 x hx).1], (h5 x hx).2⟩
        · exact ⟨by simp, h2 _ (mk_set.mpr (.inl ⟨rfl, by omega⟩))⟩
      · intro x hx hnx
        by_cases hxs : x = s
        · simp [hxs]
        · have : ¬ mk (seen.set! s true) x := by
            rw [mk_set]; rintro (⟨e, -⟩ | h); exact hxs e.symm; exact hnx h
          simp [h6 x hx this]
      · simp only [List.length_append, List.length_singleton]
        omega

/-- The invariant of `reachable`'s loop. -/
structure RInv (succs : Array (Array Nat)) (st : Array Bool × List Nat) : Prop where
  size : st.1.size = succs.size
  work : ∀ b ∈ st.2, mk st.1 b
  closed : ∀ b, mk st.1 b → b ∉ st.2 → ∀ s ∈ (succs[b]! : Array Nat).toList, mk st.1 s
  reach : ∀ b, mk st.1 b → Reach succs b
  entry : mk st.1 0

theorem rStep_inv {succs : Array (Array Nat)} (hin : SuccsIn succs) {st : Array Bool × List Nat}
    (hi : RInv succs st) {b : Nat} {rest : List Nat} (hw : st.2 = b :: rest) :
    RInv succs (rStep succs st b rest) ∧
      (rStep succs st b rest).2.length + wsum (rStep succs st b rest).1 (fun _ => 1) succs.size + 1 =
        st.2.length + wsum st.1 (fun _ => 1) succs.size := by
  obtain ⟨h1, h2, h3, new, h4, h5, h6, h7⟩ :=
    rFold succs.size (succs[b]! : Array Nat).toList (fun s h => hin b s h) st.1 rest hi.size
  have hb : mk st.1 b := hi.work b (by simp [hw])
  simp only [rStep]
  refine ⟨⟨h1, ?_, ?_, ?_, h2 _ hi.entry⟩, ?_⟩
  · intro x hx
    rw [h4, List.mem_append] at hx
    rcases hx with hx | hx
    · exact (h5 x hx).2
    · exact h2 _ (hi.work x (by simp [hw, hx]))
  · intro x hx hnx s hs
    rw [h4, List.mem_append, not_or] at hnx
    by_cases hmx : mk st.1 x
    · by_cases hxb : x = b
      · subst hxb; exact h3 s hs
      · exact h2 _ (hi.closed x hmx (by simp [hw, hxb, hnx.2]) s hs)
    · exact absurd (h6 x hx hmx) hnx.1
  · intro x hx
    by_cases hmx : mk st.1 x
    · exact hi.reach x hmx
    · exact .step (hi.reach b hb) (h5 x (h6 x hx hmx)).1
  · rw [h4, hw]
    simp only [List.length_append, List.length_cons]
    omega

theorem iterR_inv {succs : Array (Array Nat)} (hin : SuccsIn succs) :
    ∀ m (st : Array Bool × List Nat), RInv succs st →
      st.2.length + wsum st.1 (fun _ => 1) succs.size ≤ m →
      RInv succs (iterW Prod.snd (rStep succs) m st) ∧ (iterW Prod.snd (rStep succs) m st).2 = []
  | 0, st, hi, hm => by
    simp only [iterW]
    exact ⟨hi, List.eq_nil_of_length_eq_zero (by omega)⟩
  | m + 1, st, hi, hm => by
    simp only [iterW]
    split
    · rename_i h; exact ⟨hi, h⟩
    · rename_i b rest h
      obtain ⟨hi', hm'⟩ := rStep_inv hin hi h
      exact iterR_inv hin m _ hi' (by omega)

/-- **`reachable`**: the marked blocks contain the entry, are closed under successors and are
reachable from the entry. -/
theorem reachable_spec {succs : Array (Array Nat)} (hin : SuccsIn succs) (h0 : succs.size ≠ 0) :
    (reachable succs).size = succs.size ∧ mk (reachable succs) 0 ∧
      (∀ b, mk (reachable succs) b → ∀ s ∈ (succs[b]! : Array Nat).toList, mk (reachable succs) s) ∧
      (∀ b, mk (reachable succs) b → Reach succs b) := by
  have hi0 : RInv succs ((Array.replicate succs.size false).set! 0 true, [0]) := by
    refine ⟨by simp, ?_, ?_, ?_, ?_⟩
    · intro b hb
      simp only [List.mem_singleton] at hb
      subst hb
      exact mk_set.mpr (.inl ⟨rfl, by simp; omega⟩)
    · intro b hb hnb
      rcases mk_set.mp hb with ⟨rfl, -⟩ | hb
      · simp at hnb
      · exact absurd hb (not_mk_replicate _ _)
    · intro b hb
      rcases mk_set.mp hb with ⟨rfl, -⟩ | hb
      · exact .entry
      · exact absurd hb (not_mk_replicate _ _)
    · exact mk_set.mpr (.inl ⟨rfl, by simp; omega⟩)
  have hw := wsum_set (Array.replicate succs.size false) (fun _ => 1) 0 (by simp; omega)
    (Bool.eq_false_iff.mpr (not_mk_replicate _ _)) succs.size (by omega)
  have hle := wsum_le (Array.replicate succs.size false) (fun _ => 1) succs.size
  rw [sum_ones] at hle
  obtain ⟨hi, -⟩ := iterR_inv hin (succs.size + 1) _ hi0 (by simp only [List.length_singleton]; omega)
  rw [reachable_eq succs h0]
  refine ⟨hi.size, hi.entry, fun b hb s hs => hi.closed b hb ?_ s hs, hi.reach⟩
  obtain ⟨-, he⟩ := iterR_inv hin (succs.size + 1) _ hi0 (by simp only [List.length_singleton]; omega)
  rw [he]; simp

/-! ## `rpo` -/

/-- The state of `rpo`'s loop: marked blocks, postorder, stack of (block, next successor). -/
abbrev DState := Array Bool × Array Nat × List (Nat × Nat)

/-- One step of `rpo`'s depth-first search on the top frame `(b, i)`. -/
def dStep (succs : Array (Array Nat)) (st : DState) (p : Nat × Nat) (rest : List (Nat × Nat)) :
    DState :=
  match (succs[p.1]! : Array Nat)[p.2]? with
  | some s =>
    if (!st.1[s]!) = true then (st.1.set! s true, st.2.1, (s, 0) :: (p.1, p.2 + 1) :: rest)
    else (st.1, st.2.1, (p.1, p.2 + 1) :: rest)
  | none => (st.1, st.2.1.push p.1, rest)

/-- `rpo`'s fuel. -/
def dFuel (succs : Array (Array Nat)) : Nat := Array.foldl (fun n s => n + s.size + 1) 1 succs

theorem rpo_eq (succs : Array (Array Nat)) (h : succs.size ≠ 0) :
    rpo succs = (iterW (fun st : DState => st.2.2) (dStep succs) (dFuel succs)
      ((Array.replicate succs.size false).set! 0 true, #[], [(0, 0)])).2.1.reverse := by
  unfold rpo
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Id.run, h, beq_iff_eq, ite_false]
  rw [forIn_iterW (fun st : DState => st.2.2) (dStep succs)]
  · simp [Std.Legacy.Range.size, dFuel]; rfl
  · intro x st
    rcases st with ⟨seen, post, stack⟩
    cases stack with
    | nil => rfl
    | cons p rest =>
      rcases p with ⟨b, i⟩
      simp only [dStep]
      cases hs : (succs[b]! : Array Nat)[i]? with
      | none => simp only [hs]
      | some s => simp only [hs]; split <;> rfl

/-- The weight of a block: its successors and itself. -/
def wt (succs : Array (Array Nat)) (b : Nat) : Nat := (succs[b]! : Array Nat).size + 1

/-- The remaining work of the search. -/
def pot (succs : Array (Array Nat)) (st : DState) : Nat :=
  (st.2.2.map fun p => wt succs p.1 - p.2).sum + wsum st.1 (wt succs) succs.size

theorem getLast_cons_cons {α : Type} (a b : α) (l : List α) :
    (a :: b :: l).getLast? = (b :: l).getLast? := by
  simp [List.getLast?_cons]

theorem getLast_fst : ∀ (l : List (Nat × Nat)) (a a' : Nat × Nat), a.1 = a'.1 →
    (a :: l).getLast?.map Prod.fst = (a' :: l).getLast?.map Prod.fst
  | [], a, a', h => by simp [h]
  | c :: l, a, a', _ => by rw [getLast_cons_cons, getLast_cons_cons]

/-- The invariant of `rpo`'s loop. -/
structure DInv (succs : Array (Array Nat)) (st : DState) : Prop where
  size : st.1.size = succs.size
  stack : ∀ p ∈ st.2.2, mk st.1 p.1
  post : ∀ b ∈ st.2.1.toList, mk st.1 b ∧ ∀ s ∈ (succs[b]! : Array Nat).toList, mk st.1 s
  frame : ∀ p ∈ st.2.2, ∀ j < p.2, ∀ s, (succs[p.1]! : Array Nat)[j]? = some s → mk st.1 s
  cover : ∀ b, mk st.1 b → b ∈ st.2.1.toList ∨ b ∈ st.2.2.map Prod.fst
  nodup : (st.2.2.map Prod.fst ++ st.2.1.toList).Nodup
  bottom : st.2.2 ≠ [] → (st.2.2.getLast?).map Prod.fst = some 0
  done : st.2.2 = [] → st.2.1.toList.getLast? = some 0
  fr : ∀ p ∈ st.2.2, p.2 ≤ (succs[p.1]! : Array Nat).size

theorem dStep_inv {succs : Array (Array Nat)} (hin : SuccsIn succs) {st : DState}
    (hi : DInv succs st) {p : Nat × Nat} {rest : List (Nat × Nat)} (hw : st.2.2 = p :: rest) :
    DInv succs (dStep succs st p rest) ∧ pot succs (dStep succs st p rest) + 1 ≤ pot succs st := by
  rcases st with ⟨seen, post, stack⟩
  rcases p with ⟨b, i⟩
  simp only at hw
  subst hw
  have hb : mk seen b := hi.stack (b, i) (by simp)
  simp only [dStep]
  split
  · rename_i s hs
    have hsi : i < (succs[b]! : Array Nat).size := (Array.getElem?_eq_some_iff.mp hs).1
    have hsn : s < succs.size := hin b s (by
      obtain ⟨h1, h2⟩ := Array.getElem?_eq_some_iff.mp hs
      rw [Array.mem_toList_iff]; exact h2 ▸ Array.getElem_mem h1)
    split
    · rename_i hns
      have hns' : ¬ mk seen s := by simp only [mk]; simpa [getElem!_bool] using hns
      have mono : ∀ x, mk seen x → mk (seen.set! s true) x := fun x h => mk_set.mpr (.inr h)
      have hss : mk (seen.set! s true) s := mk_set.mpr (.inl ⟨rfl, by rw [hi.size]; exact hsn⟩)
      refine ⟨⟨by simp [hi.size], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · intro q hq
        simp only [List.mem_cons] at hq
        rcases hq with rfl | rfl | hq
        · exact hss
        · exact mono _ hb
        · exact mono _ (hi.stack q (by simp [hq]))
      · intro x hx
        obtain ⟨h1, h2⟩ := hi.post x hx
        exact ⟨mono _ h1, fun t ht => mono _ (h2 t ht)⟩
      · intro q hq j hj t ht
        simp only [List.mem_cons] at hq
        rcases hq with rfl | rfl | hq
        · simp at hj
        · simp only at hj ht
          by_cases hji : j = i
          · subst hji; rw [hs] at ht; cases ht; exact hss
          · exact mono _ (hi.frame (b, i) (by simp) j (by omega) t ht)
        · exact mono _ (hi.frame q (by simp [hq]) j hj t ht)
      · intro x hx
        rcases mk_set.mp hx with ⟨rfl, -⟩ | hx
        · right; simp
        · rcases hi.cover x hx with h | h
          · left; exact h
          · right; simp only [List.map_cons, List.mem_cons] at h ⊢; exact .inr h
      · have hsp : s ∉ post.toList := fun h => hns' (hi.post s h).1
        have hst : s ∉ ((b, i) :: rest).map Prod.fst := by
          intro h
          simp only [List.map_cons, List.mem_cons, List.mem_map] at h
          rcases h with rfl | ⟨q, hq, rfl⟩
          · exact hns' hb
          · exact hns' (hi.stack q (by simp [hq]))
        have := hi.nodup
        simp only [List.map_cons, List.cons_append, List.nodup_cons, List.mem_append,
          List.mem_cons, List.mem_map] at this hst ⊢
        refine ⟨?_, this⟩
        rintro (h | h | h)
        · exact hst (.inl h)
        · exact hst (.inr h)
        · exact hsp h
      · intro _
        rw [getLast_cons_cons, getLast_fst rest (b, i + 1) (b, i) rfl]
        exact hi.bottom (by simp)
      · intro h; simp at h
      · intro q hq
        simp only [List.mem_cons] at hq
        rcases hq with rfl | rfl | hq
        · simp
        · simp only; omega
        · exact hi.fr q (by simp [hq])
      · have hw := wsum_set seen (wt succs) s (by rw [hi.size]; exact hsn)
          (Bool.eq_false_iff.mpr hns') succs.size hsn
        have hwi : wt succs b - (i + 1) + 1 = wt succs b - i := by simp only [wt]; omega
        simp only [pot, List.map_cons, List.sum_cons, Nat.sub_zero]
        omega
    · rename_i hns
      have hms : mk seen s := by simp only [mk]; simpa [getElem!_bool] using hns
      refine ⟨⟨hi.size, ?_, hi.post, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · intro q hq
        simp only [List.mem_cons] at hq
        rcases hq with rfl | hq
        · exact hb
        · exact hi.stack q (by simp [hq])
      · intro q hq j hj t ht
        simp only [List.mem_cons] at hq
        rcases hq with rfl | hq
        · simp only at hj ht
          by_cases hji : j = i
          · subst hji; rw [hs] at ht; cases ht; exact hms
          · exact hi.frame (b, i) (by simp) j (by omega) t ht
        · exact hi.frame q (by simp [hq]) j hj t ht
      · intro x hx
        simpa using hi.cover x hx
      · simpa using hi.nodup
      · intro _
        rw [getLast_fst rest (b, i + 1) (b, i) rfl]
        exact hi.bottom (by simp)
      · intro h; simp at h
      · intro q hq
        simp only [List.mem_cons] at hq
        rcases hq with rfl | hq
        · simp only; omega
        · exact hi.fr q (by simp [hq])
      · have hwi : wt succs b - (i + 1) + 1 = wt succs b - i := by simp only [wt]; omega
        simp only [pot, List.map_cons, List.sum_cons]
        omega
  · rename_i hs
    have hsi : (succs[b]! : Array Nat).size ≤ i := by
      rcases Nat.lt_or_ge i (succs[b]! : Array Nat).size with h | h
      · rw [Array.getElem?_eq_getElem h] at hs; cases hs
      · exact h
    refine ⟨⟨hi.size, fun q hq => hi.stack q (by simp [hq]), ?_, fun q hq => hi.frame q (by simp [hq]),
      ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · intro x hx
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | hx
      · exact hi.post x hx
      · rw [hx]
        refine ⟨hb, fun t ht => ?_⟩
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ht
        simp only [Array.length_toList] at hj
        exact hi.frame (b, i) (by simp) j (by omega) _ (by simp [hj])
    · intro x hx
      rcases hi.cover x hx with h | h
      · left; simp [h]
      · simp only [List.map_cons, List.mem_cons] at h
        rcases h with rfl | h
        · left; simp
        · right; exact h
    · have := hi.nodup
      simp only [List.map_cons, List.cons_append, Array.toList_push] at this ⊢
      have hp : (rest.map Prod.fst ++ (post.toList ++ [b])).Perm
          (b :: (rest.map Prod.fst ++ post.toList)) := by
        simpa [List.append_assoc] using
          (List.perm_middle (a := b) (l₁ := rest.map Prod.fst ++ post.toList) (l₂ := []))
      exact hp.nodup_iff.mpr this
    · intro hne
      have := hi.bottom (by simp)
      rw [List.getLast?_cons] at this
      cases rest with
      | nil => exact absurd rfl hne
      | cons q r => simpa [List.getLast?_cons] using this
    · intro he
      simp only at he
      subst he
      have := hi.bottom (by simp)
      simp at this
      simp [this]
    · exact fun q hq => hi.fr q (by simp [hq])
    · have := hi.fr (b, i) (by simp)
      simp only at this
      simp only [pot, List.map_cons, List.sum_cons, wt]
      omega

theorem iterD_inv {succs : Array (Array Nat)} (hin : SuccsIn succs) :
    ∀ m (st : DState), DInv succs st → pot succs st ≤ m →
      DInv succs (iterW (fun st : DState => st.2.2) (dStep succs) m st) ∧
        (iterW (fun st : DState => st.2.2) (dStep succs) m st).2.2 = []
  | 0, st, hi, hm => by
    simp only [iterW]
    refine ⟨hi, ?_⟩
    cases h : st.2.2 with
    | nil => rfl
    | cons p rest =>
      have := hi.fr p (by simp [h])
      simp only [pot, h, List.map_cons, List.sum_cons, wt] at hm
      omega
  | m + 1, st, hi, hm => by
    simp only [iterW]
    split
    · rename_i h; exact ⟨hi, h⟩
    · rename_i p rest h
      obtain ⟨hi', hm'⟩ := dStep_inv hin hi h
      exact iterD_inv hin m _ hi' (by omega)

theorem getElem!_arr (a : Array (Array Nat)) (b : Nat) : a[b]! = a.toList[b]?.getD #[] := by
  simp only [getElem!_def, Array.getElem?_toList]
  split <;> simp_all <;> rfl

theorem foldl_size (k : Nat) : ∀ l : List (Array Nat),
    l.foldl (fun n s => n + s.size + 1) k = k + (l.map fun s => s.size + 1).sum
  | [] => by simp
  | s :: l => by
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [foldl_size]
    omega

theorem sum_range_getD : ∀ l : List (Array Nat),
    ((List.range l.length).map fun b => (l[b]?.getD #[]).size + 1).sum =
      (l.map fun s => s.size + 1).sum
  | [] => by simp
  | s :: l => by
    rw [List.length_cons, List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, List.sum_cons, List.getElem?_cons_zero, Option.getD_some]
    congr 1
    rw [← sum_range_getD l]
    congr 1

theorem pot_le_fuel (succs : Array (Array Nat)) :
    ((List.range succs.size).map (wt succs)).sum ≤ dFuel succs := by
  have e : (List.range succs.size).map (wt succs) =
      (List.range succs.toList.length).map fun b => (succs.toList[b]?.getD #[]).size + 1 := by
    simp only [Array.length_toList]
    exact List.map_congr_left fun b _ => by simp only [wt, getElem!_arr]
  rw [e, sum_range_getD, dFuel, ← Array.foldl_toList, foldl_size]
  omega

/-- **`rpo`**: the blocks reachable from the entry, each once, the entry first, closed under
successors. -/
theorem rpo_spec {succs : Array (Array Nat)} (hin : SuccsIn succs) (h0 : succs.size ≠ 0) :
    (∀ i ∈ (rpo succs).toList, i < succs.size) ∧ (rpo succs).toList.Nodup ∧
      (rpo succs)[0]? = some 0 ∧
      (∀ i ∈ (rpo succs).toList, ∀ s ∈ (succs[i]! : Array Nat).toList, s ∈ (rpo succs).toList) ∧
      (∀ b, Reach succs b → b ∈ (rpo succs).toList) := by
  have hn : 0 < succs.size := Nat.pos_of_ne_zero h0
  have hm0 : mk ((Array.replicate succs.size false).set! 0 true) 0 :=
    mk_set.mpr (.inl ⟨rfl, by simp; omega⟩)
  have hi0 : DInv succs ((Array.replicate succs.size false).set! 0 true, #[], [(0, 0)]) := by
    refine ⟨by simp, ?_, by simp, ?_, ?_, by simp, by simp, by simp, by simp⟩
    · intro q hq; simp only [List.mem_singleton] at hq; subst hq; exact hm0
    · intro q hq j hj; simp only [List.mem_singleton] at hq; subst hq; simp at hj
    · intro b hb
      rcases mk_set.mp hb with ⟨rfl, -⟩ | hb
      · right; simp
      · exact absurd hb (not_mk_replicate _ _)
  have hw := wsum_set (Array.replicate succs.size false) (wt succs) 0 (by simp; omega)
    (Bool.eq_false_iff.mpr (not_mk_replicate _ _)) succs.size hn
  have hle := wsum_le (Array.replicate succs.size false) (wt succs) succs.size
  have hf := pot_le_fuel succs
  obtain ⟨hi, he⟩ := iterD_inv hin (dFuel succs) _ hi0 (by
    simp only [pot, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.sub_zero]
    omega)
  rw [rpo_eq succs h0]
  generalize iterW (fun st : DState => st.2.2) (dStep succs) (dFuel succs)
    ((Array.replicate succs.size false).set! 0 true, #[], [(0, 0)]) = st at hi he
  rcases st with ⟨seen, post, stack⟩
  simp only at he
  subst he
  have hcl : ∀ i ∈ post.toList, ∀ s ∈ (succs[i]! : Array Nat).toList, s ∈ post.toList := by
    intro i hi' s hs
    rcases hi.cover s ((hi.post i hi').2 s hs) with h | h
    · exact h
    · simp at h
  have hlast := hi.done rfl
  simp only [Array.toList_reverse, List.mem_reverse]
  refine ⟨fun i h => ?_, ?_, ?_, fun i h s hs => hcl i h s hs, ?_⟩
  · have := mk_lt (hi.post i h).1
    rw [hi.size] at this; exact this
  · have := hi.nodup
    simp only [List.map_nil, List.nil_append] at this
    exact (List.reverse_perm _).nodup_iff.mpr this
  · rw [← Array.getElem?_toList, Array.toList_reverse, ← List.head?_eq_getElem?, List.head?_reverse]
    exact hlast
  · intro b hb
    induction hb with
    | entry => exact List.mem_of_getLast? hlast
    | step _ hs ih => exact hcl _ ih _ hs

/-! ## `mapM` and `forIn` in `Except` -/

theorem lmapM_ok {ε α β : Type} {f : α → Except ε β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = .ok l' → l'.length = l.length ∧
      ∀ (i : Nat) x, l[i]? = some x → ∃ y, f x = .ok y ∧ l'[i]? = some y
  | [], l', h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h; subst h; simp
  | a :: l, l', h => by
    rw [List.mapM_cons] at h
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    rename_i y hy
    split at h
    · cases h
    rename_i ys hys
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨hl, hi⟩ := lmapM_ok hys
    refine ⟨by simp [hl], fun i x hx => ?_⟩
    cases i with
    | zero => simp at hx; subst hx; exact ⟨y, hy, rfl⟩
    | succ i =>
      simp at hx
      obtain ⟨y', h1, h2⟩ := hi i x hx
      exact ⟨y', h1, by simpa using h2⟩

theorem lmapM_some {ε α β : Type} {f : α → Except ε β} :
    ∀ (l : List α), (∀ x ∈ l, ∃ y, f x = .ok y) → ∃ l', l.mapM f = .ok l'
  | [], _ => ⟨[], rfl⟩
  | a :: l, h => by
    obtain ⟨y, hy⟩ := h a (by simp)
    obtain ⟨ys, hys⟩ := lmapM_some l fun x hx => h x (by simp [hx])
    exact ⟨y :: ys, by simp [List.mapM_cons, hy, hys, bind, Except.bind, pure, Except.pure]⟩

theorem amapM_ok {ε α β : Type} {f : α → Except ε β} {as : Array α} {bs : Array β}
    (h : as.mapM f = .ok bs) : bs.size = as.size ∧
      ∀ (i : Nat) x, as[i]? = some x → ∃ y, f x = .ok y ∧ bs[i]? = some y := by
  rw [Array.mapM_eq_mapM_toList] at h
  cases hl : as.toList.mapM f with
  | error e => rw [hl] at h; cases h
  | ok l' =>
    rw [hl] at h
    simp only [Functor.map, Except.map, Except.ok.injEq] at h
    subst h
    obtain ⟨h1, h2⟩ := lmapM_ok hl
    refine ⟨by simpa using h1, fun i x hx => ?_⟩
    obtain ⟨y, hy, hy'⟩ := h2 i x (by simpa using hx)
    exact ⟨y, hy, by simpa using hy'⟩

theorem amapM_some {ε α β : Type} {f : α → Except ε β} (as : Array α)
    (h : ∀ x ∈ as.toList, ∃ y, f x = .ok y) : ∃ bs, as.mapM f = .ok bs := by
  obtain ⟨l', hl⟩ := lmapM_some as.toList h
  exact ⟨l'.toArray, by rw [Array.mapM_eq_mapM_toList, hl]; rfl⟩

theorem forIn_ok {ε α β : Type} (f : α → β → Except ε (ForInStep β))
    (hf : ∀ a b, ∃ b', f a b = .ok (.yield b')) : ∀ (l : List α) (b : β), ∃ r, forIn l b f = .ok r
  | [], b => ⟨b, rfl⟩
  | a :: l, b => by
    obtain ⟨b', hb⟩ := hf a b
    rw [List.forIn_cons, hb]
    exact forIn_ok f hf l b'

/-! ## The CFG -/

/-- The index of the block labelled `l` (`VCode.cfg`'s `idxOf`, `sigmaOf`). -/
def lab (V : Array VBlock) (l : Label) : Option Nat := V.findIdx? (·.label == l)

theorem lmapM_err {ε α β : Type} {f : α → Except ε β} :
    ∀ {l : List α} {e : ε}, l.mapM f = .error e → ∃ x ∈ l, ∃ e', f x = .error e'
  | [], e, h => by simp [List.mapM_nil, pure, Except.pure] at h
  | a :: l, e, h => by
    rw [List.mapM_cons] at h
    simp only [bind, Except.bind] at h
    split at h
    · rename_i e' he; exact ⟨a, by simp, e', he⟩
    split at h
    · rename_i e' he
      obtain ⟨x, hx, e'', hx'⟩ := lmapM_err he
      exact ⟨x, by simp [hx], e'', hx'⟩
    · cases h

theorem amapM_err {ε α β : Type} {f : α → Except ε β} {as : Array α} {e : ε}
    (h : as.mapM f = .error e) : ∃ x ∈ as.toList, ∃ e', f x = .error e' := by
  rw [Array.mapM_eq_mapM_toList] at h
  cases hl : as.toList.mapM f with
  | error e' => exact lmapM_err hl
  | ok l' => rw [hl] at h; cases h

theorem forIn_ne_error {ε α β : Type} (f : α → β → Except ε (ForInStep β))
    (hf : ∀ a b, ∃ b', f a b = .ok (.yield b')) (l : List α) (b : β) (e : ε) :
    forIn l b f ≠ .error e := by
  obtain ⟨r, hr⟩ := forIn_ok f hf l b
  rw [hr]; intro h; cases h

/-- `VCode.cfg`'s successors, block by block. -/
structure CfgSpec (V : Array VBlock) (ss : Array (Array Nat)) : Prop where
  size : ss.size = V.size
  blk : ∀ (i : Nat) (vb : VBlock), V[i]? = some vb → ∃ (t : MInst) (ts : Array Nat),
    vb.insts.back? = some t ∧ t.isTerminator = true ∧ ss[i]? = some ts ∧
    ts.size = t.targets.length ∧
    ∀ (j : Nat) (l : Label), t.targets[j]? = some l → ∃ k, ts[j]? = some k ∧ lab V l = some k

theorem cfg_spec {vc : VCode} {ss ps : Array (Array Nat)} (h : vc.cfg = .ok (ss, ps)) :
    CfgSpec vc.blocks ss := by
  unfold VCode.cfg at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  rename_i succs hsuccs
  have hss : ss = succs := by
    split at h
    · cases h
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      exact h.1.symm
  subst hss
  obtain ⟨hsz, hel⟩ := amapM_ok hsuccs
  refine ⟨hsz, fun i vb hvb => ?_⟩
  obtain ⟨ts, hts, hb⟩ := hel i vb hvb
  split at hts
  · rename_i t ht
    split at hts
    · simp [throw, throwThe, MonadExceptOf.throw] at hts
    · rename_i hterm
      refine ⟨t, ts, ht, by simpa using hterm, hb, ?_⟩
      obtain ⟨hsz', hel'⟩ := amapM_ok hts
      refine ⟨by simpa using hsz', fun j l hl => ?_⟩
      obtain ⟨y, hy, hy'⟩ := hel' j l (by simpa using hl)
      refine ⟨y, hy', ?_⟩
      split at hy
      · rename_i i hi
        simp only [pure, Except.pure, Except.ok.injEq] at hy
        subst hy; exact hi
      · simp [throw, throwThe, MonadExceptOf.throw] at hy
  · simp [throw, throwThe, MonadExceptOf.throw] at hts

theorem cfg_of {vc : VCode}
    (h : ∀ (i : Nat) (vb : VBlock), vc.blocks[i]? = some vb → ∃ t : MInst,
      vb.insts.back? = some t ∧ t.isTerminator = true ∧ ∀ l ∈ t.targets, ∃ k, lab vc.blocks l = some k) :
    ∃ ss ps, vc.cfg = .ok (ss, ps) := by
  unfold VCode.cfg
  simp only [bind, Except.bind]
  split
  · rename_i e he
    exfalso
    obtain ⟨vb, hvb, e', he'⟩ := amapM_err he
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hvb
    obtain ⟨t, h1, h2, h3⟩ := h i vc.blocks.toList[i] (by simp at hi; simp [hi])
    rw [h1] at he'
    simp only [h2, Bool.not_true, Bool.false_eq_true, ite_false] at he'
    obtain ⟨l, hl, e'', hl'⟩ := amapM_err he'
    obtain ⟨k, hk⟩ := h3 l (by simpa using hl)
    simp only [lab] at hk
    simp [hk, pure, Except.pure] at hl'
  · split
    · rename_i e he
      exfalso
      rw [← Array.forIn_toList] at he
      refine forIn_ne_error _ (fun a b => ?_) _ _ _ he
      rw [← Array.forIn_toList, forIn_yield_foldl _ _ _ _ (fun _ _ => rfl)]
      exact ⟨_, rfl⟩
    · exact ⟨_, _, rfl⟩

end Backend.Proof.Prep
