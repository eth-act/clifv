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

/-! ## Labels -/

/-- The blocks have distinct labels. -/
def Lbls (V : Array VBlock) : Prop := (V.toList.map VBlock.label).Nodup

theorem lbl_inj {V : Array VBlock} (hn : Lbls V) {j k : Nat} (hj : j < V.size) (hk : k < V.size)
    (h : V[j].label = V[k].label) : j = k :=
  hn.eq_of_getElem_eq (by simpa using hj) (by simpa using hk) (by simpa using h)

theorem lab_some {V : Array VBlock} {l : Label} {k : Nat} (h : lab V l = some k) :
    ∃ hk : k < V.size, V[k].label = l := by
  obtain ⟨hk, hp, -⟩ := Array.findIdx?_eq_some_iff_getElem.mp h
  exact ⟨hk, by simpa using hp⟩

theorem lab_of {V : Array VBlock} (hn : Lbls V) {l : Label} {k : Nat} (hk : k < V.size)
    (hl : V[k].label = l) : lab V l = some k :=
  Array.findIdx?_eq_some_iff_getElem.mpr ⟨hk, by simp [hl], fun j hj hp => by
    have := lbl_inj hn (Nat.lt_trans hj hk) hk (by simp at hp; rw [hp, hl])
    omega⟩

theorem lab_zero {V : Array VBlock} {l : Label} (hk : 0 < V.size) (hl : V[0].label = l) :
    lab V l = some 0 :=
  Array.findIdx?_eq_some_iff_getElem.mpr ⟨hk, by simp [hl], fun j hj => absurd hj (Nat.not_lt_zero _)⟩

/-! ## `setTargets` -/

theorem tryTargets {c : Label} : ∀ (hs : List TryHandler) (ls : List Label),
    ls.length = hs.length + 1 →
    ((hs.zip ls).map fun (x : TryHandler × Label) => match x.1 with
        | .tag n _ => TryHandler.tag n x.2
        | .default _ => .default x.2).map TryHandler.label ++ [ls.getLastD c] = ls
  | [], [l], _ => rfl
  | [], [], h => by simp at h
  | [], _ :: _ :: _, h => by simp at h
  | h :: hs, [], e => by simp at e
  | h :: hs, l :: ls, e => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at e
    have := tryTargets (c := c) hs ls e
    cases ls with
    | nil => simp at e
    | cons l' ls =>
      cases h <;> simpa [TryHandler.label, List.getLastD] using this

theorem setTargets_targets {i i' : MInst} {ls : List Label} (h : i.setTargets ls = some i') :
    i'.targets = ls ∧ ls.length = i.targets.length ∧
      ((∃ info ti', i' = .tryCall info ti') → ∃ info ti, i = .tryCall info ti) ∧
      ∀ a b c, i' ≠ .elfTlsGetAddr a b c := by
  unfold MInst.setTargets at h
  split at h
  all_goals (try split at h)
  all_goals (try (cases h; done))
  all_goals (cases h)
  all_goals refine ⟨?_, ?_, ?_, fun _ _ _ e => by cases e⟩
  all_goals first
    | exact fun _ => ⟨_, _, rfl⟩
    | (rintro ⟨_, _, e⟩; cases e; done)
    | (simp only [MInst.targets]; done)
    | (simp_all [MInst.targets]; done)
    | skip
  rename_i heq
  simp only [beq_iff_eq] at heq
  simp only [MInst.targets]
  exact tryTargets _ _ heq

/-! ## The kept blocks -/

theorem mk_iff {a : Array Bool} {b : Nat} : mk a b ↔ a.toList[b]? = some true := by
  simp only [mk, Array.getElem?_toList]
  cases a[b]? <;> simp

section
variable {α : Type}

theorem kept_mem : ∀ {l1 : List α} {l2 : List Bool} {x : α},
    x ∈ (l1.zip l2).filterMap (fun x => if x.2 = true then some x.1 else none) ↔
      ∃ i : Nat, l1[i]? = some x ∧ l2[i]? = some true
  | [], _, x => by simp
  | _ :: _, [], x => by simp
  | a :: l1, b :: l2, x => by
    rw [List.zip_cons_cons, List.filterMap_cons]
    have ih := kept_mem (l1 := l1) (l2 := l2) (x := x)
    constructor
    · intro h
      cases b
      · simp only [Bool.false_eq_true, ite_false] at h
        obtain ⟨i, h1, h2⟩ := ih.mp h
        exact ⟨i + 1, by simpa using h1, by simpa using h2⟩
      · simp only [ite_true, List.mem_cons] at h
        rcases h with rfl | h
        · exact ⟨0, rfl, rfl⟩
        · obtain ⟨i, h1, h2⟩ := ih.mp h
          exact ⟨i + 1, by simpa using h1, by simpa using h2⟩
    · rintro ⟨i, h1, h2⟩
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at h1 h2
        subst h1 h2
        simp
      | succ i =>
        have := ih.mpr ⟨i, by simpa using h1, by simpa using h2⟩
        split <;> simp [this]

theorem kept_sublist : ∀ (l1 : List α) (l2 : List Bool),
    ((l1.zip l2).filterMap (fun x => if x.2 = true then some x.1 else none)).Sublist l1
  | [], _ => by simp
  | _ :: _, [] => by simp
  | a :: l1, false :: l2 => by
    rw [List.zip_cons_cons, List.filterMap_cons]
    exact .cons a (kept_sublist l1 l2)
  | a :: l1, true :: l2 => by
    rw [List.zip_cons_cons, List.filterMap_cons]
    exact .cons₂ a (kept_sublist l1 l2)

theorem kept_head {a : α} {l1 : List α} {l2 : List Bool} :
    ((a :: l1).zip (true :: l2)).filterMap (fun x => if x.2 = true then some x.1 else none) =
      a :: (l1.zip l2).filterMap (fun x => if x.2 = true then some x.1 else none) := by
  simp

end

/-- The blocks `prepare` keeps. -/
abbrev keep (V : Array VBlock) (live : Array Bool) : Array VBlock :=
  Array.filterMap (fun x => if x.snd = true then some x.fst else none) (V.zip live)

theorem keep_toList (V : Array VBlock) (live : Array Bool) :
    (keep V live).toList =
      (V.toList.zip live.toList).filterMap (fun x => if x.2 = true then some x.1 else none) := by
  simp [keep, Array.toList_filterMap, Array.toList_zip]

theorem keep_lbls {V : Array VBlock} (hn : Lbls V) (live : Array Bool) : Lbls (keep V live) := by
  unfold Lbls at *
  rw [keep_toList]
  exact hn.sublist ((kept_sublist _ _).map _)

theorem keep_src {V : Array VBlock} {live : Array Bool} {k : Nat} (hk : k < (keep V live).size) :
    ∃ b, ∃ hb : b < V.size, (keep V live)[k] = V[b] ∧ mk live b := by
  have hm : (keep V live)[k] ∈ (keep V live).toList := Array.getElem_mem_toList hk
  rw [keep_toList] at hm
  obtain ⟨b, h1, h2⟩ := kept_mem.mp hm
  obtain ⟨hb, e⟩ := List.getElem?_eq_some_iff.mp h1
  rw [Array.length_toList] at hb
  exact ⟨b, hb, by rw [← e, Array.getElem_toList], mk_iff.mpr h2⟩

theorem keep_dst {V : Array VBlock} {live : Array Bool} {b : Nat} (hb : b < V.size) (hl : mk live b) :
    ∃ k, ∃ hk : k < (keep V live).size, (keep V live)[k] = V[b] := by
  have hm : V[b] ∈ (keep V live).toList := by
    rw [keep_toList]
    exact kept_mem.mpr ⟨b, by rw [Array.getElem?_toList, Array.getElem?_eq_getElem hb], mk_iff.mp hl⟩
  obtain ⟨k, hk, e⟩ := List.getElem_of_mem hm
  rw [Array.length_toList] at hk
  exact ⟨k, hk, by rw [← e, Array.getElem_toList]⟩

theorem keep_zero {V : Array VBlock} {live : Array Bool} (h0 : 0 < V.size) (hl : mk live 0) :
    ∃ hk : 0 < (keep V live).size, (keep V live)[0] = V[0] := by
  have e := keep_toList V live
  have hv : V.toList = V[0] :: V.toList.tail := by
    rcases hV : V.toList with _ | ⟨a, l⟩
    · have := Array.length_toList (xs := V); rw [hV] at this; simp at this; omega
    · have : V[0] = a := by rw [← Array.getElem_toList (h := h0)]; simp [hV]
      simp [this]
  have hL : live.toList = true :: live.toList.tail := by
    have h := mk_iff.mp hl
    cases hl' : live.toList with
    | nil => rw [hl'] at h; cases h
    | cons c l => rw [hl'] at h; simp at h; simp [h]
  rw [hv, hL, kept_head] at e
  have hk : 0 < (keep V live).size := by
    rw [← Array.length_toList, e]; exact Nat.zero_lt_succ _
  refine ⟨hk, ?_⟩
  rw [← Array.getElem_toList (h := hk)]
  simp only [e, List.getElem_cons_zero]

/-! ## Critical-edge splitting -/

theorem forIn_inv {ε α β : Type} (f : α → β → Except ε (ForInStep β)) :
    ∀ (l : List α) (P : Nat → β → Prop),
    (∀ k x b b', l[k]? = some x → P k b → f x b = .ok (.yield b') → P (k + 1) b') →
    (∀ x b b', f x b ≠ .ok (.done b')) →
    ∀ b r, P 0 b → forIn l b f = .ok r → P l.length r
  | [], P, _, _, b, r, h0, h => by
    simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact h0
  | a :: l, P, hs, hd, b, r, h0, h => by
    rw [List.forIn_cons] at h
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    rename_i st hst
    cases st with
    | done b' => exact absurd hst (hd a b b')
    | yield b' =>
      have := forIn_inv f l (fun k => P (k + 1)) (fun k x c c' hx hc hf => hs (k + 1) x c c'
        (by simpa using hx) hc hf) hd b' r (hs 0 a b b' rfl h0 hst) h
      simpa using this

/-- Edge blocks: block `e` is labelled `next0 + e` and only jumps. -/
def EdgesOk (next0 : Nat) (E : Array VBlock) : Prop :=
  ∀ (e : Nat) (he : e < E.size), ∃ l, E[e] = { label := next0 + e, insts := #[.jump l] }

/-- `E'` extends `E`. -/
def Ext (E E' : Array VBlock) : Prop := E.size ≤ E'.size ∧ ∀ e, e < E.size → E'[e]? = E[e]?

theorem ext_refl (E : Array VBlock) : Ext E E := ⟨Nat.le_refl _, fun _ _ => rfl⟩

theorem ext_trans {E E' E'' : Array VBlock} (h : Ext E E') (h' : Ext E' E'') : Ext E E'' :=
  ⟨Nat.le_trans h.1 h'.1, fun e he => by rw [h'.2 e (Nat.lt_of_lt_of_le he h.1), h.2 e he]⟩

theorem ext_push (E : Array VBlock) (b : VBlock) : Ext E (E.push b) :=
  ⟨by simp, fun e he => by simp [Array.getElem?_push, Nat.ne_of_lt he]⟩

/-- Block `vb'` is block `vb`, or `vb` with its terminator retargeted, a target being either
the old label or that of an edge block of `E` jumping to it. -/
def RwOk (E : Array VBlock) (vb vb' : VBlock) : Prop :=
  vb' = vb ∨ ∃ (t t' : MInst) (ls : List Label), vb.insts.back? = some t ∧ 2 ≤ t.targets.length ∧
    t.setTargets ls = some t' ∧ vb' = { vb with insts := vb.insts.pop.push t' } ∧
    ∀ (m : Nat) (l' : Label), ls[m]? = some l' → t.targets[m]? = some l' ∨
      ∃ (e : Nat) (l : Label), E[e]? = some { label := l', insts := #[.jump l] } ∧
        t.targets[m]? = some l

theorem rwOk_ext {E E' : Array VBlock} (h : Ext E E') {vb vb' : VBlock} (hr : RwOk E vb vb') :
    RwOk E' vb vb' := by
  rcases hr with rfl | ⟨t, t', ls, h1, h2, h3, h4, h5⟩
  · exact .inl rfl
  · refine .inr ⟨t, t', ls, h1, h2, h3, h4, fun m l' hm => ?_⟩
    rcases h5 m l' hm with h | ⟨e, l, he, hl⟩
    · exact .inl h
    · have hlt : e < E.size := (Array.getElem?_eq_some_iff.mp he).1
      exact .inr ⟨e, l, by rw [h.2 e hlt, he], hl⟩

/-- The invariant of the splitting loop after `k` kept blocks. -/
structure SInv (V1 : Array VBlock) (next0 k : Nat) (st : Nat × Array VBlock × Array VBlock) :
    Prop where
  next : st.2.2.size + next0 = st.1
  edges : EdgesOk next0 st.2.2
  size : st.2.1.size = k
  rw : ∀ (j : Nat) (h1 : j < V1.size) (h2 : j < st.2.1.size), RwOk st.2.2 V1[j] st.2.1[j]

/-- One successor of the splitting loop's inner loop. -/
def innerStep (ps : Array (Array Nat)) (st : Nat × Array VBlock × Array Label) (x : Nat × Label) :
    Nat × Array VBlock × Array Label :=
  if (ps[x.1]! : Array Nat).size > 1 then
    (st.1 + 1, st.2.1.push { label := st.1, insts := #[.jump x.2] }, st.2.2.push st.1)
  else (st.1, st.2.1, st.2.2.push x.2)

theorem innerFold (ps : Array (Array Nat)) (next0 : Nat) : ∀ (xs : List (Nat × Label))
    (next : Nat) (E : Array VBlock) (ls : Array Label), E.size + next0 = next → EdgesOk next0 E →
    (xs.foldl (innerStep ps) (next, E, ls)).2.1.size + next0 = (xs.foldl (innerStep ps) (next, E, ls)).1 ∧
    EdgesOk next0 (xs.foldl (innerStep ps) (next, E, ls)).2.1 ∧
    Ext E (xs.foldl (innerStep ps) (next, E, ls)).2.1 ∧
    (xs.foldl (innerStep ps) (next, E, ls)).2.2.size = ls.size + xs.length ∧
    (∀ j, j < ls.size → (xs.foldl (innerStep ps) (next, E, ls)).2.2[j]? = ls[j]?) ∧
    ∀ (j : Nat) (x : Nat × Label), xs[j]? = some x → ∃ l',
      (xs.foldl (innerStep ps) (next, E, ls)).2.2[ls.size + j]? = some l' ∧
      (l' = x.2 ∨ ∃ e : Nat, (xs.foldl (innerStep ps) (next, E, ls)).2.1[e]? =
        some ({ label := l', insts := #[.jump x.2] } : VBlock))
  | [], next, E, ls, hn, he => by
    simp only [List.foldl_nil, List.length_nil, Nat.add_zero]
    exact ⟨hn, he, ext_refl E, by simp, fun _ _ => by simp, fun j x h => by simp at h⟩
  | x :: xs, next, E, ls, hn, he => by
    simp only [List.foldl_cons]
    have hstep : ∃ (next' : Nat) (E' : Array VBlock) (ls' : Array Label),
        innerStep ps (next, E, ls) x = (next', E', ls') ∧
        E'.size + next0 = next' ∧ EdgesOk next0 E' ∧ Ext E E' ∧ ls' = ls.push ls'.back! ∧
        ls'.size = ls.size + 1 ∧
        (ls'.back! = x.2 ∨ ∃ e : Nat, E'[e]? = some ({ label := ls'.back!, insts := #[.jump x.2] } : VBlock)) := by
      by_cases hc : (ps[x.1]! : Array Nat).size > 1
      · refine ⟨next + 1, E.push { label := next, insts := #[.jump x.2] }, ls.push next,
          by simp only [innerStep, if_pos hc], by rw [Array.size_push]; omega, ?_,
          ext_push E _, by simp, by simp, .inr ⟨E.size, by simp⟩⟩
        intro e hes
        simp only [Array.size_push] at hes
        by_cases hee : e < E.size
        · obtain ⟨l, hl⟩ := he e hee
          exact ⟨l, by simp [Array.getElem_push, hee, hl]⟩
        · have : e = E.size := by omega
          subst this
          exact ⟨x.2, by simp only [Array.getElem_push_eq]; congr 1; rw [← hn, Nat.add_comm]⟩
      · exact ⟨next, E, ls.push x.2, by simp only [innerStep, if_neg hc], hn, he, ext_refl E,
          by simp, by simp, .inl (by simp)⟩
    obtain ⟨next', E', ls', heq, hn', he', hext, hls, hsz, hlast⟩ := hstep
    rw [heq]
    obtain ⟨r1, r2, r3, r4, r5, r6⟩ := innerFold ps next0 xs next' E' ls' hn' he'
    refine ⟨r1, r2, ext_trans hext r3, by rw [r4, hsz]; simp; omega, fun j hj => ?_, ?_⟩
    · rw [r5 j (by omega), hls, Array.getElem?_push]
      simp [Nat.ne_of_lt hj]
    · intro j y hy
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hy
        subst hy
        refine ⟨ls'.back!, ?_, ?_⟩
        · rw [Nat.add_zero, r5 ls.size (by omega), hls]; simp
        · rcases hlast with h | ⟨e, he⟩
          · exact .inl h
          · have hlt : e < E'.size := (Array.getElem?_eq_some_iff.mp he).1
            exact .inr ⟨e, by rw [r3.2 e hlt, he]⟩
      | succ j =>
        obtain ⟨l', h1, h2⟩ := r6 j y (by simpa using hy)
        exact ⟨l', by rw [hsz] at h1; rw [← h1]; congr 1; omega, h2⟩

/-- The first edge-block label: above every kept label. -/
def next0Of (V : Array VBlock) : Nat := Array.foldl (fun m b => max m b.label) 0 V + 1

theorem foldl_max_ge : ∀ (l : List VBlock) (m : Nat), m ≤ l.foldl (fun m b => max m b.label) m ∧
    ∀ b ∈ l, b.label ≤ l.foldl (fun m b => max m b.label) m
  | [], m => by simp
  | b :: l, m => by
    obtain ⟨h1, h2⟩ := foldl_max_ge l (max m b.label)
    simp only [List.foldl_cons, List.mem_cons]
    have := Nat.le_max_left m b.label
    have := Nat.le_max_right m b.label
    refine ⟨by omega, fun c hc => ?_⟩
    rcases hc with rfl | hc
    · exact Nat.le_trans (Nat.le_max_right _ _) h1
    · exact h2 c hc

theorem lt_next0 {V : Array VBlock} {k : Nat} (hk : k < V.size) : V[k].label < next0Of V := by
  have := (foldl_max_ge V.toList 0).2 V[k] (by simp)
  unfold next0Of
  rw [← Array.foldl_toList]
  exact Nat.lt_succ_of_le this

/-- **`prepare`, step by step.** -/
theorem prepare_facts {vc vcp : VCode} (h : prepare vc = .ok vcp) :
    ∃ (ss0 ps0 ss1 ps1 ss2 ps2 : Array (Array Nat)) (next : Nat) (B E : Array VBlock),
      vc.cfg = .ok (ss0, ps0) ∧
      ({ vc with blocks := keep vc.blocks (reachable ss0) } : VCode).cfg = .ok (ss1, ps1) ∧
      SInv (keep vc.blocks (reachable ss0)) (next0Of (keep vc.blocks (reachable ss0)))
        (keep vc.blocks (reachable ss0)).size (next, B, E) ∧
      ({ vc with blocks := B ++ E } : VCode).cfg = .ok (ss2, ps2) ∧
      vcp = { vc with blocks := (rpo ss2).map fun i => (B ++ E)[i]! } := by
  unfold prepare at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  rename_i r0 hc0
  split at h
  · cases h
  rename_i r1 hc1
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  split at h
  · cases h
  rename_i st hfor
  split at h
  · cases h
  rename_i r2 hc2
  simp only [pure, Except.pure, Except.ok.injEq] at h
  have hcs1 := cfg_spec hc1
  refine ⟨r0.1, r0.2, r1.1, r1.2, r2.1, r2.2, st.1, st.2.1, st.2.2, hc0, hc1, ?_, hc2, h.symm⟩
  rw [← Array.forIn_toList] at hfor
  have := forIn_inv _ _ (fun k st => SInv (keep vc.blocks (reachable r0.1))
      (next0Of (keep vc.blocks (reachable r0.1))) k st) ?_ ?_ _ st ?_ hfor
  · rw [Array.length_toList, Array.size_zipIdx] at this; exact this
  · intro k x b b' hx hb hf
    rw [Array.toList_zipIdx, List.getElem?_zipIdx] at hx
    obtain ⟨vb, hvb, rfl⟩ : ∃ vb, (keep vc.blocks (reachable r0.1)).toList[k]? = some vb ∧ x = (vb, 0 + k) := by
      cases e : (keep vc.blocks (reachable r0.1)).toList[k]? with
      | none => rw [e] at hx; cases hx
      | some vb => rw [e] at hx; simp only [Option.map_some, Option.some.injEq] at hx
                   exact ⟨vb, rfl, hx.symm⟩
    simp only [Nat.zero_add] at hf ⊢
    obtain ⟨hk, hvb'⟩ := List.getElem?_eq_some_iff.mp hvb
    rw [Array.length_toList] at hk
    have hvbk : (keep vc.blocks (reachable r0.1))[k] = vb := by rw [← hvb', Array.getElem_toList]
    split at hf
    · -- no splitting
      simp only [pure, Except.pure, Except.ok.injEq, ForInStep.yield.injEq] at hf
      subst hf
      refine ⟨hb.next, hb.edges, by simp [hb.size], fun j h1 h2 => ?_⟩
      simp only [Array.size_push] at h2
      by_cases hj : j < b.2.1.size
      · simp only [Array.getElem_push, hj, dite_true]
        exact hb.rw j h1 hj
      · have : j = k := by have := hb.size; omega
        subst this
        simp only [Array.getElem_push, hj, dite_false]
        exact .inl hvbk.symm
    · rename_i hge
      split at hf
      · rename_i t ht
        split at hf
        · cases hf
        rename_i v hv
        split at hf
        · rename_i t' ht'
          simp only [pure, Except.pure, Except.ok.injEq, ForInStep.yield.injEq] at hf
          subst hf
          rw [← Array.forIn_toList, forIn_yield_foldl _ _ (innerStep r1.2) _
            (fun a c => by simp only [innerStep]; split <;> rfl)] at hv
          simp only [pure, Except.pure, Except.ok.injEq] at hv
          subst hv
          obtain ⟨r1', r2', r3', r4', -, r6'⟩ := innerFold r1.2 (next0Of (keep vc.blocks (reachable r0.1)))
            ((r1.1[k]! : Array Nat).zip t.targets.toArray).toList b.1 b.2.2 #[] hb.next hb.edges
          -- the successors of the kept block
          obtain ⟨t0, ts, hb0, -, hts, htsz, -⟩ := hcs1.blk k vb (by
            show (keep vc.blocks (reachable r0.1))[k]? = some vb
            rw [← Array.getElem?_toList]; exact hvb)
          rw [ht] at hb0
          cases hb0
          have hts' : (r1.1[k]! : Array Nat) = ts := by
            simp only [getElem!_def, hts]
          rw [hts'] at hge
          have h2 : 2 ≤ t.targets.length := by omega
          refine ⟨r1', r2', by simp [hb.size], fun j h1 h2' => ?_⟩
          simp only [Array.size_push] at h2'
          by_cases hj : j < b.2.1.size
          · simp only [Array.getElem_push, hj, dite_true]
            exact rwOk_ext r3' (hb.rw j h1 hj)
          · have : j = k := by have := hb.size; omega
            subst this
            simp only [Array.getElem_push, hj, dite_false]
            rw [hvbk]
            refine .inr ⟨t, t', _, ht, h2, ht', rfl, fun m l' hm => ?_⟩
            rw [Array.getElem?_toList] at hm
            have hmlt := (Array.getElem?_eq_some_iff.mp hm).1
            rw [r4'] at hmlt
            simp only [Array.size_empty, Nat.zero_add] at hmlt
            obtain ⟨y, hy⟩ : ∃ y, (((r1.1[j]! : Array Nat).zip t.targets.toArray).toList)[m]? = some y :=
              ⟨_, List.getElem?_eq_getElem hmlt⟩
            obtain ⟨l'', hl1, hl2⟩ := r6' m y hy
            simp only [Array.size_empty, Nat.zero_add] at hl1
            rw [hm] at hl1
            cases hl1
            have hty : t.targets[m]? = some y.2 := by
              rw [Array.toList_zip] at hy
              have := (List.getElem?_zip_eq_some.mp hy).2
              simpa using this
            rcases hl2 with e | ⟨e, he⟩
            · exact .inl (by rw [hty, e])
            · exact .inr ⟨e, y.2, he, hty⟩
        · simp [throw, throwThe, MonadExceptOf.throw] at hf
      · simp [throw, throwThe, MonadExceptOf.throw] at hf
  · intro x c c' hf
    split at hf
    · cases hf
    · split at hf
      · split at hf
        · cases hf
        · split at hf
          · cases hf
          · simp [throw, throwThe, MonadExceptOf.throw] at hf
      · simp [throw, throwThe, MonadExceptOf.throw] at hf
  · refine ⟨?_, fun e he => by simp at he, rfl, fun j _ h => by simp at h⟩
    simp only [Array.size_empty, Nat.zero_add, next0Of, keep]

end Backend.Proof.Prep
