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
      | none => simp only
      | some s => simp only; split <;> rfl

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
    exact .cons_cons a (kept_sublist l1 l2)

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
  simp [keep, Array.toList_zip]

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
          by simp only [innerStep, hc, ↓reduceIte], by rw [Array.size_push]; omega, ?_,
          ext_push E _, by simp, by simp, .inr ⟨E.size, by simp⟩⟩
        intro e hes
        simp only [Array.size_push] at hes
        by_cases hee : e < E.size
        · obtain ⟨l, hl⟩ := he e hee
          exact ⟨l, by simp [Array.getElem_push, hee, hl]⟩
        · have : e = E.size := by omega
          subst this
          exact ⟨x.2, by simp only [Array.getElem_push_eq]; congr 1; rw [← hn, Nat.add_comm]⟩
      · exact ⟨next, E, ls.push x.2, by simp only [innerStep, hc, ↓reduceIte], hn, he, ext_refl E,
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

/-! ## The split blocks `B ++ E` -/

theorem succsIn_of {V : Array VBlock} {ss : Array (Array Nat)} (cs : CfgSpec V ss) : SuccsIn ss := by
  intro b s hs
  rcases Nat.lt_or_ge b V.size with hb | hb
  · obtain ⟨t, ts, -, -, hts, htsz, hl⟩ := cs.blk b V[b] (Array.getElem?_eq_getElem hb)
    have e : (ss[b]! : Array Nat) = ts := by simp [getElem!_def, hts]
    rw [e] at hs
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hs
    simp only [Array.length_toList] at hj
    obtain ⟨l, hl'⟩ : ∃ l, t.targets[j]? = some l :=
      ⟨_, List.getElem?_eq_getElem (by rw [← htsz]; exact hj)⟩
    obtain ⟨k, hk, hlab⟩ := hl j l hl'
    rw [Array.getElem?_eq_getElem hj] at hk
    cases hk
    obtain ⟨hk', -⟩ := lab_some hlab
    simp only [Array.getElem_toList]
    rw [cs.size]; exact hk'
  · have : (ss[b]! : Array Nat) = #[] := by
      simp [getElem!_def, Array.getElem?_eq_none (show ss.size ≤ b by rw [cs.size]; exact hb)]; rfl
    rw [this] at hs; simp at hs

theorem rw_fields {E : Array VBlock} {vb vb' : VBlock} (h : RwOk E vb vb') :
    vb'.label = vb.label ∧ vb'.params = vb.params ∧ vb'.branchArgs = vb.branchArgs := by
  rcases h with rfl | ⟨_, _, _, _, _, _, rfl, _⟩ <;> exact ⟨rfl, rfl, rfl⟩

section split
variable {V1 B E : Array VBlock} {next : Nat}
  (hS : SInv V1 (next0Of V1) V1.size (next, B, E))
include hS

theorem lbls2 (hn : Lbls V1) : Lbls (B ++ E) := by
  have hB : B.toList.map VBlock.label = V1.toList.map VBlock.label := by
    apply List.ext_getElem
    · simp [hS.size]
    · intro j h1 h2
      simp only [List.getElem_map, Array.getElem_toList]
      simp only [List.length_map, Array.length_toList] at h1 h2
      exact (rw_fields (hS.rw j h2 h1)).1
  have hE : E.toList.map VBlock.label = (List.range E.size).map (next0Of V1 + ·) := by
    apply List.ext_getElem
    · simp
    · intro j h1 h2
      simp only [List.length_map, Array.length_toList] at h1
      obtain ⟨l, hl⟩ := hS.edges j h1
      simp [hl]
  unfold Lbls at *
  rw [Array.toList_append, List.map_append, hB, hE, List.nodup_append]
  refine ⟨hn, List.Pairwise.map _ (fun a b h e => h (by simp at e; omega)) List.nodup_range, ?_⟩
  intro a ha b hb e
  subst e
  obtain ⟨vb, hvb, rfl⟩ := List.mem_map.mp ha
  obtain ⟨j, -, hj⟩ := List.mem_map.mp hb
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hvb
  simp only [Array.length_toList] at hk
  have h1 : V1[k].label < next0Of V1 := lt_next0 hk
  have hj' : next0Of V1 + j = V1[k].label := by simpa using hj
  rw [← hj'] at h1
  exact absurd h1 (Nat.not_lt.mpr (Nat.le_add_right _ _))

theorem v2_B {k : Nat} (hk : k < V1.size) : ∃ hkB : k < B.size, (B ++ E)[k]? = some B[k] := by
  have hkB : k < B.size := by rw [hS.size]; exact hk
  exact ⟨hkB, by rw [Array.getElem?_append_left hkB, Array.getElem?_eq_getElem hkB]⟩

theorem v2_E {e : Nat} : (B ++ E)[V1.size + e]? = E[e]? := by
  rw [Array.getElem?_append_right (by rw [hS.size]; omega)]
  congr 1; rw [hS.size]; omega

theorem v2_size : (B ++ E).size = V1.size + E.size := by simp [hS.size]

/-- A kept block and its rewrite in `B`. -/
theorem blk2 {ss1 : Array (Array Nat)} (cs1 : CfgSpec V1 ss1) {k : Nat} (hk : k < V1.size) :
    ∃ (hkB : k < B.size) (t t' : MInst), V1[k].insts.back? = some t ∧ B[k].insts.back? = some t' ∧
      B[k].label = V1[k].label ∧ B[k].params = V1[k].params ∧
      B[k].branchArgs = V1[k].branchArgs ∧ B[k].insts.size = V1[k].insts.size ∧
      B[k].insts.pop = V1[k].insts.pop ∧ (t' = t ∨ t.setTargets t'.targets = some t') ∧
      t'.targets.length = t.targets.length ∧
      ∀ (j : Nat) (l' : Label), t'.targets[j]? = some l' → ∃ l, t.targets[j]? = some l ∧
        (l' = l ∨ (2 ≤ t.targets.length ∧
          ∃ e : Nat, E[e]? = some ({ label := l', insts := #[.jump l] } : VBlock))) := by
  have hkB : k < B.size := by rw [hS.size]; exact hk
  obtain ⟨t, -, ht, -⟩ := cs1.blk k V1[k] (Array.getElem?_eq_getElem hk)
  refine ⟨hkB, ?_⟩
  rcases hS.rw k hk hkB with e | ⟨t0, t', ls, h1, h2, h3, h4, h5⟩
  · rw [e]
    exact ⟨t, t, ht, ht, rfl, rfl, rfl, rfl, rfl, .inl rfl, rfl,
      fun j l' hl => ⟨l', hl, .inl rfl⟩⟩
  · rw [ht] at h1
    cases h1
    obtain ⟨hT, hlen, -⟩ := setTargets_targets h3
    have hne : 0 < V1[k].insts.size := by
      rcases Nat.eq_zero_or_pos V1[k].insts.size with h | h
      · simp [Array.back?, h] at ht
      · exact h
    rw [h4]
    refine ⟨t, t', ht, by simp, rfl, rfl, rfl, by simp; omega, by simp, .inr (by rw [hT]; exact h3),
      by rw [hT, hlen], fun j l' hl => ?_⟩
    rw [hT] at hl
    rcases h5 j l' hl with h | ⟨e, l, he, hl2⟩
    · exact ⟨l', h, .inl rfl⟩
    · exact ⟨l, hl2, .inr ⟨h2, e, by rw [he]⟩⟩

end split

/-! ## The reordered blocks -/

section order
variable {V2 : Array VBlock} {R : Array Nat} (hR : ∀ i ∈ R.toList, i < V2.size)
include hR

theorem v3_get {q : Nat} (hq : q < R.size) :
    ∃ hi : R[q] < V2.size, (R.map fun i => V2[i]!)[q]? = some V2[R[q]] := by
  have hi : R[q] < V2.size := hR _ (by simp)
  refine ⟨hi, ?_⟩
  simp [Array.getElem?_map, Array.getElem?_eq_getElem hq, getElem!_pos V2 R[q] hi]

theorem lbls3 (hn : Lbls V2) (hRn : R.toList.Nodup) : Lbls (R.map fun i => V2[i]!) := by
  unfold Lbls
  rw [List.nodup_iff_eq_of_getElem_eq]
  intro p q hp hq e
  simp only [List.length_map, Array.length_toList, Array.size_map] at hp hq
  simp only [List.getElem_map, Array.getElem_toList, Array.getElem_map] at e
  have hp' : R[p] < V2.size := hR _ (by simp)
  have hq' : R[q] < V2.size := hR _ (by simp)
  rw [getElem!_pos V2 R[p] hp', getElem!_pos V2 R[q] hq'] at e
  have := lbl_inj hn hp' hq' e
  exact hRn.eq_of_getElem_eq (by simpa using hp) (by simpa using hq) (by simpa using this)

theorem lab3 (hn : Lbls V2) (hRn : R.toList.Nodup) {i : Nat} (hi : i ∈ R.toList) :
    ∃ q, ∃ hq : q < R.size, R[q] = i ∧ lab (R.map fun i => V2[i]!) (V2[i]!).label = some q := by
  obtain ⟨q, hq, e⟩ := List.getElem_of_mem hi
  simp only [Array.length_toList, Array.getElem_toList] at hq e
  refine ⟨q, hq, e, lab_of (lbls3 hR hn hRn) (by simpa using hq) (by simp [e])⟩

theorem lab3_inv {l : Label} {q : Nat} (h : lab (R.map fun i => V2[i]!) l = some q) :
    ∃ hq : q < R.size, ∃ hi : R[q] < V2.size,
      (R.map fun i => V2[i]!)[q]? = some V2[R[q]] ∧ V2[R[q]].label = l := by
  obtain ⟨hq, hl⟩ := lab_some h
  have hq' : q < R.size := by simpa using hq
  obtain ⟨hi, e⟩ := v3_get hR hq'
  refine ⟨hq', hi, e, ?_⟩
  rw [← hl]
  simp [getElem!_pos V2 R[q] hi]

end order

/-! ## Reachability across the steps -/

theorem reach_mk {ss : Array (Array Nat)} (hin : SuccsIn ss) (h0 : ss.size ≠ 0) {b : Nat}
    (h : Reach ss b) : mk (reachable ss) b := by
  induction h with
  | entry => exact (reachable_spec hin h0).2.1
  | step _ hs ih => exact (reachable_spec hin h0).2.2.1 _ ih _ hs

/-- The successor `s` of block `b`, by label. -/
theorem succ_of {V : Array VBlock} {ss : Array (Array Nat)} (cs : CfgSpec V ss) {b s : Nat}
    (hs : s ∈ (ss[b]! : Array Nat).toList) :
    ∃ (hb : b < V.size) (t : MInst) (j : Nat) (l : Label), V[b].insts.back? = some t ∧
      t.targets[j]? = some l ∧ lab V l = some s := by
  have hb : b < V.size := by
    rcases Nat.lt_or_ge b V.size with h | h
    · exact h
    · have : (ss[b]! : Array Nat) = #[] := by
        simp [getElem!_def, Array.getElem?_eq_none (show ss.size ≤ b by rw [cs.size]; exact h)]; rfl
      rw [this] at hs; simp at hs
  obtain ⟨t, ts, ht, -, hts, htsz, hl⟩ := cs.blk b V[b] (Array.getElem?_eq_getElem hb)
  have e : (ss[b]! : Array Nat) = ts := by simp [getElem!_def, hts]
  rw [e] at hs
  obtain ⟨j, hj, hjs⟩ := List.getElem_of_mem hs
  simp only [Array.length_toList, Array.getElem_toList] at hj hjs
  obtain ⟨l, hl'⟩ : ∃ l, t.targets[j]? = some l :=
    ⟨_, List.getElem?_eq_getElem (by rw [← htsz]; exact hj)⟩
  obtain ⟨k, hk, hlab⟩ := hl j l hl'
  rw [Array.getElem?_eq_getElem hj, hjs] at hk
  cases hk
  exact ⟨hb, t, j, l, ht, hl', hlab⟩

/-- A successor by label: `lab V l` is among the successors of a block targeting `l`. -/
theorem succ_mem {V : Array VBlock} {ss : Array (Array Nat)} (cs : CfgSpec V ss) {b : Nat}
    (hb : b < V.size) {t : MInst} (ht : V[b].insts.back? = some t) {j : Nat} {l : Label}
    (hl : t.targets[j]? = some l) {s : Nat} (hs : lab V l = some s) :
    s ∈ (ss[b]! : Array Nat).toList := by
  obtain ⟨t', ts, ht', -, hts, -, hl'⟩ := cs.blk b V[b] (Array.getElem?_eq_getElem hb)
  rw [ht] at ht'; cases ht'
  obtain ⟨k, hk, hlab⟩ := hl' j l hl
  rw [hs] at hlab; cases hlab
  have e : (ss[b]! : Array Nat) = ts := by simp [getElem!_def, hts]
  rw [e]
  obtain ⟨hj, rfl⟩ := Array.getElem?_eq_some_iff.mp hk
  simp

theorem reach01 {V0 : Array VBlock} {ss0 ss1 : Array (Array Nat)} (cs0 : CfgSpec V0 ss0)
    (cs1 : CfgSpec (keep V0 (reachable ss0)) ss1) (hn : Lbls V0) (h0 : 0 < V0.size) {b : Nat}
    (h : Reach ss0 b) : ∃ k, ∃ hk : k < (keep V0 (reachable ss0)).size, ∃ hb : b < V0.size,
      (keep V0 (reachable ss0))[k] = V0[b] ∧ Reach ss1 k := by
  have hin := succsIn_of cs0
  have hs0 : ss0.size ≠ 0 := by rw [cs0.size]; omega
  induction h with
  | entry =>
    obtain ⟨hk, e⟩ := keep_zero h0 (reachable_spec hin hs0).2.1
    exact ⟨0, hk, h0, e, .entry⟩
  | @step b s hr hs ih =>
    obtain ⟨k, hk, hb, e, hrk⟩ := ih
    obtain ⟨hb', t, j, l, ht, hl, hlab⟩ := succ_of cs0 hs
    obtain ⟨hs', hls⟩ := lab_some hlab
    have hmk := reach_mk hin hs0 (Reach.step hr hs)
    obtain ⟨k', hk', e'⟩ := keep_dst hs' hmk
    refine ⟨k', hk', hs', e', .step hrk (succ_mem cs1 hk (t := t) (by rw [e]; exact ht) hl ?_)⟩
    exact lab_of (keep_lbls hn _) hk' (by rw [e', hls])

theorem reach12 {V1 B E : Array VBlock} {next : Nat} (hS : SInv V1 (next0Of V1) V1.size (next, B, E))
    {ss1 ss2 : Array (Array Nat)} (cs1 : CfgSpec V1 ss1) (cs2 : CfgSpec (B ++ E) ss2)
    (hn : Lbls V1) (h0 : 0 < V1.size) {k : Nat} (h : Reach ss1 k) : k < V1.size ∧ Reach ss2 k := by
  have hn2 := lbls2 hS hn
  have lab_k : ∀ k (hk : k < V1.size), lab (B ++ E) V1[k].label = some k := fun k hk => by
    obtain ⟨hkB, e⟩ := v2_B hS hk
    have hk2 : k < (B ++ E).size := (Array.getElem?_eq_some_iff.mp e).1
    refine lab_of hn2 hk2 ?_
    have : (B ++ E)[k] = B[k] := Option.some.inj (by rw [← Array.getElem?_eq_getElem hk2, e])
    rw [this]
    exact (rw_fields (hS.rw k hk hkB)).1
  induction h with
  | entry => exact ⟨h0, .entry⟩
  | @step k k' _ hs ih =>
    obtain ⟨hk, hr⟩ := ih
    obtain ⟨hk1, t, j, l, ht, hl, hlab⟩ := succ_of cs1 hs
    obtain ⟨hk', hlk'⟩ := lab_some hlab
    obtain ⟨hkB, t0, t', ht0, ht', -, -, -, -, -, -, hlen, hrel⟩ := blk2 hS cs1 hk
    obtain rfl : t0 = t := by rw [ht] at ht0; exact (Option.some.inj ht0).symm
    obtain ⟨hkB', e2⟩ := v2_B hS hk
    have hk2 : k < (B ++ E).size := (Array.getElem?_eq_some_iff.mp e2).1
    have hBk : (B ++ E)[k] = B[k] := Option.some.inj (by rw [← Array.getElem?_eq_getElem hk2, e2])
    obtain ⟨l', hl'⟩ : ∃ l', t'.targets[j]? = some l' :=
      ⟨_, List.getElem?_eq_getElem (by rw [hlen]; exact (List.getElem?_eq_some_iff.mp hl).1)⟩
    obtain ⟨l0, hl0, hcase⟩ := hrel j l' hl'
    rw [hl] at hl0; cases hl0
    refine ⟨hk', ?_⟩
    rcases hcase with rfl | ⟨-, e, he⟩
    · exact .step hr (succ_mem cs2 hk2 (by rw [hBk]; exact ht') hl' (by rw [← hlk']; exact lab_k k' hk'))
    · have he2 : (B ++ E)[V1.size + e]? = some { label := l', insts := #[.jump l] } := by
        rw [v2_E hS, he]
      have hu : V1.size + e < (B ++ E).size := (Array.getElem?_eq_some_iff.mp he2).1
      have hEu : (B ++ E)[V1.size + e] = { label := l', insts := #[.jump l] } :=
        Option.some.inj (by rw [← Array.getElem?_eq_getElem hu, he2])
      have hr2 : Reach ss2 (V1.size + e) :=
        .step hr (succ_mem cs2 hk2 (by rw [hBk]; exact ht') hl' (lab_of hn2 hu (by rw [hEu])))
      refine .step hr2 (succ_mem cs2 hu (t := .jump l) (j := 0) (by rw [hEu]; rfl) rfl ?_)
      rw [← hlk']; exact lab_k k' hk'

/-! ## Completeness -/

/-- The VCode on which `prepCheck` accepts `prepare`'s output: at least one block, distinct
labels, and branch arguments only on blocks with at most one successor (`lowerFunction`'s
VCode: labels are block indices, `branchArgs` only on a `jump` block or an edge block). -/
structure PrepDomain (vc : VCode) : Prop where
  nonempty : 0 < vc.blocks.size
  labels : Lbls vc.blocks
  args : ∀ (b : Nat) (vb : VBlock) (t : MInst), vc.blocks[b]? = some vb → vb.insts.back? = some t →
    2 ≤ t.targets.length → vb.branchArgs = #[]

theorem pop_mem {α : Type} {xs : Array α} {x : α} (h : x ∈ xs.pop.toList) : x ∈ xs.toList := by
  rw [Array.toList_pop] at h
  exact List.dropLast_subset _ h

section main
variable {vc : VCode} {ss0 ss1 ss2 : Array (Array Nat)} {next : Nat} {B E : Array VBlock}
  (hd : PrepDomain vc) (cs0 : CfgSpec vc.blocks ss0)
  (cs1 : CfgSpec (keep vc.blocks (reachable ss0)) ss1) (cs2 : CfgSpec (B ++ E) ss2)
  (hS : SInv (keep vc.blocks (reachable ss0)) (next0Of (keep vc.blocks (reachable ss0)))
    (keep vc.blocks (reachable ss0)).size (next, B, E))

local notation "V1" => keep vc.blocks (reachable ss0)

include hd cs0 cs1 cs2 hS

omit cs1 in
theorem facts_basic :
    0 < (keep vc.blocks (reachable ss0)).size ∧ (keep vc.blocks (reachable ss0))[0]? = vc.blocks[0]? ∧
      mk (reachable ss0) 0 ∧ Lbls (keep vc.blocks (reachable ss0)) ∧ Lbls (B ++ E) ∧
      (∀ i ∈ (rpo ss2).toList, i < (B ++ E).size) ∧ (rpo ss2).toList.Nodup ∧
      (rpo ss2)[0]? = some 0 ∧
      (∀ i ∈ (rpo ss2).toList, ∀ s ∈ (ss2[i]! : Array Nat).toList, s ∈ (rpo ss2).toList) ∧
      (∀ b, Reach ss2 b → b ∈ (rpo ss2).toList) := by
  have hs0 : ss0.size ≠ 0 := by rw [cs0.size]; have := hd.nonempty; omega
  obtain ⟨-, hl0, -, -⟩ := reachable_spec (succsIn_of cs0) hs0
  obtain ⟨h10, hk0⟩ := keep_zero hd.nonempty hl0
  have hn1 := keep_lbls hd.labels (reachable ss0)
  have hs2 : ss2.size ≠ 0 := by rw [cs2.size, v2_size hS]; omega
  obtain ⟨hRlt, hRn, hR0, hRcl, hRre⟩ := rpo_spec (succsIn_of cs2) hs2
  refine ⟨h10, by rw [Array.getElem?_eq_getElem h10, Array.getElem?_eq_getElem hd.nonempty, hk0],
    hl0, hn1, lbls2 hS hn1, fun i hi => cs2.size ▸ hRlt i hi, hRn, hR0, hRcl, hRre⟩

omit cs1 in
/-- `prepare`'s output has a CFG. -/
theorem cfg3 : ∃ ss3 ps3, ({ vc with blocks := (rpo ss2).map fun i => (B ++ E)[i]! } : VCode).cfg = .ok (ss3, ps3) := by
  obtain ⟨-, -, -, -, hn2, hR, hRn, -, hRcl, -⟩ := facts_basic hd cs0 cs2 hS
  apply cfg_of
  intro q vb hq
  have hqR : q < (rpo ss2).size := by
    have := (Array.getElem?_eq_some_iff.mp hq).1; simpa using this
  obtain ⟨hi, e⟩ := v3_get hR hqR
  have hvb : vb = (B ++ E)[(rpo ss2)[q]] := by
    have : ((rpo ss2).map fun i => (B ++ E)[i]!)[q]? = some vb := hq
    rw [e] at this; exact (Option.some.inj this).symm
  subst hvb
  obtain ⟨t, ts, ht, hterm, hts, htsz, hl⟩ := cs2.blk _ _ (Array.getElem?_eq_getElem hi)
  refine ⟨t, ht, hterm, fun l hlm => ?_⟩
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hlm
  obtain ⟨k, -, hk⟩ := hl j _ (List.getElem?_eq_getElem hj)
  have hkR := hRcl _ (by simp) k (succ_mem cs2 hi ht (List.getElem?_eq_getElem hj) hk)
  obtain ⟨q', -, -, hq'⟩ := lab3 hR hn2 hRn hkR
  obtain ⟨hk2, hlk⟩ := lab_some hk
  rw [getElem!_pos (B ++ E) k hk2, hlk] at hq'
  exact ⟨q', hq'⟩

omit cs1 in
/-- Every instruction of `prepare`'s output is one of `vc`, a retargeted one, or an edge
block's `jump`. -/
theorem insts3 {vb' : VBlock} (hvb : vb' ∈ ((rpo ss2).map fun i => (B ++ E)[i]!).toList) {i' : MInst} (hi : i' ∈ vb'.insts.toList) :
    (∃ vb ∈ vc.blocks.toList, i' ∈ vb.insts.toList) ∨
      (∃ vb ∈ vc.blocks.toList, ∃ i ∈ vb.insts.toList, ∃ ls, i.setTargets ls = some i') ∨
      ∃ l, i' = .jump l := by
  obtain ⟨-, -, -, -, -, hR, -, -, -, -⟩ := facts_basic hd cs0 cs2 hS
  rw [Array.mem_toList_iff, Array.mem_map] at hvb
  obtain ⟨i, hiR, rfl⟩ := hvb
  have hi2 : i < (B ++ E).size := hR i (by simpa using hiR)
  rw [getElem!_pos (B ++ E) i hi2] at hi
  by_cases hiB : i < B.size
  · rw [Array.getElem_append_left hiB] at hi
    have hi1 : i < (V1).size := by rw [← hS.size]; exact hiB
    obtain ⟨b, hb, e, -⟩ := keep_src hi1
    have hmem : (V1)[i] ∈ vc.blocks.toList := by rw [e]; simp
    rcases hS.rw i hi1 hiB with h | ⟨t, t', ls, h1, -, h3, h4, -⟩
    · rw [h] at hi; exact .inl ⟨_, hmem, hi⟩
    · rw [h4] at hi
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hi
      rcases hi with hi | rfl
      · exact .inl ⟨_, hmem, pop_mem hi⟩
      · exact .inr (.inl ⟨_, hmem, t, Array.mem_toList_iff.mpr (Array.mem_of_back? h1), ls, h3⟩)
  · rw [Array.getElem_append_right (Nat.le_of_not_lt hiB)] at hi
    have he : i - B.size < E.size := by simp at hi2; omega
    obtain ⟨l, hl⟩ := hS.edges _ he
    rw [hl] at hi
    simp at hi
    exact .inr (.inr ⟨l, hi⟩)

/-- A live block of `vc`: its counterpart in `prepare`'s output, accepted by `keptOk`. -/
theorem live_ok {ss3 ps3 : Array (Array Nat)}
    (hc3 : ({ vc with blocks := (rpo ss2).map fun i => (B ++ E)[i]! } : VCode).cfg = .ok (ss3, ps3)) {b : Nat} (hb : b < vc.blocks.size)
    (hl : mk (reachable ss0) b) : ∃ q, sigmaOf vc { vc with blocks := (rpo ss2).map fun i => (B ++ E)[i]! } b = some q ∧
      keptOk vc { vc with blocks := (rpo ss2).map fun i => (B ++ E)[i]! } ss0 ss3 b q = true := by
  obtain ⟨h10, -, -, hn1, hn2, hR, hRn, -, -, hRre⟩ := facts_basic hd cs0 cs2 hS
  have cs3 : CfgSpec ((rpo ss2).map fun i => (B ++ E)[i]!) ss3 := cfg_spec hc3
  have hs0 : ss0.size ≠ 0 := by rw [cs0.size]; have := hd.nonempty; omega
  have hb' := (reachable_spec (succsIn_of cs0) hs0).2.2.2 b hl
  obtain ⟨k, hk, hb0, ek, hr1⟩ := reach01 cs0 cs1 hd.labels hd.nonempty hb'
  obtain ⟨-, hr2⟩ := reach12 hS cs1 cs2 hn1 h10 hr1
  obtain ⟨q, hq, hRq, hlab⟩ := lab3 hR hn2 hRn (hRre k hr2)
  obtain ⟨hkB, e2⟩ := v2_B hS hk
  have hk2 : k < (B ++ E).size := (Array.getElem?_eq_some_iff.mp e2).1
  have hBk : (B ++ E)[k] = B[k] := Option.some.inj (by rw [← Array.getElem?_eq_getElem hk2, e2])
  obtain ⟨hkB2, t, t', ht, ht', hlabel, hpar, hargs, hsz, hpop, hsame, hlen, hrel⟩ := blk2 hS cs1 hk
  rw [ek] at ht hlabel hpar hargs hsz hpop
  have hlabk : (B ++ E)[k]!.label = vc.blocks[b].label := by
    rw [getElem!_pos (B ++ E) k hk2, hBk, hlabel]
  rw [hlabk] at hlab
  -- the counterpart
  have hσ : ∀ s (hs : s < vc.blocks.size), sigmaOf vc { vc with blocks := (rpo ss2).map fun i => (B ++ E)[i]! } s =
      lab ((rpo ss2).map fun i => (B ++ E)[i]!) vc.blocks[s].label := fun s hs => by
    unfold sigmaOf; rw [Array.getElem?_eq_getElem hs]; rfl
  have hq3 : ((rpo ss2).map fun i => (B ++ E)[i]!)[q]? = some B[k] := by
    obtain ⟨hi, e⟩ := v3_get hR hq
    rw [e]; congr 1; simp only [hRq]; exact hBk
  refine ⟨q, by rw [hσ b hb]; exact hlab, ?_⟩
  unfold keptOk
  rw [Array.getElem?_eq_getElem hb]
  simp only [hq3]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨hpar, hargs⟩, hsz⟩, hpop⟩, ?_⟩, ?_⟩
  · unfold lastOk
    rw [ht, ht']
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    exact hsame
  · obtain ⟨t0, sb, ht0, -, hsb, hsbz, hl0⟩ := cs0.blk b _ (Array.getElem?_eq_getElem hb)
    rw [ht] at ht0; cases ht0
    obtain ⟨t3, sb', ht3, -, hsb', hsbz', hl3⟩ := cs3.blk q _ hq3
    rw [ht'] at ht3; cases ht3
    rw [hsb, hsb']
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨by rw [hsbz, hsbz', hlen], ?_⟩
    rw [List.all_eq_true]
    intro j hj
    rw [List.mem_range] at hj
    obtain ⟨l, hlj⟩ : ∃ l, t.targets[j]? = some l :=
      ⟨_, List.getElem?_eq_getElem (by rw [← hsbz]; exact hj)⟩
    obtain ⟨l', hlj'⟩ : ∃ l', t'.targets[j]? = some l' :=
      ⟨_, List.getElem?_eq_getElem (by rw [hlen, ← hsbz]; exact hj)⟩
    obtain ⟨s, hs, hls⟩ := hl0 j l hlj
    obtain ⟨u, hu, hlu⟩ := hl3 j l' hlj'
    rw [hs, hu]
    simp only
    obtain ⟨hs', hls'⟩ := lab_some hls
    rw [hσ s hs', hls']
    obtain ⟨l0, hl0', hcase⟩ := hrel j l' hlj'
    rw [hlj] at hl0'; cases hl0'
    rcases hcase with rfl | ⟨h2, e, he⟩
    · rw [hlu]; simp
    · -- an edge block
      obtain ⟨hu3, hiu, eu, hlabu⟩ := lab3_inv hR hlu
      have he2 : (B ++ E)[(V1).size + e]? = some { label := l', insts := #[.jump l] } := by
        rw [v2_E hS, he]
      have hiE : (V1).size + e < (B ++ E).size := (Array.getElem?_eq_some_iff.mp he2).1
      have hEe : (B ++ E)[(V1).size + e] = { label := l', insts := #[.jump l] } :=
        Option.some.inj (by rw [← Array.getElem?_eq_getElem hiE, he2])
      have hiu' : (rpo ss2)[u] = (V1).size + e := lbl_inj hn2 hiu hiE (by rw [hlabu, hEe])
      have hV3u : ((rpo ss2).map fun i => (B ++ E)[i]!)[u]? = some { label := l', insts := #[.jump l] } := by
        rw [eu, ← hEe]; congr 1; simp only [hiu']
      obtain ⟨t4, ts4, ht4, -, hts4, hts4z, hl4⟩ := cs3.blk u _ hV3u
      simp only [Array.back?] at ht4
      simp at ht4
      subst ht4
      obtain ⟨w, hw, hlw⟩ := hl4 0 l rfl
      have hts4' : ts4 = #[w] := by
        apply Array.ext
        · simp [hts4z, MInst.targets]
        · intro i h1 h2
          have : i = 0 := by simp [hts4z, MInst.targets] at h1; omega
          subst this
          simp only [Array.getElem?_eq_getElem h1] at hw
          simpa using hw
      rw [hlw]
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      refine .inr ⟨hd.args b _ t (Array.getElem?_eq_getElem hb) ht h2, ?_⟩
      unfold edgeBlockOk
      rw [hV3u]
      simp [hts4, hts4']

omit cs1 in
/-- An instruction property kept back through retargeting and false of `jump`s holds in
`vc` if it holds in `prepare`'s output. -/
theorem any3 (P : MInst → Bool)
    (hP : ∀ i ls i', i.setTargets ls = some i' → P i' = true → P i = true)
    (hJ : ∀ l, P (.jump l) = false)
    (h : (((rpo ss2).map fun i => (B ++ E)[i]!).any fun vb => vb.insts.any P) = true) :
    (vc.blocks.any fun vb => vb.insts.any P) = true := by
  rw [Array.any_eq_true'] at h ⊢
  obtain ⟨vb', hvb', hany⟩ := h
  rw [Array.any_eq_true'] at hany
  obtain ⟨i', hi', hp⟩ := hany
  rcases insts3 hd cs0 cs2 hS (Array.mem_toList_iff.mpr hvb') (Array.mem_toList_iff.mpr hi') with
    ⟨vb, hvb, hi⟩ | ⟨vb, hvb, i, hi, ls, hset⟩ | ⟨l, rfl⟩
  · exact ⟨vb, Array.mem_toList_iff.mp hvb, Array.any_eq_true'.mpr ⟨i', Array.mem_toList_iff.mp hi, hp⟩⟩
  · exact ⟨vb, Array.mem_toList_iff.mp hvb,
      Array.any_eq_true'.mpr ⟨i, Array.mem_toList_iff.mp hi, hP i ls i' hset hp⟩⟩
  · rw [hJ] at hp; cases hp

end main

/-- **Completeness of the `prepare` validator.** On `PrepDomain` VCode, `prepCheck` accepts
every output of `prepare`. -/
theorem prepCheck_complete {vc vcp : VCode} (h : prepare vc = .ok vcp) (hd : PrepDomain vc) :
    prepCheck vc vcp = true := by
  obtain ⟨ss0, ps0, ss1, ps1, ss2, ps2, next, B, E, hc0, hc1, hS, hc2, rfl⟩ := prepare_facts h
  have cs0 := cfg_spec hc0
  have cs1 : CfgSpec (keep vc.blocks (reachable ss0)) ss1 := cfg_spec hc1
  have cs2 : CfgSpec (B ++ E) ss2 := cfg_spec hc2
  obtain ⟨h10, hk0, hl0, hn1, hn2, hR, hRn, hR0, -, -⟩ := facts_basic hd cs0 cs2 hS
  obtain ⟨ss3, ps3, hc3⟩ := cfg3 hd cs0 cs2 hS
  have hs0 : ss0.size ≠ 0 := by rw [cs0.size]; have := hd.nonempty; omega
  obtain ⟨-, -, hlcl, -⟩ := reachable_spec (succsIn_of cs0) hs0
  unfold prepCheck
  rw [hc0, hc3]
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq]
  refine ⟨⟨⟨?_, hl0⟩, ?_⟩, ⟨?_, ?_⟩, trivial⟩
  · -- the entry is its own counterpart
    unfold sigmaOf
    rw [Array.getElem?_eq_getElem hd.nonempty]
    have hR0' : 0 < (rpo ss2).size := (Array.getElem?_eq_some_iff.mp hR0).1
    obtain ⟨hi, e⟩ := v3_get hR hR0'
    have e0 : (rpo ss2)[0] = 0 := by
      have := Array.getElem?_eq_getElem hR0'; rw [hR0] at this; exact (Option.some.inj this).symm
    show lab _ _ = _
    have hsz3 : 0 < ((rpo ss2).map fun i => (B ++ E)[i]!).size := by simpa using hR0'
    apply lab_zero hsz3
    have h3 : ((rpo ss2).map fun i => (B ++ E)[i]!)[0] = (B ++ E)[(rpo ss2)[0]]'hi :=
      Option.some.inj (by rw [← Array.getElem?_eq_getElem hsz3, e])
    rw [h3]
    obtain ⟨hkB, e2⟩ := v2_B hS h10
    have hk2 : 0 < (B ++ E).size := (Array.getElem?_eq_some_iff.mp e2).1
    have h4 : (B ++ E)[(rpo ss2)[0]]'hi = B[0] := by
      simp only [e0]
      exact Option.some.inj (by rw [← Array.getElem?_eq_getElem hk2, e2])
    rw [h4, (rw_fields (hS.rw 0 h10 hkB)).1]
    have := hk0
    rw [Array.getElem?_eq_getElem h10, Array.getElem?_eq_getElem hd.nonempty] at this
    rw [Option.some.inj this]
  · -- every live block
    rw [List.all_eq_true]
    intro b hb
    rw [List.mem_range] at hb
    simp only [Bool.or_eq_true, Bool.not_eq_true']
    by_cases hlb : mk (reachable ss0) b
    · right
      obtain ⟨q, hq, hk⟩ := live_ok hd cs0 cs1 cs2 hS hc3 hb hlb
      rw [hq]
      simp only [Bool.and_eq_true]
      refine ⟨hk, ?_⟩
      have e : ss0[b]?.getD #[] = ss0[b]! := by
        simp only [getElem!_def]; split <;> simp_all <;> rfl
      rw [e, Array.all_eq_true]
      intro i hi
      have hs : (ss0[b]! : Array Nat)[i] ∈ (ss0[b]! : Array Nat).toList := Array.getElem_mem_toList hi
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨cs0.size ▸ succsIn_of cs0 b _ hs, hlcl b hlb _ hs⟩
    · left
      simpa [liveOf, mk] using hlb
  · by_cases ht : vc.hasTryCall = true
    · exact .inl ht
    · right
      cases hv : VCode.hasTryCall { vc with blocks := (rpo ss2).map fun i => (B ++ E)[i]! }
      · rfl
      · refine absurd (any3 hd cs0 cs2 hS (fun i => i matches .tryCall ..) ?_ ?_ hv) ht
        · intro i ls i' hset hp
          obtain ⟨-, -, htry, -⟩ := setTargets_targets hset
          obtain ⟨a, b, rfl⟩ := htry (by cases i' <;> simp_all)
          rfl
        · intro l; rfl
  · by_cases ht : vc.hasTls = true
    · exact .inl ht
    · right
      cases hv : VCode.hasTls { vc with blocks := (rpo ss2).map fun i => (B ++ E)[i]! }
      · rfl
      · refine absurd (any3 hd cs0 cs2 hS (fun i => i matches .elfTlsGetAddr ..) ?_ ?_ hv) ht
        · intro i ls i' hset hp
          obtain ⟨-, -, -, htls⟩ := setTargets_targets hset
          cases i' <;> simp_all
        · intro l; rfl

end Backend.Proof.Prep
