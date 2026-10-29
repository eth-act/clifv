module

public import FV.Opt.Proof.Dom
public meta import FV.Opt.Cfg

@[expose] public section

/-!
# Completeness of `unreachableOk` (M1)

`Opt.removeUnreachable f` runs the validator `unreachableOk f (removeUnreachableRaw f)` and returns
`f` unchanged when it rejects. This file proves that it never rejects on a function whose block
ids are unique and whose branch targets are blocks of the function (`blocksOkB`, decidable):
`unreachableOk_raw`, hence `removeUnreachable f = removeUnreachableRaw f`
(`removeUnreachable_eq_raw`).

The proof is the correctness of the depth-first search `Cfg.postorder`: its fuel suffices
(a potential that every step lowers: the unvisited blocks' successor lists plus two each, and the
remaining successors of the stack frames), and on termination the visited blocks are exactly the
finished ones, which are closed under successors (`postorder_closed`).
-/

namespace Opt

open Clif

/-! ## Loops with a potential -/

/-- A `forIn` over a list in `Id` whose body keeps `P` and lowers the potential `μ` on every
`yield`, and ends in `Q` on `done`, ends in `Q` when `μ init` is below the list's length. -/
theorem forIn_pot {α σ : Type} (l : List α) (init : σ) (f : α → σ → Id (ForInStep σ))
    (P Q : σ → Prop) (μ : σ → Nat) (h0 : P init) (hlen : μ init < l.length)
    (hf : ∀ a s, P s → match (f a s).run with
      | .done s' => Q s'
      | .yield s' => P s' ∧ μ s' < μ s) :
    Q (forIn l init f).run := by
  induction l generalizing init with
  | nil => simp at hlen
  | cons a as ih =>
    rw [List.forIn_cons]
    have h := hf a init h0
    cases hfa : f a init with
    | done b =>
      rw [hfa] at h
      exact h
    | yield b =>
      rw [hfa] at h
      simp only [Id.run] at h
      simp only [Id.run_bind]
      exact ih b h.1 (by simp at hlen; have := h.2; omega)

/-- `forIn_pot` followed by a continuation. -/
theorem forIn_pot_bind {α σ β : Type} (l : List α) (init : σ) (f : α → σ → Id (ForInStep σ))
    (k : σ → Id β) (P Q : σ → Prop) (R : β → Prop) (μ : σ → Nat) (h0 : P init)
    (hlen : μ init < l.length)
    (hf : ∀ a s, P s → match (f a s).run with
      | .done s' => Q s'
      | .yield s' => P s' ∧ μ s' < μ s)
    (hk : ∀ s, Q s → R (k s).run) :
    R (forIn l init f >>= k).run :=
  hk _ (forIn_pot l init f P Q μ h0 hlen hf)

/-! ## Small list and array facts -/

theorem back?_toList {α : Type} {xs : Array α} {x : α} (h : xs.back? = some x) :
    xs.toList = xs.pop.toList ++ [x] := by
  have hne : xs.size ≠ 0 := by intro h0; simp [Array.back?, h0] at h
  simp only [Array.back?, Array.getElem?_eq_getElem (by omega : xs.size - 1 < xs.size),
    Option.some.injEq] at h
  have hl : xs.toList ≠ [] := by simpa using hne
  rw [Array.toList_pop, ← h]
  conv => lhs; rw [← List.dropLast_concat_getLast hl]
  rw [List.getLast_eq_getElem]
  simp

/-- Changing one entry of a sum over a duplicate-free list. -/
theorem sum_map_update {l : List Nat} (hl : l.Nodup) {g g' : Nat → Nat} {s : Nat} (hs : s ∈ l)
    (heq : ∀ v ∈ l, v ≠ s → g' v = g v) (hs' : g' s = 0) :
    (l.map g').sum + g s = (l.map g).sum := by
  induction l with
  | nil => simp at hs
  | cons a as ih =>
    simp only [List.nodup_cons] at hl
    simp only [List.map_cons, List.sum_cons]
    by_cases has : a = s
    · subst has
      have : as.map g' = as.map g :=
        List.map_congr_left fun v hv => heq v (List.mem_cons_of_mem _ hv) (fun h => hl.1 (h ▸ hv))
      rw [this, hs']; omega
    · have hs2 : s ∈ as := by simpa [Ne.symm has] using hs
      have := ih hl.2 hs2 (fun v hv hne => heq v (List.mem_cons_of_mem _ hv) hne)
      rw [heq a (List.mem_cons_self ..) has]; omega

/-! ## The depth-first search `Cfg.postorder` -/

section Dfs

variable (succs : Array (List Nat))

/-- The DFS state: visited flags, stack of frames (block, successors left), postorder. -/
abbrev DfsSt := Array Bool × Array (Nat × List Nat) × Array Nat

/-- The invariant of the search (`hS`: successors are blocks). -/
structure DfsInv (s : DfsSt) : Prop where
  size : s.1.size = succs.size
  root : s.1[0]! = true
  vis : ∀ v, s.1[v]! = true → v ∈ s.2.2.toList ∨ ∃ fr ∈ s.2.1.toList, fr.1 = v
  frames : ∀ fr ∈ s.2.1.toList, fr.1 < succs.size ∧
    ∃ done, succs[fr.1]! = done ++ fr.2 ∧ ∀ x ∈ done, s.1[x]! = true
  post : ∀ i ∈ s.2.2.toList, i < succs.size ∧ ∀ x ∈ succs[i]!, s.1[x]! = true

/-- Unvisited blocks, each weighing its successor count plus two. -/
def unvis (vis : Array Bool) : Nat :=
  ((List.range succs.size).map fun v => if vis[v]! then 0 else (succs[v]!).length + 2).sum

/-- Frames, each weighing its remaining successors plus one. -/
def frameCost (st : Array (Nat × List Nat)) : Nat := (st.toList.map fun fr => fr.2.length + 1).sum

/-- The potential of the search. -/
def dfsPot (s : DfsSt) : Nat := unvis succs s.1 + frameCost s.2.1

theorem unvis_set {vis : Array Bool} {s : Nat} (hsz : vis.size = succs.size) (hs : s < succs.size)
    (hv : vis[s]! = false) :
    unvis succs (vis.set! s true) + ((succs[s]!).length + 2) = unvis succs vis := by
  unfold unvis
  have hlt : s < vis.size := hsz ▸ hs
  have := sum_map_update (l := List.range succs.size) List.nodup_range
    (g := fun v => if vis[v]! then 0 else (succs[v]!).length + 2)
    (g' := fun v => if (vis.set! s true)[v]! then 0 else (succs[v]!).length + 2)
    (s := s) (List.mem_range.2 hs) ?_ ?_
  · simpa [hv] using this
  · intro v _ hne
    simp [Array.set!_eq_setIfInBounds, getElem!_def, Array.getElem?_setIfInBounds, Ne.symm hne]
  · simp [Array.set!_eq_setIfInBounds, getElem!_def, Array.getElem?_setIfInBounds, hlt]

theorem getElem!_set_true {vis : Array Bool} {s : Nat} (hs : s < vis.size) (v : Nat) :
    (vis.set! s true)[v]! = (v == s || vis[v]!) := by
  by_cases hv : v = s
  · subst hv; simp [Array.set!_eq_setIfInBounds, getElem!_def, Array.getElem?_setIfInBounds, hs]
  · simp [Array.set!_eq_setIfInBounds, getElem!_def, Array.getElem?_setIfInBounds, Ne.symm hv, hv]

theorem frameCost_push (st : Array (Nat × List Nat)) (fr : Nat × List Nat) :
    frameCost (st.push fr) = frameCost st + (fr.2.length + 1) := by
  simp [frameCost]

theorem frameCost_back {st : Array (Nat × List Nat)} {fr : Nat × List Nat}
    (h : st.back? = some fr) : frameCost st = frameCost st.pop + (fr.2.length + 1) := by
  unfold frameCost; rw [back?_toList h]; simp

theorem sum_range_length (succs : Array (List Nat)) :
    ((List.range succs.size).map fun v => (succs[v]!).length).sum =
      Array.foldl (fun x1 x2 => x1 + x2.length) 0 succs := by
  have : (List.range succs.size).map (fun v => (succs[v]!).length) = succs.toList.map (·.length) := by
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    simp at h1
    simp [getElem!_def, h1]
  rw [this, ← Array.foldl_toList]
  generalize succs.toList = l
  suffices ∀ a, a + (l.map (·.length)).sum = l.foldl (fun x1 x2 => x1 + x2.length) a by
    simpa using this 0
  induction l with
  | nil => simp
  | cons x xs ih => intro a; simp only [List.map_cons, List.sum_cons, List.foldl_cons, ← ih]; omega

theorem unvis_le (vis : Array Bool) :
    unvis succs vis ≤ 2 * succs.size + Array.foldl (fun x1 x2 => x1 + x2.length) 0 succs := by
  rw [← sum_range_length]
  unfold unvis
  have : ∀ l : List Nat, (l.map fun v => if vis[v]! then 0 else (succs[v]!).length + 2).sum ≤
      2 * l.length + (l.map fun v => (succs[v]!).length).sum := by
    intro l
    induction l with
    | nil => simp
    | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      cases vis[x]! <;> simp <;> omega
  simpa using this (List.range succs.size)

/-- **The depth-first search is complete**: the entry is finished, and the finished blocks are
closed under successors. -/
theorem postorder_closed (hS : ∀ i < succs.size, ∀ x ∈ succs[i]!, x < succs.size)
    (hn : succs.size ≠ 0) :
    0 ∈ (Cfg.postorder succs).toList ∧ ∀ i ∈ (Cfg.postorder succs).toList,
      i < succs.size ∧ ∀ x ∈ succs[i]!, x ∈ (Cfg.postorder succs).toList := by
  unfold Cfg.postorder
  simp only [beq_iff_eq, hn, ite_false]
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have h0n : 0 < succs.size := Nat.pos_of_ne_zero hn
  refine forIn_pot_bind _ _ _ _ (P := DfsInv succs) (Q := fun s => DfsInv succs s ∧ s.2.1 = #[])
    (R := fun P : Array Nat => 0 ∈ P.toList ∧ ∀ i ∈ P.toList,
      i < succs.size ∧ ∀ x ∈ succs[i]!, x ∈ P.toList)
    (μ := dfsPot succs) ?_ ?_ ?_ ?_
  · -- the initial state
    have hrep : ∀ v : Nat, (Array.replicate succs.size false)[v]! = false := by
      intro v; by_cases h : v < succs.size <;> simp [getElem!_def, h]
    have hlt : 0 < (Array.replicate succs.size false).size := by simp [h0n]
    refine ⟨by simp, ?_, ?_, ?_, ?_⟩
    · simp only [getElem!_set_true hlt]; simp
    · intro v hv
      simp only [getElem!_set_true hlt, hrep, Bool.or_false, beq_iff_eq] at hv
      right; exact ⟨(0, succs[0]!), by simp, hv.symm⟩
    · intro fr hfr
      have : fr = (0, succs[0]!) := by simpa using hfr
      subst this
      exact ⟨h0n, [], by simp, by simp⟩
    · intro i hi; simp at hi
  · -- the fuel suffices
    have hsz : (Array.replicate succs.size false).size = succs.size := by simp
    have hrep : (Array.replicate succs.size false)[0]! = false := by simp [getElem!_def, h0n]
    have h1 := unvis_set succs hsz h0n hrep
    have h2 := unvis_le succs (Array.replicate succs.size false)
    have h3 : frameCost #[(0, succs[0]!)] = (succs[0]!).length + 1 := by simp [frameCost]
    simp only [dfsPot, h3, Std.Legacy.Range.size, List.length_range']
    omega
  · -- one step
    intro a s hs
    obtain ⟨vis, st, post⟩ := s
    obtain ⟨hsize, hroot, hvis, hframes, hpost⟩ := hs
    simp only at hsize hroot hvis hframes hpost
    cases hb : st.back? with
    | none =>
      simp only [Id.run]
      exact ⟨⟨hsize, hroot, hvis, hframes, hpost⟩, Array.back?_eq_none_iff.1 hb⟩
    | some fr =>
      obtain ⟨b, ss⟩ := fr
      have hst := back?_toList hb
      have hfb := hframes (b, ss) (by rw [hst]; simp)
      obtain ⟨hbn, done, hdone, hdv⟩ := hfb
      have hcost := frameCost_back hb
      cases ss with
      | nil =>
        simp only [Id.run]
        refine ⟨⟨hsize, hroot, ?_, ?_, ?_⟩, ?_⟩
        · intro v hv
          rcases hvis v hv with h | ⟨fr, hfr, rfl⟩
          · left; simp [h]
          · rw [hst] at hfr
            simp only [List.mem_append, List.mem_singleton] at hfr
            rcases hfr with h | rfl
            · right; exact ⟨fr, h, rfl⟩
            · left; simp
        · intro fr hfr
          exact hframes fr (by rw [hst]; exact List.mem_append_left _ (by simpa using hfr))
        · intro i hi
          simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hi
          rcases hi with h | rfl
          · exact hpost i h
          · exact ⟨hbn, fun x hx => hdv x (by simpa [hdone] using hx)⟩
        · simp only [dfsPot]; simp at hcost; omega
      | cons x rest =>
        have hxn : x < succs.size := hS b hbn x (by rw [hdone]; simp)
        have hxv : x < vis.size := hsize ▸ hxn
        by_cases hvx : vis[x]! = true
        · simp only [hvx, Bool.not_true, Id.run]
          simp only [Bool.false_eq_true, ite_false]
          refine ⟨⟨hsize, hroot, ?_, ?_, hpost⟩, ?_⟩
          · intro v hv
            rcases hvis v hv with h | ⟨fr, hfr, rfl⟩
            · left; exact h
            · rw [hst] at hfr
              simp only [List.mem_append, List.mem_singleton] at hfr
              right
              rcases hfr with h | rfl
              · exact ⟨fr, by rw [Array.toList_push]; exact List.mem_append_left _ h, rfl⟩
              · exact ⟨(b, rest), by simp, rfl⟩
          · intro fr hfr
            simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hfr
            rcases hfr with h | rfl
            · exact hframes fr (by rw [hst]; exact List.mem_append_left _ h)
            · refine ⟨hbn, done ++ [x], by simp [hdone], ?_⟩
              intro y hy
              simp only [List.mem_append, List.mem_singleton] at hy
              rcases hy with h | rfl
              · exact hdv y h
              · exact hvx
          · simp only [dfsPot, frameCost_push]; simp at hcost; omega
        · have hvf : vis[x]! = false := by simpa using hvx
          simp only [hvf, Bool.not_false, Id.run, ite_true]
          have hset := getElem!_set_true hxv
          have hmono : ∀ y : Nat, vis[y]! = true → (vis.set! x true)[y]! = true := by
            intro y hy; rw [hset]; simp [hy]
          refine ⟨⟨by simp [hsize], hmono 0 hroot, ?_, ?_, ?_⟩, ?_⟩
          · intro v hv
            rw [hset] at hv
            by_cases hvx' : v = x
            · subst hvx'; right; exact ⟨(v, succs[v]!), by simp, rfl⟩
            · simp only [Bool.or_eq_true, beq_iff_eq, hvx', false_or] at hv
              rcases hvis v hv with h | ⟨fr, hfr, rfl⟩
              · left; exact h
              · rw [hst] at hfr
                simp only [List.mem_append, List.mem_singleton] at hfr
                right
                rcases hfr with h | rfl
                · exact ⟨fr, by
                    simp only [Array.toList_push]
                    exact List.mem_append_left _ (List.mem_append_left _ h), rfl⟩
                · exact ⟨(b, rest), by simp, rfl⟩
          · intro fr hfr
            simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hfr
            rcases hfr with (h | rfl) | rfl
            · obtain ⟨h1, d, hd, hdv'⟩ := hframes fr (by rw [hst]; exact List.mem_append_left _ h)
              exact ⟨h1, d, hd, fun y hy => hmono y (hdv' y hy)⟩
            · refine ⟨hbn, done ++ [x], by simp [hdone], ?_⟩
              intro y hy
              simp only [List.mem_append, List.mem_singleton] at hy
              rcases hy with h | rfl
              · exact hmono y (hdv y h)
              · rw [hset]; simp
            · exact ⟨hxn, [], by simp, by simp⟩
          · intro i hi
            obtain ⟨h1, h2⟩ := hpost i hi
            exact ⟨h1, fun y hy => hmono y (h2 y hy)⟩
          · have hu := unvis_set succs hsize hxn hvf
            simp only [dfsPot, frameCost_push]; simp at hcost; omega
  · -- the end: the stack is empty
    rintro ⟨vis, st, post⟩ ⟨⟨hsize, hroot, hvis, hframes, hpost⟩, hst⟩
    simp only at hst hvis hpost hroot
    subst hst
    have hin : ∀ v, vis[v]! = true → v ∈ post.toList := by
      intro v hv
      rcases hvis v hv with h | ⟨fr, hfr, _⟩
      · exact h
      · simp at hfr
    simp only [Id.run, pure]
    exact ⟨hin 0 hroot, fun i hi => ⟨(hpost i hi).1, fun x hx => hin x ((hpost i hi).2 x hx)⟩⟩

end Dfs

/-! ## `Cfg.build`: the block index, successors and reachability -/

/-- The first-occurrence fold that builds `Cfg.index`. -/
theorem index_fold_get (l : List (BlockId × Nat)) (m : Std.HashMap BlockId Nat) (id : BlockId) :
    (l.foldl (fun m (x : BlockId × Nat) => if m.contains x.1 then m else m.insert x.1 x.2) m)[id]? =
      (m[id]?).or ((l.find? (·.1 == id)).map (·.2)) := by
  induction l generalizing m with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨b, i⟩ := x
    simp only [List.foldl_cons]
    rw [ih]
    by_cases hc : m.contains b = true
    · simp only [hc, ite_true]
      by_cases hb : b = id
      · subst hb
        rw [Std.HashMap.contains_eq_isSome_getElem?] at hc
        obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hc
        simp [hy]
      · simp [List.find?_cons, hb]
    · simp only [hc, Bool.false_eq_true, ite_false, Std.HashMap.getElem?_insert, beq_iff_eq]
      by_cases hb : b = id
      · subst hb
        have : m[b]? = none := by
          rw [Std.HashMap.contains_eq_isSome_getElem?] at hc; simpa using hc
        simp [this]
      · simp [List.find?_cons, hb]

theorem find?_zipIdx_some {l : List BlockId} {k : Nat} {id : BlockId} {p : BlockId × Nat}
    (h : (l.zipIdx k).find? (·.1 == id) = some p) : k ≤ p.2 ∧ l[p.2 - k]? = some id := by
  induction l generalizing k with
  | nil => simp at h
  | cons a as ih =>
    simp only [List.zipIdx_cons, List.find?_cons, beq_iff_eq] at h
    split at h
    · cases h; rename_i ha; simp [beq_iff_eq.1 ha]
    · obtain ⟨h1, h2⟩ := ih h
      refine ⟨by omega, ?_⟩
      have : p.2 - k = (p.2 - (k + 1)) + 1 := by omega
      rw [this, List.getElem?_cons_succ]; exact h2

theorem find?_zipIdx_nodup {l : List BlockId} (hl : l.Nodup) {k j : Nat} {id : BlockId}
    (h : l[j]? = some id) : (l.zipIdx k).find? (·.1 == id) = some (id, j + k) := by
  induction l generalizing k j with
  | nil => simp at h
  | cons a as ih =>
    simp only [List.nodup_cons] at hl
    simp only [List.zipIdx_cons, List.find?_cons, beq_iff_eq]
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h; simp
    | succ j =>
      simp only [List.getElem?_cons_succ] at h
      have hne : a ≠ id := fun he => hl.1 (he ▸ List.mem_of_getElem? h)
      have := ih (k := k + 1) hl.2 h
      have hb : (a == id) = false := by simpa using hne
      simp only [this, hb]
      congr 2; omega

/-- The block ids of `f` in layout order. -/
def blockIds (f : Function) : List BlockId := f.blocks.map (·.id)

theorem build_index_get (f : Function) (id : BlockId) :
    (Cfg.build f).index[id]? =
      ((blockIds f).zipIdx.find? (·.1 == id)).map (·.2) := by
  show (Array.foldl _ ∅ (Array.map (fun x => x.id) f.blocks.toArray).zipIdx)[id]? = _
  rw [← Array.foldl_toList, Array.toList_zipIdx]
  rw [index_fold_get]
  simp [blockIds]

theorem build_index_lt {f : Function} {id : BlockId} {j : Nat}
    (h : (Cfg.build f).index[id]? = some j) : j < f.blocks.length ∧ (blockIds f)[j]? = some id := by
  rw [build_index_get] at h
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.1 h
  have := find?_zipIdx_some (k := 0) hp
  simp only [Nat.sub_zero] at this
  refine ⟨?_, this.2⟩
  have := (List.getElem?_eq_some_iff.1 this.2).1
  simpa [blockIds] using this

theorem build_index_of_nodup {f : Function} (hn : (blockIds f).Nodup) {id : BlockId} {j : Nat}
    (h : (blockIds f)[j]? = some id) : (Cfg.build f).index[id]? = some j := by
  rw [build_index_get, find?_zipIdx_nodup hn h]; simp

theorem build_succs (f : Function) :
    (Cfg.build f).succs = f.blocks.toArray.map fun b =>
      ((termSuccs b.term).filterMap (Cfg.build f).index.get?).eraseDups := rfl

theorem build_rpo (f : Function) : (Cfg.build f).rpo = (Cfg.postorder (Cfg.build f).succs).reverse :=
  rfl

/-- The `rpoNum` fold. -/
theorem rpoNum_fold (l : List (Nat × Nat)) (r : Array (Option Nat)) (i : Nat) (hi : i < r.size) :
    ((l.foldl (fun r (x : Nat × Nat) => r.set! x.1 (some x.2)) r)[i]?.join).isSome ↔
      (r[i]?.join).isSome ∨ i ∈ l.map (·.1) := by
  induction l generalizing r with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.map_cons, List.mem_cons]
    rw [ih _ (by simpa using hi)]
    by_cases hx : x.1 = i
    · subst hx; simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, hi]
    · simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, Ne.symm hx, hx]

theorem build_rpoNum (f : Function) :
    (Cfg.build f).rpoNum = (Cfg.build f).rpo.zipIdx.foldl
      (fun r (x : Nat × Nat) => r.set! x.1 (some x.2)) (Array.replicate f.blocks.length none) := by
  unfold Cfg.build
  simp only [Id.run_bind, Array.forIn_pure_yield_eq_foldl, Id.run_pure]
  simp

theorem build_reachable_iff (f : Function) {i : Nat} (hi : i < f.blocks.length) :
    (Cfg.build f).reachable i = true ↔ i ∈ (Cfg.postorder (Cfg.build f).succs).toList := by
  unfold Cfg.reachable
  rw [build_rpoNum, ← Array.foldl_toList, Array.toList_zipIdx, rpoNum_fold _ _ _ (by simpa using hi)]
  simp [build_rpo, List.zipIdx_map_fst, Array.getElem?_replicate, hi]

/-! ## `unreachableOk` accepts `removeUnreachableRaw` -/

/-- The input condition of `unreachableOk_raw`: block ids are unique and every branch target is a
block of the function. -/
def blocksOkB (f : Function) : Bool :=
  decide (blockIds f).Nodup &&
    f.blocks.all fun b => (termSuccs b.term).all fun id => (blockIds f).contains id

theorem mem_raw {f : Function} {b : Block} :
    b ∈ (removeUnreachableRaw f).blocks ↔ ∃ i, f.blocks[i]? = some b ∧ (Cfg.build f).reachable i := by
  simp only [removeUnreachableRaw, List.mem_map, List.mem_filter, List.mem_zipIdx_iff_getElem?]
  constructor
  · rintro ⟨⟨b', i⟩, ⟨h1, h2⟩, rfl⟩; exact ⟨i, h1, h2⟩
  · rintro ⟨i, h1, h2⟩; exact ⟨(b, i), ⟨h1, h2⟩, rfl⟩

theorem raw_sublist (f : Function) : (removeUnreachableRaw f).blocks.Sublist f.blocks := by
  have := (List.filter_sublist (p := fun x : Block × Nat => (Cfg.build f).reachable x.2)
    (l := f.blocks.zipIdx)).map Prod.fst
  simpa [removeUnreachableRaw, List.zipIdx_map_fst] using this

theorem find?_id_nodup {l : List Block} (hn : (l.map (·.id)).Nodup) {b : Block} (hb : b ∈ l) :
    l.find? (·.id == b.id) = some b := by
  induction l with
  | nil => simp at hb
  | cons c cs ih =>
    simp only [List.map_cons, List.nodup_cons] at hn
    simp only [List.mem_cons] at hb
    rw [List.find?_cons]
    rcases hb with rfl | hb
    · simp
    · by_cases hc : c.id = b.id
      · exact absurd (hc ▸ List.mem_map_of_mem hb) hn.1
      · have : (c.id == b.id) = false := by simpa using hc
        simp only [this]; exact ih hn.2 hb

/-- **`unreachableOk` is complete** on functions with unique block ids whose branch targets are
blocks (`blocksOkB`): it accepts the blocks `removeUnreachableRaw` keeps. -/
theorem unreachableOk_raw {f : Function} (h : blocksOkB f = true) :
    unreachableOk f (removeUnreachableRaw f) = true := by
  simp only [blocksOkB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.contains_iff_mem] at h
  obtain ⟨hn, ht⟩ := h
  have hsize : (Cfg.build f).succs.size = f.blocks.length := by simp [build_succs]
  have hS : ∀ i < (Cfg.build f).succs.size, ∀ x ∈ (Cfg.build f).succs[i]!,
      x < (Cfg.build f).succs.size := by
    intro i hi x hx
    rw [hsize] at hi ⊢
    rw [build_succs] at hx
    simp only [getElem!_def, Array.getElem?_map, List.getElem?_toArray] at hx
    rw [List.getElem?_eq_getElem hi] at hx
    simp only [Option.map_some] at hx
    have hx := List.mem_eraseDups.1 hx
    obtain ⟨id, _, hid⟩ := List.mem_filterMap.1 hx
    exact (build_index_lt hid).1
  have hgn : ((removeUnreachableRaw f).blocks.map (·.id)).Nodup :=
    ((raw_sublist f).map _).nodup hn
  cases hfb : f.blocks with
  | nil =>
    simp [unreachableOk, sameHeader, removeUnreachableRaw, hfb]
  | cons b0 rest =>
    have hn0 : (Cfg.build f).succs.size ≠ 0 := by simp [hsize, hfb]
    obtain ⟨h0, hcl⟩ := postorder_closed _ hS hn0
    have hr0 : (Cfg.build f).reachable 0 = true :=
      (build_reachable_iff f (by simp [hfb])).2 h0
    simp only [unreachableOk, Bool.and_eq_true, List.all_eq_true, beq_iff_eq]
    refine ⟨⟨by simp [sameHeader, removeUnreachableRaw], ?_⟩, ?_⟩
    · simp only [removeUnreachableRaw]
      rw [hfb]
      simp [List.zipIdx_cons, List.filter_cons, hr0]
    · intro b hb
      obtain ⟨i, hbi, hri⟩ := mem_raw.1 hb
      refine ⟨List.contains_iff_mem.2 ((raw_sublist f).subset hb), ?_⟩
      intro id hid
      have hb' : b ∈ f.blocks := List.mem_of_getElem? hbi
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 (ht b hb' id hid)
      have hidx := build_index_of_nodup hn hj
      have hjn := (build_index_lt hidx).1
      have hin : i < f.blocks.length := (List.getElem?_eq_some_iff.1 hbi).1
      have hiP := (build_reachable_iff f hin).1 hri
      have hjs : j ∈ (Cfg.build f).succs[i]! := by
        rw [build_succs]
        simp only [getElem!_def, Array.getElem?_map, List.getElem?_toArray, hbi, Option.map_some]
        exact List.mem_eraseDups.2 (List.mem_filterMap.2 ⟨id, hid, hidx⟩)
      have hjP := (hcl i hiP).2 j hjs
      have hrj := (build_reachable_iff f hjn).2 hjP
      have hbj : f.blocks[j]? = some f.blocks[j] := List.getElem?_eq_getElem hjn
      have hbjid : f.blocks[j].id = id := by
        simp only [blockIds, List.getElem?_map, hbj, Option.map_some, Option.some.injEq] at hj
        exact hj
      have hjg : f.blocks[j] ∈ (removeUnreachableRaw f).blocks := mem_raw.2 ⟨j, hbj, hrj⟩
      have hg := find?_id_nodup hgn hjg
      have hf := find?_id_nodup hn (List.getElem_mem hjn)
      rw [hbjid] at hg hf
      simp only [Function.block?, hg, hf, Option.isSome_some, and_self]

/-- On such functions `removeUnreachable` never falls back. -/
theorem removeUnreachable_eq_raw {f : Function} (h : blocksOkB f = true) :
    removeUnreachable f = removeUnreachableRaw f := by
  simp [removeUnreachable, unreachableOk_raw h]

theorem nodup_of_getElem?_inj {α : Type} {l : List α}
    (h : ∀ (i j : Nat) (a : α), l[i]? = some a → l[j]? = some a → i = j) : l.Nodup := by
  induction l with
  | nil => simp
  | cons a as ih =>
    refine List.nodup_cons.2 ⟨fun ha => ?_, ih fun i j b hi hj => ?_⟩
    · obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 ha
      exact absurd (h 0 (k + 1) a rfl (by simpa using hk)) (by omega)
    · have := h (i + 1) (j + 1) b (by simpa using hi) (by simpa using hj); omega

/-- The certificate `wfCert` (against any CFG; `check` and `simpOk` run it) implies `blocksOkB`. -/
theorem blocksOkB_of_wfCert {f : Function} {cfg : Cfg} {types : Std.HashMap ValueId Ty}
    (h : wfCert f cfg types = true) : blocksOkB f = true := by
  have hW := wfCert_sound (info := { cfg, types, defBlock := {}, pureDef := {} }) h
  simp only [blocksOkB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.contains_iff_mem]
  refine ⟨nodup_of_getElem?_inj fun i j id hi hj => ?_, fun b hb id hid => ?_⟩
  · simp only [blockIds, List.getElem?_map, Option.map_eq_some_iff] at hi hj
    obtain ⟨b, hb, rfl⟩ := hi
    obtain ⟨b', hb', hid⟩ := hj
    have h1 := hW.ids i b hb
    have h2 := hW.ids j b' hb'
    rw [hid] at h2
    simp only [wfData] at h1 h2
    rw [h1] at h2; exact Option.some.inj h2
  · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hb
    obtain ⟨j, b', -, hb', hid', -⟩ := hW.edges i b hi id hid
    exact List.mem_iff_getElem?.2 ⟨j, by simp [blockIds, hb', hid']⟩

/-- `check` implies `blocksOkB`. -/
theorem blocksOkB_of_check {f : Function} {info : Info} (h : check f = .ok info) :
    blocksOkB f = true := by
  unfold check at h
  cases hc : checkCore f with
  | error e => simp [hc, bind, Except.bind] at h
  | ok i =>
    simp only [hc, bind, Except.bind, ensure, pure, Except.pure] at h
    by_cases hw : wfCert f i.cfg i.types = true
    · exact blocksOkB_of_wfCert hw
    · simp only [hw] at h; cases h

/-! ## Witness -/

namespace CompleteUnreachableWitness

/-- `block0` jumps to `block2`; `block1` is unreachable. -/
def fn : Function where
  name := "w"
  sig := {}
  blocks := [{ id := 0, term := .jump { block := 2 } }, { id := 1, term := .ret [] },
    { id := 2, term := .ret [] }]

theorem blocksOk : blocksOkB fn = true := by decide

/-- Non-vacuity of `unreachableOk_raw` / `removeUnreachable_eq_raw`: the condition holds, and
`removeUnreachable` removes the unreachable `block1` (it does not fall back). -/
theorem witness : unreachableOk fn (removeUnreachableRaw fn) = true ∧
    (removeUnreachable fn).blocks.map (·.id) = [0, 2] := by
  refine ⟨unreachableOk_raw blocksOk, ?_⟩
  rw [removeUnreachable_eq_raw blocksOk]
  native_decide

end CompleteUnreachableWitness

end Opt
