import FV.Concurrency.Interleave
import FV.Concurrency.Program

/-!
# Replay: a sequentially consistent execution of a program is a run of the interleaving machine
(T2e, #303)

`replay`: the threads' steps are executed greedily, always a next step of least *step rank*
`fS` (the largest interleaving rank of the thread's events so far, `rank_on`). Every read then
finds in the memory the value of the write it reads from: that write is executed (it is earlier in
`po ∪ com`), and it is the `co`-latest executed write of the location (a later one would be
`fr`-after the read, so not executed yet). An atomic update's read and write stay together because
every `com` edge out of the read also leaves the write (atomicity). Plan: `docs/plans/atomics.md`
(T2e).
-/

namespace Concurrency.Prog

open Rel

theorem rank_on {E : Type} {r : Rel E} (hr : Acyclic r) (evs : List E) :
    ∃ rank : E → Nat, ∀ a b, a ∈ evs → r a b → rank a < rank b := by
  classical
  refine ⟨fun e => evs.countP (fun y => decide (Relation.TransGen r y e)), ?_⟩
  intro a b ha hab
  refine countP_lt ?_ ⟨a, ha, ?_, ?_⟩
  · intro y _ hy
    simp only [decide_eq_true_eq] at hy ⊢
    exact hy.tail hab
  · simp only [decide_eq_true_eq]; exact .single hab
  · simp only [decide_eq_false_iff_not]; exact hr a

/-! ## Maxima and minima -/

theorem exists_min {α : Type} (Q : α → Prop) (f : α → Nat) :
    ∀ v, (∃ a, Q a ∧ f a = v) → ∃ a, Q a ∧ ∀ b, Q b → f a ≤ f b := by
  intro v
  induction v using Nat.strongRecOn with
  | _ v ih =>
    rintro ⟨a, ha, rfl⟩
    by_cases h : ∃ b, Q b ∧ f b < f a
    · obtain ⟨b, hb, hlt⟩ := h
      exact ih _ hlt ⟨b, hb, rfl⟩
    · exact ⟨a, ha, fun b hb => Nat.le_of_not_lt fun hlt => h ⟨b, hb, hlt⟩⟩

theorem foldl_max_ge (a : Nat) : ∀ l : List Nat, a ≤ l.foldl max a
  | [] => Nat.le_refl _
  | x :: l => Nat.le_trans (Nat.le_max_left a x) (foldl_max_ge _ l)

theorem le_foldl_max : ∀ (l : List Nat) (a x : Nat), x ∈ l → x ≤ l.foldl max a
  | [], _, _, h => absurd h List.not_mem_nil
  | y :: l, a, x, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_trans (Nat.le_max_right a x) (foldl_max_ge _ l)
    · exact le_foldl_max l _ x h

theorem foldl_max_cases : ∀ (l : List Nat) (a : Nat), l.foldl max a = a ∨ l.foldl max a ∈ l
  | [], _ => .inl rfl
  | y :: l, a => by
    rcases foldl_max_cases l (max a y) with h | h
    · simp only [List.foldl_cons, h]
      rcases Nat.le_total a y with h' | h'
      · exact .inr (by rw [Nat.max_eq_right h']; exact List.mem_cons_self)
      · exact .inl (Nat.max_eq_left h')
    · exact .inr (List.mem_cons_of_mem _ h)

variable {K V Mem σ : Type}

/-! ## The events of the traces -/

namespace Traces

variable (P : Traces σ K V) (locs : List (Nat × Nat))

/-- The events of step `j` of thread `i`. -/
def stepEvs (i j : Nat) : List (Ev K V) := (P.tr i)[j]?.getD []

/-- All events of the execution. -/
def events : List PEv :=
  (List.range locs.length).map .init ++
  (List.range P.n).flatMap fun i => (List.range (P.tr i).length).flatMap fun j =>
    (List.range (P.stepEvs i j).length).map (.thr i j)

variable {P locs}

theorem evAt_thr {i j k : Nat} (hi : i < P.n) (hj : j < (P.tr i).length)
    (hk : k < ((P.tr i)[j]).length) : P.evAt (.thr i j k) = some ((P.tr i)[j][k]) := by
  simp [evAt, hi, hj, hk]

theorem evAt_some {i j k : Nat} {e : Ev K V} (h : P.evAt (.thr i j k) = some e) :
    i < P.n ∧ ∃ hj : j < (P.tr i).length, ∃ hk : k < ((P.tr i)[j]).length, (P.tr i)[j][k] = e := by
  simp only [evAt] at h
  split at h
  · rename_i hi
    refine ⟨hi, ?_⟩
    rcases hj : (P.tr i)[j]? with _ | es
    · rw [hj] at h; cases h
    · rw [hj] at h
      simp only [Option.bind_some] at h
      obtain ⟨hj', rfl⟩ := List.getElem?_eq_some_iff.mp hj
      obtain ⟨hk, rfl⟩ := List.getElem?_eq_some_iff.mp h
      exact ⟨hj', hk, rfl⟩
  · cases h

theorem stepEvs_eq {i j : Nat} (hj : j < (P.tr i).length) : P.stepEvs i j = (P.tr i)[j] := by
  simp [stepEvs, hj]

theorem mem_events_init {q : Nat} (hq : q < locs.length) : PEv.init q ∈ P.events locs :=
  List.mem_append_left _ (List.mem_map.mpr ⟨q, List.mem_range.mpr hq, rfl⟩)

theorem mem_events_thr {i j k : Nat} {e : Ev K V} (h : P.evAt (.thr i j k) = some e) :
    PEv.thr i j k ∈ P.events locs := by
  obtain ⟨hi, hj, hk, -⟩ := evAt_some h
  refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi,
    List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj, List.mem_map.mpr ⟨k, ?_, rfl⟩⟩⟩)
  rw [stepEvs_eq hj]; exact List.mem_range.mpr hk

end Traces


/-! ## The events of one step -/

theorem agrees_of {I : MemI Mem V} {M : Mem} : ∀ (es : List (Ev K V)),
    (∀ k (hk : k < es.length), es[k].dir = .R → es[k].val = I.get M es[k].loc es[k].n) →
    (es.length ≤ 1 ∨ ∃ (h : es.length = 2), es[0].dir = .R ∧ es[1].dir = .W) → Agrees I M es
  | [], _, _ => trivial
  | [e], h, _ => ⟨h 0 (by simp), trivial⟩
  | [r, w], h, hs => by
    rcases hs with hs | ⟨_, hr, hw⟩
    · simp at hs
    · refine ⟨h 0 (by simp), ?_, trivial⟩
      intro hw'; simp only [List.getElem_cons_succ, List.getElem_cons_zero] at hw; rw [hw] at hw'
      cases hw'
  | _ :: _ :: _ :: _, _, hs => by
    rcases hs with hs | ⟨hs, -⟩ <;> simp at hs

theorem applyEvs_cases {I : MemI Mem V} {M : Mem} : ∀ (es : List (Ev K V)),
    (es.length ≤ 1 ∨ ∃ (h : es.length = 2), es[0].dir = .R ∧ es[1].dir = .W) →
    (applyEvs I M es = M ∧ ∀ k (hk : k < es.length), es[k].dir ≠ .W) ∨
    ∃ k, ∃ hk : k < es.length, es[k].dir = .W ∧ (∀ k' (hk' : k' < es.length), k' ≠ k → es[k'].dir ≠ .W) ∧
      applyEvs I M es = I.put M es[k].loc es[k].n es[k].val
  | [], _ => .inl ⟨rfl, fun _ hk => absurd hk (Nat.not_lt_zero _)⟩
  | [e], _ => by
    by_cases he : e.dir = .W
    · refine .inr ⟨0, by simp, he, fun k' hk' hne => by simp at hk'; omega, ?_⟩
      simp [applyEvs, write1, he]
    · refine .inl ⟨by simp [applyEvs, write1, he], fun k hk => ?_⟩
      simp at hk; subst hk; exact he
  | [r, w], hs => by
    rcases hs with hs | ⟨_, hr, hw⟩
    · simp at hs
    · simp only [List.getElem_cons_succ, List.getElem_cons_zero] at hr hw
      refine .inr ⟨1, by simp, hw, fun k' hk' hne => ?_, ?_⟩
      · simp at hk'
        have : k' = 0 := by omega
        subst this; simp only [List.getElem_cons_zero]; rw [hr]; decide
      · simp [applyEvs, write1, hr, hw]
  | _ :: _ :: _ :: _, hs => by
    rcases hs with hs | ⟨hs, -⟩ <;> simp at hs

/-! ## Replay -/

section replay

variable (I : MemI Mem V) (T : TSem σ K V) (P : Traces σ K V) (locs : List (Nat × Nat))
  (rf co rmw : Rel PEv) (M0 : Mem) (v0 : V)

theorem MRun.head {I : MemI Mem V} {T : TSem σ K V} {c c' c'' : (Nat → σ) × Mem}
    (h1 : MStep I T c c') (h2 : MRun I T c' c'') : MRun I T c c'' := by
  induction h2 with
  | refl => exact .tail .refl h1
  | tail _ h ih => exact .tail ih h

/-- The number of steps of threads `< m` not yet executed at the cut `c`. -/
def rem (P : Traces σ K V) (c : Nat → Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => rem P c m + ((P.tr m).length - c m)

theorem rem_upd (c : Nat → Nat) {i0 : Nat} (hc : c i0 < (P.tr i0).length) :
    ∀ m, i0 < m → rem P (fun i => if i = i0 then c i0 + 1 else c i) m + 1 = rem P c m
  | 0, h => absurd h (Nat.not_lt_zero _)
  | m + 1, h => by
    simp only [rem]
    by_cases hm : m = i0
    · subst hm
      have : rem P (fun i => if i = m then c m + 1 else c i) m = rem P c m := rem_eq m (fun i hi => by
        simp [Nat.ne_of_lt hi])
      simp only [this, ite_true]; omega
    · have := rem_upd c hc m (by omega)
      simp only [hm, ite_false]; omega
where
  rem_eq (m : Nat) {c c' : Nat → Nat} (h : ∀ i < m, c' i = c i) : rem P c' m = rem P c m := by
    induction m with
    | zero => rfl
    | succ m ih =>
      simp only [rem, ih (fun i hi => h i (by omega)), h m (by omega)]

theorem rem_zero {c : Nat → Nat} : ∀ m, rem P c m = 0 → ∀ i < m, (P.tr i).length ≤ c i
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | m + 1, h, i, hi => by
    simp only [rem] at h
    by_cases him : i = m
    · rw [him]; omega
    · exact rem_zero m (by omega) i (by omega)

theorem rem_pos {c : Nat → Nat} : ∀ m, rem P c m ≠ 0 → ∃ i < m, c i < (P.tr i).length
  | 0, h => absurd rfl h
  | m + 1, h => by
    simp only [rem] at h
    by_cases h' : c m < (P.tr m).length
    · exact ⟨m, by omega, h'⟩
    · have h0 : (P.tr m).length - c m = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_lt h')
      rw [h0, Nat.add_zero] at h
      obtain ⟨i, hi, hc⟩ := rem_pos m h
      exact ⟨i, by omega, hc⟩

/-- The largest interleaving rank of the events of step `j` of thread `i`. -/
def smax (P : Traces σ K V) (rank : PEv → Nat) (i j : Nat) : Nat :=
  ((List.range (P.stepEvs i j).length).map fun k => rank (.thr i j k)).foldl max 0

/-- **The step rank**: the largest interleaving rank of thread `i`'s events up to step `j`. -/
def fS (P : Traces σ K V) (rank : PEv → Nat) (i j : Nat) : Nat :=
  ((List.range (j + 1)).map fun j' => smax P rank i j').foldl max 0

theorem fS_mono (P : Traces σ K V) (rank : PEv → Nat) {i j j' : Nat} (hjj : j ≤ j') :
    fS P rank i j ≤ fS P rank i j' := by
  unfold fS
  rcases foldl_max_cases ((List.range (j + 1)).map fun j' => smax P rank i j') 0 with h | h
  · rw [h]; exact Nat.zero_le _
  · obtain ⟨j'', hj'', e⟩ := List.mem_map.mp h
    rw [← e]
    exact le_foldl_max _ _ _ (List.mem_map.mpr ⟨j'', List.mem_range.mpr
      (by have := List.mem_range.mp hj''; omega), rfl⟩)

theorem le_fS (P : Traces σ K V) (rank : PEv → Nat) {i j k : Nat}
    (hk : k < (P.stepEvs i j).length) : rank (.thr i j k) ≤ fS P rank i j :=
  Nat.le_trans (le_foldl_max _ 0 _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩))
    (le_foldl_max _ 0 _ (List.mem_map.mpr ⟨j, List.mem_range.mpr (by omega), rfl⟩))

theorem fS_cases (P : Traces σ K V) (rank : PEv → Nat) (i j : Nat) : fS P rank i j = 0 ∨
    ∃ j' ≤ j, ∃ k < (P.stepEvs i j').length, fS P rank i j = rank (.thr i j' k) := by
  unfold fS
  rcases foldl_max_cases ((List.range (j + 1)).map fun j' => smax P rank i j') 0 with h | h
  · exact .inl h
  · obtain ⟨j', hj', e⟩ := List.mem_map.mp h
    rw [← e]
    rcases foldl_max_cases ((List.range (P.stepEvs i j').length).map
        fun k => rank (.thr i j' k)) 0 with h' | h'
    · left; exact h'
    · obtain ⟨k, hk, e'⟩ := List.mem_map.mp h'
      right
      exact ⟨j', by have := List.mem_range.mp hj'; omega, k, List.mem_range.mp hk, e'.symm⟩

/-- Executed at the cut `c`: the initial writes, and the steps of each thread before `c`. -/
def Exd (c : Nat → Nat) : PEv → Prop
  | .init _ => True
  | .thr i j _ => j < c i

/-- The premises of `replay`. -/
structure ReplayHyp (I : MemI Mem V) (T : TSem σ K V) (P : Traces σ K V) (locs : List (Nat × Nat))
    (rf co rmw : Rel PEv) (M0 : Mem) (v0 : V) : Prop where
  runs : P.Runs T
  wf : (P.exec locs rf co rmw).Wf
  sc : (P.exec locs rf co rmw).SC
  atom : ∀ a b, rmw a b → ¬ ∃ c, (P.exec locs rf co rmw).fr a c ∧ co c b
  val : ∀ w r, rf w r → P.val I M0 locs v0 w = P.val I M0 locs v0 r
  shape : P.StepShape rmw
  ov : NoOverlap (P.exec locs rf co rmw) (P.sz locs)
  init : InitFirst (P.exec locs rf co rmw)
  /-- the threads' writes write values of their size -/
  wok : ∀ i j k x, P.evAt (.thr i j k) = some x → x.dir = .W → I.ok x.n x.val

section facts

variable {I : MemI Mem V} {T : TSem σ K V} {P : Traces σ K V} {locs : List (Nat × Nat)}
  {rf co rmw : Rel PEv} {M0 : Mem} {v0 : V}

theorem exec_thr {i j k : Nat} {x : Ev K V} (h : P.evAt (.thr i j k) = some x) :
    (P.exec locs rf co rmw).dir (.thr i j k) = x.dir ∧ (P.exec locs rf co rmw).loc (.thr i j k) = x.loc ∧
      P.sz locs (.thr i j k) = x.n ∧ P.val I M0 locs v0 (.thr i j k) = x.val := by
  simp [Traces.exec, Traces.sz, Traces.val, h]

theorem exec_thr_none {i j k : Nat} (h : P.evAt (.thr i j k) = none) :
    (P.exec locs rf co rmw).dir (.thr i j k) = .F := by
  simp [Traces.exec, h]

theorem mem_events_of_dir {e : PEv} (h : (P.exec locs rf co rmw).dir e ≠ .F) :
    e ∈ P.events locs := by
  cases e with
  | init q =>
    by_cases hq : q < locs.length
    · exact Traces.mem_events_init hq
    · simp [Traces.exec, hq] at h
  | thr i j k =>
    rcases hx : P.evAt (.thr i j k) with _ | x
    · exact absurd (exec_thr_none (locs := locs) (rf := rf) (co := co) (rmw := rmw) hx) h
    · exact Traces.mem_events_thr hx

theorem po_thr {i j k i' j' k' : Nat} :
    (P.exec locs rf co rmw).po (.thr i j k) (.thr i' j' k') ↔ i = i' ∧ (j < j' ∨ (j = j' ∧ k < k')) :=
  Iff.rfl

theorem tid_thr {i j k : Nat} : (P.exec locs rf co rmw).tid (.thr i j k) = i + 1 := rfl

theorem tid_init {q : Nat} : (P.exec locs rf co rmw).tid (.init q) = 0 := rfl

end facts

section inv

variable (I : MemI Mem V) (P : Traces σ K V) (locs : List (Nat × Nat)) (rf co rmw : Rel PEv)
  (M0 : Mem) (v0 : V) (rank : PEv → Nat)

/-- The memory holds, at every location, the value of the `co`-latest executed write. -/
def Inv (c : Nat → Nat) (M : Mem) : Prop :=
  ∀ w, (P.exec locs rf co rmw).dir w = .W → Exd c w →
    (∀ w', (P.exec locs rf co rmw).dir w' = .W → Exd c w' →
      (P.exec locs rf co rmw).loc w' = (P.exec locs rf co rmw).loc w → w' ≠ w → co w' w) →
    I.get M ((P.exec locs rf co rmw).loc w) (P.sz locs w) = P.val I M0 locs v0 w

/-- Executed steps have step ranks at most those of the other threads' unexecuted steps. -/
def Closed (c : Nat → Nat) : Prop :=
  ∀ i j i' j', i < P.n → i' < P.n → i ≠ i' → j < c i → c i' ≤ j' → j' < (P.tr i').length →
    fS P rank i j ≤ fS P rank i' j'

end inv

section main

variable {I : MemI Mem V} {T : TSem σ K V} {P : Traces σ K V} {locs : List (Nat × Nat)}
  {rf co rmw : Rel PEv} {M0 : Mem} {v0 : V}
  (H : ReplayHyp I T P locs rf co rmw M0 v0) {rank : PEv → Nat}
  (hrank : ∀ a b, a ∈ P.events locs → union (P.exec locs rf co rmw).po (P.exec locs rf co rmw).com a b →
    rank a < rank b)
include H hrank

omit hrank in
/-- `po ∪ com` cycles of length two are impossible. -/
theorem no_back {a b : PEv} (h1 : union (P.exec locs rf co rmw).po (P.exec locs rf co rmw).com a b)
    (h2 : union (P.exec locs rf co rmw).po (P.exec locs rf co rmw).com b a) : False :=
  H.sc a (.tail (.single h1) h2)

/-- **A `com` edge out of thread `i`'s step `j` to another thread rises above its step rank.** -/
theorem fS_lt {i j k : Nat} {x : Ev K V} (hx : P.evAt (.thr i j k) = some x) {b : PEv}
    (hc : (P.exec locs rf co rmw).com (.thr i j k) b)
    (ht : (P.exec locs rf co rmw).tid (.thr i j k) ≠ (P.exec locs rf co rmw).tid b) :
    fS P rank i j < rank b := by
  have hab : rank (.thr i j k) < rank b := hrank _ _ (Traces.mem_events_thr hx) (.inr hc)
  obtain ⟨hi, hj, hk, -⟩ := Traces.evAt_some hx
  rcases fS_cases P rank i j with h | ⟨j', hj', k', hk', h⟩
  · rw [h]; omega
  · rw [h]
    have hx' : (P.evAt (.thr i j' k')).isSome := by
      rw [Traces.stepEvs_eq (by omega)] at hk'
      rw [Traces.evAt_thr hi (by omega) hk']; rfl
    obtain ⟨x', hx''⟩ := Option.isSome_iff_exists.mp hx'
    by_cases hle : j' < j ∨ (j' = j ∧ k' ≤ k)
    · rcases hle with hle | ⟨rfl, hle⟩
      · exact Nat.lt_trans (hrank _ _ (Traces.mem_events_thr hx'') (.inl
          (po_thr.mpr ⟨rfl, .inl hle⟩ : (P.exec locs rf co rmw).po (.thr i j' k') (.thr i j k)))) hab
      · rcases Nat.lt_or_eq_of_le hle with hle | rfl
        · exact Nat.lt_trans (hrank _ _ (Traces.mem_events_thr hx'') (.inl
            (po_thr.mpr ⟨rfl, .inr ⟨rfl, hle⟩⟩ : (P.exec locs rf co rmw).po (.thr i j' k') (.thr i j' k)))) hab
        · exact hab
    · -- the step is an atomic update: `k = 0` its read, `k' = 1` its write
      have hj'j : j' = j := by omega
      subst hj'j
      have hkk : k < k' := by omega
      rcases H.shape.1 i hi j' hj with h1 | ⟨h2, hrmw⟩
      · rw [Traces.stepEvs_eq hj] at hk'; omega
      · rw [Traces.stepEvs_eq hj] at hk'
        have hk0 : k = 0 := by omega
        have hk1 : k' = 1 := by omega
        subst hk0; subst hk1
        have hd := H.wf.rmw_dir _ _ hrmw
        have hl := H.wf.rmw_loc _ _ hrmw
        -- `com` from a read is `fr`
        rcases hc with hc | hc | hc
        · have := (H.wf.rf_dir _ _ hc).1; rw [hd.1] at this; cases this
        · have := (H.wf.co_dir _ _ hc).1; rw [hd.1] at this; cases this
        · have hbW := (H.wf.fr_dir hc).2
          have hbl := H.wf.fr_loc hc
          have hne : (PEv.thr i j' 1) ≠ b := by
            rintro rfl; exact ht rfl
          rcases H.wf.co_total _ _ hd.2 hbW (hl.symm.trans hbl) hne with h' | h'
          · exact hrank _ _ (Traces.mem_events_thr hx'') (.inr (.inr (.inl h')))
          · exact absurd ⟨b, hc, h'⟩ (H.atom _ _ hrmw)

/-- **The read of the next step finds its write's value in the memory.** -/
theorem read_src {c : Nat → Nat} {M : Mem} (hinv : Inv I P locs rf co rmw M0 v0 c M)
    (hcl : Closed P rank c) {i0 : Nat} (hi0 : i0 < P.n) (hj0 : c i0 < (P.tr i0).length)
    (hmin : ∀ i < P.n, c i < (P.tr i).length → fS P rank i0 (c i0) ≤ fS P rank i (c i))
    {k : Nat} {x : Ev K V} (hx : P.evAt (.thr i0 (c i0) k) = some x)
    (hr : (P.exec locs rf co rmw).dir (.thr i0 (c i0) k) = .R) :
    I.get M ((P.exec locs rf co rmw).loc (.thr i0 (c i0) k)) (P.sz locs (.thr i0 (c i0) k)) =
      P.val I M0 locs v0 (.thr i0 (c i0) k) := by
  obtain ⟨w, hrf⟩ := H.wf.rf_total _ hr
  have hwW := (H.wf.rf_dir _ _ hrf).1
  -- the write is executed
  have hex : Exd c w := by
    cases w with
    | init q => trivial
    | thr i j k' =>
      show j < c i
      rcases hw : P.evAt (.thr i j k') with _ | y
      · rw [exec_thr_none hw] at hwW; cases hwW
      obtain ⟨hi, hj, -, -⟩ := Traces.evAt_some hw
      by_cases hii : i = i0
      · subst hii
        rcases H.wf.po_total (.thr i j k') (.thr i (c i) k) rfl (by
            intro e; rw [e, hr] at hwW; cases hwW) with h | h
        · rcases (po_thr.mp h).2 with h | ⟨rfl, hk⟩
          · exact h
          · -- an earlier event of the same step is a read's write: impossible by the shape
            exfalso
            rcases H.shape.1 i hi (c i) hj0 with h1 | ⟨h2, hrmw⟩
            · have := (Traces.evAt_some hx).2.2.1; omega
            · have hk1 : k = 1 := by have := (Traces.evAt_some hx).2.2.1; omega
              subst hk1
              have := (H.wf.rmw_dir _ _ hrmw).2; rw [hr] at this; cases this
        · exact absurd (no_back H (.inr (.inl hrf)) (.inl h)) id
      · rcases Nat.lt_or_ge j (c i) with hlt | hnex
        · exact hlt
        exfalso
        have h1 := fS_lt H hrank hw (.inl hrf) (by simp [tid_thr]; omega)
        have h2 := le_fS P rank (i := i0) (j := c i0) (k := k)
          (by rw [Traces.stepEvs_eq hj0]; exact (Traces.evAt_some hx).2.2.1)
        have h3 := hmin i hi (by omega)
        have h4 := fS_mono P rank (i := i) (show c i ≤ j by omega)
        omega
  -- and the `co`-latest executed one
  have hmax : ∀ w', (P.exec locs rf co rmw).dir w' = .W → Exd c w' →
      (P.exec locs rf co rmw).loc w' = (P.exec locs rf co rmw).loc w → w' ≠ w → co w' w := by
    intro w' hw'W hw'ex hl hne
    rcases H.wf.co_total _ _ hw'W hwW hl hne with h | h
    · exact h
    · exfalso
      have hfr : (P.exec locs rf co rmw).fr (.thr i0 (c i0) k) w' := ⟨w, hrf, h⟩
      cases w' with
      | init q => exact H.init w q h
      | thr i j k' =>
        have hj : j < c i := hw'ex
        rcases hw : P.evAt (.thr i j k') with _ | y
        · rw [exec_thr_none hw] at hw'W; cases hw'W
        by_cases hii : i = i0
        · subst hii
          exact no_back H (.inr (.inr (.inr hfr))) (.inl (po_thr.mpr ⟨rfl, .inl hj⟩))
        · obtain ⟨hi, hjl, -, -⟩ := Traces.evAt_some hw
          have h1 := fS_lt H hrank hx (.inr (.inr hfr)) (by simp [tid_thr]; omega)
          have h2 := le_fS P rank (i := i) (j := j) (k := k')
            (by rw [Traces.stepEvs_eq hjl]; exact (Traces.evAt_some hw).2.2.1)
          have h3 := hcl i j i0 (c i0) hi hi0 hii hj (Nat.le_refl _) hj0
          omega
  have hget := hinv w hwW hex hmax
  have hl := H.wf.rf_loc _ _ hrf
  have hsz := (H.ov w _ (by rw [hwW]; decide) (by rw [hr]; decide)).1 hl
  rw [← hl, ← hsz, hget]
  exact H.val _ _ hrf

omit hrank in
/-- The shape of the next step, in the form of `agrees_of`/`applyEvs_cases`. -/
theorem step_shape {i0 : Nat} (hi0 : i0 < P.n) {j : Nat} (hj : j < (P.tr i0).length) :
    ((P.tr i0)[j]).length ≤ 1 ∨ ∃ (h : ((P.tr i0)[j]).length = 2),
      ((P.tr i0)[j])[0].dir = .R ∧ ((P.tr i0)[j])[1].dir = .W := by
  rcases H.shape.1 i0 hi0 j hj with h | ⟨h2, hrmw⟩
  · exact .inl h
  · refine .inr ⟨h2, ?_, ?_⟩
    · have := (H.wf.rmw_dir _ _ hrmw).1
      rwa [(exec_thr (I := I) (M0 := M0) (v0 := v0) (Traces.evAt_thr hi0 hj (by omega))).1] at this
    · have := (H.wf.rmw_dir _ _ hrmw).2
      rwa [(exec_thr (I := I) (M0 := M0) (v0 := v0) (Traces.evAt_thr hi0 hj (by omega))).1] at this

/-- **The next step's reads agree with the memory.** -/
theorem agrees_step {c : Nat → Nat} {M : Mem} (hinv : Inv I P locs rf co rmw M0 v0 c M)
    (hcl : Closed P rank c) {i0 : Nat} (hi0 : i0 < P.n) (hj0 : c i0 < (P.tr i0).length)
    (hmin : ∀ i < P.n, c i < (P.tr i).length → fS P rank i0 (c i0) ≤ fS P rank i (c i)) :
    Agrees I M ((P.tr i0)[c i0]) := by
  refine agrees_of _ (fun k hk hR => ?_) (step_shape H hi0 hj0)
  have hx := Traces.evAt_thr hi0 hj0 hk
  obtain ⟨hd, hl, hs, hv⟩ := exec_thr (I := I) (M0 := M0) (v0 := v0) (locs := locs) (rf := rf)
    (co := co) (rmw := rmw) hx
  have := read_src H hrank hinv hcl hi0 hj0 hmin hx (by rw [hd, hR])
  rw [hl, hs, hv] at this
  exact this.symm

/-- **Executing the next step keeps the memory invariant.** -/
theorem inv_step {c : Nat → Nat} {M : Mem} (hinv : Inv I P locs rf co rmw M0 v0 c M)
    (hcl : Closed P rank c) {i0 : Nat} (hi0 : i0 < P.n) (hj0 : c i0 < (P.tr i0).length) :
    Inv I P locs rf co rmw M0 v0 (fun i => if i = i0 then c i0 + 1 else c i)
      (applyEvs I M ((P.tr i0)[c i0])) := by
  intro w hwW hex' hmax'
  -- executed writes before the step stay executed
  have hsub : ∀ e, Exd c e → Exd (fun i => if i = i0 then c i0 + 1 else c i) e := by
    intro e he
    cases e with
    | init => trivial
    | thr i j k => show j < (if i = i0 then c i0 + 1 else c i); split <;> simp_all [Exd] <;> omega
  -- a write of the step is `co`-after every write executed before
  have hafter : ∀ k (hk : k < ((P.tr i0)[c i0]).length) w0, Exd c w0 →
      co (.thr i0 (c i0) k) w0 → False := by
    intro k hk w0 hw0 hco
    cases w0 with
    | init q => exact H.init _ q hco
    | thr i j k' =>
      have hj : j < c i := hw0
      by_cases hii : i = i0
      · subst hii
        exact no_back H (.inr (.inr (.inl hco))) (.inl (po_thr.mpr ⟨rfl, .inl hj⟩))
      · rcases hw : P.evAt (.thr i j k') with _ | y
        · have := (H.wf.co_dir _ _ hco).2; rw [exec_thr_none hw] at this; cases this
        obtain ⟨hi, hjl, -, -⟩ := Traces.evAt_some hw
        have h1 := fS_lt H hrank (Traces.evAt_thr hi0 hj0 hk) (.inr (.inl hco))
          (by simp [tid_thr]; omega)
        have h2 := le_fS P rank (i := i) (j := j) (k := k')
          (by rw [Traces.stepEvs_eq hjl]; exact (Traces.evAt_some hw).2.2.1)
        have h3 := hcl i j i0 (c i0) hi hi0 hii hj (Nat.le_refl _) hj0
        omega
  by_cases hnew : ∃ k, w = .thr i0 (c i0) k
  · obtain ⟨k, rfl⟩ := hnew
    rcases hx : P.evAt (.thr i0 (c i0) k) with _ | x
    · rw [exec_thr_none hx] at hwW; cases hwW
    obtain ⟨-, hj', hk, hxk⟩ := Traces.evAt_some hx
    obtain ⟨hd, hl, hs, hv⟩ := exec_thr (I := I) (M0 := M0) (v0 := v0) (locs := locs) (rf := rf)
      (co := co) (rmw := rmw) hx
    rcases applyEvs_cases (I := I) (M := M) _ (step_shape H hi0 hj0) with ⟨-, hno⟩ | ⟨kW, hkW, hW, hone, hM⟩
    · exact absurd (by rw [hxk, ← hd]; exact hwW) (hno k hk)
    · have hkk : kW = k := Classical.byContradiction fun hne =>
        hone k hk (Ne.symm hne) (by rw [hxk, ← hd]; exact hwW)
      subst hkk
      rw [hM, hl, hs, hv, ← hxk, I.get_put_same _ _ _ _ (H.wok _ _ _ _ (by rw [← hxk] at hx; exact hx)
        hW)]
  · have hex : Exd c w := by
      cases w with
      | init => trivial
      | thr i j k =>
        have h : j < (if i = i0 then c i0 + 1 else c i) := hex'
        show j < c i
        by_cases hii : i = i0
        · subst hii
          simp only [ite_true] at h
          rcases Nat.lt_or_ge j (c i) with h' | h'
          · exact h'
          · exact absurd ⟨k, by rw [show j = c i by omega]⟩ hnew
        · simpa [hii] using h
    have hget := hinv w hwW hex (fun w' h1 h2 h3 h4 => hmax' w' h1 (hsub _ h2) h3 h4)
    rcases applyEvs_cases (I := I) (M := M) _ (step_shape H hi0 hj0) with ⟨hM, -⟩ | ⟨kW, hkW, hW, -, hM⟩
    · rw [hM]; exact hget
    · rw [hM]
      have hxW := Traces.evAt_thr hi0 hj0 hkW
      obtain ⟨hd, hl, hs, -⟩ := exec_thr (I := I) (M0 := M0) (v0 := v0) (locs := locs) (rf := rf)
        (co := co) (rmw := rmw) hxW
      have hloc : (P.exec locs rf co rmw).loc (.thr i0 (c i0) kW) ≠ (P.exec locs rf co rmw).loc w := by
        intro e
        have hne : PEv.thr i0 (c i0) kW ≠ w := fun e' => hnew ⟨kW, e'.symm⟩
        exact hafter kW hkW w hex (hmax' _ (by rw [hd, hW]) (by
          show c i0 < (if i0 = i0 then c i0 + 1 else c i0); simp) e hne)
      have hov := (H.ov (.thr i0 (c i0) kW) w (by rw [hd, hW]; decide) (by rw [hwW]; decide)).2 hloc
      rw [hl, hs] at hov
      rw [I.get_put_disj _ _ _ _ _ _ hov]
      exact hget

omit H hrank in
/-- **Executing the next step keeps the step ranks closed.** -/
theorem closed_step {c : Nat → Nat} (hcl : Closed P rank c) {i0 : Nat}
    (hmin : ∀ i < P.n, c i < (P.tr i).length → fS P rank i0 (c i0) ≤ fS P rank i (c i)) :
    Closed P rank (fun i => if i = i0 then c i0 + 1 else c i) := by
  intro i j i' j' hi hi' hne hj hj' hj'l
  have hc' : c i' ≤ j' := by
    by_cases h : i' = i0
    · subst h; simp at hj'; omega
    · simpa [h] using hj'
  by_cases hnew : i = i0 ∧ j = c i0
  · obtain ⟨rfl, rfl⟩ := hnew
    have hi'0 : i' ≠ i := Ne.symm hne
    have h1 := hmin i' hi' (by omega)
    exact Nat.le_trans h1 (fS_mono P rank hc')
  · have hj0 : j < c i := by
      by_cases h : i = i0
      · subst h; simp at hj; omega
      · simpa [h] using hj
    exact hcl i j i' j' hi hi' hne hj0 hc' hj'l

/-- The greedy run from a cut to the end. -/
theorem go : ∀ m (c : Nat → Nat) (M : Mem), rem P c P.n = m → (∀ i, P.n ≤ i → c i = 0) →
    (∀ i < P.n, c i ≤ (P.tr i).length) → Inv I P locs rf co rmw M0 v0 c M → Closed P rank c →
    ∃ M', MRun I T (fun i => P.st i (c i), M)
      (fun i => P.st i (if i < P.n then (P.tr i).length else 0), M') ∧
      Inv I P locs rf co rmw M0 v0 (fun i => if i < P.n then (P.tr i).length else 0) M'
  | 0, c, M, hm, hc0, hcl', hinv, _ => by
    have hall := rem_zero P P.n hm
    have hc : c = fun i => if i < P.n then (P.tr i).length else 0 := by
      funext i
      by_cases hi : i < P.n
      · simp only [hi, ite_true, Nat.le_antisymm (hcl' i hi) (hall i hi)]
      · simp only [hi, ite_false, hc0 i (by omega)]
    subst hc
    exact ⟨M, .refl, hinv⟩
  | m + 1, c, M, hm, hc0, hcl', hinv, hcl => by
    classical
    obtain ⟨i1, hi1, hc1⟩ := rem_pos P (c := c) P.n (by rw [hm]; exact Nat.succ_ne_zero m)
    -- the next step of least step rank
    obtain ⟨i0, ⟨hi0, hj0⟩, hmin'⟩ := exists_min (fun i => i < P.n ∧ c i < (P.tr i).length)
      (fun i => fS P rank i (c i)) _ ⟨i1, ⟨hi1, hc1⟩, rfl⟩
    have hmin : ∀ i < P.n, c i < (P.tr i).length → fS P rank i0 (c i0) ≤ fS P rank i (c i) :=
      fun i hi hc => hmin' i ⟨hi, hc⟩
    let c' := fun i => if i = i0 then c i0 + 1 else c i
    have hst : upd (fun i => P.st i (c i)) i0 (P.st i0 (c i0 + 1)) = fun i => P.st i (c' i) := by
      funext i
      simp only [upd, c']
      split <;> simp_all
    have hstep : MStep I T (fun i => P.st i (c i), M)
        (fun i => P.st i (c' i), applyEvs I M ((P.tr i0)[c i0])) := by
      rw [← hst]
      exact .mk (H.runs i0 hi0 (c i0) hj0) (agrees_step H hrank hinv hcl hi0 hj0 hmin)
    have hrem : rem P c' P.n = m := by
      have := rem_upd P c hj0 P.n hi0
      show rem P (fun i => if i = i0 then c i0 + 1 else c i) P.n = m
      omega
    obtain ⟨M', hrun, hinv'⟩ := go m c' _ hrem
      (fun i hi => by simp only [c', show i ≠ i0 by omega, ite_false]; exact hc0 i hi)
      (fun i hi => by simp only [c']; split <;> simp_all <;> omega)
      (inv_step H hrank hinv hcl hi0 hj0) (closed_step hcl hmin)
    exact ⟨M', MRun.head hstep hrun, hinv'⟩

end main

/-- **Replay.** A finite sequentially consistent execution of the program `P` (traces of `T`
from `P.st · 0`, initial memory `M0`), whose reads read their writes' values, whose accesses do
not partially overlap, whose steps are single events or atomic updates, whose writes write values
of their size, and whose initial writes are `co`-first, is a run of the interleaving machine to
the threads' final states; the final memory holds the values of the `co`-last writes. -/
theorem replay (H : ReplayHyp I T P locs rf co rmw M0 v0) :
    ∃ M', MRun I T (fun i => P.st i 0, M0)
      (fun i => P.st i (if i < P.n then (P.tr i).length else 0), M') ∧
      ∀ w, (P.exec locs rf co rmw).dir w = .W →
        (∀ w', (P.exec locs rf co rmw).dir w' = .W →
          (P.exec locs rf co rmw).loc w' = (P.exec locs rf co rmw).loc w → w' ≠ w → co w' w) →
        I.get M' ((P.exec locs rf co rmw).loc w) (P.sz locs w) = P.val I M0 locs v0 w := by
  obtain ⟨rank, hrank⟩ := rank_on H.sc (P.events locs)
  have hI0 : Inv I P locs rf co rmw M0 v0 (fun _ => 0) M0 := by
    intro w hwW hex _
    cases w with
    | init q => rfl
    | thr i j k => exact absurd hex (Nat.not_lt_zero _)
  have hC0 : Closed P rank (fun _ => 0) := by
    intro i j _ _ _ _ _ hj; exact absurd hj (Nat.not_lt_zero _)
  obtain ⟨M', hrun, hinv⟩ := go H hrank _ (fun _ => 0) M0 rfl (fun _ _ => rfl)
    (fun _ _ => Nat.zero_le _) hI0 hC0
  refine ⟨M', hrun, fun w hw hmax => hinv w hw ?_ (fun w' h1 _ h3 h4 => hmax w' h1 h3 h4)⟩
  -- every write is executed at the end
  cases w with
  | init => trivial
  | thr i j k =>
    show j < (if i < P.n then (P.tr i).length else 0)
    rcases hx : P.evAt (.thr i j k) with _ | x
    · rw [exec_thr_none hx] at hw; cases hw
    obtain ⟨hi, hj, -, -⟩ := Traces.evAt_some hx
    simp only [hi, ite_true]; exact hj

end replay

end Concurrency.Prog
