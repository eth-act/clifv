import FV.Concurrency.RealizeCompiled

/-!
# Well-formed executions of one thread with reads (T2k, #311)

`realizes_compiled` holds for every well-formed execution of the realized Arm traces; for its
non-vacuity on code that reads (spill slots, shared memory), one is needed: for one thread whose
steps have at most one event (Arm steps, `ThreadCompose.prun_len`),

* `coL`: coherence, the writes of a location in `PEvLt` order (initial writes first);
* `latestW`: a read reads from the `PEvLt`-latest earlier write of its location (its own last
  write there, or the initial write);
* **`wf_single`**: when every read has some earlier write of its location (e.g. an initial one),
  these relations make a well-formed execution.
-/

namespace Concurrency.RealizeCompiled

open Prog ClifThread ProgE2E ThreadRefine

variable {σ K : Type}

/-- The execution graph's direction and location (the relations play no role in them). -/
abbrev X0 (P : Traces σ K BVal) (locs : List (Nat × Nat)) : Exec PEv :=
  P.exec locs (fun _ _ => False) (fun _ _ => False) (fun _ _ => False)

/-- Coherence: the writes of a location in `PEvLt` order. -/
def coL (P : Traces σ K BVal) (locs : List (Nat × Nat)) (a b : PEv) : Prop :=
  (X0 P locs).dir a = .W ∧ (X0 P locs).dir b = .W ∧ (X0 P locs).loc a = (X0 P locs).loc b ∧
    PEvLt a b

/-- Reads-from: the `PEvLt`-latest earlier write of the read's location. -/
def latestW (P : Traces σ K BVal) (locs : List (Nat × Nat)) (w r : PEv) : Prop :=
  (X0 P locs).dir r = .R ∧ (X0 P locs).dir w = .W ∧ (X0 P locs).loc w = (X0 P locs).loc r ∧
    PEvLt w r ∧ ∀ w', (X0 P locs).dir w' = .W → (X0 P locs).loc w' = (X0 P locs).loc r →
      PEvLt w w' → ¬ PEvLt w' r

theorem pevLt_irrefl (a : PEv) : ¬ PEvLt a a := by
  cases a <;> simp [PEvLt]

theorem pevLt_trans {a b c : PEv} (h1 : PEvLt a b) (h2 : PEvLt b c) : PEvLt a c := by
  cases a <;> cases b <;> cases c <;> simp only [PEvLt] at h1 h2 ⊢ <;> omega

theorem pevLt_total {a b : PEv} (h : a ≠ b) : PEvLt a b ∨ PEvLt b a := by
  cases a <;> cases b <;> simp only [PEvLt, ne_eq, PEv.init.injEq, PEv.thr.injEq,
    reduceCtorEq, not_false_eq_true, true_or, or_true] at h ⊢ <;> omega

/-- The rank of an event of a one-thread trace with at most one event per step. -/
def rank (locs : List (Nat × Nat)) : PEv → Nat
  | .init q => q
  | .thr _ j _ => locs.length + j

section single
variable {P : Traces σ K BVal} {locs : List (Nat × Nat)}

theorem dir_ne_F_valid (hn : P.n = 1) (h1 : ∀ j (h : j < (P.tr 0).length), ((P.tr 0)[j]).length ≤ 1)
    {e : PEv} (he : (X0 P locs).dir e ≠ .F) :
    (∃ q, e = .init q ∧ q < locs.length) ∨ ∃ j, e = .thr 0 j 0 ∧ j < (P.tr 0).length := by
  cases e with
  | init q =>
    left
    refine ⟨q, rfl, ?_⟩
    simp only [X0, Traces.exec] at he
    split at he
    · assumption
    · exact absurd rfl he
  | thr i j k =>
    right
    simp only [X0, Traces.exec] at he
    split at he
    · rename_i x hx
      have hi : i < P.n := by
        refine Classical.byContradiction fun hi => ?_
        rw [ThreadRefine.evAt_thr_ge hi] at hx; cases hx
      rw [ThreadRefine.evAt_thr_lt hi] at hx
      obtain rfl : i = 0 := by omega
      obtain ⟨hj, hk⟩ := evAt_isSome (show (evAt (P.tr 0) (j, k)).isSome by rw [hx]; rfl)
      have := h1 j hj
      exact ⟨j, by rw [show k = 0 by omega], hj⟩
    · exact absurd rfl he

theorem rank_lt (hn : P.n = 1) (h1 : ∀ j (h : j < (P.tr 0).length), ((P.tr 0)[j]).length ≤ 1)
    {a b : PEv} (ha : (X0 P locs).dir a ≠ .F) (hb : (X0 P locs).dir b ≠ .F) (h : PEvLt a b) :
    rank locs a < rank locs b := by
  rcases dir_ne_F_valid hn h1 ha with ⟨q, rfl, hq⟩ | ⟨j, rfl, hj⟩ <;>
  rcases dir_ne_F_valid hn h1 hb with ⟨q', rfl, hq'⟩ | ⟨j', rfl, hj'⟩ <;>
  simp only [PEvLt, rank] at h ⊢ <;> omega

/-- **One thread's traces with reads have a well-formed execution** (module doc). -/
theorem wf_single (hn : P.n = 1)
    (h1 : ∀ j (h : j < (P.tr 0).length), ((P.tr 0)[j]).length ≤ 1)
    (hinit : ∀ r, (X0 P locs).dir r = .R →
      ∃ w, (X0 P locs).dir w = .W ∧ (X0 P locs).loc w = (X0 P locs).loc r ∧ PEvLt w r) :
    (P.exec locs (latestW P locs) (coL P locs) (fun _ _ => False)).Wf where
  po_irrefl a := PEv.po_irrefl a
  po_trans _ _ _ := PEv.po_trans
  po_tid _ _ := PEv.po_tid
  po_total _ _ := PEv.po_total
  rf_dir _ _ h := ⟨h.2.1, h.1⟩
  rf_loc _ _ h := h.2.2.1
  rf_func a a' b h h' := by
    refine Classical.byContradiction fun hne => ?_
    rcases pevLt_total hne with hl | hl
    · exact h.2.2.2.2 a' h'.2.1 h'.2.2.1 hl h'.2.2.2.1
    · exact h'.2.2.2.2 a h.2.1 h.2.2.1 hl h.2.2.2.1
  rf_total b hb := by
    obtain ⟨w, hw, hl, hlt⟩ := hinit b hb
    have hb' : (X0 P locs).dir b = .R := hb
    have hbF : (X0 P locs).dir b ≠ .F := by rw [hb']; decide
    -- the latest candidate, by the rank's distance to the read
    suffices H : ∀ d w, rank locs b - rank locs w = d → (X0 P locs).dir w = .W →
        (X0 P locs).loc w = (X0 P locs).loc b → PEvLt w b → ∃ a, latestW P locs a b from
      H _ w rfl hw hl hlt
    intro d
    induction d using Nat.strongRecOn with
    | ind d ih =>
      intro w hd hw hl hlt
      by_cases hmax : ∃ w', (X0 P locs).dir w' = .W ∧ (X0 P locs).loc w' = (X0 P locs).loc b ∧
          PEvLt w w' ∧ PEvLt w' b
      case neg => exact ⟨w, hb, hw, hl, hlt, fun w' a1 a2 a3 a4 => hmax ⟨w', a1, a2, a3, a4⟩⟩
      · obtain ⟨w', hw', hl', h1', h2'⟩ := hmax
        have hwF : (X0 P locs).dir w ≠ .F := by rw [hw]; decide
        have hw'F : (X0 P locs).dir w' ≠ .F := by rw [hw']; decide
        have r1 := rank_lt hn h1 hwF hw'F h1'
        have r2 := rank_lt hn h1 hw'F hbF h2'
        exact ih _ (by omega) w' rfl hw' hl' h2'
  co_dir _ _ h := ⟨h.1, h.2.1⟩
  co_loc _ _ h := h.2.2.1
  co_irrefl a h := pevLt_irrefl a h.2.2.2
  co_trans _ _ _ h1 h2 := ⟨h1.1, h2.2.1, h1.2.2.1.trans h2.2.2.1, pevLt_trans h1.2.2.2 h2.2.2.2⟩
  co_total a b ha hb hl hne := by
    rcases pevLt_total hne with h | h
    · exact .inl ⟨ha, hb, hl, h⟩
    · exact .inr ⟨hb, ha, hl.symm, h⟩
  rmw_dir _ _ h := h.elim
  rmw_loc _ _ h := h.elim
  rmw_po _ _ h := h.elim
  rmw_imm _ _ _ h := h.elim

end single

/-! ## Several threads -/

/-- The number of steps of the threads before thread `i`. -/
def offs (P : Traces σ K BVal) (i : Nat) : Nat := ((List.range i).map fun i' => (P.tr i').length).sum

/-- The rank of an event of traces with at most one event per step (threads in order). -/
def rankM (P : Traces σ K BVal) (locs : List (Nat × Nat)) : PEv → Nat
  | .init q => q
  | .thr i j _ => locs.length + offs P i + j

theorem offs_succ (P : Traces σ K BVal) (i : Nat) : offs P (i + 1) = offs P i + (P.tr i).length := by
  simp [offs, List.range_succ]

theorem offs_mono (P : Traces σ K BVal) {i i' : Nat} (h : i ≤ i') : offs P i ≤ offs P i' := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => rw [offs_succ]; omega

section multi
variable {P : Traces σ K BVal} {locs : List (Nat × Nat)}

theorem dir_ne_F_validM
    (h1 : ∀ i < P.n, ∀ j (h : j < (P.tr i).length), ((P.tr i)[j]).length ≤ 1)
    {e : PEv} (he : (X0 P locs).dir e ≠ .F) :
    (∃ q, e = .init q ∧ q < locs.length) ∨
      ∃ i j, e = .thr i j 0 ∧ i < P.n ∧ j < (P.tr i).length := by
  cases e with
  | init q =>
    left
    refine ⟨q, rfl, ?_⟩
    simp only [X0, Traces.exec] at he
    split at he
    · assumption
    · exact absurd rfl he
  | thr i j k =>
    right
    simp only [X0, Traces.exec] at he
    split at he
    · rename_i x hx
      have hi : i < P.n := by
        refine Classical.byContradiction fun hi => ?_
        rw [ThreadRefine.evAt_thr_ge hi] at hx; cases hx
      rw [ThreadRefine.evAt_thr_lt hi] at hx
      obtain ⟨hj, hk⟩ := evAt_isSome (show (evAt (P.tr i) (j, k)).isSome by rw [hx]; rfl)
      have := h1 i hi j hj
      exact ⟨i, j, by rw [show k = 0 by omega], hi, hj⟩
    · exact absurd rfl he

theorem rank_ltM (h1 : ∀ i < P.n, ∀ j (h : j < (P.tr i).length), ((P.tr i)[j]).length ≤ 1)
    {a b : PEv} (ha : (X0 P locs).dir a ≠ .F) (hb : (X0 P locs).dir b ≠ .F) (h : PEvLt a b) :
    rankM P locs a < rankM P locs b := by
  rcases dir_ne_F_validM h1 ha with ⟨q, rfl, hq⟩ | ⟨i, j, rfl, hi, hj⟩ <;>
  rcases dir_ne_F_validM h1 hb with ⟨q', rfl, hq'⟩ | ⟨i', j', rfl, hi', hj'⟩
  · simp only [PEvLt, rankM] at h ⊢; omega
  · simp only [rankM]; omega
  · simp [PEvLt] at h
  · simp only [PEvLt, rankM] at h ⊢
    rcases h with h | ⟨rfl, h | ⟨rfl, h⟩⟩
    · have := offs_mono P (show i + 1 ≤ i' by omega)
      rw [offs_succ] at this
      omega
    · omega
    · omega

/-- **Traces with reads, several threads**: when every step has at most one event and every
read has an earlier write of its location (in `PEvLt` order: the initial writes, then thread
`0`, thread `1`, …), reads from the `PEvLt`-latest earlier write (`latestW`, across threads) and
coherence in `PEvLt` order (`coL`) make a well-formed execution. -/
theorem wf_multi (h1 : ∀ i < P.n, ∀ j (h : j < (P.tr i).length), ((P.tr i)[j]).length ≤ 1)
    (hinit : ∀ r, (X0 P locs).dir r = .R →
      ∃ w, (X0 P locs).dir w = .W ∧ (X0 P locs).loc w = (X0 P locs).loc r ∧ PEvLt w r) :
    (P.exec locs (latestW P locs) (coL P locs) (fun _ _ => False)).Wf where
  po_irrefl a := PEv.po_irrefl a
  po_trans _ _ _ := PEv.po_trans
  po_tid _ _ := PEv.po_tid
  po_total _ _ := PEv.po_total
  rf_dir _ _ h := ⟨h.2.1, h.1⟩
  rf_loc _ _ h := h.2.2.1
  rf_func a a' b h h' := by
    refine Classical.byContradiction fun hne => ?_
    rcases pevLt_total hne with hl | hl
    · exact h.2.2.2.2 a' h'.2.1 h'.2.2.1 hl h'.2.2.2.1
    · exact h'.2.2.2.2 a h.2.1 h.2.2.1 hl h.2.2.2.1
  rf_total b hb := by
    obtain ⟨w, hw, hl, hlt⟩ := hinit b hb
    have hb' : (X0 P locs).dir b = .R := hb
    have hbF : (X0 P locs).dir b ≠ .F := by rw [hb']; decide
    suffices H : ∀ d w, rankM P locs b - rankM P locs w = d → (X0 P locs).dir w = .W →
        (X0 P locs).loc w = (X0 P locs).loc b → PEvLt w b → ∃ a, latestW P locs a b from
      H _ w rfl hw hl hlt
    intro d
    induction d using Nat.strongRecOn with
    | ind d ih =>
      intro w hd hw hl hlt
      by_cases hmax : ∃ w', (X0 P locs).dir w' = .W ∧ (X0 P locs).loc w' = (X0 P locs).loc b ∧
          PEvLt w w' ∧ PEvLt w' b
      case neg => exact ⟨w, hb, hw, hl, hlt, fun w' a1 a2 a3 a4 => hmax ⟨w', a1, a2, a3, a4⟩⟩
      · obtain ⟨w', hw', hl', h1', h2'⟩ := hmax
        have hwF : (X0 P locs).dir w ≠ .F := by rw [hw]; decide
        have hw'F : (X0 P locs).dir w' ≠ .F := by rw [hw']; decide
        have r1 := rank_ltM h1 hwF hw'F h1'
        have r2 := rank_ltM h1 hw'F hbF h2'
        exact ih _ (by omega) w' rfl hw' hl' h2'
  co_dir _ _ h := ⟨h.1, h.2.1⟩
  co_loc _ _ h := h.2.2.1
  co_irrefl a h := pevLt_irrefl a h.2.2.2
  co_trans _ _ _ h1 h2 := ⟨h1.1, h2.2.1, h1.2.2.1.trans h2.2.2.1, pevLt_trans h1.2.2.2 h2.2.2.2⟩
  co_total a b ha hb hl hne := by
    rcases pevLt_total hne with h | h
    · exact .inl ⟨ha, hb, hl, h⟩
    · exact .inr ⟨hb, ha, hl.symm, h⟩
  rmw_dir _ _ h := h.elim
  rmw_loc _ _ h := h.elim
  rmw_po _ _ h := h.elim
  rmw_imm _ _ _ h := h.elim

end multi

/-! ## Witness: a one-thread trace that reads an initial location -/

/-- One thread, one step reading the 8 bytes at `5`. -/
def Pr1 : Traces Unit Unit BVal := ⟨1, fun _ => [[⟨(), .R, 5, 8, []⟩]], fun _ _ => ()⟩

/-- **`wf_single` is not vacuous**: the read of `Pr1` reads from the initial write of `(5, 8)`. -/
theorem wf_single_witness :
    (Pr1.exec [(5, 8)] (latestW Pr1 [(5, 8)]) (coL Pr1 [(5, 8)]) (fun _ _ => False)).Wf ∧
      latestW Pr1 [(5, 8)] (.init 0) (.thr 0 0 0) := by
  have hl : latestW Pr1 [(5, 8)] (.init 0) (.thr 0 0 0) := by
    refine ⟨rfl, rfl, rfl, trivial, fun w' hw _ h1 h2 => ?_⟩
    cases w' with
    | init q => simp only [PEvLt] at h1; simp [X0, Traces.exec] at hw; omega
    | thr i j k => simp only [PEvLt] at h2; omega
  refine ⟨wf_single rfl (fun j h => by simp [Pr1] at h ⊢) fun r hr =>
    ⟨.init 0, rfl, ?_, by
      cases r with
      | init q => simp only [X0, Traces.exec] at hr; split at hr <;> cases hr
      | thr => trivial⟩, hl⟩
  cases r with
  | init q => simp only [X0, Traces.exec] at hr; split at hr <;> cases hr
  | thr i j k =>
    simp only [X0, Traces.exec, Traces.evAt, Pr1] at hr ⊢
    by_cases hi : i < 1
    · rcases j with _ | j <;> rcases k with _ | k <;> simp_all
    · simp_all

end Concurrency.RealizeCompiled
