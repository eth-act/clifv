import FV.Backend.LinearScan

/-!
# Segment arrays of the Lean allocator (V4b-3, #275)

The validator and the builder look up segments in arrays sorted by start whose consecutive
segments are disjoint (`SegsOk`): the occupancy of each register (`Plan.occ`) and of each home
(`Plan.homeOcc`). Here: the binary search finds the first segment ending at or after a position
(`firstEndGe_spec`), so `segFree` is sound (`segFree_sound`) and `meetsOther` complete
(`meetsOther_false`); two segments of such an array that share a position are the same
(`SegsOk.unique`); `Plan.occ` (`Plan.homeOcc`) holds exactly the segments of the vregs in each
register (home) (`mem_occ`, `occ_mem`, `mem_homeOcc`, `homeOcc_mem`); `regIdx` is injective.
-/

namespace Backend.Proof.LS

open Backend Backend.LinearScan

/-- Sorted by start, consecutive segments disjoint, each an interval. -/
def SegsOk (a : Array LinearScan.Seg) : Prop := disjointSorted a = true ∧ ∀ g ∈ a.toList, g.s ≤ g.e

/-- Does segment `g` contain position `p`? -/
def _root_.Backend.LinearScan.Seg.has (g : LinearScan.Seg) (p : Nat) : Prop := g.s ≤ p ∧ p ≤ g.e

/-- Consecutive disjointness of intervals gives disjointness of all pairs, in order. -/
private theorem pairwise_of_chain :
    ∀ (l : List LinearScan.Seg), (l.zip l.tail).all (fun (x, y) => decide (x.e < y.s)) = true →
      (∀ g ∈ l, g.s ≤ g.e) → l.Pairwise fun x y => x.e < y.s
  | [], _, _ => .nil
  | [_], _, _ => List.pairwise_singleton _ _
  | x :: y :: rest, h, hse => by
    simp only [List.tail_cons, List.zip_cons_cons, List.all_cons, Bool.and_eq_true,
      decide_eq_true_eq] at h
    have ih := pairwise_of_chain (y :: rest) (by simpa using h.2)
      (fun g hg => hse g (List.mem_cons_of_mem _ hg))
    refine .cons (fun z hz => ?_) ih
    rcases List.mem_cons.mp hz with rfl | hz
    · exact h.1
    · have := List.rel_of_pairwise_cons ih hz
      have := hse y (by simp)
      omega

private theorem SegsOk.pairwise {a : Array LinearScan.Seg} (h : SegsOk a) :
    a.toList.Pairwise fun x y => x.e < y.s :=
  pairwise_of_chain a.toList (by simpa [disjointSorted] using h.1) h.2

/-- Earlier segments end before later ones start. -/
private theorem SegsOk.lt {a : Array LinearScan.Seg} (h : SegsOk a) {i j : Nat} (hij : i < j)
    (hj : j < a.size) : a[i].e < a[j].s := by
  have := List.pairwise_iff_getElem.mp h.pairwise i j (by simp; omega) (by simpa using hj) hij
  simpa using this

private theorem SegsOk.le {a : Array LinearScan.Seg} (h : SegsOk a) {i : Nat} (hi : i < a.size) :
    a[i].s ≤ a[i].e :=
  h.2 _ (by simp)

private theorem SegsOk.e_le {a : Array LinearScan.Seg} (h : SegsOk a) {i j : Nat} (hij : i ≤ j)
    (hj : j < a.size) : a[i].e ≤ a[j].e := by
  rcases Nat.lt_or_eq_of_le hij with hij | rfl
  · have := h.lt hij hj; have := h.le hj; omega
  · exact Nat.le_refl _

private theorem SegsOk.s_le {a : Array LinearScan.Seg} (h : SegsOk a) {i j : Nat} (hij : i ≤ j)
    (hj : j < a.size) : a[i].s ≤ a[j].s := by
  rcases Nat.lt_or_eq_of_le hij with hij | rfl
  · have := h.lt hij hj; have := h.le (i := i) (by omega); omega
  · exact Nat.le_refl _

theorem SegsOk.unique {a : Array LinearScan.Seg} (h : SegsOk a) {g g' : LinearScan.Seg} (hg : g ∈ a.toList)
    (hg' : g' ∈ a.toList) {p : Nat} (h1 : g.has p) (h2 : g'.has p) : g = g' := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg'
  simp only [Array.length_toList] at hi hj
  simp only [Array.getElem_toList, LinearScan.Seg.has] at h1 h2 ⊢
  rcases Nat.lt_trichotomy i j with hij | rfl | hij
  · have := h.lt hij hj; omega
  · rfl
  · have := h.lt hij hi; omega

/-- The binary search: below the result every segment ends before `x`, from it on none does. -/
private theorem firstEndGeIn_spec {a : Array LinearScan.Seg} {x : Nat}
    (hm : ∀ i j (hij : i ≤ j) (hj : j < a.size), a[j].e < x → a[i].e < x) :
    ∀ lo hi, hi ≤ a.size → (∀ i (_ : i < lo) (h : i < a.size), a[i].e < x) →
      (∀ i, hi ≤ i → ∀ (h : i < a.size), x ≤ a[i].e) →
      (∀ i (_ : i < firstEndGeIn a x lo hi) (h : i < a.size), a[i].e < x) ∧
        (∀ i, firstEndGeIn a x lo hi ≤ i → ∀ (h : i < a.size), x ≤ a[i].e)
  | lo, hi, hhi, hlo, hup => by
    rw [firstEndGeIn]
    split
    · rename_i hlh
      have hmid : (lo + hi) / 2 < a.size := by omega
      simp only [getElem!_pos a ((lo + hi) / 2) hmid]
      split
      · rename_i hlt
        exact firstEndGeIn_spec hm ((lo + hi) / 2 + 1) hi hhi
          (fun i hi' h => if hil : i < lo then hlo i hil h else hm i _ (by omega) hmid hlt) hup
      · rename_i hge
        exact firstEndGeIn_spec hm lo ((lo + hi) / 2) (by omega) hlo
          (fun i hi' h => if hih : hi ≤ i then hup i hih h else by
            have := hm _ i hi' h; omega)
    · exact ⟨hlo, fun i hi' h => hup i (by omega) h⟩
termination_by lo hi => hi - lo

private theorem firstEndGe_spec {a : Array LinearScan.Seg} (h : SegsOk a) (x : Nat) :
    (∀ i (_ : i < firstEndGe a x) (h : i < a.size), a[i].e < x) ∧
      (∀ i, firstEndGe a x ≤ i → ∀ (h : i < a.size), x ≤ a[i].e) :=
  firstEndGeIn_spec (fun i j hij hj hlt => Nat.lt_of_le_of_lt (h.e_le hij hj) hlt) 0 a.size
    (Nat.le_refl _) (fun _ h _ => absurd h (Nat.not_lt_zero _)) (fun _ h h' => absurd h' (by omega))

/-- `segFree` is sound: no segment meets `[s, e]`. -/
theorem segFree_sound {a : Array LinearScan.Seg} (h : SegsOk a) {s e : Nat} (hf : segFree a s e = true) :
    ∀ g ∈ a.toList, ∀ p, s ≤ p → p ≤ e → ¬ g.has p := by
  intro g hg p hsp hpe hp
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
  simp only [Array.length_toList] at hj
  simp only [Array.getElem_toList, LinearScan.Seg.has] at hp
  obtain ⟨hlo, -⟩ := firstEndGe_spec h s
  by_cases hjk : j < firstEndGe a s
  · have := hlo j hjk hj; omega
  · have hk : firstEndGe a s < a.size := by omega
    simp only [segFree, Array.getElem?_eq_getElem hk, decide_eq_true_eq] at hf
    have := h.s_le (i := firstEndGe a s) (by omega) hj
    omega

private theorem meetsOtherFrom_false {a : Array LinearScan.Seg} (h : SegsOk a) {s e u : Nat} :
    ∀ i, meetsOtherFrom a s e u i = false → ∀ j, i ≤ j → ∀ (hj : j < a.size), a[j].s ≤ e →
      a[j].v = u ∨ a[j].e < s
  | i, hm, j, hij, hj, hje => by
    rw [meetsOtherFrom] at hm
    split at hm
    · rename_i hi
      split at hm
      · rename_i hie
        simp only [Bool.or_eq_false_iff] at hm
        rcases Nat.lt_or_eq_of_le hij with hij | rfl
        · exact meetsOtherFrom_false h (i + 1) hm.2 j hij hj hje
        · by_cases hv : a[i].v = u
          · exact .inl hv
          · refine .inr (Nat.lt_of_not_le fun hc => ?_)
            have := hm.1
            simp [hv, hc] at this
      · rename_i hie
        have := h.s_le hij hj
        omega
    · omega
termination_by i => a.size - i

/-- `meetsOther` is complete: when it says no, every segment meeting `[s, e]` is owned by `u`. -/
theorem meetsOther_false {a : Array LinearScan.Seg} (h : SegsOk a) {s e u : Nat}
    (hm : meetsOther a s e u = false) : ∀ g ∈ a.toList, ∀ p, s ≤ p → p ≤ e → g.has p → g.v = u := by
  intro g hg p hsp hpe hp
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
  simp only [Array.length_toList] at hj
  simp only [Array.getElem_toList, LinearScan.Seg.has] at hp ⊢
  obtain ⟨hlo, -⟩ := firstEndGe_spec h s
  by_cases hjk : j < firstEndGe a s
  · have := hlo j hjk hj; omega
  · rcases meetsOtherFrom_false h _ hm j (by omega) hj (by omega) with hv | hv
    · exact hv
    · omega

theorem regIdx_inj {r r' : Reg} {i : Nat} (h : regIdx r = some i) (h' : regIdx r' = some i) :
    r = r' := by
  cases r <;> cases r' <;> simp only [regIdx, reduceCtorEq] at h h' <;>
    (split at h <;> split at h') <;> simp_all <;> omega

theorem regIdx_lt {r : Reg} {i : Nat} (h : regIdx r = some i) : i < 64 := by
  cases r <;> simp only [regIdx, reduceCtorEq] at h <;> split at h <;> simp_all <;> omega

/-! ## Folds that prepend segment lists to array entries -/

private theorem getD_modify {α : Type} (a : Array (List α)) (j i : Nat) (f : List α → List α) :
    (a.modify j f).getD i [] = if j = i ∧ i < a.size then f (a.getD i []) else a.getD i [] := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_modify]
  by_cases hji : j = i
  · subst hji
    by_cases hi : j < a.size <;> simp [hi]
  · simp [hji]

/-- A fold that prepends `seg v` to entry `key v` (if any) of an array of lists. -/
private theorem fold_spec (key : Nat → Option Nat) (seg : Nat → List LinearScan.Seg)
    (f : Array (List LinearScan.Seg) → Nat → Array (List LinearScan.Seg))
    (hf : ∀ acc v, f acc v = match key v with
      | some i => acc.modify i (seg v ++ ·)
      | none => acc) :
    ∀ (L : List Nat) (acc : Array (List LinearScan.Seg)), (L.foldl f acc).size = acc.size ∧
      ∀ i x, x ∈ (L.foldl f acc).getD i [] ↔
        x ∈ acc.getD i [] ∨ (i < acc.size ∧ ∃ v ∈ L, key v = some i ∧ x ∈ seg v)
  | [], acc => by simp
  | v :: L, acc => by
    obtain ⟨hsz, hmem⟩ := fold_spec key seg f hf L (f acc v)
    have hsz' : (f acc v).size = acc.size := by
      rw [hf]; split <;> simp
    refine ⟨by simp [hsz, hsz'], fun i x => ?_⟩
    rw [List.foldl_cons, hmem, hsz']
    have hstep : x ∈ (f acc v).getD i [] ↔
        x ∈ acc.getD i [] ∨ (i < acc.size ∧ key v = some i ∧ x ∈ seg v) := by
      rw [hf]
      split
      · rename_i j hj
        rw [getD_modify]
        by_cases hji : j = i ∧ i < acc.size
        · obtain ⟨rfl, hi⟩ := hji
          simp [hi, hj, or_comm]
        · simp only [hji, ↓reduceIte]
          constructor
          · exact .inl
          · rintro (h | ⟨hi, hk, -⟩)
            · exact h
            · exact absurd ⟨Option.some.inj (hj.symm.trans hk), hi⟩ hji
      · rename_i hk
        simp [hk]
    rw [hstep]
    constructor
    · rintro ((h | ⟨hi, hk, hx⟩) | ⟨hi, w, hw, hk, hx⟩)
      · exact .inl h
      · exact .inr ⟨hi, v, List.mem_cons_self .., hk, hx⟩
      · exact .inr ⟨hi, w, List.mem_cons_of_mem _ hw, hk, hx⟩
    · rintro (h | ⟨hi, w, hw, hk, hx⟩)
      · exact .inl (.inl h)
      · rcases List.mem_cons.mp hw with rfl | hw
        · exact .inl (.inr ⟨hi, hk, hx⟩)
        · exact .inr ⟨hi, w, hw, hk, hx⟩

private theorem mem_sortSegs {arr : Array (List LinearScan.Seg)} {i : Nat} {g : LinearScan.Seg} :
    g ∈ ((arr.map sortSegs).getD i #[]).toList ↔ g ∈ arr.getD i [] := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases arr[i]? <;> simp [sortSegs, List.mem_mergeSort]

private theorem getD_replicate_nil {n i : Nat} {x : LinearScan.Seg} :
    x ∉ (Array.replicate n ([] : List LinearScan.Seg)).getD i [] := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
  split <;> simp

private theorem mem_segList {pl : LinearScan.Plan} {v : Nat} {g : LinearScan.Seg} :
    g ∈ pl.segList v ↔ g.v = v ∧ (g.s, g.e) ∈ (pl.segs.getD v #[]).toList := by
  simp only [Plan.segList, List.mem_map]
  constructor
  · rintro ⟨⟨s, e⟩, h, rfl⟩; exact ⟨rfl, h⟩
  · rintro ⟨rfl, h⟩; exact ⟨_, h, rfl⟩

/-- The step of `Plan.occ`'s fold. -/
private def occStep (pl : LinearScan.Plan) (acc : Array (List LinearScan.Seg)) (v : Nat) : Array (List LinearScan.Seg) :=
  match (pl.regOf v).bind regIdx with
  | some i => acc.modify i (pl.segList v ++ ·)
  | none => acc

private theorem occ_eq (pl : LinearScan.Plan) :
    pl.occ = ((List.range pl.reg.size).foldl (occStep pl) (Array.replicate 64 [])).map sortSegs :=
  rfl

private theorem mem_occ_iff {pl : LinearScan.Plan} {i : Nat} {g : LinearScan.Seg} :
    g ∈ (pl.occ.getD i #[]).toList ↔ i < 64 ∧ ∃ v ∈ List.range pl.reg.size,
      (pl.regOf v).bind regIdx = some i ∧ g ∈ pl.segList v := by
  have hf := fold_spec (fun v => (pl.regOf v).bind regIdx) pl.segList (occStep pl)
    (fun _ _ => rfl) (List.range pl.reg.size) (Array.replicate 64 [])
  rw [occ_eq, mem_sortSegs, hf.2 i g, Array.size_replicate]
  exact ⟨fun h => h.resolve_left getD_replicate_nil, .inr⟩

/-- `occ` holds 64 arrays, each the sorted segments of the vregs of one register. -/
theorem occ_size (pl : LinearScan.Plan) : pl.occ.size = 64 := by
  have hf := fold_spec (fun v => (pl.regOf v).bind regIdx) pl.segList (occStep pl)
    (fun _ _ => rfl) (List.range pl.reg.size) (Array.replicate 64 [])
  rw [occ_eq, Array.size_map, hf.1, Array.size_replicate]

private theorem lt_of_regOf {pl : LinearScan.Plan} {v : Nat} {r : Reg} (h : pl.regOf v = some r) :
    v < pl.reg.size := by
  simp only [Plan.regOf, Array.getD_eq_getD_getElem?] at h
  rcases Nat.lt_or_ge v pl.reg.size with hv | hv
  · exact hv
  · rw [Array.getElem?_eq_none hv] at h
    cases h

theorem mem_occ {pl : LinearScan.Plan} {v : Nat} {r : Reg} {i s e : Nat} (hr : pl.regOf v = some r)
    (hi : regIdx r = some i) (hs : (s, e) ∈ (pl.segs.getD v #[]).toList) :
    (⟨s, e, v⟩ : LinearScan.Seg) ∈ (pl.occ.getD i #[]).toList :=
  mem_occ_iff.mpr ⟨regIdx_lt hi, v, List.mem_range.mpr (lt_of_regOf hr), by simp [hr, hi],
    mem_segList.mpr ⟨rfl, hs⟩⟩

theorem occ_mem {pl : LinearScan.Plan} {i : Nat} {g : LinearScan.Seg} (hg : g ∈ (pl.occ.getD i #[]).toList) :
    ∃ r, pl.regOf g.v = some r ∧ regIdx r = some i ∧ (g.s, g.e) ∈ (pl.segs.getD g.v #[]).toList := by
  obtain ⟨-, v, -, hk, hx⟩ := mem_occ_iff.mp hg
  obtain ⟨rfl, hx⟩ := mem_segList.mp hx
  cases hr : pl.regOf g.v with
  | none => rw [hr] at hk; cases hk
  | some r => rw [hr] at hk; exact ⟨r, rfl, hk, hx⟩

/-- The index of the home array of vreg `v`. -/
def homeIdx (fn : Fn) (pl : LinearScan.Plan) (v : Nat) : Nat :=
  2 * pl.home.getD v 0 + (if fn.clsOf v == .float then 1 else 0)

/-- The step of `Plan.homeOcc`'s fold. -/
private def homeStep (fn : Fn) (pl : LinearScan.Plan) (acc : Array (List LinearScan.Seg)) (v : Nat) :
    Array (List LinearScan.Seg) :=
  if (pl.regOf v).isSome then acc else
    acc.modify (2 * pl.home.getD v 0 + (if fn.clsOf v == .float then 1 else 0)) (pl.segList v ++ ·)

private theorem homeOcc_eq (fn : Fn) (pl : LinearScan.Plan) :
    pl.homeOcc fn = ((List.range fn.nv).foldl (homeStep fn pl)
      (Array.replicate (2 * pl.nslots) [])).map sortSegs :=
  rfl

private theorem mem_homeOcc_iff {fn : Fn} {pl : LinearScan.Plan} {i : Nat} {g : LinearScan.Seg} :
    g ∈ ((pl.homeOcc fn).getD i #[]).toList ↔ i < 2 * pl.nslots ∧ ∃ v ∈ List.range fn.nv,
      (if (pl.regOf v).isSome then none else some (homeIdx fn pl v)) = some i ∧
        g ∈ pl.segList v := by
  have hf := fold_spec (fun v => if (pl.regOf v).isSome then none else some (homeIdx fn pl v))
    pl.segList (homeStep fn pl) (fun acc v => by simp only [homeStep]; split <;> rfl)
    (List.range fn.nv) (Array.replicate (2 * pl.nslots) [])
  rw [homeOcc_eq, mem_sortSegs, hf.2 i g, Array.size_replicate]
  exact ⟨fun h => h.resolve_left getD_replicate_nil, .inr⟩

theorem mem_homeOcc {fn : Fn} {pl : LinearScan.Plan} {v s e : Nat} (hv : v < fn.nv) (hr : pl.regOf v = none)
    (hh : pl.home.getD v 0 < pl.nslots) (hs : (s, e) ∈ (pl.segs.getD v #[]).toList) :
    (⟨s, e, v⟩ : LinearScan.Seg) ∈ ((pl.homeOcc fn).getD (homeIdx fn pl v) #[]).toList := by
  refine mem_homeOcc_iff.mpr ⟨?_, v, List.mem_range.mpr hv, by simp [hr],
    mem_segList.mpr ⟨rfl, hs⟩⟩
  simp only [homeIdx]
  split <;> omega

theorem homeOcc_mem {fn : Fn} {pl : LinearScan.Plan} {i : Nat} {g : LinearScan.Seg}
    (hg : g ∈ ((pl.homeOcc fn).getD i #[]).toList) :
    g.v < fn.nv ∧ pl.regOf g.v = none ∧ homeIdx fn pl g.v = i ∧
      (g.s, g.e) ∈ (pl.segs.getD g.v #[]).toList := by
  obtain ⟨-, v, hv, hk, hx⟩ := mem_homeOcc_iff.mp hg
  obtain ⟨rfl, hx⟩ := mem_segList.mp hx
  cases hr : pl.regOf g.v with
  | some r => rw [hr] at hk; cases hk
  | none =>
    rw [hr] at hk
    exact ⟨List.mem_range.mp hv, rfl, by simpa using hk, hx⟩

theorem homeIdx_inj {fn : Fn} {pl : LinearScan.Plan} {v w : Nat} (h : homeIdx fn pl v = homeIdx fn pl w) :
    pl.home.getD v 0 = pl.home.getD w 0 ∧ fn.clsOf v = fn.clsOf w := by
  simp only [homeIdx] at h
  have hi : (RegClass.int == RegClass.float) = false := by decide
  have hf : (RegClass.float == RegClass.float) = true := by decide
  cases hv : fn.clsOf v <;> cases hw : fn.clsOf w <;>
    simp only [hv, hw, hi, hf, Bool.false_eq_true, ite_true, ite_false] at h <;>
    first | exact ⟨by omega, rfl⟩ | exact absurd h (by omega)

private theorem any_iff {l : Array (Nat × Nat)} {f : Nat → Nat → Bool} :
    (l.any fun x => f x.1 x.2) = true ↔ ∃ s e, (s, e) ∈ l.toList ∧ f s e = true := by
  rw [← Array.any_toList, List.any_eq_true]
  constructor
  · rintro ⟨⟨s, e⟩, h, h'⟩; exact ⟨s, e, h, h'⟩
  · rintro ⟨s, e, h, h'⟩; exact ⟨(s, e), h, h'⟩

/-- `cov` from a segment. -/
theorem cov_iff {pl : LinearScan.Plan} {v p : Nat} :
    pl.cov v p = true ↔ ∃ s e, (s, e) ∈ (pl.segs.getD v #[]).toList ∧ s ≤ p ∧ p ≤ e := by
  simp only [Plan.cov]
  rw [any_iff (f := fun s e => decide (s ≤ p) && decide (p ≤ e))]
  simp only [Bool.and_eq_true, decide_eq_true_eq]

theorem covI_iff {pl : LinearScan.Plan} {v p q : Nat} :
    pl.covI v p q = true ↔ ∃ s e, (s, e) ∈ (pl.segs.getD v #[]).toList ∧ s ≤ p ∧ q ≤ e := by
  simp only [Plan.covI]
  rw [any_iff (f := fun s e => decide (s ≤ p) && decide (q ≤ e))]
  simp only [Bool.and_eq_true, decide_eq_true_eq]

end Backend.Proof.LS
