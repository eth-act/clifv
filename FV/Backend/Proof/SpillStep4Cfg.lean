import FV.Backend.Proof.SpillEdgesPrep

/-!
# `VCode.cfg` facts for the spill allocator (step 4)

Successor indices are block indices, every block has a successor list and ends in a terminator,
predecessor lists of size one or zero pin down the edges into a block, and `prepare`'s output
has a CFG.
-/

namespace Backend.Proof.Spill

open Backend Backend.Proof

theorem cfg_succ_lt {vc : VCode} {ss ps : Array (Array Nat)} (h : vc.cfg = .ok (ss, ps))
    {b : Nat} {sb : Array Nat} (hb : ss[b]? = some sb) {s : Nat} (hs : s ∈ sb.toList) :
    s < vc.blocks.size := by
  have cs := Prep.cfg_spec h
  have hbl : b < vc.blocks.size := by
    rw [← cs.size]; exact (Array.getElem?_eq_some_iff.mp hb).1
  obtain ⟨t, ts, -, -, hts, hsz, hl⟩ := cs.blk b _ (Array.getElem?_eq_getElem hbl)
  rw [hb] at hts; cases hts
  obtain ⟨j, hj, e⟩ := List.getElem_of_mem hs
  have hj' : j < t.targets.length := by rw [← hsz]; simpa using hj
  obtain ⟨k, hk, hlk⟩ := hl j _ (List.getElem?_eq_getElem hj')
  have : k = s := by
    rw [Array.getElem?_eq_getElem (by simpa using hj)] at hk
    rw [← e]; simpa using hk.symm
  subst this
  exact (Prep.lab_some hlk).1

theorem cfg_succs_some {vc : VCode} {ss ps : Array (Array Nat)} (h : vc.cfg = .ok (ss, ps))
    {b : Nat} (hb : b < vc.blocks.size) : ∃ sb, ss[b]? = some sb := by
  obtain ⟨-, ts, -, -, hts, -⟩ := (Prep.cfg_spec h).blk b _ (Array.getElem?_eq_getElem hb)
  exact ⟨ts, hts⟩

theorem cfg_last {vc : VCode} {ss ps : Array (Array Nat)} (h : vc.cfg = .ok (ss, ps))
    {b : Nat} {vb : VBlock} (hvb : vc.blocks[b]? = some vb) :
    ∃ t, vb.insts.back? = some t ∧ t.isTerminator = true := by
  obtain ⟨t, -, ht, hterm, -⟩ := (Prep.cfg_spec h).blk b vb hvb
  exact ⟨t, ht, hterm⟩

theorem count_le_predsOf (s : Nat) : ∀ (L : List (Array Nat × Nat)) (q : Array Nat × Nat),
    q ∈ L → q.1.toList.count s ≤ (predsOf s L).length
  | [], _, hq => by simp at hq
  | a :: L, q, hq => by
    simp only [predsOf, List.flatMap_cons, List.length_append, List.length_replicate] at *
    rcases List.mem_cons.mp hq with rfl | hq
    · omega
    · have := count_le_predsOf s L q hq
      simp only [predsOf] at this
      omega

theorem mem_predsOf (s : Nat) : ∀ (L : List (Array Nat × Nat)) (q : Array Nat × Nat),
    q ∈ L → s ∈ q.1.toList → q.2 ∈ predsOf s L
  | [], _, hq, _ => by simp at hq
  | a :: L, q, hq, hs => by
    simp only [predsOf, List.flatMap_cons, List.mem_append]
    rcases List.mem_cons.mp hq with rfl | hq
    · exact .inl (List.mem_replicate.mpr ⟨Nat.pos_iff_ne_zero.mp (List.count_pos_iff.mpr hs), rfl⟩)
    · exact .inr (mem_predsOf s L q hq hs)

theorem two_le_count {s : Nat} : ∀ {l : List Nat} {j j' : Nat}, l[j]? = some s → l[j']? = some s →
    j ≠ j' → 2 ≤ l.count s
  | [], _, _, h, _, _ => by simp at h
  | a :: l, 0, 0, _, _, hne => absurd rfl hne
  | a :: l, 0, j' + 1, h, h', _ => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    have : 0 < l.count a := List.count_pos_iff.mpr (List.mem_of_getElem? (by simpa using h'))
    rw [List.count_cons]; simp only [beq_self_eq_true, ite_true]; omega
  | a :: l, j + 1, 0, h, h', _ => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h'
    subst h'
    have : 0 < l.count a := List.count_pos_iff.mpr (List.mem_of_getElem? (by simpa using h))
    rw [List.count_cons]; simp only [beq_self_eq_true, ite_true]; omega
  | a :: l, j + 1, j' + 1, h, h', hne => by
    have := two_le_count (l := l) (j := j) (j' := j') (by simpa using h) (by simpa using h')
      (by omega)
    rw [List.count_cons]; omega

theorem mem_zipIdx_of {ss : Array (Array Nat)} {b : Nat} {sb : Array Nat} (hb : ss[b]? = some sb) :
    (sb, b) ∈ ss.toList.zipIdx := by
  rw [List.mem_zipIdx_iff_getElem?]
  simpa using hb

/-- An edge `b → s` (successor number `j`) into a block with the single predecessor `p`: `p = b`
and `j` is the only successor number of `b` leading to `s`. -/
theorem preds_single {vc : VCode} {ss ps : Array (Array Nat)} (h : vc.cfg = .ok (ss, ps))
    {b : Nat} {sb : Array Nat} (hb : ss[b]? = some sb) {j s : Nat} (hj : sb[j]? = some s)
    {p : Nat} (hp : ps[s]? = some #[p]) : p = b ∧ ∀ j', sb[j']? = some s → j' = j := by
  have hsm : s ∈ sb.toList := by simpa using Array.mem_of_getElem? hj
  have hs := cfg_succ_lt h hb hsm
  rw [cfg_preds h hs] at hp
  have e : predsOf s ss.toList.zipIdx = [p] := by
    have := congrArg Array.toList (Option.some.inj hp); simpa using this
  have hq := mem_zipIdx_of hb
  refine ⟨?_, fun j' hj' => Classical.byContradiction fun hne => ?_⟩
  · have := mem_predsOf s _ _ hq hsm
    rw [e] at this; exact (List.mem_singleton.mp this).symm
  · have h2 := two_le_count (l := sb.toList) (j := j') (j' := j) (by simpa using hj')
      (by simpa using hj) hne
    have := count_le_predsOf s _ _ hq
    rw [e] at this
    exact absurd (Nat.le_trans h2 this) (by simp)

/-- No edge enters a block without predecessors. -/
theorem preds_empty {vc : VCode} {ss ps : Array (Array Nat)} (h : vc.cfg = .ok (ss, ps))
    {s : Nat} (hp : ps[s]? = some #[]) {b : Nat} {sb : Array Nat} (hb : ss[b]? = some sb) :
    s ∉ sb.toList := by
  intro hsm
  have hs := cfg_succ_lt h hb hsm
  rw [cfg_preds h hs] at hp
  have e : predsOf s ss.toList.zipIdx = [] := by
    have := congrArg Array.toList (Option.some.inj hp); simpa using this
  have := mem_predsOf s _ _ (mem_zipIdx_of hb) hsm
  rw [e] at this; simp at this

/-- `prepare`'s output has a CFG (on `PrepDomain` input). -/
theorem cfg_ok_of_prepare {vc vcp : VCode} (hp : prepare vc = .ok vcp) (hd : Prep.PrepDomain vc) :
    ∃ ss ps, vcp.cfg = .ok (ss, ps) := by
  obtain ⟨ss0, ps0, ss1, ps1, ss2, ps2, next, B, E, hc0, hc1, hS, hc2, rfl⟩ := Prep.prepare_facts hp
  have cs0 := Prep.cfg_spec hc0
  have cs2 : Prep.CfgSpec (B ++ E) ss2 := Prep.cfg_spec hc2
  exact Prep.cfg3 hd cs0 cs2 hS

end Backend.Proof.Spill
