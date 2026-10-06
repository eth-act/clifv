import FV.Backend.Proof.SpillLocal
import FV.Backend.Proof.PrepareComplete

/-!
# The spill allocator's CFG facts across `prepare` (V4)

`LowOk vc`: the CFG facts of the VCode `lowerFunction` builds, with labels = block indices
(entry without parameters and predecessors, branch arguments only on a `jump` to a block with
matching parameters, parameterless successors otherwise, a `try_call`'s successors targeted by
it alone). `edgesOk_prepare`: `prepare`'s output then meets `EdgesOk`. `prepare` drops
unreachable blocks, splits critical edges by edge blocks `jump l` (no parameters, no branch
arguments, for blocks with at least two successors, which have no branch arguments) and reorders
the blocks; predecessor lists are recomputed by label.

Generic facts first: `VCode.cfg`'s predecessor lists (one entry per edge), the blocks `rpo`
lists are reachable.
-/

namespace Backend.Proof.Spill

open Backend Backend.Proof

/-! ## `VCode.cfg`'s predecessors -/

theorem forIn_ok_foldl {ε α β : Type} (l : List α) (init : β) (g : β → α → β) :
    (forIn l init fun a b => (Except.ok (ForInStep.yield (g b a)) : Except ε (ForInStep β))) =
      Except.ok (l.foldl g init) :=
  Prep.forIn_yield_foldl l init g _ (fun _ _ => rfl)

theorem forIn_ok_foldlA {ε α β : Type} (l : Array α) (init : β) (g : β → α → β) :
    (forIn l init fun a b => (Except.ok (ForInStep.yield (g b a)) : Except ε (ForInStep β))) =
      Except.ok (l.toList.foldl g init) := by
  rw [← Array.forIn_toList]; exact forIn_ok_foldl _ _ _

/-- The predecessor entries of `s` the edges `L` (successor lists with their block) add. -/
def predsOf (s : Nat) (L : List (Array Nat × Nat)) : List Nat :=
  L.flatMap fun q => List.replicate (q.1.toList.count s) q.2

theorem inner_fold (s i : Nat) : ∀ (x : List Nat) (p : Array (Array Nat)),
    (x.foldl (fun q s' => q.modify s' fun a => a.push i) p)[s]?.map Array.toList =
      p[s]?.map fun a => a.toList ++ List.replicate (x.count s) i
  | [], p => by simp
  | a :: x, p => by
    rw [List.foldl_cons, inner_fold s i x, Array.getElem?_modify, List.count_cons]
    by_cases h : a = s
    · subst h
      cases p[a]? <;> simp [List.replicate_succ]
    · simp only [h, ite_false, beq_iff_eq, Nat.add_zero]

theorem outer_fold (s : Nat) : ∀ (L : List (Array Nat × Nat)) (p : Array (Array Nat)),
    (L.foldl (fun b a => a.1.toList.foldl (fun q s' => q.modify s' fun x => x.push a.2) b) p)[s]?.map
        Array.toList = p[s]?.map fun a => a.toList ++ predsOf s L
  | [], p => by simp [predsOf]
  | a :: L, p => by
    rw [List.foldl_cons, outer_fold s L,
      show (fun a : Array Nat => a.toList ++ predsOf s L) = (fun l => l ++ predsOf s L) ∘ Array.toList
        from rfl, ← Option.map_map, inner_fold]
    cases p[s]? <;> simp [predsOf]

/-- **`VCode.cfg`'s predecessors**: one entry per edge, in block order. -/
theorem cfg_preds {vc : VCode} {ss ps : Array (Array Nat)} (h : vc.cfg = .ok (ss, ps)) {s : Nat}
    (hs : s < vc.blocks.size) : ps[s]? = some (predsOf s ss.toList.zipIdx).toArray := by
  unfold VCode.cfg at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  rename_i succs hsuccs
  rw [← Array.forIn_toList] at h
  simp only [pure, Except.pure] at h
  simp only [forIn_ok_foldlA (ε := String) _ _ (fun (q : Array (Array Nat)) (s : Nat) => q.modify s _)] at h
  simp only [forIn_ok_foldl, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have := outer_fold s succs.zipIdx.toList (Array.replicate vc.blocks.size #[])
  rw [Array.getElem?_replicate, ite_eq_left_iff.mpr (fun h => absurd hs h), Array.toList_zipIdx] at this
  cases e : (List.foldl (fun b a => a.1.toList.foldl (fun q s' => q.modify s' fun x => x.push a.2) b)
      (Array.replicate vc.blocks.size #[]) succs.toList.zipIdx)[s]? with
  | none => rw [e] at this; cases this
  | some a =>
    rw [e] at this
    simp only [Option.map_some, Option.some.injEq, List.nil_append] at this
    rw [Array.toList_zipIdx, e, ← this]

theorem predsOf_nil (s : Nat) : ∀ (L : List (Array Nat)) (k : Nat),
    (∀ (i : Nat) (x : Array Nat), L[i]? = some x → s ∉ x.toList) → predsOf s (L.zipIdx k) = []
  | [], _, _ => rfl
  | a :: L, k, h => by
    rw [List.zipIdx_cons]
    simp only [predsOf, List.flatMap_cons]
    rw [List.count_eq_zero.mpr (h 0 a rfl)]
    exact predsOf_nil s L (k + 1) fun i x hx => h (i + 1) x hx

theorem count_one {s : Nat} : ∀ {l : List Nat} {j0 : Nat}, l[j0]? = some s →
    (∀ j, l[j]? = some s → j = j0) → l.count s = 1
  | [], _, h, _ => by simp at h
  | a :: l, j0, h, hu => by
    rw [List.count_cons]
    by_cases ha : a = s
    · subst ha
      have h0 := hu 0 rfl
      subst h0
      have : l.count a = 0 := List.count_eq_zero.mpr fun hm => by
        obtain ⟨j, hj, e⟩ := List.getElem_of_mem hm
        have := hu (j + 1) (by simp [List.getElem?_eq_getElem hj, e])
        omega
      simp [this]
    · cases j0 with
      | zero => simp at h; exact absurd h ha
      | succ j0 =>
        have := count_one (l := l) (j0 := j0) (by simpa using h)
          (fun j hj => by have := hu (j + 1) (by simpa using hj); omega)
        simp [this, ha]

theorem predsOf_one (s p : Nat) : ∀ (L : List (Array Nat)) (k : Nat),
    (∀ (i : Nat) (x : Array Nat), L[i]? = some x → s ∈ x.toList → k + i = p) →
    (∀ x, L[p - k]? = some x → x.toList.count s = 1) → k ≤ p → p < k + L.length →
    predsOf s (L.zipIdx k) = [p]
  | [], _, _, _, h1, h2 => by simp at h2; omega
  | a :: L, k, hu, h1, hk, hp => by
    rw [List.zipIdx_cons]
    simp only [predsOf, List.flatMap_cons]
    by_cases e : k = p
    · subst e
      rw [h1 a (by simp)]
      have := predsOf_nil s L (k + 1) fun i x hx hm => by have := hu (i + 1) x hx hm; omega
      simp only [predsOf] at this
      rw [this]; rfl
    · rw [List.count_eq_zero.mpr fun hm => e (by simpa using hu 0 a rfl hm)]
      have := predsOf_one s p L (k + 1) (fun i x hx hm => by have := hu (i + 1) x hx hm; omega)
        (fun x hx => h1 x (by rw [show p - k = (p - (k + 1)) + 1 by omega]; simpa using hx))
        (by omega) (by simp at hp; omega)
      simp only [predsOf] at this
      simpa using this

/-- No edge into `s`: no predecessors. -/
theorem preds_nil {vc : VCode} {ss ps : Array (Array Nat)} (h : vc.cfg = .ok (ss, ps)) {s : Nat}
    (hs : s < vc.blocks.size)
    (hno : ∀ (q : Nat) (sq : Array Nat) (j : Nat), ss[q]? = some sq → sq[j]? = some s → False) :
    ps[s]? = some #[] := by
  rw [cfg_preds h hs, predsOf_nil s ss.toList 0 fun i x hx hm => by
    obtain ⟨j, hj, e⟩ := List.getElem_of_mem hm
    exact hno i x j (by simpa using hx) (by simp [← e])]

/-- One edge into `s`, from `p`: one predecessor. -/
theorem preds_one {vc : VCode} {ss ps : Array (Array Nat)} (h : vc.cfg = .ok (ss, ps)) {s : Nat}
    (hs : s < vc.blocks.size) {p j0 : Nat} {sp : Array Nat} (hp : ss[p]? = some sp)
    (hj0 : sp[j0]? = some s)
    (hu : ∀ (q : Nat) (sq : Array Nat) (j : Nat), ss[q]? = some sq → sq[j]? = some s → q = p ∧ j = j0) :
    ps[s]? = some #[p] := by
  have hpl : p < ss.size := (Array.getElem?_eq_some_iff.mp hp).1
  rw [cfg_preds h hs, predsOf_one s p ss.toList 0 (fun i x hx hm => by
      obtain ⟨j, hj, e⟩ := List.getElem_of_mem hm
      simpa using (hu i x j (by simpa using hx) (by simp [← e])).1)
    (fun x hx => by
      rw [Nat.sub_zero, Array.getElem?_toList, hp] at hx
      cases hx
      exact count_one (j0 := j0) (by simpa using hj0)
        (fun j hj => (hu p sp j hp (by simpa using hj)).2))
    (Nat.zero_le _) (by simpa using hpl)]

/-! ## `rpo` lists reachable blocks -/

/-- The stacked and finished blocks of `rpo`'s search are reachable. -/
def RR (succs : Array (Array Nat)) (st : Prep.DState) : Prop :=
  (∀ p ∈ st.2.2, Prep.Reach succs p.1) ∧ ∀ b ∈ st.2.1.toList, Prep.Reach succs b

theorem dStep_rr {succs : Array (Array Nat)} {st : Prep.DState} (h : RR succs st) {p : Nat × Nat}
    {rest : List (Nat × Nat)} (hw : st.2.2 = p :: rest) : RR succs (Prep.dStep succs st p rest) := by
  rcases st with ⟨seen, post, stack⟩
  simp only at hw
  subst hw
  obtain ⟨h1, h2⟩ := h
  have hb : Prep.Reach succs p.1 := h1 p (by simp)
  unfold Prep.dStep
  split
  · rename_i s hs
    have hr : Prep.Reach succs s :=
      .step hb (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hs))
    split
    · refine ⟨fun q hq => ?_, h2⟩
      simp only [List.mem_cons] at hq
      rcases hq with rfl | rfl | hq
      · exact hr
      · exact hb
      · exact h1 q (by simp [hq])
    · refine ⟨fun q hq => ?_, h2⟩
      simp only [List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact hb
      · exact h1 q (by simp [hq])
  · refine ⟨fun q hq => h1 q (by simp [hq]), fun b hb' => ?_⟩
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hb'
    rcases hb' with hb' | rfl
    · exact h2 b hb'
    · exact hb

theorem iter_rr {succs : Array (Array Nat)} :
    ∀ m (st : Prep.DState), RR succs st → RR succs (Prep.iterW (fun st : Prep.DState => st.2.2) (Prep.dStep succs) m st)
  | 0, st, h => h
  | m + 1, st, h => by
    simp only [Prep.iterW]
    split
    · exact h
    · rename_i p rest hw
      exact iter_rr m _ (dStep_rr h hw)

/-- Every block `rpo` lists is reachable. -/
theorem rpo_reach {succs : Array (Array Nat)} {b : Nat} (hb : b ∈ (rpo succs).toList) :
    Prep.Reach succs b := by
  by_cases h0 : succs.size = 0
  · have e : rpo succs = #[] := by unfold rpo; simp [h0]
    rw [e] at hb; simp at hb
  rw [Prep.rpo_eq succs h0] at hb
  have := iter_rr (succs := succs) (Prep.dFuel succs)
    ((Array.replicate succs.size false).set! 0 true, #[], [(0, 0)])
    ⟨fun p hp => by simp at hp; subst hp; exact .entry, fun b hb => by simp at hb⟩
  exact this.2 b (by simpa using hb)

/-- `omega` on label (in)equalities. -/
macro "lomega" : tactic => `(tactic| ((try simp only [Label] at *) <;> omega))

/-! ## The lowered VCode's CFG facts -/

/-- **The CFG facts of `lowerFunction`'s VCode** (labels = block indices). -/
structure LowOk (vc : VCode) : Prop where
  nonempty : 0 < vc.blocks.size
  labels : ∀ (l : Nat) (vb : VBlock), vc.blocks[l]? = some vb → vb.label = l
  entry : ∀ vb : VBlock, vc.blocks[0]? = some vb → vb.params = #[]
  /-- no branch to the entry -/
  noEntry : ∀ (b : Nat) (vb : VBlock) (t : MInst), vc.blocks[b]? = some vb → vb.insts.back? = some t →
    0 ∉ t.targets
  /-- branch arguments: a `jump` to a block with matching parameters -/
  args : ∀ (b : Nat) (vb : VBlock), vc.blocks[b]? = some vb → vb.branchArgs ≠ #[] →
    ∃ l tb, vb.insts.back? = some (.jump l) ∧ vc.blocks[l]? = some tb ∧
      tb.params.size = vb.branchArgs.size ∧
      (∀ (k : Nat) (a p : Reg), vb.branchArgs[k]? = some a → tb.params[k]? = some p →
        ∃ x y c, a = .vreg x c ∧ p = .vreg y c) ∧
      (tb.params.toList.map Reg.homeNum).Nodup
  /-- no branch arguments: parameterless successors -/
  noArgs : ∀ (b : Nat) (vb : VBlock) (t : MInst) (l : Label) (tb : VBlock), vc.blocks[b]? = some vb →
    vb.branchArgs = #[] → vb.insts.back? = some t → l ∈ t.targets → vc.blocks[l]? = some tb →
    tb.params = #[]
  tryArgs : ∀ (b : Nat) (vb : VBlock) (info : CallInfo) (ti : TryInfo), vc.blocks[b]? = some vb →
    vb.insts.back? = some (.tryCall info ti) → vb.branchArgs = #[]
  /-- a `try_call`'s successor is targeted by it alone, once -/
  tryUniq : ∀ (b : Nat) (vb : VBlock) (info : CallInfo) (ti : TryInfo) (j : Nat) (l : Label),
    vc.blocks[b]? = some vb → vb.insts.back? = some (.tryCall info ti) →
    (MInst.tryCall info ti).targets[j]? = some l →
    ∀ (b' : Nat) (vb' : VBlock) (t' : MInst) (j' : Nat), vc.blocks[b']? = some vb' →
      vb'.insts.back? = some t' → t'.targets[j']? = some l → b' = b ∧ j' = j

theorem LowOk.multi {vc : VCode} (hv : LowOk vc) {b : Nat} {vb : VBlock} {t : MInst}
    (hb : vc.blocks[b]? = some vb) (ht : vb.insts.back? = some t) (h2 : 2 ≤ t.targets.length) :
    vb.branchArgs = #[] := by
  refine Classical.byContradiction fun hne => ?_
  obtain ⟨l, -, hj, -⟩ := hv.args b vb hb hne
  rw [ht] at hj; cases hj
  simp [MInst.targets] at h2

theorem LowOk.prepDomain {vc : VCode} (hv : LowOk vc) : Prep.PrepDomain vc := by
  refine ⟨hv.nonempty, ?_, fun b vb t hb ht h2 => hv.multi hb ht h2⟩
  unfold Prep.Lbls
  have : vc.blocks.toList.map VBlock.label = List.range vc.blocks.size := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp only [List.getElem_map, Array.getElem_toList, List.getElem_range]
      simp only [List.length_map, Array.length_toList] at h1
      exact hv.labels i _ (Array.getElem?_eq_getElem h1)
  rw [this]; exact List.nodup_range

/-- An edge block of `prepare` targeted by a kept block that has at least two successors, at
the position where the kept block targets `l`. -/
def GoodE (V1 B E : Array VBlock) (e : Nat) : Prop :=
  ∃ (l' l : Label) (k m : Nat) (hk : k < V1.size) (hkB : k < B.size) (t t' : MInst),
    E[e]? = some { label := l', insts := #[.jump l] } ∧ V1[k].insts.back? = some t ∧
    B[k].insts.back? = some t' ∧ t'.targets[m]? = some l' ∧ t.targets[m]? = some l ∧
    2 ≤ t.targets.length

section main
variable {vc : VCode} (hv : LowOk vc) {ss0 ss1 ss2 : Array (Array Nat)} {next : Nat}
  {B E : Array VBlock} (cs0 : Prep.CfgSpec vc.blocks ss0)
  (cs1 : Prep.CfgSpec (Prep.keep vc.blocks (reachable ss0)) ss1) (cs2 : Prep.CfgSpec (B ++ E) ss2)
  (hS : Prep.SInv (Prep.keep vc.blocks (reachable ss0)) (Prep.next0Of (Prep.keep vc.blocks (reachable ss0)))
    (Prep.keep vc.blocks (reachable ss0)).size (next, B, E))

local notation "V1" => Prep.keep vc.blocks (reachable ss0)
local notation "N0" => Prep.next0Of (Prep.keep vc.blocks (reachable ss0))

include hv in
theorem v1_vc {k : Nat} (hk : k < (V1).size) :
    ∃ b, ∃ hb : b < vc.blocks.size, (V1)[k] = vc.blocks[b] ∧ (V1)[k].label = b := by
  obtain ⟨b, hb, e, -⟩ := Prep.keep_src hk
  exact ⟨b, hb, e, by rw [e]; exact hv.labels b _ (Array.getElem?_eq_getElem hb)⟩

include cs1 in
/-- A target of a kept block is the label of a kept block. -/
theorem tgt_v1 {k : Nat} (hk : k < (V1).size) {t : MInst} (ht : (V1)[k].insts.back? = some t) {m : Nat}
    {l : Label} (hl : t.targets[m]? = some l) :
    ∃ k', ∃ hk' : k' < (V1).size, (V1)[k'].label = l ∧ l < N0 := by
  obtain ⟨t0, ts, h0, -, -, -, hls⟩ := cs1.blk k (V1)[k] (Array.getElem?_eq_getElem hk)
  rw [ht] at h0; cases h0
  obtain ⟨k', -, hlab⟩ := hls m l hl
  obtain ⟨hk', e⟩ := Prep.lab_some hlab
  exact ⟨k', hk', e, e ▸ Prep.lt_next0 hk'⟩

include hS in
theorem e_blk {e : Nat} {eb : VBlock} (he : E[e]? = some eb) :
    eb.label = N0 + e ∧ eb.params = #[] ∧ eb.branchArgs = #[] ∧ ∃ l, eb.insts = #[.jump l] := by
  have hlt : e < E.size := (Array.getElem?_eq_some_iff.mp he).1
  obtain ⟨l, hl⟩ := hS.edges e hlt
  have : eb = E[e] := (Option.some.inj ((Array.getElem?_eq_getElem hlt).symm.trans he)).symm
  rw [this, hl]
  exact ⟨rfl, rfl, rfl, l, rfl⟩

include hS in
theorem b_fields {k : Nat} (hk : k < (V1).size) (hkB : k < B.size) :
    B[k].label = (V1)[k].label ∧ B[k].params = (V1)[k].params ∧ B[k].branchArgs = (V1)[k].branchArgs :=
  Prep.rw_fields (hS.rw k hk hkB)

include hv cs0 cs2 hS in
theorem basics :
    0 < (V1).size ∧ (V1)[0]? = vc.blocks[0]? ∧ Prep.Lbls V1 ∧ Prep.Lbls (B ++ E) ∧
      (∀ i ∈ (rpo ss2).toList, i < (B ++ E).size) ∧ (rpo ss2).toList.Nodup ∧ (rpo ss2)[0]? = some 0 := by
  obtain ⟨h1, h2, -, h4, h5, h6, h7, h8, -, -⟩ := Prep.facts_basic hv.prepDomain cs0 cs2 hS
  exact ⟨h1, h2, h4, h5, h6, h7, h8⟩

include hv cs0 cs2 hS in
/-- The block of `B ++ E` labelled by a kept block's label is that kept block's rewrite. -/
theorem lab2_v1 {k : Nat} (hk : k < (V1).size) {i : Nat} (hl : Prep.lab (B ++ E) (V1)[k].label = some i) :
    i = k := by
  obtain ⟨-, -, -, hn2, -⟩ := basics hv cs0 cs2 hS
  obtain ⟨hkB, e2⟩ := Prep.v2_B hS hk
  have hk2 : k < (B ++ E).size := (Array.getElem?_eq_some_iff.mp e2).1
  have hBk : (B ++ E)[k] = B[k] := Option.some.inj (by rw [← Array.getElem?_eq_getElem hk2, e2])
  have := Prep.lab_of hn2 hk2 (l := (V1)[k].label) (by rw [hBk]; exact (b_fields hS hk hkB).1)
  rw [hl] at this; exact (Option.some.inj this)

include hv cs0 cs2 hS in
theorem lab2_E {e : Nat} {eb : VBlock} (he : E[e]? = some eb) {i : Nat}
    (hl : Prep.lab (B ++ E) eb.label = some i) : i = (V1).size + e := by
  obtain ⟨-, -, -, hn2, -⟩ := basics hv cs0 cs2 hS
  have he2 : (B ++ E)[(V1).size + e]? = some eb := by rw [Prep.v2_E hS, he]
  have hu : (V1).size + e < (B ++ E).size := (Array.getElem?_eq_some_iff.mp he2).1
  have := Prep.lab_of hn2 hu (l := eb.label)
    (by rw [Option.some.inj ((Array.getElem?_eq_getElem hu).symm.trans he2)])
  rw [hl] at this; exact (Option.some.inj this)

include hv cs0 cs1 cs2 hS in
/-- A reachable block of `B ++ E` past the kept ones is a targeted edge block. -/
theorem good {i : Nat} (hr : Prep.Reach ss2 i) : (V1).size ≤ i → GoodE V1 B E (i - (V1).size) := by
  obtain ⟨h10, -⟩ := basics hv cs0 cs2 hS
  induction hr with
  | entry => intro h; omega
  | @step i' i hr' hs ih =>
    intro hi
    obtain ⟨hi', t'', j, L, hback, htj, hlab⟩ := Prep.succ_of cs2 hs
    obtain ⟨hiL, hL⟩ := Prep.lab_some hlab
    by_cases hk : i' < (V1).size
    · obtain ⟨hkB, t, t', ht, ht', -, -, -, -, -, -, -, hrel⟩ := Prep.blk2 hS cs1 hk
      have e2 : (B ++ E)[i'] = B[i'] := Array.getElem_append_left hkB
      rw [e2, ht'] at hback
      have htt : t' = t'' := Option.some.inj hback
      subst htt
      obtain ⟨l, hl, hcase⟩ := hrel j L htj
      rcases hcase with rfl | ⟨h2, e, he⟩
      · exfalso
        obtain ⟨k', hk', hlk', -⟩ := tgt_v1 cs1 hk ht hl
        rw [← hlk'] at hlab
        have := lab2_v1 hv cs0 cs2 hS hk' hlab
        omega
      · have := lab2_E hv cs0 cs2 hS he (i := i) hlab
        subst this
        rw [Nat.add_sub_cancel_left]
        exact ⟨L, l, i', j, hk, hkB, t, t', he, ht, ht', htj, hl, h2⟩
    · exfalso
      obtain ⟨l', l, k, m, hk0, hkB0, t, t', he, ht, ht', hm', hm, h2⟩ := ih (by omega)
      have hE : (B ++ E)[i']? = some { label := l', insts := #[.jump l] } := by
        rw [show i' = (V1).size + (i' - (V1).size) by omega, Prep.v2_E hS, he]
      rw [Array.getElem?_eq_getElem hi'] at hE
      rw [Option.some.inj hE] at hback
      cases hback
      have hj : j = 0 := by
        have := (List.getElem?_eq_some_iff.mp htj).1
        simp [MInst.targets] at this; omega
      subst hj
      cases htj
      obtain ⟨k', hk', hlk', -⟩ := tgt_v1 cs1 hk0 ht hm
      rw [← hlk'] at hlab
      have := lab2_v1 hv cs0 cs2 hS hk' hlab
      omega

include hv cs0 cs1 cs2 hS in
/-- **The blocks of `prepare`'s output**: a kept block's rewrite, or a targeted edge block. -/
theorem cls3 {q : Nat} {vb : VBlock} (hq : ((rpo ss2).map fun i => (B ++ E)[i]!)[q]? = some vb) :
    (∃ k, ∃ hk : k < (V1).size, ∃ hkB : k < B.size, (rpo ss2)[q]? = some k ∧ vb = B[k]) ∨
      (∃ e, (rpo ss2)[q]? = some ((V1).size + e) ∧ E[e]? = some vb ∧ GoodE V1 B E e) := by
  obtain ⟨-, -, -, -, hR, -⟩ := basics hv cs0 cs2 hS
  have hqR : q < (rpo ss2).size := by
    have := (Array.getElem?_eq_some_iff.mp hq).1; simpa using this
  obtain ⟨hi, e3⟩ := Prep.v3_get hR hqR
  rw [e3] at hq
  have hvb := (Option.some.inj hq).symm
  have hRq : (rpo ss2)[q]? = some (rpo ss2)[q] := Array.getElem?_eq_getElem hqR
  by_cases hk : (rpo ss2)[q] < (V1).size
  · have hkB : (rpo ss2)[q] < B.size := by rw [hS.size]; exact hk
    refine .inl ⟨_, hk, hkB, hRq, by rw [hvb]; exact Array.getElem_append_left hkB⟩
  · right
    refine ⟨(rpo ss2)[q] - (V1).size, by rw [hRq]; congr 1; omega, ?_, ?_⟩
    · rw [← Prep.v2_E hS, show (V1).size + ((rpo ss2)[q] - (V1).size) = (rpo ss2)[q] by omega,
        Array.getElem?_eq_getElem hi, hvb]
    · exact good hv cs0 cs1 cs2 hS (rpo_reach (by simp)) (by omega)

theorem succ3 {V : Array VBlock} {ss : Array (Array Nat)} (cs : Prep.CfgSpec V ss) {q j s : Nat}
    {sq : Array Nat} (hq : ss[q]? = some sq) (hj : sq[j]? = some s) :
    ∃ vb t l, V[q]? = some vb ∧ vb.insts.back? = some t ∧ t.targets[j]? = some l ∧
      Prep.lab V l = some s := by
  have hqV : q < V.size := by rw [← cs.size]; exact (Array.getElem?_eq_some_iff.mp hq).1
  obtain ⟨t, ts, ht, -, hts, hsz, hl⟩ := cs.blk q V[q] (Array.getElem?_eq_getElem hqV)
  rw [hq] at hts; cases hts
  have hjl : j < t.targets.length := by rw [← hsz]; exact (Array.getElem?_eq_some_iff.mp hj).1
  obtain ⟨k, hk, hlab⟩ := hl j _ (List.getElem?_eq_getElem hjl)
  rw [hj] at hk; cases hk
  exact ⟨_, t, _, Array.getElem?_eq_getElem hqV, ht, List.getElem?_eq_getElem hjl, hlab⟩

theorem n0_pos (V : Array VBlock) : 0 < Prep.next0Of V := by unfold Prep.next0Of; omega

theorem nodup_idx {l : List Nat} (hn : l.Nodup) {i j x : Nat} (hi : l[i]? = some x)
    (hj : l[j]? = some x) : i = j := by
  obtain ⟨hi', e1⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hj', e2⟩ := List.getElem?_eq_some_iff.mp hj
  exact hn.eq_of_getElem_eq hi' hj' (by rw [e1, e2])

include hv cs0 cs1 cs2 hS in
/-- The block of `prepare`'s output labelled by a kept block's label has its parameters. -/
theorem params_at {u : Nat} {vbu : VBlock}
    (hu : ((rpo ss2).map fun i => (B ++ E)[i]!)[u]? = some vbu) {k' : Nat} (hk' : k' < (V1).size)
    (hl : vbu.label = (V1)[k'].label) : vbu.params = (V1)[k'].params := by
  obtain ⟨-, -, hn1, -⟩ := basics hv cs0 cs2 hS
  rcases cls3 hv cs0 cs1 cs2 hS hu with ⟨k, hk, hkB, -, rfl⟩ | ⟨e, -, he, -⟩
  · obtain ⟨h1, h2, -⟩ := b_fields hS hk hkB
    rw [h1] at hl
    have := Prep.lbl_inj hn1 hk hk' hl
    subst this; exact h2
  · obtain ⟨h1, -⟩ := e_blk hS he
    have := Prep.lt_next0 hk'
    lomega

include hv cs0 cs1 cs2 hS in
theorem no_tgt0 {q : Nat} {vb : VBlock} (hq : ((rpo ss2).map fun i => (B ++ E)[i]!)[q]? = some vb)
    {t : MInst} (ht : vb.insts.back? = some t) {j : Nat} (hj : t.targets[j]? = some 0) : False := by
  rcases cls3 hv cs0 cs1 cs2 hS hq with ⟨k, hk, hkB, -, rfl⟩ | ⟨e, -, he, ⟨l', l, kk, m, hkk, -, t1, -, he', ht1, -, -, hm, -⟩⟩
  · obtain ⟨hkB0, t0, t', ht0, ht', -, -, -, -, -, -, -, hrel⟩ := Prep.blk2 hS cs1 hk
    rw [ht'] at ht
    have htt : t' = t := Option.some.inj ht
    subst htt
    obtain ⟨l0, hl0, hc⟩ := hrel j 0 hj
    rcases hc with rfl | ⟨-, e, he⟩
    · obtain ⟨b0, hb0, e0, -⟩ := v1_vc hv hk
      rw [e0] at ht0
      exact hv.noEntry b0 _ t0 (Array.getElem?_eq_getElem hb0) ht0 (List.mem_of_getElem? hl0)
    · have h1 := (e_blk hS he).1
      have h2 := n0_pos (V1)
      simp only at h1; lomega
  · rw [he'] at he
    cases he
    simp [Array.back?] at ht
    subst ht
    have hj0 : j = 0 := by
      have := (List.getElem?_eq_some_iff.mp hj).1; simp [MInst.targets] at this; omega
    subst hj0
    cases hj
    obtain ⟨b1, hb1, e1, -⟩ := v1_vc hv hkk
    rw [e1] at ht1
    exact hv.noEntry b1 _ t1 (Array.getElem?_eq_getElem hb1) ht1 (List.mem_of_getElem? hm)

include hv cs0 cs1 cs2 hS in
/-- **`EdgesOk` of `prepare`'s output.** -/
theorem edgesOk_main {ss3 ps3 : Array (Array Nat)}
    (hc3 : ({ vc with blocks := (rpo ss2).map fun i => (B ++ E)[i]! } : VCode).cfg = .ok (ss3, ps3)) :
    EdgesOk { vc with blocks := (rpo ss2).map fun i => (B ++ E)[i]! } ss3 ps3 := by
  have cs3 : Prep.CfgSpec ((rpo ss2).map fun i => (B ++ E)[i]!) ss3 := Prep.cfg_spec hc3
  obtain ⟨h10, hV0, hn1, hn2, hR, hRn, hR0⟩ := basics hv cs0 cs2 hS
  have hRs : 0 < (rpo ss2).size := (Array.getElem?_eq_some_iff.mp hR0).1
  have h0B : 0 < B.size := by rw [hS.size]; exact h10
  have hV1vc : (V1)[0] = vc.blocks[0]'hv.nonempty :=
    Option.some.inj ((Array.getElem?_eq_getElem h10).symm.trans
      (hV0.trans (Array.getElem?_eq_getElem hv.nonempty)))
  have hV30 : ((rpo ss2).map fun i => (B ++ E)[i]!)[0]? = some B[0] := by
    obtain ⟨hi, e⟩ := Prep.v3_get hR hRs
    rw [e]; congr 1
    have : (rpo ss2)[0] = 0 := Option.some.inj ((Array.getElem?_eq_getElem hRs).symm.trans hR0)
    simp only [this]
    exact Array.getElem_append_left h0B
  obtain ⟨hl0, hp0, -⟩ := b_fields hS h10 h0B
  rw [hV1vc] at hl0 hp0
  have hlab0 := hv.labels 0 _ (Array.getElem?_eq_getElem hv.nonempty)
  have hpar0 := hv.entry _ (Array.getElem?_eq_getElem hv.nonempty)
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · -- the entry exists
    show ((rpo ss2).map fun i => (B ++ E)[i]!).size ≠ 0
    rw [Array.size_map]; omega
  · -- the entry has no predecessors
    refine preds_nil hc3 (by show 0 < ((rpo ss2).map fun i => (B ++ E)[i]!).size; rw [Array.size_map]; exact hRs) fun q sq j hq hj => ?_
    obtain ⟨vb, t, l, hvb, ht, hl, hlab⟩ := succ3 cs3 hq hj
    obtain ⟨hlab0', hlab'⟩ := Prep.lab_some hlab
    have : l = 0 := by
      rw [← hlab']
      have := Option.some.inj ((Array.getElem?_eq_getElem hlab0').symm.trans hV30)
      rw [this, hl0, hlab0]
    subst this
    exact no_tgt0 hv cs0 cs1 cs2 hS hvb ht hl
  · -- the entry has no parameters
    show (((rpo ss2).map fun i => (B ++ E)[i]!)[0]!).params = #[]
    have h03 : 0 < ((rpo ss2).map fun i => (B ++ E)[i]!).size := by rw [Array.size_map]; exact hRs
    rw [getElem!_pos _ 0 h03, Option.some.inj ((Array.getElem?_eq_getElem h03).symm.trans hV30),
      hp0, hpar0]
  · -- branch arguments
    intro b vb hvb hba
    change ((rpo ss2).map fun i => (B ++ E)[i]!)[b]? = some vb at hvb
    rcases cls3 hv cs0 cs1 cs2 hS hvb with ⟨k, hk, hkB, -, rfl⟩ | ⟨e, -, he, -⟩
    · obtain ⟨-, -, hba'⟩ := b_fields hS hk hkB
      obtain ⟨b0, hb0, e0, hlb0⟩ := v1_vc hv hk
      rw [hba', e0] at hba
      obtain ⟨l, tb, hj, htb, hsz, hcls, hnd⟩ := hv.args b0 _ (Array.getElem?_eq_getElem hb0) hba
      have hBk : B[k] = (V1)[k] := by
        rcases hS.rw k hk hkB with h | ⟨t, -, -, h1, h2, -⟩
        · exact h
        · rw [e0, hj] at h1; cases h1; simp [MInst.targets] at h2
      rw [hBk, e0]
      rw [hBk, e0] at hvb
      refine ⟨⟨_, hj, rfl⟩, ?_⟩
      obtain ⟨t3, ts, ht3, -, hts, hsz3, hl3⟩ := cs3.blk b _ hvb
      rw [hj] at ht3; cases ht3
      obtain ⟨u, hu, hlab⟩ := hl3 0 l rfl
      have hts' : ts = #[u] := by
        apply Array.ext
        · simp [hsz3, MInst.targets]
        · intro i h1 h2
          have : i = 0 := by simp [hsz3, MInst.targets] at h1; omega
          subst this
          simp only [Array.getElem?_eq_getElem h1] at hu
          simpa using hu
      subst hts'
      obtain ⟨hu', hlu⟩ := Prep.lab_some hlab
      have hj' : ((V1)[k]).insts.back? = some (.jump l) := by rw [e0]; exact hj
      obtain ⟨k', hk', hlk', -⟩ := tgt_v1 cs1 hk hj' (m := 0) rfl
      obtain ⟨b', hb', e', hlb'⟩ := v1_vc hv hk'
      have hbl : b' = l := by rw [← hlb', hlk']
      subst hbl
      have hpar := params_at hv cs0 cs1 cs2 hS (Array.getElem?_eq_getElem hu') hk' (by rw [hlu, hlk'])
      rw [e', Option.some.inj ((Array.getElem?_eq_getElem hb').symm.trans htb)] at hpar
      refine ⟨u, _, hts, Array.getElem?_eq_getElem hu', by rw [hpar, hsz], fun i a p ha hp => ?_, by rw [hpar]; exact hnd⟩
      rw [hpar] at hp
      exact hcls i a p ha hp
    · exact absurd (e_blk hS he).2.2.1 hba
  · -- no branch arguments
    intro b vb ss s sb hvb hba hss hs hsb
    change ((rpo ss2).map fun i => (B ++ E)[i]!)[b]? = some vb at hvb
    change ((rpo ss2).map fun i => (B ++ E)[i]!)[s]? = some sb at hsb
    obtain ⟨j, hj, hjs⟩ := List.getElem_of_mem hs
    have hj' : ss[j]? = some s := by simpa [← hjs] using hj
    obtain ⟨vb', t, l, hvb', ht, htj, hlab⟩ := succ3 cs3 hss hj'
    rw [hvb] at hvb'; cases hvb'
    obtain ⟨hsl, hsl'⟩ := Prep.lab_some hlab
    have hsbl : sb.label = l := by
      rw [← hsl', Option.some.inj ((Array.getElem?_eq_getElem hsl).symm.trans hsb)]
    rcases cls3 hv cs0 cs1 cs2 hS hsb with ⟨k', hk', hkB', -, rfl⟩ | ⟨e, -, he, -⟩
    · obtain ⟨hl', hp', -⟩ := b_fields hS hk' hkB'
      rw [hp']
      rw [hl'] at hsbl
      obtain ⟨b', hb', e', hlb'⟩ := v1_vc hv hk'
      have hbl : b' = l := by rw [← hlb', hsbl]
      subst hbl
      rw [e']
      have htb := Array.getElem?_eq_getElem hb'
      rcases cls3 hv cs0 cs1 cs2 hS hvb with ⟨k, hk, hkB, -, rfl⟩ |
        ⟨e, -, he, ⟨l'', l1, kk, m, hkk, -, t1, -, he', ht1, -, -, hm, h2⟩⟩
      · obtain ⟨hkB0, t0, t', ht0, ht', -, -, -, -, -, -, -, hrel⟩ := Prep.blk2 hS cs1 hk
        rw [ht'] at ht
        have htt : t' = t := Option.some.inj ht
        subst htt
        obtain ⟨l0, hl0, hc⟩ := hrel j _ htj
        rcases hc with hc | ⟨-, e, he⟩
        · subst hc
          obtain ⟨-, -, hba'⟩ := b_fields hS hk hkB
          obtain ⟨b0, hb0, e0, -⟩ := v1_vc hv hk
          rw [e0] at ht0 hba'
          exact hv.noArgs b0 _ t0 _ _ (Array.getElem?_eq_getElem hb0) (hba'.symm.trans hba) ht0
            (List.mem_of_getElem? hl0) htb
        · have := (e_blk hS he).1
          have := Prep.lt_next0 hk'
          lomega
      · rw [he'] at he
        cases he
        simp [Array.back?] at ht
        subst ht
        have hj0 : j = 0 := by
          have := (List.getElem?_eq_some_iff.mp htj).1; simp [MInst.targets] at this; omega
        subst hj0
        cases htj
        obtain ⟨b1, hb1, e1, -⟩ := v1_vc hv hkk
        rw [e1] at ht1
        exact hv.noArgs b1 _ t1 _ _ (Array.getElem?_eq_getElem hb1)
          (hv.multi (Array.getElem?_eq_getElem hb1) ht1 h2) ht1 (List.mem_of_getElem? hm) htb
    · exact (e_blk hS he).2.1
  · -- `try_call` successors
    intro b vb info ti ss s hvb hback
    change ((rpo ss2).map fun i => (B ++ E)[i]!)[b]? = some vb at hvb
    rcases cls3 hv cs0 cs1 cs2 hS hvb with ⟨k, hk, hkB, hRb, rfl⟩ | ⟨e, -, he, -⟩
    · obtain ⟨hkB0, t0, t', ht0, ht', -, -, -, -, -, hsame, -, hrel⟩ := Prep.blk2 hS cs1 hk
      rw [ht'] at hback
      have htt : t' = .tryCall info ti := Option.some.inj hback
      subst htt
      obtain ⟨info0, ti0, rfl⟩ : ∃ info0 ti0, t0 = .tryCall info0 ti0 := by
        rcases hsame with h | h
        · exact ⟨info, ti, h.symm⟩
        · exact (Prep.setTargets_targets h).2.2.1 ⟨info, ti, rfl⟩
      obtain ⟨b0, hb0, e0, hlb0⟩ := v1_vc hv hk
      have hb0' := Array.getElem?_eq_getElem hb0
      rw [e0] at ht0
      obtain ⟨-, -, hba'⟩ := b_fields hS hk hkB
      refine ⟨by rw [hba', e0]; exact hv.tryArgs b0 _ info0 ti0 hb0' ht0, fun hss hs => ?_⟩
      obtain ⟨j, hj, hjs⟩ := List.getElem_of_mem hs
      have hj' : ss[j]? = some s := by simpa [← hjs] using hj
      obtain ⟨vb', t, L, hvb', ht, htj, hlab⟩ := succ3 cs3 hss hj'
      rw [hvb] at hvb'; cases hvb'
      rw [ht'] at ht; cases ht
      obtain ⟨hsl, hsl'⟩ := Prep.lab_some hlab
      obtain ⟨l0, hl0, hc⟩ := hrel j L htj
      have huq := hv.tryUniq b0 _ info0 ti0 j l0 hb0' ht0 hl0
      obtain ⟨-, -, -, hl0N⟩ := tgt_v1 cs1 hk (by rw [e0]; exact ht0) hl0
      refine preds_one hc3 (by simpa using hsl) hss hj' fun q sq j2 hq hj2 => ?_
      obtain ⟨vb2, t2, L2, hvb2, ht2, htj2, hlab2⟩ := succ3 cs3 hq hj2
      obtain ⟨hsl2', hsl2⟩ := Prep.lab_some hlab2
      have hLL : L2 = L := by rw [← hsl2, hsl']
      subst hLL
      rcases cls3 hv cs0 cs1 cs2 hS hvb2 with ⟨k2, hk2, hkB2, hRq, rfl⟩ |
        ⟨e2, -, he2, ⟨L3, l3, k3, m3, hk3, hk3B, t3, t3', he3, ht3, ht3', hm3', hm3, -⟩⟩
      · obtain ⟨hkB20, t2o, t2', ht2o, ht2', -, -, -, -, -, -, -, hrel2⟩ := Prep.blk2 hS cs1 hk2
        rw [ht2'] at ht2
        have htt : t2' = t2 := Option.some.inj ht2
        subst htt
        obtain ⟨l2, hl2, hc2⟩ := hrel2 j2 L2 htj2
        obtain ⟨-, -, -, hl2N⟩ := tgt_v1 cs1 hk2 ht2o hl2
        have hll : l2 = l0 := by
          rcases hc with rfl | ⟨-, e, he⟩ <;> rcases hc2 with h | ⟨-, e2, he2⟩
          · exact h.symm
          · have := (e_blk hS he2).1; simp at this; lomega
          · have := (e_blk hS he).1; simp at this; lomega
          · have h1 := (e_blk hS he).1
            have h2 := (e_blk hS he2).1
            simp only at h1 h2
            have : e = e2 := by lomega
            subst this
            have := he.symm.trans he2
            simp only [Option.some.injEq, VBlock.mk.injEq, true_and, and_true] at this
            simpa using (congrArg Array.toList this).symm
        subst hll
        obtain ⟨b2, hb2, e2', hlb2⟩ := v1_vc hv hk2
        rw [e2'] at ht2o
        obtain ⟨rfl, rfl⟩ := huq b2 _ t2o j2 (Array.getElem?_eq_getElem hb2) ht2o hl2
        have hkk : k2 = k := Prep.lbl_inj hn1 hk2 hk (by rw [hlb2, hlb0])
        subst hkk
        exact ⟨nodup_idx hRn (by simpa using hRq) (by simpa using hRb), rfl⟩
      · exfalso
        rw [he3] at he2
        cases he2
        simp [Array.back?] at ht2
        subst ht2
        have hj0 : j2 = 0 := by
          have := (List.getElem?_eq_some_iff.mp htj2).1; simp [MInst.targets] at this; omega
        subst hj0
        cases htj2
        obtain ⟨-, -, -, hL⟩ := tgt_v1 cs1 hk3 ht3 hm3
        have hL0 : L2 = l0 := by
          rcases hc with h | ⟨-, e, he⟩
          · exact h
          · have := (e_blk hS he).1; simp at this; lomega
        subst hL0
        obtain ⟨b3, hb3, e3', hlb3⟩ := v1_vc hv hk3
        rw [e3'] at ht3
        obtain ⟨rfl, rfl⟩ := huq b3 _ t3 m3 (Array.getElem?_eq_getElem hb3) ht3 hm3
        have hkk : k3 = k := Prep.lbl_inj hn1 hk3 hk (by rw [hlb3, hlb0])
        subst hkk
        rw [ht'] at ht3'
        cases ht3'
        rw [htj] at hm3'
        cases hm3'
        have := (e_blk hS he3).1
        simp at this
        lomega
    · have := (e_blk hS he).2.2.2
      obtain ⟨l, hl⟩ := this
      rw [hl] at hback
      simp [Array.back?] at hback

end main

/-- **`prepare` keeps the CFG facts** of the lowered VCode. -/
theorem edgesOk_prepare {vc vcp : VCode} (hv : LowOk vc) (hp : prepare vc = .ok vcp) :
    ∀ succs preds, vcp.cfg = .ok (succs, preds) → EdgesOk vcp succs preds := by
  obtain ⟨ss0, ps0, ss1, ps1, ss2, ps2, next, B, E, hc0, hc1, hS, hc2, rfl⟩ := Prep.prepare_facts hp
  intro succs preds hc3
  exact edgesOk_main hv (Prep.cfg_spec hc0) (Prep.cfg_spec hc1) (Prep.cfg_spec hc2) hS hc3

end Backend.Proof.Spill
