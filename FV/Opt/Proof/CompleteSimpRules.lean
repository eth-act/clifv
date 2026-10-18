import FV.Opt.Proof.CompleteSimpMat

/-!
# Completeness of simplify: the rules phase

While the rules rewrite a value (`Opt.optimizeAt`, `Opt.skelMake`, `Opt.runSkel`) the output side
of the state does not change, the graph only grows by fresh well-typed nodes over placeable values,
and (under `Opt.SimpRulesOk`/`Opt.SkelRulesOk`) every candidate is placeable or the root
(`opt_spec`, `runSkel_ok`). `RInv` is the state invariant of this phase: the `materialize` facts,
no partial node, hash-consing entries mapping to placeable values or to the exceptional values `X`
(the current statement's value, which `Opt.pureBest` pre-inserts), and e-classes of one type.
-/

namespace Opt

open Clif

section Rules

variable {f : Function} {V : Nat → Option Block} {B : ValueId → Prop} {X : ValueId → Prop}
  {XN : Inst → Prop}

/-- The state invariant of the rules phase (module doc). -/
structure RInv (f : Function) (V : Nat → Option Block) (B X : ValueId → Prop) (XN : Inst → Prop)
    (st : SState) : Prop where
  m : MInv f V B st
  noPartial : ∀ x, st.partialVals.contains x = false
  memo : ∀ n w, st.memo.get? n = some w → (Placed st B w ∨ (X w ∧ XN n)) ∧ st.known w = true ∧
    st.types.get? w = SState.nodeTy n
  alts : ∀ x ms, st.alts.get? x = some ms → ∀ m ∈ ms, st.known m = true ∧
    st.types.get? m = st.types.get? x

/-- The recorded e-classes: members of the class's type, known, with placeable node operands. -/
def CInv (B : ValueId → Prop) (st : SState) : Prop :=
  ∀ k ms, st.classes.get? k = some ms → st.known k = true ∧ ∀ m ∈ ms, st.known m = true ∧
    st.types.get? m = st.types.get? k ∧
      ∀ n, st.defs.get? m = some n → ∀ y ∈ operands n, Placed st B y

/-- How the state moves in the rules phase. -/
structure RStep (B : ValueId → Prop) (st st' : SState) : Prop where
  avail : st'.avail = st.avail
  alts : st'.alts = st.alts
  fn : st'.fn = st.fn
  trap : st'.trapBlocks = st.trapBlocks
  remat : st'.rematConst = st.rematConst
  next : st.next ≤ st'.next
  defs : ∀ y n, st.defs.get? y = some n → st'.defs.get? y = some n
  defsNew : ∀ y n, st'.defs.get? y = some n → st.defs.get? y = some n ∨ st.known y = false
  types : ∀ y t, st.types.get? y = some t → st'.types.get? y = some t
  typesKnown : ∀ y, st.known y = true → st'.types.get? y = st.types.get? y
  good : ∀ y, Placed st B y → Placed st' B y
  fresh : ∀ y n, st'.defs.get? y = some n → st.defs.get? y = some n ∨ maxValue st.fn < y

theorem RStep.refl (st : SState) : RStep B st st :=
  ⟨rfl, rfl, rfl, rfl, rfl, Nat.le_refl _, fun _ _ h => h, fun _ _ h => .inl h, fun _ _ h => h,
   fun _ _ => rfl, fun _ h => h, fun _ _ h => .inl h⟩

theorem RStep.known {st st' : SState} (h : RStep B st st') {x : ValueId}
    (hx : st.known x = true) : st'.known x = true := by
  rcases known_iff.1 hx with hx | hx
  · obtain ⟨n, hn⟩ := Option.isSome_iff_exists.1 hx
    exact known_iff.2 (.inl (by rw [h.defs x n hn]; rfl))
  · exact known_iff.2 (.inr (by rw [h.avail]; exact hx))

theorem RStep.trans {st1 st2 st3 : SState} (h1 : RStep B st1 st2) (h2 : RStep B st2 st3) :
    RStep B st1 st3 := by
  refine
  ⟨h2.avail.trans h1.avail, h2.alts.trans h1.alts, h2.fn.trans h1.fn, h2.trap.trans h1.trap,
   h2.remat.trans h1.remat, Nat.le_trans h1.next h2.next, fun y n h => h2.defs y n (h1.defs y n h),
   fun y n h => ?_, fun y t h => h2.types y t (h1.types y t h),
   fun y hy => (h2.typesKnown y (h1.known hy)).trans (h1.typesKnown y hy),
   fun y h => h2.good y (h1.good y h), fun y n h => ?_⟩
  rotate_left
  · rcases h2.fresh y n h with h | h
    · exact h1.fresh y n h
    · exact .inr (by rw [← h1.fn]; exact h)
  rcases h2.defsNew y n h with h | h
  · exact h1.defsNew y n h
  · cases hk : st1.known y with
    | false => exact .inr rfl
    | true => rw [h1.known hk] at h; cases h

theorem MInv.congr {st st' : SState} (h : MInv f V B st) (hd : st'.defs = st.defs)
    (ha : st'.alts = st.alts) (hv : st'.avail = st.avail) (ht : st'.types = st.types)
    (hn : st'.next = st.next) (hf : st'.fn = st.fn) : MInv f V B st' := by
  have hk : ∀ x, st'.known x = st.known x := by intro x; simp [SState.known, hd, hv]
  exact ⟨by rw [hf]; exact h.fn, by rw [hn]; exact h.maxLt,
    fun x hx => by rw [hn]; exact h.knownLt x (by rw [← hk]; exact hx),
    fun x hx => by rw [ht]; exact h.typesFresh x (by rw [← hn]; exact hx),
    fun x n hx => by rw [ht]; rw [hd] at hx; exact h.defsTy x n hx,
    fun x ms hx => by rw [hk]; rw [ha] at hx; exact h.altsKnown x ms hx,
    fun x d hx => by rw [hv] at hx; exact h.availDef x d hx,
    fun x d t hx => by rw [hv]; exact h.defAvail x d t hx,
    fun x n hx hav => by rw [hd] at hx; rw [hv] at hav; exact h.newBig x n hx hav,
    h.badLe, h.uniq⟩

/-- States that agree on every field the invariants read. -/
theorem RInv.congr {st st' : SState} (h : RInv f V B X XN st) (hd : st'.defs = st.defs)
    (ha : st'.alts = st.alts) (hv : st'.avail = st.avail) (ht : st'.types = st.types)
    (hn : st'.next = st.next) (hf : st'.fn = st.fn) (hm : st'.memo = st.memo)
    (hp : st'.partialVals = st.partialVals) : RInv f V B X XN st' := by
  have hk : ∀ x, st'.known x = st.known x := by intro x; simp [SState.known, hd, hv]
  have hg : ∀ x, Placed st B x → Placed st' B x := fun x h => Placed.congr hd ha hv h
  refine ⟨h.m.congr hd ha hv ht hn hf, fun x => by rw [hp]; exact h.noPartial x,
    fun n w hw => ?_, fun x ms hx m hm' => ?_⟩
  · rw [hm] at hw
    obtain ⟨h1, h2, h3⟩ := h.memo n w hw
    exact ⟨h1.imp (hg w) id, by rw [hk]; exact h2, by rw [ht]; exact h3⟩
  · rw [ha] at hx
    obtain ⟨h1, h2⟩ := h.alts x ms hx m hm'
    exact ⟨by rw [hk]; exact h1, by rw [ht]; exact h2⟩

theorem RStep.of_fields {st st' : SState} (hd : st'.defs = st.defs)
    (ha : st'.alts = st.alts) (hv : st'.avail = st.avail) (ht : st'.types = st.types)
    (hn : st'.next = st.next) (hf : st'.fn = st.fn) (htr : st'.trapBlocks = st.trapBlocks)
    (hr : st'.rematConst = st.rematConst) : RStep B st st' :=
  ⟨hv, ha, hf, htr, hr, Nat.le_of_eq hn.symm, fun y n h => by rw [hd]; exact h,
   fun y n h => .inl (by rw [← hd]; exact h), fun y t h => by rw [ht]; exact h, fun y _ => by rw [ht],
   fun y h => Placed.congr hd ha hv h, fun y n h => .inl (by rw [← hd]; exact h)⟩

theorem CInv.congr {st st' : SState} (h : CInv B st) (hd : st'.defs = st.defs)
    (ha : st'.alts = st.alts) (hv : st'.avail = st.avail) (ht : st'.types = st.types)
    (hc : st'.classes = st.classes) : CInv B st' := by
  have hk : ∀ x, st'.known x = st.known x := by intro x; simp [SState.known, hd, hv]
  intro k ms hk'
  rw [hc] at hk'
  obtain ⟨h0, h1⟩ := h k ms hk'
  refine ⟨by rw [hk]; exact h0, fun m hm => ?_⟩
  obtain ⟨e1, e2, e3⟩ := h1 m hm
  refine ⟨by rw [hk]; exact e1, by rw [ht]; exact e2, fun n hn y hy => ?_⟩
  rw [hd] at hn
  exact Placed.congr hd ha hv (e3 n hn y hy)

theorem CInv.step {st st' : SState} (h : CInv B st) (hs : RStep B st st')
    (hc : st'.classes = st.classes) : CInv B st' := by
  intro k ms hk'
  rw [hc] at hk'
  obtain ⟨h0, h1⟩ := h k ms hk'
  refine ⟨hs.known h0, fun m hm => ?_⟩
  obtain ⟨e1, e2, e3⟩ := h1 m hm
  refine ⟨hs.known e1, by rw [hs.typesKnown m e1, hs.typesKnown k h0]; exact e2,
    fun n hn y hy => ?_⟩
  rcases hs.defsNew m n hn with hn0 | hn0
  · exact hs.good y (e3 n hn0 y hy)
  · rw [e1] at hn0; cases hn0

/-- The nodes of a value whose nodes are placeable are typed nodes over placeable values. -/
theorem enodes_nodeIn {st : SState} (h : RInv f V B X XN st) {x : ValueId}
    (hd : ∀ n, st.defs.get? x = some n → ∀ y ∈ operands n, Placed st B y)
    (ha : ∀ ms, st.alts.get? x = some ms → ∀ m ∈ ms, ∀ n, st.defs.get? m = some n →
      ∀ y ∈ operands n, Placed st B y) :
    ∀ n ∈ SState.enodes st x,
      NodeIn (fun y => st.types.get? y) f (Placed st B) (st.types.get? x) n := by
  intro n hn
  simp only [SState.enodes, List.mem_append, Option.mem_toList, List.mem_filterMap] at hn
  rcases hn with hn | ⟨m, hm, hmn⟩
  · obtain ⟨h1, h2, h3⟩ := h.m.defsTy x n hn
    exact ⟨h1, h2, h3.symm, hd n hn⟩
  · cases hax : st.alts.get? x with
    | none => rw [hax] at hm; cases hm
    | some ms =>
      rw [hax] at hm
      obtain ⟨h1, h2, h3⟩ := h.m.defsTy m n hmn
      exact ⟨h1, h2, by rw [← h3, (h.alts x ms hax m hm).2], ha ms hax m hm n hmn⟩

theorem nodeTy_isSome {ty : ValueId → Option Ty} {fn : Function} {n : Inst} (hp : isPure n = true)
    (ht : pureTyped ty fn n = true) : (SState.nodeTy n).isSome := by
  cases n <;> simp_all [isPure, SState.nodeTy, Inst.resultTypes, pureTyped]
  rename_i t _ _
  cases h : t.double? <;> simp_all

/-- Inserting a typed node over placeable values under the fresh `st.next`. -/
theorem insert_rinv {st : SState} (h : RInv f V B X XN st) {allowed : Inst → Bool} {n : Inst}
    (hn : NodeIn (fun y => st.types.get? y) f (Placed st B) (SState.nodeTy n) n) :
    RInv f V B X XN (st.insertNode allowed n).2 ∧ RStep B st (st.insertNode allowed n).2 ∧
      (st.insertNode allowed n).1 = st.next ∧ Placed (st.insertNode allowed n).2 B st.next ∧
      (∀ n' ∈ SState.enodes (st.insertNode allowed n).2 st.next,
        NodeIn (fun y => (st.insertNode allowed n).2.types.get? y) f
          (Placed (st.insertNode allowed n).2 B) ((st.insertNode allowed n).2.types.get? st.next) n') ∧
      (st.insertNode allowed n).2.types.get? st.next = SState.nodeTy n ∧
      (st.insertNode allowed n).2.classes = st.classes ∧
      (st.insertNode allowed n).2.memo = st.memo := by
  obtain ⟨hw, hd, ht, hnx, ha, hal, hm, hf, htr, hr⟩ := insertNode_fields allowed st n
  obtain ⟨hp, hty, -, hops⟩ := hn
  obtain ⟨t, htn⟩ := Option.isSome_iff_exists.1 (nodeTy_isSome hp hty)
  rw [htn] at ht
  have hpar : (st.insertNode allowed n).2.partialVals = st.partialVals := rfl
  have hcl : (st.insertNode allowed n).2.classes = st.classes := rfl
  generalize st.insertNode allowed n = r at hw hd ht hnx ha hal hm hf htr hr hpar hcl ⊢
  obtain ⟨w, st2⟩ := r
  simp only at hw hd ht hnx ha hal hm hf htr hr hpar hcl ⊢
  subst hw
  have hwk : st.known st.next = false := by
    cases hk : st.known st.next with
    | false => rfl
    | true => exact absurd (h.m.knownLt _ hk) (Nat.lt_irrefl _)
  have hdefs : ∀ y, st2.defs.get? y = if st.next = y then some n else st.defs.get? y := by
    intro y; rw [hd, hm_get?_insert']
  have htypes : ∀ y, st2.types.get? y = if st.next = y then some t else st.types.get? y := by
    intro y; rw [ht, hm_get?_insert']
  have hne : ∀ y, st.known y = true → st.next ≠ y := by
    intro y hy he; subst he; rw [hwk] at hy; cases hy
  have kgrow : ∀ y, st.known y = true → st2.known y = true := by
    intro y hy
    rcases known_iff.1 hy with h1 | h1
    · obtain ⟨m, hm'⟩ := Option.isSome_iff_exists.1 h1
      exact known_iff.2 (.inl (by rw [hdefs, ite_eq_right (hne y hy), hm']; rfl))
    · exact known_iff.2 (.inr (by rw [ha]; exact h1))
  have hwk2 : st2.known st.next = true := known_iff.2 (.inl (by rw [hdefs, ite_eq_left rfl]; rfl))
  have tgrow : ∀ y u, st.types.get? y = some u → st2.types.get? y = some u := by
    intro y u hy
    rw [htypes]; split
    · rename_i he; subst he; rw [h.m.typesFresh _ (Nat.le_refl _)] at hy; cases hy
    · exact hy
  have tknown : ∀ y, st.known y = true → st2.types.get? y = st.types.get? y := by
    intro y hy; rw [htypes, ite_eq_right (hne y hy)]
  have hgood : ∀ y, Placed st B y → Placed st2 B y := by
    refine Placed.mono kgrow (fun y hy => hy.not_bad) (fun y m hm' => ?_) (fun y ms hms => ?_)
    · rw [hdefs] at hm'; split at hm'
      · cases hm'; exact .inr hops
      · exact .inl hm'
    · rw [hal] at hms; exact .inl hms
  have hstep : RStep B st st2 := by
    refine ⟨ha, hal, hf, htr, hr, by rw [hnx]; exact Nat.le_succ _, fun y m hm' => ?_,
      fun y m hm' => ?_, tgrow, tknown, hgood, fun y m hm' => ?_⟩
    · have hy : st.known y = true := known_iff.2 (.inl (by rw [hm']; rfl))
      rw [hdefs, ite_eq_right (hne y hy)]; exact hm'
    · rw [hdefs] at hm'; split at hm'
      · rename_i he; subst he; exact .inr hwk
      · exact .inl hm'
    · rw [hdefs] at hm'; split at hm'
      · rename_i he; subst he; exact .inr (by rw [h.m.fn]; exact h.m.maxLt)
      · exact .inl hm'
  have hgw : Placed st2 B st.next := by
    refine Placed.mk (fun hb => absurd (Nat.lt_of_lt_of_le h.m.maxLt (h.m.badLe _ hb)) (Nat.lt_irrefl _))
      hwk2 (fun m hm' y hy => ?_) (fun ms hms => ?_)
    · rw [hdefs, ite_eq_left rfl] at hm'; cases hm'; exact hgood y (hops y hy)
    · rw [hal] at hms
      have := h.m.altsKnown _ ms hms; rw [hwk] at this; cases this
  have hinv : RInv f V B X XN st2 := by
    refine ⟨⟨by rw [hf]; exact h.m.fn, by rw [hnx]; exact Nat.lt_succ_of_lt h.m.maxLt,
      fun y hy => ?_, fun y hy => ?_, fun y m hm' => ?_, fun y ms hms => ?_,
      fun y d hy hb => by rw [ha] at hy; exact h.m.availDef y d hy hb,
      fun y d t' hy => by rw [ha]; exact h.m.defAvail y d t' hy,
      fun y m hm' hav hb => ?_, h.m.badLe, h.m.uniq⟩, fun y => by rw [hpar]; exact h.noPartial y,
      fun n' w hw => ?_, fun y ms hms m hmm => ?_⟩
    · rw [hnx]
      rcases known_iff.1 hy with h1 | h1
      · rw [hdefs] at h1; split at h1
        · rename_i he; subst he; exact Nat.lt_succ_self _
        · exact Nat.lt_succ_of_lt (h.m.knownLt y (known_iff.2 (.inl h1)))
      · rw [ha] at h1; exact Nat.lt_succ_of_lt (h.m.knownLt y (known_iff.2 (.inr h1)))
    · rw [hnx] at hy
      rw [htypes, ite_eq_right (Nat.ne_of_lt (Nat.lt_of_succ_le hy))]
      exact h.m.typesFresh y (Nat.le_of_succ_le hy)
    · rw [hdefs] at hm'; split at hm'
      · rename_i he; subst he; cases hm'
        exact ⟨hp, pureTyped_grow hp hty tgrow, by rw [htypes, ite_eq_left rfl, htn]⟩
      · obtain ⟨e1, e2, e3⟩ := h.m.defsTy y m hm'
        rename_i he
        exact ⟨e1, pureTyped_grow e1 e2 tgrow, by rw [htypes, ite_eq_right he]; exact e3⟩
    · rw [hal] at hms; exact kgrow y (h.m.altsKnown y ms hms)
    · rw [hdefs] at hm'; split at hm'
      · rename_i he; subst he; exact h.m.maxLt
      · rw [ha] at hav; exact h.m.newBig y m hm' hav hb
    · rw [hm] at hw
      obtain ⟨e1, e2, e3⟩ := h.memo n' w hw
      exact ⟨e1.imp (hgood w) id, kgrow w e2, by rw [tknown w e2]; exact e3⟩
    · rw [hal] at hms
      obtain ⟨e1, e2⟩ := h.alts y ms hms m hmm
      exact ⟨kgrow m e1, by rw [tknown m e1, tknown y (h.m.altsKnown y ms hms)]; exact e2⟩
  refine ⟨hinv, hstep, rfl, hgw, ?_, by rw [htypes, ite_eq_left rfl, htn], hcl, hm⟩
  refine enodes_nodeIn hinv (fun m hm' y hy => ?_) (fun ms hms => ?_)
  · rw [hdefs, ite_eq_left rfl] at hm'; cases hm'; exact hgood y (hops y hy)
  · rw [hal] at hms
    have := h.m.altsKnown _ ms hms; rw [hwk] at this; cases this

theorem RInv.memoInsert {st : SState} (h : RInv f V B X XN st) {n : Inst} {b : ValueId}
    (hb : Placed st B b ∨ (X b ∧ XN n)) (hbk : st.known b = true) (hbt : st.types.get? b = SState.nodeTy n) :
    RInv f V B X XN ({ st with memo := st.memo.insert n b } : SState) := by
  refine ⟨h.m.congr rfl rfl rfl rfl rfl rfl, h.noPartial, fun n' w hw => ?_, h.alts⟩
  simp only [hm_get?_insert] at hw
  have hg : ∀ x, Placed st B x → Placed ({ st with memo := st.memo.insert n b } : SState) B x :=
    fun x h => h
  split at hw
  · rename_i he; subst he; cases hw; exact ⟨hb.imp (hg b) id, hbk, hbt⟩
  · obtain ⟨e1, e2, e3⟩ := h.memo n' w hw
    exact ⟨e1.imp (hg w) id, e2, e3⟩

/-- `chooseBest` over candidates that are the root or placeable values of its type. -/
theorem chooseBest_rinv {st : SState} (h : RInv f V B X XN st) {v : ValueId}
    (hvk : st.known v = true) (hv : Placed st B v ∨ X v)
    (hvd : ∀ n, st.defs.get? v = some n → ∀ y ∈ operands n, Placed st B y)
    {cands : List (ValueId × Bool)}
    (hcands : ∀ c ∈ cands, c.1 = v ∨ (Placed st B c.1 ∧ st.types.get? c.1 = st.types.get? v)) :
    RInv f V B X XN (chooseBest st v cands).2 ∧ RStep B st (chooseBest st v cands).2 ∧
      (CInv B st → CInv B (chooseBest st v cands).2) ∧
      ((chooseBest st v cands).1 = v ∨ (Placed (chooseBest st v cands).2 B (chooseBest st v cands).1 ∧
        (chooseBest st v cands).2.types.get? (chooseBest st v cands).1 = st.types.get? v)) ∧
      (chooseBest st v cands).2.memo = st.memo := by
  obtain ⟨hbest, ⟨cl, hcl⟩, hcls⟩ := chooseBest_spec st v cands
  generalize chooseBest st v cands = r at hbest hcl hcls ⊢
  obtain ⟨best, st2⟩ := r
  simp only at hbest hcl hcls ⊢
  subst hcl
  have hbr : best = v ∨ (Placed st B best ∧ st.types.get? best = st.types.get? v) := by
    rcases hbest with h1 | ⟨c, hc', h1⟩
    · exact .inl h1
    · rw [← h1]; exact hcands c hc'
  refine ⟨h.congr rfl rfl rfl rfl rfl rfl rfl rfl, RStep.of_fields rfl rfl rfl rfl rfl rfl rfl rfl,
    fun hc k ms hk => ?_, hbr.imp id (fun h => ⟨h.1, h.2⟩), rfl⟩
  rcases hcls k ms hk with hk | ⟨hkb, hms⟩
  · obtain ⟨h0, h1⟩ := hc k ms hk
    refine ⟨h0, fun m hm => ?_⟩
    obtain ⟨e1, e2, e3⟩ := h1 m hm
    exact ⟨e1, e2, fun n hn y hy => (e3 n hn y hy)⟩
  · rw [hkb]
    have hbk : st.known best = true := by
      rcases hbr with rfl | hb
      · exact hvk
      · exact hb.1.known
    have hbt : st.types.get? best = st.types.get? v := by
      rcases hbr with rfl | hb
      · rfl
      · exact hb.2
    refine ⟨hbk, fun m hm => ?_⟩
    rcases hms m hm with rfl | ⟨c, hc', rfl⟩
    · exact ⟨hvk, hbt.symm, fun n hn y hy => (hvd n hn y hy)⟩
    · rcases hcands c hc' with h1 | h1
      · rw [h1]
        exact ⟨hvk, hbt.symm, fun n hn y hy => (hvd n hn y hy)⟩
      · exact ⟨h1.1.known, by rw [h1.2, hbt], fun n hn y hy => (h1.1.defs n hn y hy)⟩

/-- **The rewriting of a value** (`optimizeAt`) under `SimpRulesOk`: the invariant is kept, the
state grows, and the result is the root or a placeable value of its type. -/
theorem opt_spec {rules : SimplifyFn} (hR : SimpRulesOk rules) (allowed : Inst → Bool) :
    ∀ d st v, RInv f V B X XN st → st.known v = true → (Placed st B v ∨ X v) →
      (∀ n, st.defs.get? v = some n → ∀ y ∈ operands n, Placed st B y) →
      (∀ n ∈ SState.enodes st v,
        NodeIn (fun y => st.types.get? y) f (Placed st B) (st.types.get? v) n) →
      RInv f V B X XN (optimizeAt rules allowed d st v).2 ∧
        RStep B st (optimizeAt rules allowed d st v).2 ∧
        (CInv B st → CInv B (optimizeAt rules allowed d st v).2) ∧
        ((optimizeAt rules allowed d st v).1 = v ∨
          (Placed (optimizeAt rules allowed d st v).2 B (optimizeAt rules allowed d st v).1 ∧
            (optimizeAt rules allowed d st v).2.types.get? (optimizeAt rules allowed d st v).1 =
              st.types.get? v)) := by
  intro d
  induction d with
  | zero => intro st v h _ _ _ _; exact ⟨h, RStep.refl st, id, .inl rfl⟩
  | succ d ih =>
    intro st v h hvk hv hvd hen
    rw [optimizeAt_succ]
    let P : SState → Prop := fun st' => RInv f V B X XN st' ∧ RStep B st st' ∧ (CInv B st → CInv B st')
    have hG : GraphIn SState.enodes (fun st x => st.types.get? x) f P (fun st x => Placed st B x) :=
      fun st1 x hP hx => enodes_nodeIn hP.1 hx.defs hx.alts
    have hM : MakeIn (optMake rules allowed d) (fun st x => st.types.get? x) f P
        (fun st x => Placed st B x) X := by
      intro st1 n hP hn
      obtain ⟨hI1, hS1, hC1⟩ := hP
      have hnok : st1.nodeOk n = true := by
        simp only [SState.nodeOk, List.all_eq_true]
        exact fun y hy => (hn.2.2.2 y hy).known
      unfold optMake
      simp only [hnok, Bool.not_true, Bool.false_eq_true, ite_false]
      cases hmemo : st1.memo.get? n with
      | some w =>
        obtain ⟨e1, e2, e3⟩ := hI1.memo n w hmemo
        exact ⟨⟨hI1, hS1, hC1⟩, ⟨fun _ h => h, fun _ _ h => h⟩, e1.imp id And.left, e3⟩
      | none =>
        have hsolid : st1.solidNode n = true := by
          simp only [SState.solidNode, SState.solid, SState.typedNode, Bool.and_eq_true,
            List.all_eq_true, hI1.noPartial, Bool.not_false]
          refine ⟨fun y hy => ⟨(hn.2.2.2 y hy).known, trivial⟩, hn.1, ?_⟩
          rw [hI1.m.fn]; exact hn.2.1
        simp only [hsolid, Bool.not_true, Bool.false_eq_true, ite_false]
        obtain ⟨hI2, hS2, hw, hgw, hen2, htw, hcl2, hm2⟩ := insert_rinv (allowed := allowed) hI1 hn
        generalize hins : st1.insertNode allowed n = r at hI2 hS2 hw hgw hen2 htw hcl2 hm2 ⊢
        obtain ⟨w, st2⟩ := r
        simp only at hw hI2 hS2 hgw hen2 htw hcl2 hm2 ⊢
        subst hw
        obtain ⟨hI3, hS3, hC3, hb3⟩ := ih st2 st1.next hI2 hgw.known (.inl hgw) hgw.defs hen2
        generalize optimizeAt rules allowed d st2 st1.next = r3 at hI3 hS3 hC3 hb3 ⊢
        obtain ⟨b, st3⟩ := r3
        simp only at hI3 hS3 hC3 hb3 ⊢
        have hgb : Placed st3 B b ∧ st3.types.get? b = SState.nodeTy n := by
          rcases hb3 with rfl | hb
          · exact ⟨hS3.good _ hgw, by rw [hS3.typesKnown _ hgw.known, htw]⟩
          · exact ⟨hb.1, by rw [hb.2, htw]⟩
        have hS4 : RStep B st3 ({ st3 with memo := st3.memo.insert n b } : SState) :=
          RStep.of_fields rfl rfl rfl rfl rfl rfl rfl rfl
        refine ⟨⟨hI3.memoInsert (.inl hgb.1) hgb.1.known hgb.2,
          hS1.trans (hS2.trans (hS3.trans hS4)), fun hc => ?_⟩,
          ⟨fun y hy => hS4.good y (hS3.good y (hS2.good y hy)),
           fun y t hy => hS3.types y t (hS2.types y t hy)⟩, .inl (hgb.1), hgb.2⟩
        have := hC3 (CInv.step (hC1 hc) hS2 hcl2)
        exact this.congr rfl rfl rfl rfl rfl
    have hP0 : P st := ⟨h, RStep.refl st, id⟩
    cases hr : rules SState.enodes (fun st x => st.types.get? x) (optMake rules allowed d) st v with
    | error e =>
      simp only
      exact ⟨h.congr rfl rfl rfl rfl rfl rfl rfl rfl, RStep.of_fields rfl rfl rfl rfl rfl rfl rfl rfl,
        fun hc => hc.congr rfl rfl rfl rfl rfl, .inl (by simp)⟩
    | ok res =>
      obtain ⟨cands, names, st1⟩ := res
      obtain ⟨⟨hI1, hS1, hC1⟩, -, hc⟩ := hR SState.enodes (fun st x => st.types.get? x)
        (optMake rules allowed d) f P (fun st x => Placed st B x) X hG hM st v cands names st1 hP0
        hen hr
      simp only
      let st1' : SState := { st1 with stats := { st1.stats with fired :=
        (names.foldl (fun m n => m.insert n ((m.get? n).getD 0 + 1)) st1.stats.fired) } }
      have hI1' : RInv f V B X XN st1' := hI1.congr rfl rfl rfl rfl rfl rfl rfl rfl
      have hS1' : RStep B st1 st1' := RStep.of_fields rfl rfl rfl rfl rfl rfl rfl rfl
      have hvk1 : st1'.known v = true := hS1'.known (hS1.known hvk)
      have hvd1 : ∀ n, st1'.defs.get? v = some n → ∀ y ∈ operands n, Placed st1' B y := by
        intro n hn y hy
        rcases hS1.defsNew v n hn with hn0 | hn0
        · exact hS1.good y (hvd n hn0 y hy)
        · rw [hvk] at hn0; cases hn0
      have hcands : ∀ c ∈ cands, c.1 = v ∨
          (Placed st1' B c.1 ∧ st1'.types.get? c.1 = st1'.types.get? v) := by
        intro c hc'
        rcases hc c hc' with h1 | h1
        · exact .inl h1
        · exact .inr ⟨h1.1, by rw [h1.2]; exact (hS1.typesKnown v hvk).symm⟩
      obtain ⟨hI2, hS2, hC2, hb2, -⟩ := chooseBest_rinv hI1' hvk1
        (hv.imp (fun h => hS1.good v h) id) hvd1 hcands
      refine ⟨hI2, hS1.trans (hS1'.trans hS2), fun hc0 => hC2 ((hC1 hc0).congr rfl rfl rfl rfl rfl),
        hb2.imp id (fun h => ⟨h.1, by rw [h.2]; exact hS1.typesKnown v hvk⟩)⟩

/-- `make` of the skeleton rules (`skelMake`) on a typed node over placeable values. -/
theorem skelMake_in {rules : SimplifyFn} (hR : SimpRulesOk rules) (allowed : Inst → Bool)
    (st0 : SState) :
    MakeIn (skelMake rules allowed) (fun st x => st.types.get? x) f
      (fun st => RInv f V B (fun _ => False) (fun _ => False) st ∧ RStep B st0 st) (fun st x => Placed st B x)
      (fun _ => False) := by
  intro st1 n hP hn
  obtain ⟨hI1, hS1⟩ := hP
  have hnok : st1.nodeOk n = true := by
    simp only [SState.nodeOk, List.all_eq_true]
    exact fun y hy => (hn.2.2.2 y hy).known
  unfold skelMake
  simp only [hnok, Bool.not_true, Bool.false_eq_true, ite_false]
  cases hmemo : st1.memo.get? n with
  | some w =>
    obtain ⟨e1, e2, e3⟩ := hI1.memo n w hmemo
    exact ⟨⟨hI1, hS1⟩, ⟨fun _ h => h, fun _ _ h => h⟩, e1.imp id And.left, e3⟩
  | none =>
    have hsolid : st1.solidNode n = true := by
      simp only [SState.solidNode, SState.solid, SState.typedNode, Bool.and_eq_true,
        List.all_eq_true, hI1.noPartial, Bool.not_false]
      refine ⟨fun y hy => ⟨(hn.2.2.2 y hy).known, trivial⟩, hn.1, ?_⟩
      rw [hI1.m.fn]; exact hn.2.1
    simp only [hsolid, Bool.not_true, Bool.false_eq_true, ite_false]
    obtain ⟨hI2, hS2, hw, hgw, hen2, htw, -, -⟩ := insert_rinv (allowed := allowed) hI1 hn
    generalize hins : st1.insertNode allowed n = r at hI2 hS2 hw hgw hen2 htw ⊢
    obtain ⟨w, st2⟩ := r
    simp only at hw hI2 hS2 hgw hen2 htw ⊢
    subst hw
    let st2' : SState := { st2 with memo := st2.memo.insert n st1.next }
    have hI2' : RInv f V B (fun _ => False) (fun _ => False) st2' :=
      hI2.memoInsert (.inl hgw) hgw.known htw
    have hS2' : RStep B st2 st2' := RStep.of_fields rfl rfl rfl rfl rfl rfl rfl rfl
    obtain ⟨hI3, hS3, -, hb3⟩ := opt_spec (X := fun _ => False) hR allowed rewriteLimit st2'
      st1.next hI2' hgw.known (.inl hgw) hgw.defs hen2
    generalize optimizeAt rules allowed rewriteLimit st2' st1.next = r3 at hI3 hS3 hb3 ⊢
    obtain ⟨b, st3⟩ := r3
    simp only at hI3 hS3 hb3 ⊢
    have hgb : Placed st3 B b ∧ st3.types.get? b = SState.nodeTy n := by
      rcases hb3 with rfl | hb
      · exact ⟨hS3.good _ (hS2'.good _ hgw), by rw [hS3.typesKnown _ hgw.known]; exact htw⟩
      · exact ⟨hb.1, by rw [hb.2]; exact htw⟩
    have hS4 : RStep B st3 ({ st3 with memo := st3.memo.insert n b } : SState) :=
      RStep.of_fields rfl rfl rfl rfl rfl rfl rfl rfl
    exact ⟨⟨hI3.memoInsert (.inl hgb.1) hgb.1.known hgb.2,
      hS1.trans (hS2.trans (hS2'.trans (hS3.trans hS4)))⟩,
      ⟨fun y hy => hS4.good y (hS3.good y (hS2'.good y (hS2.good y hy))),
       fun y t hy => hS3.types y t (hS2'.types y t (hS2.types y t hy))⟩, .inl hgb.1, hgb.2⟩

/-- **The skeleton rules** (`runSkel`) under `SkelRulesOk`: the chosen simplification mentions
only placeable values. -/
theorem runSkel_ok {rules : SimplifyFn} {skel : SkeletonFn} (hR : SimpRulesOk rules)
    (hK : SkelRulesOk skel) (allowed : Inst → Bool) {st : SState} {i : Isle.Opt.SkelInst}
    (h : RInv f V B (fun _ => False) (fun _ => False) st) (hi : ∀ y ∈ skelOps i, Placed st B y) :
    RInv f V B (fun _ => False) (fun _ => False) (runSkel skel rules allowed st i).2 ∧
      RStep B st (runSkel skel rules allowed st i).2 ∧
      ∀ c, (runSkel skel rules allowed st i).1 = some c →
        SkelCandOk (fun x => (runSkel skel rules allowed st i).2.types.get? x)
          (Placed (runSkel skel rules allowed st i).2 B) i c := by
  unfold runSkel
  by_cases hsk : skelCandidate i = true
  case neg =>
    simp only [Bool.not_eq_true] at hsk
    simp only [hsk, Bool.not_false, ite_true]
    exact ⟨h, RStep.refl st, fun c hc => by cases hc⟩
  simp only [hsk, Bool.not_true, Bool.false_eq_true, ite_false]
  have hI0 : RInv f V B (fun _ => False) (fun _ => False) ({ st with made := {} } : SState) :=
    h.congr rfl rfl rfl rfl rfl rfl rfl rfl
  have hS0 : RStep B st ({ st with made := {} } : SState) :=
    RStep.of_fields rfl rfl rfl rfl rfl rfl rfl rfl
  let P : SState → Prop := fun st' => RInv f V B (fun _ => False) (fun _ => False) st' ∧ RStep B st st'
  have hG : GraphIn SState.enodes (fun st x => st.types.get? x) f P (fun st x => Placed st B x) :=
    fun st1 x hP hx => enodes_nodeIn hP.1 hx.defs hx.alts
  cases hr : skel SState.enodes (fun st x => st.types.get? x) (skelMake rules allowed)
      (fun st b => st.trapBlocks.get? b) ({ st with made := {} } : SState) i with
  | error e =>
    simp only
    exact ⟨h.congr rfl rfl rfl rfl rfl rfl rfl rfl, RStep.of_fields rfl rfl rfl rfl rfl rfl rfl rfl,
      fun c hc => by cases hc⟩
  | ok res =>
    obtain ⟨cands, names, st1⟩ := res
    obtain ⟨⟨hI1, hS1⟩, -, hc⟩ := hK SState.enodes (fun st x => st.types.get? x)
      (skelMake rules allowed) (fun st b => st.trapBlocks.get? b) f P (fun st x => Placed st B x)
      hG (skelMake_in hR allowed st) _ i cands names st1 ⟨hI0, hS0⟩ hi hr
    simp only
    cases hch : chooseSkel i cands with
    | some c' =>
      simp only
      refine ⟨hI1.congr rfl rfl rfl rfl rfl rfl rfl rfl,
        hS1.trans (RStep.of_fields rfl rfl rfl rfl rfl rfl rfl rfl), fun c hcc => ?_⟩
      cases hcc
      exact hc c' (chooseSkel_mem hch)
    | none =>
      simp only
      exact ⟨hI1.congr rfl rfl rfl rfl rfl rfl rfl rfl,
        hS1.trans (RStep.of_fields rfl rfl rfl rfl rfl rfl rfl rfl), fun c hcc => by cases hcc⟩

end Rules

end Opt
