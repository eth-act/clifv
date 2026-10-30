import FV.Backend.Proof.RelocProvCheck
import FV.Backend.Proof.IselExtern
import FV.Backend.Proof.LowerLoopCtx
import FV.Backend.Proof.RelocProvExt

/-!
# Name provenance of the ISLE lowering: the model (L1e, #216)

The meaning of the abstract values of `RelocProvCheck` and the facts the soundness proof needs
about the embedding `sem ctx` (`provModel`, a `Model (sem ctx) true`):

* `γP f a v`: every name inside `v` is an external function name of `f` (if `a.e`), a symbol
  name of `f` (if `a.g`), or anything (if `a.u`); with `a.i` every integer leaf of `v` is a
  reference offset of `f`; with `a.s` every `MInst` inside `v` has its references in `f`
  (`VGood`). It does not depend on the lowering state.
* `RefsSince f s0 s`: the instructions emitted since `s0` have their references in `f` (the
  state invariant).
* `CleanP ctx`: the context's instruction data holds no name and no `MInst` (`cleanP_of_build`,
  `cleanP_termCtx`, `cleanP_tryCtx`); `inst_data_value` gives such data.

The extern helpers are analysed with the splitters of `IselFlowSplit` (one goal per
alternative): `externExtract_prov` (only `func_ref_data` and `symbol_value_data` give names,
external function names and symbol names with their offsets; `inst_data_value` gives the
context's data; every other extractor gives no names and no `MInst`) and `externCtor_prov` (a
constructor's names come from its arguments, it builds `MInst` data only from its arguments or
as a `LoadAddr`, and it emits instructions with references in `f`, `emit` given its argument is
`VGood`). `MInst.ofV` builds a referencing instruction only from the referencing variants
(`ofV_refs`).
-/

namespace Backend.Proof.RelocProv

open Backend Isle Isle.Aarch64

/-! ## Atoms of lists -/

theorem mem_vNamesL {n : String} : ∀ {vs : List V}, n ∈ vNamesL vs ↔ ∃ v ∈ vs, n ∈ vNames v
  | [] => by simp [vNamesL]
  | v :: vs => by simp [vNamesL, mem_vNamesL]

theorem mem_vIntsL {x : Int} : ∀ {vs : List V}, x ∈ vIntsL vs ↔ ∃ v ∈ vs, x ∈ vInts v
  | [] => by simp [vIntsL]
  | v :: vs => by simp [vIntsL, mem_vIntsL]

theorem vGoodL_iff {f : Clif.Function} : ∀ {vs : List V}, VGoodL f vs ↔ ∀ v ∈ vs, VGood f v
  | [] => by simp [VGoodL]
  | v :: vs => by simp [VGoodL, vGoodL_iff]

@[simp] theorem vNames_data (ty : TypeId) (k : Nat) (fs : List V) :
    vNames (.data ty k fs) = vNamesL fs := by simp [vNames]

@[simp] theorem vInts_data (ty : TypeId) (k : Nat) (fs : List V) :
    vInts (.data ty k fs) = vIntsL fs := by simp [vInts]

theorem vGood_data {f : Clif.Function} {ty : TypeId} {k : Nat} {fs : List V} :
    VGood f (.data ty k fs) ↔
      (ty = tyMInst → ∀ m, MInst.ofV (.data ty k fs) = some m → RefsOk f m) ∧ VGoodL f fs := by
  simp [VGood]

/-! ## The meaning of the abstract values -/

/-- **The meaning of an abstract value** in function `f`. -/
def γP (f : Clif.Function) (a : NA) (v : V) : Prop :=
  (∀ n ∈ vNames v, (a.e = true ∧ n ∈ externNames f) ∨ (a.g = true ∧ n ∈ gvNames f) ∨ a.u = true) ∧
    (a.i = true → ∀ x ∈ vInts v, x ∈ refOffs f) ∧ (a.s = true → VGood f v)

theorem γP_top {f : Clif.Function} {v : V} : γP f NA.top v :=
  ⟨fun _ _ => .inr (.inr rfl), fun h => absurd h (by decide), fun h => absurd h (by decide)⟩

/-- A value without names and integer leaves, whose `MInst`s are good. -/
theorem γP_noNames {f : Clif.Function} {a : NA} {v : V} (hn : vNames v = []) (hi : vInts v = [])
    (hg : VGood f v) : γP f a v :=
  ⟨fun n h => (by rw [hn] at h; cases h), fun _ x h => (by rw [hi] at h; cases h), fun _ => hg⟩

theorem γP_inst (f : Clif.Function) (a : NA) (ii : Nat) : γP f a (.inst ii) :=
  γP_noNames (by simp [vNames]) (by simp [vInts]) (by simp [VGood])

/-- **`γP` is monotone** in the order of the domain. -/
theorem γP_le {f : Clif.Function} {a b : NA} {v : V} (hab : a.le b = true) (h : γP f a v) :
    γP f b v := by
  simp only [NA.le, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hab
  obtain ⟨⟨⟨⟨he, hg⟩, hu⟩, hi⟩, hs⟩ := hab
  refine ⟨fun n hn => ?_, fun hb => h.2.1 ?_, fun hb => h.2.2 ?_⟩
  · rcases h.1 n hn with ⟨h1, h2⟩ | ⟨h1, h2⟩ | h1
    · rcases he with he | he
      · rw [he] at h1; cases h1
      · exact .inl ⟨he, h2⟩
    · rcases hg with hg | hg
      · rw [hg] at h1; cases h1
      · exact .inr (.inl ⟨hg, h2⟩)
    · rcases hu with hu | hu
      · rw [hu] at h1; cases h1
      · exact .inr (.inr hu)
  · rcases hi with hi | hi
    · rw [hi] at hb; cases hb
    · exact hi
  · rcases hs with hs | hs
    · rw [hs] at hb; cases hb
    · exact hs

theorem le_join_left (a b : NA) : a.le (a.join b) = true := by
  obtain ⟨e1, g1, u1, i1, s1⟩ := a
  obtain ⟨e2, g2, u2, i2, s2⟩ := b
  simp only [NA.le, NA.join]
  cases e1 <;> cases g1 <;> cases u1 <;> cases i1 <;> cases s1 <;> simp

theorem le_join_right (a b : NA) : b.le (a.join b) = true := by
  obtain ⟨e1, g1, u1, i1, s1⟩ := a
  obtain ⟨e2, g2, u2, i2, s2⟩ := b
  simp only [NA.le, NA.join]
  cases e2 <;> cases g2 <;> cases u2 <;> cases i2 <;> cases s2 <;> simp

theorem γP_join_left {f : Clif.Function} {a v} (b : NA) (h : γP f a v) : γP f (a.join b) v :=
  γP_le (le_join_left a b) h

theorem γP_join_right {f : Clif.Function} {b v} (a : NA) (h : γP f b v) : γP f (a.join b) v :=
  γP_le (le_join_right a b) h

/-! ## The join of a list -/

theorem foldl_join_fields : ∀ (as : List NA) (a : NA),
    (as.foldl NA.join a).e = (a.e || as.any (·.e)) ∧ (as.foldl NA.join a).g = (a.g || as.any (·.g)) ∧
    (as.foldl NA.join a).u = (a.u || as.any (·.u)) ∧ (as.foldl NA.join a).i = (a.i && as.all (·.i)) ∧
    (as.foldl NA.join a).s = (a.s && as.all (·.s))
  | [], a => by simp
  | b :: bs, a => by
    rw [List.foldl_cons]
    obtain ⟨h1, h2, h3, h4, h5⟩ := foldl_join_fields bs (a.join b)
    rw [h1, h2, h3, h4, h5]
    simp [NA.join, Bool.or_assoc, Bool.and_assoc]

theorem joinAll_e (as : List NA) : (joinAll as).e = as.any (·.e) := by
  rw [joinAll, (foldl_join_fields as NA.c0).1]; simp [NA.c0]
theorem joinAll_g (as : List NA) : (joinAll as).g = as.any (·.g) := by
  rw [joinAll, (foldl_join_fields as NA.c0).2.1]; simp [NA.c0]
theorem joinAll_u (as : List NA) : (joinAll as).u = as.any (·.u) := by
  rw [joinAll, (foldl_join_fields as NA.c0).2.2.1]; simp [NA.c0]
theorem joinAll_i (as : List NA) : (joinAll as).i = as.all (·.i) := by
  rw [joinAll, (foldl_join_fields as NA.c0).2.2.2.1]; simp [NA.c0]
theorem joinAll_s (as : List NA) : (joinAll as).s = as.all (·.s) := by
  rw [joinAll, (foldl_join_fields as NA.c0).2.2.2.2]; simp [NA.c0]

/-- A member of a list describes its values in the join of the list. -/
theorem γP_joinAll {f : Clif.Function} {a : NA} {as : List NA} {v : V} (ha : a ∈ as)
    (h : γP f a v) : γP f (joinAll as) v := by
  refine ⟨fun n hn => ?_, fun hi => h.2.1 ?_, fun hs => h.2.2 ?_⟩
  · rcases h.1 n hn with ⟨h1, h2⟩ | ⟨h1, h2⟩ | h1
    · exact .inl ⟨by rw [joinAll_e]; exact List.any_eq_true.mpr ⟨a, ha, h1⟩, h2⟩
    · exact .inr (.inl ⟨by rw [joinAll_g]; exact List.any_eq_true.mpr ⟨a, ha, h1⟩, h2⟩)
    · exact .inr (.inr (by rw [joinAll_u]; exact List.any_eq_true.mpr ⟨a, ha, h1⟩))
  · rw [joinAll_i] at hi; exact List.all_eq_true.mp hi a ha
  · rw [joinAll_s] at hs; exact List.all_eq_true.mp hs a ha

/-! ## Pointwise descriptions -/

section Holds
variable {σ : Type} {f : Clif.Function} {st : σ}

theorem holds2_mem {γ : NA → σ → V → Prop} : ∀ {as : List NA} {vs : List V},
    Holds2 γ st as vs → ∀ v ∈ vs, ∃ a ∈ as, γ a st v
  | [], [], _ => fun _ h => by cases h
  | a :: as, v :: vs, ⟨h1, h2⟩ => by
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact ⟨a, List.mem_cons_self, h1⟩
    · obtain ⟨b, hb, h⟩ := holds2_mem h2 w hw
      exact ⟨b, List.mem_cons_of_mem _ hb, h⟩
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h

/-- The names of described values: from the sources of the join. -/
theorem args_names {as : List NA} {vs : List V}
    (h : Holds2 (fun a (_ : σ) v => γP f a v) st as vs) :
    ∀ n ∈ vNamesL vs, ((joinAll as).e = true ∧ n ∈ externNames f) ∨
      ((joinAll as).g = true ∧ n ∈ gvNames f) ∨ (joinAll as).u = true := by
  intro n hn
  obtain ⟨v, hv, hn⟩ := mem_vNamesL.mp hn
  obtain ⟨a, ha, hav⟩ := holds2_mem h v hv
  exact (γP_joinAll ha hav).1 n hn

theorem args_ints {as : List NA} {vs : List V}
    (h : Holds2 (fun a (_ : σ) v => γP f a v) st as vs) (hi : (joinAll as).i = true) :
    ∀ x ∈ vIntsL vs, x ∈ refOffs f := by
  intro x hx
  obtain ⟨v, hv, hx⟩ := mem_vIntsL.mp hx
  obtain ⟨a, ha, hav⟩ := holds2_mem h v hv
  exact (γP_joinAll ha hav).2.1 hi x hx

theorem args_good_all {as : List NA} {vs : List V}
    (h : Holds2 (fun a (_ : σ) v => γP f a v) st as vs) (hs : ∀ a ∈ as, a.s = true) :
    VGoodL f vs := by
  refine vGoodL_iff.mpr fun v hv => ?_
  obtain ⟨a, ha, hav⟩ := holds2_mem h v hv
  exact hav.2.2 (hs a ha)

theorem args_good {as : List NA} {vs : List V}
    (h : Holds2 (fun a (_ : σ) v => γP f a v) st as vs) (hs : (joinAll as).s = true) :
    VGoodL f vs := by
  rw [joinAll_s] at hs
  exact args_good_all h fun a ha => List.all_eq_true.mp hs a ha

end Holds

/-! ## Instructions emitted since a state -/

/-- **The instructions emitted since `s0`** have their references in `f`. -/
def RefsSince (f : Clif.Function) (s0 s : LState) : Prop :=
  ∃ ms : List MInst, s.emitted = s0.emitted ++ ms.toArray ∧ ∀ m ∈ ms, RefsOk f m

theorem refsSince_refl (f : Clif.Function) (s : LState) : RefsSince f s s :=
  ⟨[], by simp, by simp⟩

theorem refsSince_of_eq {f : Clif.Function} {s s' : LState} (h : s'.emitted = s.emitted) :
    RefsSince f s s' :=
  ⟨[], by simp [h], by simp⟩

theorem refsSince_trans {f : Clif.Function} {a b c : LState} (h1 : RefsSince f a b)
    (h2 : RefsSince f b c) : RefsSince f a c := by
  obtain ⟨ms1, e1, o1⟩ := h1
  obtain ⟨ms2, e2, o2⟩ := h2
  refine ⟨ms1 ++ ms2, by rw [e2, e1]; simp, fun m hm => ?_⟩
  rcases List.mem_append.mp hm with hm | hm
  · exact o1 m hm
  · exact o2 m hm

/-- Emitting an instruction with references in `f`. -/
theorem refsSince_emit {f : Clif.Function} {s0 s : LState} {m : MInst} (h0 : RefsSince f s0 s)
    (h : RefsOk f m) : RefsSince f s0 (s.emit m) :=
  refsSince_trans h0 ⟨[m], by simp [LState.emit], by simp [h]⟩

/-- Every instruction emitted by a state reached from one whose instructions are good is good. -/
theorem refsSince_all {f : Clif.Function} {s0 s : LState} (h : RefsSince f s0 s)
    (h0 : ∀ m ∈ s0.emitted.toList, RefsOk f m) : ∀ m ∈ s.emitted.toList, RefsOk f m := by
  obtain ⟨ms, he, hms⟩ := h
  intro m hm
  rw [he] at hm
  simp only [Array.toList_append, List.mem_append] at hm
  rcases hm with hm | hm
  · exact h0 m hm
  · exact hms m (by simpa using hm)

/-! ## `MInst.ofV` -/

/-- What `MInst.ofV` builds from variant `k` with fields `fs`: an instruction without
references, or a call of a `CallInfo` field, or an address load of an external-name field (with
an integer field as offset). -/
def OfVRefs (f : Clif.Function) (k : Nat) (fs : List V) (m : MInst) : Prop :=
  RefsOk f m ∨
  (∃ i c, fs = [i] ∧ (k = VIdx.MInst.Call ∨ k = VIdx.MInst.CallInd) ∧ i.callInfo? = some c ∧
    m = .call c) ∨
  (∃ rd nm r n, fs = [rd, nm] ∧ k = VIdx.MInst.LoadExtNameGot ∧ nm.extName? = some n ∧
    m = .loadExtNameGot r n) ∨
  (∃ rd nm o r n x, fs = [rd, nm, o] ∧ k = VIdx.MInst.LoadExtNameNear ∧ nm.extName? = some n ∧
    o.int? = some x ∧ m = .loadExtNameNear r n x)

/-- **`MInst.ofV`** builds a referencing instruction only from the referencing variants. -/
theorem ofV_refs (f : Clif.Function) {v : V} {m : MInst} (h : MInst.ofV v = some m) :
    ∃ k fs, v = .data tyMInst k fs ∧ OfVRefs f k fs m := by
  unfold MInst.ofV at h
  obtain ⟨⟨k, fs⟩, he, h2⟩ := Flow.bind_some_ex h
  clear h
  refine ⟨k, fs, Flow.enumOf_eq he, ?_⟩
  revert h2
  revert m
  apply ofV_split _ (fun k fs (r : Option MInst) => ∀ m, r = some m → OfVRefs f k fs m)
  all_goals
    intros
    rename_i m hm
    try simp only at hm
    repeat' (first | (obtain ⟨_, _, hm⟩ := Flow.bind_some_ex hm) | split at hm)
    all_goals first
      | (cases hm; done)
      | (simp only [pure, Option.some.injEq] at hm
         subst hm
         first
           | exact .inl trivial
           | exact .inr (.inl ⟨_, _, rfl, by decide, by assumption, rfl⟩)
           | exact .inr (.inr (.inl ⟨_, _, _, _, rfl, rfl, by assumption, rfl⟩))
           | exact .inr (.inr (.inr ⟨_, _, _, _, _, _, rfl, rfl, by assumption, by assumption, rfl⟩)))

/-- A good value decodes to an instruction with references in `f`. -/
theorem ofV_good {f : Clif.Function} {v : V} {m : MInst} (hg : VGood f v)
    (h : MInst.ofV v = some m) : RefsOk f m := by
  obtain ⟨k, fs, rfl, -⟩ := ofV_refs f h
  exact (vGood_data.mp hg).1 rfl m h

/-- A variant other than the referencing ones decodes to an instruction without references. -/
theorem ofV_other {f : Clif.Function} {k : Nat} {fs : List V} {m : MInst}
    (h : MInst.ofV (.data tyMInst k fs) = some m)
    (hk : k ≠ VIdx.MInst.Call ∧ k ≠ VIdx.MInst.CallInd ∧ k ≠ VIdx.MInst.LoadExtNameGot ∧
      k ≠ VIdx.MInst.LoadExtNameNear) : RefsOk f m := by
  obtain ⟨k', fs', he, hr⟩ := ofV_refs f h
  cases he
  rcases hr with hr | ⟨_, _, _, hk', _⟩ | ⟨_, _, _, _, _, hk', _⟩ | ⟨_, _, _, _, _, _, _, hk', _⟩
  · exact hr
  · rcases hk' with hk' | hk'
    · exact absurd hk' hk.1
    · exact absurd hk' hk.2.1
  · exact absurd hk' hk.2.2.1
  · exact absurd hk' hk.2.2.2

theorem callInfo_names {i : V} {c : CallInfo} {n : String} (h : i.callInfo? = some c)
    (hd : c.dest = .sym n) : n ∈ vNames i := by
  cases i <;> simp [V.callInfo?] at h
  rename_i o
  cases o <;> simp at h
  subst h
  simp [vNames, opNames, hd]

theorem extName_names {i : V} {n : String} (h : i.extName? = some n) : n ∈ vNames i := by
  cases i <;> simp [V.extName?] at h
  rename_i o
  cases o <;> simp at h
  subst h
  simp [vNames, opNames]

theorem int_ints {i : V} {x : Int} (h : i.int? = some x) : x ∈ vInts i := by
  cases i <;> simp [V.int?] at h
  subst h
  simp [vInts]

/-! ## Building data -/

theorem refChk_call {k : Nat} {as : List NA}
    (hk : k = VIdx.MInst.Call ∨ k = VIdx.MInst.CallInd) (h : refChk k as = true) :
    ∃ ci, as = [ci] ∧ ci.g = false ∧ ci.u = false := by
  have hc : (k == VIdx.MInst.Call || k == VIdx.MInst.CallInd) = true := by
    rcases hk with rfl | rfl <;> decide
  unfold refChk at h
  simp only [hc, ↓reduceIte] at h
  split at h
  · rename_i ci
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    exact ⟨ci, rfl, h.1, h.2⟩
  · cases h

theorem refChk_got {k : Nat} {as : List NA} (hk : k = VIdx.MInst.LoadExtNameGot)
    (h : refChk k as = true) : ∃ a nm, as = [a, nm] ∧ nm.u = false := by
  subst hk
  unfold refChk at h
  split at h
  · rename_i hc; exact absurd hc (by decide)
  split at h
  · split at h
    · rename_i a nm
      simp only [Bool.not_eq_true'] at h
      exact ⟨a, nm, rfl, h⟩
    · cases h
  · rename_i hc; exact absurd hc (by decide)

theorem refChk_near {k : Nat} {as : List NA} (hk : k = VIdx.MInst.LoadExtNameNear)
    (h : refChk k as = true) : ∃ a nm o, as = [a, nm, o] ∧ nm.u = false ∧ o.i = true := by
  subst hk
  unfold refChk at h
  split at h
  · rename_i hc; exact absurd hc (by decide)
  split at h
  · rename_i hc; exact absurd hc (by decide)
  split at h
  · split at h
    · rename_i a nm o
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
      exact ⟨a, nm, o, rfl, h.1, h.2⟩
    · cases h
  · rename_i hc; exact absurd hc (by decide)

/-- A name of a value described by an abstract value without `u`: a declared name. -/
theorem refName_of {f : Clif.Function} {a : NA} {v : V} {n : String} (h : γP f a v)
    (hu : a.u = false) (hn : n ∈ vNames v) : n ∈ refNames f := by
  rcases h.1 n hn with ⟨_, h⟩ | ⟨_, h⟩ | h
  · exact List.mem_append_left _ h
  · exact List.mem_append_right _ h
  · rw [hu] at h; cases h

theorem amk_fields (ty : TypeId) (k : Nat) (as : List NA) :
    (amk ty k as).e = (joinAll as).e ∧ (amk ty k as).g = (joinAll as).g ∧
      (amk ty k as).u = (joinAll as).u ∧ (amk ty k as).i = (joinAll as).i ∧
      ((amk ty k as).s = true → (joinAll as).s = true ∧ (ty = tyMInst → refChk k as = true)) := by
  unfold amk
  split
  · rename_i hty
    refine ⟨rfl, rfl, rfl, rfl, fun h => ?_⟩
    simp only [Bool.and_eq_true] at h
    exact ⟨h.1, fun _ => h.2⟩
  · rename_i hty
    exact ⟨rfl, rfl, rfl, rfl, fun h => ⟨h, fun e => absurd (beq_iff_eq.mpr e) hty⟩⟩

/-- **Building data**: `amk` describes the built value. -/
theorem γP_mkd {σ : Type} {f : Clif.Function} {st : σ} {ty : TypeId} {k : Nat} {as : List NA}
    {vs : List V} (h : Holds2 (fun a (_ : σ) v => γP f a v) st as vs) :
    γP f (amk ty k as) (.data ty k vs) := by
  obtain ⟨he, hg, hu, hi, hs⟩ := amk_fields ty k as
  refine ⟨fun n hn => ?_, fun hi' => ?_, fun hs' => ?_⟩
  · rw [he, hg, hu]
    exact args_names h n (by simpa using hn)
  · rw [hi] at hi'
    simpa using args_ints h hi'
  · obtain ⟨hj, hr⟩ := hs hs'
    refine vGood_data.mpr ⟨fun hty m hm => ?_, args_good h hj⟩
    subst hty
    have hc := hr rfl
    obtain ⟨k', fs', he', hrefs⟩ := ofV_refs f hm
    cases he'
    rcases hrefs with hrefs | ⟨i, c, rfl, hk, hc', rfl⟩ | ⟨rd, nm, r, n, rfl, hk, hn, rfl⟩ |
      ⟨rd, nm, o, r, n, x, rfl, hk, hn, hx, rfl⟩
    · exact hrefs
    · obtain ⟨ci, rfl, hcg, hcu⟩ := refChk_call hk hc
      obtain ⟨hci, -⟩ := h
      intro n hd
      rcases hci.1 n (callInfo_names hc' hd) with ⟨_, h⟩ | ⟨h, _⟩ | h
      · exact h
      · rw [hcg] at h; cases h
      · rw [hcu] at h; cases h
    · obtain ⟨a, anm, rfl, hnu⟩ := refChk_got hk hc
      obtain ⟨-, hnm, -⟩ := h
      exact refName_of hnm hnu (extName_names hn)
    · obtain ⟨a, anm, ao, rfl, hnu, hoi⟩ := refChk_near hk hc
      obtain ⟨-, hnm, ho, -⟩ := h
      exact ⟨refName_of hnm hnu (extName_names hn), ho.2.1 hoi x (int_ints hx)⟩

/-! ## Extern constructors -/

/-- What one extern constructor call `id args` from `st` returning `v` in `st'` does to names,
`MInst`s and the emitted instructions. -/
structure CtorSpec (ctx : Ctx) (id : TermId) (args : List V) (st : LState) (v : V) (st' : LState) :
    Prop where
  names : ∀ n ∈ vNames v, n ∈ vNamesL args
  good : VGoodL ctx.func args → VGood ctx.func v
  emit : (id = TId.emit → VGoodL ctx.func args) → RefsSince ctx.func st st'

/-- `CtorSpec` of every successful result of a constructor call. -/
def CtorSpecP (ctx : Ctx) (st : LState) (id : TermId) (args : List V)
    (r : ExtResult (V × LState)) : Prop :=
  ∀ v st', r = .ok (v, st') → CtorSpec ctx id args st v st'

theorem ctorSpec_noEmit {ctx : Ctx} {id : TermId} {args : List V} {st st' : LState} {v : V}
    (he : st'.emitted = st.emitted) (hn : ∀ n ∈ vNames v, n ∈ vNamesL args)
    (hg : VGoodL ctx.func args → VGood ctx.func v) : CtorSpec ctx id args st v st' :=
  ⟨hn, hg, fun _ => refsSince_of_eq he⟩

theorem ctorSpec_emit {ctx : Ctx} {id : TermId} {i : V} {st : LState} {m : MInst}
    (hid : id = TId.emit) (h : MInst.ofV i = some m) :
    CtorSpec ctx id [i] st (.op .unit) (st.emit m) :=
  ⟨by simp [vNames, opNames], fun _ => by simp [VGood],
    fun hg => refsSince_emit (refsSince_refl _ _) (ofV_good (vGoodL_iff.mp (hg hid) i (by simp)) h)⟩

theorem ctorSpec_emitOk {ctx : Ctx} {id : TermId} {args : List V} {st : LState} {m : MInst}
    (h : RefsOk ctx.func m) : CtorSpec ctx id args st (.op .unit) (st.emit m) :=
  ⟨by simp [vNames, opNames], fun _ => by simp [VGood],
    fun _ => refsSince_emit (refsSince_refl _ _) h⟩

theorem ctorSpec_reg {ctx : Ctx} {id : TermId} {args : List V} {st st' : LState} {r : Reg}
    (h : RefsSince ctx.func st st') : CtorSpec ctx id args st (.reg r) st' :=
  ⟨by simp [vNames], fun _ => by simp [VGood], fun _ => h⟩

/-- `loadConstantFull` emits `movz`/`movn` and `movk`s. -/
theorem loadConstantFull_refs (f : Clif.Function) (bits : Nat) (se : Bool) (sz : OperandSize)
    (value : Nat) (st : LState) : RefsSince f st (loadConstantFull bits se sz value st).2 := by
  unfold loadConstantFull
  dsimp only
  refine Flow.foldl_inv (fun x : Reg × LState × Nat => RefsSince f st x.2.1) _ _ _ ?_ ?_
  · exact refsSince_emit (refsSince_of_eq rfl) trivial
  · intro sh _ x hx
    refine Flow.ite_inv (I := fun x : Reg × LState × Nat => RefsSince f st x.2.1)
      (fun _ => hx) fun _ => ?_
    refine Flow.ite_inv (I := fun x : Reg × LState × Nat => RefsSince f st x.2.1)
      (fun _ => ?_) fun _ => hx
    exact refsSince_emit (refsSince_trans hx (refsSince_of_eq rfl)) trivial

/-- `gen_call_output`: fresh registers. -/
theorem ctorSpec_callOutput {ctx : Ctx} {id : TermId} {args : List V} {st : LState} {β : Type}
    (F : Array (List Reg) × LState → β → Array (List Reg) × LState) (l : List β)
    (hF : ∀ a b, ∃ c, F a b = (a.1.push [(a.2.fresh c).1], (a.2.fresh c).2)) :
    CtorSpec ctx id args st (.regsVec (l.foldl F (#[], st)).1.toList) (l.foldl F (#[], st)).2 := by
  have := Flow.foldl_inv (fun a : Array (List Reg) × LState => a.2.emitted = st.emitted)
    F l (#[], st) rfl (by intro b _ a h; obtain ⟨c, hc⟩ := hF a b; rw [hc]; exact h)
  exact ctorSpec_noEmit this (by simp [vNames]) (fun _ => by simp [VGood])

/-- `gen_call_args`: stores of the stack arguments. -/
theorem ctorSpec_callArgs {ctx : Ctx} {id : TermId} {args : List V} {st : LState}
    (F : Array (Reg × Reg) × LState → (ArgLoc × Reg) × Nat → Array (Reg × Reg) × LState)
    (l : List ((ArgLoc × Reg) × Nat))
    (hF : ∀ a b, F a b = match b.1.1 with
      | .reg p => (a.1.push (b.1.2, p), a.2)
      | .stack off => (a.1, a.2.emit (stackArgStore b.1.2 b.2 (.spOffset off)))) :
    CtorSpec ctx id args st (.op (.callArgs (l.foldl F (#[], st)).1.toList)) (l.foldl F (#[], st)).2 := by
  have := Flow.foldl_inv (fun a : Array (Reg × Reg) × LState => RefsSince ctx.func st a.2)
    F l (#[], st) (refsSince_refl _ _) (by
      intro b _ a h
      rw [hF]
      split
      · exact h
      · exact refsSince_emit h (by unfold stackArgStore; split <;> trivial))
  exact ⟨by simp [vNames, opNames], fun _ => by simp [VGood], fun _ => this⟩

/-- `abi_stackslot_addr`: a `LoadAddr` of its register argument. -/
theorem ctorSpec_loadAddr {ctx : Ctx} {id : TermId} {st : LState} {rd a b : V} {k : Nat} {x : Int} :
    CtorSpec ctx id [rd, a, b] st
      (.data tyMInst VIdx.MInst.LoadAddr [rd, .data tyAMode k [.int x]]) st := by
  refine ctorSpec_noEmit rfl (fun n hn => ?_) fun hg => ?_
  · simp only [vNamesL, vNames, List.append_nil, List.mem_append] at hn ⊢
    exact .inl hn
  refine vGood_data.mpr ⟨fun _ m hm => ofV_other hm (by decide), ?_⟩
  have hrd : VGood ctx.func rd := vGoodL_iff.mp hg rd (by simp)
  refine vGoodL_iff.mpr fun w hw => ?_
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
  rcases hw with rfl | rfl
  · exact hrd
  · exact vGood_data.mpr ⟨fun h => absurd h (by decide), by simp [VGoodL, VGood]⟩

/-- Close `CtorSpec` of a constructor that emits nothing. -/
macro "ctor_plain" : tactic => `(tactic| (refine ctorSpec_noEmit rfl ?_ ?_ <;> simp_all (config := { decide := true }) [vNames, vNamesL, opNames, VGood, VGoodL] <;> done))

set_option maxHeartbeats 2000000 in
/-- **Every extern constructor** satisfies `CtorSpec`. -/
theorem externCtor_prov (ctx : Ctx) (t : Term) (args : List V) (st : LState) :
    CtorSpecP ctx st t.id args (externCtor ctx t args st) := by
  unfold externCtor
  split
  · intro v st' h
    split at h
    · cases h
      exact ctorSpec_noEmit rfl (by simp [vNames]) (fun _ => by simp [VGood])
    · cases h
  · apply externCtor_split _ (CtorSpecP ctx st)
    all_goals
      intros
      unfold CtorSpecP
      intro v st' h
      try dsimp only at h
      repeat' (split at h)
      all_goals try (cases h; done)
    all_goals cases h
    all_goals first
      | ctor_plain
      | (rename_i heq; simp only [Option.map_eq_some_iff, Function.comp_apply] at heq
         obtain ⟨_, _, rfl⟩ := heq; ctor_plain)
      | exact ctorSpec_emit rfl ‹_›
      | exact ctorSpec_emitOk (by trivial)
      | exact ctorSpec_reg (loadConstantFull_refs _ _ _ _ _ _)
      | exact ctorSpec_reg (refsSince_of_eq rfl)
      | exact ctorSpec_callOutput _ _ (fun _ _ => ⟨_, rfl⟩)
      | exact ctorSpec_callArgs _ _ (fun _ _ => rfl)
      | exact ctorSpec_loadAddr

/-! ## The context's instruction data -/

/-- A value without names and without `MInst`s. -/
def PlainV (f : Clif.Function) (v : V) : Prop := vNames v = [] ∧ VGood f v

/-- `PlainV` of every value of a list. -/
def PlainL (f : Clif.Function) (fs : List V) : Prop := ∀ w ∈ fs, PlainV f w

theorem plainL_names {f : Clif.Function} : ∀ {fs : List V}, (∀ w ∈ fs, PlainV f w) → vNamesL fs = []
  | [], _ => rfl
  | w :: ws, h => by
    simp only [vNamesL, List.append_eq_nil_iff]
    exact ⟨(h w List.mem_cons_self).1, plainL_names fun g hg => h g (List.mem_cons_of_mem _ hg)⟩

theorem plain_data {f : Clif.Function} {ty : TypeId} {k : Nat} {fs : List V} (hty : ty ≠ tyMInst)
    (h : ∀ w ∈ fs, PlainV f w) : PlainV f (.data ty k fs) :=
  ⟨by simp [plainL_names h], vGood_data.mpr ⟨fun e => absurd e hty,
    vGoodL_iff.mpr fun w hw => (h w hw).2⟩⟩

theorem plain_mkVariant {f : Clif.Function} {ty : TypeId} {name : String} {fs : List V}
    (hty : ty ≠ tyMInst) (h : PlainL f fs) : PlainV f (mkVariant ty name fs) := by
  unfold mkVariant
  split
  · exact plain_data hty h
  · exact ⟨by simp [vNames, opNames], by simp [VGood]⟩

theorem plainL_nil {f : Clif.Function} : PlainL f [] := fun _ h => by cases h

theorem plainL_cons {f : Clif.Function} {w : V} {ws : List V} (h1 : PlainV f w)
    (h2 : PlainL f ws) : PlainL f (w :: ws) := by
  intro v hv
  rcases List.mem_cons.mp hv with rfl | hv
  · exact h1
  · exact h2 v hv

theorem plain_int {f : Clif.Function} {i : Int} : PlainV f (.int i) :=
  ⟨by simp [vNames], by simp [VGood]⟩
theorem plain_value {f : Clif.Function} {x : Nat} : PlainV f (.value x) :=
  ⟨by simp [vNames], by simp [VGood]⟩
theorem plain_values {f : Clif.Function} {xs : List Nat} : PlainV f (.values xs) :=
  ⟨by simp [vNames], by simp [VGood]⟩
theorem plain_blockCalls {f : Clif.Function} {bs : List Nat} : PlainV f (.blockCalls bs) :=
  ⟨by simp [vNames], by simp [VGood]⟩
theorem plain_op {f : Clif.Function} {o : Opnd} (h : opNames o = []) : PlainV f (.op o) :=
  ⟨by simp [vNames, h], by simp [VGood]⟩

/-- Build `PlainV` of an `instDataV` term. -/
macro "plain_ok" : tactic => `(tactic| (
  unfold instDataV opcodeV
  repeat' first
    | with_reducible apply plain_mkVariant (by decide)
    | with_reducible exact plainL_nil
    | with_reducible apply plainL_cons
    | with_reducible exact plain_int
    | with_reducible exact plain_value
    | with_reducible exact plain_values
    | with_reducible exact plain_blockCalls
    | with_reducible exact plain_op rfl))

set_option maxRecDepth 20000 in
/-- **The data of a statement** has no names and no `MInst`s. -/
theorem instData_plain (g : Clif.Function) {f : Clif.Function} {c : Clif.Inst} {d : V}
    (h : instData f c = .ok d) : PlainV g d := by
  cases c <;> simp only [instData] at h
  all_goals (repeat' split at h)
  all_goals first
    | (simp only [throw, throwThe, MonadExceptOf.throw, reduceCtorEq] at h)
    | (simp only [pure, Except.pure, Except.ok.injEq] at h
       subst h
       plain_ok)

/-- **The data of a terminator** (`termData`). -/
theorem termData_plain (g : Clif.Function) {t : Clif.Terminator} {d : V} (h : termData t = .ok d) :
    PlainV g d := by
  cases t <;> simp only [termData] at h
  all_goals first
    | (simp only [throw, throwThe, MonadExceptOf.throw, reduceCtorEq] at h)
    | (simp only [pure, Except.pure, Except.ok.injEq] at h
       subst h
       plain_ok)

set_option maxRecDepth 20000 in
/-- **The data of a `try_call`** (`tryCallData`). -/
theorem tryCallData_plain (g : Clif.Function) {f : Clif.Function} {t : Clif.Terminator} {d : V}
    (h : tryCallData f t = .ok d) : PlainV g d := by
  cases t <;> simp only [tryCallData] at h
  all_goals first
    | (simp only [throw, throwThe, MonadExceptOf.throw, reduceCtorEq] at h; done)
    | skip
  all_goals
    rename_i et
    cases he : exnTableOpnd f et with
    | error e => rw [he] at h; cases h
    | ok q =>
      rw [he] at h
      obtain ⟨sig, items⟩ := q
      simp only [bind, Except.bind] at h
      repeat' split at h
      all_goals first
        | (simp only [throw, throwThe, MonadExceptOf.throw, reduceCtorEq] at h; done)
        | (simp only [pure, Except.pure, Except.ok.injEq] at h
           subst h
           plain_ok)

/-- **The context's instruction data has no names and no `MInst`s.** -/
def CleanP (ctx : Ctx) : Prop :=
  ∀ (j : Nat) (info : IInfo), ctx.insts[j]? = some info →
    vNames info.data = [] ∧ VGood ctx.func info.data

/-- **`buildCtx`'s context is clean**: its entries are the terminators' placeholders and the
statements' `instData`. -/
theorem cleanP_of_build {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)}
    {st0 : LState} (hb : buildCtx f = .ok (ctx, ranges, st0)) : CleanP ctx := by
  have sp := Driver.ctxSpec_of hb
  intro i info hi
  rcases sp.insts info (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hi)) with
    rfl | ⟨B, hB, s, hs, rfl⟩
  · exact ⟨rfl, trivial⟩
  · obtain ⟨d, hd⟩ := ((sp.blockC B hB).2 s hs).1
    have hdo : (Driver.infoOf f s).data = d := by
      show Driver.dataOf f s = d
      unfold Driver.dataOf
      rw [hd]
    rw [hdo]
    exact instData_plain ctx.func hd

/-- Setting a terminator slot to plain data keeps the context clean. -/
theorem cleanP_set {ctx : Ctx} (hcl : CleanP ctx) {ti : Nat} {data : V} (hp : PlainV ctx.func data) :
    CleanP (Driver.termCtx ctx ti data) := by
  intro j info hj
  by_cases hji : j = ti
  · subst hji
    by_cases hlt : j < ctx.insts.size
    · have : (Driver.termCtx ctx j data).insts[j]? = some ⟨data, [], [], none⟩ := by
        show (ctx.insts.set! j _)[j]? = _
        rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt hlt]
      rw [this] at hj
      cases hj
      exact hp
    · have : (Driver.termCtx ctx j data).insts = ctx.insts := by
        show ctx.insts.set! j _ = _
        rw [Array.set!_eq_setIfInBounds, Array.setIfInBounds]
        simp [hlt]
      rw [this] at hj
      exact hcl j info hj
  · rw [Driver.termCtx_insts_ne hji] at hj
    exact hcl j info hj

/-- A terminator's data at its slot keeps the context clean. -/
theorem cleanP_termCtx {ctx : Ctx} (hcl : CleanP ctx) {t : Clif.Terminator} {data : V}
    (hd : termData t = .ok data) (ti : Nat) : CleanP (Driver.termCtx ctx ti data) :=
  cleanP_set hcl (termData_plain ctx.func hd)

/-- A `try_call`'s data at its slot keeps the context clean. -/
theorem cleanP_tryCtx {ctx : Ctx} (hcl : CleanP ctx) {t : Clif.Terminator} {data : V}
    (hd : tryCallData ctx.func t = .ok data) (ti : Nat) (trs : List Reg × List Reg) :
    CleanP (Driver.tryCtx ctx ti data trs) :=
  cleanP_set (ti := ti) hcl (tryCallData_plain ctx.func hd)

/-! ## The model -/

section ModelP
variable {ctx : Ctx}

theorem γP_int {f : Clif.Function} (ty : TypeId) (i : Int) :
    γP f (NA.cInt ty i) (.int (normInt ty i)) := by
  refine ⟨fun n hn => by simp [vNames] at hn, fun hi x hx => ?_, fun _ => by simp [VGood]⟩
  simp only [NA.cInt, beq_iff_eq] at hi
  simp only [vInts, List.mem_singleton] at hx
  rw [hx, hi]
  exact List.mem_cons_self

theorem sem_prim_ty {ty : TypeId} {n : String} {c : V} (h : (sem ctx).prim ty n = some c) :
    ∃ t, c = .ty t := by
  simp only [sem] at h
  split at h
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨t, -, rfl⟩ := h
    exact ⟨t, rfl⟩
  · cases h

theorem sem_unData_data {ty : TypeId} {v : V} {k : Nat} {fs : List V}
    (h : (sem ctx).unData ty v = some (k, fs)) : v = .data ty k fs := by
  simp only [sem] at h
  split at h
  · split at h
    · rename_i hty
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [beq_iff_eq.mp hty]
    · cases h
  · cases h

/-- The fields of a described value are described by the same abstract value. -/
theorem γP_field {f : Clif.Function} {a : NA} {ty : TypeId} {k : Nat} {fs : List V} {w : V}
    (h : γP f a (.data ty k fs)) (hw : w ∈ fs) : γP f a w := by
  refine ⟨fun n hn => h.1 n ?_, fun hi x hx => h.2.1 hi x ?_, fun hs => ?_⟩
  · simpa using mem_vNamesL.mpr ⟨w, hw, hn⟩
  · simpa using mem_vIntsL.mpr ⟨w, hw, hx⟩
  · exact vGoodL_iff.mp (vGood_data.mp (h.2.2 hs)).2 w hw

theorem γP_plain {f : Clif.Function} {w : V} (h : vNames w = [] ∧ VGood f w) : γP f aPlain w :=
  ⟨fun n hn => (by rw [h.1] at hn; cases hn), fun hi => absurd hi (by decide), fun _ => h.2⟩

/-- **Extern extractors**: `aext` describes their outputs. -/
theorem γP_ext (hcl : CleanP ctx) (st : LState) (a : NA) (term : Term) (v : V) (fs : List V)
    (h : (sem ctx).extract term v st = .ok fs) : ∀ w ∈ fs, γP ctx.func (aext term.id a) w := by
  obtain ⟨hfr, hsv, hidv, hpl⟩ := externExtract_prov ctx term v st fs h
  intro w hw
  unfold aext
  split
  · rename_i hid
    obtain ⟨h1, h2, h3⟩ := hfr (beq_iff_eq.mp hid) w hw
    exact ⟨fun n hn => .inl ⟨rfl, h1 n hn⟩, fun _ => h2, fun _ => h3⟩
  · rename_i hid1
    split
    · rename_i hid2
      obtain ⟨h1, h2, h3⟩ := hsv (beq_iff_eq.mp hid2) w hw
      exact ⟨fun n hn => .inr (.inl ⟨rfl, h1 n hn⟩), fun _ => h2, fun _ => h3⟩
    · rename_i hid2
      split
      · refine γP_plain ?_
        by_cases hi : term.id = TId.inst_data_value
        · rcases hidv hi w hw with hp | ⟨j, info, hj, rfl⟩
          · exact hp
          · exact hcl j info hj
        · refine hpl ?_ w hw
          simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or]
          exact ⟨fun e => hid1 (beq_iff_eq.mpr e), fun e => hid2 (beq_iff_eq.mpr e), hi⟩
      · exact γP_top

/-- **Extern constructors**: `actor` describes their result, and they emit instructions with
references in `f` (`emit` of a value with `s` set, by `apre`). -/
theorem γP_ctor (s0 st : LState) (as : List NA) (vs : List V) (term : Term) (v : V) (st' : LState)
    (hvs : Holds2 (fun a (_ : LState) v => γP ctx.func a v) st as vs)
    (hIs : RefsSince ctx.func s0 st) (hpre : apre true term.id as = true)
    (h : (sem ctx).ctor term vs st = .ok (v, st')) :
    γP ctx.func (actor term.id as) v ∧ RefsSince ctx.func s0 st' := by
  have hok := externCtor_prov ctx term vs st v st' h
  refine ⟨⟨fun n hn => args_names hvs n (hok.names n hn), fun hi => absurd hi (by simp [actor]),
    fun hs => hok.good (args_good hvs hs)⟩, refsSince_trans hIs (hok.emit fun hid => ?_)⟩
  simp only [apre, Bool.not_true, Bool.false_or, hid, bne_self_eq_false] at hpre
  exact args_good_all hvs fun a ha => by simpa using List.all_eq_true.mp hpre a ha

end ModelP

/-- **The provenance model** of a run from `s0` in a clean context: `γP` (independent of the
state), the instructions emitted since `s0` have their references in the function. -/
def provModel (ctx : Ctx) (hcl : CleanP ctx) (s0 : LState) : Model (sem ctx) true where
  γ := fun a _ v => γP ctx.func a v
  Is := RefsSince ctx.func s0
  Rs := fun _ _ => True
  rs_refl := fun _ => trivial
  rs_trans := fun _ _ _ _ _ => trivial
  rs_ctor := fun _ _ _ _ _ _ => trivial
  top := fun _ _ => γP_top
  le := fun _ _ _ _ hab h => γP_le hab h
  mono := fun _ _ _ _ _ h => h
  int := fun _ ty i => γP_int ty i
  bool := fun _ _ => γP_noNames rfl rfl trivial
  prim := fun _ _ _ _ h => by
    obtain ⟨t, rfl⟩ := sem_prim_ty h
    exact γP_noNames (by simp [vNames]) (by simp [vInts]) (by simp [VGood])
  mkd := fun _ _ _ _ _ h => γP_mkd h
  un := fun _ _ _ _ _ _ hv hu w hw => by
    rw [sem_unData_data hu] at hv
    exact γP_field hv hw
  ext := fun st a term v fs _ h => γP_ext hcl st a term v fs h
  ctor := fun st as vs term v st' hvs hIs hpre h => γP_ctor s0 st as vs term v st' hvs hIs hpre h

end Backend.Proof.RelocProv
