module

public import FV.Backend.Proof.RelocProvDefs
public import FV.Backend.Proof.IselFlowExt

@[expose] public section

/-!
# Name provenance of the extern extractors (L1e, #216)

`externExtract_prov`: the names and integers an extern extractor gives are `f`'s declarations:
`func_ref_data` gives an external function's name (and no integer), `symbol_value_data` a
symbol global value's name and offset, `inst_data_value` a type and an instruction's own data;
every other extractor gives values without names. No extractor gives an `MInst` value, so every
result is `VGood`. The proof is `Flow.externExtract_ok`'s case split (`externExtract_split`).
-/

namespace Backend.Proof.RelocProv

open Backend Isle Isle.Aarch64

/-- What extractor `x` gives on success (on any input), by the groups of `externExtract_prov`. -/
def ExtProv (ctx : Ctx) (x : TermId) (_ : V) (r : ExtResult (List V)) : Prop :=
  ∀ fs, r = .ok fs →
    (x = TId.func_ref_data → ∀ w ∈ fs, (∀ n ∈ vNames w, n ∈ externNames ctx.func) ∧
      (∀ i ∈ vInts w, i ∈ refOffs ctx.func) ∧ VGood ctx.func w) ∧
    (x = TId.symbol_value_data → ∀ w ∈ fs, (∀ n ∈ vNames w, n ∈ gvNames ctx.func) ∧
      (∀ i ∈ vInts w, i ∈ refOffs ctx.func) ∧ VGood ctx.func w) ∧
    (x = TId.inst_data_value → ∀ w ∈ fs, (vNames w = [] ∧ VGood ctx.func w) ∨
      ∃ (j : Nat) (info : IInfo), ctx.insts[j]? = some info ∧ w = info.data) ∧
    (x ∉ [TId.func_ref_data, TId.symbol_value_data, TId.inst_data_value] →
      ∀ w ∈ fs, vNames w = [] ∧ VGood ctx.func w)

/-- A name-free, integer-free, `VGood` value meets every group. -/
theorem ext_plain {ctx : Ctx} {x : TermId} {fs : List V}
    (h : ∀ w ∈ fs, vNames w = [] ∧ vInts w = [] ∧ VGood ctx.func w) :
    (x = TId.func_ref_data → ∀ w ∈ fs, (∀ n ∈ vNames w, n ∈ externNames ctx.func) ∧
      (∀ i ∈ vInts w, i ∈ refOffs ctx.func) ∧ VGood ctx.func w) ∧
    (x = TId.symbol_value_data → ∀ w ∈ fs, (∀ n ∈ vNames w, n ∈ gvNames ctx.func) ∧
      (∀ i ∈ vInts w, i ∈ refOffs ctx.func) ∧ VGood ctx.func w) ∧
    (x = TId.inst_data_value → ∀ w ∈ fs, (vNames w = [] ∧ VGood ctx.func w) ∨
      ∃ (j : Nat) (info : IInfo), ctx.insts[j]? = some info ∧ w = info.data) ∧
    (x ∉ [TId.func_ref_data, TId.symbol_value_data, TId.inst_data_value] →
      ∀ w ∈ fs, vNames w = [] ∧ VGood ctx.func w) := by
  refine ⟨fun _ w hw => ?_, fun _ w hw => ?_, fun _ w hw => ?_, fun _ w hw => ?_⟩
  all_goals obtain ⟨h1, h2, h3⟩ := h w hw
  · exact ⟨by simp [h1], by simp [h2], h3⟩
  · exact ⟨by simp [h1], by simp [h2], h3⟩
  · exact .inl ⟨h1, h3⟩
  · exact ⟨h1, h3⟩

theorem ext_mem_lookup {α β : Type} [BEq α] [LawfulBEq α] {l : List (α × β)} {a : α} {b : β}
    (h : l.lookup a = some b) : (a, b) ∈ l := by
  obtain ⟨l₁, l₂, rfl, -⟩ := List.lookup_eq_some_iff.mp h
  simp

/-- An extern's name is an external function's name. -/
theorem ext_externName {f : Clif.Function} {fn : Clif.FnRef} {ext : Clif.ExtFunc}
    (h : f.extern? fn = some ext) : ext.name ∈ externNames f := by
  unfold Clif.Function.extern? at h
  unfold externNames
  exact List.mem_map.2 ⟨(fn, ext), ext_mem_lookup h, rfl⟩

/-- A symbol global value's name and offset are `f`'s. -/
theorem ext_gvRef {f : Clif.Function} {gv : Nat} {n : String} {o : Int} {c : Bool}
    (h : f.globals.lookup gv = some (.symbol n o c) ∨ f.globals.lookup gv = some (.tlsSymbol n o c)) :
    n ∈ gvNames f ∧ o ∈ refOffs f := by
  have hm : (n, o) ∈ gvRefs f := by
    unfold gvRefs
    rw [List.mem_filterMap]
    rcases h with h | h
    · exact ⟨(gv, _), ext_mem_lookup h, rfl⟩
    · exact ⟨(gv, _), ext_mem_lookup h, rfl⟩
  exact ⟨List.mem_map.2 ⟨_, hm, rfl⟩, List.mem_cons_of_mem _ (List.mem_map.2 ⟨_, hm, rfl⟩)⟩

/-- **Name provenance of every extern extractor.** -/
theorem externExtract_prov (ctx : Ctx) (t : Term) (v : V) (st : LState) (fs : List V)
    (h : externExtract ctx t v st = .ok fs) :
    (t.id = TId.func_ref_data → ∀ w ∈ fs, (∀ n ∈ vNames w, n ∈ externNames ctx.func) ∧
      (∀ x ∈ vInts w, x ∈ refOffs ctx.func) ∧ VGood ctx.func w) ∧
    (t.id = TId.symbol_value_data → ∀ w ∈ fs, (∀ n ∈ vNames w, n ∈ gvNames ctx.func) ∧
      (∀ x ∈ vInts w, x ∈ refOffs ctx.func) ∧ VGood ctx.func w) ∧
    (t.id = TId.inst_data_value → ∀ w ∈ fs, (vNames w = [] ∧ VGood ctx.func w) ∨
      ∃ (j : Nat) (info : IInfo), ctx.insts[j]? = some info ∧ w = info.data) ∧
    (t.id ∉ [TId.func_ref_data, TId.symbol_value_data, TId.inst_data_value] →
      ∀ w ∈ fs, vNames w = [] ∧ VGood ctx.func w) := by
  have hs : ExtProv ctx t.id v (externExtract ctx t v st) := by
    unfold externExtract
    split
    · unfold ExtProv
      intro fs h
      split at h
      · cases h
        exact ext_plain (by simp [vNames, vInts, VGood])
      · cases h
    · unfold ExtProv
      intro fs h; cases h
    · apply externExtract_split _ (ExtProv ctx)
      all_goals
        intros
        unfold ExtProv
        intro fs h
        try dsimp only at h
        repeat' (split at h)
        all_goals try (cases h; done)
      all_goals cases h
      all_goals
        refine ⟨?_, ?_, ?_, ?_⟩
        all_goals intro hx
        all_goals first
          | exact absurd hx (by decide)
          | (simp (config := { decide := true }) [vNames, vNamesL, opNames, vInts, vIntsL, VGood,
               VGoodL]; done)
          | (simp (config := { decide := true }) [vNames, vNamesL, opNames, vInts, vIntsL, VGood,
               VGoodL]; exact ext_externName ‹_›)
          | (simp (config := { decide := true }) [vNames, vNamesL, opNames, vInts, vIntsL, VGood,
               VGoodL]; exact ext_gvRef (.inl ‹_›))
          | (simp (config := { decide := true }) [vNames, vNamesL, opNames, vInts, vIntsL, VGood,
               VGoodL]; exact ext_gvRef (.inr ‹_›))
          | (intro w hw
             simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
             rcases hw with rfl | rfl
             · exact .inl ⟨rfl, trivial⟩
             · exact .inr ⟨_, _, ‹_›, rfl⟩)
  unfold ExtProv at hs
  exact hs fs h

end Backend.Proof.RelocProv
