module

public import FV.E2E.LinkScopeInputDefsT2
public import FV.E2E.LinkScopeInputT

@[expose] public section

/-!
# The typed input conditions with the verifier's entry and `select` typing: basic facts

* `fnScopeInTB_of_T2`, `inScopeInT_of_T2`: `fnScopeInTB2` is inside `fnScopeInTB`;
* `entryClassOkB_of_functionE`, `fnScopeInTB2_of_fnScopeInB`, `inScopeInT2_of_inScopeIn`:
  every function of the integer input scope is in it (integer inclusion, no extra premise).
-/

namespace E2E.LinkCheck

open Backend Backend.Proof

theorem fnScopeInT2_parts {g : Clif.Function} (h : fnScopeInTB2 g = true) :
    fnScopeInTB g = true ∧ entryClassOkB g = true ∧ Compile.selectTypedB g = true := by
  simp only [fnScopeInTB2, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- `fnScopeInTB2` is inside `fnScopeInTB`. -/
theorem fnScopeInTB_of_T2 {g : Clif.Function} (h : fnScopeInTB2 g = true) : fnScopeInTB g = true :=
  (fnScopeInT2_parts h).1

/-- `InScopeInT2` is inside `InScopeInT`. -/
theorem inScopeInT_of_T2 {I : LinkInput} (h : InScopeInT2 I = true) : InScopeInT I = true := by
  simp only [InScopeInT2, Bool.and_eq_true, List.all_eq_true] at h
  simp only [InScopeInT, Bool.and_eq_true, List.all_eq_true]
  exact ⟨h.1, fun g hg => fnScopeInTB_of_T2 (h.2 g hg)⟩

/-- **Subset E passes `entryClassOkB`** (its parameters are all integers). -/
theorem entryClassOkB_of_functionE {f : Clif.Function} (hE : Compile.functionE f = true) :
    entryClassOkB f = true := by
  have hsig := (functionE_sig_int hE).1
  simp only [Compile.functionE, Bool.and_eq_true, List.all_eq_true] at hE
  obtain ⟨-, hb⟩ := hE
  unfold entryClassOkB
  split
  · rfl
  · rename_i B0 bs hbl
    have hB := (hb B0 (by rw [hbl]; exact List.mem_cons_self)).1.1
    refine List.all_eq_true.mpr fun q hq => decide_eq_true ?_
    have h1 := hB q.1 (List.of_mem_zip hq).1
    have h2 := List.all_eq_true.mp hsig q.2 (List.of_mem_zip hq).2
    simp only [Compile.tyE, Bool.and_eq_true] at h1
    simp only [tyClass]
    rw [h1.1, h2]

/-- **Integer inclusion**: `fnScopeInB g → fnScopeInTB2 g`. -/
theorem fnScopeInTB2_of_fnScopeInB {g : Clif.Function} (h : fnScopeInB g = true) :
    fnScopeInTB2 g = true := by
  have hE := (fnScopeIn_parts h).1
  simp only [fnScopeInTB2, fnScopeInTB_of_fnScopeInB h, entryClassOkB_of_functionE hE,
    Compile.selectTypedB_of_functionE hE, Bool.and_self]

/-- **Integer inclusion** of crates: `InScopeIn I → InScopeInT2 I`. -/
theorem inScopeInT2_of_inScopeIn {I : LinkInput} (h : InScopeIn I = true) :
    InScopeInT2 I = true := by
  simp only [InScopeIn, Bool.and_eq_true, List.all_eq_true] at h
  simp only [InScopeInT2, Bool.and_eq_true, List.all_eq_true]
  exact ⟨h.1, fun g hg => fnScopeInTB2_of_fnScopeInB (h.2 g hg)⟩

end E2E.LinkCheck
