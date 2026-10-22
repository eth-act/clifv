import FV.Link.OptFacts
import FV.E2E.SrcBoundedLegal

/-! # The optimised input keeps the input's indirect calls: the source run enters callees of the
optimised program (A2/B1)

The source theorems without the memory-bound premise (`FV/Link/ExeSourceNB.lean`) budget the
source run's activations by the compiled frames of the callees of the linked system
(`SrcBounded.callee_of_enter`). For the optimising compiler the compiled program is the optimised
one: a direct call keeps its callee (the optimised function declares the input's externs,
`ShapeFacts.externs`), but the mid-end's branch folding can drop an indirect call with its block
(`removeUnreachable`), so a callee the source run can enter through a pointer need not be a callee
of the optimised caller. `FnInput.opt` keeps its input then (`keepsIndB`, `FV/Link/OptCompile.lean`):

* `FnInput.opt_keepsInd`: the optimised input's function keeps every indirect-call signature id
  of the input's (`KeepsInd`); `LinkSpec.optRelK`: pointwise with `OptPair` (`OptRelK`);
* **`callee_of_enter_opt`**: a function `h` the source run enters from an activation of `g`
  (`SrcBounded.EnterVia`, source domain) has its optimised counterpart `h'` (same name, the same
  slots) as a callee of `g`'s optimised counterpart `g'` in any linked system of the optimised
  program with the source's link-time symbols.
-/

namespace Link
set_option autoImplicit false
open E2E E2E.LinkCheck E2E.SrcBounded E2E.LegalProgram Opt.Legalize128

/-- `g` keeps every indirect-call signature id of `f` (`keepsIndB`). -/
def KeepsInd (f g : Clif.Function) : Prop := ∀ i ∈ Opt.indSigIds f, i ∈ Opt.indSigIds g

theorem keepsIndB_sound {f g : Clif.Function} (h : keepsIndB f g = true) : KeepsInd f g := by
  simp only [keepsIndB, List.all_eq_true, List.contains_iff_mem] at h
  exact h

/-- **The optimised input's function keeps the input's indirect calls** (`FnInput.opt`'s guard
`keepsIndB`). -/
theorem _root_.E2E.LinkCheck.FnInput.opt_keepsInd (fi : FnInput) :
    KeepsInd fi.func fi.opt.func := by
  unfold FnInput.opt
  dsimp only
  split
  · exact fun _ h => h
  · rename_i hg
    split
    · rename_i h
      rw [of_decide_eq_true h]
      simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true', not_or,
        Bool.not_eq_false] at hg
      exact keepsIndB_sound hg.2
    · exact fun _ h => h

/-- Two programs with pointwise `OptPair` functions keeping the indirect calls. -/
def OptRelK (P P' : Clif.Program) : Prop :=
  Opt.Pw2 (fun f g => OptPair f g ∧ KeepsInd f g) P.funcs P'.funcs

theorem LinkSpec.optRelK (S : LinkSpec) : OptRelK S.input.prog S.opt.input.prog := by
  show Opt.Pw2 _ (S.funcs.map FnInput.func) ((S.funcs.map FnInput.opt).map FnInput.func)
  rw [List.map_map]
  induction S.funcs with
  | nil => exact .nil
  | cons fi fs ih => exact .cons ⟨fi.opt_pair, fi.opt_keepsInd⟩ ih

/-- Lookup by name finds the counterpart. -/
theorem OptRelK.func? {P P' : Clif.Program} (h : OptRelK P P') {n : String} {f : Clif.Function}
    (hf : P.func? n = some f) : ∃ g, P'.func? n = some g ∧ OptPair f g ∧ KeepsInd f g := by
  have : ∀ {fs gs : List Clif.Function}, Opt.Pw2 (fun f g => OptPair f g ∧ KeepsInd f g) fs gs →
      fs.find? (·.name == n) = some f →
        ∃ g, gs.find? (·.name == n) = some g ∧ OptPair f g ∧ KeepsInd f g := by
    intro fs gs hp
    induction hp with
    | nil => simp
    | @cons x y xs ys hq _ ih =>
      simp only [List.find?_cons, hq.1.2.name]
      split
      · intro hx; cases hx; exact ⟨y, rfl, hq⟩
      · exact ih
  exact this h hf

/-- A signature id of an indirect call is an indirect call site. -/
theorem indSite_of_mem {g : Clif.Function} {i : Nat} (h : i ∈ Opt.indSigIds g) :
    Opt.Legal.IndSite g i := by
  simp only [Opt.indSigIds, List.mem_flatMap, List.mem_append, List.mem_filterMap] at h
  obtain ⟨b, hb, ⟨st, hst, hs⟩ | ht⟩ := h
  · split at hs
    · rename_i sig callee args hi
      cases hs
      exact .inl ⟨b, hb, st, hst, callee, args, hi⟩
    · cases hs
  · split at ht
    · rename_i callee args et hte
      simp only [List.mem_singleton] at ht
      exact .inr ⟨b, hb, callee, args, et, hte, ht.symm⟩
    · cases ht

/-- The indirect-call signatures of a function kept by the optimised one. -/
theorem mem_indSigs_of_keeps {f g : Clif.Function} (hs : ShapeFacts f g) (hk : KeepsInd f g)
    {s : Clif.Signature} (h : s ∈ Backend.indSigs f) : s ∈ Backend.indSigs g := by
  obtain ⟨i, hi, hl⟩ := mem_indSigs.1 h
  exact mem_indSigs.2 ⟨i, hk i hi, by rw [hs.sigDecls]; exact hl⟩

/-- **The source run enters only callees of the optimised program**: in a linked system `L` of
a program related to the legalisation of a source program `P` (source domain) by `OptRelK`, with
`P`'s link-time symbols, a function `h` the source run enters from an activation of `g` (whose
memory has those symbols at an indirect call) has its counterpart `h'` (same name and slots) as a
callee of `g`'s counterpart `g'`. -/
theorem callee_of_enter_opt {L : LinkSys} {P : Clif.Program} {B : Clif.Env}
    {syms : String → Option Nat} (hC : ProgCtx P B syms) (hR : OptRelK (legalProg P) L.P)
    (hsy : L.syms = syms) {g h : Clif.Function} (hg : g ∈ P.funcs) {mem : Clif.Mem}
    (hv : EnterVia P g h mem) (hms : (∃ sig, Opt.Legal.IndSite g sig) → mem.symbols = syms) :
    ∃ g' h', L.P.func? g.name = some g' ∧ L.P.func? h.name = some h' ∧ h'.slots = h.slots ∧
      L.Callee g' h' := by
  have hh : h ∈ P.funcs := by
    rcases hv with ⟨e, -, hpf⟩ | ⟨hh, -⟩
    · exact (Clif.Program.func?_some hpf).1
    · exact hh
  obtain ⟨g', hg', hpg, hkg⟩ := hR.func? (hC.func?_some (func?_name hC.nd hg))
  obtain ⟨h', hh', hph, -⟩ := hR.func? (hC.func?_some (func?_name hC.nd hh))
  have hFg := legalFacts (hC.ok g hg)
  have hFh := legalFacts (hC.ok h hh)
  refine ⟨g', h', hg', hh', by rw [hph.2.slots, hFh.slots], ?_⟩
  rcases hv with ⟨e, he, hpf⟩ | ⟨-, sig, d, hs, hd, hm, a, ha⟩
  · obtain ⟨hn, hne, -⟩ := hFg.names
    have hen : e.name ∈ g'.externs.map (·.2.name) := by
      rw [hpg.2.externs, hne, List.mem_append]
      left
      obtain ⟨e', he', rfl⟩ := List.mem_map.1 he
      exact List.mem_map_of_mem (f := (·.2.name)) he'
    obtain ⟨e', he', hee⟩ := List.mem_map.1 hen
    refine .inr (.inl ⟨e'.2, List.mem_map_of_mem (f := (·.2)) he', ?_⟩)
    rw [hee, ← (Clif.Program.func?_some hpf).2]
    exact hh'
  · obtain ⟨s, hs', hsm⟩ := indSig_legal (hC.ok g hg) (hC.ok h hh) hs hd hm
    have hs'' := mem_indSigs_of_keeps hpg.2 hkg hs'
    obtain ⟨i, hi, -⟩ := mem_indSigs.1 hs''
    have hname := (Clif.Program.func?_some hh').2
    refine .inr (.inr ⟨(Clif.Program.func?_some hh').1,
      .inr ⟨not_indFree_of_site (indSite_of_mem hi), ?_, fun h'' hh'' => ?_⟩⟩)
    · rw [hsy, hname, ← hms ⟨sig, hs⟩, ha]; simp
    · rw [hname, hh'] at hh''
      cases hh''
      refine ⟨s, hs'', ?_⟩
      show s.abiMatch h'.sig = true
      rw [hph.2.sig]
      exact hsm

end Link
