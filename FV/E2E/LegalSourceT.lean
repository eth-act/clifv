import FV.E2E.LegalSource
import FV.E2E.LegalProgramT
import FV.E2E.SrcScopeDefsT

/-!
# The source domain of an input, `try_call_indirect` included (#1076)

`srcCtxT`: `SrcScopeTB I` (`FV/E2E/SrcScopeDefsT.lean`) gives `E2E.LegalProgram.ProgCtxT`, the
domain of the whole-program refinement `legalProg_refinesT`, as `srcCtx` gives `ProgCtx` from
`SrcScopeB I`. `srcScopeTB_of_srcScopeB`: the old source domain is inside the new one.
-/

namespace E2E.LinkCheck

open Clif Opt.Legalize128 E2E.LegalProgram

/-- **The old source domain is inside the new one.** -/
theorem srcScopeTB_of_srcScopeB {I : LinkInput} (h : SrcScopeB I = true) : SrcScopeTB I = true := by
  simp only [SrcScopeB, SrcScopeTB, Bool.and_eq_true, List.all_eq_true] at h ⊢
  obtain ⟨⟨⟨hok, hlf⟩, hds⟩, hhf⟩ := h
  exact ⟨⟨⟨fun f hf => Opt.Legal.Complete.legalOkTB_of_legalOkB (hok f hf), hlf⟩, hds⟩, hhf⟩

/-- **The domain of the whole-program refinement, `try_call_indirect` included** (`srcCtx` for
`SrcScopeTB`): an input in `SrcScopeTB` whose legalised program satisfies the linked system's
facts (`LinkSys.Ok`'s `names`, `free`, `declSig`, `indScope`), over a base environment with the
`i128` contracts where needed. -/
theorem srcCtxT {I : LinkInput} (hs : SrcScopeTB I = true) {B : Clif.Env}
    {syms : String → Option Nat}
    (hnd : (I.prog.funcs.map (·.name)).Nodup) (hfree' : ∀ g ∈ I.prog.funcs, LinkFree g)
    (hdecl' : ∀ g ∈ I.prog.funcs, ∀ e ∈ g.externs.map (·.2), ∀ h,
      I.prog.func? e.name = some h → e.sig = h.sig)
    (hind : ∀ g ∈ I.prog.funcs, ¬ IndFree g → IndScope I.prog B syms)
    (hlegal : (∃ f ∈ I.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B ∧ Opt.Legal.ExtLegal B ∧ Opt.Legal.EnvKeepsBounded B)
    (hsig : (∃ g ∈ I.prog.funcs, ¬ IndFree g) → ∀ n, B.sigOf n = none) :
    ProgCtxT I.srcProg B syms := by
  simp only [SrcScopeTB, Bool.and_eq_true, List.all_eq_true] at hs
  obtain ⟨⟨⟨hok, hlf⟩, hds⟩, hhf⟩ := hs
  rw [LinkInput.prog_eq] at hnd hfree' hdecl' hind hsig
  have hnames : (legalProg I.srcProg).funcs.map (·.name) = I.srcProg.funcs.map (·.name) := by
    simp only [legalProg_funcs, List.map_map]
    exact List.map_congr_left fun f hf => (legalFactsT (hok f hf)).name
  exact {
    ok := hok
    nd := by rw [← hnames]; exact hnd
    free := fun f hf => linkFreeB_sound (hlf f hf)
    free' := fun f hf => hfree' _ (List.mem_map_of_mem hf)
    decl := fun g hg => declSigB_sound (hds g hg)
    decl' := fun g hg fn e he h hp => by
      obtain ⟨fn', hmem⟩ := E2E.LegalProgram.lookup_mem he
      exact (hdecl' g hg e (List.mem_map.mpr ⟨(fn', e), hmem, rfl⟩) h hp).symm
    helpers := helperFreeB_sound hhf
    base := hlegal
    ind := fun ⟨g, hg, hnf⟩ => ⟨hind g hg hnf, hsig ⟨g, hg, hnf⟩⟩ }

end E2E.LinkCheck
