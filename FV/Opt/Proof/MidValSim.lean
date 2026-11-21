import FV.Opt.Proof.MidValEntry
import FV.Opt.Proof.MidValPrefix
import FV.Opt.Proof.MidValFStep
import FV.Opt.Proof.MidValMatch
import FV.Opt.Proof.MidValTermin
import FV.Opt.Proof.SimWin
import FV.Opt.Proof.MidValNormAlg2
import FV.Opt.Proof.MidValNormFam4

/-!
# Soundness of the mid-end validator (#1119, module (5))

**`Opt.MidVal.check_sound : checkCert f g cert = true → FunSimMU f g`**: if the re-check of the
certificate accepts, `g` simulates `f` with the memory-aware simulation of
`FV/Opt/Proof/SemSimM.lean`, so `Opt.runLoopX_refinesMU` gives the refinement of programs whose
functions are related this way (`XOutcomeRefines`: same return values and final memory, same
trap code, same exception). With a normaliser: `check_sound_norm` under `NormSound norm`, and
`check_sound_normT` under the typed obligation `NormSoundT f norm` (the default normaliser
`Norm.stdT f` meets it, `normSoundT_stdT`).
The hoisting mode (`checkCertSyms`, `g` evaluating a `symbol_value`/`tls_value`/`func_addr` of
`f` earlier): **`check_soundSyms : checkCertSyms f g cert = true → globalsResolve f syms = true →
FunSimMUAt syms f g`**, the simulation at every symbol table where the function's global values
resolve.

The frame relation is `MRW`: `MR` (`FV/Opt/Proof/MidValRel.lean`) with equal register windows
from the fresh values on (`Win`, where `try_call` results and exception payloads are bound). Each local step of `f` is matched
(`isSimMU`): a `nop`, a pure statement or a removed skeleton statement of `f` is a step of `f`
alone (`rel_nop`, `rel_pure`, `rel_remove`); a matched skeleton statement is `g`'s pure prefix
followed by the same instruction (`rel_matched`); a terminator is `g`'s pure tail followed by the
same terminator (`rel_term`, `rel_try`); function entry is `rel_entry`.
-/

namespace Opt.MidVal

open Clif

section

variable {f g : Function} {fi gi : Info} {cert : Cert} {norm : Norm}

/-- The bodies of related frames are the ones of the block walk. -/
theorem Rel.bodies {syms : String → Option Nat} {bi k k' : Nat} {S : List Fact} {fr fr' : Frame}
    {m : Mem} (hR : Rel f g fi gi cert norm syms bi k k' S fr fr' m) :
    ∃ fb gb Send, f.blocks[bi]? = some fb ∧ g.blocks[bi]? = some gb ∧
      (ccOf fi gi cert norm).walk bi fr.body fr'.body k k' S = some Send ∧
      EndOk (ccOf fi gi cert norm) bi fb gb Send := by
  obtain ⟨fb, gb, Send, hfb, hgb, hw, he⟩ := hR.walk
  obtain ⟨b, hb, hbody, -⟩ := hR.invf.block
  obtain ⟨b', hb', hbody', -⟩ := hR.invg.block
  rw [hfb] at hb; cases hb
  rw [hgb] at hb'; cases hb'
  exact ⟨fb, gb, Send, hfb, hgb, by rw [hbody, hbody']; exact hw, he⟩

theorem removeOk_call {c : CC} {bi k : Nat} {st : Stmt} {S : List Fact} {fn : FnRef}
    {args : List ValueId} (hst : st.inst = .call fn args) :
    c.removeOk bi k st S (mapOperands c.ef st.inst) = false := by
  rw [hst]
  rfl

theorem removeOk_callIndirect {c : CC} {bi k : Nat} {st : Stmt} {S : List Fact} {sig : Nat}
    {callee : ValueId} {args : List ValueId} (hst : st.inst = .callIndirect sig callee args) :
    c.removeOk bi k st S (mapOperands c.ef st.inst) = false := by
  rw [hst]
  rfl

variable (H : Hyp f g fi gi cert norm) (hrun : GPreRun f g fi gi cert norm)
  {syms : String → Option Nat}

/-- A step of `f` at a statement (module doc). -/
theorem step_consT (H : HypT f g fi gi cert norm) (hrun : GPreRun f g fi gi cert norm)
    {bi k k' : Nat} {S : List Fact} {fr fr' : Frame} {m : Mem} {st : Stmt}
    {rest : List Stmt} (hR : Rel f g fi gi cert norm syms bi k k' S fr fr' m)
    (hm : m.symbols = syms) (hb : fr.body = st :: rest) :
    (∀ fr1 m1, lstep fr m = .next fr1 m1 →
      ∃ fr1', LStar fr' m fr1' m1 ∧ MR f g fi gi cert norm syms fr1 fr1' m1) ∧
    (∀ c', lstep fr m = .trap c' → ∃ fr2 m2, LStar fr' m fr2 m2 ∧ lstep fr2 m2 = .trap c') ∧
    (∀ ext vals rs rest', lstep fr m = .call ext vals rs rest' →
      ∃ fr2 rs' rest'', LStar fr' m fr2 m ∧ lstep fr2 m = .call ext vals rs' rest'' ∧
        ContM syms (MR f g fi gi cert norm syms) { fr with body := rest' } rs
          { fr2 with body := rest'' } rs' (AbiParam.tys ext.sig.returns)) := by
  -- an `f`-only step: `.next` within the same memory, or `stuck`
  have fonly : ∀ (S' : List Fact) (k1 : Nat),
      ((∃ fr1, lstep fr m = .next fr1 m ∧ Rel f g fi gi cert norm syms bi k1 k' S' fr1 fr' m) ∨
        ∃ msg, lstep fr m = .stuck msg) →
      (∀ fr1 m1, lstep fr m = .next fr1 m1 →
        ∃ fr1', LStar fr' m fr1' m1 ∧ MR f g fi gi cert norm syms fr1 fr1' m1) ∧
      (∀ c', lstep fr m = .trap c' → ∃ fr2 m2, LStar fr' m fr2 m2 ∧ lstep fr2 m2 = .trap c') ∧
      (∀ ext vals rs rest', lstep fr m = .call ext vals rs rest' →
        ∃ fr2 rs' rest'', LStar fr' m fr2 m ∧ lstep fr2 m = .call ext vals rs' rest'' ∧
          ContM syms (MR f g fi gi cert norm syms) { fr with body := rest' } rs
            { fr2 with body := rest'' } rs' (AbiParam.tys ext.sig.returns)) := by
    intro S' k1 h
    rcases h with ⟨fr1, hs, hR1⟩ | ⟨msg, hs⟩
    · refine ⟨fun fr2 m2 h2 => ?_, fun c' h2 => ?_, fun ext vals rs rest' h2 => ?_⟩
      · rw [hs] at h2
        cases h2
        exact ⟨fr', .refl _ _, bi, k1, k', S', hR1⟩
      · rw [hs] at h2; cases h2
      · rw [hs] at h2; cases h2
    · refine ⟨fun fr2 m2 h2 => ?_, fun c' h2 => ?_, fun ext vals rs rest' h2 => ?_⟩ <;>
        (rw [hs] at h2; cases h2)
  by_cases hn : st.inst = .nop
  · obtain ⟨hs, hR1⟩ := rel_nopT H hR hb hn
    exact fonly S (k + 1) (.inl ⟨_, hs, hR1⟩)
  by_cases hp : pureK st.inst = true
  · rcases rel_pureT H hR hm hb hn hp with ⟨fr1, S', hs, hR1⟩ | hst
    · exact fonly S' (k + 1) (.inl ⟨fr1, hs, hR1⟩)
    · exact fonly S (k + 1) (.inr hst)
  have hp' : pureK st.inst = false := by simpa using hp
  obtain ⟨fb, gb, Send, hfb, hgb, hw, he⟩ := hR.bodies
  rw [hb] at hw
  rcases walk_skel_spec hn hp' hw with ⟨t, ts, k'', hM, hw'⟩ | ⟨-, hrm, hw'⟩
  · obtain ⟨h1, h2, h3, -⟩ := rel_matchedT H hrun hR hm hb hn hp' hM ⟨fb, gb, Send, hfb, hgb, hw', he⟩
    exact ⟨h1, h2, h3⟩
  · exact fonly S (k + 1) (rel_removeT H hR hm hb hn hp' hrm ⟨fb, gb, Send, hfb, hgb, hw', he⟩)

include H hrun in
/-- A step of `f` at a statement (module doc). -/
theorem step_cons {bi k k' : Nat} {S : List Fact} {fr fr' : Frame} {m : Mem} {st : Stmt}
    {rest : List Stmt} (hR : Rel f g fi gi cert norm syms bi k k' S fr fr' m)
    (hm : m.symbols = syms) (hb : fr.body = st :: rest) :
    (∀ fr1 m1, lstep fr m = .next fr1 m1 →
      ∃ fr1', LStar fr' m fr1' m1 ∧ MR f g fi gi cert norm syms fr1 fr1' m1) ∧
    (∀ c', lstep fr m = .trap c' → ∃ fr2 m2, LStar fr' m fr2 m2 ∧ lstep fr2 m2 = .trap c') ∧
    (∀ ext vals rs rest', lstep fr m = .call ext vals rs rest' →
      ∃ fr2 rs' rest'', LStar fr' m fr2 m ∧ lstep fr2 m = .call ext vals rs' rest'' ∧
        ContM syms (MR f g fi gi cert norm syms) { fr with body := rest' } rs
          { fr2 with body := rest'' } rs' (AbiParam.tys ext.sig.returns)) := by
  exact step_consT H.toT hrun hR hm hb

/-- Related frames are at program points of their functions. -/
theorem Rel.inB {syms : String → Option Nat} {bi k k' : Nat} {S : List Fact} {fr fr' : Frame}
    {m : Mem} (hR : Rel f g fi gi cert norm syms bi k k' S fr fr' m) : InB fr ∧ InB fr' := by
  obtain ⟨b, hb, hbody, hterm, -⟩ := hR.invf.block
  obtain ⟨b', hb', hbody', hterm', -⟩ := hR.invg.block
  refine ⟨⟨trivial, b, ?_, ?_, hterm⟩, ⟨trivial, b', ?_, ?_, hterm'⟩⟩
  · rw [hR.invf.func]; exact List.mem_of_getElem? hb
  · rw [hbody]; exact List.drop_suffix _ _
  · rw [hR.invg.func]; exact List.mem_of_getElem? hb'
  · rw [hbody']; exact List.drop_suffix _ _

/-- A `next` step of `MR` keeps equal windows. -/
theorem Win.next {fr fr' fr1 fr1' : Frame} {m m1 m' : Mem} (hI : InB fr) (hI' : InB fr')
    (hw : Win fr fr') (hs : lstep fr m = .next fr1 m1) (hs' : LStar fr' m' fr1' m1) :
    Win fr1 fr1' := by
  obtain ⟨-, hf1, hw1⟩ := lstep_next_win hI hs
  obtain ⟨-, hf1', hw1'⟩ := LStar.win hI' hs'
  intro i
  rw [hf1, hf1', hw1 i, hw1' i]
  exact hw i

/-- A call's continuation of `MR` is one of `MRW` (results bound below the fresh values). -/
theorem ContM.win {syms : String → Option Nat} {fr fr2 : Frame} {st st' : Stmt}
    {rest rest' : List Stmt} {rtys : List Ty} (hI : InB fr) (hI2 : InB fr2) (hw : Win fr fr2)
    (hb : fr.body = st :: rest) (hb2 : fr2.body = st' :: rest')
    (h : ContM syms (MR f g fi gi cert norm syms) { fr with body := rest } st.results
      { fr2 with body := rest' } st'.results rtys) :
    ContM syms (MRW f g fi gi cert norm syms) { fr with body := rest } st.results
      { fr2 with body := rest' } st'.results rtys := by
  intro vs regs m ht hm hs
  obtain ⟨regs', hs', hr⟩ := h vs regs m ht hm hs
  refine ⟨regs', hs', hr, fun i => ?_⟩
  show regs (fr.func.freshValue + i) = regs' (fr2.func.freshValue + i)
  rw [setMany_above hs (stmt_results_lt hI hb), setMany_above hs' (stmt_results_lt hI2 hb2)]
  exact hw i

/-- **The relation is a memory-aware simulation** (`HypT`). -/
theorem isSimMUT (H : HypT f g fi gi cert norm) (hrun : GPreRun f g fi gi cert norm)
    (syms : String → Option Nat) : IsSimMU syms (MRW f g fi gi cert norm syms) where
  toIsSimM :=
    { frame := by
        rintro fr fr' m ⟨⟨bi, k, k', S, hR⟩, -⟩
        refine ⟨hR.slots, ?_⟩
        rw [hR.invg.func, hR.invf.func, H.ok.sig]
      next := by
        rintro fr fr' m fr1 m1 ⟨⟨bi, k, k', S, hR⟩, hw⟩ hm hs
        obtain ⟨hI, hI'⟩ := hR.inB
        obtain ⟨fr1', hst, hr1⟩ : ∃ fr1', LStar fr' m fr1' m1 ∧ MR f g fi gi cert norm syms fr1 fr1' m1 := by
          cases hb : fr.body with
          | nil => exact (rel_termT H hrun hR hm hb).1 fr1 m1 hs
          | cons st rest => exact (step_consT H hrun hR hm hb).1 fr1 m1 hs
        exact ⟨fr1', hst, hr1, Win.next hI hI' hw hs hst⟩
      call := by
        rintro fr fr' m ext vals rs rest ⟨⟨bi, k, k', S, hR⟩, hw⟩ hm hs
        obtain ⟨hI, hI'⟩ := hR.inB
        obtain ⟨st, fn, args, hb, -, hrs, -⟩ := lstep_call_inv hs
        obtain ⟨fr2, rs', rest', hst, hs2, hk⟩ := (step_consT H hrun hR hm hb).2.2 ext vals rs rest hs
        obtain ⟨st', fn', args', hb2, -, hrs', -⟩ := lstep_call_inv hs2
        obtain ⟨hI2, hf2, hw2⟩ := LStar.win hI' hst
        have hw' : Win fr fr2 := fun i => by rw [hf2, hw2 i]; exact hw i
        subst hrs hrs'
        exact ⟨fr2, st'.results, rest', hst, hs2, ContM.win hI hI2 hw' hb hb2 hk⟩
      ret := by
        rintro fr fr' m vals ⟨⟨bi, k, k', S, hR⟩, -⟩ hm hs
        exact (rel_termT H hrun hR hm (lstep_ret_inv hs)).2.1 vals hs
      tail := by
        rintro fr fr' m ext vals ⟨⟨bi, k, k', S, hR⟩, -⟩ hm hs
        exact (rel_termT H hrun hR hm (lstep_tail_inv hs)).2.2.1 ext vals hs
      trap := by
        rintro fr fr' m c' ⟨⟨bi, k, k', S, hR⟩, -⟩ hm hs
        cases hb : fr.body with
        | nil => exact (rel_termT H hrun hR hm hb).2.2.2 c' hs
        | cons st rest => exact (step_consT H hrun hR hm hb).2.1 c' hs }
  ci := by
    rintro fr fr' m st rest sig callee args d a vals ⟨⟨bi, k, k', S, hR⟩, hw⟩ hm hb hst hca
    obtain ⟨hI, hI'⟩ := hR.inB
    have hn : st.inst ≠ .nop := by rw [hst]; exact fun h => by cases h
    have hp : pureK st.inst = false := by rw [hst]; rfl
    obtain ⟨fb, gb, Send, hfb, hgb, hw0, he⟩ := hR.bodies
    rw [hb] at hw0
    rcases walk_skel_spec hn hp hw0 with ⟨t, ts, k'', hM, hw'⟩ | ⟨-, hrm, -⟩
    · obtain ⟨fr2, st', rest', sig', callee', args', hst2, hb2, hi2, hca2, hk⟩ :=
        (rel_matchedT H hrun hR hm hb hn hp hM ⟨fb, gb, Send, hfb, hgb, hw', he⟩).2.2.2
          sig callee args d a vals hst hca
      obtain ⟨hI2, hf2, hw2⟩ := LStar.win hI' hst2
      have hw' : Win fr fr2 := fun i => by rw [hf2, hw2 i]; exact hw i
      exact ⟨fr2, st', rest', sig', callee', args', hst2, hb2, hi2, hca2,
        ContM.win hI hI2 hw' hb hb2 hk⟩
    · rw [removeOk_callIndirect hst] at hrm
      cases hrm
  tc := rel_tryT H hrun

include H hrun in
/-- **The relation is a memory-aware simulation.** -/
theorem isSimMU (syms : String → Option Nat) : IsSimMU syms (MRW f g fi gi cert norm syms) where
  toIsSimM := (isSimMUT H.toT hrun syms).toIsSimM
  ci := (isSimMUT H.toT hrun syms).ci
  tc := (isSimMUT H.toT hrun syms).tc

/-- The entry frames are related (`MRW`) at every memory with the symbols `syms` where the entry
block's facts hold in `f`'s entry frame. -/
theorem entry_relT (H : HypT f g fi gi cert norm) {syms : String → Option Nat}
    (h0 : ∀ (fr : Frame) (m : Mem), fr.func = f →
      ∀ F ∈ (ccOf fi gi cert norm).factsAt 0, FactHolds f cert syms fr m F)
    {b : Block} (hb : f.entry? = some b) :
    ∃ b', g.entry? = some b' ∧ b'.params = b.params ∧
      ∀ args regs (slots : List (SlotId × Nat)) (m : Mem),
        args.map (·.ty) = b.params.map (·.2) →
        Regs.empty.setMany (b.params.map (·.1)) args = some regs →
        slots.map (·.1) = f.slots.map (·.1) → m.symbols = syms →
        MRW f g fi gi cert norm syms ⟨f, regs, slots, b.body, b.term⟩
          ⟨g, regs, slots, b'.body, b'.term⟩ m := by
  have hb0 : f.blocks[0]? = some b := by simpa [Function.entry?, List.head?_eq_getElem?] using hb
  have hlen : 0 < g.blocks.length := by
    rw [H.ok.len]; exact (List.getElem?_eq_some_iff.1 hb0).1
  obtain ⟨b', hb0'⟩ : ∃ b', g.blocks[0]? = some b' := ⟨_, List.getElem?_eq_getElem hlen⟩
  have hb' : g.entry? = some b' := by simpa [Function.entry?, List.head?_eq_getElem?] using hb0'
  have hp : b'.params = b.params := by
    have := H.ok.entryParams
    rw [List.head?_eq_getElem?, List.head?_eq_getElem?, hb0, hb0'] at this
    simpa using this
  refine ⟨b', hb', hp, fun args regs slots m hty hr hsl _ =>
    ⟨⟨0, 0, 0, _, rel_entryT H hb hb' hp m hty hr hsl (h0 _ m rfl)⟩, fun i => ?_⟩⟩
  -- both windows are empty at entry: the parameters are below each function's fresh value
  have hbm : b ∈ f.blocks := List.mem_of_getElem? hb0
  have hbm' : b' ∈ g.blocks := List.mem_of_getElem? hb0'
  show regs (f.freshValue + i) = regs (g.freshValue + i)
  rw [setMany_above hr (fun x hx => by
      obtain ⟨p, hp', rfl⟩ := List.mem_map.1 hx
      exact (lt_freshValue hbm).1 p hp') i,
    setMany_above hr (fun x hx => by
      obtain ⟨p, hp', rfl⟩ := List.mem_map.1 hx
      rw [← hp] at hp'
      exact (lt_freshValue hbm').1 p hp') i]
  rfl

/-- The entry frames are related (`MRW`) at every memory with the symbols `syms` where the entry
block's facts hold in `f`'s entry frame. -/
theorem entry_rel (H : Hyp f g fi gi cert norm) {syms : String → Option Nat}
    (h0 : ∀ (fr : Frame) (m : Mem), fr.func = f →
      ∀ F ∈ (ccOf fi gi cert norm).factsAt 0, FactHolds f cert syms fr m F)
    {b : Block} (hb : f.entry? = some b) :
    ∃ b', g.entry? = some b' ∧ b'.params = b.params ∧
      ∀ args regs (slots : List (SlotId × Nat)) (m : Mem),
        args.map (·.ty) = b.params.map (·.2) →
        Regs.empty.setMany (b.params.map (·.1)) args = some regs →
        slots.map (·.1) = f.slots.map (·.1) → m.symbols = syms →
        MRW f g fi gi cert norm syms ⟨f, regs, slots, b.body, b.term⟩
          ⟨g, regs, slots, b'.body, b'.term⟩ m := by
  exact entry_relT H.toT h0 hb

end

/-- **Soundness of the mid-end validator, with a normaliser sound under typing.** -/
theorem check_sound_normT {f g : Function} {cert : Cert} {norm : Norm}
    (h : checkCert f g cert norm = true) (hN : NormSoundT f norm) : FunSimMU f g := by
  obtain ⟨fi, gi, hf, hg, hok, h0⟩ := checkCert_spec h
  have H : HypT f g fi gi cert norm := ⟨hf, hg, hok, hN⟩
  exact ⟨hok.name, hok.sig, hok.slots, hok.externs, fun syms =>
    ⟨MRW f g fi gi cert norm syms, isSimMUT H (gPre_runT H) syms, fun b hb =>
      entry_relT H (fun _ _ _ F hF => by rw [h0] at hF; cases hF) hb⟩⟩

/-- **Soundness of the hoisting mode, with a normaliser sound under typing**: at every symbol
table where the function's global values resolve. -/
theorem check_soundSyms_normT {f g : Function} {cert : Cert} {norm : Norm}
    (h : checkCertSyms f g cert norm = true) (hN : NormSoundT f norm) {syms : String → Option Nat}
    (hres : globalsResolve f syms = true) : FunSimMUAt syms f g := by
  obtain ⟨fi, gi, hf, hg, hok, -⟩ := checkCertWith_spec h
  have H : HypT f g fi gi cert norm := ⟨hf, hg, hok, hN⟩
  exact ⟨hok.name, hok.sig, hok.slots, hok.externs,
    ⟨MRW f g fi gi cert norm syms, isSimMUT H (gPre_runT H) syms, fun b hb =>
      entry_relT H (fun fr m hfr => entry_facts_holdT H hres hfr m) hb⟩⟩

/-- **Soundness of the mid-end validator, with a normaliser.** -/
theorem check_sound_norm {f g : Function} {cert : Cert} {norm : Norm}
    (h : checkCert f g cert norm = true) (hN : NormSound norm) : FunSimMU f g := by
  exact check_sound_normT h hN.toT

/-- **Soundness of the hoisting mode, with a normaliser**: at every symbol table where the
function's global values resolve. -/
theorem check_soundSyms_norm {f g : Function} {cert : Cert} {norm : Norm}
    (h : checkCertSyms f g cert norm = true) (hN : NormSound norm) {syms : String → Option Nat}
    (hres : globalsResolve f syms = true) : FunSimMUAt syms f g := by
  exact check_soundSyms_normT h hN.toT hres

/-- **Soundness of the mid-end validator** (with its default normaliser `Norm.stdT f`: constant
evaluation, the single-node algebraic rules and the typed rules, `normSoundT_stdT`): if
`checkCert` accepts the certificate, `g` simulates `f` (`FunSimMU`). -/
theorem check_sound {f g : Function} {cert : Cert} (h : checkCert f g cert = true) :
    FunSimMU f g :=
  check_sound_normT h normSoundT_stdT

/-- **Soundness of the hoisting mode** (default normaliser `Norm.stdT f`): if `checkCertSyms`
accepts the certificate, `g` simulates `f` at every symbol table where `f`'s global values
resolve (`FunSimMUAt`). -/
theorem check_soundSyms {f g : Function} {cert : Cert} (h : checkCertSyms f g cert = true)
    {syms : String → Option Nat} (hres : globalsResolve f syms = true) : FunSimMUAt syms f g :=
  check_soundSyms_normT h normSoundT_stdT hres

end Opt.MidVal
