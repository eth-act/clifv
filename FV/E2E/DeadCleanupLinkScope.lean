import FV.E2E.LinkScope
import FV.E2E.DeadCleanupLinkCheck
import FV.E2E.DeadCleanupPreparedSize
import FV.E2E.DeadCleanupSpillCheckAlloc
import FV.E2E.DeadCleanupLinkCalls
import FV.E2E.DeadCleanupLinkFrames
import FV.E2E.DeadCleanupTotal

/-! Completeness of the cleanup pipeline under the unchanged linked-input scope.
The linker's facts describe the actual cleaned artifacts. -/
namespace E2E.LinkCheck
open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

def LinkInput.resultsCleanupT (I : LinkInput) : Res :=
  I.funcs.map fun fi => (fi.func, pipeCleanupT fi.func fi.k
    (BitVec.ofNat 64 (I.baseOf fi.func.name)) (raJ fi.ra fi.j))

theorem mem_resultsCleanupT {I : LinkInput} {e : Clif.Function × Except String Art}
    (he : e ∈ I.resultsCleanupT) : ∃ fi ∈ I.funcs, e.1 = fi.func ∧
      e.2 = pipeCleanupT fi.func fi.k (BitVec.ofNat 64 (I.baseOf fi.func.name)) (raJ fi.ra fi.j) := by
  obtain ⟨fi, hfi, rfl⟩ := List.mem_map.1 he
  exact ⟨fi, hfi, rfl, rfl⟩

theorem progOf_resultsCleanupT (I : LinkInput) : progOf I.resultsCleanupT = I.prog := by
  simp [progOf, LinkInput.resultsCleanupT, LinkInput.prog, Function.comp_def]

theorem resultsCleanupT_ok (I : LinkInput) (R : Res) :
    ResOkWith prune (I.withDepth R) I.resultsCleanupT := by
  intro e he a ha
  obtain ⟨fi, -, h1, h2⟩ := mem_resultsCleanupT he
  rw [h2] at ha
  obtain ⟨hl, hp, -, hlr, hem, hla, -, hb⟩ := pipeCleanupT_spec ha
  rw [h1]
  exact ⟨hl, hp, hlr, hem, hla, hb⟩

theorem pipeCleanupT_ok {g : Clif.Function} (hsc : fnScopeB g = true) (hD : SpillDefinedHyp)
    (k : Nat) (base : BitVec 64) (o : Lean.Json) :
    ∃ a, pipeCleanupT g k base o = .ok a ∧ lowerCheck g a.vc = true ∧ prepCheck (prune a.vc) a.vcp = true ∧
      checkAlloc a.vcp a.rf = .ok () ∧ FormsCovered ⟨a.fa.k, a.af.slotBase⟩ a.vcp := by
  obtain ⟨-, -, -, -, -, -, -, hd, hs, har, hlw, hen⟩ := fnScope_parts hsc
  obtain ⟨hw, vc, vcp, hl, hp, hsz⟩ := lowersB_spec hlw
  have hS := lowerScope_of hs
  obtain ⟨ss, ps, hcfg⟩ := Spill.cfg_ok_of_prepare hp (prepDomain_of_lower hS hl hS.nonempty)
  have hp' := prune_prepare_ok hp
  have hsize := preparedCleanup_spillSizeOkB vc vcp hcfg hsz
  have hem := emitCondsB_cleanup_of_input hs hw hl hp' hsize
  let clean := preparedCleanup vc vcp
  have hsub := inSubset_of_fnScope hsc { funcs := [] }
  have hD' := dominated_of hd
  have hS := lowerScope_of hs
  obtain ⟨af, ha, fa, fb, he, hla, -⟩ :=
    backend_correct_final_cleanup_total_emit (k := k) hsub hd hs har hl hp' hem (raAnswer clean o)
  refine ⟨⟨k, vc, clean, allocResult clean (readyAnswer clean (raAnswer clean o)), af, fa, fb, base⟩,
    ?_, lowerCheck_complete hD' hS hl,
    Prep.prepCheck_complete hp' (prune_prepDomain (prepDomain_of_lower hS hl hS.nonempty)),
    checkAlloc_allocResult (spillCheckAlloc_cleanup hD hsub (Spill.arityOk_of har) hD' hS hen hl hp) _,
    formsCovered_cleanup_complete hS hl hp' _⟩
  simp [pipeCleanupT, hl, hp', clean, ha, he, hla, bind, Except.bind, pure, Except.pure]

theorem chks_resultsCleanupT (hD : SpillDefinedHyp) {I : LinkInput} (hin : InScopeP I = true)
    (hlk : linkerOkR I I.resultsCleanupT = true) {e : Clif.Function × Except String Art} (he : e ∈ I.resultsCleanupT) :
    (chksWith prune (I.withDepth I.resultsCleanupT) (progOf I.resultsCleanupT) (tabOf I.resultsCleanupT) e.1 e.2).all
      (·.2) = true := by
  simp only [InScopeP, Bool.and_eq_true] at hin
  obtain ⟨hps, hfs⟩ := hin
  obtain ⟨hnd, hpg, -⟩ := progScope_parts hps
  obtain ⟨-, -, -, -, hlf⟩ := linker_parts hlk
  obtain ⟨hfit, hra⟩ := hlf e he
  have hdep := le_depthOf he
  obtain ⟨fi, hfi, h1, h2⟩ := mem_resultsCleanupT he
  obtain ⟨g, r⟩ := e
  dsimp only at h1 h2 hfit hra hdep ⊢
  subst h1 h2
  have hgP : fi.func ∈ I.prog.funcs := List.mem_map_of_mem hfi
  have hsc : fnScopeB fi.func = true := List.all_eq_true.1 hfs _ hgP
  obtain ⟨hE, habi, hind, hnd', harg, hw, hfree, hd, hs, -, -⟩ := fnScope_parts hsc
  obtain ⟨a, ha, hlc, hpc, hca, hcov⟩ := pipeCleanupT_ok hsc hD fi.k
    (BitVec.ofNat 64 (I.baseOf fi.func.name)) (raJ fi.ra fi.j)
  obtain ⟨hl, hp, -, hlr, -, -, -, -⟩ := pipeCleanupT_spec ha
  obtain ⟨raw, hraw, hvp⟩ := prune_prepare_ok_inv hp
  have hga : getOk (pipeCleanupT fi.func fi.k (BitVec.ofNat 64 (I.baseOf fi.func.name))
      (raJ fi.ra fi.j)) = a := by rw [ha]; rfl
  rw [hga] at hfit hra hdep
  obtain ⟨hdecl, hindB, hcall, hos⟩ := hpg _ hgP
  have hsite := sites_of_lower
    (callShapeHyp_of (callRunHyp_of callStmtRunHyp tryRunHyp)
      (gotRunHyp_of segRangeHyp gotLocalHyp))
    (inSubset_of_fnScope hsc I.prog) hd hs hnd hcall hl hraw
  have hsite' := preparedCleanup_sites a.vc raw hsite
  rw [← hvp] at hsite'
  have hout := outFits_cleanup_of_lower hd hs hos hl hraw a.rf
  rw [← hvp] at hout
  have hfr := frame_cleanup_of_lower hl hraw hvp hlr
  have hrets := retsB_of_lower iselNoRets hs hl
  have hent := entryB_cleanup_of_lower hs hl hraw
  rw [← hvp] at hent
  rw [List.all_eq_true]
  intro c hc
  simp only [chksWith, staticChksWith, linkChks, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false, ha, progOf_resultsCleanupT] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · exact hlc
  · exact hpc
  · simp [getOk, hca, Except.toBool]
  · exact (formsCoveredB_iff _ _).2 hcov
  · exact hrets
  · exact decide_eq_true hnd'
  · exact List.all_eq_true.2 harg
  · simpa using hw
  · exact hent
  · exact decide_eq_true hfit
  · exact decide_eq_true hdep
  · exact hfree
  · exact hE
  · simpa [Bool.and_eq_true, List.all_eq_true] using habi
  · exact hind
  · exact hout
  · simp only [Bool.or_eq_true]
    exact .inr hfr
  · exact hsite'
  · exact hdecl
  · exact hra
  · exact hindB

/-- **The program's checks hold** for the compiler's results of an in-scope input. -/
theorem outArea_cleanup_of_intBase {I : LinkInput} {x : Clif.Function × Art}
    (hx : x ∈ tabOf I.resultsCleanupT) (h : (RAFrame.compute x.2.vcp x.2.rf).intBase ≠ 0) :
    x.1 ∈ I.prog.funcs ∧ outAreaB x.1 = true := by
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
  obtain ⟨fi, hfi, h1, h2⟩ := mem_resultsCleanupT he
  dsimp only at h ⊢
  rw [h1]
  refine ⟨List.mem_map_of_mem hfi, ?_⟩
  rw [h2] at h
  cases hp : pipeCleanupT fi.func fi.k (BitVec.ofNat 64 (I.baseOf fi.func.name)) (raJ fi.ra fi.j) with
  | error m =>
    rw [hp] at h
    exact (h (show alignTo (default : Art).vcp.outgoing 16 = 0 from rfl)).elim
  | ok a =>
    rw [hp] at h
    obtain ⟨hl, hpr, -⟩ := pipeCleanupT_spec hp
    unfold outAreaB
    rw [hl]
    simp only [bne_iff_ne, ne_eq]
    intro h0
    apply h
    show alignTo a.vcp.outgoing 16 = 0
    obtain ⟨raw, hraw, hv⟩ := prune_prepare_ok_inv hpr
    rw [hv, (preparedCleanup_metadata a.vc raw).2.2.2.1, outgoing_of_prepare hraw, h0]
    rfl

theorem addrSlotsB_cleanup_of_in {I : LinkInput} {S : String → Option Nat}
    (h : addrSlotsInB I.prog S = true) : addrSlotsB I.prog (tabOf I.resultsCleanupT) S = true := by
  simp only [addrSlotsInB, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff] at h
  simp only [addrSlotsB, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff]
  rcases h with ((h | h) | h) | h
  · refine .inl (.inl (.inl ?_))
    rw [List.any_eq_false] at h ⊢
    intro x hx hne
    obtain ⟨hm, ho⟩ := outArea_cleanup_of_intBase hx (by simpa using hne)
    exact h x.1 hm ho
  · exact .inl (.inl (.inr h))
  · exact .inl (.inr h)
  · exact .inr h

theorem global_resultsCleanupT {I : LinkInput} (hin : InScopeP I = true) (hlk : linkerOkR I I.resultsCleanupT = true) :
    (globalChks (I.withDepth I.resultsCleanupT) (progOf I.resultsCleanupT) (tabOf I.resultsCleanupT)).all (·.2) =
      true := by
  simp only [InScopeP, Bool.and_eq_true] at hin
  obtain ⟨hnd, -, has⟩ := progScope_parts hin.1
  obtain ⟨himg, hstar, hinj, hsym, -⟩ := linker_parts hlk
  rw [List.all_eq_true]
  intro c hc
  simp only [globalChks, List.mem_cons, List.not_mem_nil, or_false, progOf_resultsCleanupT] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact decide_eq_true hnd
  · exact himg
  · exact hstar
  · rw [progOf_resultsCleanupT] at hinj; exact hinj
  · exact hsym
  · exact addrSlotsB_cleanup_of_in has

/-- **`okB`'s checks hold on the compiler's results of every in-scope input** whose link the
linker's facts describe: `InScopeP` (the input) and `linkerOkB` (the linker), no check of the
compiler's own output. -/
theorem okT_of_inScopeCleanup (hD : SpillDefinedHyp) {I : LinkInput} (hin : InScopeP I = true)
    (hlk : linkerOkR I I.resultsCleanupT = true) : okRWith prune (I.withDepth I.resultsCleanupT) I.resultsCleanupT = true := by
  simp only [okRWith, Bool.and_eq_true]
  exact ⟨global_resultsCleanupT hin hlk, List.all_eq_true.2 fun e he => chks_resultsCleanupT hD hin hlk he⟩


def _root_.E2E.LinkSys.ofInputCleanupT (I : LinkInput) (B : BaseEnv) (F : BitVec 64 → Prop) : LinkSys :=
  ofRes (I.withDepth I.resultsCleanupT) I.resultsCleanupT B F

theorem okCleanupT_sound (hD : SpillDefinedHyp) {I : LinkInput} (hin : InScopeP I = true)
    (hlk : linkerOkR I I.resultsCleanupT = true) {B : BaseEnv} {F : BitVec 64 → Prop}
    (hB : BaseOk (LinkSys.ofInputCleanupT I B F))
    (hF : ∀ a, (LinkSys.ofInputCleanupT I B F).Img a → F a) :
    (LinkSys.ofInputCleanupT I B F).Ok :=
  okRWith_sound prune (.inr rfl) (resultsCleanupT_ok I I.resultsCleanupT)
    (okT_of_inScopeCleanup hD hin hlk) hB hF

def CrateStmtCleanupT (I : LinkInput) (n : String) : Prop :=
  ∀ (B : BaseEnv) (F : BitVec 64 → Prop), BaseOk (LinkSys.ofInputCleanupT I B F) →
    (∀ a, (LinkSys.ofInputCleanupT I B F).Img a → F a) → ProgStmt (LinkSys.ofInputCleanupT I B F) n

theorem crate_correct_inScope_cleanup (hD : SpillDefinedHyp) {I : LinkInput} (hin : InScopeP I = true)
    (hlk : linkerOkR I I.resultsCleanupT = true) (n : String) : CrateStmtCleanupT I n :=
  fun _ _ hB hF _ hf M _ _ _ _ _ hent hres hFeq hgfree himg hbe hargs hcs hsav hrel hpl htr =>
    backend_correct_program _ (okCleanupT_sound hD hin hlk hB hF) (Clif.Program.func?_some hf).1 M hent
      hres hFeq hgfree himg hbe hargs hcs hsav hrel hpl htr

end E2E.LinkCheck
