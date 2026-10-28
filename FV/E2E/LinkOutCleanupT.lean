import FV.E2E.LinkOutT
import FV.E2E.PipelineCheckT
import FV.E2E.DeadCleanupLinkScope

/-! # The typed checker on the dead-cleanup pipeline's output (S11e5 Stage C, slice 8)

`okT_of_inScopeCleanupT`: `okT_of_inScopeT` (`FV/E2E/LinkOutT.lean`) for the shipped pipeline
`pipeCleanupT` (dead cleanup before `prepare`): the typed checker `okRWithT prune` accepts the
compiler's results `resultsCleanupT` from the typed input conditions `InScopePT`, the output
checks `OutOkTCleanup` (`outChksT` on the cleanup results), the pipeline's success and the
linker's facts. -/

namespace E2E.LinkCheck

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

/-- **`OutOkTCleanup`**: the output checks of the dead-cleanup pipeline's results. -/
def OutOkTCleanup (I : LinkInput) : Bool := outOkTR I I.resultsCleanupT

/-- The program's checks hold for the cleanup results of a typed in-scope input. -/
theorem global_resultsCleanupTT {I : LinkInput} (hin : InScopePT I = true)
    (hlk : linkerOkR I I.resultsCleanupT = true) :
    (globalChks (I.withDepth I.resultsCleanupT) (progOf I.resultsCleanupT)
      (tabOf I.resultsCleanupT)).all (·.2) = true := by
  obtain ⟨hps, -⟩ := inScopePT_parts hin
  obtain ⟨hnd, -, has⟩ := progScope_parts hps
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

/-- **The typed per-function checks hold** for the cleanup results of a typed in-scope input
that passes the output checks. -/
theorem chksWithT_resultsCleanupT {I : LinkInput} (hin : InScopePT I = true)
    (hout : OutOkTCleanup I = true) (hpipe : I.resultsCleanupT.all (·.2.toBool) = true)
    (hlk : linkerOkR I I.resultsCleanupT = true)
    {e : Clif.Function × Except String Art} (he : e ∈ I.resultsCleanupT) :
    (chksWithT cleanupStage (I.withDepth I.resultsCleanupT) (progOf I.resultsCleanupT)
      (tabOf I.resultsCleanupT) e.1 e.2).all (·.2) = true := by
  obtain ⟨hps, hfs⟩ := inScopePT_parts hin
  obtain ⟨-, hpg, -⟩ := progScope_parts hps
  obtain ⟨-, -, -, -, hlf⟩ := linker_parts hlk
  obtain ⟨hfit, hra⟩ := hlf e he
  have hdep := le_depthOf he
  have hok := List.all_eq_true.1 hpipe e he
  have ho := List.all_eq_true.1 hout e he
  obtain ⟨fi, hfi, h1, h2⟩ := mem_resultsCleanupT he
  obtain ⟨g, r⟩ := e
  dsimp only at h1 h2 hfit hra hdep hok ho ⊢
  subst h1 h2
  have hgP : fi.func ∈ I.prog.funcs := List.mem_map_of_mem hfi
  have hsc : fnScopeTB fi.func = true := hfs _ hgP
  obtain ⟨hE, hst, -, habi, hind, hnd', harg, hw, hfree, hd, hs, -⟩ := fnScopeT_parts hsc
  obtain ⟨a, hpr⟩ : ∃ a, pipeCleanupT fi.func fi.k (BitVec.ofNat 64 (I.baseOf fi.func.name))
      (raJ fi.ra fi.j) = .ok a := by
    cases hpr : pipeCleanupT fi.func fi.k (BitVec.ofNat 64 (I.baseOf fi.func.name))
      (raJ fi.ra fi.j) with
    | error m => rw [hpr] at hok; cases hok
    | ok a => exact ⟨a, rfl⟩
  rw [hpr] at hfit hra hdep ho
  obtain ⟨hl, hp, -, hlr, -, -, -, -⟩ := pipeCleanupT_spec hpr
  obtain ⟨raw, hraw, hvp⟩ := cleanupStage_prepare_ok_inv hp
  have hga : getOk (Except.ok (ε := String) a) = a := rfl
  simp only [outChksT, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, hga,
    progOf_resultsCleanupT] at ho
  obtain ⟨hca, hcov, hrets, hent, hout, hsite, hsr, hci⟩ := ho
  have hS := lowerScopeT_of hs
  have hlc := lowerCheckT_complete (dominated_of hd) hS hl
  have hpc := Prep.prepCheck_complete hp
    (cleanupStage_prepDomain _ (Spill.prepDomain_ofT (dominated_of hd) hS hl))
  have hfr := frame_stage_of_lower hl hraw hvp hlr
  obtain ⟨hdecl, hindB, -, -⟩ := hpg _ hgP
  rw [List.all_eq_true]
  intro c hc'
  simp only [chksWithT, staticChksWithT, linkChksT, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false, List.append_assoc, progOf_resultsCleanupT, hpr,
    hga] at hc'
  rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · simp [hE, hlc]
  · exact hpc
  · exact hca
  · exact hcov
  · exact hrets
  · exact decide_eq_true hnd'
  · exact List.all_eq_true.2 harg
  · simpa using hw
  · exact hent
  · exact decide_eq_true hfit
  · exact decide_eq_true hdep
  · exact hfree
  · exact hst
  · simpa [Bool.and_eq_true, List.all_eq_true] using habi
  · exact hind
  · simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true] at hsr ⊢
    rcases hsr with h | h
    · exact .inl h
    · exact .inr ⟨h, lowerCheck_complete (dominated_of hd) (lowerScope_of_T hS h) hl⟩
  · exact hout
  · simp only [Bool.or_eq_true]
    exact .inr hfr
  · exact allInsts_siteOk_le hsite
  · exact hdecl
  · exact hra
  · exact hindB
  · exact hci

/-- **`okRWithT prune`'s checks hold on the cleanup results of every typed in-scope input** that
passes the output checks, whose pipeline succeeds and whose link the linker's facts describe. -/
theorem okT_of_inScopeCleanupT {I : LinkInput} (hin : InScopePT I = true)
    (hout : OutOkTCleanup I = true) (hpipe : I.resultsCleanupT.all (·.2.toBool) = true)
    (hlk : linkerOkR I I.resultsCleanupT = true) :
    okRWithT cleanupStage (I.withDepth I.resultsCleanupT) I.resultsCleanupT = true := by
  simp only [okRWithT, Bool.and_eq_true]
  exact ⟨global_resultsCleanupTT hin hlk,
    List.all_eq_true.2 fun e he => chksWithT_resultsCleanupT hin hout hpipe hlk he⟩

/-- **`LinkSys.OkT` of the compiler's cleanup linked system** of a typed in-scope input. -/
theorem okCleanupT_soundT {I : LinkInput} (hin : InScopePT I = true)
    (hout : OutOkTCleanup I = true) (hpipe : I.resultsCleanupT.all (·.2.toBool) = true)
    (hlk : linkerOkR I I.resultsCleanupT = true) {B : BaseEnv} {F : BitVec 64 → Prop}
    (hB : BaseOk (LinkSys.ofInputCleanupT I B F))
    (hF : ∀ a, (LinkSys.ofInputCleanupT I B F).Img a → F a) :
    (LinkSys.ofInputCleanupT I B F).OkT :=
  okRWith_soundT cleanupStage (.inr rfl) (resultsCleanupT_ok I I.resultsCleanupT)
    (okT_of_inScopeCleanupT hin hout hpipe hlk) hB hF

end E2E.LinkCheck
