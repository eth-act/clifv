import FV.E2E.SemanticStackBoundTS
import FV.E2E.SemanticPipelineCheckTR
import FV.E2E.StackBoundTR

/-!
# `SemanticStackBoundTS` for `LinkSys.OkTR` and `okBTSR` (#753, stage R4)

The declarations of `SemanticStackBoundTS` on the paths from the typed Stock binary theorems to
`LinkSys.OkT`/`okBTS`, for the link contract with the register-guarded calls `LinkSys.OkTR` and
the checks `okBTSR` (suffix `R`).
-/
namespace E2E.SemanticStackBound
set_option autoImplicit false
open Backend Backend.Proof Backend.Proof.Driver E2E.LinkCheck E2E.StackBound

/-- **The typed checks on the compiler input's results** (`okRWithTSR`). -/
def okBTSR (I : CompilerInput) : Bool := okRWithTSR I.stage I.toLinkInput I.results

theorem okBTS_namesR {I : CompilerInput} (hI : okBTSR I = true) :
    ((progOf I.results).funcs.map (·.name)).Nodup := okRWithTSR_names I.stage hI

theorem okBTS_globalR {I : CompilerInput} (hI : okBTSR I = true) :
    ∀ c ∈ globalChks I.toLinkInput (progOf I.results) (tabOf I.results), c.2 = true :=
  okRWithTSR_global I.stage hI

theorem factsTSR {I : CompilerInput} (hI : okBTSR I = true) {g : Clif.Function}
    (hg : g ∈ (progOf I.results).funcs) :
    FactsWithTSR I.stage I.toLinkInput I.results g (artOf I.results g) :=
  factsRWithTSR I.stage (I.toLinkInput.resultsProductionWith_prepared I.lower I.cleanup) hI hg

/-- **The typed checks establish the typed link contract** of the input's linked system. -/
theorem okBTS_soundR {I : CompilerInput} (hI : okBTSR I = true)
    {B : BaseEnv} {F : BitVec 64 → Prop}
    (hB : BaseOk (ofInput I B F)) (hF : ∀ a, (ofInput I B F).Img a → F a) :
    (ofInput I B F).OkTR :=
  okRWithTSR_soundTR I.stage (stage_cases I)
    (I.toLinkInput.resultsProductionWith_prepared I.lower I.cleanup) hI hB hF

/-- Under `okBTSR`, a callee of the linked system is an edge of the call graph. -/
theorem edgeB_of_calleeTSR {I : CompilerInput} (hI : okBTSR I = true) {B : BaseEnv}
    {F : BitVec 64 → Prop} {g h : Clif.Function} (hg : g ∈ (progOf I.results).funcs)
    (hc : (ofInput I B F).Callee g h) : edgeB (fun n => I.syms.lookup n) g h = true := by
  have hdecl : ∀ e ∈ g.externs, e.2.name = h.name → edgeB (fun n => I.syms.lookup n) g h = true :=
    fun e he hn => by
      simp only [edgeB, edgeW, Bool.or_eq_true, List.any_eq_true, beq_iff_eq]
      exact .inl ⟨e, he, hn⟩
  rcases hc with ⟨info, hs, n, hd, hpf⟩ | ⟨e, he, hpf⟩ | hc
  · have hpf' : (progOf I.results).func? n = some h := hpf
    obtain ⟨⟨e, he, hen⟩, -⟩ := siteOkCR_sym_sound (site_sound (factsTSR hI hg).sites hs) hd hpf'
    exact hdecl e he (by rw [hen, (Clif.Program.func?_some hpf').2])
  · obtain ⟨e', he', rfl⟩ := List.mem_map.1 he
    exact hdecl e' he' (Clif.Program.func?_some (p := progOf I.results) hpf).2.symm
  · obtain ⟨hh, hmay⟩ := hc
    rcases hmay with hm | ⟨hnf, hsy, hsig⟩
    · obtain ⟨e, he, hen⟩ := List.mem_map.1 hm
      exact hdecl e he hen
    · obtain ⟨sig, hsm, hm⟩ := hsig h (func?_of_mem (okBTS_namesR hI) hh)
      have hsy' : (I.syms.lookup h.name).isSome = true := by
        revert hsy; show I.syms.lookup h.name ≠ none → _
        cases I.syms.lookup h.name <;> simp
      simp only [edgeB, edgeW, indFreeB_false hnf, hsy', Bool.not_false, Bool.true_and,
        Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq]
      exact .inr ⟨sig, hsm, hm⟩

theorem goodN_iffTSR {I : CompilerInput} (hI : okBTSR I = true) {n : String} :
    goodN I n = true ↔
      ∃ f, (progOf I.results).func? n = some f ∧ ¬ CycleFrom (Calls I I.results) f := by
  unfold goodN
  cases hf : (progOf I.results).func? n with
  | none => simp
  | some f =>
    simp only [Option.some.injEq, exists_eq_left']
    exact budC_isSome_iff (okBTS_namesR hI) (Clif.Program.func?_some hf).1

/-- **Soundness of the budgets** (`budget_of` under `okBTSR`). -/
theorem budget_ofTSR {I : CompilerInput} (hI : okBTSR I = true) (B : BaseEnv) (F : BitVec 64 → Prop) :
    (ofInput I B F).Budget ((ofInput I B F).hybrid (budO I) (budMax I)) := by
  refine LinkSys.budget_hybrid _ _ _ (fun h hh => (factsTSR hI hh).depth) ?_ ?_
    fun g hg bg hbg => E2E.StackBound.budC_probe (I := I) (R := I.results) (okBTS_namesR hI) hg hbg
  · intro g hg bg hbg h hcl
    have hok := budOkW_budMap (I := I) (R := I.results) (okBTS_namesR hI)
    have he := edgeB_of_calleeTSR hI hg hcl
    have hh : h ∈ (progOf I.results).funcs := (ofInput I B F).callee_mem hcl
    simp only [E2E.StackBound.budOkW, List.all_eq_true] at hok
    have h1 := hok g hg
    change E2E.StackBound.budC I I.results g = some bg at hbg
    rw [hbg] at h1
    simp only [List.all_eq_true] at h1
    have h2 := h1 h hh
    simp only [edgeB] at he
    rw [he] at h2
    show ∃ bh, E2E.StackBound.budC I I.results h = some bh ∧ _
    cases hch : E2E.StackBound.budC I I.results h with
    | none => rw [hch] at h2; simp at h2
    | some bh =>
      rw [hch] at h2
      simp only [Bool.not_true, Bool.false_or, decide_eq_true_eq] at h2
      exact ⟨bh, rfl, h2⟩
  · intro h hh bh hbh
    have := le_foldl_max (stackFn I) _ 0 hh
    simp only [stackFn, bud, hbh, Option.getD_some] at this
    exact this

/-- **A function whose calls never reach a call cycle** (`goodN`) of an input that passes the
typed checks refines at every fuel with its stack bound `stackFn I f`. -/
theorem crate_correct_stackNTSR {I : CompilerInput} (hI : okBTSR I = true) {n : String}
    (hn : goodN I n = true) : StackStmtTS I n := by
  intro B F hB hFI f hf M _ _ _ _ _ hent hroom hgfree hFeq himg hbe hargs hcs hsav hrel hpl htr
  have hf' : (progOf I.results).func? n = some f := hf
  unfold goodN at hn
  rw [hf'] at hn
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hn
  have hbud : bud I f = b := by simp [bud, hb]
  refine backend_correct_program_stackTR _ (okBTS_soundR hI hB hFI) (budget_ofTSR hI B F) (bud I f)
    (fun M => by simp [LinkSys.hybrid, hb, hbud]) (Clif.Program.func?_some hf).1 M hent hroom
    hgfree hFeq himg hbe hargs hcs hsav hrel hpl htr

end E2E.SemanticStackBound
