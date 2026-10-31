import FV.E2E.SemanticStackBound
import FV.E2E.SemanticPipelineCheckT
import FV.E2E.StackBoundT

/-! # Typed copies of `FV.E2E.SemanticStackBound` (#722)

The declarations of `FV.E2E.SemanticStackBound` that depend on the link contract
(`LinkSys.OkSemanticNI`, `okB`, `ArmRefines`), for the typed contract `LinkSys.OkT` and the
typed checks on the Stock pipeline's results `okBTS` (`okRWithTS`: per function the Stock
validator on an integer function, or the typed validators on `lowerFunction`'s output);
suffix `TS`, as `FV/E2E/DeadCleanupStackBoundT.lean` is of `FV/E2E/DeadCleanupStackBound.lean`. -/

namespace E2E.SemanticStackBound
set_option autoImplicit false
open Backend Backend.Proof Backend.Proof.Driver E2E.LinkCheck E2E.StackBound

/-- **The typed checks on the compiler input's results** (`okRWithTS`). -/
def okBTS (I : CompilerInput) : Bool := okRWithTS I.stage I.toLinkInput I.results

theorem okBTS_names {I : CompilerInput} (hI : okBTS I = true) :
    ((progOf I.results).funcs.map (·.name)).Nodup := okRWithTS_names I.stage hI

theorem okBTS_global {I : CompilerInput} (hI : okBTS I = true) :
    ∀ c ∈ globalChks I.toLinkInput (progOf I.results) (tabOf I.results), c.2 = true :=
  okRWithTS_global I.stage hI

theorem factsTS {I : CompilerInput} (hI : okBTS I = true) {g : Clif.Function}
    (hg : g ∈ (progOf I.results).funcs) :
    FactsWithTS I.stage I.toLinkInput I.results g (artOf I.results g) :=
  factsRWithTS I.stage (I.toLinkInput.resultsProductionWith_prepared I.lower I.cleanup) hI hg

/-- **The typed checks establish the typed link contract** of the input's linked system. -/
theorem okBTS_sound {I : CompilerInput} (hI : okBTS I = true)
    {B : BaseEnv} {F : BitVec 64 → Prop}
    (hB : BaseOk (ofInput I B F)) (hF : ∀ a, (ofInput I B F).Img a → F a) :
    (ofInput I B F).OkT :=
  okRWithTS_soundT I.stage (stage_cases I)
    (I.toLinkInput.resultsProductionWith_prepared I.lower I.cleanup) hI hB hF

/-- Under `okBTS`, a callee of the linked system is an edge of the call graph. -/
theorem edgeB_of_calleeTS {I : CompilerInput} (hI : okBTS I = true) {B : BaseEnv}
    {F : BitVec 64 → Prop} {g h : Clif.Function} (hg : g ∈ (progOf I.results).funcs)
    (hc : (ofInput I B F).Callee g h) : edgeB (fun n => I.syms.lookup n) g h = true := by
  have hdecl : ∀ e ∈ g.externs, e.2.name = h.name → edgeB (fun n => I.syms.lookup n) g h = true :=
    fun e he hn => by
      simp only [edgeB, edgeW, Bool.or_eq_true, List.any_eq_true, beq_iff_eq]
      exact .inl ⟨e, he, hn⟩
  rcases hc with ⟨info, hs, n, hd, hpf⟩ | ⟨e, he, hpf⟩ | hc
  · have hpf' : (progOf I.results).func? n = some h := hpf
    obtain ⟨⟨e, he, hen⟩, -⟩ := siteOkC_sound (site_sound (factsTS hI hg).sites hs) hd hpf'
    exact hdecl e he (by rw [hen, (Clif.Program.func?_some hpf').2])
  · obtain ⟨e', he', rfl⟩ := List.mem_map.1 he
    exact hdecl e' he' (Clif.Program.func?_some (p := progOf I.results) hpf).2.symm
  · obtain ⟨hh, hmay⟩ := hc
    rcases hmay with hm | ⟨hnf, hsy, hsig⟩
    · obtain ⟨e, he, hen⟩ := List.mem_map.1 hm
      exact hdecl e he hen
    · obtain ⟨sig, hsm, hm⟩ := hsig h (func?_of_mem (okBTS_names hI) hh)
      have hsy' : (I.syms.lookup h.name).isSome = true := by
        revert hsy; show I.syms.lookup h.name ≠ none → _
        cases I.syms.lookup h.name <;> simp
      simp only [edgeB, edgeW, indFreeB_false hnf, hsy', Bool.not_false, Bool.true_and,
        Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq]
      exact .inr ⟨sig, hsm, hm⟩

theorem goodN_iffTS {I : CompilerInput} (hI : okBTS I = true) {n : String} :
    goodN I n = true ↔
      ∃ f, (progOf I.results).func? n = some f ∧ ¬ CycleFrom (Calls I I.results) f := by
  unfold goodN
  cases hf : (progOf I.results).func? n with
  | none => simp
  | some f =>
    simp only [Option.some.injEq, exists_eq_left']
    exact budC_isSome_iff (okBTS_names hI) (Clif.Program.func?_some hf).1

/-- **Soundness of the budgets** (`budget_of` under `okBTS`). -/
theorem budget_ofTS {I : CompilerInput} (hI : okBTS I = true) (B : BaseEnv) (F : BitVec 64 → Prop) :
    (ofInput I B F).Budget ((ofInput I B F).hybrid (budO I) (budMax I)) := by
  refine LinkSys.budget_hybrid _ _ _ (fun h hh => (factsTS hI hh).depth) ?_ ?_
    fun g hg bg hbg => E2E.StackBound.budC_probe (I := I) (R := I.results) (okBTS_names hI) hg hbg
  · intro g hg bg hbg h hcl
    have hok := budOkW_budMap (I := I) (R := I.results) (okBTS_names hI)
    have he := edgeB_of_calleeTS hI hg hcl
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

/-- **`backend_correct_program_stackT` for the function named `n`** of the linked system `L` of
the input `I`, every premise but `L.OkT` (`ProgStmtS` with `ArmRefinesT`). -/
def ProgStmtSTS (L : LinkSys) (I : CompilerInput) (n : String) : Prop :=
  ∀ (f : Clif.Function), L.P.func? n = some f →
  ∀ (M : Nat) (ra : BitVec 64) (s w₀ : Arm.ArmState) (args : List Clif.Val) (cs : Clif.State),
    AbiEntry (L.A f).fb (L.A f).base ra s →
    stackFn I f ≤ (spv s).toNat → (∀ a, L.Img a → ¬ StackBelow (stackFn I f) (spv s) a) →
    L.F = frameWG (bud I f) (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase
      (RAFrame.compute (L.A f).vcp (L.A f).rf).size (L.A f).af L.Img s →
    (∀ a, L.Img a → s.mem a = L.imgMem a) →
    BodyEntry (L.A f).af s w₀ → ArgsIn f.sig args s → ClifEntry f args cs →
    StackArgsAvoid L.Img f.sig args s →
    Rel.holds ⟨L.F, L.syms, (L.A f).af.slotBase,
      (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase⟩ f cs.frame.slots cs.mem w₀ →
    (L.NeedSlots → L.PlaceAt cs.mem (spv w₀)) →
    TrapsExplicit (Clif.linkEnvN L.P L.base M) L.P.bare cs →
    ArmRefinesT (L.A f).fb (L.A f).base ra (L.mach M f) s (Clif.runLoop L.base L.P (M + 1) cs)

/-- **The crate's theorem with the stack bound** for its function named `n` (`StackStmt` with
`ProgStmtSTS`). -/
def StackStmtTS (I : CompilerInput) (n : String) : Prop :=
  ∀ (B : BaseEnv) (F : BitVec 64 → Prop), BaseOk (ofInput I B F) →
    (∀ a, (ofInput I B F).Img a → F a) → ProgStmtSTS (ofInput I B F) I n

/-- **A function whose calls never reach a call cycle** (`goodN`) of an input that passes the
typed checks refines at every fuel with its stack bound `stackFn I f`. -/
theorem crate_correct_stackNTS {I : CompilerInput} (hI : okBTS I = true) {n : String}
    (hn : goodN I n = true) : StackStmtTS I n := by
  intro B F hB hFI f hf M _ _ _ _ _ hent hroom hgfree hFeq himg hbe hargs hcs hsav hrel hpl htr
  have hf' : (progOf I.results).func? n = some f := hf
  unfold goodN at hn
  rw [hf'] at hn
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hn
  have hbud : bud I f = b := by simp [bud, hb]
  refine backend_correct_program_stackT _ (okBTS_sound hI hB hFI) (budget_ofTS hI B F) (bud I f)
    (fun M => by simp [LinkSys.hybrid, hb, hbud]) (Clif.Program.func?_some hf).1 M hent hroom
    hgfree hFeq himg hbe hargs hcs hsav hrel hpl htr

end E2E.SemanticStackBound
