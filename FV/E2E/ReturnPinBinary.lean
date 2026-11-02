import FV.E2E.SemanticBinaryGood
import FV.E2E.PreparedReturnPinCalls
import FV.E2E.BinaryBoundaryFacts

namespace E2E.ReturnPinBinary
open Backend Backend.Proof Backend.Proof.Driver E2E.LinkCheck E2E.SemanticBinary
set_option autoImplicit false
set_option Elab.async false

def okB (I : SemanticStackBound.CompilerInput) : Bool :=
  okRReturnPinCalls I.stage I.toLinkInput I.results

/-- Every previously checked program keeps its complete binary-checker verdict. -/
theorem okB_previous {I : SemanticStackBound.CompilerInput} (previous : SemanticStackBound.okB I = true) :
    okB I = true :=
  okRReturnPinCalls_previous (okRReturnPins_of_previous I.stage
    (I.toLinkInput.resultsProductionWith_prepared I.lower I.cleanup) previous)

theorem okB_sound {I : SemanticStackBound.CompilerInput} (checked : okB I = true)
    {B : BaseEnv} {F : BitVec 64 → Prop} (base : BaseOk (SemanticStackBound.ofInput I B F))
    (world : ∀ a,(SemanticStackBound.ofInput I B F).Img a → F a) :
    (SemanticStackBound.ofInput I B F).OkSemanticReturnPins :=
  semanticPreparedReturnPinCallsResults_sound I.stage (SemanticStackBound.stage_cases I)
    (I.toLinkInput.resultsProductionWith_prepared I.lower I.cleanup) checked base world

theorem binary_correct_depth {I : SemanticStackBound.CompilerInput} (checked : okB I = true) (B : BaseEnv)
    (base : BaseOk (sys I B)) {n : String} {f : Clif.Function} (found : (prog I).func? n = some f)
    (M : Nat) {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (outside : OutsideCall I (fun _ => none) f (frameDrop (art I f).af + I.D*M) r args cs.mem)
    (source : ClifRun I B f r args cs)
    (traps : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) (prog I).bare cs) :
    ArmRefines (art I f).fb (art I f).base (xreg 30 r) ((sys I B).mach M f) (modelOf I f r)
      (Clif.runLoop B.env (prog I) (M+1) cs) := by
  have base' : BaseOk (SemanticStackBound.ofInput I B (worldF I f (I.D*M) r)) := baseOk_F base
  have world : ∀ a,(SemanticStackBound.ofInput I B (worldF I f (I.D*M) r)).Img a →
      worldF I f (I.D*M) r a := fun _ h => .inr h
  have contract := okB_sound checked base' world
  obtain ⟨entry,room,free,image,body,args,avoids,memory,placement⟩ :=
    BinaryBoundaryFacts.premises (BinaryBoundaryFacts.of_returnPins contract)
      (Clif.Program.func?_some found).1 (fun _ _ impossible => by cases impossible) outside source
  rw [mach_F I B (fun _ => False) (worldF I f (I.D*M) r)]
  exact backend_correct_program_budget_return_pins _ contract (LinkSys.budget_K_return_pins _ contract)
    (Clif.Program.func?_some found).1 M entry room rfl free image body args source.entry avoids memory placement traps

structure BinFacts (I : SemanticStackBound.CompilerInput) (X : Image) (R : BitVec 64 → Prop)
    (roB : BitVec 64 → Option (BitVec 8)) : Prop where
  ok : okB I = true
  code : ∀ a, img I a → X.kept a ∧ (X.mem a = some (imgMem I a) ∨ R a)
  data : ∀ a b, roB a = some b → X.kept a ∧ X.mem a = some b

theorem BinFacts.previous {I : SemanticStackBound.CompilerInput} {X : Image} {R : BitVec 64 → Prop}
    {roB : BitVec 64 → Option (BitVec 8)} (previous : SemanticBinary.BinFacts I X R roB) :
    BinFacts I X R roB := ⟨okB_previous previous.ok,previous.code,previous.data⟩

theorem BinFacts.modelOf_ne {I : SemanticStackBound.CompilerInput} {X : Image} {R : BitVec 64 → Prop}
    {roB : BitVec 64 → Option (BitVec 8)} (hbin : BinFacts I X R roB) {f : Clif.Function}
    {r : Arm.ArmState} (hX : X.Intact r) : ∀ a, (modelOf I f r).mem a ≠ r.mem a → R a := by
  intro a hne
  by_cases hi : img I a
  · rw [mem_modelOf_img hi] at hne
    rcases (hbin.code a hi).2 with h | h
    · exact absurd (hX a _ (hbin.code a hi).1 h).symm hne
    · exact h
  · exact absurd (mem_modelOf_not hi) hne

theorem binary_correct_depthX {I : SemanticStackBound.CompilerInput} {X : Image} {R : BitVec 64 → Prop}
    {roB : BitVec 64 → Option (BitVec 8)} (hbin : BinFacts I X R roB) (B : BaseEnv)
    (hB : BaseOk (sys I B)) {n : String} {f : Clif.Function} (hf : (prog I).func? n = some f)
    (M : Nat) {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State} (hX : X.Intact r)
    (ho : OutsideCall I roB f (frameDrop (art I f).af + I.D * M) r args cs.mem)
    (hr : ClifRun I B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) (prog I).bare cs) :
    ArmRefines (art I f).fb (art I f).base (xreg 30 r) ((sys I B).mach M f) (modelOf I f r)
      (Clif.runLoop B.env (prog I) (M + 1) cs) ∧
    (∀ a, (modelOf I f r).mem a ≠ r.mem a → R a) ∧
    ((∃ vals cm, Clif.runLoop B.env (prog I) (M + 1) cs = .returned vals cm) ∨
      (∃ c, Clif.runLoop B.env (prog I) (M + 1) cs = .trapped c) →
      (sys I B).RunGoodL M f (modelOf I f r)) := by
  have hB' : BaseOk (SemanticStackBound.ofInput I B (worldF I f (I.D * M) r)) := baseOk_F hB
  have himgF : ∀ a, (SemanticStackBound.ofInput I B (worldF I f (I.D * M) r)).Img a →
      worldF I f (I.D * M) r a := fun _ h => .inr h
  have hL := okB_sound hbin.ok hB' himgF
  have hro : ∀ a b, roB a = some b → r.mem a = b := fun a b h =>
    hX a b (hbin.data a b h).1 (hbin.data a b h).2
  obtain ⟨hent, hres, hgfree, himg, hbe, hargs, hsav, hrel, hpl⟩ :=
    BinaryBoundaryFacts.premises (BinaryBoundaryFacts.of_returnPins hL) (Clif.Program.func?_some hf).1 hro ho hr
  obtain ⟨hA, hG⟩ := backend_correct_program_budgetX_return_pins _ hL (LinkSys.budget_K_return_pins _ hL)
    (Clif.Program.func?_some hf).1 M hent hres rfl hgfree himg hbe hargs hr.entry hsav hrel hpl htr
  refine ⟨?_, hbin.modelOf_ne hX, fun hout => runGoodL_F (hG hout)⟩
  rw [mach_F I B (fun _ => False) (worldF I f (I.D * M) r)]
  exact hA

theorem binary_correct_peakX {I : SemanticStackBound.CompilerInput} {X : Image} {R : BitVec 64 → Prop}
    {roB : BitVec 64 → Option (BitVec 8)} (hbin : BinFacts I X R roB) (B : BaseEnv)
    (hB : BaseOk (sys I B)) {n : String} {f : Clif.Function} (hf : (prog I).func? n = some f)
    (F d : Nat) {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State} (hX : X.Intact r)
    (ho : OutsideCall I roB f (frameDrop (art I f).af + I.D * d) r args cs.mem)
    (hr : ClifRun I B f r args cs) (hd : Clif.DepthLe B.env (prog I) d cs)
    (htr : TrapsExplicit (Clif.linkEnvD (prog I) B.env F d) (prog I).bare cs) :
    ArmRefines (art I f).fb (art I f).base (xreg 30 r) ((sys I B).mach d f) (modelOf I f r)
      (Clif.runLoop B.env (prog I) (F + 1) cs) ∧
    (∀ a, (modelOf I f r).mem a ≠ r.mem a → R a) ∧
    ((∃ vals cm, Clif.runLoop B.env (prog I) (F + 1) cs = .returned vals cm) ∨
      (∃ c, Clif.runLoop B.env (prog I) (F + 1) cs = .trapped c) →
      (sys I B).RunGoodL d f (modelOf I f r)) := by
  have hB' : BaseOk (SemanticStackBound.ofInput I B (worldF I f (I.D * d) r)) := baseOk_F hB
  have himgF : ∀ a, (SemanticStackBound.ofInput I B (worldF I f (I.D * d) r)).Img a →
      worldF I f (I.D * d) r a := fun _ h => .inr h
  have hL := okB_sound hbin.ok hB' himgF
  have hro : ∀ a b, roB a = some b → r.mem a = b := fun a b h =>
    hX a b (hbin.data a b h).1 (hbin.data a b h).2
  obtain ⟨hent, hres, hgfree, himg, hbe, hargs, hsav, hrel, hpl⟩ :=
    BinaryBoundaryFacts.premises (BinaryBoundaryFacts.of_returnPins hL) (Clif.Program.func?_some hf).1 hro ho hr
  obtain ⟨hA, hG⟩ := backend_correct_program_peakX_return_pins _ hL (LinkSys.budget_K_return_pins _ hL)
    (Clif.Program.func?_some hf).1 F d hent hres rfl hgfree himg hbe hargs hr.entry hsav hrel hpl
    hd htr
  refine ⟨?_, hbin.modelOf_ne hX, fun hout => runGoodL_F (hG hout)⟩
  rw [mach_F I B (fun _ => False) (worldF I f (I.D * d) r)]
  exact hA

theorem binFacts_of_checks {I : SemanticStackBound.CompilerInput} {D : List Clif.DataObject} {file : ByteArray}
    (hI : okB I = true) (hB : BinCheck.BinOkWithResults I I.results D file) :
    BinFacts I (imageOf file) (BinCheck.RelocAtWithResults I I.results) (BinCheck.roByte I D) where
  ok := hI
  code := fun _ ha =>
    have himg : imgB (tabOf I.results) = true :=
      okRSemanticFor_global returnPinCallsExtra I.stage (Bool.and_eq_true_iff.mp hI).1 ("imgCode: the image reads back",imgB (tabOf I.results))
        (by simp [globalChks])
    have h := BinCheck.img_bytesWithResults hB himg ha
    ⟨.inl h.1, h.2⟩
  data := fun _ _ h =>
    have h' := BinCheck.roByte_sound hB.data h
    ⟨h'.2, h'.1⟩


end E2E.ReturnPinBinary

namespace E2E.ReturnPinStackBound
open Backend Backend.Proof Backend.Proof.Driver E2E.LinkCheck E2E.StackBound E2E.SemanticStackBound
set_option autoImplicit false
set_option Elab.async false
abbrev CompilerInput := SemanticStackBound.CompilerInput
abbrev okB := ReturnPinBinary.okB
abbrev ofInput := SemanticStackBound.ofInput

theorem okB_names {I : CompilerInput} (checked : okB I = true) :
    ((progOf I.results).funcs.map (·.name)).Nodup :=
  okRSemanticFor_names returnPinCallsExtra I.stage (Bool.and_eq_true_iff.mp checked).1

theorem facts {I : CompilerInput} (checked : okB I = true) {g : Clif.Function}
    (member : g ∈ (progOf I.results).funcs) :
    SemanticPreparedFactsFor returnPinCallsExtra I.stage I.toLinkInput I.results g (artOf I.results g) :=
  semanticPreparedFactsFor returnPinCallsExtra I.stage
    (I.toLinkInput.resultsProductionWith_prepared I.lower I.cleanup) (Bool.and_eq_true_iff.mp checked).1 member

theorem edgeB_of_callee {I : CompilerInput} (hI : okB I = true) {B : BaseEnv}
    {F : BitVec 64 → Prop} {g h : Clif.Function} (hg : g ∈ (progOf I.results).funcs)
    (hc : (ofInput I B F).Callee g h) : edgeB (fun n => I.syms.lookup n) g h = true := by
  have hdecl : ∀ e ∈ g.externs, e.2.name = h.name → edgeB (fun n => I.syms.lookup n) g h = true :=
    fun e he hn => by
      simp only [edgeB, edgeW, Bool.or_eq_true, List.any_eq_true, beq_iff_eq]
      exact .inl ⟨e, he, hn⟩
  rcases hc with ⟨info, hs, n, hd, hpf⟩ | ⟨e, he, hpf⟩ | hc
  · have hpf' : (progOf I.results).func? n = some h := hpf
    obtain ⟨⟨e, he, hen⟩, -⟩ := siteOk_sound (site_sound (facts hI hg).sites hs) hd hpf'
    exact hdecl e he (by rw [hen, (Clif.Program.func?_some hpf').2])
  · obtain ⟨e', he', rfl⟩ := List.mem_map.1 he
    exact hdecl e' he' (Clif.Program.func?_some (p := progOf I.results) hpf).2.symm
  · obtain ⟨hh, hmay⟩ := hc
    rcases hmay with hm | ⟨hnf, hsy, hsig⟩
    · obtain ⟨e, he, hen⟩ := List.mem_map.1 hm
      exact hdecl e he hen
    · obtain ⟨sig, hsm, hm⟩ := hsig h (func?_of_mem (okB_names hI) hh)
      have hsy' : (I.syms.lookup h.name).isSome = true := by
        revert hsy; show I.syms.lookup h.name ≠ none → _
        cases I.syms.lookup h.name <;> simp
      simp only [edgeB, edgeW, indFreeB_false hnf, hsy', Bool.not_false, Bool.true_and,
        Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq]
      exact .inr ⟨sig, hsm, hm⟩


theorem goodN_iff {I : CompilerInput} (hI : okB I = true) {n : String} :
    SemanticStackBound.goodN I n = true ↔
      ∃ f, (progOf I.results).func? n = some f ∧ ¬ SemanticStackBound.CycleFrom (SemanticStackBound.Calls I I.results) f := by
  unfold SemanticStackBound.goodN
  cases hf : (progOf I.results).func? n with
  | none => simp
  | some f =>
    simp only [Option.some.injEq, exists_eq_left']
    exact budC_isSome_iff (okB_names hI) (Clif.Program.func?_some hf).1

theorem budget_of {I : CompilerInput} (hI : okB I = true) (B : BaseEnv) (F : BitVec 64 → Prop) :
    (ofInput I B F).Budget ((ofInput I B F).hybrid (SemanticStackBound.budO I) (SemanticStackBound.budMax I)) := by
  refine LinkSys.budget_hybrid _ _ _ (fun h hh => (facts hI hh).depth) ?_ ?_
  · intro g hg bg hbg h hcl
    have hok := budOkW_budMap (I := I) (R := I.results) (okB_names hI)
    have he := edgeB_of_callee hI hg hcl
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
    have := le_foldl_max (SemanticStackBound.stackFn I) _ 0 hh
    simp only [SemanticStackBound.stackFn, SemanticStackBound.bud, hbh, Option.getD_some] at this
    exact this

variable {modes : Clif.Function → ReturnPinMode}
theorem backend_correct_program_stackX (L : LinkSys) (hL : L.OkReturnPins modes) {κ : Nat → Clif.Function → Nat}
    (hκ : L.Budget κ) {f : Clif.Function} (b : Nat) (hb : ∀ M, κ M f = b)
    (hf : f ∈ L.P.funcs) (M : Nat) {ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val}
    {cs : Clif.State}
    (hent : AbiEntry (L.A f).fb (L.A f).base ra s)
    (hroom : frameDrop (L.A f).af + b ≤ (spv s).toNat)
    (hgfree : ∀ a, L.Img a → ¬ StackBelow (frameDrop (L.A f).af + b) (spv s) a)
    (hF : L.F = frameWG b (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase
      (RAFrame.compute (L.A f).vcp (L.A f).rf).size (L.A f).af L.Img s)
    (himg : ∀ a, L.Img a → s.mem a = L.imgMem a)
    (hbe : BodyEntry (L.A f).af s w₀) (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hsav : StackArgsAvoid L.Img f.sig args s)
    (hrel : Rel.holds ⟨L.F, L.syms, (L.A f).af.slotBase,
      (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (hpl : L.NeedSlots → L.PlaceAt cs.mem (spv w₀))
    (htr : TrapsExplicit (Clif.linkEnvN L.P L.base M) L.P.bare cs) :
    ArmRefines (L.A f).fb (L.A f).base ra (L.mach M f) s (Clif.runLoop L.base L.P (M + 1) cs) ∧
      ((∃ vals cm, Clif.runLoop L.base L.P (M + 1) cs = .returned vals cm) ∨
        (∃ c, Clif.runLoop L.base L.P (M + 1) cs = .trapped c) → L.RunGoodL M f s) := by
  have hd := L.frameDrop_eq_return_pins hL hf
  have hres : StackAvail b (L.A f).af s := by
    unfold StackAvail
    rw [show (L.A f).af.frameSize + 16 + b = frameDrop (L.A f).af + b by omega]
    refine stackRoom_of hroom fun a ha => hgfree a (hL.imgAddr f hf a ?_)
    simpa [CodeAddr, hent.program] using ha
  rw [← hb M] at hres hF hgfree
  exact backend_correct_program_budgetX_return_pins L hL hκ hf M hent hres hF hgfree himg hbe hargs hcs hsav
    hrel hpl htr

theorem crate_correct_stackNX {I : SemanticStackBound.CompilerInput} (hI : okB I = true) {n : String}
    (hn : SemanticStackBound.goodN I n = true) : SemanticStackBound.StackStmtX I n := by
  intro B F hB hFI f hf M _ _ _ _ _ hent hroom hgfree hFeq himg hbe hargs hcs hsav hrel hpl htr
  have hf' : (progOf I.results).func? n = some f := hf
  unfold SemanticStackBound.goodN at hn
  rw [hf'] at hn
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hn
  have hbud : SemanticStackBound.bud I f = b := by simp [SemanticStackBound.bud, hb]
  exact backend_correct_program_stackX _ (ReturnPinBinary.okB_sound hI hB hFI) (budget_of hI B F) (SemanticStackBound.bud I f)
    (fun M => by simp [LinkSys.hybrid, hb, hbud]) (Clif.Program.func?_some hf).1 M hent hroom
    hgfree hFeq himg hbe hargs hcs hsav hrel hpl htr

end E2E.ReturnPinStackBound

namespace E2E.ReturnPinBinary
open Backend Backend.Proof Backend.Proof.Driver E2E.LinkCheck E2E.SemanticBinary E2E.SemanticStackBound
theorem binary_correctX {I : SemanticStackBound.CompilerInput} {X : Image} {R : BitVec 64 → Prop}
    {roB : BitVec 64 → Option (BitVec 8)} (hbin : BinFacts I X R roB) (B : BaseEnv)
    (hB : BaseOk (sys I B)) {n : String} (hn : SemanticStackBound.goodN I n = true) {f : Clif.Function}
    (hf : (prog I).func? n = some f) (M : Nat) {r : Arm.ArmState}
    {args : List Clif.Val} {cs : Clif.State} (hX : X.Intact r)
    (ho : OutsideCall I roB f (SemanticStackBound.stackFn I f) r args cs.mem)
    (hr : ClifRun I B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) (prog I).bare cs) :
    ArmRefines (art I f).fb (art I f).base (xreg 30 r) ((sys I B).mach M f) (modelOf I f r)
      (Clif.runLoop B.env (prog I) (M + 1) cs) ∧
    (∀ a, (modelOf I f r).mem a ≠ r.mem a → R a) ∧
    ((∃ vals cm, Clif.runLoop B.env (prog I) (M + 1) cs = .returned vals cm) ∨
      (∃ c, Clif.runLoop B.env (prog I) (M + 1) cs = .trapped c) →
      (sys I B).RunGoodL M f (modelOf I f r)) := by
  have hB' : BaseOk (SemanticStackBound.ofInput I B (worldF I f (SemanticStackBound.bud I f) r)) := baseOk_F hB
  have himgF : ∀ a, (SemanticStackBound.ofInput I B (worldF I f (SemanticStackBound.bud I f) r)).Img a →
      worldF I f (SemanticStackBound.bud I f) r a := fun _ h => .inr h
  have hL := okB_sound hbin.ok hB' himgF
  have hro : ∀ a b, roB a = some b → r.mem a = b := fun a b h =>
    hX a b (hbin.data a b h).1 (hbin.data a b h).2
  obtain ⟨hent, -, hgfree, himg, hbe, hargs, hsav, hrel, hpl⟩ :=
    BinaryBoundaryFacts.premises (BinaryBoundaryFacts.of_returnPins hL) (Clif.Program.func?_some hf).1 hro ho hr
  obtain ⟨hA, hG⟩ := ReturnPinStackBound.crate_correct_stackNX hbin.ok hn B _ hB' himgF f hf M _ _ _ args
    cs hent (by rw [spv_modelOf]; exact ho.stack) hgfree rfl himg hbe hargs hr.entry hsav hrel hpl
    htr
  refine ⟨?_, hbin.modelOf_ne hX, fun hout => runGoodL_F (hG hout)⟩
  rw [mach_F I B (fun _ => False) (worldF I f (SemanticStackBound.bud I f) r)]
  exact hA


end E2E.ReturnPinBinary

namespace E2E.ReturnPinBinary
open Backend Backend.Proof Backend.Proof.Driver E2E.LinkCheck E2E.SemanticBinary
variable {modes : Clif.Function → ReturnPinMode}
theorem trapsExplicit_of_run {L : LinkSys} (hL : L.OkReturnPins modes) {f : Clif.Function} (hf : f ∈ L.P.funcs)
    {M : Nat} {args : List Clif.Val} {cs : Clif.State} {vals : List Clif.Val} {cm : Clif.Mem}
    (hcs : ClifEntry f args cs) (hsym : cs.mem.symbols = L.syms)
    (hrun : Clif.runLoop L.base L.P (M + 1) cs = .returned vals cm) :
    TrapsExplicit (Clif.linkEnvN L.P L.base M) L.P.bare cs := by
  have hIf : Clif.LInv (L.P.only f) cs := runInv_entry (by simp [Clif.Program.only]) hcs
  obtain ⟨m, hm⟩ := Clif.runLoop_linkN (base := L.base) (syms := L.syms) M hL.names hf hL.free
    (hL.indScope f hf)
    (E := Clif.linkEnvN L.P L.base M) rfl rfl (fun _ _ => rfl) (fun _ _ _ => rfl)
    (M + 1) cs (Nat.le_refl _) (runInv_entry hf hcs) hIf
    (fun _ => hsym) (by rw [hrun]; exact fun _ h => nomatch h)
    (by rw [hrun]; exact fun h => nomatch h)
  rw [hrun] at hm
  exact trapsExplicit_of_returned hm


end E2E.ReturnPinBinary

namespace E2E.ReturnPinBinary
open Backend Backend.Proof Backend.Proof.Driver E2E.LinkCheck E2E.SemanticBinary
variable {modes : Clif.Function → ReturnPinMode}
theorem trapsExplicit_of_runD {L : LinkSys} (hL : L.OkReturnPins modes) {f : Clif.Function} (hf : f ∈ L.P.funcs)
    {F d : Nat} {args : List Clif.Val} {cs : Clif.State} {vals : List Clif.Val} {cm : Clif.Mem}
    (hcs : ClifEntry f args cs) (hsym : cs.mem.symbols = L.syms)
    (hd : Clif.DepthLe L.base L.P d cs)
    (hrun : Clif.runLoop L.base L.P (F + 1) cs = .returned vals cm) :
    TrapsExplicit (Clif.linkEnvD L.P L.base F d) L.P.bare cs := by
  have hIf : Clif.LInv (L.P.only f) cs := runInv_entry (by simp [Clif.Program.only]) hcs
  obtain ⟨m, hm⟩ := Clif.runLoop_linkD (base := L.base) (syms := L.syms) F d hL.names hf hL.free
    (hL.indScope f hf)
    (E := Clif.linkEnvD L.P L.base F d) rfl rfl (fun _ _ => rfl) (fun _ _ _ => rfl)
    (F + 1) cs (Nat.le_refl _) hd (runInv_entry hf hcs) hIf
    (fun _ => hsym) (by rw [hrun]; exact fun _ h => nomatch h)
    (by rw [hrun]; exact fun h => nomatch h)
  rw [hrun] at hm
  exact trapsExplicit_of_returned hm

/-! ## The binary facts -/


end E2E.ReturnPinBinary
