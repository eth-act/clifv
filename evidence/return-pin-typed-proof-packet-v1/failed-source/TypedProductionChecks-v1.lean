import FV.E2E.SemanticChecksWith
import FV.E2E.SemanticStackBoundTS

namespace E2E.TypedProductionChecks
open Backend E2E.LinkCheck E2E.StackBound
set_option autoImplicit false
set_option Elab.async false
variable {lower : ProductionLowering}

def fnsBProduction (lower : ProductionLowering) (I : LinkInput) (cleanup : Bool)
    (fs : List FnInput) : Bool :=
  let R := I.resultsProductionWith lower cleanup
  fs.all fun fi => (chksWithTS (productionStage cleanup) I (progOf R) (tabOf R) fi.func
    (I.pipeProductionWith lower cleanup fi)).all (·.2)

theorem fnsBProduction_append (I : LinkInput) (cleanup : Bool) (a b : List FnInput) :
    fnsBProduction lower I cleanup (a ++ b) =
      (fnsBProduction lower I cleanup a && fnsBProduction lower I cleanup b) := by
  simp only [fnsBProduction,List.all_append]

theorem okRProduction_of_checks {I : LinkInput} {cleanup : Bool}
    (hg : SemanticChecksWith.globalBProduction lower I cleanup = true)
    (hf : fnsBProduction lower I cleanup I.funcs = true) :
    okRWithTS (productionStage cleanup) I (I.resultsProductionWith lower cleanup) = true := by
  unfold okRWithTS
  rw [Bool.and_eq_true]
  constructor
  · exact hg
  · simpa only [fnsBProduction,LinkInput.resultsProductionWith,List.all_map,
      Function.comp_def] using hf

def ProgStmtTS (L : LinkSys) (n : String) : Prop :=
  ∀ (f : Clif.Function), L.P.func? n = some f →
  ∀ (M : Nat) (ra : BitVec 64) (s w₀ : Arm.ArmState) (args : List Clif.Val) (cs : Clif.State),
    AbiEntry (L.A f).fb (L.A f).base ra s → StackAvail (L.K M) (L.A f).af s →
    L.F = frameWG (L.K M) (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase
      (RAFrame.compute (L.A f).vcp (L.A f).rf).size (L.A f).af L.Img s →
    (∀ a, L.Img a → ¬ StackBelow (frameDrop (L.A f).af + L.K M) (spv s) a) →
    (∀ a, L.Img a → s.mem a = L.imgMem a) →
    BodyEntry (L.A f).af s w₀ → ArgsIn f.sig args s → ClifEntry f args cs →
    StackArgsAvoid L.Img f.sig args s →
    Rel.holds ⟨L.F, L.syms, (L.A f).af.slotBase,
      (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase⟩ f cs.frame.slots cs.mem w₀ →
    (L.NeedSlots → L.PlaceAt cs.mem (spv w₀)) →
    TrapsExplicit (Clif.linkEnvN L.P L.base M) L.P.bare cs →
    ArmRefinesT (L.A f).fb (L.A f).base ra (L.mach M f) s (Clif.runLoop L.base L.P (M + 1) cs)

def CrateStmtProduction (lower : ProductionLowering) (I : LinkInput) (cleanup : Bool) (n : String) : Prop :=
  ∀ (B : BaseEnv) (F : BitVec 64 → Prop),
    BaseOk (ofRes I (I.resultsProductionWith lower cleanup) B F) →
    (∀ a, (ofRes I (I.resultsProductionWith lower cleanup) B F).Img a → F a) →
    ProgStmtTS (ofRes I (I.resultsProductionWith lower cleanup) B F) n

theorem crate_correct_production (I : LinkInput) (cleanup : Bool)
    (hI : okRWithTS (productionStage cleanup) I (I.resultsProductionWith lower cleanup) = true) (n : String) :
    CrateStmtProduction lower I cleanup n :=
  fun _ _ hB hF f hf M _ _ _ _ _ hent hres hFeq hgfree himg hbe hargs hcs hsav hrel hpl htr =>
    backend_correct_programT _
      (okRWithTS_soundT (productionStage cleanup) (productionStage_cases cleanup)
        (I.resultsProductionWith_prepared lower cleanup) hI hB hF)
      (Clif.Program.func?_some hf).1 M hent hres hFeq hgfree himg hbe hargs hcs hsav hrel hpl htr

theorem crate_correct_stack {I : SemanticStackBound.CompilerInput}
    (hI : SemanticStackBound.okBTS I = true) {S : Nat}
    (hS : SemanticStackBound.stackB I = some S) (n : String) :
    SemanticStackBound.StackStmtTS I n := by
  intro B F hB hFI f hf
  have hf' : (progOf I.results).func? n = some f := hf
  have hn : SemanticStackBound.goodN I n = true := by
    unfold SemanticStackBound.goodN
    rw [hf']
    exact (SemanticStackBound.stackB_some hS).1 f (Clif.Program.func?_some hf').1
  exact SemanticStackBound.crate_correct_stackNTS hI hn B F hB hFI f hf

end E2E.TypedProductionChecks
