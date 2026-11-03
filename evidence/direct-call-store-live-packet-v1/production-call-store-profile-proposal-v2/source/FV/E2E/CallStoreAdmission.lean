import FV.E2E.ReturnPinAdmission

namespace E2E.LinkCheck
open Backend Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Internal admission adds the checked call-store class without changing any old profile. -/
def returnPinCallStoresExtra (f : Clif.Function) (vc : VCode) : Bool :=
  returnPinLiveCallsExtra f vc || Stock.CallStore.check f vc

def ReturnPinAdmission.callStores : ReturnPinAdmission where
  extra := returnPinCallStoresExtra
  compiled := by
    intro f vc vcp rf af fa fb cleanup k checked prepared prepOk check alloc emit layout
    apply CompiledSemanticReturnPins.of_checks_call_stores ?_ prepared prepOk check alloc emit layout
    simpa only [returnPinCallStoresExtra,returnPinLiveCallsExtra,returnPinResultCallsExtra,
      returnPinCallsExtra,SemanticABI.checkCallStores,SemanticABI.checkLiveCalls,
      SemanticABI.checkResultCalls,SemanticABI.checkCalls,SemanticABI.check,Bool.or_assoc] using checked

abbrev okRReturnPinCallStores := okRReturnPinFor ReturnPinAdmission.callStores

/-- Extending an internal artifact predicate preserves every previous program acceptance. -/
theorem okRReturnPinFor_mono {before after : ReturnPinAdmission}
    (extend : ∀ f vc, before.extra f vc = true → after.extra f vc = true)
    {stage : Clif.Function → VCode → VCode} {I : LinkInput} {R : Res}
    (previous : okRReturnPinFor before stage I R = true) :
    okRReturnPinFor after stage I R = true := by
  simp only [okRReturnPinFor,Bool.and_eq_true] at previous ⊢
  refine ⟨?_,previous.2⟩
  simp only [okRSemanticFor,chksSemanticFor,List.all_append,Bool.and_eq_true,List.all_eq_true] at previous ⊢
  refine ⟨previous.1.1,?_⟩
  intro e member
  have old := previous.1.2 e member
  refine ⟨?_,old.2⟩
  simp only [staticChksSemanticFor,List.all_map,List.all_eq_true,Function.comp_def] at old ⊢
  intro check present
  obtain ⟨raw,rawMember,rfl⟩ := List.mem_map.mp present
  have accepted := old.1 _ (List.mem_map.mpr ⟨raw,rawMember,rfl⟩)
  by_cases named : raw.1 = "compiled: lowerCheck"
  · simp only [named,↓reduceIte,Bool.or_eq_true] at accepted ⊢
    rcases accepted with ordinary | extra
    · exact Or.inl ordinary
    · exact Or.inr (extend _ _ extra)
  · simpa only [named,↓reduceIte] using accepted

theorem okRReturnPinCallStores_previous {stage : Clif.Function → VCode → VCode}
    {I : LinkInput} {R : Res} (previous : okRReturnPinLiveCalls stage I R = true) :
    okRReturnPinCallStores stage I R = true := by
  apply okRReturnPinFor_mono ?_ previous
  intro f vc accepted
  change returnPinLiveCallsExtra f vc = true at accepted
  change (returnPinLiveCallsExtra f vc || Stock.CallStore.check f vc) = true
  simp only [accepted,Bool.true_or]

end E2E.LinkCheck
