import FV.Backend.StockFloatCallStoreCheck

namespace Backend.Stock.FloatCallStore
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false

/-- The checker supplies these source facts internally. -/
structure SourceFacts (f : Clif.Function) (data : SourceData) : Prop where
  blocks : f.blocks = [data.block]
  parameters : data.block.params = [(data.pointer,.i64),(data.argument,.f64)]
  body : data.block.body = [⟨[data.called],.call data.fn [data.argument]⟩, ⟨[],.store .store .f64 data.flags data.called data.pointer 8⟩]
  term : data.block.term = .ret [data.called]
  parameterTypes : f.sig.params.map (·.ty) = [.i64,.f64]
  returnTypes : f.sig.returns.map (·.ty) = [.f64]
  callParameterTypes : data.ext.sig.params.map (·.ty) = [.f64]
  callReturns : data.ext.sig.returns = [data.returned]
  returnedType : data.returned.ty = .f64
  extern : f.extern? data.fn = some data.ext
  pins : returnPins f 1 = some [.v 0]
  pointerNotCalled : data.pointer ≠ data.called
  argumentNotCalled : data.argument ≠ data.called
  pointerNotArgument : data.pointer ≠ data.argument
  flags : data.flags = {}
  callArgumentBytes : (sigParamBytes data.ext.sig).toOption = some [8]

/-- Decode the checked source shape without a caller certificate. -/
theorem sourceFacts_of_sourceB {f : Clif.Function} {data : SourceData}
    (accepted : sourceB f data = true) : SourceFacts f data := by
  simp only [sourceB, Bool.and_eq_true, decide_eq_true_eq] at accepted
  rcases accepted with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hBlocks,hParameters⟩,hBody⟩,hTerm⟩,hParameterTypes⟩,hReturnTypes⟩,hCallParameterTypes⟩,hCallReturns⟩,hReturnedType⟩,hExtern⟩,hPins⟩,hPointerNotCalled⟩,hArgumentNotCalled⟩,hPointerNotArgument⟩,hFlags⟩,hCallArgumentBytes⟩
  exact ⟨hBlocks,hParameters,hBody,hTerm,hParameterTypes,hReturnTypes,hCallParameterTypes,hCallReturns,hReturnedType,hExtern,hPins,hPointerNotCalled,hArgumentNotCalled,hPointerNotArgument,hFlags,hCallArgumentBytes⟩

/-- Actual checker success retains the extracted source and its facts. -/
theorem sourceFacts_of_check {f : Clif.Function} {vc : VCode}
    (accepted : check f vc = true) :
    ∃ data, sourceData? f = some data ∧ SourceFacts f data := by
  unfold check at accepted
  cases extracted : sourceData? f with
  | none => simp [extracted] at accepted
  | some data =>
    simp only [extracted] at accepted
    have first := (Bool.and_eq_true.mp accepted).1
    have second := (Bool.and_eq_true.mp first).1
    have third := (Bool.and_eq_true.mp second).1
    have source := (Bool.and_eq_true.mp third).1
    exact ⟨data,extracted,sourceFacts_of_sourceB source⟩

/-- The original ABI computation selects v0 for this checked result. -/
theorem check_returnPins {f : Clif.Function} {vc : VCode}
    (accepted : check f vc = true) : returnPins f 1 = some [.v 0] := by
  obtain ⟨data,_,facts⟩ := sourceFacts_of_check accepted
  exact facts.pins

/-- Checker success retains the default trapping flags. -/
theorem check_default_flags {f : Clif.Function} {vc : VCode}
    (accepted : check f vc = true) :
    ∃ data, sourceData? f = some data ∧ data.flags = {} := by
  obtain ⟨data,extracted,facts⟩ := sourceFacts_of_check accepted
  exact ⟨data,extracted,facts.flags⟩

/-- The integer pointer and floating value remain separate ABI parameters. -/
theorem check_parameter_types {f : Clif.Function} {vc : VCode}
    (accepted : check f vc = true) :
    f.sig.params.map (·.ty) = [.i64,.f64] ∧ f.sig.returns.map (·.ty) = [.f64] := by
  obtain ⟨data,_,facts⟩ := sourceFacts_of_check accepted
  exact ⟨facts.parameterTypes,facts.returnTypes⟩

end Backend.Stock.FloatCallStore
