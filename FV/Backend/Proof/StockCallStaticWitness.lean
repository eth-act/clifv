import FV.Backend.Proof.StockCallStaticObservation
namespace Backend.Stock.Proof.CallStaticWitnessDraft
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.Cov Backend.Proof.PerEdgePrep Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.CallStaticFixture Backend.Stock.Proof.CallOutputStaticDraft Backend.Stock.Proof.CallAbiStaticDraft
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm Stock.lower Stock.externCtor

private theorem ctor_ok {ctx : Ctx} {term : Term} {args : List V} {st next : State} {v : V}
    (run : ctorAt ctx term args st = .ok (v,next)) : Stock.externCtor ctx term args st = .ok (v,next) := by
  unfold ctorAt at run
  cases actual : Stock.externCtor ctx term args st with
  | fail => rw [actual] at run; cases run
  | unmodeled error => rw [actual] at run; cases run
  | ok pair => rw [actual] at run; cases run; rfl

/-- Four complete original caller pipelines and their real helper protocols
inhabit all fresh-output, return-pin and direct/indirect call-static contracts.
Returned/prepared programs contain actual calls; direct ordinary code has nine
arguments and a real stack store. Protocol calls use the SAME built context and
initial allocation; selected-root/record composition is a separate obligation. -/
theorem stock_complete_call_static_witness (indirect implicit : Bool) :
    ∃ out : Output,pipeline indirect implicit = .ok out ∧
      LowerScope (function indirect implicit) ∧ Dominated (function indirect implicit) ∧
      ArityOk (function indirect implicit) ∧ sigAbiOk (signature indirect implicit) = true ∧
      Stock.lower (function indirect implicit) = .ok out.result ∧
      prepareAt out.result.code out.result.edgeArgs = .ok out.prepared ∧
      out.rf = spillAllocAt out.prepared.code out.prepared.edges ∧
      checkAllocAt out.prepared.code out.prepared.edges out.rf = .ok () ∧
      lowerRFunc out.prepared.code out.rf = .ok out.af ∧ Facts indirect implicit out ∧
      Stock.externCtor out.result.ctx T.gen_call_output [.op (.sig (signature indirect implicit))] out.result.initial = .ok (out.outs,out.afterOut) ∧
      Stock.externCtor out.result.ctx T.gen_call_rets [.op (.sig (signature indirect implicit)),out.outs] out.afterOut = .ok (out.defs,out.afterPins) ∧
      Stock.externCtor out.result.ctx T.gen_call_args [.op (.sig (signature indirect implicit)),
        .regsVec (((numbers indirect implicit).map fun n => Reg.vreg n .int).map fun r => [r])] out.afterPins = .ok (out.uses,out.afterArgs) ∧
      Stock.externCtor out.result.ctx (infoTerm indirect)
        (infoArgs indirect (signature indirect implicit) calleeName (target out.result) out.uses out.defs) out.afterArgs = .ok (out.info,out.afterInfo) ∧
      (out.outs = .regsVec (outRegs out.result.initial.base (signature indirect implicit).returns.length) ∧
        out.afterOut = {out.result.initial with base := freshN out.result.initial.base (signature indirect implicit).returns.length} ∧
        out.afterPins = out.afterOut ∧ (signature indirect implicit).returns.length ≤ 8 ∧
        out.defs = .op (.callRets (callDefs (outDefs out.result.initial.base.nextVreg (signature indirect implicit).returns.length))) ∧
        CallOk out.result.initial.base.nextVreg [] (outDefs out.result.initial.base.nextVreg (signature indirect implicit).returns.length) ∧
        (∀ q ∈ outDefs out.result.initial.base.nextVreg (signature indirect implicit).returns.length,
          out.result.initial.base.nextVreg ≤ q.2 ∧ q.2 < out.afterOut.base.nextVreg) ∧
        out.afterOut.base.emitted = out.result.initial.base.emitted) ∧
      ∃ (locs : List ArgLoc) (bytes : List Nat) (stack : Nat) (call : CallInfo),
        sigParamBytes (signature indirect implicit) = .ok bytes ∧ sigArgLocs (signature indirect implicit) = .ok (locs,stack) ∧
        out.uses = .op (.callArgs (retPairs (regPairsOf ((locs.zip (numbers indirect implicit)).zip bytes)))) ∧
        out.defs = .op (.callRets (callDefs (outDefs out.result.initial.base.nextVreg (signature indirect implicit).returns.length))) ∧
        out.info = .op (.callInfo call) ∧
        call = ⟨if indirect then .reg (.vreg (target out.result) .int) else .sym calleeName,
          retPairs (regPairsOf ((locs.zip (numbers indirect implicit)).zip bytes)),callDefs (outDefs out.result.initial.base.nextVreg (signature indirect implicit).returns.length)⟩ ∧
        CallOk out.result.initial.base.nextVreg (regPairsOf ((locs.zip (numbers indirect implicit)).zip bytes))
          (outDefs out.result.initial.base.nextVreg (signature indirect implicit).returns.length) ∧
        SpillInstOk (.call call) ∧
        out.afterArgs = {out.afterPins with base.emitted := out.afterPins.base.emitted ++
          ((stackEnts ((locs.zip (numbers indirect implicit)).zip bytes)).map argStore).toArray} ∧
        out.afterPins = out.afterOut ∧ out.afterInfo = {out.afterArgs with base.outgoing := max out.afterArgs.base.outgoing stack} := by
  have actual := observed indirect implicit
  unfold Observed at actual
  cases run : pipeline indirect implicit with
  | error error => simp only [run,Except.toOption,Option.map_none] at actual; cases actual
  | ok out =>
    rw [run] at actual
    simp only [Except.toOption,Option.map_some,Option.some.injEq] at actual
    have facts : Facts indirect implicit out := of_decide_eq_true actual
    unfold pipeline at run
    obtain ⟨result,lowered,h⟩ := Except.bind_ok run
    obtain ⟨prepared,prepare,h⟩ := Except.bind_ok h
    obtain ⟨rf,allocated,h⟩ := Except.bind_ok h
    obtain ⟨af,physical,h⟩ := Except.bind_ok h
    obtain ⟨⟨outs,afterOut⟩,output,h⟩ := Except.bind_ok h
    obtain ⟨⟨defs,afterPins⟩,pins,h⟩ := Except.bind_ok h
    obtain ⟨⟨uses,afterArgs⟩,args,h⟩ := Except.bind_ok h
    obtain ⟨⟨info,afterInfo⟩,formed,h⟩ := Except.bind_ok h
    cases h
    have outputRun := ctor_ok output
    have pinRun := ctor_ok pins
    have argRun := ctor_ok args
    have infoRun := ctor_ok formed
    have checked := PerEdge.allocResultAt_checked allocated
    have fallback : rf = spillAllocAt prepared.code prepared.edges := by
      unfold allocResultAt checkedSpillAt at allocated
      simp only [bind,Except.bind] at allocated
      split at allocated <;> cases allocated
      rfl
    obtain ⟨scope,dominated,arity,abi⟩ := source_conditions indirect implicit
    have fresh := stock_gen_call_rets_fresh_defs outputRun pinRun
    have static := stock_call_helpers_static abi indirect calleeName (target result) outputRun argRun pinRun infoRun
    exact ⟨_,rfl,scope,dominated,arity,abi,lowered,prepare,fallback,checked,physical,facts,
      outputRun,pinRun,argRun,infoRun,fresh,static⟩
end Backend.Stock.Proof.CallStaticWitnessDraft
