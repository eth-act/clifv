import StockPipelineProvenanceProbe
import StockActualCheckerProbe
import FV.Backend.Proof.StockD0PipelineWitness

namespace E2E.LinkCheck.ActualCodeProbe
open Backend

/-- Actual successful Stock output inhabits the callback-provenance theorem,
for every D0 configuration and allocator answer; no joint-rejection witness. -/
theorem actual_stock_witness (name : String) (c : Stock.D0.Configuration)
    (runs : List Clif.RunCommand) (k : Nat) (base : BitVec 64) (answer : Lean.Json) :
    ∃ (r : Stock.Result) (a : Art),
      Stock.lower (Stock.D0.source name c runs) = .ok r ∧
      pipeTWithLowering Stock.D0.defaultLower id (Stock.D0.source name c runs)
        k base answer = .ok a ∧
      a.vc = Stock.D0.compact name r ∧
      Stock.D0.defaultLower (Stock.D0.source name c runs) = .ok a.vc ∧
      prepare a.vc = .ok a.vcp ∧
      a.rf = allocResult a.vcp (readyAnswer a.vcp (raAnswer a.vcp answer)) := by
  obtain ⟨r, plain, clean, run, selected, hp, hc, code, cleanCode⟩ :=
    Stock.D0.complete_pipeline_witness name c runs k base answer
  have actual : pipeTWithLowering Stock.D0.defaultLower id
      (Stock.D0.source name c runs) k base answer = .ok plain := hp
  have facts := pipeTWithLowering_spec actual
  exact ⟨r, plain, run, actual, code, facts.1, facts.2.1, facts.2.2.1⟩

/-- Non-vacuity for the additive M7 contract: every D0 configuration has an
actual successful Stock artifact satisfying the source/preparation/allocation/
emission contract, for arbitrary names, run metadata and allocator answers. -/
theorem actual_stock_validated_witness (name : String) (c : Stock.D0.Configuration)
    (runs : List Clif.RunCommand) (k : Nat) (base : BitVec 64) (answer : Lean.Json) :
    ∃ (r : Stock.Result) (a : Art),
      Stock.lower (Stock.D0.source name c runs) = .ok r ∧
      pipeTWithLowering Stock.D0.defaultLower id (Stock.D0.source name c runs)
        k base answer = .ok a ∧
      a.vc = Stock.D0.compact name r ∧
      CompiledValidated (Stock.D0.source name c runs) a.k a.vc a.vcp
        a.rf a.af a.fa a.fb ∧ FormsCovered ⟨a.fa.k, a.af.slotBase⟩ a.vcp := by
  have input : fnScopeInB (Stock.D0.source name c runs) = true := by
    cases c <;> d0_open_kernel_decide
  have scope := fnScopeB_of_input input
  obtain ⟨r, a, run, actual, code, rest⟩ := actual_stock_witness name c runs k base answer
  obtain ⟨a', hp, lowerOk, prepOk, check, covered⟩ :=
    pipeT_ok scope spillDefinedHyp k base answer
  have samePipe : pipeTWithLowering Stock.D0.defaultLower id
      (Stock.D0.source name c runs) k base answer = .ok a' := hp
  have same : a' = a := Except.ok.inj (samePipe.symm.trans actual)
  subst a'
  obtain ⟨lower, prep, rf, alloc, emit, layout, index, addr⟩ := pipeTWithLowering_spec actual
  exact ⟨r, a, run, actual, code,
    ⟨⟨lowerOk, prep, prepOk, Backend.Proof.allocChecked_of_checkAlloc check,
      alloc, emit, layout⟩, check⟩, covered⟩

/-- Successful actual Stock artifacts inhabit the cleanup contract for all
D0 configurations, names, metadata and allocator answers. -/
theorem actual_stock_cleanup_validated_witness (name : String) (c : Stock.D0.Configuration)
    (runs : List Clif.RunCommand) (k : Nat) (base : BitVec 64) (answer : Lean.Json) :
    ∃ (r : Stock.Result) (a : Art),
      Stock.lower (Stock.D0.source name c runs) = .ok r ∧
      pipeCleanupT (Stock.D0.source name c runs) k base answer = .ok a ∧
      a.vc = Stock.D0.compact name r ∧
      CompiledCleanupValidated (Stock.D0.source name c runs) a.k a.vc a.vcp
        a.rf a.af a.fa a.fb ∧ FormsCovered ⟨a.fa.k, a.af.slotBase⟩ a.vcp := by
  have input : fnScopeInB (Stock.D0.source name c runs) = true := by
    cases c <;> d0_open_kernel_decide
  have scope := fnScopeB_of_input input
  obtain ⟨r, plain, clean, run, selected, hp, hc, code, cleanCode⟩ :=
    Stock.D0.complete_pipeline_witness name c runs k base answer
  obtain ⟨a, ha, lowerOk, prepOk, check, covered⟩ :=
    pipeCleanupT_ok scope spillDefinedHyp k base answer
  have same : a = clean := Except.ok.inj (ha.symm.trans hc)
  subst a
  obtain ⟨lower, prep, alloc, emit, layout, index, addr⟩ := pipeCleanupT_spec hc
  exact ⟨r, clean, run, hc, cleanCode,
    ⟨⟨lowerOk, prep, prepOk, Backend.Proof.allocChecked_of_checkAlloc check,
      alloc, emit, layout⟩, check⟩, covered⟩

/-- Both production constructors are inhabited by complete successful actual
Stock paths for the same input, in both cleanup modes. No fallback-only witness. -/
theorem actual_stock_production_modes_witness (name : String) (c : Stock.D0.Configuration)
    (runs : List Clif.RunCommand) (k : Nat) (base : BitVec 64) (answer : Lean.Json) :
    ∃ (r : Stock.Result) (plain clean : Art),
      Stock.lower (Stock.D0.source name c runs) = .ok r ∧
      pipeTWithLowering Stock.D0.defaultLower id (Stock.D0.source name c runs)
        k base answer = .ok plain ∧
      pipeCleanupT (Stock.D0.source name c runs) k base answer = .ok clean ∧
      plain.vc = Stock.D0.compact name r ∧ clean.vc = Stock.D0.compact name r ∧
      CompiledProduction (Stock.D0.source name c runs) plain.k plain.vc plain.vcp
        plain.rf plain.af plain.fa plain.fb ∧
      CompiledProduction (Stock.D0.source name c runs) clean.k clean.vc clean.vcp
        clean.rf clean.af clean.fa clean.fb := by
  obtain ⟨r, plain, run, hp, code, certificate, covered⟩ :=
    actual_stock_validated_witness name c runs k base answer
  obtain ⟨r', clean, run', hc, cleanCode, cleanCertificate, cleanCovered⟩ :=
    actual_stock_cleanup_validated_witness name c runs k base answer
  have same : r' = r := Except.ok.inj (run'.symm.trans run)
  subst r'
  exact ⟨r, plain, clean, run, hp, hc, code, cleanCode,
    .stock certificate, .stockCleanup cleanCertificate⟩

#print axioms actual_stock_cleanup_validated_witness
#print axioms actual_stock_production_modes_witness

#print axioms actual_stock_validated_witness

#print axioms actual_stock_witness
end E2E.LinkCheck.ActualCodeProbe
