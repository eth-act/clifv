module

public import FV.Backend.Proof.StockPureDriverUnsunk
public import FV.Backend.Proof.StockTerminalDriverWitness

@[expose] public section

/-! Actual critical-edge and effectful runs inhabit the complete driver frame.
These reuse the existing kernel witnesses and retain their original claims. -/
namespace Backend.Stock.Proof.PureDriverWitness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

theorem critical_edges :
    ∃ (f : Clif.Function) (result : Result),
      Stock.lower f = .ok result ∧ LowerScope f ∧ f.blocks.length = 2 ∧ result.order.nodes.size = 4 ∧
      (∃ pred k target,.edge pred k target ∈ result.order.nodes.toList) ∧
      ZeroColorLe result.initial result.final ∧ RecordsZeroColorLe result.initial result.blockScans := by
  obtain ⟨f,result,run,scope,blocks,nodes,edge,rest⟩ :=
    TerminalDriverWitness.stock_critical_driver_unsunk_witness
  exact ⟨f,result,run,scope,blocks,nodes,edge,(stock_lower_zeroColorLe run).1,
    (stock_lower_zeroColorLe run).2⟩

theorem effect_sink :
    ∃ (f : Clif.Function) (result : Result) (event : BlockScanEvent) (record : ScanRecord)
      (out : V) (next : State) (rules : List RuleId),
      Stock.lower f = .ok result ∧ LowerScope f ∧ event ∈ result.blockScans.toList ∧
      record ∈ event.output.records ∧
      Stock.runTerm event.ctx "lower" [.inst record.inst] (scanState record.input record.inst) =
        .ok (some out,next,rules) ∧
      (scanState record.input record.inst).sunk = #[false,false,false] ∧ next.sunk = #[true,false,false] ∧
      ZeroColorLe result.initial result.final ∧ RecordsZeroColorLe result.initial result.blockScans := by
  obtain ⟨f,result,event,record,step,out,next,rules,run,scope,events,records,
    recorded,emitted,current,size,slot,before,after,root,rest⟩ :=
      TerminalDriverWitness.stock_atomic_driver_unsunk_witness
  exact ⟨f,result,event,record,out,next,rules,run,scope,events,records,root,before,after,
    (stock_lower_zeroColorLe run).1,(stock_lower_zeroColorLe run).2⟩
end Backend.Stock.Proof.PureDriverWitness
