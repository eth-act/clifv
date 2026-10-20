import FV.Backend.Proof.StockPrepareTotal
import FV.Backend.Proof.StockPrepareCompleteWitness
import FV.Backend.Proof.StockPerEdgeCriticalAllocatorWitness
import FV.Backend.Proof.StockTermContractWitness

namespace Backend.Stock.Proof.EntryWitness
open Backend.Proof Backend.Proof.Driver

private def EntryFacts (f : Clif.Function) (result : Result) : Prop :=
  result.order.nodes[0]? = some (.original 0) ∧
  (∃ block,result.code.blocks[0]? = some block ∧ block.label = 0 ∧ block.params = #[]) ∧
  (∀ pred index,Node.edge pred index 0 ∉ result.order.nodes.toList) ∧
  (∀ (label : Nat) (row : Array Nat),result.order.successors[label]? = some row → 0 ∉ row.toList) ∧
  ∃ source,stockSourceTable f = .ok source ∧
    ∀ (b : Nat) (row : Array Nat),source[b]? = some row → 0 ∉ row.toList

private theorem entry_facts {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) : EntryFacts f result := by
  have ordered := stock_lower_order run
  obtain ⟨_,entry,placed,label,params⟩ := stock_lower_entry_code run scope
  obtain ⟨source,computed,_⟩ := stock_blockOrder_sourceTable ordered
  exact ⟨stock_blockOrder_entry ordered scope.nonempty,⟨entry,placed,label,params⟩,
    stock_blockOrder_edges_nonentry ordered scope,stock_lower_graph_nonentry run scope,
    source,computed,stock_sourceTable_nonentry computed scope⟩

/-- The complete original-scope/dominated conditional Stock program inhabits
actual entry order/code, parameterlessness and all source/computed no-entry facts. -/
theorem stock_conditional_entry_witness :
    ∃ (f : Clif.Function) (result : Result),Stock.lower f = .ok result ∧ LowerScope f ∧
      Dominated f ∧ EntryFacts f result := by
  obtain ⟨f,result,p,run,scope,dominated,_⟩ := PrepareCompleteWitness.stock_prepare_complete_return_witness
  exact ⟨f,result,run,scope,dominated,entry_facts run scope⟩

/-- Parallel critical edges are inserted after actual entry0; the complete
original source still supplies parameterlessness and every no-entry graph fact. -/
theorem stock_critical_entry_witness :
    ∃ (f : Clif.Function) (result : Result) (p : EdgeVCode),Stock.lower f = .ok result ∧
      LowerScope f ∧ Dominated f ∧ EntryFacts f result ∧
      prepareAt result.code result.edgeArgs = .ok p ∧
      p.edges[1]? = some #[#[Reg.vreg 192 .int]] ∧ p.edges[2]? = some #[#[Reg.vreg 192 .int]] := by
  obtain ⟨result,p,rf,af,run,scope,dominated,prepared,_,e1,e2,_⟩ :=
    PerEdgeCriticalAllocatorWitness.stock_per_edge_critical_allocator_fallback_witness
  exact ⟨_,result,p,run,scope,dominated,entry_facts run scope,prepared,e1,e2⟩

private def trapFunction : Clif.Function := {
  name := "stock_trap_abi_contract",sig := {callConv := some .systemV}
  blocks := [{id := 0,term := .trap (.user 9)}] }

/-- A complete actual original-scope/dominated source trap derives emitted
CFG correspondence from its actual UDF code, then reaches raw/checked preparation
by totality rather than assuming raw success. Real csem halt/coded-trap
observations are preserved for every initial world/register file. -/
theorem stock_trap_preparation_total_witness :
    ∃ (result : Result) (prepared : EdgeVCode),Stock.lower trapFunction = .ok result ∧
      LowerScope trapFunction ∧ Dominated trapFunction ∧ EntryFacts trapFunction result ∧
      Prep.CfgSpec result.code.blocks result.order.successors ∧
      prepareAt result.code result.edgeArgs = .ok prepared ∧
      prepareCheckedAt result.code result.edgeArgs = .ok prepared ∧
      PerEdgePrep.prepCheckAt result.code result.edgeArgs prepared = true ∧
      ∀ (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) (w : Arm.ArmState) (ρ : Nat → CV),
        Star (VStepAt result.code result.edgeArgs (csem F ctx X)) (VConf.init ρ w) (.halt w) ∧
        Star (VStepAt prepared.code prepared.edges (csem F ctx X)) (VConf.init ρ w) (.halt w) ∧
        PerEdgePrep.VTrapFromAt result.code result.edgeArgs (csem F ctx X) ⟨0,0,ρ,w⟩ (.user 9) ∧
        PerEdgePrep.VTrapFromAt prepared.code prepared.edges (csem F ctx X) ⟨0,0,ρ,w⟩ (.user 9) := by
  obtain ⟨result,old,rf,af,lowered,scope,dominated,_,_,_,_,runs⟩ :=
    PreparedForwardWitness.stock_prepared_halt_forward_witness
  change Stock.lower trapFunction = .ok result at lowered
  change LowerScope trapFunction at scope
  change Dominated trapFunction at dominated
  obtain ⟨result',lowered',_,code,_⟩ := TermContractWitness.stock_trap_term_contract_witness
  change Stock.lower trapFunction = .ok result' at lowered'
  rw [lowered] at lowered'
  cases lowered'
  have computed : blockOrder trapFunction = .ok ⟨#[.original 0],#[#[]]⟩ := by cbv
  have order : result.order = ⟨#[.original 0],#[#[]]⟩ :=
    Except.ok.inj ((stock_lower_order lowered).symm.trans computed)
  have dimensions := stock_prepare_dimensions lowered
  have size : result.code.blocks.size = 1 := by rw [← dimensions.1,dimensions.2.1,order]; rfl
  have graph : Prep.CfgSpec result.code.blocks result.order.successors := by
    refine ⟨by rw [order,size]; rfl,?_⟩
    intro b vb lookup
    have bound := (Array.getElem?_eq_some_iff.mp lookup).1
    have zero : b = 0 := by rw [size] at bound; omega
    subst b
    have equal : vb = result.code.blocks[0]! := by
      rw [Array.getElem!_eq_getD,Array.getD_eq_getD_getElem?,lookup]
      rfl
    refine ⟨.udf (.user 9),#[],?_,rfl,by rw [order]; rfl,rfl,?_⟩
    · rw [equal,code]
      rfl
    · intro j l impossible
      simp [MInst.targets] at impossible
  obtain ⟨prepared,raw,checked,accepted⟩ := stock_prepare_total_of_graph lowered scope graph
  refine ⟨result,prepared,lowered,scope,dominated,entry_facts lowered scope,graph,raw,checked,accepted,?_⟩
  intro F ctx X w ρ
  obtain ⟨source,_,observation,_⟩ := runs F ctx X w ρ (fun _ => 0)
  have sem := (driverSem_csem F ctx X).toDriverSemG
  exact ⟨source,stock_prepare_halt lowered scope raw sem source,observation,
    (stock_prepare_sound lowered scope raw sem ρ w).2 (.user 9) observation⟩

end Backend.Stock.Proof.EntryWitness
