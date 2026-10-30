import FV.Backend.Proof.StockCfgTotal
import FV.Backend.Proof.StockNodeCoverageWitness
import FV.Backend.Proof.StockBranchTargetsWitness
import FV.Backend.Proof.StockEmittedGraphWitness

namespace Backend.Stock.Proof.CfgTotalWitness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

private def ty (kind : Fin 3) : Clif.Ty := if kind.val = 2 then .i32 else .i64
private def sourceBody (kind : Fin 3) : List Clif.Stmt :=
  if kind.val = 2 then [] else
    [⟨[13],.iconst .i64 8⟩,⟨[17],.binary .band .i64 7 13⟩] ++
      if kind.val = 1 then [⟨[19],.iconst .i64 0⟩,⟨[23],.icmp .eq .i64 17 19⟩] else []
private def sourceTerm (kind : Fin 3) : Clif.Terminator :=
  if kind.val = 2 then .brTable 7 ⟨1,[7]⟩ [⟨2,[7]⟩,⟨3,[7]⟩]
  else .brif (if kind.val = 1 then 23 else 17) ⟨1,[7]⟩ ⟨2,[7]⟩
private def function (kind : Fin 3) : Clif.Function := {
  name := "stock_branch_target_cases"
  sig := {params := [⟨ty kind,.none,.normal⟩],returns := [⟨ty kind,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(7,ty kind)],body := sourceBody kind,term := sourceTerm kind},
    {id := 1,params := [(31,ty kind)],term := .ret [31]},
    {id := 2,params := [(47,ty kind)],term := .ret [47]}] ++
    if kind.val = 2 then [{id := 3,params := [(59,ty kind)],term := .ret [59]}] else [] }

/-- Complete priority-test-bit and table source programs inhabit the whole CFG
and raw/checked preparation theorems, with their actual original entry-node
terminator and computed target row. Original scope and dominance are retained. -/
theorem stock_branch_cfg_prepare_witness (kind : Fin 3) :
    ∃ (result : Result) (block : VBlock) (last : MInst) (prepared : EdgeVCode),
      Stock.lower (function kind) = .ok result ∧ LowerScope (function kind) ∧ Dominated (function kind) ∧
      result.order.nodes[0]? = some (.original 0) ∧ result.code.blocks[0]? = some block ∧
      block.insts.back? = some last ∧ last.isTerminator = true ∧
      last.targets = result.order.successors[0]!.toList ∧
      Prep.CfgSpec result.code.blocks result.order.successors ∧
      prepareAt result.code result.edgeArgs = .ok prepared ∧
      prepareCheckedAt result.code result.edgeArgs = .ok prepared ∧
      PerEdgePrep.prepCheckAt result.code result.edgeArgs prepared = true := by
  obtain ⟨result,out,next,trace,run,scope,dominated,_⟩ := BranchTargetsWitness.stock_branch_named_targets_witness kind
  change Stock.lower (function kind) = .ok result at run
  change LowerScope (function kind) at scope
  change Dominated (function kind) at dominated
  have node := stock_blockOrder_entry (stock_lower_order run) scope.nonempty
  have ord : OrdinaryCfg.ordinary (function kind).blocks[0]!.term = true := by
    have cases : kind.val = 0 ∨ kind.val = 1 ∨ kind.val = 2 := by omega
    rcases cases with h | h | h <;> simp [function,sourceTerm,OrdinaryCfg.ordinary,h]
  obtain ⟨block,last,placed,back,ends,targets⟩ := OrdinaryCfg.stock_lower_ordinary_targets run scope node ord
  obtain ⟨prepared,raw,checked,accepted⟩ := stock_prepare_total run scope
  exact ⟨result,block,last,prepared,run,scope,dominated,node,placed,back,ends,targets,
    stock_lower_cfg run scope,raw,checked,accepted⟩

/-- A complete critical-edge source driver also passes whole CFG and indexed
preparation, including its actual synthetic edge node; no graph verdict is supplied. -/
theorem stock_critical_cfg_prepare_witness :
    ∃ (f : Clif.Function) (result : Result) (prepared : EdgeVCode),
      Stock.lower f = .ok result ∧ LowerScope f ∧
      (∃ (label pred index target : Nat),result.order.nodes[label]? = some (Node.edge pred index target)) ∧
      Prep.CfgSpec result.code.blocks result.order.successors ∧
      prepareAt result.code result.edgeArgs = .ok prepared ∧
      prepareCheckedAt result.code result.edgeArgs = .ok prepared ∧
      PerEdgePrep.prepCheckAt result.code result.edgeArgs prepared = true := by
  obtain ⟨f,result,label,pred,index,target,run,scope,_,_,node,_⟩ := EmittedGraphWitness.stock_critical_cfg_witness
  obtain ⟨prepared,raw,checked,accepted⟩ := stock_prepare_total run scope
  exact ⟨f,result,prepared,run,scope,⟨label,pred,index,target,node⟩,stock_lower_cfg run scope,raw,checked,accepted⟩

/-- Every supported scalar/two-result/implicit-sret complete return fixture
inhabits the whole graph and unconditional indexed preparation composition. -/
theorem stock_return_cfg_prepare_witness (p : ReturnFixture.Case) :
    ∃ (result : Result) (prepared : EdgeVCode),
      Stock.lower (ReturnFixture.function p) = .ok result ∧ LowerScope (ReturnFixture.function p) ∧
      Dominated (ReturnFixture.function p) ∧ Prep.CfgSpec result.code.blocks result.order.successors ∧
      prepareAt result.code result.edgeArgs = .ok prepared ∧
      prepareCheckedAt result.code result.edgeArgs = .ok prepared ∧
      PerEdgePrep.prepCheckAt result.code result.edgeArgs prepared = true := by
  obtain ⟨result,vb,last,run,scope,dominated,_⟩ := NodeCoverageWitness.stock_return_node_cfg_witness p
  obtain ⟨prepared,raw,checked,accepted⟩ := stock_prepare_total run scope
  exact ⟨result,prepared,run,scope,dominated,stock_lower_cfg run scope,raw,checked,accepted⟩

/-- A complete original-scope/dominated coded-trap source also inhabits the
whole graph and raw/checked preparation results. -/
theorem stock_trap_cfg_prepare_witness :
    ∃ (f : Clif.Function) (result : Result) (prepared : EdgeVCode),
      Stock.lower f = .ok result ∧ LowerScope f ∧ Dominated f ∧ f.blocks[0]!.term = .trap (.user 9) ∧
      Prep.CfgSpec result.code.blocks result.order.successors ∧
      prepareAt result.code result.edgeArgs = .ok prepared ∧
      prepareCheckedAt result.code result.edgeArgs = .ok prepared ∧
      PerEdgePrep.prepCheckAt result.code result.edgeArgs prepared = true := by
  obtain ⟨result,vb,last,run,scope,dominated,_⟩ := NodeCoverageWitness.stock_trap_node_cfg_witness
  obtain ⟨prepared,raw,checked,accepted⟩ := stock_prepare_total run scope
  exact ⟨_,result,prepared,run,scope,dominated,rfl,stock_lower_cfg run scope,raw,checked,accepted⟩

/-- Both complete direct/indirect TryCall programs with real tag/default/normal
successors inhabit the complete CFG and indexed preparation results. -/
theorem stock_try_cfg_prepare_witness (indirect : Bool) :
    ∃ (f : Clif.Function) (result : Result) (prepared : EdgeVCode),
      Stock.lower f = .ok result ∧ LowerScope f ∧ Dominated f ∧ f.blocks[0]!.term.isTry = true ∧
      Prep.CfgSpec result.code.blocks result.order.successors ∧
      prepareAt result.code result.edgeArgs = .ok prepared ∧
      prepareCheckedAt result.code result.edgeArgs = .ok prepared ∧
      PerEdgePrep.prepCheckAt result.code result.edgeArgs prepared = true := by
  obtain ⟨result,vb,last,replaced,run,scope,dominated,_⟩ := EmittedGraphWitness.stock_try_targets_witness indirect
  obtain ⟨prepared,raw,checked,accepted⟩ := stock_prepare_total run scope
  refine ⟨_,result,prepared,run,scope,dominated,?_,stock_lower_cfg run scope,raw,checked,accepted⟩
  cases indirect <;> rfl

end Backend.Stock.Proof.CfgTotalWitness
