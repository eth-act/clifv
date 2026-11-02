import FV.Backend.Proof.StockCriticalCode
import FV.Backend.Proof.StockPerEdgeValues
import FV.Backend.Proof.StockSelectedGraph

/-! Source-selected successor copies, deriving the lowered route internally. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- The source target index; successful source binding proves the default
unreachable, rather than imposing another accepted-program condition. -/
def sourceTargetIndex (f : Clif.Function) (bc : Clif.BlockCall) : Nat :=
  (blockIdx? f bc.block).getD 0

def sourceTargetParams (f : Clif.Function) (bc : Clif.BlockCall) : List Nat :=
  ((f.block? bc.block).getD default).params.map (·.1)

/-- Actual selected copies, directly or via a real emitted synthetic jump.
Successful actual VCode CFG correspondence is a separate execution obligation. -/
inductive SelectedCopyRoute (result : Result) (label index : Nat) (ρ : Nat → CV)
    (targetLabel : Nat) (ρ' : Nat → CV) : Prop
  | direct : result.order.successors[label]![index]? = some targetLabel →
      edgeEnvAt result.code result.edgeArgs label targetLabel index ρ = some ρ' →
      SelectedCopyRoute result label index ρ targetLabel ρ'
  | synthetic {middle : Nat} : result.order.successors[label]![index]? = some middle →
      edgeEnvAt result.code result.edgeArgs label middle index ρ = some ρ →
      result.order.successors[middle]? = some #[targetLabel] →
      (∃ block : VBlock,result.code.blocks[middle]? = some block ∧ block.insts = #[.jump targetLabel]) →
      edgeEnvAt result.code result.edgeArgs middle targetLabel 0 ρ = some ρ' →
      SelectedCopyRoute result label index ρ targetLabel ρ'

/-- Actual successful source successor binding selects a direct or synthetic
lowered copy route and preserves held values. Target lookup/index, graph case,
nonentry, vectors, helper runs and assembly are all derived internally. -/
theorem stock_lower_selected_route_values {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {label bi index : Nat} {b : Clif.Block} {bc : Clif.BlockCall}
    (tag : result.order.nodes[label]? = some (.original bi)) (source : f.blocks[bi]? = some b)
    (selected : (dests b.term)[index]? = some bc)
    {fr fr' : Clif.Frame} (func : fr.func = f) (entered : Clif.enterBlock fr bc = .ok fr')
    {needed : Nat → Prop}
    (available : ∀ x,needed x → x ∈ availOf f (availIn f result.ctx) (sourceTargetIndex f bc) 0)
    {ρ : Nat → CV} (held : ValuesHeld
      (fun x => x ∈ bc.args ∨ (needed x ∧ x ∉ sourceTargetParams f bc)) result.ctx fr
      (fun key => ρ (aliasNum result.final.alias key))) :
    ∃ tl targetLabel ρ',blockIdx? f bc.block = some tl ∧
      result.order.nodes[targetLabel]? = some (.original tl) ∧
      SelectedCopyRoute result label index ρ targetLabel ρ' ∧
      ValuesHeld needed result.ctx fr' (fun key => ρ' (aliasNum result.final.alias key)) := by
  obtain ⟨tl,middle,targetIndex,nonentry,successor,node⟩ := stock_lower_selected_successor run scope tag source selected
  obtain ⟨targetBlock,args,regs,found,read,types,set,frame⟩ := enterBlock_spec entered
  rw [func] at found
  have targetAvailable : ∀ x,needed x → x ∈ availOf f (availIn f result.ctx) tl 0 := by
    simpa only [sourceTargetIndex,targetIndex,Option.getD_some] using available
  have targetHeld : ValuesHeld
      (fun x => x ∈ bc.args ∨ (needed x ∧ x ∉ targetBlock.params.map (·.1))) result.ctx fr
      (fun key => ρ (aliasNum result.final.alias key)) := by
    simpa only [sourceTargetParams,found,Option.getD_some] using held
  rcases node with original | synthetic
  · obtain ⟨ρ',copy,transfer⟩ := stock_lower_direct_per_edge_values run scope dominated tag source selected
      successor original targetIndex func found entered targetAvailable targetHeld
    exact ⟨tl,middle,ρ',targetIndex,original,.direct successor copy,transfer⟩
  · obtain ⟨targetLabel,ρ',targetTag,successors,copy,transfer⟩ := stock_lower_critical_per_edge_values run scope
      dominated synthetic source selected targetIndex func found entered targetAvailable targetHeld
    obtain ⟨input,next,registers,placedLabel,call,placedSuccessors,placedTag,placed⟩ :=
      stock_lower_critical_code run synthetic
    have same : placedLabel = targetLabel := by
      have equal := Option.some.inj (placedSuccessors.symm.trans successors)
      simpa using congrArg (fun xs : Array Nat => xs[0]!) equal
    subst placedLabel
    have deferred := stock_lower_deferred_outgoing run tag successor synthetic
    have identity : edgeEnvAt result.code result.edgeArgs label middle index ρ = some ρ := by
      have empty : parCopyEnv ρ [] [] = ρ := by funext x; rfl
      simpa only [empty] using (edgeEnvAt_eq (ps := []) (xs := []) placed deferred rfl rfl ρ)
    exact ⟨tl,targetLabel,ρ',targetIndex,targetTag,
      .synthetic successor identity successors ⟨_,placed,rfl⟩ copy,transfer⟩
end Backend.Stock.Proof
