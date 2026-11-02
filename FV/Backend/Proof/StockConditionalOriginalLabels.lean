import FV.Backend.Proof.StockConditionalArgsAt
import FV.Backend.Proof.StockConditionalBodyCalls
import FV.Backend.Proof.StockSelectedGraph

/-! When the lowered order has only original nodes, the actual successor labels of any
conditional block on a parameter are two original blocks. These are the label premises of the
argument-carrying compositions (`returning/trapping_original_parameter_at`) at any block. -/

namespace Backend.Stock.Proof.ConditionalValues
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- Every node of an order with only original nodes is original. -/
def OriginalOrder (order : Order) : Prop :=
  ∀ (label : Nat) (node : Node),order.nodes[label]? = some node → ∃ bi,node = .original bi

/-- A selected successor of an original block in an all-original order is an original block at
the selected label. -/
theorem original_selected_successor {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (original : OriginalOrder result.order)
    {label bi index : Nat} {b : Clif.Block} {bc : Clif.BlockCall}
    (tag : result.order.nodes[label]? = some (.original bi))
    (block : f.blocks[bi]? = some b) (selected : (dests b.term)[index]? = some bc) :
    ∃ target targetLabel,blockIdx? f bc.block = some target ∧ target ≠ 0 ∧
      result.order.successors[label]![index]? = some targetLabel ∧
      result.order.nodes[targetLabel]? = some (.original target) := by
  obtain ⟨target,targetLabel,lookup,nonentry,successor,node⟩ :=
    stock_lower_selected_successor run scope tag block selected
  refine ⟨target,targetLabel,lookup,nonentry,successor,?_⟩
  rcases node with node | synthetic
  · exact node
  · obtain ⟨_,same⟩ := original _ _ synthetic
    cases same

/-- The two actual successor labels of a conditional block on a parameter are original blocks. -/
theorem ConditionalBodySpec.original_successor_labels {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (original : OriginalOrder result.order)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (tag : result.order.nodes[label]? = some (.original bi))
    (block : f.blocks[bi]? = some b) (term : b.term = .brif c yes no)
    (parameter : result.ctx.defInst? c = none) :
    ∃ first second yesBlock noBlock,result.order.successors[label]! = #[first,second] ∧
      result.order.nodes[first]? = some (.original yesBlock) ∧
      result.order.nodes[second]? = some (.original noBlock) := by
  obtain ⟨calls,_⟩ := spec.parameter_calls block term parameter
  have labels : result.order.successors[label]! = #[calls.yes,calls.no] := Array.toList_inj.mp calls.labels_eq
  obtain ⟨yesBlock,first,_,_,firstSuccessor,firstTag⟩ :=
    original_selected_successor run scope original tag block (index := 0) (bc := yes) (by simp [term,dests])
  obtain ⟨noBlock,second,_,_,secondSuccessor,secondTag⟩ :=
    original_selected_successor run scope original tag block (index := 1) (bc := no) (by simp [term,dests])
  rw [labels] at firstSuccessor secondSuccessor
  simp only [List.getElem?_toArray,List.getElem?_cons_zero,List.getElem?_cons_succ,
    Option.some.injEq] at firstSuccessor secondSuccessor
  subst first second
  exact ⟨calls.yes,calls.no,yesBlock,noBlock,labels,firstTag,secondTag⟩

end Backend.Stock.Proof.ConditionalValues
