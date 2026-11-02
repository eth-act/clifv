import FV.Backend.Proof.StockOutgoingOrigin
import FV.Backend.Proof.StockSelectedArguments
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Stock.runTerm lowerBlockCore branchArgs emitBranch collectOutgoing scanBlock
private def Collected (ctx : Ctx) (order : Order) (bi : Nat) (item : Nat × Nat) (args : Array Reg) : Prop :=
  match order.nodes[item.1]! with
  | .edge .. => args = #[]
  | .original _ => ∃ before after,branchArgs ctx before bi item.2 = .ok (args,after)
private theorem outgoing_vector {ctx : Ctx} {order : Order} {bi : Nat}
    {before after : State × Array (Array Reg)} {item : Nat × Nat}
    (run : outgoingStep ctx order bi before item = .ok after) :
    ∃ args,after.2 = before.2.push args ∧ Collected ctx order bi item args := by
  unfold outgoingStep at run
  cases tag : order.nodes[item.1]! with
  | edge pred index target =>
    simp only [tag,pure,Except.pure,Except.ok.injEq] at run
    subst after
    exact ⟨#[],rfl,by simp [Collected,tag]⟩
  | original target =>
    simp only [tag] at run
    cases call : branchArgs ctx before.1 bi item.2 with
    | error e => simp only [call,bind,Except.bind] at run; cases run
    | ok pair =>
      obtain ⟨args,next⟩ := pair
      simp only [call,bind,Except.bind,pure,Except.pure,Except.ok.injEq] at run
      subst after
      exact ⟨args,rfl,by simp only [Collected,tag]; exact ⟨before.1,next,call⟩⟩
private theorem outgoing_fold {ctx : Ctx} {order : Order} {bi : Nat}
    {items : List (Nat × Nat)} {before after : State × Array (Array Reg)}
    (run : items.foldlM (outgoingStep ctx order bi) before = .ok after) :
    after.2.size = before.2.size + items.length ∧
    (∀ j,j < before.2.size → after.2[j]? = before.2[j]?) ∧
    (∀ j item,items[j]? = some item → ∃ args,
      after.2[before.2.size+j]? = some args ∧ Collected ctx order bi item args) := by
  induction items generalizing before with
  | nil =>
    simp only [List.foldlM_nil,pure,Except.pure,Except.ok.injEq] at run
    subst after
    exact ⟨by simp,fun _ _ => rfl,fun j item h => by simp at h⟩
  | cons item rest ih =>
    rw [List.foldlM_cons] at run
    cases step : outgoingStep ctx order bi before item with
    | error e => simp only [step,bind,Except.bind] at run; cases run
    | ok middle =>
      simp only [step,bind,Except.bind] at run
      obtain ⟨args,installed,meaning⟩ := outgoing_vector step
      obtain ⟨size,prelude,selected⟩ := ih run
      have middleSize : middle.2.size = before.2.size + 1 := by simp [installed]
      refine ⟨by simpa [middleSize,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using size,?_,?_⟩
      · intro j bound
        rw [prelude j (by omega),installed,Array.getElem?_push]
        simp [bound,show j ≠ before.2.size by omega]
      · intro j pair found
        cases j with
        | zero =>
          simp only [List.getElem?_cons_zero,Option.some.injEq] at found
          subst pair
          refine ⟨args,?_,meaning⟩
          rw [Nat.add_zero,prelude before.2.size (by omega),installed,Array.getElem?_push]
          simp
        | succ j =>
          simp only [List.getElem?_cons_succ] at found
          obtain ⟨vector,present,value⟩ := selected j pair found
          exact ⟨vector,by simpa [middleSize,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using present,value⟩
private theorem collected_at {ctx : Ctx} {order : Order} {bi index target : Nat}
    {targets : Array Nat} {before after : State} {outgoing : Array (Array Reg)}
    (run : collectOutgoing ctx order bi targets before = .ok (after,outgoing))
    (selected : targets[index]? = some target) :
    ∃ args,outgoing[index]? = some args ∧ Collected ctx order bi (target,index) args := by
  unfold collectOutgoing at run
  obtain ⟨_,_,present⟩ := outgoing_fold run
  have item : targets.zipIdx.toList[index]? = some (target,index) := by simpa using selected
  obtain ⟨args,found,meaning⟩ := present index (target,index) item
  exact ⟨args,by simpa using found,meaning⟩

private theorem core_outgoing {ctx : Ctx} {order : Order} {f : Clif.Function} {b : Clif.Block}
    {bi start stop : Nat} {data : Backend.V} {targets : Array Nat} {input : State} {core : LoweredBlockCore}
    (run : lowerBlockCore ctx order f b bi start stop data targets input = .ok core) :
    ∃ before after,collectOutgoing ctx order bi targets before = .ok (after,core.outgoing) := by
  unfold lowerBlockCore at run
  dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind,Except.bind,pure,Except.pure] at run
    | split at run
  all_goals cases run; exact ⟨_,_,by assumption⟩

def outgoingAt (result : Result) (label index : Nat) : Option (Array Reg) :=
  result.edgeArgs[label]?.bind (·[index]?)

/-- A direct original successor's actual per-successor metadata is precisely
the selected source argument vector after mapping and final resolution. -/
theorem stock_lower_selected_outgoing {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {label bi index targetLabel targetBi : Nat} {b : Clif.Block} {bc : Clif.BlockCall}
    (tag : result.order.nodes[label]? = some (.original bi)) (source : f.blocks[bi]? = some b)
    (selected : (dests b.term)[index]? = some bc)
    (successor : result.order.successors[label]![index]? = some targetLabel)
    (target : result.order.nodes[targetLabel]? = some (.original targetBi)) :
    outgoingAt result label index = some
      ((edgeArgumentNumbers result bc).map (fun n => Reg.vreg n .int)).toArray := by
  obtain ⟨ranges,input,data,core,coreRun,stored⟩ := stock_lower_original_outgoing run tag
  obtain ⟨before,after,collect⟩ := core_outgoing coreRun
  obtain ⟨args,present,meaning⟩ := collected_at collect successor
  have node : result.order.nodes[targetLabel]! = .original targetBi := by simp [getElem!_def,target]
  simp only [Collected,node] at meaning
  obtain ⟨initial,next,call⟩ := meaning
  have numbers := stock_branchArgs_selected_numbers run scope source selected call
  simp only [outgoingAt,stored,Option.bind_some,Array.getElem?_map,present,Option.map_some,numbers]

/-- Arguments for a synthetic target are owned by that node: the actual source
node's per-successor vector is empty, as the real collector specifies. -/
theorem stock_lower_deferred_outgoing {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {label bi index targetLabel pred k targetBi : Nat}
    (tag : result.order.nodes[label]? = some (.original bi))
    (successor : result.order.successors[label]![index]? = some targetLabel)
    (target : result.order.nodes[targetLabel]? = some (.edge pred k targetBi)) :
    outgoingAt result label index = some #[] := by
  obtain ⟨ranges,input,data,core,coreRun,stored⟩ := stock_lower_original_outgoing run tag
  obtain ⟨before,after,collect⟩ := core_outgoing coreRun
  obtain ⟨args,present,meaning⟩ := collected_at collect successor
  have node : result.order.nodes[targetLabel]! = .edge pred k targetBi := by simp [getElem!_def,target]
  simp only [Collected,node] at meaning
  subst args
  simp [outgoingAt,stored,present]

/-- The actual synthetic node carries its selected source vector in its sole
outgoing metadata slot, after the real final alias resolver. -/
theorem stock_lower_critical_argument_vector {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {label pred index targetBi : Nat} {b : Clif.Block} {bc : Clif.BlockCall}
    (tag : result.order.nodes[label]? = some (.edge pred index targetBi))
    (source : f.blocks[pred]? = some b) (selected : (dests b.term)[index]? = some bc) :
    outgoingAt result label 0 = some
      ((edgeArgumentNumbers result bc).map (fun n => Reg.vreg n .int)).toArray := by
  obtain ⟨input,next,args,call,stored⟩ := stock_lower_critical_outgoing run tag
  have numbers := stock_branchArgs_selected_numbers run scope source selected call
  simp [outgoingAt,stored,numbers,getElem!_def]
end Backend.Stock.Proof
