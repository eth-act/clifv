import FV.Backend.Lowering.Stock
import FV.Backend.Proof.RegallocLemmas
import FV.Arm.MinTheory
import FV.Backend.Proof.IselInterp
import FV.Backend.Proof.PrepareCheck

namespace Backend.Stock.Proof.LinearCfg
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
attribute [local irreducible] lowerNode lowerBlockCore assembleOriginalBlock

/-- The one actual reverse traversal supplies every compiler state used for
cross-block demand transfer; independently selected core witnesses are not
assumed to share an input state. -/
theorem actual_traversal {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) :
    ∃ (ranges : Array (Nat × Nat)) (params : List Nat) (starting finishing : DriverState),
      Stock.buildCtx f = .ok (result.ctx,ranges,result.initial) ∧
      blockOrder f = .ok result.order ∧
      starting.state = result.initial ∧ starting.blockScans = #[] ∧
      (Array.range result.order.nodes.size).reverse.toList.foldlM
        (fun d k => lowerNode result.ctx ranges result.order f params k d) starting = .ok finishing ∧
      finishing.blockScans = result.blockScans := by
  unfold Stock.lower at run
  try dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind,Except.bind,pure,Except.pure] at run
    | split at run
  cases run
  rename_i _ _ params _ _ _ _ _ source build _ order ordered _ driver folded
  exact ⟨_,params,_,driver,build,ordered,rfl,rfl,folded,rfl⟩

/-- Original-node assembly records the same core state and scan in the shared
traversal. No state supplied by another lowering invocation is substituted. -/
theorem original_node_scan {ctx : Ctx} {ranges : Array (Nat × Nat)} {order : Order}
    {f : Clif.Function} {params : List Nat} {label bi : Nat} {input output : DriverState}
    (run : lowerNode ctx ranges order f params label input = .ok output)
    (node : order.nodes[label]! = .original bi) :
    ∃ (data : Backend.V) (core : LoweredBlockCore),
      lowerBlockCore ctx order f f.blocks[bi]! bi ranges[bi]!.1 ranges[bi]!.2
        data order.successors[label]! input.state = .ok core ∧
      output.state = core.state ∧ output.blockScans = input.blockScans.push core.scan := by
  unfold lowerNode at run
  simp only [node] at run
  try dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind,Except.bind,pure,Except.pure] at run
    | split at run
  all_goals
    cases run
    exact ⟨_,_,by assumption,rfl,rfl⟩

private theorem fold_three {α : Type} (step : α → Nat → Except String α)
    {initial final : α} (run : ([2,1,0] : List Nat).foldlM step initial = .ok final) :
    ∃ target middle,step initial 2 = .ok target ∧ step target 1 = .ok middle ∧ step middle 0 = .ok final := by
  rw [List.foldlM_cons] at run
  obtain ⟨target,first,rest⟩ := Except.bind_ok run
  rw [List.foldlM_cons] at rest
  obtain ⟨middle,second,last⟩ := Except.bind_ok rest
  rw [List.foldlM_cons] at last
  obtain ⟨finished,third,empty⟩ := Except.bind_ok last
  simp only [List.foldlM_nil,pure,Except.pure,Except.ok.injEq] at empty
  subst finished
  exact ⟨target,middle,first,second,third⟩

/-- Consecutive source-chain cores are coupled by the real reverse traversal,
with the exact ordered scan list retained in the returned Stock result. -/
theorem three_original_scans {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result)
    (order : result.order = ⟨#[.original 0,.original 1,.original 2],#[#[1],#[2],#[]]⟩) :
    ∃ (ranges : Array (Nat × Nat)) (input : State) (target middle entry : LoweredBlockCore)
      (targetData middleData entryData : Backend.V),
      Stock.buildCtx f = .ok (result.ctx,ranges,result.initial) ∧
      lowerBlockCore result.ctx result.order f f.blocks[2]! 2 ranges[2]!.1 ranges[2]!.2
        targetData #[] input = .ok target ∧
      lowerBlockCore result.ctx result.order f f.blocks[1]! 1 ranges[1]!.1 ranges[1]!.2
        middleData #[2] target.state = .ok middle ∧
      lowerBlockCore result.ctx result.order f f.blocks[0]! 0 ranges[0]!.1 ranges[0]!.2
        entryData #[1] middle.state = .ok entry ∧
      result.blockScans = #[target.scan,middle.scan,entry.scan] := by
  obtain ⟨ranges,params,starting,finishing,build,ordered,initial,empty,folded,events⟩ := actual_traversal run
  have labels : (Array.range result.order.nodes.size).reverse.toList = [2,1,0] := by rw [order]; decide +kernel
  rw [labels] at folded
  obtain ⟨afterTarget,afterMiddle,lowerTarget,lowerMiddle,lowerEntry⟩ := fold_three _ folded
  obtain ⟨targetData,target,targetCore,targetState,targetScans⟩ := original_node_scan lowerTarget
    (by simp [order] : result.order.nodes[2]! = .original 2)
  obtain ⟨middleData,middle,middleCore,middleState,middleScans⟩ := original_node_scan lowerMiddle
    (by simp [order] : result.order.nodes[1]! = .original 1)
  obtain ⟨entryData,entry,entryCore,entryState,entryScans⟩ := original_node_scan lowerEntry
    (by simp [order] : result.order.nodes[0]! = .original 0)
  refine ⟨ranges,starting.state,target,middle,entry,targetData,middleData,entryData,build,?_,?_,?_,?_⟩
  · simpa [order] using targetCore
  · rw [targetState] at middleCore
    simpa [order] using middleCore
  · rw [middleState] at entryCore
    simpa [order] using entryCore
  · rw [← events,entryScans,middleScans,targetScans,empty]
    rfl

end Backend.Stock.Proof.LinearCfg
