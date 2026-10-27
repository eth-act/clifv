import FV.Backend.Proof.StockConditionalSuccessorWitness
import FV.Backend.Proof.StockSelectedRouteExecution

namespace Backend.Stock.Proof.ConditionalValues.RouteWitness
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

private abbrev function := ConditionalCalls.sourceFunction
private def initial : Clif.Frame := {
  func := function,regs := Clif.Regs.empty.set 7 ⟨.i64,1⟩,slots := [],
  body := [],term := .brif 7 ⟨1,[7]⟩ ⟨2,[7]⟩ }
private def after : Clif.Frame := {
  initial with regs := initial.regs.set 31 ⟨.i64,1⟩,term := .ret [31] }

/-- The complete conditional source and actual assembled VCode execute the
chosen branch and nonempty copies into the real guarded successor scan. -/
theorem selected_route_execution_witness (X : ExtSem) :
    ∃ result, ∃ (spec : ConditionalBodySpec function result function.blocks[0]! 0 0 7
      ⟨1,[7]⟩ ⟨2,[7]⟩ (csem (fun _ => False) ⟨0,0⟩ X)
      (fun _ _ _ => True) Clif.Env.empty {funcs := []}),
      ∃ next targetLabel ρ' endWorld,
      Stock.lower function = .ok result ∧ LowerScope function ∧ Dominated function ∧
      Clif.enterFunc function [⟨.i64,1⟩] Clif.Mem.empty = .ok (initial,Clif.Mem.empty) ∧
      Clif.runLoop Clif.Env.empty {funcs := []} 2 ⟨initial,[],Clif.Mem.empty⟩ =
        .returned [⟨.i64,1⟩] Clif.Mem.empty ∧
      Star (VStepAt result.code result.edgeArgs (csem (fun _ => False) ⟨0,0⟩ X))
        (.run ⟨0,spec.preludeCode.size+spec.body.code.size,
          entrySeed spec.core.scan.ctx initial,Arm.ArmState.default⟩)
        (.run ⟨targetLabel,0,ρ',endWorld⟩) ∧
      next ∈ result.blockScans.toList ∧ next.block = 1 ∧
      result.order.nodes[targetLabel]? = some (.original 1) ∧
      SourceDefinedAt function result.ctx 1 0 after ∧
      GuardedScanRel function result next.ctx next.block (fun _ _ _ => True)
        next.output.state (0,after,Clif.Mem.empty) ρ' endWorld := by
  obtain ⟨result,spec,next,targetLabel,ρ',index,inst,ops,regs,prefixWorld,endWorld,
    run,scope,dominated,entered,returned,crossed,machine,last,event,atBlock,targetTag,route,defined,guarded⟩ :=
    SuccessorWitness.selected_successor_witness X
  let resolve := Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)
  let vb : VBlock := {spec.raw with
    insts := spec.raw.insts.map (·.mapRegs resolve)
    params := spec.raw.params.map resolve
    branchArgs := spec.raw.branchArgs.map resolve}
  have raw : spec.raw.insts = (spec.preludeCode ++ spec.body.code) ++ spec.origin.emission.code := by
    rw [spec.rawCode,spec.bodyCode,Array.append_assoc]
  have segment : SegAt vb (spec.preludeCode.size+spec.body.code.size)
      (spec.origin.emission.code.toList.map (·.mapRegs resolve)) := by
    intro k hk
    have bound : k < spec.origin.emission.code.size := by simpa using hk
    change (spec.raw.insts.map (·.mapRegs resolve))[spec.preludeCode.size+spec.body.code.size+k]? = _
    rw [raw,Array.map_append]
    rw [Array.getElem?_append_right (by simp only [Array.size_map,Array.size_append]; omega)]
    simp only [Array.size_map,Array.size_append,Nat.add_sub_cancel_left]
    simp [bound]
  have endPosition : spec.preludeCode.size+spec.body.code.size+index+1 = vb.insts.size := by
    change _ = (spec.raw.insts.map (·.mapRegs resolve)).size
    rw [raw]
    simp only [Array.size_map,Array.size_append]
    omega
  have execution := route.execute run scope (driverSem_csem (fun _ => False) ⟨0,0⟩ X).toDriverSemG
    spec.placed segment machine endPosition
  exact ⟨result,spec,next,targetLabel,ρ',endWorld,run,scope,dominated,entered,returned,
    execution,event,atBlock,targetTag,defined,guarded⟩

end Backend.Stock.Proof.ConditionalValues.RouteWitness
