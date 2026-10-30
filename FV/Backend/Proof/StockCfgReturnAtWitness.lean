import FV.Backend.Proof.StockComputedCfg
import FV.Backend.Proof.StockCfgReturnEdgeAt
import FV.Backend.Proof.StockInheritedJumpDefined
import FV.Backend.Proof.StockInheritedFixture
import FV.Backend.Proof.StockScalarCheck
import FV.Backend.Proof.StockEntrySeed
import FV.Backend.Proof.LowerShapeOkFacts
import FV.Backend.Proof.RefinesCSem
import FV.E2E.RegLevelDriverSem
import FV.Backend.Proof.StockJumpDemand
import FV.Backend.Proof.StockPerEdgeValues
import FV.Backend.Proof.StockSourceEdgeDFG

namespace Backend.Stock.Proof.CfgReturnAtWitness
open InheritedWitness
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

private def initial : Clif.Frame := {
  func := function
  regs := Clif.Regs.empty.set 0 ⟨.i64,7⟩
  slots := []
  body := function.blocks[0]!.body
  term := function.blocks[0]!.term }

private theorem globalFamily : ∀ b ∈ function.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst := by
  have all : function.blocks.all (fun b => b.body.all Stock.Scalar.maskMixedBodyEligible) = true := by
    decide +kernel
  intro b member stm present
  exact Stock.Scalar.maskMixedBodyEligible_sound
    (List.all_eq_true.mp (List.all_eq_true.mp all b member) stm present)

private theorem bodyFamily : ∀ stm ∈ function.blocks[0]!.body,
    (∃ ty imm,stm.inst = .iconst ty imm) ∨ stm.inst = .nop := by
  intro stm member
  change stm ∈ [⟨[1],.iconst .i64 9⟩,⟨[],.nop⟩] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact Or.inl ⟨.i64,9,rfl⟩
  · exact Or.inr rfl

private theorem target_entry_cases (ctx : Ctx) {x : Nat}
    (available : x ∈ availOf function (availIn function ctx) 1 0) : x = 0 ∨ x = 1 ∨ x = 2 := by
  have block : function.blocks[1]? = some function.blocks[1]! := rfl
  obtain ⟨present,noLater⟩ := (mem_av block).mp available
  rcases present with parameter | incoming | ⟨j,stm,earlier,found,defined⟩
  · change x ∈ [2] at parameter
    exact Or.inr (Or.inr (List.mem_singleton.mp parameter))
  · have defined := ((inFix_fixOk (f := function) (ctx := ctx) (gn := id)).cand 1 x incoming).2.2.2.1
    change x ∈ [0,1,2,3] at defined
    simp only [List.mem_cons,List.not_mem_nil,or_false] at defined
    rcases defined with zero | one | two | three
    · exact Or.inl zero
    · exact Or.inr (Or.inl one)
    · exact Or.inr (Or.inr two)
    · subst x
      exact False.elim (noLater ⟨0,⟨[3],.binary .iadd .i64 0 2⟩,Nat.zero_le _,rfl,by decide +kernel⟩)
  · omega

/-- Actual entered-source two-block composition: the emitted first body and
jump preserve inherited7, real per-edge copies bind9, and the actual nonentry
return core computes16 with its ABI return starting at instruction zero. -/
theorem executable_return_edge_witness (X : ExtSem) :
    ∃ result, ∃ (spec : Control.JumpBodySpec function result function.blocks[0]! 0 0 ⟨10,[1]⟩
      (csem (fun _ => False) ⟨0,0⟩ X) (fun _ _ _ => True) Clif.Env.empty {funcs := []}),
      ∃ (t : Clif.State), ∃ left ρ w ρ',
      Stock.lower function = .ok result ∧ LowerScope function ∧ Dominated function ∧
      Clif.enterFunc function [⟨.i64,7⟩] Clif.Mem.empty = .ok (initial,Clif.Mem.empty) ∧
      left+2 = 5 ∧
      seqRun (csem (fun _ => False) ⟨0,0⟩ X)
        (spec.core.code.toList.map (·.mapRegs
          (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))))
        (entrySeed spec.core.scan.ctx initial) Arm.ArmState.default =
          some (.stop spec.body.code.size (.jump spec.target) #[] ρ w [] w (.goto 0)) ∧
      edgeEnvAt result.code result.edgeArgs 0 spec.target 0 ρ = some ρ' ∧
      RunOkABIAt function result.code result.edgeArgs (csem (fun _ => False) ⟨0,0⟩ X) (fun _ _ _ => True)
        t.frame.slots ⟨0,spec.preludeCode.size,entrySeed spec.core.scan.ctx initial,Arm.ArmState.default⟩ (.returned [⟨.i64,16⟩] Clif.Mem.empty) := by
  obtain ⟨result,run,scope,dominated⟩ := actual_inherited_driver_witness
  have tag := stock_blockOrder_entry (stock_lower_order run) scope.nonempty
  have stable : MRStable (fun _ => False) (fun _ _ _ => True) := by intro _ _ _ _ _ _; trivial
  obtain ⟨spec⟩ := Control.stock_lower_jump_body_spec run scope dominated globalFamily tag
    (b := function.blocks[0]!) rfl (bc := ⟨10,[1]⟩) rfl
    (refines_csem (fun _ => False) ⟨0,0⟩ X) (driverSem_csem (fun _ => False) ⟨0,0⟩ X)
    stable Clif.Env.empty {funcs := []}
  have entered : Clif.enterFunc function [⟨.i64,7⟩] Clif.Mem.empty = .ok (initial,Clif.Mem.empty) := rfl
  have returned : Clif.runLoop Clif.Env.empty {funcs := []} 5 ⟨initial,[],Clif.Mem.empty⟩ =
      .returned [⟨.i64,16⟩] Clif.Mem.empty := rfl
  have block : function.blocks[0]? = some function.blocks[0]! := rfl
  have available : ∀ x,x = 0 → x ∈ availOf function (availIn function result.ctx) spec.core.scan.block 0 := by
    intro x equal
    subst x
    rw [spec.atBlock]
    apply (mem_av block).mpr
    refine ⟨Or.inl (by decide +kernel),?_⟩
    rintro ⟨j,stm,_,found,defined⟩
    exact param_not_result dominated.ssa (List.mem_of_getElem? block) (List.mem_of_getElem? block)
      (by decide +kernel) (List.mem_flatMap.mpr ⟨stm,List.mem_of_getElem? found,defined⟩)
  have guarded := stock_lower_entered_seed_guarded run scope dominated spec.events entered
    spec.core.scan.output.state (MR := fun _ _ _ => True) Arm.ArmState.default trivial
  have allValues := entrySeed_entered_resolved_values_frame run scope dominated spec.events
    (SourceEntry.of_enterFunc entered)
  obtain ⟨t,left,ρ,w,total,continued,empty,frame,sourceFrame,jump,executed,post,tDefined⟩ :=
    Inherited.constant_jump_carry_returns_defined run scope dominated
      (refines_csem (fun _ => False) ⟨0,0⟩ X) (driverSem_csem (fun _ => False) ⟨0,0⟩ X) stable
      spec rfl bodyFamily available rfl rfl returned
      ⟨guarded,allValues.mono (fun _ _ => True.intro)⟩
      (by simpa only [spec.atBlock] using source_defined_enterFunc dominated result.ctx entered)
  change left+2 = 5 at total
  have order : result.order = ⟨#[.original 0,.original 1],#[#[1],#[]]⟩ :=
    Except.ok.inj ((stock_lower_order run).symm.trans (by with_unfolding_all rfl))
  have targetValue : spec.target = 1 := by
    have labels := spec.targets
    rw [order] at labels
    exact (List.cons.inj labels).1.symm
  have targetTag : result.order.nodes[spec.target]? = some (.original 1) := by rw [order,targetValue]; rfl
  obtain ⟨returnSpec⟩ := CfgReturn.stock_lower_return_block_spec run scope dominated
    (by decide +kernel) globalFamily targetTag (b := function.blocks[1]!) rfl rfl
    (refines_csem (fun _ => False) ⟨0,0⟩ X) (driverSem_csem (fun _ => False) ⟨0,0⟩ X)
    stable Clif.Env.empty {funcs := []}
  have crossing : ∃ fr',Clif.enterBlock t.frame ⟨10,[1]⟩ = .ok fr' := by
    cases call : Clif.enterBlock t.frame ⟨10,[1]⟩ with
    | ok fr' => exact ⟨fr',rfl⟩
    | trap code =>
      have leftEq : left = 3 := by omega
      rw [leftEq,Clif.runLoop_succ] at continued
      simp only [Clif.step,empty,jump,Clif.stepTerm,call,Clif.StepResult.ofRes] at continued
      cases continued
    | stuck message =>
      have leftEq : left = 3 := by omega
      rw [leftEq,Clif.runLoop_succ] at continued
      simp only [Clif.step,empty,jump,Clif.stepTerm,call,Clif.StepResult.ofRes] at continued
      cases continued
  obtain ⟨fr',crossed⟩ := crossing
  have arguments := Control.stock_jump_body_argument_values run scope dominated spec rfl targetTag post.1
  have carried : ValuesHeld (fun x => x = 0) result.ctx t.frame
      (fun k => ρ (aliasNum result.final.alias k)) := by
    intro x member v read
    obtain ⟨n,map,held⟩ := post.2 x member v read
    refine ⟨n,?_,held⟩
    rw [← (stock_lower_record_context run scope spec.events).2.1 x]
    exact map
  have successor : result.order.successors[0]![0]? = some spec.target := by rw [order,targetValue]; rfl
  have nextReturned : Clif.runLoop Clif.Env.empty {funcs := []} 2 ⟨fr',[],t.mem⟩ =
      .returned [⟨.i64,16⟩] Clif.Mem.empty := by
    have leftEq : left = 3 := by omega
    rw [leftEq,Clif.runLoop_succ] at continued
    have callers : t.callers = [] := frame.1.trans rfl
    simpa only [Clif.step,empty,jump,Clif.stepTerm,crossed,Clif.StepResult.ofRes,callers] using continued
  obtain ⟨ρ',copied,finished⟩ := CfgReturnAt.direct_successor_returns_at run scope dominated
    (by decide +kernel) globalFamily
    spec.events tag (b := function.blocks[0]!) rfl (bc := ⟨10,[1]⟩) rfl successor targetTag rfl
    (targetBlock := function.blocks[1]!) rfl spec.atBlock
    (refines_csem (fun _ => False) ⟨0,0⟩ X) (driverSem_csem (fun _ => False) ⟨0,0⟩ X) stable
    rfl returnSpec post.1
    (by simpa only [spec.atBlock] using tDefined) crossed (by
      intro x needed
      rcases needed with argument | ⟨available,notParam⟩
      · exact arguments x argument
      · rcases target_entry_cases result.ctx available with zero | one | two
        · exact carried x zero
        · exact arguments x (by simp [one])
        · exact False.elim (notParam (by simp [two,function]))) nextReturned
  let resolve := Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)
  have segment : SegAt {spec.raw with
      insts := spec.raw.insts.map (·.mapRegs resolve)
      params := spec.raw.params.map resolve
      branchArgs := spec.raw.branchArgs.map resolve}
      spec.preludeCode.size (spec.core.code.toList.map (·.mapRegs resolve)) := by
    intro k hk
    have bound : k < spec.core.code.size := by simpa using hk
    simp only [spec.rawCode,Array.map_append]
    rw [Array.getElem?_append_right (by simpa only [Array.size_map] using Nat.le_add_right spec.preludeCode.size k)]
    simp only [Array.size_map,Nat.add_sub_cancel_left]
    simp [bound]
  have last : spec.preludeCode.size+spec.body.code.size+1 =
      (spec.raw.insts.map (·.mapRegs resolve)).size := by
    simp only [spec.rawCode,spec.bodyCode,Array.size_map,Array.size_append,Array.size_singleton]
    omega
  obtain ⟨ps,cfg⟩ := stock_lower_computed_cfg run scope
  have actualSuccessor : succOf result.code 0 0 = some spec.target := by
    simp only [succOf,cfg]
    rw [order,targetValue]
    rfl
  have path := seqRun_goto_starAt spec.placed segment executed last actualSuccessor
    (by simpa only [vdefUpd,writeV,List.foldl_nil,Array.toList_empty,List.filter_nil,List.zip_nil_left] using copied)
  have whole := RunOkABIAt.prefix path finished
  exact ⟨result,spec,t,left,ρ,w,ρ',run,scope,dominated,entered,total,executed,copied,whole⟩

end Backend.Stock.Proof.CfgReturnAtWitness
