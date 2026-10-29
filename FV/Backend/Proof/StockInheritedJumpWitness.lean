module

public import FV.Backend.Proof.StockInheritedJump
public import FV.Backend.Proof.StockInheritedFixture
public import FV.Backend.Proof.StockScalarCheck
public import FV.Backend.Proof.StockEntrySeed
public import FV.Backend.Proof.LowerShapeOkFacts
public import FV.Backend.Proof.RefinesCSem
public import FV.E2E.RegLevelDriverSem
public import FV.Backend.Proof.StockJumpDemand
public import FV.Backend.Proof.StockPerEdgeValues
public import FV.Backend.Proof.StockSourceEdgeDFG

@[expose] public section

namespace Backend.Stock.Proof.InheritedWitness
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

/-- The actual source returns16 by adding inherited7 to copied9 in block one.
The first complete machine core preserves the inherited source value, which is
not a target parameter and is never supplied as a machine-value certificate. -/
theorem executable_inherited_jump_witness (X : ExtSem) :
    ∃ result, ∃ (spec : Control.JumpBodySpec function result function.blocks[0]! 0 0 ⟨10,[1]⟩
      (csem (fun _ => False) ⟨0,0⟩ X) (fun _ _ _ => True) Clif.Env.empty {funcs := []}),
      ∃ t left ρ w key,
      Stock.lower function = .ok result ∧ LowerScope function ∧ Dominated function ∧
      Clif.enterFunc function [⟨.i64,7⟩] Clif.Mem.empty = .ok (initial,Clif.Mem.empty) ∧
      left+2 = 5 ∧ Clif.runLoop Clif.Env.empty {funcs := []} left t = .returned [⟨.i64,16⟩] Clif.Mem.empty ∧
      t.frame.body = [] ∧ t.frame.term = .jump ⟨10,[1]⟩ ∧
      seqRun (csem (fun _ => False) ⟨0,0⟩ X)
        (spec.core.code.toList.map (·.mapRegs
          (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))))
        (entrySeed spec.core.scan.ctx initial) Arm.ArmState.default =
          some (.stop spec.body.code.size (.jump spec.target) #[] ρ w [] w (.goto 0)) ∧
      (0 : Nat) ∉ function.blocks[1]!.params.map (·.1) ∧
      t.frame.regs 0 = some ⟨.i64,7⟩ ∧ spec.core.scan.ctx.valueReg? 0 = some (.vreg key .int) ∧
      VHolds ⟨.i64,7⟩ (ρ (aliasNum result.final.alias key)) ∧
      Inherited.CarryRel function result spec.core.scan.ctx spec.core.scan.block (fun _ _ _ => True)
        (fun x => x = 0) spec.term.output.state (2,t.frame,t.mem) ρ w := by
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
  obtain ⟨t,left,ρ,w,total,continued,empty,frame,sourceFrame,jump,executed,post⟩ :=
    Inherited.constant_jump_carry_returns run scope dominated
      (refines_csem (fun _ => False) ⟨0,0⟩ X) (driverSem_csem (fun _ => False) ⟨0,0⟩ X) stable
      spec rfl bodyFamily available rfl rfl returned
      ⟨guarded,allValues.mono (fun _ _ => True.intro)⟩
  have sourceValue : t.frame.regs 0 = some ⟨.i64,7⟩ := (sourceFrame 0 rfl).trans rfl
  obtain ⟨key,mapped,value⟩ := post.2 0 rfl _ sourceValue
  exact ⟨result,spec,t,left,ρ,w,key,run,scope,dominated,entered,total,continued,empty,jump,executed,
    by decide +kernel,sourceValue,mapped,value,post⟩

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

/-- Complete first-edge transfer on the real inherited-value function. Source
binding and the actual per-edge copies establish the next actual scan's whole
guard, including inherited values, DFG consistency and the memory relation. -/
theorem executable_inherited_successor_guard_witness (X : ExtSem) :
    ∃ result, ∃ (spec : Control.JumpBodySpec function result function.blocks[0]! 0 0 ⟨10,[1]⟩
      (csem (fun _ => False) ⟨0,0⟩ X) (fun _ _ _ => True) Clif.Env.empty {funcs := []}),
      ∃ t left ρ w second fr' ρ',
      Stock.lower function = .ok result ∧ LowerScope function ∧ Dominated function ∧
      Clif.enterFunc function [⟨.i64,7⟩] Clif.Mem.empty = .ok (initial,Clif.Mem.empty) ∧
      left+2 = 5 ∧ Clif.runLoop Clif.Env.empty {funcs := []} left t = .returned [⟨.i64,16⟩] Clif.Mem.empty ∧
      seqRun (csem (fun _ => False) ⟨0,0⟩ X)
        (spec.core.code.toList.map (·.mapRegs
          (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))))
        (entrySeed spec.core.scan.ctx initial) Arm.ArmState.default =
          some (.stop spec.body.code.size (.jump spec.target) #[] ρ w [] w (.goto 0)) ∧
      second ∈ result.blockScans.toList ∧ second.block = 1 ∧
      Clif.enterBlock t.frame ⟨10,[1]⟩ = .ok fr' ∧
      edgeEnvAt result.code result.edgeArgs 0 spec.target 0 ρ = some ρ' ∧
      GuardedScanRel function result second.ctx second.block (fun _ _ _ => True)
        second.output.state (0,fr',t.mem) ρ' w := by
  obtain ⟨result,spec,t,left,ρ,w,key,run,scope,dominated,entered,total,continued,empty,jump,executed,
    notParameter,sourceValue,mapped,value,post⟩ := executable_inherited_jump_witness X
  have order : result.order = ⟨#[.original 0,.original 1],#[#[1],#[]]⟩ :=
    Except.ok.inj ((stock_lower_order run).symm.trans (by with_unfolding_all rfl))
  have targetValue : spec.target = 1 := by
    have labels := spec.targets
    rw [order] at labels
    exact (List.cons.inj labels).1.symm
  have targetTag : result.order.nodes[spec.target]? = some (.original 1) := by rw [order,targetValue]; rfl
  have targetAtOne : result.order.nodes[1]? = some (.original 1) := by rw [order]; rfl
  obtain ⟨ranges,params,input,data,core,raw,preludeCode,coreRun,assembled,build,sizes,prepared,
    events,atBlock,rawCode,placed⟩ := stock_lower_original_block_scan_assembly run targetAtOne
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
  have tag := stock_blockOrder_entry (stock_lower_order run) scope.nonempty
  obtain ⟨ρ',copied,values⟩ := stock_lower_direct_per_edge_values run scope dominated tag
    (b := function.blocks[0]!) rfl (bc := ⟨10,[1]⟩) rfl successor targetTag rfl post.1.1
    (targetBlock := function.blocks[1]!) rfl crossed
    (needed := fun x => x ∈ availOf function (availIn function result.ctx) 1 0) (fun _ h => h)
    (ρ := ρ) (by
      intro x needed
      rcases needed with argument | ⟨available,notParam⟩
      · exact arguments x argument
      · rcases target_entry_cases result.ctx available with zero | one | two
        · exact carried x zero
        · exact arguments x (by simp [one])
        · exact False.elim (notParam (by simp [two,function])))
  have beforeDFG : DFGCons spec.core.scan.ctx
      (restrict t.frame (availOf function (availIn function result.ctx) 0 function.blocks[0]!.body.length)) := by
    change DFGCons spec.core.scan.ctx (restrict t.frame (availOf function (availIn function result.ctx) 0 2))
    simpa only [spec.atBlock] using post.1.2.1
  have targetDFG := stock_lower_source_enterBlock_dfg run scope dominated spec.events events
    (bi := 0) (tl := 1) (b := function.blocks[0]!) (target := function.blocks[1]!)
    (bc := ⟨10,[1]⟩) rfl rfl (by decide +kernel) rfl post.1.1 beforeDFG crossed
  have nextGuard : GuardedScanRel function result core.scan.ctx core.scan.block (fun _ _ _ => True)
      core.scan.output.state (0,fr',t.mem) ρ' w := by
    obtain ⟨tb,vs,regs,found,read,types,set,frame⟩ := enterBlock_spec crossed
    refine ⟨?_,?_,True.intro,?_⟩
    · rw [frame]
      exact post.1.1
    · simpa only [atBlock] using targetDFG
    · intro x needed
      have held := values x (by simpa only [atBlock] using needed.2)
      intro v read
      obtain ⟨n,map,value⟩ := held v read
      refine ⟨n,?_,value⟩
      rw [(stock_lower_record_context run scope events).2.1 x]
      exact map
  exact ⟨result,spec,t,left,ρ,w,core.scan,fr',ρ',run,scope,dominated,entered,total,continued,
    executed,events,atBlock,crossed,copied,nextGuard⟩

end Backend.Stock.Proof.InheritedWitness
