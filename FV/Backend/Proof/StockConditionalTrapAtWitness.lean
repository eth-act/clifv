import FV.Backend.Proof.MemRefines
import FV.Backend.Proof.StockConditionalLeaf
import FV.Backend.Proof.StockConditionalEntryPrelude
import FV.Backend.Proof.StockConditionalTrapAt
import FV.Backend.Proof.StockConditionalEmptyTrapFixture
import FV.Backend.Proof.StockCfgReturnTrapAt
import FV.Backend.Proof.StockScalarCheck
import FV.Backend.Proof.RefinesCSem
import FV.E2E.RegLevelDriverSem

namespace Backend.Stock.Proof.ConditionalValues.TrapAtWitness
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

private abbrev function := EmptyTrapFixture.function
private theorem family : ∀ b ∈ function.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst := by
  have checked : function.blocks.all (fun b => b.body.all Stock.Scalar.maskMixedBodyEligible) = true := by decide +kernel
  intro b member stm present
  exact Stock.Scalar.maskMixedBodyEligible_sound
    (List.all_eq_true.mp (List.all_eq_true.mp checked b member) stm present)

private theorem terminal_successor {result : Result}
    (run : Stock.lower function = .ok result) (scope : LowerScope function) (dominated : Dominated function)
    (X : ExtSem) {bc : Clif.BlockCall} {tl targetLabel : Nat} {b : Clif.Block} {xs : List Nat}
    (lookup : blockIdx? function bc.block = some tl) (found : function.block? bc.block = some b)
    (source : function.blocks[tl]? = some b)
    (tag : result.order.nodes[targetLabel]? = some (.original tl))
    (ret : b.term = .ret xs) (nonentry : tl ≠ 0) (forward : 0 < targetLabel) :
    Nonempty (SuccessorTrap function result 0 bc (csem (fun _ => False) ⟨0,0⟩ X)
      (fun _ _ _ => True) Clif.Env.empty {funcs := []} .intDivz) := by
  have abi : sigAbiOk function.sig = true := rfl
  have stable : MRStable (fun _ => False) (fun _ _ _ => True) := by intro _ _ _ _ _ _; trivial
  exact SuccessorTrap.of_return_block run scope dominated abi family
    (refines_csem (fun _ => False) ⟨0,0⟩ X) (driverSem_csem (fun _ => False) ⟨0,0⟩ X)
    stable lookup found source tag ret nonentry forward

/-- A complete original conditional source with scalar successor bodies
inhabits whole-core, actual selected copies and first-trap composition. -/
private theorem trapping_empty_parameter_packet (X : ExtSem) :
    ∃ result, ∃ (spec : ConditionalBodySpec function result function.blocks[0]! 0 0 7
      ⟨1,[]⟩ ⟨2,[]⟩ (csem (fun _ => False) ⟨0,0⟩ X)
      (fun _ _ _ => True) Clif.Env.empty {funcs := []}),
      Stock.lower function = .ok result ∧ LowerScope function ∧ Dominated function ∧
      Clif.enterFunc function [⟨.i64,0⟩] Clif.Mem.empty = .ok (EmptyTrapFixture.initial,Clif.Mem.empty) ∧
      Clif.runLoop Clif.Env.empty {funcs := []} 4 ⟨EmptyTrapFixture.initial,[],Clif.Mem.empty⟩ =
        .trapped .intDivz ∧
      (result.ctx.defInst? 7 = none ∧ result.ctx.valueType? 7 = some (.int 64)) ∧
      (∀ (ρ : Nat → CV) (world : Arm.ArmState),
        GuardedScanRel function result spec.core.scan.ctx spec.core.scan.block (fun _ _ _ => True)
          spec.core.scan.output.state (0,EmptyTrapFixture.initial,Clif.Mem.empty) ρ world →
        RunOkABIAt function result.code result.edgeArgs (csem (fun _ => False) ⟨0,0⟩ X)
          (fun _ _ _ => True) EmptyTrapFixture.initial.slots
          ⟨0,spec.preludeCode.size,ρ,world⟩ (.trapped .intDivz)) := by
  obtain ⟨result,run,scope,dominated,entered,returned⟩ := EmptyTrapFixture.driver_witness
  have tag := stock_blockOrder_entry (stock_lower_order run) scope.nonempty
  have stable : MRStable (fun _ => False) (fun _ _ _ => True) := by intro _ _ _ _ _ _; trivial
  obtain ⟨spec⟩ := stock_lower_conditional_body_spec run scope dominated family tag
    (b := function.blocks[0]!) rfl (c := 7) (yes := ⟨1,[]⟩) (no := ⟨2,[]⟩) rfl
    (refines_csem (fun _ => False) ⟨0,0⟩ X) (driverSem_csem (fun _ => False) ⟨0,0⟩ X)
    stable Clif.Env.empty {funcs := []}
  let built := (Stock.buildCtx function).toOption.getD (sinkCtx,#[],sinkState)
  have build : Stock.buildCtx function = .ok built := rfl
  have context : result.ctx = built.1 := congrArg Prod.fst (Except.ok.inj (spec.build.symm.trans build))
  have parameter : result.ctx.defInst? 7 = none := by rw [context]; rfl
  have conditionTy : result.ctx.valueType? 7 = some (.int 32) ∨ result.ctx.valueType? 7 = some (.int 64) := by
    right
    rw [context]
    rfl
  have ordered : blockOrder function = .ok ⟨#[.original 0,.original 2,.original 1],#[#[2,1],#[],#[]]⟩ := by cbv
  have orderEq := Except.ok.inj ((stock_lower_order run).symm.trans ordered)
  have successors : ∀ (index : Nat) (bc : Clif.BlockCall),(dests function.blocks[0]!.term)[index]? = some bc →
      Nonempty (SuccessorTrap function result 0 bc (csem (fun _ => False) ⟨0,0⟩ X)
        (fun _ _ _ => True) Clif.Env.empty {funcs := []} .intDivz) := by
    intro index bc selected
    cases index with
    | zero =>
      change some ⟨1,[]⟩ = some bc at selected
      cases Option.some.inj selected
      exact terminal_successor run scope dominated X (tl := 1) (targetLabel := 2)
        (b := function.blocks[1]!) rfl rfl rfl (by rw [orderEq]; rfl) rfl (by decide) (by decide)
    | succ index =>
      cases index with
      | zero =>
        change some ⟨2,[]⟩ = some bc at selected
        cases Option.some.inj selected
        exact terminal_successor run scope dominated X (tl := 2) (targetLabel := 1)
          (b := function.blocks[2]!) rfl rfl rfl (by rw [orderEq]; rfl) rfl (by decide) (by decide)
      | succ index => cases selected
  have typed : result.ctx.valueType? 7 = some (.int 64) := by rw [context]; rfl
  refine ⟨result,spec,run,scope,dominated,entered,returned,⟨parameter,typed⟩,?_⟩
  intro ρ world held
  have defined : SourceDefinedAt function result.ctx spec.core.scan.block 0 EmptyTrapFixture.initial := by
    rw [spec.atBlock]
    exact source_defined_enterFunc dominated result.ctx entered
  exact spec.trapping_empty_parameter_at run scope dominated family
    (refines_csem (fun _ => False) ⟨0,0⟩ X) (driverSem_csem (fun _ => False) ⟨0,0⟩ X)
    stable tag rfl parameter conditionTy ⟨rfl,rfl⟩ successors rfl rfl rfl defined returned held

/-- The complete source inhabits trap composition from its actual entry seed. -/
theorem trapping_empty_parameter_at_witness (X : ExtSem) :
    ∃ result, ∃ (spec : ConditionalBodySpec function result function.blocks[0]! 0 0 7
      ⟨1,[]⟩ ⟨2,[]⟩ (csem (fun _ => False) ⟨0,0⟩ X)
      (fun _ _ _ => True) Clif.Env.empty {funcs := []}),
      Stock.lower function = .ok result ∧ LowerScope function ∧ Dominated function ∧
      Clif.enterFunc function [⟨.i64,0⟩] Clif.Mem.empty = .ok (EmptyTrapFixture.initial,Clif.Mem.empty) ∧
      Clif.runLoop Clif.Env.empty {funcs := []} 4 ⟨EmptyTrapFixture.initial,[],Clif.Mem.empty⟩ =
        .trapped .intDivz ∧
      RunOkABIAt function result.code result.edgeArgs (csem (fun _ => False) ⟨0,0⟩ X)
        (fun _ _ _ => True) EmptyTrapFixture.initial.slots
        ⟨0,spec.preludeCode.size,entrySeed spec.core.scan.ctx EmptyTrapFixture.initial,Arm.ArmState.default⟩
        (.trapped .intDivz) := by
  obtain ⟨result,spec,run,scope,dominated,entered,returned,metadata,finish⟩ := trapping_empty_parameter_packet X
  have held := stock_lower_entered_seed_guarded run scope dominated spec.events entered
    spec.core.scan.output.state (MR := fun _ _ _ => True) Arm.ArmState.default trivial
  exact ⟨result,spec,run,scope,dominated,entered,returned,finish _ _ held⟩

/-- Instruction-zero ABI entry, the actual conditional core, selected copies
and a reachable scalar divide-by-zero execute for a complete original source. -/
theorem trapping_empty_parameter_entry_witness (X : ExtSem) :
    ∃ result ρ0,Stock.lower function = .ok result ∧ LowerScope function ∧ Dominated function ∧
      Clif.enterFunc function [⟨.i64,0⟩] Clif.Mem.empty = .ok (EmptyTrapFixture.initial,Clif.Mem.empty) ∧
      Clif.runLoop Clif.Env.empty {funcs := []} 4 ⟨EmptyTrapFixture.initial,[],Clif.Mem.empty⟩ =
        .trapped .intDivz ∧
      RunOkABIAt function result.code result.edgeArgs (csem (fun _ => False) ⟨0,0⟩ X)
        (fun _ _ _ => True) EmptyTrapFixture.initial.slots
        ⟨0,0,ρ0,Arm.write_base_gpr 0#5 0 Arm.ArmState.default⟩
        (.trapped .intDivz) := by
  obtain ⟨result,spec,run,scope,dominated,entered,returned,metadata,finish⟩ := trapping_empty_parameter_packet X
  let world := Arm.write_base_gpr 0#5 0 Arm.ArmState.default
  have arguments : ArgsAtEntry (fun _ => False) function.sig [⟨.i64,0⟩] world := by
    intro loc value member
    change (loc,value) ∈ [(.reg (.x 0),⟨.i64,0⟩)] at member
    cases List.mem_singleton.mp member
    simp only [VHolds,regVal,world,Arm.r,Arm.read_base_gpr,Arm.write_base_gpr,
      Arm.read_store,Arm.write_store,rnum]
    rfl
  have memorySem : MemRefines (fun _ => False) 0 (fun _ => none) (csem (fun _ => False) ⟨0,0⟩ X) :=
    memRefines_csem (fun _ => False) ⟨0,0⟩ X rfl (fun _ _ h => by cases h)
  have stable : MRStable (fun _ => False) (fun _ _ _ => True) := by intro _ _ _ _ _ _; trivial
  obtain ⟨ρ,w,path,guarded,values,sameWorld⟩ := conditional_entry_prelude run scope dominated spec
    rfl metadata.1 (Or.inr metadata.2) (SourceEntry.of_enterFunc entered)
    (driverSem_csem (fun _ => False) ⟨0,0⟩ X) memorySem stable trivial arguments
  exact ⟨result,entrySeed spec.core.scan.ctx EmptyTrapFixture.initial,run,scope,dominated,entered,returned,
    RunOkABIAt.prefix path (finish ρ w guarded)⟩

end Backend.Stock.Proof.ConditionalValues.TrapAtWitness
