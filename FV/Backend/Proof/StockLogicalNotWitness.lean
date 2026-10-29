module

public import FV.Backend.Proof.StockLogicalNotValues
public import FV.Backend.Proof.StockLogicalFixtures

@[expose] public section

namespace Backend.Stock.Proof.LogicalNot
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.LogicalSemantics
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
inductive Form where
  | registers | immediate | shift
private def fixture : Form → LogicalForm
  | .registers => .registers | .immediate => .immediateRight | .shift => .shiftRight
private def selected : Form → RuleId
  | .registers => rule_inst_3939.id | .immediate => rule_inst_3941.id | .shift => rule_inst_3944.id
inductive Op where
  | band | bor | bxor
private def Op.tag : Op → Nat
  | .band => 6 | .bor => 3 | .bxor => 8
private def Op.alu : Op → ALUOp
  | .band => .andNot | .bor => .orrNot | .bxor => .eorNot
private theorem Op.ofIdx (op : Op) : ALUOp.ofIdx? op.tag = some op.alu := by cases op <;> rfl
private theorem Op.notOp (op : Op) : NotOp op.alu := by cases op <;> simp [Op.alu,NotOp]

private theorem observed (form : Form) (op : Op) :
    ((applyTerm program (Stock.sem (formBuilt (fixture form)).1) {} 60 27 566
      [.data 59 op.tag [],.ty (.int 64),.value (formX (fixture form)),.value (formY (fixture form))]).run
        ((formBuilt (fixture form)).2.2,#[])).toOption.any (fun result => result.1.isSome &&
          decide (result.2.1.demand = formDemand (fixture form)) &&
          decide (result.2.2.back? = some (selected form))) = true := by
  cases form <;> cases op <;> decide +kernel

/-- All three actual NOT-helper selections are inhabited for AND/OR/XOR-NOT
in sparse mapped contexts. Fused constant/shift values remain unmaterialized in
machine registers, while demanded inputs establish the original helper value. -/
theorem stock_not_helper_values_witness (form : Form) (op : Op) :
    ∃ (out : V) (after : State) (trace : Array RuleId),
      MappedCtxInv (formFunction (fixture form)) (formBuilt (fixture form)).1 ∧
      DFGCons (formBuilt (fixture form)).1 (formFrame (fixture form)) ∧
      (applyTerm program (Stock.sem (formBuilt (fixture form)).1) {} 60 27 566
        [.data 59 op.tag [],.ty (.int 64),.value (formX (fixture form)),.value (formY (fixture form))]).run
          ((formBuilt (fixture form)).2.2,#[]) = .ok (some out,after,trace) ∧
      trace.back? = some (selected form) ∧
      NotValueOut (fun _ => True) ispec op.alu .i64 (BitVec.ofNat 64 (formValueX (fixture form)))
        (BitVec.ofNat 64 (formValueY (fixture form))) (formBuilt (fixture form)).2.2 after out #[] (formRegs (fixture form)) := by
  have actual := observed form op
  cases run : (applyTerm program (Stock.sem (formBuilt (fixture form)).1) {} 60 27 566
      [.data 59 op.tag [],.ty (.int 64),.value (formX (fixture form)),.value (formY (fixture form))]).run
        ((formBuilt (fixture form)).2.2,#[]) with
  | error err => simp [run,Except.toOption] at actual
  | ok result =>
    obtain ⟨value,after,trace⟩ := result
    cases value with
    | none => simp [run,Except.toOption] at actual
    | some out =>
      simp only [run,Except.toOption,Option.any_some,Option.isSome_some,Bool.true_and,Bool.and_eq_true,
        decide_eq_true_eq] at actual
      obtain ⟨demand,chosen⟩ := actual
      have sourceX : (formFrame (fixture form)).getAs (formX (fixture form)) .i64 =
          .ok (BitVec.ofNat 64 (formValueX (fixture form))) := by cases form <;> rfl
      have sourceY : (formFrame (fixture form)).getAs (formY (fixture form)) .i64 =
          .ok (BitVec.ofNat 64 (formValueY (fixture form))) := by cases form <;> rfl
      have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
      have value := stock_not_helper_values data_program (formInv (fixture form)) self (Op.ofIdx op) (Op.notOp op)
        (by decide) (formDFG (fixture form)) sourceX sourceY (aliases := #[]) (ρ := formRegs (fixture form))
        (by simp) (formExtent (fixture form)) (formHeld (fixture form) demand) (n := 0) run
      exact ⟨out,after,trace,formInv (fixture form),formDFG (fixture form),rfl,chosen,value⟩

end Backend.Stock.Proof.LogicalNot
