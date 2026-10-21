import FV.Backend.Proof.StockSelectConditions
import FV.Backend.Proof.StockSelectValues
namespace Backend.Stock.Proof.ScalarSelect.Witness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
private def function : Clif.Function := {
  name := "stock_select_original_parameters"
  sig := {params := [⟨.i64,.none,.normal⟩,⟨.i64,.none,.normal⟩],returns := [⟨.i64,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(7,.i64),(31,.i64)],body := [],term := .ret [7]}] }
private def built : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx function).toOption.getD (sinkCtx,#[],sinkState)
private def producer : V := .data 58 2 [.data 59 10 [],.data 93 1 [],.reg .xzr,.reg (.vreg 192 .int),.reg (.vreg 193 .int)]
private theorem safeX : DemandAllowed built.1 built.2.2 7 := by
  intro i h
  change none = some i at h
  cases h
private theorem safeY : DemandAllowed built.1 (built.2.2.mark 7) 31 := by
  intro i h
  change none = some i at h
  cases h
/-- Ordinary accepted sparse-ID input inhabits actual csel construction and
both explicit-flags select consumers. These are helper witnesses; they do not
claim a retained select record or whole-driver source transfer. -/
theorem stock_select_flags_helper_witness (w : Nat) (width : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) (condition : Cond) :
    (∃ out next trace, ApplyInternal program (Stock.sem built.1) {} 999 49 425
      [.data 96 condition.idx [],.reg (.vreg 192 .int),.reg (.vreg 193 .int)] (built.2.2,#[]) out (next,trace)) ∧
    (∃ out next trace, ApplyInternal program (Stock.sem built.1) {} 999 22 660
      [.ty (.int w),.data 47 1 [producer],.data 96 condition.idx [],.value 7,.value 31]
      (built.2.2,#[]) out (next,trace)) ∧
    (∃ out next trace, ApplyInternal program (Stock.sem built.1) {} 999 22 659
      [.ty (.int w),.data 123 2 [.data 47 1 [producer],.data 96 condition.idx []],.value 7,.value 31]
      (built.2.2,#[]) out (next,trace)) := by
  have decoded : MInst.ofV producer = some (.aluRRR .subS .size64 .xzr (.vreg 192 .int) (.vreg 193 .int)) := rfl
  have constructor := stock_csel_builder data_program built.1 (cfg := {}) rfl built.2.2 #[] 960
    (.data 96 condition.idx []) (.reg (.vreg 192 .int)) (.reg (.vreg 193 .int))
  have consumer := stock_select_cond_run data_program built.1 (cfg := {}) rfl width built.2.2 #[] 840 condition
    decoded (by rfl) (by rfl) safeX safeY
  have select := stock_select_flags_run data_program built.1 (cfg := {}) rfl width built.2.2 #[] 780 condition
    decoded (by rfl) (by rfl) safeX safeY
  exact ⟨⟨_,_,_,constructor⟩,⟨_,_,_,consumer⟩,⟨_,_,_,select⟩⟩
/-- Both Zero/NotZero constructors and both operand sizes inhabit the real659
helper using an accepted original context, without excluding any scheduling field. -/
theorem stock_select_zero_helper_witness (w : Nat) (width : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64)
    (nonzero : Bool) (size : OperandSize) :
    ∃ out next trace, ApplyInternal program (Stock.sem built.1) {} 999 22 659
      [.ty (.int w),.data 123 (if nonzero then 1 else 0)
        [.reg (.vreg 192 .int),.data 93 (if size = .size32 then 0 else 1) []],.value 7,.value 31]
      (built.2.2,#[]) out (next,trace) := by
  exact ⟨_,_,_,stock_select_zero_run data_program built.1 (cfg := {}) rfl width built.2.2 #[] 780
    nonzero size 192 (by rfl) (by rfl) safeX safeY⟩
private def aliases : Array (Option Nat) := #[some 1,none,some 3,none]
private def registers (k : Nat) : CV := BitVec.ofNat 128 (2^100 + if k = 1 then 7 else 9)
/-- Both distinct selected values inhabit final-alias csel semantics, with
dirty upper bits and preservation of every register except the fresh result. -/
theorem stock_select_resolved_value_witness (chooseX : Bool) (world : Arm.ArmState) :
    Runs (fun _ => True) ispec
      ([MInst.aluRRR .subS .size64 .xzr (.vreg 0 .int) (.vreg 0 .int),
        .csel (.vreg 4 .int) (.vreg 0 .int) (.vreg 2 .int) (if chooseX then .eq else .ne)].map
          (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) registers world
      (fun ρ' _ => VHolds ⟨.i64,if chooseX then 7 else 9⟩ (ρ' 4) ∧ ∀ k,k ≠ 4 → ρ' k = registers k) := by
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
  have flags : SetsFlags
      ((MInst.aluRRR .subS .size64 .xzr (.vreg 0 .int) (.vreg 0 .int)).mapRegs
        (Backend.lowerFunction.resolve aliases (aliases.size+1))) registers
      (cmpFlags (opnd .size64 (registers 1)) (opnd .size64 (registers 1))) := by
    change SetsFlags (.aluRRR .subS .size64 .xzr (.vreg 1 .int) (.vreg 1 .int)) registers _
    exact setsFlags_cmpRR .size64 1 1 registers
  exact stock_select_flags_resolved self (by decide) (by decide) flags
    (by cases chooseX <;> decide +kernel) (by unfold VHolds; decide +kernel) (by unfold VHolds; decide +kernel) world
end Backend.Stock.Proof.ScalarSelect.Witness
