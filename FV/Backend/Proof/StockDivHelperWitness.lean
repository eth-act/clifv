import FV.Backend.Proof.StockDivHelpers
namespace Backend.Stock.Proof.ScalarDiv
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
private def framed : State := {sinkState with demand := #[2,1],sunk := #[true,false]}
/-- Every actual division helper path is inhabited with nonzero demand/sunk
fields; these witnesses are foundations, not complete original-source records. -/
theorem stock_div_helper_witness (signed : Bool) (w : Nat)
    (width : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) :
    (∃ trace,(applyTerm program (Stock.sem sinkCtx) {} 30 27 (if signed then 493 else 492)
      [.ty (.int w),.reg (.vreg 192 .int),.reg (.vreg 193 .int)]).run (framed,#[]) =
      .ok (some (.reg (framed.base.fresh .int).1),
        {framed with base := ((framed.base.fresh .int).2.emit
          (.aluRRR (if signed then .sDiv else .uDiv) (szOf w) (framed.base.fresh .int).1
            (.vreg 192 .int) (.vreg 193 .int)))},trace)) ∧
    (∃ trace,(applyTerm program (Stock.sem sinkCtx) {} 30 27 444
      [.ty (.int w),.reg (.vreg 192 .int),.reg (.vreg 193 .int),.reg (.vreg 194 .int)]).run (framed,#[]) =
      .ok (some (.reg (framed.base.fresh .int).1),
        {framed with base := ((framed.base.fresh .int).2.emit
          (.aluRRRR .mSub (szOf w) (framed.base.fresh .int).1 (.vreg 192 .int) (.vreg 193 .int) (.vreg 194 .int)))},trace)) ∧
    (applyTerm program (Stock.sem sinkCtx) {} 40 27 559
      [.reg (.vreg 193 .int),.data 93 (sizeIndex (szOf w)) []]).run (framed,#[]) =
      .ok (some (.reg (.vreg 193 .int)),
        {framed with base := framed.base.emit (.trapIf (.zero (.vreg 193 .int) (szOf w)) .intDivz)},
        #[rule_inst_3838.id]) ∧
    (∃ trace,(applyTerm program (Stock.sem sinkCtx) {} 60 27 561
      [.ty (.int w),.reg (.vreg 192 .int),.reg (.vreg 194 .int),.reg (.vreg 193 .int)]).run (framed,#[]) =
      .ok (some (.reg (.vreg 194 .int)),
        {framed with base := overflowBase framed.base w (.vreg 192 .int) (.vreg 193 .int)},trace)) := by
  have small : w ≤ 64 := by omega
  exact ⟨stock_div_quotient_helper data_program sinkCtx rfl small signed framed #[] 0 _ _,
    stock_div_msub_helper data_program sinkCtx rfl small framed #[] 0 _ _ _,
    stock_div_zero_guard_helper data_program sinkCtx rfl (szOf w) framed #[] 0 _,
    stock_div_overflow_guard_helper data_program sinkCtx rfl width framed #[] 0 _ _ _⟩
/-- Actual minimum-check helper runs preserve nonzero scheduling fields for
both narrow allocation and wide pass-through paths. -/
theorem stock_div_intmin_helper_witness (w : Nat)
    (width : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) :
    ∃ trace,(applyTerm program (Stock.sem sinkCtx) {} 60 27 562
      [.ty (.int w),.reg (.vreg 192 .int)]).run (framed,#[]) =
      .ok (some (.reg (if w ≤ 16 then (framed.base.fresh .int).1 else .vreg 192 .int)),
        (if w ≤ 16 then {framed with base := ((framed.base.fresh .int).2.emit
          (.aluRRImmShift .lsl .size32 (framed.base.fresh .int).1 (.vreg 192 .int) (32-w)))} else framed),trace) :=
  stock_div_intmin_helper data_program sinkCtx rfl width framed #[] 0 _
end Backend.Stock.Proof.ScalarDiv
