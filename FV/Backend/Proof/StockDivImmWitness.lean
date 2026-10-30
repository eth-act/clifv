import FV.Backend.Proof.IselCtlTry
import FV.Backend.Proof.StockDivImmFrame
namespace Backend.Stock.Proof.ScalarDiv
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private theorem legacy_imm_nine {p : Program} (hp : Data p) (ctx : Ctx) (st : LState) :
    ∃ st' tr',
      (applyTerm p (Backend.sem ctx) {} 2000 27 553 (immArgs 8 1 9)).run (st, #[]) =
        .ok (some (.reg (st.fresh .int).1), st', tr') := by
  have hm := match_3742 hp ctx (cfg := {}) st #[] 1987 (w := 8) (i := 9)
    (mw := ⟨9, 0⟩) (Or.inl rfl) rfl
  obtain ⟨tr', he⟩ := rhs_3742 hp ctx (cfg := {}) rfl st #[] 1969
    (w := 8) (i := 9) (mw := ⟨9, 0⟩) (by decide)
  cases hp
  refine ⟨(st.fresh .int).2.emit (.movWide .movZ (st.fresh .int).1 ⟨9, 0⟩ (szOf 8)),
    tr'.push rule_inst_3742.id, ?_⟩
  isel_eval [*, R.imm]

private def framed : State := {sinkState with demand := #[2,1],sunk := #[true,false]}
/-- Real immediate materialization inhabits full-frame projection with nonzero
scheduling fields. This witness uses actual forward execution, without invoking
legacy machine-value proofs. -/
theorem stock_div_imm_frame_witness :
    ∃ next trace,(applyTerm program (Stock.sem sinkCtx) {} 2000 27 553 (immArgs 8 1 9)).run (framed,#[]) =
      .ok (some (.reg (framed.base.fresh .int).1),next,trace) ∧ next = {framed with base := next.base} ∧
      (applyTerm program (Backend.sem sinkCtx) {} 2000 27 553 (immArgs 8 1 9)).run (framed.base,#[]) =
        .ok (some (.reg (framed.base.fresh .int).1),next.base,trace) := by
  obtain ⟨base,trace,legacy⟩ := legacy_imm_nine data_program sinkCtx framed.base
  have actual := stock_div_imm_pure_helper data_program sinkCtx rfl (by decide) legacy
  have observed := stock_div_imm_observed data_program sinkCtx rfl (n := 1999) actual
  exact ⟨_,trace,actual,observed.1,observed.2⟩
end Backend.Stock.Proof.ScalarDiv
