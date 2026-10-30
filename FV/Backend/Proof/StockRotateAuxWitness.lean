import FV.Backend.Proof.StockRotateSemantics
import FV.Backend.Proof.StockRotateNarrowRhs
namespace Backend.Stock.Proof.ScalarRotate
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
private def directImmState : LState := {nextVreg := 2,classes := #[]}
private def directImmAfter (w : Nat) : LState := {nextVreg := 5,classes := #[],emitted :=
  [.aluRRImmShift .lsr .size32 (.vreg 2 .int) (.vreg 0 .int) 0,
   .aluRRImmShift .lsl .size32 (.vreg 3 .int) (.vreg 0 .int) w,
   .aluRRR .orr .size32 (.vreg 4 .int) (.vreg 3 .int) (.vreg 2 .int)].toArray}
/-- Both retained existential helper variants have concrete complete executions
at both narrow widths and zero count. The subtraction kernel also has an
inhabited zero masked-count premise. Whole-source fixtures cover the other
selected/helper variants with actual mapped contexts and original frames. -/
theorem stock_rotate_helper_variants_witness : ∀ w ∈ ([8,16] : List Nat),
    (∃ trace,(applyTerm program (Stock.sem sinkCtx) {} 60 27 710
      [.ty (.int w),.reg (.vreg 0 .int),.reg (.vreg 1 .int)]).run (sinkState,#[]) =
      .ok (some (.reg (.vreg (sinkState.base.nextVreg+5) .int)),
        {sinkState with base := rotateNarrowRegBase w sinkState.base (.vreg 0 .int) (.vreg 1 .int)},trace)) ∧
    (∃ trace,(applyTerm program (Stock.sem sinkCtx) {} 60 27 712
      [.ty (.int w),.reg (.vreg 0 .int),.op (.immShift 0)]).run (sinkState,#[]) =
      .ok (some (.reg (.vreg (sinkState.base.nextVreg+2) .int)),
        {sinkState with base := rotateNarrowImmBase w sinkState.base (.vreg 0 .int) 0},trace)) ∧
    (∃ b : BitVec 32,b.toNat < w ∧ (0-(b-BitVec.ofNat 32 w)).toNat = w-b.toNat) ∧
    ∃ st next,st.nextVreg = 2 ∧ next.nextVreg = 5 ∧
      NarrowRotateImmRun (fun _ => True) ispec w 0 0 st next (.reg (.vreg 4 .int)) := by
  intro w member
  have width : w = 8 ∨ w = 16 := by simpa only [List.mem_cons,List.not_mem_nil,or_false] using member
  have positive : 0 < w := by rcases width with h | h <;> omega
  refine ⟨stock_rotate_narrow_rr_helper data_program sinkCtx width sinkState #[] 0 (.vreg 0 .int) (.vreg 1 .int),
    stock_rotate_narrow_imm_helper data_program sinkCtx width positive sinkState #[] 0 (.vreg 0 .int),
    ⟨0,by simpa using positive,stock_small_rotate_neg width 0 (by simpa using positive)⟩,?_⟩
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ world' _ h => ⟨world',h,SameWorld.refl _ _⟩
  refine ⟨directImmState,directImmAfter w,rfl,rfl,?_⟩
  exact stock_small_rotate_imm_run self width positive (.inl (by decide))
    (by simp [directImmState,directImmAfter]) rfl
end Backend.Stock.Proof.ScalarRotate
