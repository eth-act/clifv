import FV.Backend.Proof.IselTermFactsBase
import FV.Backend.Proof.StockResolvedDefs
import FV.Backend.Proof.IselCmpExt

namespace Backend.Stock.Proof.Resolved
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false

/-- A real extension prefix reads source alias0→2, writes its own fresh1 and
preserves2 at its endpoint. Thus the removed companion's number can also be a
live source register; no source inequality premise is needed. -/
theorem fragment_endpoint_witness (ρ : Nat → CV) (world : Arm.ArmState) :
    ∃ (before next : LState) (code : List MInst) (final : Nat → CV) (endWorld : Arm.ArmState),
      Frag before next code ∧ (#[some 2] : Array (Option Nat)).size ≤ before.nextVreg ∧
      next.nextVreg = 2 ∧
      code.map (·.mapRegs (Backend.lowerFunction.resolve #[some 2] 2)) =
        [.extend (.vreg 1 .int) (.vreg 2 .int) false 8 32] ∧
      seqRun ispec (code.map (·.mapRegs (Backend.lowerFunction.resolve #[some 2] 2))) ρ world =
        some (.fall final endWorld) ∧
      (∀ inst ∈ code.map (·.mapRegs (Backend.lowerFunction.resolve #[some 2] 2)),
        ∀ key ∈ vdefs inst,before.nextVreg ≤ key ∧ key < next.nextVreg) ∧ final 2 = ρ 2 := by
  let before : LState := {nextVreg := 1,classes := #[.int]}
  let inst : MInst := .extend (.vreg 1 .int) (.vreg 0 .int) false 8 32
  let next := (before.fresh .int).2.emit inst
  have fragment : Frag before next [inst] := Frag.fresh_emit before (by
    change [1] ⊆ [1]
    exact List.Subset.refl _)
  have bounded : (#[some 2] : Array (Option Nat)).size ≤ before.nextVreg := by decide
  have mapped : [inst].map (·.mapRegs (Backend.lowerFunction.resolve #[some 2] 2)) =
      [.extend (.vreg 1 .int) (.vreg 2 .int) false 8 32] := rfl
  have spec := ispec_extend (d := 1) (rn := .vreg 2 .int) (sg := false) (a := 8) (b := 32)
    (x := ρ 2) (w := world) (by decide) (by decide) (by decide)
  obtain ⟨endWorld,run,_⟩ := seqRun_one_next refines_ispec
    (operands_extend' 1 2 false 8 32) (ρ := ρ) spec (by simp [Operand.isDef])
  have actual := run
  rw [← mapped] at actual
  refine ⟨before,next,[inst],_,endWorld,fragment,bounded,rfl,mapped,actual,
    fragment_defs fragment #[some 2] bounded,?_⟩
  exact fragment_frame fragment #[some 2] bounded actual 2 (Or.inr (by decide))

end Backend.Stock.Proof.Resolved
