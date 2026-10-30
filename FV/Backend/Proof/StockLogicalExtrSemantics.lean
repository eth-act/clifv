import FV.Backend.Proof.StockAliasSemantics
import FV.Backend.Proof.IselFamALUAExtr

namespace Backend.Stock.Proof.LogicalExtr
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

private theorem fresh_reg {aliases : Array (Option Nat)} {d : Nat} (bounded : aliases.size ≤ d) :
    Backend.lowerFunction.resolve aliases (aliases.size+1) (.vreg d .int) = .vreg d .int := by
  rw [resolve_vreg]
  have fresh : aliasNum aliases d = d := by
    apply chaseF_none
    rw [Array.getElem?_eq_none bounded]
    rfl
  change Reg.vreg (aliasNum aliases d) .int = _
  rw [fresh]

/-- A two-input EXTR uses original values through final aliases and writes
only its fresh destination. The concatenated inputs need not be equal. -/
theorem extr_resolved {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) {ty : Clif.Ty} (width : ty.width = 32 ∨ ty.width = 64)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} {d x y X : Nat} {sh : ShiftOpAndAmt}
    (bounded : aliases.size ≤ d) (sum : X + sh.amt = ty.width) (count : sh.amt < ty.width)
    {u v : BitVec ty.width} (heldX : VHolds ⟨ty,u⟩ (ρ (aliasNum aliases x)))
    (heldY : VHolds ⟨ty,v⟩ (ρ (aliasNum aliases y))) :
    ∃ ρ', PRun F isem
      [(MInst.aluRRRShift .extr (szOf ty.width) (.vreg d .int) (.vreg x .int)
        (.vreg y .int) sh).mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1))] ρ ρ' ∧
      VHolds ⟨ty,(u <<< X) ||| (v >>> sh.amt)⟩ (ρ' d) ∧ ∀ n,n ≠ d → ρ' n = ρ n := by
  have bits : (szOf ty.width).bits = ty.width := by
    rcases width with h | h <;> simp [szOf,h,OperandSize.bits]
  have fits : sh.amt < (szOf ty.width).bits := by rwa [bits]
  let r := resX (szOf ty.width)
    (((opnd (szOf ty.width) (ρ (aliasNum aliases x)) ++
       opnd (szOf ty.width) (ρ (aliasNum aliases y))) >>> sh.amt).setWidth (szOf ty.width).bits)
  refine ⟨upd ρ d r,?_,?_,?_⟩
  · simp only [MInst.mapRegs]
    rw [fresh_reg bounded,resolve_vreg,resolve_vreg]
    exact prun_rrr refines (operands_aluRRRShift _ _ _ _ _ _)
      (fun _ => ispec_extr fits) (prun_nil _)
  · rw [upd_same]
    exact extr_holds width heldX heldY sum
  · intro n different
    simp only [upd,different,ite_false]

/-- Both source widths have actual executable instances for arbitrary, distinct
machine words and caller state, with the destination separate from the inputs. -/
theorem extr_resolved_witness (ty : Clif.Ty) (supported : ty = .i32 ∨ ty = .i64) (a b : CV) :
    let ρ : Nat → CV := fun n => if n = 0 then a else if n = 1 then b else 0
    ∃ ρ', PRun (fun _ => True) ispec
      [(MInst.aluRRRShift .extr (szOf ty.width) (.vreg 2 .int) (.vreg 0 .int)
        (.vreg 1 .int) ⟨.lsr,1⟩).mapRegs (Backend.lowerFunction.resolve #[] 1)] ρ ρ' ∧
      VHolds ⟨ty,(a.setWidth ty.width <<< (ty.width-1)) ||| (b.setWidth ty.width >>> 1)⟩ (ρ' 2) ∧
      ∀ n,n ≠ 2 → ρ' n = ρ n := by
  dsimp only
  have width : ty.width = 32 ∨ ty.width = 64 := by rcases supported with rfl | rfl <;> simp [Clif.Ty.width]
  have sum : ty.width-1+1 = ty.width := by rcases supported with rfl | rfl <;> decide
  have count : 1 < ty.width := by rcases supported with rfl | rfl <;> decide
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
  exact extr_resolved self width (aliases := #[]) (d := 2) (x := 0) (y := 1)
    (X := ty.width-1) (sh := ⟨.lsr,1⟩) (by decide) sum count (by rfl) (by rfl)

end Backend.Stock.Proof.LogicalExtr
