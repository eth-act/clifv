import FV.Backend.Proof.StockAliasSemantics
import FV.Backend.Proof.IselFamAluBShiftTerms
namespace Backend.Stock.Proof.ScalarShift
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
private theorem fresh_reg {aliases : Array (Option Nat)} {d : Nat} (bounded : aliases.size ≤ d) :
    Backend.lowerFunction.resolve aliases (aliases.size+1) (.vreg d .int) = .vreg d .int := by
  rw [resolve_vreg]
  have fresh : aliasNum aliases d = d := by
    apply chaseF_none; rw [Array.getElem?_eq_none bounded]; rfl
  change Reg.vreg (aliasNum aliases d) .int = _
  rw [fresh]

/-- A resolved immediate shift establishes the complete operand-size value and
preserves every register outside the fresh result. -/
theorem stock_shift_imm_resolved {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) {op : ALUOp} (operation : IsShift op) {w : Nat} (width : IW w)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} {a d amount : Nat}
    (bounded : aliases.size ≤ d) (fits : amount < (szOf w).bits) :
    ∃ ρ', PRun F isem
      [(MInst.aluRRImmShift op (szOf w) (.vreg d .int) (.vreg a .int) amount).mapRegs
        (Backend.lowerFunction.resolve aliases (aliases.size+1))] ρ ρ' ∧
      opnd (szOf w) (ρ' d) = shiftF op (opnd (szOf w) (ρ (aliasNum aliases a))) amount ∧
      ∀ n,n ≠ d → ρ' n = ρ n := by
  have code : (MInst.aluRRImmShift op (szOf w) (.vreg d .int) (.vreg a .int) amount).mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size+1)) =
      .aluRRImmShift op (szOf w) (.vreg d .int) (.vreg (aliasNum aliases a) .int) amount := by
    change MInst.aluRRImmShift op (szOf w)
      (Backend.lowerFunction.resolve aliases (aliases.size+1) (.vreg d .int))
      (Backend.lowerFunction.resolve aliases (aliases.size+1) (.vreg a .int)) amount = _
    rw [fresh_reg bounded,resolve_vreg]
    rfl
  let r := shiftF op (opnd (szOf w) (ρ (aliasNum aliases a))) amount
  refine ⟨upd ρ d (resX (szOf w) r),?_,?_,?_⟩
  · rw [code]
    exact prun_rr refines rfl (fun world => ispec_imm_shift_fb (w := world) operation fits) (prun_nil _)
  · rw [upd_same,opnd_resX]
  · intro n different; simp only [upd,different,ite_false]

/-- Resolved register shifts at32/64 bits implement the original count modulo
width, including amount values whose source type differs from the result type. -/
theorem stock_shift_rrr_resolved {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) {op : ALUOp} (operation : IsShift op) {w : Nat}
    (width : w = 32 ∨ w = 64) {aliases : Array (Option Nat)} {ρ : Nat → CV} {a y d : Nat}
    (bounded : aliases.size ≤ d) {amount : Clif.Val} (held : VHolds amount (ρ (aliasNum aliases y))) :
    ∃ ρ', PRun F isem
      [(MInst.aluRRR op (szOf w) (.vreg d .int) (.vreg a .int) (.vreg y .int)).mapRegs
        (Backend.lowerFunction.resolve aliases (aliases.size+1))] ρ ρ' ∧
      opnd (szOf w) (ρ' d) = shiftF op (opnd (szOf w) (ρ (aliasNum aliases a))) (amount.bits.toNat % w) ∧
      ∀ n,n ≠ d → ρ' n = ρ n := by
  have iw : IW w := by rcases width with rfl | rfl <;> simp [IW]
  have bits : (szOf w).bits = w := by rcases width with rfl | rfl <;> rfl
  have code : (MInst.aluRRR op (szOf w) (.vreg d .int) (.vreg a .int) (.vreg y .int)).mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size+1)) =
      .aluRRR op (szOf w) (.vreg d .int) (.vreg (aliasNum aliases a) .int) (.vreg (aliasNum aliases y) .int) := by
    change MInst.aluRRR op (szOf w)
      (Backend.lowerFunction.resolve aliases (aliases.size+1) (.vreg d .int))
      (Backend.lowerFunction.resolve aliases (aliases.size+1) (.vreg a .int))
      (Backend.lowerFunction.resolve aliases (aliases.size+1) (.vreg y .int)) = _
    rw [fresh_reg bounded,resolve_vreg,resolve_vreg]
    rfl
  let r := shiftF op (opnd (szOf w) (ρ (aliasNum aliases a)))
    ((opnd (szOf w) (ρ (aliasNum aliases y))).toNat % (szOf w).bits)
  refine ⟨upd ρ d (resX (szOf w) r),?_,?_,?_⟩
  · rw [code]
    exact prun_rrr refines (operands_aluRRR _ _ _ _ _) (fun world => ispec_rrr_shift_fb (w := world) operation) (prun_nil _)
  · rw [upd_same,opnd_resX]
    dsimp only [r]
    congr 1
    rw [amt_of_holds iw held,← opnd_mod iw (szOf w) (ρ (aliasNum aliases y))]
    exact congrArg (fun modulus => (opnd (szOf w) (ρ (aliasNum aliases y))).toNat % modulus) bits
  · intro n different; simp only [upd,different,ite_false]

/-- Narrow resolved shifts mask the amount in a fresh scratch register before
shifting. The value-register separation is a local obligation discharged by
original source availability when this fragment belongs to an actual record. -/
theorem stock_shift_mask_resolved {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) {op : ALUOp} (operation : IsShift op) {w : Nat}
    (width : w = 8 ∨ w = 16) {aliases : Array (Option Nat)} {ρ : Nat → CV} {a y d : Nat}
    (bounded : aliases.size ≤ d) (separate : aliasNum aliases a ≠ d)
    {amount : Clif.Val} (held : VHolds amount (ρ (aliasNum aliases y)))
    (immediate : ImmLogic.ofNat? (w-1) .size32 = some ⟨w-1,.size32⟩) :
    ∃ ρ', PRun F isem
      ([MInst.aluRRImmLogic .and .size32 (.vreg d .int) (.vreg y .int) ⟨w-1,.size32⟩,
        .aluRRR op .size32 (.vreg (d+1) .int) (.vreg a .int) (.vreg d .int)].map
          (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ ρ' ∧
      opnd .size32 (ρ' (d+1)) = shiftF op (opnd .size32 (ρ (aliasNum aliases a))) (amount.bits.toNat % w) ∧
      ∀ n,n ≠ d → n ≠ d+1 → ρ' n = ρ n := by
  have iw : IW w := by rcases width with rfl | rfl <;> simp [IW]
  have nextBound : aliases.size ≤ d+1 := by omega
  have firstCode : (MInst.aluRRImmLogic .and .size32 (.vreg d .int) (.vreg y .int) ⟨w-1,.size32⟩).mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size+1)) =
      .aluRRImmLogic .and .size32 (.vreg d .int) (.vreg (aliasNum aliases y) .int) ⟨w-1,.size32⟩ := by
    change MInst.aluRRImmLogic .and .size32
      (Backend.lowerFunction.resolve aliases (aliases.size+1) (.vreg d .int))
      (Backend.lowerFunction.resolve aliases (aliases.size+1) (.vreg y .int)) ⟨w-1,.size32⟩ = _
    rw [fresh_reg bounded,resolve_vreg]; rfl
  have secondCode : (MInst.aluRRR op .size32 (.vreg (d+1) .int) (.vreg a .int) (.vreg d .int)).mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size+1)) =
      .aluRRR op .size32 (.vreg (d+1) .int) (.vreg (aliasNum aliases a) .int) (.vreg d .int) := by
    change MInst.aluRRR op .size32
      (Backend.lowerFunction.resolve aliases (aliases.size+1) (.vreg (d+1) .int))
      (Backend.lowerFunction.resolve aliases (aliases.size+1) (.vreg a .int))
      (Backend.lowerFunction.resolve aliases (aliases.size+1) (.vreg d .int)) = _
    rw [fresh_reg nextBound,resolve_vreg,fresh_reg bounded]; rfl
  let mask := resX .size32 (opnd .size32 (ρ (aliasNum aliases y)) &&& BitVec.ofNat _ (w-1))
  let mid := upd ρ d mask
  let r := shiftF op (opnd .size32 (mid (aliasNum aliases a))) ((opnd .size32 (mid d)).toNat % OperandSize.size32.bits)
  refine ⟨upd mid (d+1) (resX .size32 r),?_,?_,?_⟩
  · simp only [List.map_cons,List.map_nil,firstCode,secondCode]
    exact prun_rr refines rfl (fun world => ispec_and_imm_fb (w := world) immediate)
      (prun_rrr refines (operands_aluRRR _ _ _ _ _) (fun world => ispec_rrr_shift_fb (w := world) operation) (prun_nil _))
  · rw [upd_same,opnd_resX]
    change shiftF op (opnd .size32 (mid (aliasNum aliases a))) ((opnd .size32 (mid d)).toNat % OperandSize.size32.bits) = _
    simp only [mid,upd,separate,ite_false,ite_true,mask,opnd_resX]
    congr 1
    have masked : (opnd .size32 (ρ (aliasNum aliases y)) &&& BitVec.ofNat _ (w-1)).toNat =
        (opnd .size32 (ρ (aliasNum aliases y))).toNat % w := by
      rw [BitVec.toNat_and,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show w-1 < 2^OperandSize.size32.bits by
        rcases width with rfl | rfl <;> decide)]
      exact land_mask_mod iw _
    rw [masked,Nat.mod_eq_of_lt (show (opnd .size32 (ρ (aliasNum aliases y))).toNat % w < OperandSize.size32.bits by
      have limit := Nat.mod_lt (opnd .size32 (ρ (aliasNum aliases y))).toNat iw.pos
      rcases width with rfl | rfl <;> simp [OperandSize.bits] <;> omega),opnd_mod iw,← amt_of_holds iw held]
  · intro n first second; simp only [upd,first,second,ite_false,mid]
end Backend.Stock.Proof.ScalarShift
