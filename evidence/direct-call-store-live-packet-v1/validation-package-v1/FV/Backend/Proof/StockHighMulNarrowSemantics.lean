import FV.Backend.Proof.StockAliasSemantics
import FV.Backend.Proof.IselFamALUAMulN
namespace Backend.Stock.Proof.ScalarHighMul
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
def narrowCode (signed : Bool) (w d nx ny : Nat) : List MInst :=
  [.extend (.vreg d .int) (.vreg nx .int) signed w 64,
   .extend (.vreg (d+1) .int) (.vreg ny .int) signed w 64,
   .aluRRRR .mAdd .size64 (.vreg (d+2) .int) (.vreg d .int) (.vreg (d+1) .int) .xzr,
   .aluRRImmShift (if signed then .asr else .lsr) .size64 (.vreg (d+3) .int) (.vreg (d+2) .int) w]
private theorem fresh_reg {aliases : Array (Option Nat)} {d : Nat} (bounded : aliases.size ≤ d) :
    Backend.lowerFunction.resolve aliases (aliases.size+1) (.vreg d .int) = .vreg d .int := by
  rw [resolve_vreg]
  have fresh : aliasNum aliases d = d := by
    apply chaseF_none; rw [Array.getElem?_eq_none bounded]; rfl
  change Reg.vreg (aliasNum aliases d) .int = _
  rw [fresh]
private theorem mapped_code (signed : Bool) (w d nx ny : Nat) (aliases : Array (Option Nat))
    (bounded : aliases.size ≤ d) :
    (narrowCode signed w d nx ny).map (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1))) =
      narrowCode signed w d (aliasNum aliases nx) (aliasNum aliases ny) := by
  simp only [narrowCode,List.map_cons,List.map_nil,MInst.mapRegs]
  rw [fresh_reg bounded,fresh_reg (by omega : aliases.size ≤ d+1),
    fresh_reg (by omega : aliases.size ≤ d+2),fresh_reg (by omega : aliases.size ≤ d+3),
    resolve_vreg,resolve_vreg]
  rfl
/-- Narrow high multiplication runs its two extensions, multiply and shift.
The second source must survive the first temporary write; retained/source
contracts derive this condition from original availability and actual allocation. -/
theorem stock_highmul_narrow_resolved {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) (signed : Bool) {ty : Clif.Ty}
    (width : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} {d nx ny : Nat}
    (bounded : aliases.size ≤ d) (secondFree : aliasNum aliases ny ≠ d)
    {u v : BitVec ty.width}
    (heldX : VHolds ⟨ty,u⟩ (ρ (aliasNum aliases nx))) (heldY : VHolds ⟨ty,v⟩ (ρ (aliasNum aliases ny))) :
    ∃ ρ', PRun F isem ((narrowCode signed ty.width d nx ny).map
        (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.binary (if signed then .smulhi else .umulhi) u v⟩ (ρ' (d+3)) ∧
      ∀ n,n < d ∨ d+4 ≤ n → ρ' n = ρ n := by
  have small : ty.width ≤ 32 := by rcases width with h | h | h <;> omega
  let a := extW signed u
  let b := extW signed v
  let p : BitVec 64 := 0+a*b
  let r : BitVec 64 := if signed then p.sshiftRight ty.width else p >>> ty.width
  let ρ1 := upd ρ d (ofX a)
  let ρ2 := upd ρ1 (d+1) (ofX b)
  let ρ3 := upd ρ2 (d+2) (resX .size64 p)
  let ρ4 := upd ρ3 (d+3) (resX .size64 r)
  have first : ∀ world,ispec (.extend (.vreg d .int) (.vreg (aliasNum aliases nx) .int) signed ty.width 64)
      [ρ (aliasNum aliases nx)] world = some ([ofX a],world,.next) := by
    intro world
    rw [ispec_extend64 width,extW_holds (by omega) heldX]
  have second : ∀ world,ispec (.extend (.vreg (d+1) .int) (.vreg (aliasNum aliases ny) .int) signed ty.width 64)
      [ρ1 (aliasNum aliases ny)] world = some ([ofX b],world,.next) := by
    intro world
    have kept : ρ1 (aliasNum aliases ny) = ρ (aliasNum aliases ny) := by simp only [ρ1,upd,secondFree,ite_false]
    rw [kept,ispec_extend64 width,extW_holds (by omega) heldY]
  have product : ∀ world,ispec (.aluRRRR .mAdd .size64 (.vreg (d+2) .int) (.vreg d .int) (.vreg (d+1) .int) .xzr)
      [ρ2 d,ρ2 (d+1)] world = some ([resX .size64 p],world,.next) := by
    intro world
    have x : ρ2 d = ofX a := by simp [ρ2,ρ1,upd]
    have y : ρ2 (d+1) = ofX b := by simp [ρ2,upd]
    rw [x,y]
    apply ispec_aluRRRR_xzr
    simp [mulAddVal,opnd64_lo,lo64_ofX,p]
    rfl
  have shifted : ∀ world,ispec (.aluRRImmShift (if signed then .asr else .lsr) .size64
      (.vreg (d+3) .int) (.vreg (d+2) .int) ty.width) [ρ3 (d+2)] world = some ([resX .size64 r],world,.next) := by
    intro world
    have productValue : ρ3 (d+2) = resX .size64 p := by simp only [ρ3,upd_same]
    rw [productValue]
    apply ispec_aluRRImmShift (sz := .size64) (by change ty.width < 64; omega)
    have opndValue : opnd .size64 (resX .size64 p) = p := opnd_resX64 p
    rw [opndValue]
    cases signed <;> rfl
  refine ⟨ρ4,?_,?_,?_⟩
  · rw [mapped_code signed ty.width d nx ny aliases bounded]
    exact prun_rr refines rfl first (prun_rr refines rfl second
      (prun_rrr refines rfl product (prun_rr refines rfl shifted (prun_nil _))))
  · simp only [ρ4,upd_same]
    change (resX .size64 r).setWidth ty.width = _
    rw [resX64_setWidth_le (by omega)]
    cases signed
    · exact mulhi_narrow_u small u v
    · exact mulhi_narrow_s small u v
  · intro n outside
    simp only [ρ4,ρ3,ρ2,ρ1,upd,show n ≠ d+3 by omega,show n ≠ d+2 by omega,
      show n ≠ d+1 by omega,show n ≠ d by omega,ite_false]
end Backend.Stock.Proof.ScalarHighMul
