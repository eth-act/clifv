import FV.E2E.DeadCleanupGuarded
import FV.E2E.DeadCleanupContracts
import FV.Backend.Proof.CSemRename

namespace E2E.StockAcquirePending
open Backend Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Existing read guards depend on register classes and operand values, not virtual names. -/
theorem guardR_mapRegs {g : Reg → Reg} {gn : Nat → Nat} (hg : VRenaming g gn)
    (F Rd : BitVec 64 → Prop) (sb : Nat) (i : MInst) (us : List CV) (w : Arm.ArmState) :
    GuardR F Rd sb (i.mapRegs g) us w = GuardR F Rd sb i us w := by
  cases i with
  | load op rd am flags =>
    simp only [MInst.mapRegs]
    rgc rd <;> simp only [GuardR,amodeAddr_mapRegs hg]
  | store op rd am flags =>
    simp only [MInst.mapRegs]
    rgc rd <;> us_cases <;> simp only [GuardR,amodeAddr_mapRegs hg]
  | loadAcquire ty dest pointer flags =>
    simp only [MInst.mapRegs]
    rgc dest <;> rgc pointer <;> us_cases <;> rfl
  | storeRelease ty dest pointer flags =>
    simp only [MInst.mapRegs]
    rgc dest <;> rgc pointer <;> us_cases <;> rfl
  | atomicRmwLoop ty op flags addr operand oldval scratch1 scratch2 => cases us <;> rfl
  | atomicCasLoop ty flags addr expected replace oldval scratch => cases us <;> rfl
  | _ => rfl

/-- Existing call guards retain the same target values under virtual renaming. -/
theorem guardC_mapRegs {g : Reg → Reg} {gn : Nat → Nat} (hg : VRenaming g gn)
    (F : BitVec 64 → Prop) (syms : String → Option Nat) (X : ExtSem)
    (exts : List Clif.ExtFunc) (sigs : List Clif.Signature) (sp : BitVec 64)
    (pin : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop)
    (i : MInst) (us : List CV) (w : Arm.ArmState) :
    GuardC F syms X exts sigs sp pin (i.mapRegs g) us w = GuardC F syms X exts sigs sp pin i us w := by
  cases i with
  | call info =>
    obtain ⟨dest,uses,defs⟩ := info
    cases dest <;> simp [MInst.mapRegs,GuardC,CallG]
  | tryCall info target =>
    obtain ⟨dest,uses,defs⟩ := info
    cases dest <;> simp [MInst.mapRegs,GuardC,CallG]
  | _ => rfl

/-- Guarded concrete semantics preserve the existing virtual renaming contract. -/
theorem csemG_mapRegs {g : Reg → Reg} {gn : Nat → Nat} (hg : VRenaming g gn)
    (F Rd : BitVec 64 → Prop) (fc : FnCtx) (X : ExtSem) (syms : String → Option Nat)
    (exts : List Clif.ExtFunc) (sigs : List Clif.Signature) (sp : BitVec 64)
    (pin : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop) (i : MInst) :
    csemG F fc X Rd syms exts sigs sp pin (i.mapRegs g) = csemG F fc X Rd syms exts sigs sp pin i := by
  funext us w
  unfold csemG
  rw [guardR_mapRegs hg F Rd fc.slotBase i us w,
    guardC_mapRegs hg F syms X exts sigs sp pin i us w,
    (driverSem_csem F fc X).rename g gn hg i]

/-- The value adapter retains the same guarded virtual renaming contract. -/
theorem valueSemG_mapRegs {g : Reg → Reg} {gn : Nat → Nat} (hg : VRenaming g gn)
    (F Rd : BitVec 64 → Prop) (fc : FnCtx) (X : ExtSem) (syms : String → Option Nat)
    (exts : List Clif.ExtFunc) (sigs : List Clif.Signature) (sp : BitVec 64)
    (pin : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop) (i : MInst) :
    valueSemG F fc X Rd syms exts sigs sp pin (i.mapRegs g) = valueSemG F fc X Rd syms exts sigs sp pin i := by
  funext us w
  simp only [valueSemG,Backend.DeadCleanup.specForm_mapRegs hg,mspec_mapRegs hg,csemG_mapRegs hg]

end E2E.StockAcquirePending
