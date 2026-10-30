import FV.ArmFault.Step

/-!
# Faults depend only on the registers (A3, #412, slice F8c)

`instEvs_key`: the kinds, addresses and sizes of an instruction's memory events
(`Concurrency.ArmInstFoot.instEvs`) are functions of the registers (incl. the pc); only the bytes a
read event carries depend on the memory. So whether an instruction faults under a memory map
(`ArmFault.evsOk`) is the same on two states with the same registers (`evsOk_congr`), e.g. a
model state and the executable state that simulates it.
-/

namespace E2E.ExecBytes
open Arm Concurrency Concurrency.ArmThread Concurrency.ArmInstFoot

/-- The kind, address and size of an event (what `ArmFault.evsOk` reads). -/
def evKey (e : Ev) : AKind × BitVec 64 × Nat := (e.k, e.addr, e.n)

section
variable {s t : ArmState} (h : ∀ fld, r fld s = r fld t)
include h

theorem rg_congr (n : Nat) (i : BitVec 5) : read_gpr n i s = read_gpr n i t := by simp [read_gpr, h]
theorem sp_congr : CheckSPAlignment s ↔ CheckSPAlignment t := by simp [CheckSPAlignment, rg_congr h]
theorem off_congr (o : LDST.Reg_offset) (sc : Nat) : o.value sc s = o.value sc t := by
  cases o <;> simp [LDST.Reg_offset.value, read_gpr_zr, rg_congr h]

theorem immEvs_key (inst : LDST.Reg_imm_cls) : (immEvs inst s).map evKey = (immEvs inst t).map evKey := by
  unfold immEvs
  simp only [rg_congr h, sp_congr h, off_congr h]
  repeat' split
  all_goals rfl

theorem pairEvs_key (inst : LDST.Reg_pair_cls) : (pairEvs inst s).map evKey = (pairEvs inst t).map evKey := by
  unfold pairEvs
  simp only [rg_congr h, sp_congr h]
  repeat' split
  all_goals rfl

theorem ldsturEvs_key (inst : Reg_unscaled_imm_cls) : (ldsturEvs inst s).map evKey = (ldsturEvs inst t).map evKey := by
  unfold ldsturEvs
  simp only [rg_congr h, sp_congr h]
  repeat' split
  all_goals rfl

theorem exclEvs_key (inst : Reg_exclusive_cls) : (exclEvs inst s).map evKey = (exclEvs inst t).map evKey := by
  unfold exclEvs
  simp only [rg_congr h, sp_congr h]
  repeat' split
  all_goals rfl

theorem literalEvs_key (inst : Reg_literal_cls) : (literalEvs inst s).map evKey = (literalEvs inst t).map evKey := by
  have hpc : LDST.literal_address inst.imm19 s = LDST.literal_address inst.imm19 t := by
    simp [LDST.literal_address, read_pc, h]
  unfold literalEvs litEv
  simp only [hpc]
  repeat' split
  all_goals rfl

theorem instEvs_key (a : ArmInst) : (instEvs a s).map evKey = (instEvs a t).map evKey := by
  cases a with
  | LDST i =>
    cases i with
    | Reg_imm_post_indexed i => exact immEvs_key h _
    | Reg_unsigned_imm i => exact immEvs_key h _
    | Reg_unscaled_imm i =>
      simp only [instEvs]
      split
      · exact ldsturEvs_key h _
      · exact immEvs_key h _
    | Reg_pair_pre_indexed i => exact pairEvs_key h _
    | Reg_pair_post_indexed i => exact pairEvs_key h _
    | Reg_pair_signed_offset i => exact pairEvs_key h _
    | Reg_imm_pre_indexed i => exact immEvs_key h _
    | Reg_reg_offset i =>
      simp only [instEvs]
      split
      · rfl
      · exact immEvs_key h _
    | Reg_exclusive i => exact exclEvs_key h _
    | Reg_literal i => exact literalEvs_key h _
  | BR i => cases i <;> simp only [instEvs]
  | _ => simp only [instEvs]

/-- **Faults depend only on the registers** (the accesses' addresses and sizes). -/
theorem evsOk_congr (mp : ArmFault.MemMap) (a : ArmInst) :
    ArmFault.evsOk mp (instEvs a s) = ArmFault.evsOk mp (instEvs a t) := by
  have hk := instEvs_key h a
  generalize instEvs a s = L1 at hk
  generalize instEvs a t = L2 at hk
  induction L1 generalizing L2 with
  | nil => cases L2 <;> simp_all
  | cons e es ih =>
    cases L2 with
    | nil => simp at hk
    | cons e' es' =>
      simp only [List.map_cons, List.cons.injEq] at hk
      obtain ⟨he, hes⟩ := hk
      simp only [evKey, Prod.mk.injEq] at he
      obtain ⟨hk1, ha1, hn1⟩ := he
      simp only [ArmFault.evsOk, List.all_cons] at ih ⊢
      rw [ih es' hes]
      congr 1
      simp only [ArmFault.evOk, hk1, ha1, hn1]

end

end E2E.ExecBytes
