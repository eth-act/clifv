import FV.Backend.Proof.RegallocMemCorr
import FV.Backend.Proof.RegallocOS

/-!
# `OperandsSound` for loads and stores (M6 proof)

Every addressing mode of `amodeAddr` (stack-slot offset, `unscaled`, `unsignedOffset`,
`regReg`, `regScaled`, `regScaledExtended`, `regExtended`) with vreg operands, for loads
(`uload*`/`sload*`) and stores (`store8..64`).
-/

namespace Backend.Proof

open Backend

variable (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (X : ExtSem)

/-! ## `Corr` per addressing mode -/

section
variable {bytes : Nat}

theorem mm_unscaled {off : Int} (h1 : -256 ≤ off) (h2 : off < 256) :
    ∀ a : Nat, a < 29 → MemMode bytes (.unscaled (.x a) off) := fun a ha =>
  ⟨by simp [BaseOk]; omega, h1, h2⟩

theorem mm_uoff {off : Nat} (h1 : off % bytes = 0) (h2 : off / bytes < 4096) :
    ∀ a : Nat, a < 29 → MemMode bytes (.unsignedOffset (.x a) off) := fun a ha =>
  ⟨by simp [BaseOk]; omega, h1, h2⟩

theorem mm_regReg : ∀ a b : Nat, a < 29 → b < 29 → MemMode bytes (.regReg (.x a) (.x b)) :=
  fun a b ha hb => ⟨by simp [BaseOk]; omega, by simp [IdxOk]; omega⟩

theorem mm_regScaled : ∀ a b : Nat, a < 29 → b < 29 → MemMode bytes (.regScaled (.x a) (.x b)) :=
  fun a b ha hb => ⟨by simp [BaseOk]; omega, by simp [IdxOk]; omega⟩

theorem mm_regScaledExtended {e : ExtendOp} (he : extOk e) :
    ∀ a b : Nat, a < 29 → b < 29 → MemMode bytes (.regScaledExtended (.x a) (.x b) e) :=
  fun a b ha hb => ⟨by simp [BaseOk]; omega, by simp [IdxOk]; omega, he⟩

theorem mm_regExtended {e : ExtendOp} (he : extOk e) :
    ∀ a b : Nat, a < 29 → b < 29 → MemMode bytes (.regExtended (.x a) (.x b) e) :=
  fun a b ha hb => ⟨by simp [BaseOk]; omega, by simp [IdxOk]; omega, he⟩

end

/-! ## Loads -/

theorem os_load_slot (op : LoadOp) (hop : op ≠ .fpuLoad128) (d : Nat) (off : Int)
    (fl : Clif.MemFlags) :
    OperandsSound F (execMInst ctx env) (csem F ctx X) (.load op (.vreg d .int) (.slotOffset off) fl) :=
  os_of_corr rfl _ (by assign_tac) (by fo_tac) rfl rfl (corr_load0 F ctx env op hop d off fl)

theorem os_load_sp (op : LoadOp) (hop : op ≠ .fpuLoad128) (d : Nat) (off : Int)
    (fl : Clif.MemFlags) :
    OperandsSound F (execMInst ctx env) (csem F ctx X) (.load op (.vreg d .int) (.spOffset off) fl) :=
  os_of_corr rfl _ (by assign_tac) (by fo_tac) rfl rfl (corr_load_sp F ctx env op hop d off fl)

theorem os_load_fp (op : LoadOp) (hop : op ≠ .fpuLoad128) (d : Nat) (off : Int)
    (fl : Clif.MemFlags) :
    OperandsSound F (execMInst ctx env) (csem F ctx X) (.load op (.vreg d .int) (.fpOffset off) fl) :=
  os_of_corr rfl _ (by assign_tac) (by fo_tac) rfl rfl (corr_load_fp F ctx env op hop d off fl)

theorem os_load_unscaled (op : LoadOp) (hop : op ≠ .fpuLoad128) (d n : Nat) (off : Int)
    (h1 : -256 ≤ off) (h2 : off < 256) (fl : Clif.MemFlags) :
    OperandsSound F (execMInst ctx env) (csem F ctx X)
      (.load op (.vreg d .int) (.unscaled (.vreg n .int) off) fl) :=
  os_of_corr rfl _ (by assign_tac) (by fo_tac) rfl rfl
    (corr_load1 F ctx env op hop d n fl (fun r => .unscaled r off) (fun a => a + BitVec.ofInt 64 off) (mm_unscaled h1 h2)
      (fun _ _ => rfl))

theorem os_load_uoff (op : LoadOp) (hop : op ≠ .fpuLoad128) (d n off : Nat)
    (h1 : off % op.bytes = 0) (h2 : off / op.bytes < 4096) (fl : Clif.MemFlags) :
    OperandsSound F (execMInst ctx env) (csem F ctx X)
      (.load op (.vreg d .int) (.unsignedOffset (.vreg n .int) off) fl) :=
  os_of_corr rfl _ (by assign_tac) (by fo_tac) rfl rfl
    (corr_load1 F ctx env op hop d n fl (fun r => .unsignedOffset r off) (fun a => a + BitVec.ofNat 64 off) (mm_uoff h1 h2)
      (fun _ _ => rfl))

theorem os_load_regReg (op : LoadOp) (hop : op ≠ .fpuLoad128) (d n m : Nat) (fl : Clif.MemFlags) :
    OperandsSound F (execMInst ctx env) (csem F ctx X)
      (.load op (.vreg d .int) (.regReg (.vreg n .int) (.vreg m .int)) fl) :=
  os_of_corr rfl _ (by assign_tac) (by fo_tac) rfl rfl
    (corr_load2 F ctx env op hop d n m fl .regReg (fun a b => a + b) mm_regReg (fun _ _ _ => rfl))

theorem os_load_regScaled (op : LoadOp) (hop : op ≠ .fpuLoad128) (d n m : Nat) (fl : Clif.MemFlags) :
    OperandsSound F (execMInst ctx env) (csem F ctx X)
      (.load op (.vreg d .int) (.regScaled (.vreg n .int) (.vreg m .int)) fl) :=
  os_of_corr rfl _ (by assign_tac) (by fo_tac) rfl rfl
    (corr_load2 F ctx env op hop d n m fl .regScaled (fun a b => a + b <<< log2 op.bytes) mm_regScaled (fun _ _ _ => rfl))

theorem os_load_regScaledExtended (op : LoadOp) (hop : op ≠ .fpuLoad128) (d n m : Nat)
    (e : ExtendOp) (he : extOk e) (fl : Clif.MemFlags) :
    OperandsSound F (execMInst ctx env) (csem F ctx X)
      (.load op (.vreg d .int) (.regScaledExtended (.vreg n .int) (.vreg m .int) e) fl) :=
  os_of_corr rfl _ (by assign_tac) (by fo_tac) rfl rfl
    (corr_load2 F ctx env op hop d n m fl (fun a b => .regScaledExtended a b e)
      (fun a b => a + Arm.extend_reg b (Arm.decode_reg_extend e.bits) (log2 op.bytes))
      (mm_regScaledExtended he) (fun _ _ _ => rfl))

theorem os_load_regExtended (op : LoadOp) (hop : op ≠ .fpuLoad128) (d n m : Nat)
    (e : ExtendOp) (he : extOk e) (fl : Clif.MemFlags) :
    OperandsSound F (execMInst ctx env) (csem F ctx X)
      (.load op (.vreg d .int) (.regExtended (.vreg n .int) (.vreg m .int) e) fl) :=
  os_of_corr rfl _ (by assign_tac) (by fo_tac) rfl rfl
    (corr_load2 F ctx env op hop d n m fl (fun a b => .regExtended a b e)
      (fun a b => a + Arm.extend_reg b (Arm.decode_reg_extend e.bits) 0)
      (mm_regExtended he) (fun _ _ _ => rfl))

/-! ## Stores -/

theorem os_store_slot (op : StoreOp) (hop : op ≠ .fpuStore128) (d : Nat) (off : Int)
    (fl : Clif.MemFlags) :
    OperandsSound F (execMInst ctx env) (csem F ctx X) (.store op (.vreg d .int) (.slotOffset off) fl) :=
  os_of_corr rfl _ (by assign_tac) (by fo_tac) rfl rfl (corr_store0 F ctx env op hop d off fl)

theorem os_store_sp (op : StoreOp) (hop : op ≠ .fpuStore128) (d : Nat) (off : Int)
    (fl : Clif.MemFlags) :
    OperandsSound F (execMInst ctx env) (csem F ctx X) (.store op (.vreg d .int) (.spOffset off) fl) :=
  os_of_corr rfl _ (by assign_tac) (by fo_tac) rfl rfl (corr_store_sp F ctx env op hop d off fl)

theorem os_store_fp (op : StoreOp) (hop : op ≠ .fpuStore128) (d : Nat) (off : Int)
    (fl : Clif.MemFlags) :
    OperandsSound F (execMInst ctx env) (csem F ctx X) (.store op (.vreg d .int) (.fpOffset off) fl) :=
  os_of_corr rfl _ (by assign_tac) (by fo_tac) rfl rfl (corr_store_fp F ctx env op hop d off fl)

theorem os_store_unscaled (op : StoreOp) (hop : op ≠ .fpuStore128) (d n : Nat) (off : Int)
    (h1 : -256 ≤ off) (h2 : off < 256) (fl : Clif.MemFlags) :
    OperandsSound F (execMInst ctx env) (csem F ctx X)
      (.store op (.vreg d .int) (.unscaled (.vreg n .int) off) fl) :=
  os_of_corr rfl _ (by assign_tac) (by fo_tac) rfl rfl
    (corr_store1 F ctx env op hop d n fl (fun r => .unscaled r off) (fun a => a + BitVec.ofInt 64 off) (mm_unscaled h1 h2)
      (fun _ _ => rfl))

theorem os_store_uoff (op : StoreOp) (hop : op ≠ .fpuStore128) (d n off : Nat)
    (h1 : off % op.bytes = 0) (h2 : off / op.bytes < 4096) (fl : Clif.MemFlags) :
    OperandsSound F (execMInst ctx env) (csem F ctx X)
      (.store op (.vreg d .int) (.unsignedOffset (.vreg n .int) off) fl) :=
  os_of_corr rfl _ (by assign_tac) (by fo_tac) rfl rfl
    (corr_store1 F ctx env op hop d n fl (fun r => .unsignedOffset r off) (fun a => a + BitVec.ofNat 64 off) (mm_uoff h1 h2)
      (fun _ _ => rfl))

theorem os_store_regReg (op : StoreOp) (hop : op ≠ .fpuStore128) (d n m : Nat) (fl : Clif.MemFlags) :
    OperandsSound F (execMInst ctx env) (csem F ctx X)
      (.store op (.vreg d .int) (.regReg (.vreg n .int) (.vreg m .int)) fl) :=
  os_of_corr rfl _ (by assign_tac) (by fo_tac) rfl rfl
    (corr_store2 F ctx env op hop d n m fl .regReg (fun a b => a + b) mm_regReg (fun _ _ _ => rfl))

theorem os_store_regScaled (op : StoreOp) (hop : op ≠ .fpuStore128) (d n m : Nat) (fl : Clif.MemFlags) :
    OperandsSound F (execMInst ctx env) (csem F ctx X)
      (.store op (.vreg d .int) (.regScaled (.vreg n .int) (.vreg m .int)) fl) :=
  os_of_corr rfl _ (by assign_tac) (by fo_tac) rfl rfl
    (corr_store2 F ctx env op hop d n m fl .regScaled (fun a b => a + b <<< log2 op.bytes) mm_regScaled (fun _ _ _ => rfl))

theorem os_store_regScaledExtended (op : StoreOp) (hop : op ≠ .fpuStore128) (d n m : Nat)
    (e : ExtendOp) (he : extOk e) (fl : Clif.MemFlags) :
    OperandsSound F (execMInst ctx env) (csem F ctx X)
      (.store op (.vreg d .int) (.regScaledExtended (.vreg n .int) (.vreg m .int) e) fl) :=
  os_of_corr rfl _ (by assign_tac) (by fo_tac) rfl rfl
    (corr_store2 F ctx env op hop d n m fl (fun a b => .regScaledExtended a b e)
      (fun a b => a + Arm.extend_reg b (Arm.decode_reg_extend e.bits) (log2 op.bytes))
      (mm_regScaledExtended he) (fun _ _ _ => rfl))

theorem os_store_regExtended (op : StoreOp) (hop : op ≠ .fpuStore128) (d n m : Nat)
    (e : ExtendOp) (he : extOk e) (fl : Clif.MemFlags) :
    OperandsSound F (execMInst ctx env) (csem F ctx X)
      (.store op (.vreg d .int) (.regExtended (.vreg n .int) (.vreg m .int) e) fl) :=
  os_of_corr rfl _ (by assign_tac) (by fo_tac) rfl rfl
    (corr_store2 F ctx env op hop d n m fl (fun a b => .regExtended a b e)
      (fun a b => a + Arm.extend_reg b (Arm.decode_reg_extend e.bits) 0)
      (mm_regExtended he) (fun _ _ _ => rfl))

end Backend.Proof
