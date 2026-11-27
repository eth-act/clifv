import FV.Backend.Proof.DeadCleanupSem
import FV.E2E.Guarded
import FV.E2E.PairGuardS

/-! Witnesses for #1181: the cleanup removes the literal-pool load (`ldr dN, <entry>`,
`fpuLoad … (.const v)`) of an unused float constant, as Cranelift never lowers an instruction
whose result is unused (`machinst/lower.rs`), and keeps a used one. Shape: serde_json's
float-parsing function `_RNxC10serde_json12HdPCfZJjEMTN` in cg_clif's optimised CLIF, where LICM
left `v47 = f64const 0x1.1ccf385ebc8a0p1023` unused in a block whose successor defines and uses
its own copy (`v116 = fdiv.f64 v95, v115`); reduced: `v1 = f64const A` (unused),
`v2 = f64const B`, `v3 = fdiv v0, v2`, `return v3`. Stock emits `ldr d, <B>; fdiv`; the pool
holds `B` only (the pool is built from the emitted lines, `Asm.poolUses`).

Negative witnesses: an addressed float load (a memory access) is not a pure form, and a pool load
whose result is used stays.

The three statements this change replaces are false under the new `pureForm` (rule (a)); the dead
pool load refutes each (last three examples): `specForm_loadForm` (now `specForm_loadForm_npool`),
`loadForm_of_flagFree_or_jump` (now `loadForm_of_flagFree_or_jump_npool`) and the private
`spec_guarded` of `FV/E2E/DeadCleanupGuarded.lean` (now `spec_guarded_npool`). -/

namespace Backend.DeadCleanup
open Backend.Proof

/-- `0x1.1ccf385ebc8a0p1023` and `0x1.0c6f7a0b5ed8dp-20` (their `u64` bits). -/
private def entA : Nat := 0x7fe1ccf385ebc8a0
private def entB : Nat := 0x3eb0c6f7a0b5ed8d
private def poolDead : MInst := .fpuLoad .size64 (.vreg 1 .float) (.const entA) default
private def poolUsed : MInst := .fpuLoad .size64 (.vreg 2 .float) (.const entB) default
private def fdiv : MInst := .fpuRRR .div .size64 (.vreg 3 .float) (.vreg 0 .float) (.vreg 2 .float)
private def retF : MInst := .rets [(.vreg 3 .float, .v 0)]
/-- the dead constant also returned: it stays live -/
private def retBoth : MInst := .rets [(.vreg 3 .float, .v 0), (.vreg 1 .float, .v 1)]
/-- an addressed float load of a stack slot: a memory access, not a pure form -/
private def slotLoad : MInst := .fpuLoad .size64 (.vreg 1 .float) (.slotOffset 8) default

/-- The literal-pool load is a flag-free producer; an addressed float load is not pure. -/
example : pureForm poolDead = true ∧ flagFree poolDead = true ∧ pureForm slotLoad = false :=
  ⟨rfl, rfl, rfl⟩

/-- Its specification gives the entry's value from no use, keeps the world and continues. -/
example (w : Arm.ArmState) : mspec 0 poolDead [] w = some ([poolVal .size64 entA], w, .next) := by
  simp [poolDead, mspec]

/-- From a world whose flags a compare wrote it steps alike (it reads no flags). -/
example (p : Arm.PState) (w : Arm.ArmState) :
    mspec 0 poolDead [] (Arm.write_pstate p w) =
      (mspec 0 poolDead [] w).map (fun r => (r.1, Arm.write_pstate p r.2.1, r.2.2)) :=
  mspec_flagFree_pstate rfl p w

/-- The unused constant's load goes: `ldr d, <B>; fdiv`, as stock emits. -/
example : (scan 4 [poolDead, poolUsed, fdiv, retF] []).1 = [poolUsed, fdiv, retF] := by decide

/-- Negative: a pool load whose result is returned stays. -/
example : (scan 4 [poolDead, poolUsed, fdiv, retBoth] []).1 =
    [poolDead, poolUsed, fdiv, retBoth] := by decide

/-- Negative: an unused addressed float load stays (memory access). -/
example : (scan 4 [slotLoad, poolUsed, fdiv, retF] []).1 = [slotLoad, poolUsed, fdiv, retF] := by
  decide

/-- The production pass (`prune`) on the whole function. -/
example : ∃ vc : VCode, (prune vc).blocks[0]!.insts.toList = [poolUsed, fdiv, retF] := by
  refine ⟨⟨"dead_pool_const", #[⟨0, #[poolDead, poolUsed, fdiv, retF], #[], #[]⟩],
    #[.float, .float, .float, .float], 0, 0, #[], #[], none⟩, ?_⟩
  decide +kernel

/-- Old `specForm_loadForm` is false: the pool load is a specification form and a load form. -/
example : ¬ ∀ i : MInst, specForm i = true → i.loadForm = false := fun h =>
  absurd (h poolDead rfl) (by decide)

/-- Old `loadForm_of_flagFree_or_jump` is false: the pool load is flag-free and a load form. -/
example : ¬ ∀ j : MInst, (flagFree j || isJump j) = true → j.loadForm = false := fun h =>
  absurd (h poolDead rfl) (by decide)

/-- Old `spec_guarded` is false for every guard parameter: the pool load is a specification form,
`GuardR` rejects every float load (`csemG` gives `none`), and `csem` gives the entry's value. -/
example (F Rd : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) (syms : String → Option Nat)
    (exts : List Clif.ExtFunc) (sigs : List Clif.Signature) (sp0 : BitVec 64)
    (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop) (w : Arm.ArmState) :
    specForm poolDead = true ∧
      E2E.csemG F ctx X Rd syms exts sigs sp0 Pc poolDead [] w ≠ csem F ctx X poolDead [] w := by
  refine ⟨rfl, ?_⟩
  simp only [poolDead]
  rw [csem_pool_mspec]
  simp [E2E.csemG, E2E.GuardR, mspec]

end Backend.DeadCleanup
