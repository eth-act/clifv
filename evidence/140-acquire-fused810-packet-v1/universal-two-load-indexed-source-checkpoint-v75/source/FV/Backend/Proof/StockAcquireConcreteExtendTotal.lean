import FV.Backend.Proof.StockAcquirePureExtendHelper
import FV.Backend.Proof.RefinesCSem

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- These actual extension forms emit identical physical lines for every target width.
The concrete equality does not evaluate an unreached source instruction. -/
theorem straight_unsigned_small_extend_target {F : BitVec 64 → Prop} {ctx : FnCtx}
    {dest pointer fromB toB : Nat} (width : fromB = 8 ∨ fromB = 16)
    (value : CV) (world : Arm.ArmState) :
    straightSem F ctx (.extend (.vreg dest .int) (.vreg pointer .int) false fromB toB) [value] world =
      straightSem F ctx (.extend (.vreg dest .int) (.vreg pointer .int) false fromB 32) [value] world := by
  rcases width with rfl | rfl <;> rfl

/-- On the original well-formed machine world, every unsigned small extension executes concretely.
The target may describe a source instruction that execution never reaches after an earlier fault. -/
theorem csem_unsigned_small_extend_total {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem}
    {dest pointer fromB toB : Nat} (width : fromB = 8 ∨ fromB = 16)
    (value : CV) {world : Arm.ArmState}
    (errorFree : Arm.r .ERR world = .None) (aligned : Arm.CheckSPAlignment world) :
    ∃ nextWorld,csem F ctx X (.extend (.vreg dest .int) (.vreg pointer .int) false fromB toB) [value] world =
      some ([ofX ((((lo64 value).setWidth fromB).setWidth 32).setWidth 64)],nextWorld,.next) ∧
      SameWorld F nextWorld world := by
  have actualWidth : fromB = 8 ∨ fromB = 16 ∨ fromB = 32 := Or.elim width Or.inl (fun same => Or.inr (Or.inl same))
  have grows : fromB < 32 := by rcases width with rfl | rfl <;> decide
  obtain ⟨nextWorld,executed,same⟩ := refines_csem F ctx X _ _ _ _ _
    (ispec_extend (d := dest) (rn := .vreg pointer .int) (sg := false) (x := value)
      (w := world) actualWidth (Or.inl rfl) grows)
  have control : (MInst.extend (.vreg dest .int) (.vreg pointer .int) false fromB toB).isCtl = false := rfl
  have control32 : (MInst.extend (.vreg dest .int) (.vreg pointer .int) false fromB 32).isCtl = false := rfl
  have wellFormed : csemWF ctx (.extend (.vreg dest .int) (.vreg pointer .int) false fromB toB) [value] = true := rfl
  have wellFormed32 : csemWF ctx (.extend (.vreg dest .int) (.vreg pointer .int) false fromB 32) [value] = true := rfl
  rw [csem_of_wf control32 wellFormed32 errorFree aligned] at executed
  refine ⟨nextWorld,?_,same⟩
  rw [csem_of_wf control wellFormed errorFree aligned,straight_unsigned_small_extend_target width value world]
  exact executed

end Backend.Stock.Proof.Acquire810
