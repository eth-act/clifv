import FV.Backend.Proof.StockAcquireFallbackExtendConcrete

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- The same emitted move or bitfield form, including source instructions that are never reached. -/
def concreteExtendCanonical (signed : Bool) (fromB toB dest pointer : Nat) : MInst :=
  if !signed && fromB == 32 && toB == 64 then .mov .size32 (.vreg dest .int) (.vreg pointer .int)
  else .bitfieldMove (if signed && toB > 32 then .size64 else .size32)
    (if signed then .sBfm else .uBfm) (.vreg dest .int) (.vreg pointer .int) 0 (fromB-1)

/-- Every original scalar width pair has the identical concrete canonical execution.
Encoding rejection is preserved by this equality; totality is a separate theorem. -/
theorem straight_extend_canonical {F : BitVec 64 → Prop} {ctx : FnCtx}
    {signed : Bool} {fromB toB dest pointer : Nat}
    (sourceWidth : fromB = 8 ∨ fromB = 16 ∨ fromB = 32 ∨ fromB = 64)
    (targetWidth : toB = 8 ∨ toB = 16 ∨ toB = 32 ∨ toB = 64)
    (value : CV) (world : Arm.ArmState) :
    straightSem F ctx (.extend (.vreg dest .int) (.vreg pointer .int) signed fromB toB) [value] world =
      straightSem F ctx (concreteExtendCanonical signed fromB toB dest pointer) [value] world := by
  rcases sourceWidth with rfl | rfl | rfl | rfl <;>
    rcases targetWidth with rfl | rfl | rfl | rfl <;> cases signed <;> rfl

/-- The exact 25 encodable scalar cases have total canonical specifications for arbitrary values.
The seven rejected cases remain outside this internal encoding branch, not outside source admission. -/
theorem concrete_extend_canonical_spec_total {signed : Bool} {fromB toB dest pointer : Nat}
    (sourceWidth : fromB = 8 ∨ fromB = 16 ∨ fromB = 32 ∨ fromB = 64)
    (targetWidth : toB = 8 ∨ toB = 16 ∨ toB = 32 ∨ toB = 64)
    (encoded : fromB ≤ 32 ∨ (signed = true ∧ toB = 64)) (value : CV) :
    ∃ output : CV,∀ world,ispec (concreteExtendCanonical signed fromB toB dest pointer) [value] world =
      some ([output],world,.next) := by
  rcases sourceWidth with rfl | rfl | rfl | rfl <;>
    rcases targetWidth with rfl | rfl | rfl | rfl <;> cases signed
  all_goals first
    | (simp at encoded)
    | (refine ⟨_,?_⟩;intro world;rfl)

/-- The original concrete semantics executes every encoded fallback width, without future source evaluation. -/
theorem csem_extend_encoded_total {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem}
    {signed : Bool} {fromB toB dest pointer : Nat}
    (sourceWidth : fromB = 8 ∨ fromB = 16 ∨ fromB = 32 ∨ fromB = 64)
    (targetWidth : toB = 8 ∨ toB = 16 ∨ toB = 32 ∨ toB = 64)
    (encoded : fromB ≤ 32 ∨ (signed = true ∧ toB = 64))
    (value : CV) {world : Arm.ArmState}
    (errorFree : Arm.r .ERR world = .None) (aligned : Arm.CheckSPAlignment world) :
    ∃ output nextWorld,csem F ctx X (.extend (.vreg dest .int) (.vreg pointer .int) signed fromB toB) [value] world =
      some ([output],nextWorld,.next) ∧ SameWorld F nextWorld world := by
  obtain ⟨output,spec⟩ := concrete_extend_canonical_spec_total sourceWidth targetWidth encoded value
  obtain ⟨nextWorld,executed,same⟩ := refines_csem F ctx X _ _ _ _ _ (spec world)
  have control : (MInst.extend (.vreg dest .int) (.vreg pointer .int) signed fromB toB).isCtl = false := rfl
  have wellFormed : csemWF ctx (.extend (.vreg dest .int) (.vreg pointer .int) signed fromB toB) [value] = true := rfl
  have canonicalControl : (concreteExtendCanonical signed fromB toB dest pointer).isCtl = false := by
    unfold concreteExtendCanonical
    split <;> rfl
  have canonicalWf : csemWF ctx (concreteExtendCanonical signed fromB toB dest pointer) [value] = true := by
    unfold concreteExtendCanonical
    split <;> rfl
  rw [csem_of_wf canonicalControl canonicalWf errorFree aligned] at executed
  refine ⟨output,nextWorld,?_,same⟩
  rw [csem_of_wf control wellFormed errorFree aligned,straight_extend_canonical sourceWidth targetWidth value world]
  exact executed

end Backend.Stock.Proof.Acquire810
