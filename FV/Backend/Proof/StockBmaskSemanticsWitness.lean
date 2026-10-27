import FV.Backend.Proof.StockBmaskSemantics

namespace Backend.Stock.Proof.ScalarMask
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

private def registers (ty : Clif.Ty) (literal : Int) (n : Nat) : CV :=
  if n = 7 then (BitVec.ofInt ty.width literal).setWidth 128 else 0

/-- All original input/output type pairs and arbitrary source integers inhabit
resolved machine semantics. The original operand resolves above the entire
fresh interval, exercising the reverse-allocation case. -/
theorem stock_bmask_resolved_witness :
    ∀ ti ∈ ([Clif.Ty.i8,.i16,.i32,.i64] : List Clif.Ty),
    ∀ to ∈ ([Clif.Ty.i8,.i16,.i32,.i64] : List Clif.Ty),∀ literal : Int,
      Runs (fun _ => False) ispec ((bmaskCode ti.width 2 0).map
        (·.mapRegs (Backend.lowerFunction.resolve #[some 7] 2))) (registers ti literal)
          Arm.ArmState.default (fun ρ' _ =>
            VHolds ⟨to,Clif.Sem.bmask (Clif.Val.ofInt ti literal).bits⟩
              (ρ' (bmaskResultNum ti.width 2)) ∧
            ∀ n,n < 2 ∨ 2+bmaskAlloc ti.width ≤ n → ρ' n = registers ti literal n) := by
  intro ti inMember to outMember literal
  have input : ti.width = 8 ∨ ti.width = 16 ∨ ti.width = 32 ∨ ti.width = 64 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at inMember
    rcases inMember with rfl | rfl | rfl | rfl <;> simp [Clif.Ty.width]
  have output : eTy to = true := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at outMember
    rcases outMember with rfl | rfl | rfl | rfl <;> rfl
  have typed : CTy.ofClif (Clif.Val.ofInt ti literal).ty = .int ti.width := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at inMember
    rcases inMember with rfl | rfl | rfl | rfl <;> rfl
  have held : VHolds (Clif.Val.ofInt ti literal)
      (registers ti literal (aliasNum #[some 7] 0)) := by
    rw [show aliasNum #[some 7] 0 = 7 from rfl]
    simp only [registers,ite_true,VHolds,Clif.Val.ofInt]
    rw [BitVec.setWidth_setWidth_of_le _ (by rcases input with h | h | h | h <;> omega)]
    simp only [BitVec.setWidth_eq]
  have refines : Refines (fun _ => False) ispec := by
    intro inst args world outs next ctl executed
    exact ⟨next,executed,SameWorld.refl _ _⟩
  exact stock_bmask_resolved refines input output typed (by decide) held Arm.ArmState.default

end Backend.Stock.Proof.ScalarMask
