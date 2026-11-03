import FV.Backend.Proof.StockAcquireExtendCanonical

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Actual successful line encoding supplies the internal width branch.
The theorem preserves assembly rejection instead of adding a source type check. -/
theorem extend_encoded_lines_widths {signed : Bool} {fromB toB : Nat}
    (sourceWidth : fromB = 8 ∨ fromB = 16 ∨ fromB = 32 ∨ fromB = 64)
    (targetWidth : toB = 8 ∨ toB = 16 ∨ toB = 32 ∨ toB = 64)
    {ctx : FnCtx} {env : Backend.Env} {dest pointer : Reg} {state next : PState} {lines : List Line}
    (expanded : (MInst.extend dest pointer signed fromB toB).lines ctx state = .ok (lines,next))
    (encoded : ∀ instruction trap,Line.ins instruction trap ∈ lines →
      ∃ arm, instruction.armFields env = .ok arm) :
    fromB ≤ 32 ∨ (signed = true ∧ toB = 64) := by
  by_cases small : fromB ≤ 32
  · exact Or.inl small
  · have width64 : fromB = 64 := by rcases sourceWidth with h | h | h | h <;> omega
    subst fromB
    cases signed
    · have actual : Except.ok ([Line.ins (.bfm .uBfm false dest pointer 0 63) none],state) =
          (Except.ok (lines,next) : Except String (List Line × PState)) := by
        simpa only [MInst.lines,Nat.reduceBEq,Bool.not_false,Bool.true_and,Bool.false_and,
          Bool.false_eq_true,ite_false,Nat.reduceSub,pure,Except.pure] using expanded
      have exactLines := congrArg Prod.fst (Except.ok.inj actual)
      dsimp only at exactLines
      obtain ⟨arm,word⟩ := encoded (.bfm .uBfm false dest pointer 0 63) none (by rw [← exactLines];simp)
      simp [Insn.armFields] at word
    · by_cases wide : toB = 64
      · exact Or.inr ⟨rfl,wide⟩
      · have targetSmall : ¬toB > 32 := by rcases targetWidth with h | h | h | h <;> omega
        have actual : Except.ok ([Line.ins (.bfm .sBfm false dest pointer 0 63) none],state) =
            (Except.ok (lines,next) : Except String (List Line × PState)) := by
          simpa [MInst.lines,targetSmall] using expanded
        have exactLines := congrArg Prod.fst (Except.ok.inj actual)
        dsimp only at exactLines
        obtain ⟨arm,word⟩ := encoded (.bfm .sBfm false dest pointer 0 63) none (by rw [← exactLines];simp)
        simp [Insn.armFields] at word

end Backend.Stock.Proof.Acquire810
