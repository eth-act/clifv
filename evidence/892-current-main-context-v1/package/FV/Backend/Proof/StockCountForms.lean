import FV.Backend.Proof.IselRulesALU
import FV.Backend.Proof.PrepareCheck
namespace Backend.Stock.Proof.ScalarCount
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
def countAlloc (trailing : Bool) (w : Nat) : Nat :=
  if w = 8 ∨ w = 16 then 3 else if trailing then 2 else 1
def countResult (trailing : Bool) (w d : Nat) : Nat := d + countAlloc trailing w - 1
def countCode (trailing : Bool) (w d x : Nat) : List MInst :=
  if w = 8 ∨ w = 16 then
    if trailing then
      [.bitRR .rbit .size32 (.vreg d .int) (.vreg x .int),
       .aluRRImmLogic .orr .size32 (.vreg (d+1) .int) (.vreg d .int) ⟨2^(32-w-1),.size32⟩,
       .bitRR .clz .size32 (.vreg (d+2) .int) (.vreg (d+1) .int)]
    else
      [.extend (.vreg d .int) (.vreg x .int) false w 32,
       .bitRR .clz .size32 (.vreg (d+1) .int) (.vreg d .int),
       .aluRRImm12 .sub .size32 (.vreg (d+2) .int) (.vreg (d+1) .int) ⟨32-w,false⟩]
  else if trailing then
    [.bitRR .rbit (szOf w) (.vreg d .int) (.vreg x .int),
     .bitRR .clz (szOf w) (.vreg (d+1) .int) (.vreg d .int)]
  else [.bitRR .clz (szOf w) (.vreg d .int) (.vreg x .int)]
end Backend.Stock.Proof.ScalarCount
