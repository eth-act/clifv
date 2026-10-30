import FV.Backend.Proof.IselRulesALU
import FV.Backend.Proof.PrepareCheck
namespace Backend.Stock.Proof.ScalarBit
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64

def bitrevRule (w : Nat) : Rule :=
  if w = 8 then rule_lower_1931 else if w = 16 then rule_lower_1937 else rule_lower_1946
def bitrevResult (w b : Nat) : Nat := if w = 8 ∨ w = 16 then b+1 else b
def bitrevAlloc (w : Nat) : Nat := if w = 8 ∨ w = 16 then 2 else 1
def bitrevCode (w b x : Nat) : List MInst :=
  if w = 8 ∨ w = 16 then
    [.bitRR .rbit .size32 (.vreg b .int) (.vreg x .int),
     .aluRRImmShift .lsr .size32 (.vreg (b+1) .int) (.vreg b .int) (32-w)]
  else [.bitRR .rbit (szOf w) (.vreg b .int) (.vreg x .int)]
def bitrevBase (w : Nat) (st : LState) (x : Reg) : LState :=
  if w = 8 ∨ w = 16 then
    (((st.fresh .int).2.emit (.bitRR .rbit .size32 (st.fresh .int).1 x)).fresh .int).2.emit
      (.aluRRImmShift .lsr .size32 (.vreg (st.nextVreg+1) .int) (st.fresh .int).1 (32-w))
  else (st.fresh .int).2.emit (.bitRR .rbit (szOf w) (st.fresh .int).1 x)
end Backend.Stock.Proof.ScalarBit
