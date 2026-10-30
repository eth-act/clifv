import FV.Clif.Syntax

/-! The source/target type pairs of the scalar cast witnesses (`StockCastWitness`,
`StockReduceWitness`). Their own module, so that the latter need not wait for the former. -/
namespace Backend.Stock.Proof.ScalarCast.Witness
inductive Pair where
  | b8_16 | b8_32 | b8_64 | b16_32 | b16_64 | b32_64
  deriving DecidableEq
def Pair.fromTy : Pair → Clif.Ty
  | .b8_16 | .b8_32 | .b8_64 => .i8
  | .b16_32 | .b16_64 => .i16
  | .b32_64 => .i32
def Pair.toTy : Pair → Clif.Ty
  | .b8_16 => .i16
  | .b8_32 | .b16_32 => .i32
  | .b8_64 | .b16_64 | .b32_64 => .i64
end Backend.Stock.Proof.ScalarCast.Witness
