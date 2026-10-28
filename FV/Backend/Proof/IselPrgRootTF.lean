import FV.Backend.Proof.IselPrgRootT
import FV.Backend.Proof.IselPrgExtTF

/-!
# Progress of the ISLE lowering over the float scope: the roots (S11f, #35)

The V7 progress analysis over the float scope (`Compile.functionETF`: the typed movement scope
with the S11f float operations of `Compile.instETF`). The transfer functions are
`IselPrgExtTF`'s `aextTF` (`def_inst` may also find a float operation, `fDataTF`) and `actorT`.

`formOfTF` is the root form of a statement: `formOfT` on the typed movement scope; for a float
operation its `InstructionData` with the opcode (`fOpcIdx`), the operands as values of the typed
scope (`aVM`), of E (`aV`: the integer operand of an `fcvt_from_*`) or floats (`aVF`: the
operands of an `fcmp` and of a saturating `fcvt_to_*_sat`, whose `lower` roots match on the operand
type), and an `fcmp`'s condition as its `FloatCC` variant (`fccIdxF`). `stmtFormsTF` lists every
form.
-/

namespace Backend.Proof.Prg

open Backend Backend.Proof Isle Isle.Aarch64

/-- The `Opcode` index of a float operation of the float scope. -/
def fOpcIdx : Clif.FOp → Nat
  | .fadd => VIdx.Opcode.Fadd | .fsub => VIdx.Opcode.Fsub | .fmul => VIdx.Opcode.Fmul
  | .fdiv => VIdx.Opcode.Fdiv | .fmin => VIdx.Opcode.Fmin | .fmax => VIdx.Opcode.Fmax
  | .sqrt => VIdx.Opcode.Sqrt | .fneg => VIdx.Opcode.Fneg | .fabs => VIdx.Opcode.Fabs
  | .ceil => VIdx.Opcode.Ceil | .floor => VIdx.Opcode.Floor | .trunc => VIdx.Opcode.Trunc
  | .nearest => VIdx.Opcode.Nearest | .fpromote => VIdx.Opcode.Fpromote
  | .fdemote => VIdx.Opcode.Fdemote | .fcvtFromUint => VIdx.Opcode.FcvtFromUint
  | .fcvtFromSint => VIdx.Opcode.FcvtFromSint | .fcvtToUintSat => VIdx.Opcode.FcvtToUintSat
  | .fcvtToSintSat => VIdx.Opcode.FcvtToSintSat
  | _ => 0

/-- The abstract operand of a one-operand float operation: an integer for an `fcvt_from_*`, a
float for a saturating `fcvt_to_*_sat`, a value of the typed scope otherwise. -/
def fArgOf : Clif.FOp → PA
  | .fcvtFromUint | .fcvtFromSint => aV
  | .fcvtToUintSat | .fcvtToSintSat => aVF
  | _ => aVM

/-- The form of a two-operand float arithmetic statement. -/
def fFormBin (op : Clif.FOp) (ty : Clif.Ty) : PA :=
  .inst (tyOf ty) (idat VIdx.InstructionData.Binary [opc (fOpcIdx op), .vals [aVM, aVM]])

/-- The form of a one-operand float statement. -/
def fFormUn (op : Clif.FOp) (ty : Clif.Ty) : PA :=
  .inst (tyOf ty) (idat VIdx.InstructionData.Unary [opc (fOpcIdx op), fArgOf op])

/-- The variant index of a `FloatCC` (`mkVariant TyId.FloatCC (floatccName cc)`). -/
def fccIdxF : Clif.FloatCC → Nat
  | .eq => 0 | .gt => 1 | .ge => 2 | .lt => 3 | .le => 4 | .ne => 5 | .ord => 6 | .one => 7
  | .uno => 8 | .ueq => 9 | .ugt => 10 | .uge => 11 | .ult => 12 | .ule => 13

/-- The form of an `fcmp` (its result an `i8`). -/
def fFormCmp (cc : Clif.FloatCC) : PA :=
  .inst (.ty [.int 8]) (idat VIdx.InstructionData.FloatCompare
    [opc VIdx.Opcode.Fcmp, .vals [aVF, aVF], .data TyId.FloatCC (fccIdxF cc) []])

/-- **The root form of a statement of the float scope**: `formOfT`, or the form of a float
operation. -/
def formOfTF (f : Clif.Function) (c : Clif.Inst) : PA :=
  match c with
  | .float (.fcmp cc) _ _ => fFormCmp cc
  | .float op ty [_, _] => fFormBin op ty
  | .float op ty [_] => fFormUn op ty
  | c => formOfT f c

/-- The two-operand float arithmetic. -/
def fBinOps : List Clif.FOp := [.fadd, .fsub, .fmul, .fdiv, .fmin, .fmax]

/-- The one-operand float arithmetic and rounding at `f32`/`f64`. -/
def fUnOps : List Clif.FOp := [.sqrt, .fneg, .fabs, .ceil, .floor, .trunc, .nearest]

/-- The conversions from an integer. -/
def fFromOps : List Clif.FOp := [.fcvtFromUint, .fcvtFromSint]

/-- The saturating conversions to an integer. -/
def fToOps : List Clif.FOp := [.fcvtToUintSat, .fcvtToSintSat]

/-- The `fcmp` conditions `instData` admits (`fccOk`). -/
def fCCs : List Clif.FloatCC := [.eq, .ne, .lt, .le, .gt, .ge, .ord, .uno, .ult, .ule, .ugt, .uge]

/-- **The float operations' forms.** -/
def fFormsTF : List PA :=
  (fBinOps.flatMap fun op => fTys.map (fFormBin op)) ++
  (fUnOps.flatMap fun op => fTys.map (fFormUn op)) ++
  [fFormUn .fpromote .f64, fFormUn .fdemote .f32] ++
  (fFromOps.flatMap fun op => fTys.map (fFormUn op)) ++
  (fToOps.flatMap fun op => [Clif.Ty.i32, .i64].map (fFormUn op)) ++
  fCCs.map fFormCmp

/-- **Every statement form of the float scope**: the typed movement scope's and the float
operations'. -/
def stmtFormsTF : List PA := stmtFormsT ++ fFormsTF

end Backend.Proof.Prg
