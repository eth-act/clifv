import FV.Clif
import Lean.Data.Json

/-!
# Oracle records (`clif-oracle interp` / `clif-native` JSON lines)

The run-line result schema shared by `clif-filetest` and `clif-fuzz` (`docs/contracts/clif.md`),
and the comparison of a `Clif.run` outcome with a record.
-/

open Clif Lean

namespace ClifFiletest

def hexBits (v : Val) : String :=
  let digits := v.ty.width / 4
  let h := String.ofList (Nat.toDigits 16 v.toNat)
  "0x" ++ String.ofList (List.replicate (digits - h.length) '0') ++ h

inductive OracleActual where
  | returned (vals : List (String × Nat))
  | trapped (code : String)
  | error (msg : String)

structure OracleRecord where
  attached : String
  func : String
  actual : OracleActual

def parseBits (s : String) : Option Nat :=
  match s.toList with
  | '0' :: 'x' :: hs =>
    hs.foldlM (init := 0) fun acc h =>
      if h.isDigit then some (acc * 16 + (h.toNat - '0'.toNat))
      else if 'a' ≤ h ∧ h ≤ 'f' then some (acc * 16 + (h.toNat - 'a'.toNat + 10))
      else if 'A' ≤ h ∧ h ≤ 'F' then some (acc * 16 + (h.toNat - 'A'.toNat + 10))
      else none
  | _ => none

def parseValue (j : Json) : Except String (String × Nat) := do
  let ty ← j.getObjValAs? String "ty"
  let bits ← j.getObjValAs? String "bits"
  match parseBits bits with
  | some n => return (ty, n)
  | none => throw s!"bad bits {bits}"

def parseRecord (j : Json) : Except String OracleRecord := do
  let attached ← j.getObjValAs? String "attached"
  let func ← j.getObjValAs? String "func"
  let act ← j.getObjVal? "actual"
  let actual ←
    match act.getObjVal? "returned" with
    | .ok (.arr vs) => pure (.returned (← vs.toList.mapM parseValue))
    | _ =>
      match act.getObjValAs? String "trapped" with
      | .ok c => pure (.trapped c)
      | _ => pure (.error ((act.getObjValAs? String "error").toOption.getD "?"))
  return { attached, func, actual }

def loadOracle (path : System.FilePath) : IO (Except String (List OracleRecord)) := do
  let txt ← IO.FS.readFile path
  let mut out := #[]
  for line in txt.splitOn "\n" do
    if line.trimAscii.isEmpty then continue
    match Json.parse line with
    | .error e => return .error s!"{path}: {e}"
    | .ok j =>
      if let .ok e := j.getObjValAs? String "file_error" then
        return .error s!"oracle could not read the file: {e}"
      match parseRecord j with
      | .ok r => out := out.push r
      | .error e => return .error s!"{path}: {e}"
  return .ok out.toList

/-- The type name the interpreter reports for a value of type `t`: its `DataValue::V128`/`V64`
carry no lane type and report `i8x16`/`i8x8` (`DataValue::ty`). -/
def oracleTyName : Ty → String
  | .vec s => if s.width == 128 then "i8x16" else "i8x8"
  | t => t.name

/-- The interpreter returned a non-vector value where the signature has a vector result: its
`bitcast` from a scalar to a vector type converts the scalar to the lane type and returns that
lane alone (Cranelift 0.136.1 `interpreter/src/step.rs`, `Opcode::Bitcast`), so the record is no
observation of the function. -/
def illTypedVec (o : Outcome) (a : OracleActual) : Bool :=
  match o, a with
  | .returned vs _, .returned ws =>
    vs.length == ws.length && (vs.zip ws).any fun (v, (tn, _)) => v.ty.isVec && tn != oracleTyName v.ty
  | _, _ => false

/-- Agreement of our outcome with the interpreter's. `none`: the oracle reported an error or an
ill-typed vector result (`illTypedVec`; no comparison possible). -/
def agree (o : Outcome) (a : OracleActual) : Option Bool :=
  if illTypedVec o a then none else
  match o, a with
  | .returned vs _, .returned ws => some (vs.map (fun v => (oracleTyName v.ty, v.toNat)) == ws)
  | .trapped c, .trapped d => some (c.name == d)
  | _, .error _ => none
  | _, _ => some false

/-- Are the bits `n` of type `ty` a NaN (exponent all ones, fraction nonzero)? -/
def isNaNBits (ty : Ty) (n : Nat) : Bool :=
  ty.isFloat &&
    (let (e, t) := FloatLit.fields ty.width
     n / 2 ^ t % 2 ^ e == 2 ^ e - 1 && n % 2 ^ t != 0)

/-- Our returned values and the interpreter's agree up to NaN payloads: pairwise equal, or both
NaN of the same float type. -/
def agreeUpToNaN (o : Outcome) (a : OracleActual) : Bool :=
  match o, a with
  | .returned vs _, .returned ws =>
    vs.length == ws.length && (vs.zip ws).all fun (v, (tn, n)) =>
      oracleTyName v.ty == tn && (v.toNat == n || (isNaNBits v.ty v.toNat && isNaNBits v.ty n))
  | _, _ => false

end ClifFiletest
