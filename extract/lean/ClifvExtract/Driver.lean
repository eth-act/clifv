import Lean.Data.Json
import ClifvGen.Funs

/-! `clifv-extract-lean REQUEST.json RESULT.json`: the extracted pipeline behind the request/result
schema of `clifv-extract-native` (`extract/rust/native-cli/src/main.rs`). Results are written
byte-for-byte as the native CLI writes them (`serde_json::to_vec` of a `Value`: compact, object
keys sorted, serde_json string escaping), so `compare.py --candidate lean` can compare the two
result files directly. -/

open Aeneas Aeneas.Std Result
open clifv_extract_entry clifv_extract_entry.cranelift_codegen

namespace ClifvExtract.Driver

/-! ## JSON output (serde_json's compact writer) -/

inductive Out where
  | num (n : Int)
  | str (s : String)
  | arr (xs : List Out)
  /-- Keys must be given in sorted order (serde_json `Map` is a `BTreeMap`). -/
  | obj (kvs : List (String × Out))

def hexDigit (n : Nat) : Char := "0123456789abcdef".toList[n % 16]!

/-- serde_json escaping: `"` `\\` and the C0 controls; `\b \t \n \f \r` short forms, the
others `\u00XX` with lowercase hex. Everything else is written as UTF-8. -/
def escape (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    match c with
    | '"' => acc ++ "\\\""
    | '\\' => acc ++ "\\\\"
    | '\x08' => acc ++ "\\b"
    | '\t' => acc ++ "\\t"
    | '\n' => acc ++ "\\n"
    | '\x0c' => acc ++ "\\f"
    | '\r' => acc ++ "\\r"
    | c =>
      if c.toNat < 0x20 then acc ++ "\\u00" ++ (hexDigit (c.toNat / 16)).toString
        ++ (hexDigit c.toNat).toString
      else acc.push c

partial def Out.render : Out → String
  | .num n => toString n
  | .str s => "\"" ++ escape s ++ "\""
  | .arr xs => "[" ++ ",".intercalate (xs.map Out.render) ++ "]"
  | .obj kvs =>
    "{" ++ ",".intercalate (kvs.map fun (k, v) => "\"" ++ escape k ++ "\":" ++ v.render) ++ "}"

/-! ## Conversions between Lean and the extracted types -/

def bytesOf (s : Slice U8) : ByteArray := ⟨s.val.toArray.map fun b => b.bv.toNat.toUInt8⟩

def sliceOf {α} (l : List α) : Except String (Slice α) :=
  if h : l.length ≤ Usize.max then .ok (Slice.from l h) else .error "slice too long"

def strOf (s : String) : Except String Str :=
  sliceOf (s.toUTF8.toList.map fun b => (⟨b.toBitVec⟩ : U8))

def utf8 (s : Slice U8) : Except String String :=
  match String.fromUTF8? (bytesOf s) with
  | some t => .ok t
  | none => .error "testcase name is not UTF-8 (stock Display unwraps)"

/-- `format!("{:?}", v)` of a fieldless enum variant: the constructor name. -/
def debugName {α} [Repr α] (v : α) : String :=
  ((toString (repr v)).splitOn ".").getLast!

deriving instance Repr for binemit.Reloc
deriving instance Repr for ir.libcall.LibCall
deriving instance Repr for ir.known_symbol.KnownSymbol

def userName (u : ir.extname.UserExternalName) : Out :=
  .obj [("user", .arr [.num u.«namespace».val, .num u.index.val])]

/-- `TestcaseName` is its bytes (`Box<[u8]>`). -/
def testcase (t : ir.extname.TestcaseName) : Except String Out :=
  return .obj [("testcase", .str (← utf8 (show Slice U8 from t)))]

def funcName (f : ir.function.Function) : Except String Out :=
  match f.«name» with
  | .User u => .ok (userName u)
  | .Testcase t => testcase t

def relocTarget (f : ir.function.Function) :
    machinst.buffer.FinalizedRelocTarget → Except String Out
  | .Func off => .ok (.obj [("func_offset", .num off.val)])
  | .ExternalName (.User r) =>
    match f.params.user_named_funcs.elems.val[(show U32 from r).val]? with
    | some u => .ok (userName u)
    | none => .error "dangling UserExternalNameRef"
  | .ExternalName (.TestCase t) => testcase t
  | .ExternalName (.LibCall lc) => .ok (.obj [("libcall", .str (debugName lc))])
  | .ExternalName (.KnownSymbol ks) => .ok (.obj [("known_symbol", .str (debugName ks))])

/-- `TrapCode::as_raw().get()`: a `NonZero<u8>`, i.e. its `u8`. -/
def trapCodeRaw (c : ir.trapcode.TrapCode) : Nat := (show U8 from c).val

/-! ## Requests -/

/-- The triple each `TargetSpec` builds (`clifv_extract_entry::triple`), as `extract/targets.json`
spells it. The native CLI parses `target` with `target_lexicon`; the Lean driver accepts exactly
these spellings, which are the only ones `compare.py` sends. -/
def specOf : String → Except String (TargetSpec × String)
  | "Aarch64UnknownUnknown" => .ok (.Aarch64UnknownUnknown, "aarch64-unknown-unknown")
  | "Aarch64UnknownUnknownElf" => .ok (.Aarch64UnknownUnknownElf, "aarch64-unknown-unknown-elf")
  | "Aarch64UnknownLinuxGnu" => .ok (.Aarch64UnknownLinuxGnu, "aarch64-unknown-linux-gnu")
  | "Aarch64AppleDarwin" => .ok (.Aarch64AppleDarwin, "aarch64-apple-darwin")
  | s => .error s!"unknown target_spec {s}"

def settingsOf (j : Lean.Json) : Except String (Slice Setting) := do
  let xs ← j.getArr?
  sliceOf (← xs.toList.mapM fun s => do
    return { «name» := ← (← s.getObjVal? "name").getStr?,
             value := ← (← s.getObjVal? "value").getStr? })

def stage : CompileFailure → String
  | .Parse => "parse"
  | .FunctionCount => "function_count"
  | .SharedSetting => "shared_setting"
  | .IsaSetting => "isa_setting"
  | .Codegen _ => "codegen"

def run (request : Lean.Json) : IO Out := do
  let ex {α} (e : Except String α) : IO α := IO.ofExcept (e.mapError IO.userError)
  unless request.getObjValD "schema" == (1 : Nat) do throw (IO.userError "unsupported request schema")
  let target ← ex (request.getObjValAs? String "target")
  let (spec, triple) ← ex (specOf (← ex (request.getObjValAs? String "target_spec")))
  if target != triple then
    return .obj [("reason", .str "target_spec_mismatch"), ("schema", .num 1), ("status", .str "error")]
  let clif ← IO.FS.readFile (← ex (request.getObjValAs? String "clif_path"))
  let flags ← ex (settingsOf (request.getObjValD "flags"))
  let isaFlags ← ex (settingsOf (request.getObjValD "isa_flags"))
  let res := compile_aarch64 (← ex (strOf clif)) spec flags isaFlags
  match res.match with
  | .div => throw (IO.userError "extracted compile_aarch64 diverged")
  | .vis (.fail e) _ => throw (IO.userError s!"extracted compile_aarch64 failed: {repr e}")
  | .ok (.Err f) =>
    return .obj [("schema", .num 1), ("stage", .str (stage f)), ("status", .str "rejected")]
  | .ok (.Ok a) =>
    let codeHex := (bytesOf a.code.slice).foldl (init := "") fun s b =>
      (s.push (hexDigit (b.toNat / 16))).push (hexDigit b.toNat)
    let relocs ← a.relocs.val.mapM fun r => do
      return Out.obj [("addend", .num r.addend.val), ("kind", .str (debugName r.kind)),
                      ("offset", .num r.offset.val), ("target", ← ex (relocTarget a.func r.target))]
    let traps := a.traps.val.map fun t =>
      Out.obj [("code", .num (trapCodeRaw t.code)), ("offset", .num t.offset.val)]
    return .obj [("alignment", .num a.alignment.val), ("code_hex", .str codeHex),
                 ("func_name", ← ex (funcName a.func)), ("relocs", .arr relocs),
                 ("schema", .num 1), ("status", .str "compiled"), ("traps", .arr traps)]

end ClifvExtract.Driver

def main (args : List String) : IO UInt32 := do
  let [req, res] := args
    | IO.eprintln "usage: clifv-extract-lean REQUEST.json RESULT.json"; return 2
  let request ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile req))
  let out ← ClifvExtract.Driver.run request
  IO.FS.writeFile res out.render
  return 0
