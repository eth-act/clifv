import FV.Backend.MInst
import FV.Backend.Isel
import FV.Backend.StackAlloc
import FV.Backend.Asm
import FV.Backend.Encode
import FV.Backend.Obj
import Std.Data.HashSet

/-!
# The Lean AArch64 backend (M4/M5, unproven): CLIF → machine code

`Backend.compileFunction f` = `emitFunc ∘ allocate ∘ lowerFunction`: ISLE instruction
selection (`Isel`), stack-slot allocation and frame layout (`StackAlloc`), the final
instruction list (`Asm`). `Backend.compileFile` does this for every function of a `.clif` file
and reports the functions it does not support (outside `clif-subset-v1` E, or not parsed by
`Clif.parseFile`). The result is printed as assembly (`FileAsm.text`) or encoded and laid out
(`Encode`) into an ELF relocatable object (`FileAsm.object`, `Obj`).
Contracts: `docs/contracts/backend.md`, `docs/contracts/encoder.md`.
-/

namespace Backend

/-- Compile one function (`k` = index in the file, for local labels); also returns the ISLE
rules that fired. -/
def compileFunction (k : Nat) (f : Clif.Function) : Except String (FnAsm × Array Isle.RuleId) := do
  let vc ← lowerFunction f
  let af ← allocate vc
  pure (← emitFunc k af, vc.rulesFired)

/-- Result of compiling a file. -/
structure FileAsm where
  /-- Assembly text of all compiled functions. -/
  text : String
  funcs : List FnAsm
  /-- Functions not compiled, with the reason. -/
  unsupported : List (String × String)
  /-- Distinct ISLE rules fired while compiling the file (ascending ids). -/
  rules : List Isle.RuleId

/-- Names of the functions `f` calls. -/
def callees (f : Clif.Function) : List String :=
  (f.blocks.flatMap fun b => b.body.filterMap fun s => match s.inst with
    | .call fn _ => (f.extern? fn).map (·.name)
    | _ => none).eraseDups

/-- Compile every function of a parsed `.clif` file. A function that calls a function of the
file that is not compiled is not compiled either (its object code would reference an
undefined symbol). -/
def compileFile (pf : Clif.ParsedFile) : FileAsm := Id.run do
  let mut done : Array (FnAsm × List String) := #[]
  let mut bad : Array (String × String) := #[]
  let mut rules : Std.HashSet Isle.RuleId := {}
  for (p, k) in pf.funcs.zipIdx do
    match p.func with
    | .error e => bad := bad.push (p.name, e.toString)
    | .ok f =>
      match compileFunction k f with
      | .ok (a, rs) =>
        done := done.push (a, callees f)
        rules := rs.foldl (·.insert ·) rules
      | .error e => bad := bad.push (p.name, e)
  -- propagate to callers (fixpoint; at most one round per function)
  for _ in [0:done.size] do
    let (keep, drop) := done.partition fun (_, cs) => cs.all fun c => (bad.find? (·.1 == c)).isNone
    if drop.isEmpty then break
    for (a, cs) in drop do
      let c := (cs.find? fun c => (bad.find? (·.1 == c)).isSome).getD "?"
      bad := bad.push (a.name, s!"calls %{c}, which is not compiled")
    done := keep
  let funcs := done.toList.map (·.1)
  let text := "  .text\n" ++ String.join (funcs.map (·.text ++ "\n"))
  pure { text, funcs, unsupported := bad.toList,
         rules := rules.toArray.qsort (· < ·) |>.toList }

def jsonString (s : String) : String :=
  "\"" ++ String.join (s.toList.map fun c =>
    if c == '"' then "\\\"" else if c == '\\' then "\\\\"
    else if c == '\n' then "\\n" else if c.toNat < 0x20 then " " else c.toString) ++ "\""

/-- The trap/function table for `clif-native --functions-obj` (schema in
`docs/contracts/drivers.md`). -/
def FileAsm.tableJson (fa : FileAsm) : String :=
  let fn (f : FnAsm) : String :=
    let traps := ", ".intercalate (f.traps.map fun t =>
      s!"\{\"offset\": {t.offset}, \"code\": {jsonString t.code.name}}")
    s!"  \{\"name\": {jsonString f.name}, \"size\": {f.size}, \"traps\": [{traps}]}"
  let bad (p : String × String) : String :=
    s!"  \{\"name\": {jsonString p.1}, \"reason\": {jsonString p.2}}"
  "{\"functions\": [\n" ++ ",\n".intercalate (fa.funcs.map fn) ++ "\n],\n\"unsupported\": [\n" ++
    ",\n".intercalate (fa.unsupported.map bad) ++ "\n]}\n"

/-- Encode and lay out every compiled function (an error is an encoder or backend bug). -/
def FileAsm.layout (fa : FileAsm) : Except String (List (FnAsm × FnBin)) :=
  fa.funcs.mapM fun f => do pure (f, ← f.layout)

/-- The ELF relocatable object of the compiled functions (no assembler). -/
def FileAsm.object (fa : FileAsm) : Except String ByteArray :=
  elfObject <$> fa.layout

/-- `name.relocs.json` of a laid-out function (the `clif2obj` schema,
`docs/contracts/drivers.md`). -/
def FnBin.relocsJson (f : FnBin) : String :=
  "[" ++ ",\n ".intercalate (f.relocs.map fun r =>
    s!"\{\"offset\": {r.offset}, \"kind\": {jsonString r.type.craneliftName}, " ++
    s!"\"target\": {jsonString r.sym}, \"addend\": {r.addend}}") ++ "]\n"

/-- `name.traps.json` of a laid-out function (the `clif2obj` schema). -/
def FnBin.trapsJson (f : FnBin) : String :=
  "[" ++ ", ".intercalate (f.traps.map fun t =>
    s!"\{\"offset\": {t.offset}, \"code\": {jsonString t.code.name}}") ++ "]\n"

end Backend
