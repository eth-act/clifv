import FV.Backend.MInst
import FV.Backend.Isel
import FV.Backend.StackAlloc
import FV.Backend.Regalloc
import FV.Backend.Asm
import FV.Backend.Encode
import FV.Backend.Obj
import Std.Data.HashSet

/-!
# The Lean AArch64 backend (M4–M6, unproven): CLIF → machine code

`Backend.compileFileWith alloc` = `emitFunc ∘ alloc ∘ lowerFunction` per function: ISLE
instruction selection (`Isel`), register allocation and frame layout — regalloc2 run as an
untrusted oracle and validated by the Lean checker (`Regalloc`, `RegallocCheck`; the
default), or the stack-slot allocator (`StackAlloc`, the baseline) —, and the final
instruction list (`Asm`). It compiles every function of a `.clif` file and reports the
functions it does not support (outside `clif-subset-v1` E, or not parsed by
`Clif.parseFile`). The result is printed as assembly (`FileAsm.text`) or encoded and laid out
(`Encode`) into an ELF relocatable object (`FileAsm.object`, `Obj`).
Contracts: `docs/contracts/backend.md`, `docs/contracts/regalloc.md`,
`docs/contracts/encoder.md`.
-/

namespace Backend

/-- The register allocator. `regalloc2 bin`: the `lean-regalloc` executable `bin`. -/
inductive Allocator where
  | stack
  | regalloc2 (bin : String)

/-- Allocate a batch of functions (one file). -/
def Allocator.run : Allocator → Array VCode → IO (Array (Except String AFunc))
  | .stack, vcs => pure (vcs.map allocate)
  | .regalloc2 bin, vcs => allocateRegalloc2 bin vcs

/-- `lean-regalloc`: `$LEAN_REGALLOC`, else `rust/target/release/lean-regalloc` of the
checkout that holds this executable (`.lake/build/bin/…`). -/
def defaultRegallocBin : IO String := do
  if let some p ← IO.getEnv "LEAN_REGALLOC" then return p
  let app ← IO.appPath
  let root := ((app.parent.bind (·.parent)).bind (·.parent)).bind (·.parent)
  pure ((root.getD ".") / "rust" / "target" / "release" / "lean-regalloc").toString

/-- Compile one function with the stack-slot allocator (`k` = index in the file, for local
labels); also returns the ISLE rules that fired. -/
def compileFunction (k : Nat) (f : Clif.Function) : Except String (FnAsm × Array Isle.RuleId) := do
  let vc ← lowerFunction f
  let af ← allocate vc
  pure (← emitFunc k af, vc.rulesFired)

/-- Compile one function with the given allocator. -/
def compileFunctionWith (a : Allocator) (k : Nat) (f : Clif.Function) :
    IO (Except String (FnAsm × Array Isle.RuleId)) := do
  match lowerFunction f with
  | .error e => pure (.error e)
  | .ok vc =>
    let rs ← a.run #[vc]
    pure do
      let af ← rs[0]!
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

/-- Compile every function of a parsed `.clif` file: lower each function, allocate all of
them with `alloc` (one batch), emit. A function that calls a function of the file that is not
compiled is not compiled either (its object code would reference an undefined symbol). -/
def compileFileWith {m : Type → Type} [Monad m]
    (alloc : Array VCode → m (Array (Except String AFunc))) (pf : Clif.ParsedFile) : m FileAsm := do
  -- lowering (per function, in file order)
  let lowered : Array (String × Except String (Clif.Function × VCode)) :=
    pf.funcs.toArray.map fun p => (p.name, match p.func with
      | .error e => .error e.toString
      | .ok f => (lowerFunction f).map (f, ·))
  let vcs := lowered.filterMap fun (_, r) => r.toOption.map (·.2)
  let afs ← alloc vcs
  let mut done : Array (FnAsm × List String) := #[]
  let mut bad : Array (String × String) := #[]
  let mut rules : Std.HashSet Isle.RuleId := {}
  let mut j := 0
  for ((name, r), k) in lowered.zipIdx do
    match r with
    | .error e => bad := bad.push (name, e)
    | .ok (f, vc) =>
      let af := afs[j]?.getD (.error "allocator returned too few results")
      j := j + 1
      match af.bind (emitFunc k) with
      | .ok a =>
        done := done.push (a, callees f)
        rules := vc.rulesFired.foldl (·.insert ·) rules
      | .error e => bad := bad.push (name, e)
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

/-- `compileFileWith` the stack-slot allocator (pure). -/
def compileFile (pf : Clif.ParsedFile) : FileAsm :=
  Id.run (compileFileWith (fun vcs => pure (vcs.map allocate)) pf)

/-- `compileFileWith` the given allocator. -/
def compileFileIO (a : Allocator) (pf : Clif.ParsedFile) : IO FileAsm :=
  compileFileWith a.run pf

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
