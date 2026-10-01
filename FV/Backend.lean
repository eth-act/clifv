import FV.Backend.MInst
import FV.Backend.Isel
import FV.Backend.StackAlloc
import FV.Backend.Regalloc
import FV.Backend.Asm
import FV.Backend.Encode
import FV.Backend.Obj
import FV.Backend.Proof.DriverCheck
import FV.Compile.Subset
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

/-- The register allocator. `regalloc2 bin env`: the `lean-regalloc` executable `bin` with
machine environment `env` (`aarch64Env`, or `smallEnv` for stress tests). -/
inductive Allocator where
  | stack
  | regalloc2 (bin : String) (env : MachineEnv := aarch64Env)

/-- Allocate a batch of functions (one file). -/
def Allocator.run : Allocator → Array VCode → IO (Array (Except String AFunc))
  | .stack, vcs => pure (vcs.map allocate)
  | .regalloc2 bin env, vcs => allocateRegalloc2 bin env vcs

/-- `lean-regalloc`: `$LEAN_REGALLOC`, else `rust/target/release/lean-regalloc` of the
checkout that holds this executable (`.lake/build/bin/…`). -/
def defaultRegallocBin : IO String := do
  if let some p ← IO.getEnv "LEAN_REGALLOC" then return p
  let app ← IO.appPath
  let root := ((app.parent.bind (·.parent)).bind (·.parent)).bind (·.parent)
  pure ((root.getD ".") / "rust" / "target" / "release" / "lean-regalloc").toString

/-- The allocator named on the command line: `regalloc2` (Cranelift's environment), `stack`,
or `regalloc2-small` (`smallEnv`, testing only). -/
def Allocator.ofName? (n : String) : IO (Option Allocator) := do
  match n with
  | "stack" => pure (some .stack)
  | "regalloc2" => pure (some (.regalloc2 (← defaultRegallocBin)))
  | "regalloc2-small" => pure (some (.regalloc2 (← defaultRegallocBin) smallEnv))
  | _ => pure none

/-- `lowerFunction`, then (if `verify`) M7's lowering validator (`lowerCheck`, whose acceptance
the end-to-end theorem assumes, `docs/contracts/e2e.md`); a rejection is a compile error.
Functions outside the theorem (`unverifiedReason?`) are not validated (they are reported as
unverified instead). -/
def lowerChecked (f : Clif.Function) (verify : Bool) : Except String VCode := do
  let vc ← lowerFunction f
  if verify && !Proof.Driver.lowerCheck f vc then
    throw "lowering rejected by the M7 lowering validator (lowerCheck)"
  pure vc

/-- Every extern of `f` takes at most 8 parameters (`E2E.InSubset.callRegArgs`: calls pass all
their arguments in registers). -/
def regArgCalls (f : Clif.Function) : Bool := f.externs.all fun e => e.2.sig.params.length ≤ 8

/-- The signatures of `f` and of every callee are ones the end-to-end theorem covers
(`sigAbiOk`, `E2E.InSubset.abiSigs`): `normal` parameters plus at most one `sret` pointer (in
x8, returned in x0), `normal` returns. Other special-purpose parameters (`vmctx`, `sarg`) are
compiled but flagged unverified. -/
def abiSigs (f : Clif.Function) : Bool :=
  sigAbiOk f.sig && f.externs.all (sigAbiOk ·.2.sig)

/-- The theorem's conditions that do not need the rest of the file (`E2E.InSubset.subsetE`,
`E2E.InSubset.regParams`, `E2E.InSubset.callRegArgs`, `E2E.InSubset.abiSigs`,
`E2E.InSubset.indSigs`). -/
def verifiable (f : Clif.Function) : Bool :=
  Compile.functionE f && f.sig.params.length ≤ 8 && regArgCalls f && abiSigs f && indSigsOk f

/-- The lowering validator's size measure: instructions (statements and terminators) × values.
`lowerCheck` re-runs the lowering recording every statement's states (their vreg class arrays
grow with the function), its dataflow keeps a blocks × values table, and its certificate check
visits every block's entry values once and the target block's at every edge; the rest of it is
(near-)linear in the function. -/
def validationCost (f : Clif.Function) : Nat :=
  (f.blocks.length + (f.blocks.map (·.body.length)).sum) * f.freshValue

/-- The validation budget (`docs/USAGE.md`): a function inside the theorem's scope whose
`validationCost` exceeds it is compiled but not validated (`lowerCheck` does not run), and
reported unverified ("validation budget"). It bounds the validator's time and memory on
pathological inputs (at the budget: about 1.5 s and under 1 GB); it is far above every function
of `examples/` (the largest costs 3276540: a survey test function with 188 blocks, 1992
statements and 1503 values; the validator takes about 0.2 s on functions of that size). -/
def validationBudget : Nat := 25000000

/-- The reason `f` is not validated although inside the theorem's scope: over the validation
budget. -/
def overBudget? (f : Clif.Function) : Option String :=
  let c := validationCost f
  if c > validationBudget then
    some s!"{c} instructions × values > {validationBudget}, lowerCheck not run"
  else none

/-- Compile one function with the stack-slot allocator (`k` = index in the file, for local
labels); also returns the ISLE rules that fired. -/
def compileFunction (k : Nat) (f : Clif.Function) : Except String (FnAsm × Array Isle.RuleId) := do
  let vc ← lowerChecked f (verifiable f)
  let af ← allocate vc
  pure (← emitFunc k af, vc.rulesFired)

/-- Compile one function with the given allocator. -/
def compileFunctionWith (a : Allocator) (k : Nat) (f : Clif.Function) :
    IO (Except String (FnAsm × Array Isle.RuleId)) := do
  match lowerChecked f (verifiable f) with
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
  /-- Compiled functions outside the end-to-end theorem (`unverifiedReason?`), with the reason. -/
  unverified : List (String × String) := []
  /-- Compiled functions inside the theorem's scope that were not validated because they are
  over the validation budget (`overBudget?`), with the reason. -/
  unvalidated : List (String × String) := []
  /-- Distinct ISLE rules fired while compiling the file (ascending ids). -/
  rules : List Isle.RuleId
  /-- Unwind rows of each compiled function (`unwindRows`, unverified; for `.eh_frame`). -/
  unwind : List (String × List (Nat × Cfi)) := []
  /-- Call-site tables of the compiled functions with landing pads (`callSites`, unverified;
  for the LSDA). -/
  lsda : List (String × List CallSite) := []

/-- Names of the functions `f` calls (`call`, `try_call`). -/
def callees (f : Clif.Function) : List String :=
  (f.blocks.flatMap fun b => (b.body.filterMap fun s => match s.inst with
    | .call fn _ => (f.extern? fn).map (·.name)
    | _ => none) ++ match b.term with
    | .tryCall fn _ _ => ((f.extern? fn).map (·.name)).toList
    | _ => []).eraseDups

/-- Does `f` have a `try_call`/`try_call_indirect` (landing pads)? -/
def hasTryCall (f : Clif.Function) : Bool :=
  f.blocks.any (·.term.isTry)

/-- `tls_value` in `f` (Cranelift's `elf_gd` TLSDESC sequence; outside clif-subset-v2 E). -/
def hasTls (f : Clif.Function) : Bool :=
  f.blocks.any fun b => b.body.any fun st => match st.inst with
    | .tlsValue .. => true
    | _ => false

/-- Why a compiled function of `pf` is outside `E2E.backend_correct` (`E2E.InSubset`), if it is:
`tls_value`, outside clif-subset-v2 E, stack-passed parameters, stack-passed call arguments
(an extern or an indirect call with more than 8 parameters), special-purpose parameters, or a
call (also a `try_call`) of a function of the file. A `try_call`/`try_call_indirect` of an
extern is inside the theorem for its normal return (`hasTryCall`: the landing pads and the LSDA
are trusted); `call_indirect`, `try_call_indirect` and `func_addr` are inside it (an indirect
call of a function of the file is excluded by the theorem's run premise
`TrapsExplicit.indirect`); so are `bmask`, the atomics and `fence` (single-threaded semantics;
the Arm model's exclusive store always succeeds, `docs/decisions/arm-model.md`). -/
def unverifiedReason? (pf : Clif.ParsedFile) (f : Clif.Function) : Option String :=
  if hasTls f then some "tls_value (outside backend_correct)"
  else if !Compile.functionE f then some "outside clif-subset-v2 E"
  else if f.sig.params.length > 8 then some "stack-passed parameters (more than 8)"
  else if !regArgCalls f then some "stack-passed call arguments (an extern with more than 8 parameters)"
  else if !abiSigs f then some "special-purpose parameter other than one sret pointer (outside backend_correct)"
  else if !indSigsOk f then
    some "indirect call with stack-passed arguments or a special-purpose parameter (outside backend_correct)"
  else
    let own := pf.funcs.map (·.name)
    match (callees f).find? (own.contains ·) with
    | some c => some s!"calls %{c}, a function of the file"
    | none => none

/-- Compile every function of a parsed `.clif` file: lower each function, allocate all of
them with `alloc` (one batch), emit. A function that calls a function of the file that is not
compiled is not compiled either (its object code would reference an undefined symbol).
`preUnverified` marks functions already known to be outside the theorem before this check
(`Opt.Legalize128.parsedFile128`: legalised `i128` functions the validator `Opt.Legal.check`
rejects, "i128 legalized (outside backend_correct: …)"); they are not lowering-validated. -/
def compileFileWith {m : Type → Type} [Monad m]
    (alloc : Array VCode → m (Array (Except String AFunc))) (pf : Clif.ParsedFile)
    (preUnverified : List (String × String) := []) : m FileAsm := do
  -- lowering (per function, in file order)
  let lowered : Array (String × Except String (Clif.Function × VCode)) :=
    pf.funcs.toArray.map fun p => (p.name, match p.func with
      | .error e => .error e.toString
      | .ok f => (lowerChecked f
          ((unverifiedReason? pf f).isSome || (preUnverified.lookup p.name).isSome ||
            (overBudget? f).isSome).not
          ).map (f, ·))
  let vcs := lowered.filterMap fun (_, r) => r.toOption.map (·.2)
  let afs ← alloc vcs
  let mut done : Array (FnAsm × List String) := #[]
  let mut bad : Array (String × String) := #[]
  let mut unwind : Array (String × List (Nat × Cfi)) := #[]
  let mut lsda : Array (String × List CallSite) := #[]
  let mut rules : Std.HashSet Isle.RuleId := {}
  let mut j := 0
  for ((name, r), k) in lowered.zipIdx do
    match r with
    | .error e => bad := bad.push (name, e)
    | .ok (f, vc) =>
      let af := afs[j]?.getD (.error "allocator returned too few results")
      j := j + 1
      match af.bind fun af => do
          let a ← emitFunc k af
          pure (a, ← unwindRows af a, ← callSites af a) with
      | .ok (a, rows, sites) =>
        done := done.push (a, callees f)
        unwind := unwind.push (a.name, rows)
        if let some s := sites then lsda := lsda.push (a.name, s)
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
  let unverified := lowered.toList.filterMap fun (name, r) => match r with
    | .ok (f, _) => if funcs.any (·.name == name) then
        ((preUnverified.lookup name).orElse (fun _ => unverifiedReason? pf f)).map (name, ·)
      else none
    | .error _ => none
  let unvalidated := lowered.toList.filterMap fun (name, r) => match r with
    | .ok (f, _) =>
      if funcs.any (·.name == name) && !unverified.any (·.1 == name) then
        (overBudget? f).map (name, ·)
      else none
    | .error _ => none
  pure { text, funcs, unsupported := bad.toList, unverified, unvalidated,
         rules := rules.toArray.qsort (· < ·) |>.toList,
         unwind := unwind.toList.filter fun (n, _) => funcs.any (·.name == n),
         lsda := lsda.toList.filter fun (n, _) => funcs.any (·.name == n) }

/-- `compileFileWith` the stack-slot allocator (pure). -/
def compileFile (pf : Clif.ParsedFile) : FileAsm :=
  Id.run (compileFileWith (fun vcs => pure (vcs.map allocate)) pf)

/-- `compileFileWith` the given allocator. -/
def compileFileIO (a : Allocator) (pf : Clif.ParsedFile)
    (preUnverified : List (String × String) := []) : IO FileAsm :=
  compileFileWith a.run pf preUnverified

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

/-- The ELF relocatable object of the compiled functions (no assembler), with `.eh_frame`,
and with a `personality` the LSDAs of the functions with landing pads. -/
def FileAsm.object (fa : FileAsm) (personality : Option String := none) :
    Except String ByteArray :=
  (elfObject · fa.unwind fa.lsda personality) <$> fa.layout

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
