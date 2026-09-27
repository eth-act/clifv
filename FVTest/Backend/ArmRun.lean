import FV.Backend
import FV.Arm

/-!
# Running Lean-backend code on the Lean Arm model (seed of M7's execution relation)

`lake exe lean-backend-armrun [--regalloc regalloc2|stack|regalloc2-small] [--bins DIR] [FILE.clif...]`
(default: every `corpus/clif/*.clif`, regalloc2). For every function of the files that makes no
calls, no memory accesses (other than its own frame) and no `symbol_value`, and has `; run:`
commands:

1. compile it alone with the Lean backend (`Backend.compileFunctionWith`, the chosen
   allocator); with `--bins DIR`, take Cranelift's code for it instead (`DIR/NAME.bin`, as
   `clif2obj` dumps it) to measure Cranelift on the same model;
2. encode it with the Lean encoder (`FnAsm.layout`, no assembler; the code has no
   relocations: branches and jump tables are PC-relative within the function);
3. load the words at `codeBase` into an `Arm.ArmState` (`set_program`), set `pc`, the
   argument registers (and stack arguments, `Backend.argLocs`), `sp`, distinct values in the
   callee-saved registers x19–x28, and a sentinel return address in `x30`; step the model
   until the `ret` reaches the sentinel, counting executed instructions;
4. compare the return registers `x0..` (truncated to the return types) with `Clif.run` on the
   same function and arguments; a CLIF trap must be a `udf` trap in the model at a trap site of
   the backend's trap table with the same code (any `udf` for `--bins`). A return must also
   leave `sp` and x19–x28 as they were (AAPCS64 callee-saved registers).

Output: one line per function (code size, runs agreeing, executed instructions summed over its
runs), then totals; exit status 0 iff every run agrees.
-/

open Backend Arm

def codeBase : Nat := 0x10000
def stackTop : Nat := 0x7fff0000
def sentinel : Nat := 0xdead0000

/-- Is `f` free of calls, of memory accesses and of `symbol_value` (GOT relocations, which
need a linker the model does not have)? -/
def selfContained (f : Clif.Function) : Bool :=
  f.blocks.all fun b => b.body.all fun s => match s.inst with
    | .call .. | .load .. | .store .. | .symbolValue .. => false
    | _ => true

/-- The value the callee-saved register `x{19 + i}` holds at the call. -/
def calleeSavedInit (i : Nat) : Nat := 0x5a5a000000000000 + 0x1111 * (19 + i)

/-- Initial model state for a call of the code with `args`. -/
def initState (code : Array (BitVec 32)) (args : List Clif.Val) : ArmState := Id.run do
  let prog : Program := def_program <|
    (code.toList.zipIdx).map fun (w, i) => (BitVec.ofNat 64 (codeBase + 4 * i), w)
  let mut s := set_program ArmState.default prog
  -- The model keeps code (`program`) apart from data (`mem`); the process image also has the
  -- code bytes in memory, which jump tables (`ldrsw` from the `.word` table) read.
  for (word, i) in code.toList.zipIdx do
    for k in [0:4] do
      s := write_mem (BitVec.ofNat 64 (codeBase + 4 * i + k)) (BitVec.ofNat 8 (word.toNat / 2 ^ (8 * k))) s
  let (locs, stackBytes) := argLocs (args.map (·.ty.bytes))
  let sp := stackTop - stackBytes
  for (a, loc) in args.zip locs do
    match loc with
    | .reg (.x n) => s := w (.GPR (BitVec.ofNat 5 n)) (BitVec.ofNat 64 a.toNat) s
    | .stack off =>
      for k in [0:a.ty.bytes] do
        s := write_mem (BitVec.ofNat 64 (sp + off + k)) (BitVec.ofNat 8 (a.toNat / 2 ^ (8 * k))) s
    | _ => pure ()
  for i in [0:10] do
    s := w (.GPR (BitVec.ofNat 5 (19 + i))) (BitVec.ofNat 64 (calleeSavedInit i)) s
  s := w (.GPR 31#5) (BitVec.ofNat 64 sp) s
  s := w (.GPR 30#5) (BitVec.ofNat 64 sentinel) s
  s := w .PC (BitVec.ofNat 64 codeBase) s
  return s

/-- Outcome of the model run, in `Clif.Outcome` terms, with the number of executed instructions. -/
inductive ArmOutcome where
  | returned (regs : List (BitVec 64)) (steps : Nat)
  | trapped (offset : Nat) (steps : Nat)
  | other (msg : String)

/-- Step until the state has an error (or fuel runs out); counts the steps taken. -/
def runCount : Nat → ArmState → Nat → ArmState × Nat
  | 0, s, k => (s, k)
  | n + 1, s, k => match read_err s with
    | .None => runCount n (stepi s) (k + 1)
    | _ => (s, k)

def armRun (code : Array (BitVec 32)) (args : List Clif.Val) (nrets : Nat) : ArmOutcome :=
  let s0 := initState code args
  let (s, k) := runCount 2000000 s0 0
  let pc := (read_pc s).toNat
  match read_err s with
  | .Trap _ => .trapped (pc - codeBase) k
  | .NotFound _ =>
    if pc != sentinel then .other s!"no instruction at pc {pc}"
    else if r (.GPR 31#5) s != r (.GPR 31#5) s0 then .other "sp not restored"
    else match (List.range 10).find? fun i =>
        (r (.GPR (BitVec.ofNat 5 (19 + i))) s).toNat != calleeSavedInit i with
      | some i => .other s!"callee-saved x{19 + i} not preserved"
      | none =>
        -- the last step is the failed fetch at the sentinel
        .returned ((List.range nrets).map fun i => r (.GPR (BitVec.ofNat 5 i)) s) (k - 1)
  | .None => .other "out of fuel"
  | e => .other s!"model error {repr e} at pc {pc}"

structure Tally where
  agree : Nat := 0
  disagree : Nat := 0
  funcs : Nat := 0
  /-- Functions the backend does not compile (outside E). -/
  skipped : Nat := 0
  /-- Executed instructions over all agreeing runs. -/
  steps : Nat := 0

/-- The code to run: compiled by the Lean backend, or Cranelift's from `bins`. -/
inductive Source where
  | lean (a : Allocator)
  | bins (dir : String)

/-- Code words and trap table (`none`: any `udf` is accepted as a trap). -/
def codeOf (src : Source) (f : Clif.Function) :
    IO (Except String (Array (BitVec 32) × Option (List TrapSite))) := do
  match src with
  | .lean a =>
    match ← compileFunctionWith a 0 f with
    | .error e => pure (.error e)
    | .ok (asm, _) => match asm.layout with
      | .ok fb => pure (.ok (fb.words, some asm.traps))
      | .error e => throw (IO.userError s!"%{f.name}: encoding failed: {e}")
  | .bins dir =>
    let path := System.FilePath.mk dir / s!"{f.name}.bin"
    if !(← path.pathExists) then return .error s!"no {path}"
    let bytes ← IO.FS.readBinFile path
    let words := (Array.range (bytes.size / 4)).map fun i =>
      BitVec.ofNat 32 ((List.range 4).foldl (fun acc j => acc + bytes[4 * i + j]!.toNat * 2 ^ (8 * j)) 0)
    pure (.ok (words, none))

def checkFunction (src : Source) (p : Clif.Program) (f : Clif.Function) (t : Tally) :
    IO Tally := do
  let (code, traps) ← match ← codeOf src f with
    | .ok r => pure r
    | .error e => do
      IO.println s!"%{f.name}: not compiled ({e})"
      return { t with skipped := t.skipped + 1 }
  let mut t := { t with funcs := t.funcs + 1 }
  let mut agree := 0
  let mut steps := 0
  for rc in f.runs do
    if rc.func != f.name then continue
    let expected := Clif.run Clif.Env.empty p f.name rc.args 1000000
    let got := armRun code rc.args f.sig.returns.length
    let ok := match expected, got with
      | .returned vals _, .returned regs _ =>
        vals.length == regs.length &&
          (vals.zip regs).all fun (v, x) => v.toNat == x.toNat % 2 ^ v.ty.width
      | .trapped code, .trapped off _ => match traps with
        | some ts => ts.any fun ts => ts.offset == off && ts.code == code
        | none => true
      | _, _ => false
    if ok then
      agree := agree + 1
      steps := steps + match got with
        | .returned _ k | .trapped _ k => k
        | .other _ => 0
    else
      let exp := match expected with
        | .returned vals _ => s!"returned {vals.map fun (v : Clif.Val) => v.toNat}"
        | .trapped c => s!"trapped {c.name}" | .stuck m => s!"stuck {m}" | .outOfFuel => "out of fuel"
      let gotS := match got with
        | .returned regs _ => s!"returned {regs.map fun (x : BitVec 64) => x.toNat}"
        | .trapped off _ => s!"udf at +{off}" | .other m => m
      IO.println s!"  MISMATCH %{f.name}{rc.args.map (·.toNat)}: Clif.run {exp}, Arm model {gotS}"
      t := { t with disagree := t.disagree + 1 }
  IO.println s!"%{f.name}: {code.size} instructions, {agree} runs agree, {steps} executed"
  pure { t with agree := t.agree + agree, steps := t.steps + steps }

def main (args : List String) : IO UInt32 := do
  let rec opts (src : Source) : List String → IO (Source × List String)
    | "--regalloc" :: a :: rest => do
      match ← Allocator.ofName? a with
      | some al => opts (.lean al) rest
      | none => throw (IO.userError s!"unknown allocator {a}")
    | "--bins" :: d :: rest => opts (.bins d) rest
    | rest => pure (src, rest)
  let (src, args) ← opts (.lean (.regalloc2 (← defaultRegallocBin))) args
  let files ← if args.isEmpty then do
      let entries ← System.FilePath.readDir "corpus/clif"
      pure ((entries.filter (·.path.extension == some "clif")).map (·.path.toString)
        |>.qsort (· < ·) |>.toList)
    else pure args
  let mut t : Tally := {}
  for file in files do
    let pf := Clif.parseFile (← IO.FS.readFile file)
    let fs := pf.funcs.filterMap fun pfn => pfn.func.toOption
    let p : Clif.Program := { header := pf.header, funcs := fs }
    for f in fs do
      if selfContained f && f.runs.any (·.func == f.name) then
        t ← checkFunction src p f t
  IO.println s!"functions {t.funcs} (not compiled {t.skipped}), runs agree {t.agree}, disagree {t.disagree}, executed {t.steps}"
  return if t.disagree == 0 && t.funcs > 0 then 0 else 1
