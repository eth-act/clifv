import FV.Backend
import FV.Backend.Proof.EncodeBranch

/-!
# Branch-range tests (`lake exe lean-backend-encode-test range`)

The branch-range policy (`Env.pcRel`, `docs/contracts/encoder.md`): a label operand beyond
its form's reach is a compile error, never a truncated word (proved:
`Insn.encode_error_of_out_of_range`); `emitFunc` relaxes the conditional branches to block and
trap labels that would be out of range (`relaxLine`, `relaxOf`). Checked here at four levels:

1. **Encoder**, every label-relative form (b, b.cond, cbz/cbnz, tbz/tbnz, adr): the extreme
   in-range offsets (`reach - align`, `-reach`) encode, decode and resolve to the offset; one
   step beyond (`reach`, `-reach - align`) and a misaligned offset are errors.
2. **Layout**, large functions of filler instructions: forward `tbz` (±32 KiB), backward
   `b.cond` and forward `cbz` (±1 MiB), each at the last fitting size and one instruction more.
3. **Relaxation**, the same line lists through `relaxLines (relaxOf ·)`: the fitting ones are
   unchanged, the others become `b.!c .+8; b T` and lay out.
4. **Whole backend** (stack-slot allocator), a generated CLIF function whose `brif` becomes a
   `tbz`/`tbnz` over > 32 KiB of code: it is relaxed and lays out; a small one is not relaxed.
-/

namespace Backend.RangeTest

open Backend Arm

def hasSub (s pat : String) : Bool := (s.splitOn pat).length > 1

structure Res where
  pass : Nat := 0
  fail : Nat := 0

abbrev M := StateT Res IO

def check (ok : Bool) (what : String) : M Unit :=
  if ok then modify fun r => { r with pass := r.pass + 1 }
  else do
    IO.println s!"FAIL: {what}"
    modify fun r => { r with fail := r.fail + 1 }

def forms : List (String × Insn) :=
  [("b", .b (.block 0)), ("b.ne", .bcond .ne (.block 0)), ("cbz x", .cbz false true (.x 3) (.block 0)),
   ("cbnz w", .cbz true false (.x 3) (.block 0)), ("tbz #5", .tbz false (.x 3) 5 (.block 0)),
   ("tbnz #40", .tbz true (.x 3) 40 (.block 0)), ("adr", .adr (.x 3) (.block 0))]

/-- The instruction at `pc = 2^28` with its target at `pc + d`. -/
def encodeAt (i : Insn) (d : Int) : Except String (BitVec 32) × Option ArmInst :=
  let pc := 2 ^ 28
  let env : Env := { pc, lbl := fun _ => some (pc + d).toNat }
  (i.encode env, (i.toArmInst env).toOption)

def encoderLevel : M Unit := do
  for (name, i) in forms do
    let some (_, reach, align) := i.pcRelSpec? | check false s!"{name}: no pcRelSpec"
    for d in [reach - align, -reach, 0, align, -align] do
      match encodeAt i d with
      | (.ok w, some a) =>
        check (decode_raw_inst w == some a) s!"{name} {d}: decode"
        check (a.pcRelOffset? == some d) s!"{name} {d}: offset {a.pcRelOffset?}"
      | (.error _, _) | (_, none) => check false s!"{name} {d}: rejected"
    for d in [reach, -reach - align, reach + 4096, -reach - 4096] do
      match encodeAt i d with
      | (.error e, _) => check (hasSub e "branch out of range") s!"{name} {d}: message {e}"
      | (.ok _, _) => check false s!"{name} {d}: out of range but encoded"
    if align == 4 then
      match encodeAt i 2 with
      | (.error e, _) => check (hasSub e "not a multiple of 4") s!"{name} 2: message {e}"
      | (.ok _, _) => check false s!"{name} 2: misaligned but encoded"

def filler : Line := .ins (.aluRRR .add true (.x 1) (.x 1) (.x 0))

def mkFn (name : String) (lines : Array Line) : FnAsm :=
  { name, k := 0, lines, size := lines.foldl (fun s l => s + l.size) 0, traps := [] }

/-- `br` at line index `at` must resolve to byte offset `d` (fits) or be rejected (does not). -/
def layoutCase (name : String) (f : FnAsm) (brPc : Nat) (d : Int) (fits : Bool) : M Unit := do
  match f.layout with
  | .ok fb =>
    if !fits then check false s!"{name}: out of range but laid out" else
    let some (_, i) := fb.insns.find? (·.1 == brPc) | check false s!"{name}: no branch"
    let w := fb.words[brPc / 4]!
    match decode_raw_inst w with
    | some a => check (a.pcRelOffset? == some d) s!"{name}: offset {a.pcRelOffset?} ≠ {d} ({i.asm 0})"
    | none => check false s!"{name}: undecodable"
  | .error e =>
    if fits then check false s!"{name}: {e}"
    else check (hasSub e "branch out of range" && hasSub e s!"{f.name}+{brPc}") s!"{name}: message {e}"

/-- `relaxOf` on a case: unchanged if it fits, else the branch at line `j` is relaxed and the
function lays out. -/
def relaxCase (name : String) (lines : Array Line) (j : Nat) (fits : Bool) : M Unit := do
  let pre := lines.toList
  let out := relaxLines (relaxOf pre) pre
  if fits then check (out.length == pre.length) s!"{name}: relaxed although it fits"
  else
    check (out.length == pre.length + 1) s!"{name}: not relaxed ({out.length} lines)"
    match out[j]?, out[j + 1]? with
    | some (.ins i none), some (.ins (.b _) none) =>
      check (i.condTarget? == some .skip) s!"{name}: relaxed branch {i.asm 0}"
    | _, _ => check false s!"{name}: relaxed lines"
  match (mkFn name out.toArray).layout with
  | .ok _ => check true name
  | .error e => check false s!"{name} relaxed: {e}"

def layoutLevel : M Unit := do
  -- forward tbz over n fillers: offset 4 (n + 1); reach 32 KiB
  for (n, fits) in [(8190, true), (8191, false)] do
    let lines := #[.ins (.tbz false (.x 0) 3 (.block 1))] ++ Array.replicate n filler ++
      #[.label (.block 1), .ins .ret]
    layoutCase s!"tbz over {n}" (mkFn "big_tbz" lines) 0 (4 * (n + 1)) fits
    relaxCase s!"relaxed tbz over {n}" lines 0 fits
  -- backward b.cond over n fillers: offset -4 n; reach 1 MiB
  for (n, fits) in [(262144, true), (262145, false)] do
    let lines := #[.label (.block 1)] ++ Array.replicate n filler ++
      #[.ins (.bcond .eq (.block 1)), .ins .ret]
    layoutCase s!"b.eq back over {n}" (mkFn "big_bcond" lines) (4 * n) (-4 * n) fits
    relaxCase s!"relaxed b.eq back over {n}" lines (n + 1) fits
  -- forward cbz over n fillers: offset 4 (n + 1)
  for (n, fits) in [(262142, true), (262143, false)] do
    let lines := #[.ins (.cbz false true (.x 0) (.block 1))] ++ Array.replicate n filler ++
      #[.label (.block 1), .ins .ret]
    layoutCase s!"cbz over {n}" (mkFn "big_cbz" lines) 0 (4 * (n + 1)) fits
    relaxCase s!"relaxed cbz over {n}" lines 0 fits

/-- `brif (band v0, 4), block1, block2` where both successors are `n` chained `iadd`s: whichever
block is placed second, the `tbz`/`tbnz x, #2` to it crosses the first. -/
def clifFn (name : String) (n : Nat) : String := Id.run do
  let mut s := "\n".intercalate
    [s!"function %{name}(i64) -> i64 " ++ "{", "block0(v0: i64):", "    v1 = iconst.i64 4",
     "    v2 = band v0, v1", "    brif v2, block1, block2", ""]
  let mut v := 10
  for b in [1, 2] do
    s := s ++ s!"block{b}:\n"
    let mut prev := "v0"
    for _ in [0:n] do
      s := s ++ s!"    v{v} = iadd {prev}, v0\n"
      prev := s!"v{v}"
      v := v + 1
    s := s ++ s!"    return {prev}\n"
  s ++ "}\n"

def backendLevel : M Unit := do
  for (name, n, fits) in [("small_fn", 100, true), ("big_fn", 3000, false)] do
    let fa := compileFile (Clif.parseFile (clifFn name n))
    check (fa.unsupported.isEmpty && fa.funcs.length == 1) s!"{name}: not compiled"
    check (hasSub fa.text "  tbz x" || hasSub fa.text "  tbnz x") s!"{name}: no tbz in the output"
    check (hasSub fa.text ", .+8" != fits) s!"{name}: relaxed = {hasSub fa.text ", .+8"}"
    match fa.layout with
    | .ok _ => check true name
    | .error e => check false s!"{name}: {e}"

def rangeMain : IO UInt32 := do
  let ((), r) ← (do encoderLevel; layoutLevel; backendLevel : M Unit).run {}
  IO.println s!"range: {r.pass} checks passed, {r.fail} failed"
  return if r.fail == 0 then 0 else 1

end Backend.RangeTest
