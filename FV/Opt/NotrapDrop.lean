import FV.Opt.Dce
import FV.Opt.ConstPhiSelect

/-! # Unused `notrap` loads (option D prototype, #1017; not proved yet)

Cranelift 0.136.1 does not lower an instruction none of whose results lowering asks for, unless
`must_lower_even_if_unused` holds (`machinst/lower.rs`, `lower_clif_block`;
`inst_predicates.rs:113`: `op != GetPinnedReg && has_side_effect`), and a `load` whose flags have
no trap code (`notrap`) has no side effect (`is_load_with_defined_trapping`). Lowering runs
bottom-up and counts a value as needed only when a lowered instruction asks for its register
(`value_lowered_uses`), so a chain of dead loads, and the address computations only they read, go
too (filetest `isa/aarch64/dead-notrap-load.clif`; wasmtime #14114). Cranelift 0.135.0 (cg_clif of
nightly-2026-09-26) lowers every load.

`run f` deletes, before lowering, the statements Cranelift 0.136.1 does not lower in such a
function: liveness is `Opt.dce`'s mark phase with `notrap` loads counted as removable; every
removable statement and every `notrap` load with no live result is deleted. Only when a `notrap`
load goes; otherwise `f` is returned unchanged (functions without such a load compile exactly as
before). Value numbers are kept, so regalloc2's input numbering (`CraneliftInput.shape`) is
Cranelift's.

Why it is sound (to be proved, `docs/contracts`): a `notrap` load never traps
(`Clif.evalInst_notrap_load`): it reads without changing memory, or the run is `stuck` (out of
bounds, misaligned `aligned`, uninitialised), and a stuck source run constrains nothing
(`Opt.OutcomeRefines`, `E2E.ArmRefines`).
-/

namespace Opt.NotrapDrop

open Clif

/-- A load with no trap code (`notrap`): never traps (`Clif.evalInst_notrap_load`). -/
def notrapLoad : Inst → Bool
  | .load _ _ fl _ _ => fl.trapCode.isNone
  | _ => false

/-- What may be deleted when no result is live: `Opt.removable`, or a `notrap` load. -/
def droppable (i : Inst) : Bool := removable i || notrapLoad i

/-- The live values: `Opt.dce`'s mark phase from the roots (operands of every statement that is not
`droppable`, and of every terminator) through the operands of `droppable` definitions. -/
def live (f : Function) : Std.HashSet ValueId := Id.run do
  let mut defOps : Std.HashMap ValueId (List ValueId) := {}
  let mut work : Array ValueId := #[]
  for b in f.blocks do
    for st in b.body do
      if droppable st.inst then
        for r in st.results do defOps := defOps.insert r (operands st.inst)
      else work := work ++ (operands st.inst).toArray
    work := work ++ (termOperands b.term).toArray
  let mut live : Std.HashSet ValueId := {}
  for _ in [0:defOps.size + work.size + 1] do
    if work.isEmpty then break
    let mut next : Array ValueId := #[]
    for v in work do
      if live.contains v then continue
      live := live.insert v
      next := next ++ ((defOps.get? v).getD []).toArray
    work := next
  return live

/-- A statement kept by the drop. -/
def keep (L : Std.HashSet ValueId) (st : Stmt) : Bool :=
  !droppable st.inst || st.results.any L.contains

/-- The number of `notrap` loads the drop with live set `L` deletes. -/
def droppedWith (f : Function) (L : Std.HashSet ValueId) : Nat :=
  f.blocks.foldl (fun n b => n + (b.body.filter fun st => notrapLoad st.inst && !keep L st).length) 0

/-- The number of `notrap` loads the drop deletes. -/
def dropped (f : Function) : Nat := droppedWith f (live f)

/-- **The check** the proof relies on (the mark phase is not trusted): every operand of a kept
statement and every operand of a terminator is in `L`. -/
def closedB (f : Function) (L : Std.HashSet ValueId) : Bool :=
  f.blocks.all fun b =>
    b.body.all (fun st => !keep L st || (operands st.inst).all L.contains) &&
      (termOperands b.term).all L.contains

/-- `f` without the statements `keep L` rejects. -/
def dropWith (f : Function) (L : Std.HashSet ValueId) : Function :=
  { f with blocks := f.blocks.map fun b => { b with body := b.body.filter (keep L) } }

/-- The live values stay below the output's fresh value, which is at most the input's: the
registers a `try_call` binds (from each side's fresh value on, `Opt.Win`) are never live. -/
def freshOk (f : Function) (L : Std.HashSet ValueId) : Bool :=
  let g := dropWith f L
  decide (g.freshValue ≤ f.freshValue) && L.toList.all fun v => decide (v < g.freshValue)

/-- **The pass**: `f` without its dead `notrap` loads and the dead removable statements, when at
least one `notrap` load goes and the live set passes `closedB` and `freshOk`; `f` otherwise. -/
def run (f : Function) : Function :=
  let L := live f
  if droppedWith f L != 0 && closedB f L && freshOk f L then dropWith f L else f

/-- `lean-backend`'s decision, as `Opt.ConstPhi.keeps`: the pass changes `f` and its output,
printed after `header`, parses back to itself. -/
def keeps (header : String) (f : Function) : Bool :=
  let g := run f
  !decide (g = f) && decide (ConstPhi.reparse header g = g)

def select (header : String) (f : Function) : Function :=
  if keeps header f then run f else f

def selectFile (header : String) (pf : ParsedFile) : ParsedFile :=
  { pf with funcs := pf.funcs.map fun p => { p with func := p.func.map (select header) } }

end Opt.NotrapDrop
