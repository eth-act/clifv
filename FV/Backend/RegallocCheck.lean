import FV.Backend.RegallocOps

/-!
# Register-allocation checker (M6, executable; soundness proof to come)

regalloc2 is an untrusted oracle. This module decides, independently of anything the
allocator claims, whether an **allocated function** (`RFunc`: every original instruction with
one location per operand, plus the moves, spills and reloads inserted between them and the
callee-saved saves/restores of the frame) implements the **VCode** it was computed from
(`VCode` after `prepare`, with the operands of `MInst.operands`). `check` returns
`.ok ()` or the reason for rejection; the backend refuses to compile a rejected function.

## Algorithm (forward symbolic dataflow, after regalloc2's `src/checker.rs`)

Abstract state at a program point: for every location `ℓ` (allocatable register, spill slot
per class, callee-save slot) the finite set `A ℓ` of *symbols* it is known to hold: `vreg v`
(the current value of vreg `v`) or `entry r` (the value callee-saved register `r` had when the
function was entered). Sets are lists; the lattice is ordered by inclusion, the meet at a join
point is pointwise intersection, `none` (block not reached yet) is ⊤.

Transfer functions:

* `move src dst` (inserted by the allocator): `A' = A[dst ↦ A src]`;
* original instruction `op k allocs`, operands `ops`, clobbers `C` (in execution order):
  1. every early use `(v, ℓ)` needs `vreg v ∈ A ℓ`;
  2. every early def `(v, ℓ)`: remove `vreg v` from all sets, then `A ℓ := {vreg v}`;
  3. every late use `(v, ℓ)` needs `vreg v ∈ A ℓ`;
  4. every clobbered register `c`: `A c := A c ∩ {entry c}` (vreg values are lost; the entry
     value of a callee-saved register survives a call, since the callee preserves it —
     `DEFAULT_AAPCS_CLOBBERS` lists v8–v15 only because regalloc2 cannot express "low half");
  5. every late def as in 2;
  6. at a `Rets`: every callee-saved register `r` needs `entry r ∈ A r`;
* edge `b → s` with branch arguments `a⃗` for parameters `p⃗` (the VCode's parallel copy):
  `A' ℓ = (A ℓ \ {vreg p⃗}) ∪ {vreg pᵢ | vreg aᵢ ∈ A ℓ}`.

Entry state: callee-saved register `r` holds `{entry r}`, everything else `∅`.
Static checks per operand: the location is allocatable (never x16/x17/x18/fp/lr/sp, which the
emitted code uses itself) and of the vreg's class, spill slots are below the frame's count,
and the constraint holds (`reg`: a register; `fixed p`: exactly `p`; `reuse i`: the location
of operand `i`, a use). Per instruction: defs have pairwise distinct locations; an early def's
location differs from every use and every clobber; a late def's location differs from every
late use and every clobber (so the operand-position semantics above describes the emitted
instruction). Per move: at least one side is a register, both sides have the same class, a
callee-save slot only pairs with its own register. Structure: each block holds its VCode
instructions in order, each exactly once, and ends with its terminator (no move after it).

The fixpoint is computed by round-robin rounds (fuel-bounded: states only shrink after a block
is first reached, so the number of rounds is bounded by `blocks × (locations × symbols + 1)`
plus one); checks run in every round, and the last round (no state changes) runs them on the
fixpoint states. Running out of fuel is a rejection.

## Invariant and intended soundness theorem (see `docs/contracts/regalloc.md`)

Invariant (per program point, for machine state `m`, VCode vreg environment `ρ`, entry
register file `r₀`): `∀ ℓ s, s ∈ A ℓ → m ℓ = ⟦s⟧` with `⟦vreg v⟧ = ρ v`, `⟦entry r⟧ = r₀ r`.
The use checks then say every instruction reads the values the VCode reads, and the return
check says callee-saved registers hold their entry values when the function returns.
-/

namespace Backend

/-- A location of the allocated code. `stack slot cls`: regalloc2 spill slot `slot` of class
`cls` (the frame keeps int and float slots in separate areas, so they never overlap);
`save r`: the frame slot where the prologue saves callee-saved register `r`. -/
inductive Loc where
  | reg (r : Reg)
  | stack (slot : Nat) (cls : RegClass)
  | save (r : Reg)
  deriving DecidableEq, Repr, BEq, Inhabited, Hashable

/-- An item of an allocated block: the `k`-th VCode instruction of the block with the
location of each operand (in `MInst.operands` order), or a move inserted by the allocator or
the frame (callee-saved save/restore). -/
inductive RItem where
  | op (k : Nat) (allocs : Array Loc)
  | move (src dst : Loc)
  deriving DecidableEq, Repr, BEq, Inhabited

/-- An allocated function: one item list per block of the prepared VCode (same order). -/
structure RFunc where
  blocks : Array (Array RItem)
  /-- Number of spill slots per class (regalloc2 `num_spillslots`). -/
  spillSlots : Nat
  /-- Callee-saved registers with a save slot in the frame. -/
  saved : List Reg
  deriving Repr, Inhabited

/-- Symbolic values. -/
inductive Sym where
  | vreg (n : Nat)
  | entry (r : Reg)
  deriving DecidableEq, Repr, BEq, Inhabited

/-- The class of a location, if it is a location of the allocated code at all. -/
def Loc.cls? : Loc → Option RegClass
  | .reg r | .save r => r.realClass?
  | .stack _ c => some c

def Loc.isReg : Loc → Bool
  | .reg _ => true
  | _ => false

/-- Dense index of a location in the abstract state (registers x0–x31 = 0–31, v0–v31 =
32–63, save slots 64–127, spill slots from 128 on, int/float interleaved). -/
def Loc.index : Loc → Option Nat
  | .reg (.x n) => if n < 32 then some n else none
  | .reg (.v n) => if n < 32 then some (32 + n) else none
  | .save (.x n) => if n < 32 then some (64 + n) else none
  | .save (.v n) => if n < 32 then some (96 + n) else none
  | .stack s .int => some (128 + 2 * s)
  | .stack s .float => some (129 + 2 * s)
  | _ => none

/-- Abstract state: the symbol set of each location index. -/
abbrev AState := Array (List Sym)

namespace AState

def get (a : AState) (l : Loc) : List Sym :=
  match l.index with
  | some i => a.getD i []
  | none => []

def put (a : AState) (l : Loc) (s : List Sym) : AState :=
  match l.index with
  | some i => a.setIfInBounds i s
  | none => a

def remove (a : AState) (s : Sym) : AState := a.map (·.filter (· != s))

/-- A definition: the symbol leaves every location and is the only content of `l`. -/
def define (a : AState) (l : Loc) (s : Sym) : AState := (a.remove s).put l [s]

/-- Pointwise intersection (keeps the order of `a`, so `meet a b = a` iff `a ⊆ b`). -/
def meet (a b : AState) : AState :=
  a.mapIdx fun i s => let t := b.getD i []; s.filter (t.contains ·)

/-- The parallel copy `params := args` on symbols. -/
def parCopy (a : AState) (params args : List Nat) : AState :=
  let ps := params.map Sym.vreg
  a.map fun s =>
    let adds := (params.zip args).filterMap fun (p, x) =>
      if s.contains (.vreg x) then some (Sym.vreg p) else none
    let kept := s.filter (!ps.contains ·)
    kept ++ adds.filter (!kept.contains ·)

end AState

/-- Checker context: the prepared VCode, its operands (per block, per instruction), CFG. -/
structure CheckCtx where
  vc : VCode
  ops : Array (Array (Array Operand))
  succs : Array (Array Nat)
  rf : RFunc
  size : Nat

section
variable (c : CheckCtx)

def vregNum : Reg → Except String Nat
  | .vreg n _ => pure n
  | r => throw s!"{repr r} is not a virtual register"

/-- Is `l` a location the allocated code may hold a value of class `cls` in? -/
def CheckCtx.locOk (l : Loc) (cls : RegClass) : Bool :=
  l.cls? == some cls &&
  match l with
  | .reg r => r.allocatable
  | .stack s _ => s < c.rf.spillSlots
  | .save r => c.rf.saved.contains r && calleeSaved.contains r

/-- Static checks of one instruction's allocation (state-independent). -/
def CheckCtx.checkStatic (where_ : String) (ops : Array Operand) (allocs : Array Loc)
    (clob : List Reg) : Except String Unit := do
  if ops.size != allocs.size then
    throw s!"{where_}: {allocs.size} allocations for {ops.size} operands"
  let pairs := (ops.zip allocs).toList
  for ((o, l), j) in pairs.zipIdx do
    if !(c.locOk l o.cls) || l matches .save _ then
      throw s!"{where_}: operand {j} (v{o.vreg}) in invalid location {repr l}"
    match o.con with
    | .any => pure ()
    | .reg => if !l.isReg then throw s!"{where_}: operand {j} (v{o.vreg}) must be in a register"
    | .stack => if l.isReg then throw s!"{where_}: operand {j} (v{o.vreg}) must be on the stack"
    | .fixed p =>
      if l != .reg p then throw s!"{where_}: operand {j} (v{o.vreg}) must be in {repr p}, is in {repr l}"
    | .reuse i =>
      match ops[i]?, allocs[i]? with
      | some oi, some li =>
        if oi.kind != .use || !l.isReg || l != li then
          throw s!"{where_}: operand {j} (v{o.vreg}) must reuse operand {i}'s register"
      | _, _ => throw s!"{where_}: reuse of a missing operand"
  let clobLocs := clob.map Loc.reg
  let defs := pairs.filter (·.1.kind == .def)
  let uses := pairs.filter (·.1.kind == .use)
  let defLocs := defs.map (·.2)
  if defLocs.eraseDups.length != defLocs.length then
    throw s!"{where_}: two defs in the same location"
  for (o, l) in defs do
    let conflicts : List Loc := match o.pos with
      | .early => uses.map (fun (p : Operand × Loc) => p.2) ++ clobLocs
      | .late => (uses.filter (fun (p : Operand × Loc) => p.1.pos == .late)).map
          (fun (p : Operand × Loc) => p.2) ++ clobLocs
    if conflicts.contains l then
      throw s!"{where_}: def of v{o.vreg} in {repr l} overwrites an input or clobber"
  for (o, l) in uses.filter (·.1.pos == .late) do
    if clobLocs.contains l then throw s!"{where_}: late use of v{o.vreg} in clobbered {repr l}"

def needs (where_ : String) (a : AState) (l : Loc) (s : Sym) : Except String Unit :=
  if (a.get l).contains s then pure ()
  else throw s!"{where_}: {repr l} does not hold {repr s} (holds {repr (a.get l)})"

/-- Transfer (with the state-dependent checks) of one original instruction. -/
def CheckCtx.stepOp (where_ : String) (i : MInst) (ops : Array Operand) (allocs : Array Loc)
    (a : AState) : Except String AState := do
  let clob := i.clobbers
  c.checkStatic where_ ops allocs clob
  let pairs := (ops.zip allocs).toList
  let at_ (k : OpKind) (p : OpPos) := pairs.filter fun (o, _) => o.kind == k && o.pos == p
  for (o, l) in at_ .use .early do needs where_ a l (.vreg o.vreg)
  let a := (at_ .def .early).foldl (fun a (o, l) => a.define l (.vreg o.vreg)) a
  for (o, l) in at_ .use .late do needs where_ a l (.vreg o.vreg)
  -- A clobbered register loses every vreg; a callee-saved one keeps its entry value (AAPCS64:
  -- the callee preserves d8–d15, which Cranelift's clobber set over-approximates as clobbered).
  let a := clob.foldl (fun a r => a.put (.reg r) ((a.get (.reg r)).filter (· == .entry r))) a
  let a := (at_ .def .late).foldl (fun a (o, l) => a.define l (.vreg o.vreg)) a
  if i matches .rets _ then
    for r in calleeSaved do
      needs s!"{where_} (return: callee-saved register not restored)" a (.reg r) (.entry r)
  pure a

def CheckCtx.stepMove (where_ : String) (src dst : Loc) (a : AState) : Except String AState := do
  let some cls := src.cls? | throw s!"{where_}: bad move source {repr src}"
  if !(c.locOk src cls && c.locOk dst cls) then
    throw s!"{where_}: move {repr src} → {repr dst}: invalid location or class mismatch"
  if !src.isReg && !dst.isReg then throw s!"{where_}: memory-to-memory move"
  match src, dst with
  | .save r, .reg r' | .reg r', .save r =>
    if r != r' then throw s!"{where_}: save slot of {repr r} used with {repr r'}"
  | _, _ => pure ()
  pure (a.put dst (a.get src))

/-- Run one block from its in-state: structural checks, transfer and checks of every item.
Returns the out-state. -/
def CheckCtx.runBlock (b : Nat) (a : AState) : Except String AState := do
  let some vb := c.vc.blocks[b]? | throw s!"no block {b}"
  let some items := c.rf.blocks[b]? | throw s!"no allocated block {b}"
  let some bops := c.ops[b]? | throw s!"no operands for block {b}"
  let mut a := a
  let mut next := 0
  for it in items do
    if next == vb.insts.size then throw s!"block {vb.label}: code after the terminator"
    match it with
    | .move src dst => a ← c.stepMove s!"block {vb.label}" src dst a
    | .op k allocs =>
      if k != next then throw s!"block {vb.label}: instruction {k} where {next} is due"
      let where_ := s!"block {vb.label} inst {k}"
      a ← c.stepOp where_ vb.insts[k]! (bops[k]?.getD #[]) allocs a
      next := next + 1
  if next != vb.insts.size then throw s!"block {vb.label}: missing instructions"
  pure a

/-- The state entering successor number `j` of block `b` (branch arguments as a parallel copy). -/
def CheckCtx.edge (b s : Nat) (a : AState) : Except String AState := do
  let vb := c.vc.blocks[b]!
  let sb := c.vc.blocks[s]!
  if vb.branchArgs.size != sb.params.size then
    throw s!"edge {vb.label} → {sb.label}: {vb.branchArgs.size} arguments for {sb.params.size} parameters"
  if vb.branchArgs.isEmpty then return a
  let ps ← sb.params.toList.mapM vregNum
  let xs ← vb.branchArgs.toList.mapM vregNum
  pure (a.parCopy ps xs)

/-- One round over all blocks; returns the new in-states and whether any changed. -/
def CheckCtx.round (ins : Array (Option AState)) : Except String (Array (Option AState) × Bool) := do
  let mut ins := ins
  let mut changed := false
  for b in [0:c.vc.blocks.size] do
    let some a := ins[b]! | continue
    let out ← c.runBlock b a
    for s in c.succs[b]!.toList do
      let e ← c.edge b s out
      let new := match ins[s]! with
        | none => e
        | some old => old.meet e
      if ins[s]! != some new then
        ins := ins.set! s (some new)
        changed := true
  pure (ins, changed)

def CheckCtx.fixpoint (fuel : Nat) (ins : Array (Option AState)) :
    Except String (Array (Option AState)) :=
  match fuel with
  | 0 => throw "checker did not reach a fixpoint (fuel exhausted)"
  | fuel + 1 => do
    let (ins, changed) ← c.round ins
    if changed then CheckCtx.fixpoint fuel ins else pure ins

end

/-- The entry state: callee-saved registers hold their entry values. -/
def entryState (size : Nat) : AState :=
  calleeSaved.foldl (fun a r => a.put (.reg r) [.entry r]) (Array.replicate size [])

/-- Check an allocated function against the (prepared) VCode it was allocated from. -/
def checkAlloc (vc : VCode) (rf : RFunc) : Except String Unit := do
  let (succs, preds) ← vc.cfg
  if vc.blocks.size == 0 then throw "no blocks"
  if rf.blocks.size != vc.blocks.size then throw "block count differs"
  if !(preds[0]!).isEmpty then throw "the entry block is a branch target"
  if !(vc.blocks[0]!).params.isEmpty then throw "the entry block has parameters"
  if !rf.saved.all calleeSaved.contains then throw "save slot for a register that is not callee-saved"
  let ops ← vc.blocks.mapM fun b => b.insts.mapM MInst.operands
  let size := 128 + 2 * rf.spillSlots
  let c : CheckCtx := { vc, ops, succs, rf, size }
  let nsyms := vc.classes.size + calleeSaved.length
  let fuel := vc.blocks.size * (size * nsyms + 1) + 2
  let ins0 := (Array.replicate vc.blocks.size none).set! 0 (some (entryState size))
  let ins ← c.fixpoint fuel ins0
  for (s, b) in ins.zipIdx do
    if s.isNone then throw s!"block {(vc.blocks[b]!).label} is never reached"

end Backend
