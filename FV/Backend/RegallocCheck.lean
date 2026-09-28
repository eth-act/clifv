import FV.Backend.RegallocOps

/-!
# Register-allocation checker (M6, executable; proven sound: `Backend.Proof.checkAlloc_sound`)

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
  6. at a branch (`MInst.isBranch`): every def vreg leaves every set (`JTSequence`'s
     temporaries are dead after the branch);
  7. at a `Rets`: every callee-saved register `r` needs `entry r ∈ A r`;
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
plus one); running out of fuel is a rejection. The iteration is untrusted: `verify` checks its
result (entry in-state ⊆ `entryState`; every block reached, its items check from its in-state,
every successor's in-state ⊆ the edge's state). The soundness proof relies only on `verify`.

## Invariant and soundness theorem (`FV/Backend/Proof/RegallocSound.lean`, `docs/contracts/regalloc-proof.md`)

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
  deriving DecidableEq, Repr, Inhabited, Hashable

/-- An item of an allocated block: the `k`-th VCode instruction of the block with the
location of each operand (in `MInst.operands` order), or a move inserted by the allocator or
the frame (callee-saved save/restore). -/
inductive RItem where
  | op (k : Nat) (allocs : Array Loc)
  | move (src dst : Loc)
  deriving DecidableEq, Repr, Inhabited

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
  deriving DecidableEq, Repr, Inhabited

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

/-- Pointwise inclusion `a ⊆ b` (every symbol `a` puts in a location, `b` puts there too). -/
def le (a b : AState) : Bool :=
  (List.range a.size).all fun i => (a.getD i []).all fun s => (b.getD i []).contains s

end AState

/-- Checker context: the prepared VCode, its CFG and the allocated function. -/
structure CheckCtx where
  vc : VCode
  succs : Array (Array Nat)
  rf : RFunc
  size : Nat

/-- `pure ()` if `b`, else the error `msg ()` (built only on failure). -/
def ensure (b : Bool) (msg : Unit → String) : Except String Unit :=
  if b then pure () else throw (msg ())

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

/-- The per-operand static check (location and constraint) of operand `j`. -/
def CheckCtx.checkOperand (where_ : String) (ops : Array Operand) (allocs : Array Loc) :
    (Operand × Loc) × Nat → Except String Unit
  | ((o, l), j) => do
    ensure (c.locOk l o.cls && !(l matches .save _)) fun _ =>
      s!"{where_}: operand {j} (v{o.vreg}) in invalid location {repr l}"
    match o.con with
    | .any => pure ()
    | .reg => ensure l.isReg fun _ => s!"{where_}: operand {j} (v{o.vreg}) must be in a register"
    | .stack => ensure (!l.isReg) fun _ => s!"{where_}: operand {j} (v{o.vreg}) must be on the stack"
    | .fixed p =>
      ensure (l == .reg p) fun _ =>
        s!"{where_}: operand {j} (v{o.vreg}) must be in {repr p}, is in {repr l}"
    | .reuse i =>
      match ops[i]?, allocs[i]? with
      | some oi, some li =>
        ensure (oi.kind == .use && l.isReg && l == li) fun _ =>
          s!"{where_}: operand {j} (v{o.vreg}) must reuse operand {i}'s register"
      | _, _ => throw s!"{where_}: reuse of a missing operand"

/-- The locations a def must not share: every use and clobber (early def), every late use and
clobber (late def). -/
def defConflicts (uses : List (Operand × Loc)) (clobLocs : List Loc) : OpPos → List Loc
  | .early => uses.map (·.2) ++ clobLocs
  | .late => (uses.filter (·.1.pos == .late)).map (·.2) ++ clobLocs

/-- Static checks of one instruction's allocation (state-independent). -/
def CheckCtx.checkStatic (where_ : String) (ops : Array Operand) (allocs : Array Loc)
    (clob : List Reg) : Except String Unit := do
  ensure (ops.size == allocs.size) fun _ =>
    s!"{where_}: {allocs.size} allocations for {ops.size} operands"
  let pairs := (ops.zip allocs).toList
  pairs.zipIdx.forM (c.checkOperand where_ ops allocs)
  let clobLocs := clob.map Loc.reg
  let defs := pairs.filter (·.1.kind == .def)
  let uses := pairs.filter (·.1.kind == .use)
  ensure (decide (defs.map (·.2)).Nodup) fun _ => s!"{where_}: two defs in the same location"
  defs.forM fun (o, l) =>
    ensure (!(defConflicts uses clobLocs o.pos).contains l) fun _ =>
      s!"{where_}: def of v{o.vreg} in {repr l} overwrites an input or clobber"
  (uses.filter (·.1.pos == .late)).forM fun (o, l) =>
    ensure (!clobLocs.contains l) fun _ => s!"{where_}: late use of v{o.vreg} in clobbered {repr l}"

def needs (where_ : String) (a : AState) (l : Loc) (s : Sym) : Except String Unit :=
  ensure ((a.get l).contains s) fun _ =>
    s!"{where_}: {repr l} does not hold {repr s} (holds {repr (a.get l)})"

/-- The operand–location pairs of kind `k` at position `p`. -/
def atPos (pairs : List (Operand × Loc)) (k : OpKind) (p : OpPos) : List (Operand × Loc) :=
  pairs.filter fun (o, _) => o.kind == k && o.pos == p

/-- Definitions: each vreg in turn becomes the only content of its location. -/
def defineAll (a : AState) (ds : List (Operand × Loc)) : AState :=
  ds.foldl (fun a (o, l) => a.define l (.vreg o.vreg)) a

/-- A clobbered register loses every vreg; a callee-saved one keeps its entry value (AAPCS64:
the callee preserves d8–d15, which Cranelift's clobber set over-approximates as clobbered). -/
def clobberAll (a : AState) (clob : List Reg) : AState :=
  clob.foldl (fun a r => a.put (.reg r) ((a.get (.reg r)).filter (· == .entry r))) a

/-- The def vregs of `pairs` leave every location (a branch's defs, `JTSequence`'s
temporaries, are dead after the branch; the proof's allocated-code semantics havocs them). -/
def forgetDefs (a : AState) (pairs : List (Operand × Loc)) : AState :=
  a.map (·.filter fun s => !(pairs.any fun p => p.1.kind == .def && s == .vreg p.1.vreg))

/-- The transfer of an original instruction with operand–location pairs `pairs`, in execution
order: early defs, clobbers, late defs; a branch's defs are then forgotten. -/
def transferOp (i : MInst) (pairs : List (Operand × Loc)) (a : AState) : AState :=
  let a' :=
    defineAll (clobberAll (defineAll a (atPos pairs .def .early)) i.clobbers) (atPos pairs .def .late)
  if i.isBranch then forgetDefs a' pairs else a'

/-- At a `Rets`: every callee-saved register holds its entry value. -/
def retCheck (where_ : String) (i : MInst) (a : AState) : Except String Unit :=
  match i with
  | .rets _ => calleeSaved.forM fun r =>
      needs s!"{where_} (return: callee-saved register not restored)" a (.reg r) (.entry r)
  | _ => pure ()

/-- Transfer (with the state-dependent checks) of one original instruction: early uses are
checked in the in-state, late uses after the early defs. -/
def CheckCtx.stepOp (where_ : String) (i : MInst) (ops : Array Operand) (allocs : Array Loc)
    (a : AState) : Except String AState := do
  c.checkStatic where_ ops allocs i.clobbers
  let pairs := (ops.zip allocs).toList
  (atPos pairs .use .early).forM fun p => needs where_ a p.2 (.vreg p.1.vreg)
  (atPos pairs .use .late).forM fun p =>
    needs where_ (defineAll a (atPos pairs .def .early)) p.2 (.vreg p.1.vreg)
  let a' := transferOp i pairs a
  retCheck where_ i a'
  pure a'

/-- Static checks of a move: at least one side a register, both of one class, a callee-save
slot only with its own register. -/
def CheckCtx.checkMove (where_ : String) (src dst : Loc) : Except String Unit :=
  match src.cls? with
  | none => throw s!"{where_}: bad move source {repr src}"
  | some cls => do
    ensure (c.locOk src cls && c.locOk dst cls) fun _ =>
      s!"{where_}: move {repr src} → {repr dst}: invalid location or class mismatch"
    ensure (src.isReg || dst.isReg) fun _ => s!"{where_}: memory-to-memory move"
    match src, dst with
    | .save r, .reg r' | .reg r', .save r =>
      ensure (r == r') fun _ => s!"{where_}: save slot of {repr r} used with {repr r'}"
    | _, _ => pure ()

def CheckCtx.stepMove (where_ : String) (src dst : Loc) (a : AState) : Except String AState := do
  c.checkMove where_ src dst
  pure (a.put dst (a.get src))

/-- Run the items of block `vb` from its in-state, `next` being the index of the next VCode
instruction due: structural checks, transfer and checks of every item. Returns the
out-state. -/
def CheckCtx.runItems (vb : VBlock) : Nat → List RItem → AState → Except String AState
  | next, [], a => do
    ensure (next == vb.insts.size) fun _ => s!"block {vb.label}: missing instructions"
    pure a
  | next, it :: its, a => do
    ensure (next != vb.insts.size) fun _ => s!"block {vb.label}: code after the terminator"
    match it with
    | .move src dst => do
      let a ← c.stepMove s!"block {vb.label}" src dst a
      CheckCtx.runItems vb next its a
    | .op k allocs => do
      ensure (k == next) fun _ => s!"block {vb.label}: instruction {k} where {next} is due"
      match vb.insts[k]? with
      | none => throw s!"block {vb.label}: no instruction {k}"
      | some i => do
        let ops ← i.operands
        let a ← c.stepOp s!"block {vb.label} inst {k}" i ops allocs a
        CheckCtx.runItems vb (next + 1) its a

/-- Run one block from its in-state. Returns the out-state. -/
def CheckCtx.runBlock (b : Nat) (a : AState) : Except String AState :=
  match c.vc.blocks[b]?, c.rf.blocks[b]? with
  | some vb, some items => c.runItems vb 0 items.toList a
  | none, _ => throw s!"no block {b}"
  | _, none => throw s!"no allocated block {b}"

/-- The state entering successor `s` of block `b` (branch arguments as a parallel copy). -/
def CheckCtx.edge (b s : Nat) (a : AState) : Except String AState :=
  match c.vc.blocks[b]?, c.vc.blocks[s]? with
  | some vb, some sb => do
    ensure (vb.branchArgs.size == sb.params.size) fun _ =>
      s!"edge {vb.label} → {sb.label}: {vb.branchArgs.size} arguments for {sb.params.size} parameters"
    if vb.branchArgs.isEmpty then pure a
    else do
      let ps ← sb.params.toList.mapM vregNum
      let xs ← vb.branchArgs.toList.mapM vregNum
      ensure (decide ps.Nodup) fun _ => s!"block {sb.label}: parameters are not distinct"
      pure (a.parCopy ps xs)
  | none, _ => throw s!"no block {b}"
  | _, none => throw s!"no block {s}"

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

/-- The (untrusted) fixpoint iteration: it only proposes in-states; `verify` checks them. -/
def CheckCtx.fixpoint (fuel : Nat) (ins : Array (Option AState)) :
    Except String (Array (Option AState)) :=
  match fuel with
  | 0 => throw "checker did not reach a fixpoint (fuel exhausted)"
  | fuel + 1 => do
    let (ins, changed) ← c.round ins
    if changed then CheckCtx.fixpoint fuel ins else pure ins

/-- Block `b` of the proposed in-states `ins`: reached, its items check from its in-state, and
every successor's in-state is included in the state the edge produces. -/
def CheckCtx.verifyBlock (ins : Array (Option AState)) (b : Nat) : Except String Unit :=
  match ins[b]? with
  | some (some a) => do
    let out ← c.runBlock b a
    (c.succs[b]?.getD #[]).toList.forM fun s => do
      let e ← c.edge b s out
      match ins[s]? with
      | some (some a') => ensure (a'.le e) fun _ => s!"block {s}: in-state is not a fixpoint"
      | _ => throw s!"block {s} is never reached"
  | _ => throw s!"block {b} is never reached"

end

/-- The entry state: callee-saved registers hold their entry values. -/
def entryState (size : Nat) : AState :=
  calleeSaved.foldl (fun a r => a.put (.reg r) [.entry r]) (Array.replicate size [])

/-- Check the proposed in-states: the entry block's is included in `entryState`, every block
passes `verifyBlock`. This (not the iteration) is what the soundness proof relies on. -/
def CheckCtx.verify (c : CheckCtx) (ins : Array (Option AState)) : Except String Unit :=
  match ins[0]? with
  | some (some a0) => do
    ensure (a0.le (entryState c.size)) fun _ => "entry in-state is not the entry state"
    (List.range c.vc.blocks.size).forM (c.verifyBlock ins)
  | _ => throw "the entry block is never reached"

/-- Check an allocated function against the (prepared) VCode it was allocated from. -/
def checkAlloc (vc : VCode) (rf : RFunc) : Except String Unit := do
  let (succs, preds) ← vc.cfg
  ensure (vc.blocks.size != 0) fun _ => "no blocks"
  ensure (rf.blocks.size == vc.blocks.size) fun _ => "block count differs"
  ensure (preds[0]!).isEmpty fun _ => "the entry block is a branch target"
  ensure (vc.blocks[0]!).params.isEmpty fun _ => "the entry block has parameters"
  ensure (rf.saved.all calleeSaved.contains) fun _ =>
    "save slot for a register that is not callee-saved"
  -- every instruction has an operand view
  let _ ← vc.blocks.mapM fun b => b.insts.mapM MInst.operands
  let size := 128 + 2 * rf.spillSlots
  let c : CheckCtx := { vc, succs, rf, size }
  let nsyms := vc.classes.size + calleeSaved.length
  let fuel := vc.blocks.size * (size * nsyms + 1) + 2
  let ins0 := (Array.replicate vc.blocks.size none).set! 0 (some (entryState size))
  let ins ← c.fixpoint fuel ins0
  ins.zipIdx.toList.forM fun (s, b) =>
    ensure s.isSome fun _ => s!"block {(vc.blocks[b]!).label} is never reached"
  c.verify ins

end Backend
