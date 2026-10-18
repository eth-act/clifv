import FV.Backend.AllocReady

/-!
# A register allocator in Lean: linear scan with lifetime holes (V4b, #57)

`leanAlloc vc` allocates a prepared `VCode` (`prepare`) and returns an ordinary `RFunc`, so it
is used exactly like regalloc2's answer: `allocateLean` lowers `lowerAllocReady vcp (leanAlloc
vcp)`, i.e. the allocation is kept only if `checkAlloc` accepts it (and `lowerRFunc`/emission
accept it), else the proven spill allocation replaces it. Every theorem about `allocResult`
/ `lowerAllocReady` (`E2E.backend_correct_final_alloc_proven`, `E2E.backend_correct_final_total_emit`,
the link theorems) therefore holds for this allocator with no new proof.

The allocator is split for the proof that the fallback is never taken (V4b-3/V4b-4,
#275/#276): an untrusted *planner* (liveness, segments, the linear scan: `Fn.plan`) chooses one
location per vreg and the segments where it must hold it (`Plan`); a decidable *validator*
(`Ctx.structOk`: a liveness certificate in position form and interference freedom) checks the
plan; the deterministic *builder* (`Ctx.build`) turns it into items, inserting only the moves
the plan's locations require. `planOk vc pl`: the plan passes the validator and builds.
`leanAlloc` uses the first of the planner's plans that passes, else the plan with every vreg
spilled (`Fn.spillPlan`, which passes on every in-scope function).

## Positions

Every instruction (global index `g`, blocks in prepared order) has five positions
`pos g s = 5 g + s`: `0` pre-read (sources of the moves before the instruction are read; block
arguments are read), `1` pre-write (moves into the instruction's operand registers; block
parameters are written), `2` early (early uses read, early defs written), `3` late (late uses
read, clobbers, late defs written), `4` post (moves out of the def registers).

## Planner

* *Liveness*: backward block dataflow; `inP b` (live at the start of `b`, parameters included),
  `out b`.
* *Segments*: per vreg, the sorted disjoint position intervals where its location must hold it
  (from its def, or the block start if live in, to its last read, or the block end if live out).
  A block parameter is written at position 1 of every predecessor's `jump`; a branch argument is
  read at position 0.
* *Claims*: positions where an instruction itself writes a physical register: a fixed use `p`
  of `v` (`[1, 2]`, owned by `v`), a fixed def (`[3, 4]`, owned), a clobber (`3`, no owner). A
  vreg may only be given a register whose claims it owns wherever its segments meet them.
* *Linear scan with lifetime holes, no splitting*: vregs in order of their first position; a
  vreg gets the first register of its class (hints first: its fixed registers, the registers
  of its block-parameter/argument and reuse partners) whose occupied segments and claims miss
  its segments; otherwise the cheapest set of lighter vregs occupying a register is evicted
  (weight: uses and defs weighted by `10 ^ loop depth`, divided by the length of the segments),
  or the vreg is spilled. A spilled vreg lives in a stack home for its whole life (homes are
  shared by vregs whose segments are disjoint).

Int registers: x0–x15, x19–x28; float registers: v0–v31 (both classes from the start). A
value live across a call is never in a clobbered register, so ints live across calls are in
x19–x28 and floats are spilled (the checker treats v8–v15 as clobbered).

## Builder

Per instruction: an operand whose vreg has a register is read/written in place; a fixed
operand is moved into/out of its register; an operand of a spilled vreg uses a scratch
register free at that instruction (no segment of a vreg in it, no claim of the instruction —
fixed operand, clobber — and no other operand register meets it) with a load before / a store
after; a reuse operand (`movk`) shares its register with the operand it reuses. Before a
`jump` with arguments: the parallel copy of the arguments into the parameters' locations
(`seqMoves`: a cycle goes through a free register or a temporary stack slot, a
memory-to-memory move through a free register); at the start of a `try_call`'s successor: its
live results out of their fixed registers. The moves around an instruction and out of a
`try_call`'s results need no sequencing in a validated plan (`cleanMoves`). Callee-saved
registers the allocation uses are saved at the entry and restored before every `Rets`,
exactly as `buildRFunc` does for regalloc2.

## Validator

`Ctx.structOk` (the conditions the proof of the builder assumes): every segment starts where
its vreg gets its value (a block start, its def, the parameter copy of a `jump`) and every
edge into a block delivers the vregs live at its start; every use and def is covered; the
segments in one register or home are disjoint and miss the other vregs' fixed-operand claims
and the clobbers. If the linear scan's plan fails it (or does not build: no free scratch
register), the planner retries with 2, then 4 registers per class withheld for scratch, then
the all-spill plan is used.
-/

namespace Backend
namespace LinearScan

open Std (HashSet HashMap)

/-- Position of slot `s` of global instruction `g` (module doc). -/
@[inline] def pos (g s : Nat) : Nat := 5 * g + s

/-- Maximal length of a claim (`[2, 4]`: an early fixed def). -/
def maxClaim : Nat := 2

/-- A position interval `[s, e]` held by `v` (for claims: `v` = owner + 1, `0` = no owner). -/
structure Seg where
  s : Nat
  e : Nat
  v : Nat
  deriving Inhabited, Repr

/-- First index `≥ lo` of `a` (sorted, disjoint) whose segment ends at or after `x`, searching
`[lo, hi)`. -/
def firstEndGeIn (a : Array Seg) (x : Nat) (lo hi : Nat) : Nat :=
  if lo < hi then
    let mid := (lo + hi) / 2
    if a[mid]!.e < x then firstEndGeIn a x (mid + 1) hi else firstEndGeIn a x lo mid
  else lo
termination_by hi - lo

/-- First index of `a` (sorted, disjoint) whose segment ends at or after `x`. -/
def firstEndGe (a : Array Seg) (x : Nat) : Nat := firstEndGeIn a x 0 a.size

/-- First index `≥ lo` of `a` (sorted by start) whose segment starts after `x`, searching
`[lo, hi)`. -/
def firstStartGtIn (a : Array Seg) (x : Nat) (lo hi : Nat) : Nat :=
  if lo < hi then
    let mid := (lo + hi) / 2
    if a[mid]!.s ≤ x then firstStartGtIn a x (mid + 1) hi else firstStartGtIn a x lo mid
  else lo
termination_by hi - lo

/-- First index of `a` (sorted by start) whose segment starts after `x`. -/
def firstStartGt (a : Array Seg) (x : Nat) : Nat := firstStartGtIn a x 0 a.size

/-- Does no segment of `a` (sorted, disjoint) meet `[s, e]`? -/
def segFree (a : Array Seg) (s e : Nat) : Bool :=
  match a[firstEndGe a s]? with
  | some g => e < g.s
  | none => true

/-- Owners of the segments of `a` (sorted, disjoint) meeting `[s, e]`. -/
def segOwners (a : Array Seg) (s e : Nat) : List Nat := Id.run do
  let mut out : List Nat := []
  let mut i := firstEndGe a s
  for _ in [0:a.size] do
    match a[i]? with
    | some g =>
      if g.s ≤ e then
        out := g.v :: out
        i := i + 1
      else break
    | none => break
  return out

/-- Insert a segment that meets none of `a`'s. -/
def insertSeg (a : Array Seg) (g : Seg) : Array Seg := a.insertIdx! (firstEndGe a g.s) g

/-- Does a claim of `cl` (sorted by start) not owned by `owner` meet `[s, e]`? -/
def claimsMeet (cl : Array Seg) (s e : Nat) (owner : Option Nat) : Bool := Id.run do
  let mut i := firstStartGt cl e
  for _ in [0:cl.size] do
    if i == 0 then break
    i := i - 1
    let c := cl[i]!
    if c.s + maxClaim < s then break
    if s ≤ c.e && (match owner with | some v => c.v != v + 1 | none => true) then return true
  return false

/-- Index of an allocatable-class register (x0–x31 = 0–31, v0–v31 = 32–63). -/
def regIdx : Reg → Option Nat
  | .x n => if n < 32 then some n else none
  | .v n => if n < 32 then some (32 + n) else none
  | _ => none

/-- Registers a vreg of the class may get, in order of preference: caller-saved ones first
(argument registers last, they are often claimed), then callee-saved ones (which cost a save
and restores). -/
def pool : RegClass → List Reg
  | .int => ([8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7] ++
      (List.range 10).map (19 + ·)).map .x
  | .float => ((List.range 16).map (16 + ·) ++ List.range 8 ++ (List.range 8).map (8 + ·)).map .v

/-- Registers withheld from vregs when the planner retries with scratch reserved. -/
def reserveOrder : RegClass → List Reg
  | .int => [15, 14, 13, 12].map .x
  | .float => [31, 30, 29, 28].map .v

/-- Scratch registers, in order of preference. -/
def scratchOrder : RegClass → List Reg
  | .int => ([9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 8] ++
      (List.range 10).map (19 + ·)).map .x
  | .float => ((List.range 16).map (16 + ·) ++ List.range 8 ++ (List.range 8).map (8 + ·)).map .v

def vregOf : Reg → Option Nat
  | .vreg n _ => some n
  | _ => none

/-! ## The function view -/

/-- A prepared `VCode` with its CFG and the operands of every instruction, numbered globally
(blocks in order). -/
structure Fn where
  vc : VCode
  succs : Array (Array Nat)
  preds : Array (Array Nat)
  /-- Global index of each block's first instruction; one more entry, the total. -/
  start : Array Nat
  /-- The block of each global instruction. -/
  blk : Array Nat
  insts : Array MInst
  ops : Array (Array Operand)
  /-- Vreg numbers are below `nv`. -/
  nv : Nat
  /-- The class of each vreg (`vc.classes`, `int` past its end). -/
  cls : Array RegClass
  deriving Inhabited

/-- Prefix sums from `a`: `starts [n₀, n₁, …] a = [a, a + n₀, a + n₀ + n₁, …]`. -/
def starts : List Nat → Nat → List Nat
  | [], a => [a]
  | n :: ns, a => a :: starts ns (a + n)

def Fn.make (vc : VCode) : Except String Fn := do
  let (succs, preds) ← vc.cfg
  let insts := vc.blocks.toList.flatMap (·.insts.toList)
  let ops ← insts.mapM MInst.operands
  if !(vc.blocks.all fun b => (b.params ++ b.branchArgs).all fun r => (vregOf r).isSome) then
    throw "a block parameter or argument is not a vreg"
  let nv0 := vc.blocks.foldl (fun n b =>
    (b.params ++ b.branchArgs).foldl (fun n r => max n ((vregOf r).getD 0 + 1)) n) vc.classes.size
  let nv := ops.foldl (fun n os => os.foldl (fun n o => max n (o.vreg + 1)) n) nv0
  pure {
    vc, succs, preds, nv
    start := (starts (vc.blocks.toList.map (·.insts.size)) 0).toArray
    blk := (vc.blocks.toList.zipIdx.flatMap fun (b, i) => List.replicate b.insts.size i).toArray
    insts := insts.toArray
    ops := ops.toArray
    cls := Array.ofFn (n := nv) fun v => vc.classes.getD v .int }

def Fn.nblocks (fn : Fn) : Nat := fn.vc.blocks.size

def Fn.params (fn : Fn) (b : Nat) : List Nat :=
  ((fn.vc.blocks[b]?.map (·.params.toList)).getD []).filterMap vregOf

def Fn.args (fn : Fn) (b : Nat) : List Nat :=
  ((fn.vc.blocks[b]?.map (·.branchArgs.toList)).getD []).filterMap vregOf

/-- Loop depth of every block: the number of back edges `b → s` (`s ≤ b` in the prepared
reverse postorder) with the block between `s` and `b`. -/
def loopDepth (succs : Array (Array Nat)) : Array Nat := Id.run do
  let mut d := Array.replicate succs.size 0
  for b in [0:succs.size] do
    for s in succs[b]! do
      if s ≤ b then
        for x in [s:b + 1] do d := d.modify x (· + 1)
  return d

/-! ## Liveness -/

structure Live where
  /-- Live at the start of each block, its parameters included. -/
  inP : Array (HashSet Nat)
  /-- Live at the end of each block. -/
  out : Array (HashSet Nat)
  deriving Inhabited

/-- Upward-exposed uses (parameters included) and defs of block `b`. -/
def Fn.genDefs (fn : Fn) (b : Nat) : HashSet Nat × HashSet Nat := Id.run do
  let mut live : HashSet Nat := {}
  for a in fn.args b do live := live.insert a
  let mut defs : HashSet Nat := {}
  let s := fn.start[b]!
  let e := fn.start[b + 1]!
  for k in [0:e - s] do
    let os := fn.ops[e - 1 - k]!
    for o in os do
      if o.kind == .def then
        live := live.erase o.vreg
        defs := defs.insert o.vreg
    for o in os do
      if o.kind == .use then live := live.insert o.vreg
  return (live, defs)

/-- Backward dataflow to the fixpoint (sets only grow; fuel-bounded). -/
def Fn.liveness (fn : Fn) : Live := Id.run do
  let nb := fn.nblocks
  let gd := (Array.range nb).map fn.genDefs
  let mut inP := gd.map (·.1)
  let mut out : Array (HashSet Nat) := Array.replicate nb {}
  for _ in [0:nb * (fn.nv + 1) + 2] do
    let mut changed := false
    for k in [0:nb] do
      let b := nb - 1 - k
      let mut o : HashSet Nat := {}
      for s in fn.succs[b]! do
        let ps := fn.params s
        for v in inP[s]! do
          if !ps.contains v then o := o.insert v
      let (g, d) := gd[b]!
      let mut i := g
      for v in o do
        if !d.contains v then i := i.insert v
      if i.size != inP[b]!.size || o.size != out[b]!.size then changed := true
      inP := inP.set! b i
      out := out.set! b o
    if !changed then break
  return { inP, out }

/-! ## Segments, claims, hints -/

/-- Sort and merge the intervals of one vreg. -/
def mergeIvs (l : List (Nat × Nat)) : Array (Nat × Nat) := Id.run do
  let a := l.toArray.qsort fun x y => x.1 < y.1
  let mut out : Array (Nat × Nat) := #[]
  for (s, e) in a do
    match out.back? with
    | some (s', e') =>
      if s ≤ e' + 1 then out := out.pop.push (s', max e e') else out := out.push (s, e)
    | none => out := out.push (s, e)
  return out

/-- The segments of every vreg and its weighted occurrence count. -/
def Fn.segments (fn : Fn) (lv : Live) (depth : Array Nat) :
    Array (Array (Nat × Nat)) × Array Nat := Id.run do
  let mut segs : Array (List (Nat × Nat)) := Array.replicate fn.nv []
  let mut cost : Array Nat := Array.replicate fn.nv 0
  for b in [0:fn.nblocks] do
    let s0 := fn.start[b]!
    let e0 := fn.start[b + 1]!
    if e0 == s0 then continue
    let gl := e0 - 1
    let w := 10 ^ min depth[b]! 3
    let mut opn : HashMap Nat Nat := {}
    for v in lv.out[b]! do opn := opn.insert v (pos gl 4)
    match fn.succs[b]!.toList with
    | [t] =>
      for (a, p) in (fn.args b).zip (fn.params t) do
        cost := cost.modify a (· + w)
        if !opn.contains a then opn := opn.insert a (pos gl 0)
        if lv.inP[t]!.contains p then
          segs := segs.modify p ((pos gl 1, pos gl 4) :: ·)
          cost := cost.modify p (· + w)
    | _ => pure ()
    for k in [0:e0 - s0] do
      let g := e0 - 1 - k
      let os := fn.ops[g]!
      for o in os do
        if o.kind == .def then
          let st := pos g (if o.pos == .early then 2 else 3)
          cost := cost.modify o.vreg (· + w)
          match opn[o.vreg]? with
          | some e =>
            segs := segs.modify o.vreg ((st, e) :: ·)
            opn := opn.erase o.vreg
          | none => segs := segs.modify o.vreg ((st, pos g 3) :: ·)
      for o in os do
        if o.kind == .use then
          cost := cost.modify o.vreg (· + w)
          let e := pos g (if o.pos == .early then 2 else 3)
          match opn[o.vreg]? with
          | some e' => if e' < e then opn := opn.insert o.vreg e
          | none => opn := opn.insert o.vreg e
    for (v, e) in opn.toList do segs := segs.modify v ((pos s0 0, e) :: ·)
  return (segs.map mergeIvs, cost)

/-- Positions of an operand's register at instruction `g` (claims and scratch ranges). -/
def opRange (g : Nat) (o : Operand) (post : Bool) : Nat × Nat :=
  match o.kind with
  | .use => (pos g 1, pos g (if o.pos == .early then 2 else 3))
  | .def => (pos g (if o.pos == .early then 2 else 3), if post then pos g 4 else pos g 3)

/-- The claims on every register (module doc), sorted by start. -/
def Fn.claims (fn : Fn) : Array (Array Seg) := Id.run do
  let mut cl : Array (Array Seg) := Array.replicate 64 #[]
  for g in [0:fn.insts.size] do
    for o in fn.ops[g]! do
      match o.con with
      | .fixed p =>
        match regIdx p with
        | some i =>
          let (s, e) := opRange g o true
          cl := cl.modify i (·.push ⟨s, e, o.vreg + 1⟩)
        | none => pure ()
      | _ => pure ()
    for r in fn.insts[g]!.clobbers do
      match regIdx r with
      | some i => cl := cl.modify i (·.push ⟨pos g 3, pos g 3, 0⟩)
      | none => pure ()
  return cl.map fun a => a.qsort fun x y => x.s < y.s

/-- Fixed registers of each vreg's operands (hints), and its partners: block parameter ↔
argument, reused use ↔ reuse def. -/
def Fn.hints (fn : Fn) : Array (List Reg) × Array (List Nat) := Id.run do
  let mut hs : Array (List Reg) := Array.replicate fn.nv []
  let mut ps : Array (List Nat) := Array.replicate fn.nv []
  for os in fn.ops do
    for o in os do
      match o.con with
      | .fixed p => if !(hs[o.vreg]!).contains p then hs := hs.modify o.vreg (· ++ [p])
      | .reuse i =>
        match os[i]? with
        | some u =>
          ps := ps.modify o.vreg (u.vreg :: ·)
          ps := ps.modify u.vreg (o.vreg :: ·)
        | none => pure ()
      | _ => pure ()
  for b in [0:fn.nblocks] do
    match fn.succs[b]!.toList with
    | [t] =>
      for (a, p) in (fn.args b).zip (fn.params t) do
        ps := ps.modify p (a :: ·)
        ps := ps.modify a (p :: ·)
    | _ => pure ()
  return (hs, ps)

/-! ## The plan -/

/-- One location per vreg — a register, or (`none`) the stack home `home v` — and the segments
(position intervals) where that location must hold it. This is all the builder (`Ctx.build`)
and the validator (`Ctx.structOk`) look at; the planner's liveness, claims and occupancy are
its own. -/
structure Plan where
  segs : Array (Array (Nat × Nat))
  reg : Array (Option Reg)
  home : Array Nat
  /-- Number of homes (per class; the temporary slot of a parallel move is the next one). -/
  nslots : Nat
  deriving Inhabited

/-- The linear scan (module doc), with the registers `reserved` withheld. -/
def Fn.plan (fn : Fn) (reserved : List Reg) : Plan := Id.run do
  let live := fn.liveness
  let depth := loopDepth fn.succs
  let (segs, cost) := fn.segments live depth
  let claims := fn.claims
  let (hints, partners) := fn.hints
  let span (v : Nat) : Nat := segs[v]!.foldl (fun n (s, e) => n + (e - s + 1)) 0
  let weight : Array Nat := (Array.range fn.nv).map fun v => cost[v]! * 4096 / (span v + 5)
  let order := ((Array.range fn.nv).filter (!segs[·]!.isEmpty)).qsort fun a b =>
    let sa := segs[a]![0]!.1
    let sb := segs[b]![0]!.1
    sa < sb || (sa == sb && a < b)
  let mut reg : Array (Option Reg) := Array.replicate fn.nv none
  let mut occ : Array (Array Seg) := Array.replicate 64 #[]
  for v in order do
    let c := fn.cls[v]!
    let vs := segs[v]!
    let claimOk (i : Nat) : Bool := vs.all fun (s, e) => !claimsMeet claims[i]! s e (some v)
    let fits (occ : Array (Array Seg)) (r : Reg) : Bool :=
      match regIdx r with
      | some i => claimOk i && vs.all fun (s, e) => segFree occ[i]! s e
      | none => false
    let pl := (pool c).filter (!reserved.contains ·)
    let hinted := (hints[v]! ++ (partners[v]!.filterMap (reg[·]!))).filter pl.contains
    match (hinted ++ pl).find? (fits occ) with
    | some r =>
      let i := (regIdx r).getD 0
      reg := reg.set! v (some r)
      occ := occ.modify i fun a => vs.foldl (fun a (s, e) => insertSeg a ⟨s, e, v⟩) a
    | none =>
      -- evict the lightest set of lighter vregs from a register whose claims allow `v`
      let mut best : Option (Reg × List Nat × Nat) := none
      for r in pl do
        let some i := regIdx r | continue
        if !claimOk i then continue
        let ws := (vs.toList.flatMap fun (s, e) => segOwners occ[i]! s e).eraseDups
        if ws.all (weight[·]! < weight[v]!) then
          let tot := ws.foldl (· + weight[·]!) 0
          match best with
          | some (_, _, t) => if tot < t then best := some (r, ws, tot)
          | none => best := some (r, ws, tot)
      match best with
      | some (r, ws, _) =>
        let i := (regIdx r).getD 0
        for w in ws do reg := reg.set! w none
        occ := occ.modify i fun a =>
          vs.foldl (fun a (s, e) => insertSeg a ⟨s, e, v⟩) (a.filter fun g => !ws.contains g.v)
        reg := reg.set! v (some r)
      | none => pure ()
  -- homes: first fit per class among the spilled vregs
  let mut home : Array Nat := Array.replicate fn.nv 0
  let mut slots : Array (Array Seg) × Array (Array Seg) := (#[], #[])
  for v in order do
    if reg[v]!.isSome then continue
    let vs := segs[v]!
    let sl := if fn.cls[v]! == .int then slots.1 else slots.2
    let k := (sl.findIdx? fun a => vs.all fun (s, e) => segFree a s e).getD sl.size
    let sl := if k < sl.size then sl else sl.push #[]
    let sl := sl.modify k fun a => vs.foldl (fun a (s, e) => insertSeg a ⟨s, e, v⟩) a
    home := home.set! v k
    slots := if fn.cls[v]! == .int then (sl, slots.2) else (slots.1, sl)
  { segs, reg, home, nslots := max slots.1.size slots.2.size }

/-! ## Building the allocated function -/

namespace Plan
variable (pl : Plan)

/-- The register of `v`, if it has one. -/
def regOf (v : Nat) : Option Reg := pl.reg.getD v none

/-- Does a segment of `v` contain position `p`? -/
def cov (v p : Nat) : Bool := (pl.segs.getD v #[]).any fun (s, e) => s ≤ p && p ≤ e

/-- Does one segment of `v` contain `[p, q]`? -/
def covI (v p q : Nat) : Bool := (pl.segs.getD v #[]).any fun (s, e) => s ≤ p && q ≤ e

/-- The segments of `v`, owned by `v`. -/
def segList (v : Nat) : List Seg := (pl.segs.getD v #[]).toList.map fun (s, e) => ⟨s, e, v⟩

end Plan

/-- Segments sorted by start. -/
def sortSegs (l : List Seg) : Array Seg := (l.mergeSort fun a b => a.s ≤ b.s).toArray

/-- The segments of the vregs in each register (index `regIdx`), sorted by start. -/
def Plan.occ (pl : Plan) : Array (Array Seg) :=
  ((List.range pl.reg.size).foldl (fun (acc : Array (List Seg)) v =>
    match (pl.regOf v).bind regIdx with
    | some i => acc.modify i (pl.segList v ++ ·)
    | none => acc) (Array.replicate 64 [])).map sortSegs

def Fn.clsOf (fn : Fn) (v : Nat) : RegClass := fn.cls.getD v .int

/-- The location of `v` in the plan `pl`: its register, else its home. -/
def Fn.loc (fn : Fn) (pl : Plan) (v : Nat) : Loc :=
  match pl.regOf v with
  | some r => .reg r
  | none => .stack (pl.home.getD v 0) (fn.clsOf v)

/-- Is register `r` free over `[s, e]`: no segment of a vreg in it (`occ`) and no entry of
`taken` (what the current instruction itself puts in registers: fixed operands, clobbers, the
operand registers chosen so far) meets it? -/
def regFree (occ : Array (Array Seg)) (taken : List (Reg × Nat × Nat)) (r : Reg) (s e : Nat) :
    Bool :=
  match regIdx r with
  | some i =>
    segFree (occ.getD i #[]) s e && !taken.any fun (r', s', e') => r' == r && s' ≤ e && s ≤ e'
  | none => false

/-- A scratch register of class `c` free over `[s, e]`, not in `avoid`. -/
def scratchReg (occ : Array (Array Seg)) (taken : List (Reg × Nat × Nat)) (c : RegClass)
    (s e : Nat) (avoid : List Reg) : Option Reg :=
  (scratchOrder c).find? fun r => !avoid.contains r && regFree occ taken r s e

def locReg? : Loc → Option Reg
  | .reg r => some r
  | _ => none

/-- A move item. -/
def mv (m : Loc × Loc) : RItem := .move m.1 m.2

/-- Moves without no-ops and repetitions. In a plan that passes `Ctx.structOk`, no move around
an instruction or out of a `try_call`'s results reads another's destination (fixed registers
are claimed, scratch registers free), so these need no sequencing. -/
def cleanMoves (ms : List (Loc × Loc)) : List (Loc × Loc) := (ms.filter fun (a, b) => a != b).eraseDups

/-- The class of a move's location (`int` for a location without one). -/
def locCls (l : Loc) : RegClass := l.cls?.getD .int

/-- One move, through the register `scr` of its class if both sides are in memory. -/
def emitMove (scr : RegClass → Option Reg) (m : Loc × Loc) : Except String (List RItem) :=
  if m.1.isReg || m.2.isReg then pure [.move m.1 m.2]
  else match scr (locCls m.1) with
    | some r => pure [.move m.1 (.reg r), .move (.reg r) m.2]
    | none => throw "no scratch register for a memory-to-memory move"

/-- Sequentialise the pending moves (`fuel` steps): a move whose destination no pending move
reads; else (only cycles are left) the first move's destination is saved to `tmp` of its class
and read from there. -/
def seqGo (scr : RegClass → Option Reg) (tmp : RegClass → Loc) :
    Nat → List (Loc × Loc) → Except String (List RItem)
  | _, [] => pure []
  | 0, _ :: _ => throw "parallel move did not resolve"
  | fuel + 1, m :: ms =>
    match (m :: ms).find? (fun x => !(m :: ms).any (·.1 == x.2)) with
    | some x => do
      let its ← emitMove scr x
      pure (its ++ (← seqGo scr tmp fuel ((m :: ms).erase x)))
    | none => do
      let t := tmp (locCls m.2)
      let its ← emitMove scr (m.2, t)
      pure (its ++ (← seqGo scr tmp fuel
        ((m :: ms).map fun x => (if x.1 == m.2 then t else x.1, x.2))))

/-- Sequentialise the parallel move `ms` (distinct destinations): no-ops and repetitions
dropped; a cycle is broken through `tmp` (a free register or a temporary stack slot, at most
one live at a time), a memory-to-memory move goes through the free register `scr`. -/
def seqMoves (ms : List (Loc × Loc)) (scr : RegClass → Option Reg) (tmp : RegClass → Loc) :
    Except String (List RItem) :=
  seqGo scr tmp (2 * ms.length + 2) (cleanMoves ms)

/-- Indices (in operand order) of the defs whose value the instruction keeps
(`MInst.keptDefs`). -/
def keptIdx (i : MInst) (os : Array Operand) : List Nat :=
  let ds := (os.toList.zipIdx.filter (·.1.kind == .def)).map (·.2)
  match i.keptDefs with
  | none => ds
  | some n => ds.take n

/-- The position slot where an operand is read (use) or written (def): 2 early, 3 late. -/
def opSlot (o : Operand) : Nat := if o.pos == .early then 2 else 3

/-- The builder's state at one instruction: the register of each operand chosen so far, the
registers taken (with the position range), the moves before and after (reversed), the scratch
register of each spilled use vreg. -/
structure IS where
  R : Array (Option Reg)
  taken : List (Reg × Nat × Nat)
  pre : List (Loc × Loc)
  post : List (Loc × Loc)
  useScr : List (Nat × Reg)

/-- The builder's result for one instruction: operand locations, moves before and after. -/
structure IOut where
  allocs : Array Loc
  pre : List (Loc × Loc)
  post : List (Loc × Loc)

/-- The function and plan the builder works on, with the plan's register occupancy. -/
structure Ctx where
  fn : Fn
  pl : Plan
  occ : Array (Array Seg)

def Ctx.ofPlan (fn : Fn) (pl : Plan) : Ctx := { fn, pl, occ := pl.occ }

namespace Ctx
variable (c : Ctx)

def loc (v : Nat) : Loc := c.fn.loc c.pl v

/-- Is def operand `j` (`o`) of global instruction `g` stored after it: kept (`kept`), not a
terminator's (`term`), its vreg live at the post position. -/
def store (g : Nat) (term : Bool) (kept : List Nat) (j : Nat) (o : Operand) : Bool :=
  !term && kept.contains j && c.pl.cov o.vreg (pos g 4)

/-- Fixed operands: their register, claimed over `opRange`; a use moved in before, a stored def
moved out after. -/
def fixedPass (g : Nat) (st : Nat → Operand → Bool) : List (Operand × Nat) → IS → Except String IS
  | [], s => pure s
  | (o, j) :: rest, s =>
    match o.con with
    | .fixed p =>
      let s := { s with
        R := s.R.set! j (some p)
        taken := (p, (opRange g o true).1, (opRange g o true).2) :: s.taken }
      let s := if o.kind == .use then
          (if c.loc o.vreg != .reg p then { s with pre := (c.loc o.vreg, .reg p) :: s.pre } else s)
        else if st j o && c.loc o.vreg != .reg p then
          { s with post := (.reg p, c.loc o.vreg) :: s.post }
        else s
      fixedPass g st rest s
    | .stack => throw "stack operand constraint"
    | _ => fixedPass g st rest s

/-- The register a reuse def with location `lrd` shares with the use it reuses (location
`lrn`), and whether `lrn` is moved into it before / it is moved to `lrd` after: the common
register, else `lrd`'s register if free over `[1, 2]`, else `lrn`'s if free over `[3, 4]`,
else a scratch register free over `[1, 4]`. -/
def reuseReg (g : Nat) (taken : List (Reg × Nat × Nat)) (cl : RegClass) (lrd lrn : Loc) :
    Except String (Reg × Bool × Bool) :=
  match locReg? lrd, locReg? lrn with
  | some r, some r' =>
    if r == r' then pure (r, false, false) else
    if regFree c.occ taken r (pos g 1) (pos g 2) then pure (r, true, false) else
    if regFree c.occ taken r' (pos g 3) (pos g 4) then pure (r', false, true) else
    match scratchReg c.occ taken cl (pos g 1) (pos g 4) [] with
    | some x => pure (x, true, true)
    | none => throw "no scratch register"
  | some r, none =>
    if regFree c.occ taken r (pos g 1) (pos g 2) then pure (r, true, false) else
    match scratchReg c.occ taken cl (pos g 1) (pos g 4) [] with
    | some x => pure (x, true, true)
    | none => throw "no scratch register"
  | none, some r' =>
    if regFree c.occ taken r' (pos g 3) (pos g 4) then pure (r', false, true) else
    match scratchReg c.occ taken cl (pos g 1) (pos g 4) [] with
    | some x => pure (x, true, true)
    | none => throw "no scratch register"
  | none, none =>
    match scratchReg c.occ taken cl (pos g 1) (pos g 4) [] with
    | some x => pure (x, true, true)
    | none => throw "no scratch register"

/-- Reuse defs (`movk`): one register for the def and the use it reuses (`reuseReg`). -/
def reusePass (g : Nat) (st : Nat → Operand → Bool) (os : Array Operand) :
    List (Operand × Nat) → IS → Except String IS
  | [], s => pure s
  | (o, j) :: rest, s =>
    match o.con with
    | .reuse ui => do
      let some u := os[ui]? | throw "reuse of a missing operand"
      let lrd := c.loc o.vreg
      let lrn := c.loc u.vreg
      let (x, inPre, inPost) ← c.reuseReg g s.taken o.cls lrd lrn
      reusePass g st os rest { s with
        R := (s.R.set! j (some x)).set! ui (some x)
        taken := (x, pos g 1, pos g 4) :: s.taken
        pre := if inPre then (lrn, .reg x) :: s.pre else s.pre
        post := if inPost && st j o then (.reg x, lrd) :: s.post else s.post }
    | _ => reusePass g st os rest s

/-- Uses: in place, or one scratch register per spilled vreg, loaded before. -/
def usePass (g : Nat) (os : Array Operand) : List (Operand × Nat) → IS → Except String IS
  | [], s => pure s
  | (o, j) :: rest, s =>
    if (s.R.getD j none).isSome || o.kind != .use then usePass g os rest s else
    match c.pl.regOf o.vreg with
    | some r => usePass g os rest { s with R := s.R.set! j (some r) }
    | none =>
      match s.useScr.lookup o.vreg with
      | some r => usePass g os rest { s with R := s.R.set! j (some r) }
      | none =>
        let late := os.any fun o' => o'.vreg == o.vreg && o'.kind == .use && o'.pos == .late
        let e := pos g (if late then 3 else 2)
        match scratchReg c.occ s.taken o.cls (pos g 1) e [] with
        | some r => usePass g os rest { s with
            R := s.R.set! j (some r)
            taken := (r, pos g 1, e) :: s.taken
            useScr := (o.vreg, r) :: s.useScr
            pre := (c.loc o.vreg, .reg r) :: s.pre }
        | none => throw "no scratch register"

/-- Defs (and anything left): in place, or a scratch register, stored after if `st`. -/
def defPass (g : Nat) (st : Nat → Operand → Bool) : List (Operand × Nat) → IS → Except String IS
  | [], s => pure s
  | (o, j) :: rest, s =>
    if (s.R.getD j none).isSome then defPass g st rest s else
    match c.pl.regOf o.vreg with
    | some r => defPass g st rest { s with R := s.R.set! j (some r) }
    | none =>
      let keep := st j o
      match scratchReg c.occ s.taken o.cls (opRange g o keep).1 (opRange g o keep).2 [] with
      | some r => defPass g st rest { s with
          R := s.R.set! j (some r)
          taken := (r, (opRange g o keep).1, (opRange g o keep).2) :: s.taken
          post := if keep then (.reg r, c.loc o.vreg) :: s.post else s.post }
      | none => throw "no scratch register"

/-- The operand registers and the moves of global instruction `g`: fixed operands, reuse defs,
uses, defs (in that order); the clobbers are taken at position 3. -/
def inst (g : Nat) : Except String IOut := do
  let os := c.fn.ops.getD g #[]
  let i := c.fn.insts.getD g default
  let st := c.store g i.isTerminator (keptIdx i os)
  let ops := os.toList.zipIdx
  let s ← c.fixedPass g st ops
    { R := Array.replicate os.size none, taken := [], pre := [], post := [], useScr := [] }
  let s := { s with taken := i.clobbers.map (fun r => (r, pos g 3, pos g 3)) ++ s.taken }
  let s ← c.reusePass g st os ops s
  let s ← c.usePass g os ops s
  let s ← c.defPass g st ops s
  pure {
    allocs := s.R.map fun r => .reg (r.getD .sp)
    pre := cleanMoves s.pre.reverse
    post := cleanMoves s.post.reverse }

/-- The parallel copy of block `b`'s branch arguments into its successor's parameters live there
(before its terminator, global index `g`): memory-to-memory moves through the first register
free over `[0, 1]` and outside the copy (`scr`), a cycle through the second one, else through
the temporary stack slot `nslots`. -/
def argMoves (b g : Nat) : Except String (List RItem) :=
  match (c.fn.succs.getD b #[]).toList with
  | [t] =>
    let ms := ((c.fn.args b).zip (c.fn.params t)).filterMap fun (a, p) =>
      if c.pl.cov p (pos (c.fn.start.getD t 0) 0) then some (c.loc a, c.loc p) else none
    let avoid := ms.flatMap fun (a, p) => [locReg? a, locReg? p].filterMap id
    let scr (cl : RegClass) := scratchReg c.occ [] cl (pos g 0) (pos g 1) avoid
    let tmp (cl : RegClass) : Loc :=
      match scratchReg c.occ [] cl (pos g 0) (pos g 1) ((scr cl).toList ++ avoid) with
      | some r => .reg r
      | none => .stack c.pl.nslots cl
    seqMoves ms scr tmp
  | _ =>
    if (c.fn.args b).isEmpty then pure [] else
      throw "block arguments on a branch with several successors"

/-- The moves out of the result registers of the terminator of `s`'s predecessor `b`: its defs
live on the edge (`termEdgeDefs`, a `try_call`'s results) and at the start of `s` (global index
`g0`), from their fixed register into their location. -/
def termMoves (s g0 b : Nat) : Except String (List (Loc × Loc)) := do
  let defs : List Operand := match c.fn.vc.blocks[b]?, c.fn.succs[b]? with
    | some vb, some ss => match ss.toList.idxOf? s with
      | some j => (termEdgeDefs vb j).map (·.1)
      | none => []
    | _, _ => []
  let ms ← defs.foldlM (fun ms o =>
    if !c.pl.cov o.vreg (pos g0 0) then pure ms else
    match o.con with
    | .fixed p =>
      if c.loc o.vreg != .reg p then
        if (c.fn.preds.getD s #[]).size != 1 then throw "terminator results into a join block"
        else pure ((.reg p, c.loc o.vreg) :: ms)
      else pure ms
    | _ => if (c.pl.regOf o.vreg).isNone then throw "spilled non-fixed terminator def" else pure ms) []
  pure ms.reverse

/-- The moves at the start of block `s`: the results of its predecessors' terminators
(`termMoves`). -/
def entryMoves (s : Nat) : Except String (List RItem) := do
  let ms ← (c.fn.preds.getD s #[]).toList.mapM (c.termMoves s (c.fn.start.getD s 0))
  pure ((cleanMoves ms.flatten).map mv)

/-- The pieces of block `b`: its entry moves, then per instruction the argument copies before it
(the last one's) and the instruction's result. -/
structure Parts where
  entry : List RItem
  insts : List (List RItem × IOut)

def blockParts (b : Nat) : Except String Parts := do
  let s0 := c.fn.start.getD b 0
  let e0 := c.fn.start.getD (b + 1) 0
  let entry ← c.entryMoves b
  let insts ← (List.range (e0 - s0)).mapM fun k => do
    let args ← if s0 + k + 1 == e0 then c.argMoves b (s0 + k) else pure []
    let io ← c.inst (s0 + k)
    pure (args, io)
  pure { entry, insts }

/-- The items of a block from its pieces, with `restores` before a `Rets`. -/
def blockItems (vb : VBlock) (p : Parts) (restores : List RItem) : List RItem :=
  p.entry ++ p.insts.zipIdx.flatMap fun ((args, io), k) =>
    args ++ io.pre.map mv ++ (if vb.insts[k]? matches some (.rets _) then restores else []) ++
      [.op k io.allocs] ++ io.post.map mv

/-- The allocated function of the plan: items per block, saves of the callee-saved registers it
uses at the entry, restores before every `Rets` (as `buildRFunc`). -/
def build : Except String RFunc := do
  let parts ← (List.range c.fn.nblocks).mapM c.blockParts
  let vbs := c.fn.vc.blocks.toList
  let items := (parts.zip vbs).flatMap fun (p, vb) => blockItems vb p []
  let clobAll := c.fn.vc.blocks.any fun b => b.insts.any fun
    | .tryCall _ ti => ti.clobberAll
    | _ => false
  let saved := calleeSaved.filter fun r => clobAll || items.any (·.locs.contains (.reg r))
  let saves := saved.map fun r => RItem.move (.reg r) (.save r)
  let restores := saved.map fun r => RItem.move (.save r) (.reg r)
  let blocks := (parts.zip vbs).zipIdx.map fun ((p, vb), b) =>
    ((if b == 0 then saves else []) ++ blockItems vb p restores).toArray
  let slots := items.foldl (fun m it => it.locs.foldl (fun m l => match l with
    | .stack s _ => max m (s + 1)
    | _ => m) m) 0
  pure { blocks := blocks.toArray, spillSlots := slots, saved }

end Ctx

/-! ## The validator

`Ctx.structOk` (decidable, checked on every plan before it is used) is what the proof of the
builder (`planOk ⇒ AllocChecked`, #275) assumes of a plan: a liveness certificate in position
form — every segment starts where its vreg gets its value (`birthOk`), covers its uses and defs
(`usesOk`), and every vreg live at a block's start is live at the end of each predecessor, or is
a parameter whose argument is live at the `jump` (`edgeOk`) — and interference freedom: the
segments of the vregs in one register (`occ`) or one home (`homeOcc`) are disjoint, and miss the
claims of fixed operands of other vregs and clobbers (`claimsOk`). -/

/-- Sorted (by start) segments, each ending before the next one starts. -/
def disjointSorted (a : Array Seg) : Bool := (a.toList.zip a.toList.tail).all fun (x, y) => x.e < y.s

/-- Does a segment of `a` from index `i` on meet `[s, e]` with an owner other than `u` (`a`
sorted by start)? -/
def meetsOtherFrom (a : Array Seg) (s e u : Nat) (i : Nat) : Bool :=
  if h : i < a.size then
    if a[i].s ≤ e then (a[i].v != u && s ≤ a[i].e) || meetsOtherFrom a s e u (i + 1) else false
  else false
termination_by a.size - i

/-- Does a segment of `a` (sorted, disjoint) meet `[s, e]` with an owner other than `u`? -/
def meetsOther (a : Array Seg) (s e u : Nat) : Bool := meetsOtherFrom a s e u (firstEndGe a s)

/-- Is global instruction `g` the first of its block? -/
def Fn.isStart (fn : Fn) (g : Nat) : Bool :=
  g < fn.insts.size && fn.start.getD (fn.blk.getD g 0) 0 == g

/-- Is global instruction `g` the last of its block, whose only successor has the parameter `v`? -/
def Fn.paramAt (fn : Fn) (g v : Nat) : Bool :=
  let b := fn.blk.getD g 0
  g < fn.insts.size && g + 1 == fn.start.getD (b + 1) 0 &&
    match (fn.succs.getD b #[]).toList with
    | [t] => (fn.params t).contains v
    | _ => false

/-- First block index in `[lo, hi)` whose start position is at or after `x` (`hi` if none). -/
def Fn.firstBlockIn (fn : Fn) (x lo hi : Nat) : Nat :=
  if lo < hi then
    let mid := (lo + hi) / 2
    if pos (fn.start.getD mid 0) 0 < x then fn.firstBlockIn x (mid + 1) hi else fn.firstBlockIn x lo mid
  else lo
termination_by hi - lo

/-- The blocks from `b` on whose start position is at most `e`. -/
def Fn.blocksUpTo (fn : Fn) (e b : Nat) : List Nat :=
  if b < fn.nblocks then
    if pos (fn.start.getD b 0) 0 ≤ e then b :: fn.blocksUpTo e (b + 1) else []
  else []
termination_by fn.nblocks - b

/-- The blocks whose start position is in `[s, e]` (`start` is sorted). -/
def Fn.blocksIn (fn : Fn) (s e : Nat) : List Nat := fn.blocksUpTo e (fn.firstBlockIn s 0 fn.nblocks)

/-- The segments of the spilled vregs in each home (index `2 · home`, `+ 1` for floats), sorted. -/
def Plan.homeOcc (pl : Plan) (fn : Fn) : Array (Array Seg) :=
  ((List.range fn.nv).foldl (fun (acc : Array (List Seg)) v =>
    if (pl.regOf v).isSome then acc else
      acc.modify (2 * pl.home.getD v 0 + (if fn.clsOf v == .float then 1 else 0)) (pl.segList v ++ ·))
    (Array.replicate (2 * pl.nslots) [])).map sortSegs

namespace Ctx
variable (c : Ctx)

/-- A segment of `v` may start at `s` only where `v` gets its value: at a block's start, at a
def of `v`, or where the copy before a `jump` writes the parameter `v`. -/
def birthOk (v s : Nat) : Bool :=
  let g := s / 5
  match s % 5 with
  | 0 => c.fn.isStart g
  | 1 => c.fn.paramAt g v
  | sl => g < c.fn.ops.size && (c.fn.ops.getD g #[]).any fun o =>
      o.kind == .def && o.vreg == v && opSlot o == sl

/-- The last global instruction of block `b`. -/
def lastOf (b : Nat) : Nat := c.fn.start.getD (b + 1) 0 - 1

/-- `v`, live at the start of block `t`, reaches it from the predecessor `b`: a parameter of `t`
has its argument live at `b`'s `jump` and its location reserved from the copy on; every other
vreg is live at the end of `b`. -/
def edgeOk (v t b : Nat) : Bool :=
  let gl := c.lastOf b
  match (c.fn.params t).idxOf? v with
  | some k =>
    (c.fn.succs.getD b #[]).toList == [t] &&
      match (c.fn.args b)[k]? with
      | some a => c.pl.cov a (pos gl 0) && c.pl.covI v (pos gl 1) (pos gl 4)
      | none => false
  | none => c.pl.cov v (pos gl 4)

/-- Every segment is an interval starting at a birth of its vreg; at every block start it covers,
every edge into the block delivers the vreg (`edgeOk`). -/
def segsOk : Bool :=
  (List.range c.fn.nv).all fun v => (c.pl.segs.getD v #[]).all fun (s, e) =>
    s ≤ e && c.birthOk v s &&
      (c.fn.blocksIn s e).all fun t => (c.fn.preds.getD t #[]).all fun b => c.edgeOk v t b

/-- Every use is covered from its instruction's start to where it is read, every def from where
it is written to position 3. -/
def usesOk : Bool :=
  (List.range c.fn.ops.size).all fun g => (c.fn.ops.getD g #[]).all fun o =>
    match o.kind with
    | .use => c.pl.covI o.vreg (pos g 0) (pos g (opSlot o))
    | .def => c.pl.covI o.vreg (pos g (opSlot o)) (pos g 3)

/-- Registers are given to vregs below `nv` only, each in its vreg's class pool. -/
def regsOk : Bool :=
  c.pl.reg.size ≤ c.fn.nv && (List.range c.pl.reg.size).all fun v =>
    match c.pl.regOf v with
    | some r => (pool (c.fn.clsOf v)).contains r
    | none => true

/-- The home of every spilled vreg with a segment is below `nslots`; the segments in one home
are disjoint. -/
def homesOk : Bool :=
  (List.range c.fn.nv).all (fun v => (c.pl.regOf v).isSome || (c.pl.segs.getD v #[]).isEmpty ||
    c.pl.home.getD v 0 < c.pl.nslots) &&
    (c.pl.homeOcc c.fn).all disjointSorted

/-- No vreg's segment in register `p` meets a fixed operand claim of `p` by another vreg; no
vreg's segment in a clobbered register contains the clobber's position, where a `Rets` (whose
restores precede it) counts as clobbering the callee-saved registers. -/
def claimsOk : Bool :=
  (List.range c.fn.ops.size).all fun g =>
    let i := c.fn.insts.getD g default
    ((c.fn.ops.getD g #[]).all fun o => match o.con with
      | .fixed p => match regIdx p with
        | some i => !meetsOther (c.occ.getD i #[]) (opRange g o true).1 (opRange g o true).2 o.vreg
        | none => false
      | _ => true) &&
    ((i.clobbers ++ (if i matches .rets _ then calleeSaved else [])).all fun r => match regIdx r with
      | some i => segFree (c.occ.getD i #[]) (pos g 3) (pos g 3)
      | none => true)

/-- A def of a vreg with a register reads none of its own instruction's uses of it, except a late
def an early use. -/
def defUseOk : Bool :=
  (List.range c.fn.ops.size).all fun g =>
    let os := c.fn.ops.getD g #[]
    os.all fun o => o.kind != .def || (c.pl.regOf o.vreg).isNone ||
      os.all fun o' => o'.kind != .use || o'.vreg != o.vreg || (o.pos == .late && o'.pos == .early)

/-- **The structural conditions on a plan** (module doc of the validator). -/
def structOk : Bool :=
  c.segsOk && c.usesOk && c.regsOk && c.occ.all disjointSorted && c.homesOk && c.claimsOk &&
    c.defUseOk

/-- The allocated function of a plan that passes `structOk` and builds. -/
def checked : Option RFunc := if c.structOk then c.build.toOption else none

/-- Why a plan is not `checked` (diagnostics: the first failing condition, or the builder's
error). -/
def whyNot : String :=
  if !c.segsOk then "segsOk" else if !c.usesOk then "usesOk" else if !c.regsOk then "regsOk"
  else if !c.occ.all disjointSorted then "occ" else if !c.homesOk then "homesOk"
  else if !c.claimsOk then "claimsOk" else if !c.defUseOk then "defUseOk"
  else match c.build with
    | .ok _ => "ok"
    | .error e => s!"build: {e}"

end Ctx

/-- The plan with every vreg spilled for its whole life, each in its own home. -/
def Fn.spillPlan (fn : Fn) : Plan where
  segs := Array.replicate fn.nv #[(0, pos fn.insts.size 0)]
  reg := Array.replicate fn.nv none
  home := Array.range fn.nv
  nslots := fn.nv

/-- The registers withheld from vregs in the `n`-th retry (`reserveOrder`). -/
def reserved (n : Nat) : List Reg := (reserveOrder .int).take n ++ (reserveOrder .float).take n

/-- The first plan that passes the validator and builds: the linear scan, then with 2 and 4
registers per class withheld for scratch, then the all-spill plan. -/
def Fn.alloc (fn : Fn) : Option RFunc :=
  ((Ctx.ofPlan fn (fn.plan (reserved 0))).checked).orElse fun _ =>
    ((Ctx.ofPlan fn (fn.plan (reserved 2))).checked).orElse fun _ =>
      ((Ctx.ofPlan fn (fn.plan (reserved 4))).checked).orElse fun _ =>
        (Ctx.ofPlan fn fn.spillPlan).checked

end LinearScan

/-- **The validator on a plan of `vc`**: the plan passes `Ctx.structOk` and builds. -/
def planOk (vc : VCode) (pl : LinearScan.Plan) : Bool :=
  match LinearScan.Fn.make vc with
  | .ok fn => (LinearScan.Ctx.ofPlan fn pl).checked.isSome
  | .error _ => false

/-- The allocated function of a plan of `vc`. -/
def buildPlan (vc : VCode) (pl : LinearScan.Plan) : Except String RFunc := do
  (LinearScan.Ctx.ofPlan (← LinearScan.Fn.make vc) pl).build

/-- The Lean allocator: the first of the linear scan's plans (with 0, 2, 4 registers per class
withheld for scratch) that passes the validator (`planOk`), else the all-spill plan (`Fn.alloc`),
built. -/
def leanAlloc (vc : VCode) : Except String RFunc := do
  match (← LinearScan.Fn.make vc).alloc with
  | some rf => pure rf
  | none => throw "no plan of the Lean allocator passes planOk"

/-- Allocate a batch of functions with the Lean allocator; each allocation is kept only if
`checkAlloc` accepts it and it lowers and emits (`lowerAllocReady`), else the spill
allocation is used. -/
def allocateLean (vcs : Array VCode) : Array (Except String AFunc) :=
  vcs.map fun vc => prepareChecked vc >>= fun vcp => lowerAllocReady vcp (leanAlloc vcp)

/-! ## The allocation as a `lean-regalloc` answer

`cargo fv --keep-temps` keeps the allocator's answers of every compiled file (`$FV_RA_OUT`, in
the schema of `lean-regalloc`'s output, `docs/contracts/regalloc.md`); `lean-link` and
`link-check` rebuild each allocation from it (`parseRAOut`, `buildRFunc`). -/

def locAnswerName : Loc → String
  | .reg r => r.pregName
  | .stack n _ => s!"s{n}"
  | .save r => s!"<save {r.pregName}>"

def RItem.isSaveMove : RItem → Bool
  | .move (.save _) _ | .move _ (.save _) => true
  | _ => false

/-- `rf`, an allocation of the prepared `vc` whose callee-saved saves and restores are those
`buildRFunc` adds (`Plan.build`), as one entry of a `lean-regalloc` answer's `"functions"`
array: the operand locations of every instruction, every other move as an edit before the next
instruction. -/
def raAnswerJson (vc : VCode) (rf : RFunc) : String := Id.run do
  let mut allocs : Array String := #[]
  let mut edits : Array String := #[]
  let mut g := 0
  for items in rf.blocks do
    for it in items do
      match it with
      | .op _ ls =>
        allocs := allocs.push (jlist (ls.toList.map fun l => jstr (locAnswerName l)))
        g := g + 1
      | .move a b =>
        if !it.isSaveMove then
          edits := edits.push (s!"\{\"inst\":{g},\"pos\":\"before\",\"from\":{jstr (locAnswerName a)}," ++
            s!"\"to\":{jstr (locAnswerName b)}}")
  return s!"\{\"name\":{jstr vc.name},\"ok\":true,\"num_spillslots\":{rf.spillSlots}," ++
    s!"\"allocs\":{jlist allocs.toList},\"edits\":{jlist edits.toList},\"checker\":\"ok\"}"

/-- Does `buildRFunc` rebuild `rf` from `raAnswerJson vc rf`? -/
def raAnswerRoundTrip (vc : VCode) (rf : RFunc) : Bool :=
  match Lean.Json.parse (raAnswerJson vc rf) >>= parseRAOut >>= buildRFunc vc with
  | .ok rf' => rf'.blocks == rf.blocks && rf'.spillSlots == rf.spillSlots && rf'.saved == rf.saved
  | .error _ => false

/-- A failed answer (the consumer uses the spill allocation). -/
def raFailJson (name e : String) : String :=
  s!"\{\"name\":{jstr name},\"ok\":false,\"error\":{jstr e}}"

/-- `allocateLean`, also returning the answer for every function `prepareChecked` accepts, in
order (the functions `allocateRegalloc2` passes to `lean-regalloc`): `raAnswerJson` of
`leanAlloc`'s allocation, or a failed answer if there is none or it would not rebuild it. -/
def allocateLeanAnswers (vcs : Array VCode) : Array (Except String AFunc) × Array String := Id.run do
  let mut out : Array (Except String AFunc) := #[]
  let mut ans : Array String := #[]
  for vc in vcs do
    match prepareChecked vc with
    | .error e => out := out.push (.error e)
    | .ok vcp =>
      let ra := leanAlloc vcp
      out := out.push (lowerAllocReady vcp ra)
      ans := ans.push <| match ra with
        | .ok rf =>
          if raAnswerRoundTrip vcp rf then raAnswerJson vcp rf
          else raFailJson vcp.name "the answer does not rebuild the allocation"
        | .error e => raFailJson vcp.name e
  return (out, ans)

end Backend
