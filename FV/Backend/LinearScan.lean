import FV.Backend.AllocReady

/-!
# A register allocator in Lean: linear scan with lifetime holes (V4b, #57)

`leanAlloc vc` allocates a prepared `VCode` (`prepare`) and returns an ordinary `RFunc`, so it
is used exactly like regalloc2's answer: `allocateLean` lowers `lowerAllocReady vcp (leanAlloc
vcp)`, i.e. the allocation is kept only if `checkAlloc` accepts it (and `lowerRFunc`/emission
accept it), else the proven spill allocation replaces it. Every theorem about `allocResult`
/ `lowerAllocReady` (`E2E.backend_correct_final_alloc_proven`, `E2E.backend_correct_final_total_emit`,
the link theorems) therefore holds for this allocator with no new proof; what a proof still
has to add is that the fallback is never taken (V4b-3/V4b-4, #275/#276).

The allocator is split for that proof: an untrusted *planner* (liveness, segments, the linear
scan: `Fn.plan`) chooses one location per vreg; the deterministic *builder* (`Plan.build`)
turns any plan into items, inserting only the moves the plan's locations require.

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
register free at that instruction (no segment, claim or other operand register meets it) with
a load before / a store after; a reuse operand (`movk`) shares its register with the operand it
reuses. Before a `jump` with arguments: the parallel copy of the arguments into the
parameters' locations; at the start of a `try_call`'s successor: its live results out of
their fixed registers. Parallel moves are sequentialised (`seqMoves`; a cycle goes through a
free register or a temporary stack slot, a memory-to-memory move through a free register).
Callee-saved registers the allocation uses are saved at the entry and restored before every
`Rets`, exactly as `buildRFunc` does for regalloc2. If a scratch register cannot be found, the
planner retries with registers reserved for scratch; failing that, `leanAlloc` fails and the
spill allocation is used.
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

/-- First index of `a` (sorted, disjoint) whose segment ends at or after `x`. -/
def firstEndGe (a : Array Seg) (x : Nat) : Nat := Id.run do
  let mut lo := 0
  let mut hi := a.size
  for _ in [0:64] do
    if lo < hi then
      let mid := (lo + hi) / 2
      if a[mid]!.e < x then lo := mid + 1 else hi := mid
  return lo

/-- First index of `a` (sorted by start) whose segment starts after `x`. -/
def firstStartGt (a : Array Seg) (x : Nat) : Nat := Id.run do
  let mut lo := 0
  let mut hi := a.size
  for _ in [0:64] do
    if lo < hi then
      let mid := (lo + hi) / 2
      if a[mid]!.s ≤ x then lo := mid + 1 else hi := mid
  return lo

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
  insts : Array MInst
  ops : Array (Array Operand)
  /-- Vreg numbers are below `nv`. -/
  nv : Nat
  cls : Array RegClass
  deriving Inhabited

def Fn.make (vc : VCode) : Except String Fn := do
  let (succs, preds) ← vc.cfg
  let mut start : Array Nat := #[0]
  let mut insts : Array MInst := #[]
  let mut ops : Array (Array Operand) := #[]
  for b in vc.blocks do
    for i in b.insts do
      insts := insts.push i
      ops := ops.push (← i.operands)
    start := start.push insts.size
  let mut nv := vc.classes.size
  for os in ops do
    for o in os do nv := max nv (o.vreg + 1)
  for b in vc.blocks do
    for r in b.params ++ b.branchArgs do
      match r with
      | .vreg n _ => nv := max nv (n + 1)
      | _ => throw "a block parameter or argument is not a vreg"
  let mut cls : Array RegClass := Array.replicate nv .int
  for os in ops do
    for o in os do cls := cls.set! o.vreg o.cls
  for b in vc.blocks do
    for r in b.params ++ b.branchArgs do
      match r with
      | .vreg n c => cls := cls.set! n c
      | _ => pure ()
  pure { vc, succs, preds, start, insts, ops, nv, cls }

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

/-- One location per vreg: a register, or (`none`) the stack home `home v`. -/
structure Plan where
  fn : Fn
  live : Live
  segs : Array (Array (Nat × Nat))
  claims : Array (Array Seg)
  reg : Array (Option Reg)
  home : Array Nat
  /-- Segments of the vregs in each register. -/
  occ : Array (Array Seg)
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
  { fn, live, segs, claims, reg, home, occ, nslots := max slots.1.size slots.2.size }

/-! ## Building the allocated function -/

def Plan.loc (pl : Plan) (v : Nat) : Loc :=
  match pl.reg[v]! with
  | some r => .reg r
  | none => .stack pl.home[v]! pl.fn.cls[v]!

/-- Does a segment of `v` contain position `p`? -/
def Plan.liveAt (pl : Plan) (v : Nat) (p : Nat) : Bool :=
  pl.segs[v]!.any fun (s, e) => s ≤ p && p ≤ e

/-- Is register `r` free over `[s, e]`: no vreg segment, no claim, no register in `taken`
(operand registers of the current instruction) meets it? -/
def Plan.regFree (pl : Plan) (taken : List (Reg × Nat × Nat)) (r : Reg) (s e : Nat) : Bool :=
  match regIdx r with
  | some i =>
    segFree pl.occ[i]! s e && !claimsMeet pl.claims[i]! s e none &&
      !taken.any fun (r', s', e') => r' == r && s' ≤ e && s ≤ e'
  | none => false

/-- A scratch register of class `c` free over `[s, e]`, not in `avoid`. -/
def Plan.scratch (pl : Plan) (taken : List (Reg × Nat × Nat)) (c : RegClass) (s e : Nat)
    (avoid : List Reg) : Option Reg :=
  (scratchOrder c).find? fun r => !avoid.contains r && pl.regFree taken r s e

def locReg? : Loc → Option Reg
  | .reg r => some r
  | _ => none

/-- Sequentialise the parallel move `ms` (distinct destinations). `scr c avoid` is a free
register of class `c` outside `avoid`; a cycle is broken through a free register, else through
the temporary stack slot `tmp`; a memory-to-memory move goes through a free register. -/
def seqMoves (ms : List (Loc × Loc)) (scr : RegClass → List Reg → Option Reg) (tmp : Nat) :
    Except String (List RItem) := do
  let clsOf (l : Loc) : RegClass := l.cls?.getD .int
  let mut avoid : List Reg := ms.flatMap fun (a, b) => [locReg? a, locReg? b].filterMap id
  let mut pending := (ms.filter fun (a, b) => a != b).eraseDups
  let mut out : Array RItem := #[]
  for _ in [0:2 * ms.length + 2] do
    if pending.isEmpty then break
    let mut m := pending.find? fun (_, b) => !pending.any fun (a', _) => a' == b
    if m.isNone then
      -- a cycle: save the destination of the first move (a source of another) first
      let (_, b) := pending.head!
      let c := clsOf b
      let t : Loc := match scr c avoid with
        | some r => .reg r
        | none => .stack tmp c
      if let some r := locReg? t then avoid := r :: avoid
      pending := (b, t) :: pending.map fun (a', d) => (if a' == b then t else a', d)
      m := some (b, t)
    let (a, b) := m.getD (.reg .sp, .reg .sp)
    if a.isReg || b.isReg then out := out.push (.move a b)
    else match scr (clsOf a) avoid with
      | some r => out := out ++ #[.move a (.reg r), .move (.reg r) b]
      | none => throw "no scratch register for a memory-to-memory move"
    pending := pending.erase (a, b)
  if !pending.isEmpty then throw "parallel move did not resolve"
  pure out.toList

/-- Indices (in operand order) of the defs whose value the instruction keeps
(`MInst.keptDefs`). -/
def keptIdx (i : MInst) (os : Array Operand) : List Nat :=
  let ds := (os.toList.zipIdx.filter (·.1.kind == .def)).map (·.2)
  match i.keptDefs with
  | none => ds
  | some n => ds.take n

/-- The items of global instruction `g` (`k`-th of its block): moves before, the instruction
with its operand registers, moves after (none after a terminator). -/
def Plan.inst (pl : Plan) (g k : Nat) : Except String (List RItem) := do
  let fn := pl.fn
  let os := fn.ops[g]!
  let i := fn.insts[g]!
  let term := i.isTerminator
  let kept := keptIdx i os
  let store (j : Nat) (o : Operand) : Bool := !term && kept.contains j && pl.liveAt o.vreg (pos g 4)
  let mut R : Array (Option Reg) := Array.replicate os.size none
  let mut taken : List (Reg × Nat × Nat) := []
  let mut pre : List (Loc × Loc) := []
  let mut post : List (Loc × Loc) := []
  -- fixed operands
  for (o, j) in os.toList.zipIdx do
    match o.con with
    | .fixed p =>
      R := R.set! j (some p)
      let (s, e) := opRange g o true
      taken := (p, s, e) :: taken
      if o.kind == .use then
        if pl.loc o.vreg != .reg p then pre := (pl.loc o.vreg, .reg p) :: pre
      else if store j o && pl.loc o.vreg != .reg p then post := (.reg p, pl.loc o.vreg) :: post
    | .stack => throw "stack operand constraint"
    | _ => pure ()
  -- reuse defs: one register for the def and the use it reuses
  for (o, j) in os.toList.zipIdx do
    match o.con with
    | .reuse ui =>
      let some u := os[ui]? | throw "reuse of a missing operand"
      let lrd := pl.loc o.vreg
      let lrn := pl.loc u.vreg
      let keep := store j o
      -- `x`: the shared register; `inPre`: `rn` moved into it before, `inPost`: moved out
      -- of it into `rd`'s location after
      let mut x : Option Reg := none
      let mut inPre := false
      let mut inPost := false
      if let (some r, some r') := (locReg? lrd, locReg? lrn) then
        if r == r' then x := some r
      if x.isNone then
        if let some r := locReg? lrd then
          if pl.regFree taken r (pos g 1) (pos g 2) then
            x := some r
            inPre := true
      if x.isNone then
        if let some r' := locReg? lrn then
          if pl.regFree taken r' (pos g 3) (pos g 4) then
            x := some r'
            inPost := true
      if x.isNone then
        let some s := pl.scratch taken o.cls (pos g 1) (pos g 4) [] | throw "no scratch register"
        x := some s
        inPre := true
        inPost := true
      let xr := x.getD .sp
      if inPre then pre := (lrn, .reg xr) :: pre
      if inPost && keep then post := (.reg xr, lrd) :: post
      R := (R.set! j (some xr)).set! ui (some xr)
      taken := (xr, pos g 1, pos g 4) :: taken
    | _ => pure ()
  -- uses: in place, or one scratch per spilled vreg
  let mut useScr : List (Nat × Reg) := []
  for (o, j) in os.toList.zipIdx do
    if R[j]!.isSome || o.kind != .use then continue
    match pl.reg[o.vreg]! with
    | some r => R := R.set! j (some r)
    | none =>
      match useScr.lookup o.vreg with
      | some r => R := R.set! j (some r)
      | none =>
        let late := os.any fun o' => o'.vreg == o.vreg && o'.kind == .use && o'.pos == .late
        let e := pos g (if late then 3 else 2)
        let some r := pl.scratch taken o.cls (pos g 1) e [] | throw "no scratch register"
        taken := (r, pos g 1, e) :: taken
        useScr := (o.vreg, r) :: useScr
        pre := (pl.loc o.vreg, .reg r) :: pre
        R := R.set! j (some r)
  -- defs: in place, or a scratch stored after
  for (o, j) in os.toList.zipIdx do
    if R[j]!.isSome then continue
    match pl.reg[o.vreg]! with
    | some r => R := R.set! j (some r)
    | none =>
      let keep := store j o
      let (s, e) := opRange g o keep
      let some r := pl.scratch taken o.cls s e [] | throw "no scratch register"
      taken := (r, s, e) :: taken
      if keep then post := (.reg r, pl.loc o.vreg) :: post
      R := R.set! j (some r)
  let allocs := R.map fun r => Loc.reg (r.getD .sp)
  let scrAt (s e : Nat) (c : RegClass) (avoid : List Reg) : Option Reg :=
    pl.scratch taken c s e avoid
  let before ← seqMoves pre.reverse (scrAt (pos g 0) (pos g 1)) pl.nslots
  let after ← seqMoves post.reverse (scrAt (pos g 4) (pos g 4)) pl.nslots
  pure (before ++ [.op k allocs] ++ after)

/-- The parallel copy of block `b`'s branch arguments into its successor's parameters (before
its terminator, global index `g`). -/
def Plan.argMoves (pl : Plan) (b g : Nat) : Except String (List RItem) := do
  let fn := pl.fn
  match fn.succs[b]!.toList with
  | [t] =>
    let ms := ((fn.args b).zip (fn.params t)).filterMap fun (a, p) =>
      if pl.live.inP[t]!.contains p then some (pl.loc a, pl.loc p) else none
    seqMoves ms (fun c avoid => pl.scratch [] c (pos g 0) (pos g 1) avoid) pl.nslots
  | _ =>
    if (fn.args b).isEmpty then pure [] else throw "block arguments on a branch with several successors"

/-- Moves at the start of block `s` (first global instruction `g0`): the results of its
predecessor's `try_call` that are live in `s`, out of their fixed registers. -/
def Plan.entryMoves (pl : Plan) (s : Nat) : Except String (List RItem) := do
  let fn := pl.fn
  let g0 := fn.start[s]!
  let mut ms : List (Loc × Loc) := []
  for b in fn.preds[s]! do
    let gl := fn.start[b + 1]! - 1
    let i := fn.insts[gl]!
    let os := fn.ops[gl]!
    if !i.isTerminator then continue
    let kept := keptIdx i os
    let defs := (os.toList.zipIdx.filter fun (_, j) => kept.contains j).map (·.1)
    let defs := match i.normalDead with
      | some (jn, n) => if fn.succs[b]![jn]? == some s then defs.take n else defs
      | none => defs
    for o in defs do
      if !pl.live.inP[s]!.contains o.vreg then continue
      match o.con with
      | .fixed p =>
        if pl.loc o.vreg != .reg p then
          if fn.preds[s]!.size != 1 then throw "terminator results into a join block"
          ms := (.reg p, pl.loc o.vreg) :: ms
      | _ => if pl.reg[o.vreg]!.isNone then throw "spilled non-fixed terminator def"
  seqMoves ms.reverse (fun c avoid => pl.scratch [] c (pos g0 0) (pos g0 0) avoid) pl.nslots

/-- The allocated function of a plan: items per block, then saves/restores of the callee-saved
registers it uses (as `buildRFunc`). -/
def Plan.build (pl : Plan) : Except String RFunc := do
  let fn := pl.fn
  let mut blocks : Array (Array RItem) := #[]
  for b in [0:fn.nblocks] do
    let s0 := fn.start[b]!
    let e0 := fn.start[b + 1]!
    let mut items : Array RItem := (← pl.entryMoves b).toArray
    for k in [0:e0 - s0] do
      let g := s0 + k
      if g + 1 == e0 then items := items ++ (← pl.argMoves b g).toArray
      items := items ++ (← pl.inst g k).toArray
    blocks := blocks.push items
  let mut used : HashSet Loc := {}
  for items in blocks do
    for it in items do
      for l in it.locs do used := used.insert l
  let clobAll := fn.vc.blocks.any fun b => b.insts.any fun
    | .tryCall _ ti => ti.clobberAll
    | _ => false
  let saved := calleeSaved.filter fun r => clobAll || used.contains (.reg r)
  let saves : Array RItem := saved.toArray.map fun r => .move (.reg r) (.save r)
  let restores : Array RItem := saved.toArray.map fun r => .move (.save r) (.reg r)
  let blocks' := blocks.mapIdx fun bi items =>
    let vb := fn.vc.blocks[bi]!
    let items := items.flatMap fun it => match it with
      | .op k _ => if vb.insts[k]! matches .rets _ then restores.push it else #[it]
      | _ => #[it]
    if bi == 0 then saves ++ items else items
  let slots := used.fold (fun m l => match l with | .stack s _ => max m (s + 1) | _ => m) 0
  pure { blocks := blocks', spillSlots := slots, saved }

end LinearScan

/-- The Lean allocator: the linear scan's plan, built; if a scratch register is missing, the
planner retries with 2, then 4 registers per class withheld for scratch. -/
def leanAlloc (vc : VCode) : Except String RFunc := do
  let fn ← LinearScan.Fn.make vc
  let attempt (n : Nat) : Except String RFunc :=
    (fn.plan (LinearScan.reserveOrder .int |>.take n |>.append
      (LinearScan.reserveOrder .float |>.take n))).build
  match attempt 0 with
  | .ok rf => pure rf
  | .error _ =>
    match attempt 2 with
    | .ok rf => pure rf
    | .error _ => attempt 4

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
