import FV.Backend.Lowering.StockAlloc

/-!
Stock Cranelift 0.136.1 lowering schedule (`machinst/lower.rs`). This module is
being developed alongside the proved layout-order driver. Its result retains
per-successor arguments, which stock attaches to every branch, and an explicit
schedule for the replacement lowering simulation. It is not a compiler cutover.
-/

namespace Backend.Stock

open Isle Isle.Aarch64

def instArgs : Clif.Inst → List Nat
  | .iconst .. | .stackAddr .. | .fence | .nop | .symbolValue .. | .tlsValue ..
  | .funcAddr .. => []
  | .unary _ _ x | .bmask _ x | .extend _ _ x | .ireduce _ x | .isplit _ x
  | .load _ _ _ x _ | .atomicLoad _ _ x | .bitcast _ _ x | .trapz x _ | .trapnz x _ => [x]
  | .binary _ _ x y | .div _ _ x y | .overflow _ _ x y | .icmp _ _ x y
  | .uaddOverflowTrap _ x y _ | .iconcat _ x y | .store _ _ _ x y _ | .atomicRmw _ _ _ x y
  | .atomicStore _ _ x y => [x, y]
  | .carry _ _ x y z | .select _ x y z | .selectSpectreGuard _ x y z | .bitselect _ x y z
  | .atomicCas _ _ x y z => [x, y, z]
  | .call _ args => args
  | .callIndirect _ callee args => callee :: args

def termArgs : Clif.Terminator → List Nat
  | .jump bc => bc.args
  | .brif c t e => c :: t.args ++ e.args
  | .brTable x d tbl => x :: d.args ++ tbl.flatMap (·.args)
  | .ret xs => xs
  | .returnCall _ args => args
  | .trap _ => []
  | .tryCall _ args et => args ++ et.vals
  | .tryCallIndirect callee args et => callee :: args ++ et.vals

/-- Loads are ordering barriers even when not mandatory. Other memory operations
and possible traps must be lowered even when none of their outputs is demanded. -/
def mustLower : Clif.Inst → Bool
  | .load _ _ flags _ _ => !flags.notrap
  | .div .. | .uaddOverflowTrap .. | .store .. | .call .. | .callIndirect ..
  | .atomicLoad .. | .atomicStore .. | .atomicRmw .. | .atomicCas ..
  | .fence | .trapz .. | .trapnz .. => true
  | _ => false

def colored (i : Clif.Inst) : Bool :=
  mustLower i || match i with | .load .. => true | _ => false

inductive UseState where
  | unused | once | multiple
  deriving DecidableEq, Repr, Inhabited

def UseState.inc : UseState → UseState
  | .unused => .once | _ => .multiple

/-- Exact transitive multiplicity analysis: every value can become Multiple once;
the work budget counts each dependency edge once, including duplicate operands. -/
def useStates (ctx : Ctx) (args : Array (List Nat)) : Array UseState := Id.run do
  let mut uses := Array.replicate ctx.valTy.size UseState.unused
  for v in sretRet ctx.func do uses := uses.set! v .multiple
  let budget := args.foldl (fun n xs => n + xs.length) 1
  for xs in args do
    for v in xs do
      let old := uses[v]!
      let new := old.inc
      uses := uses.set! v new
      if old == .multiple || new != .multiple then continue
      let mut work := (ctx.defInst? v).map (fun i => args[i]!) |>.getD []
      for _ in [0:budget] do
        match work with
        | [] => break
        | x :: rest =>
          work := rest
          if uses[x]! == .multiple then continue
          uses := uses.set! x .multiple
          if let some i := ctx.defInst? x then work := args[i]! ++ work
  return uses

structure Opportunistic where
  block : Nat
  regs : List Reg
  count : Nat
  deriving Inhabited, Repr, DecidableEq

deriving instance DecidableEq for LState

structure State where
  base : LState
  demand : Array Nat
  uses : Array UseState
  instBlock : Array Nat
  entryColor : Array Nat
  endColor : Array Nat
  tryRegs : Array (List Reg × List Reg)
  current : Option Nat := none
  color : Option Nat := none
  sunk : Array Bool
  opportunistic : Array (Option Opportunistic)
  alias : Array (Option Nat) := #[]
  deriving Inhabited, DecidableEq

def State.mark (st : State) (v : Nat) : State :=
  { st with demand := st.demand.modify v (· + 1) }

def State.setAlias (st : State) (dst src : Reg) : Except String State := do
  let .vreg n c := dst | throw "alias destination is not virtual"
  let .vreg m d := src | throw "alias source is not virtual"
  if c != d then throw "alias register classes differ"
  let a := if st.alias.size ≤ n then st.alias ++ Array.replicate (n + 1 - st.alias.size) none
    else st.alias
  pure { st with alias := a.set! n (some m) }

/-- Match stock's UniqueUse versus Use distinction. `def_inst` itself remains
the raw DFG extractor, as in `isle_prelude.rs`; `is_sinkable_inst` uses this filter. -/
def source (ctx : Ctx) (st : State) (v : Nat) : Option (Nat × Bool) := do
  let i ← ctx.defInst? v
  let c := st.entryColor[i]!
  let once := st.uses[v]! == .once
  if c == 0 then some (i, once)
  else if once && ctx.insts[i]!.results.length == 1 && st.color == some (c + 1) then
    some (i, true)
  else none

def externCtor (ctx : Ctx) (t : Term) (args : List V) (st : State) :
    ExtResult (V × State) :=
  let delegate (s : State) := match Backend.externCtor ctx t args s.base with
    | .ok (v, b) => .ok (v, { s with base := b })
    | .fail => .fail
    | .unmodeled e => .unmodeled e
  match t.id, args with
  | TId.put_in_reg, [.value v] | TId.put_in_regs, [.value v]
  | TId.mark_value_used, [.value v]
  | TId.put_extended_in_reg, [.op (.extended v _)] =>
    if let some i := ctx.defInst? v then
      if st.sunk[i]! then .unmodeled s!"demand for sunk instruction {i}"
      else if t.id == TId.mark_value_used then .ok (.op .unit, st.mark v)
      else delegate (st.mark v)
    else if t.id == TId.mark_value_used then .ok (.op .unit, st.mark v)
    else delegate (st.mark v)
  | TId.put_in_regs_vec, [.values vs] =>
    if vs.any (fun v => (ctx.defInst? v).any (fun i => st.sunk[i]!)) then
      .unmodeled "demand for sunk instruction"
    else delegate (vs.foldl State.mark st)
  | TId.is_sinkable_inst, [.value v] => match source ctx st v with
    | some (i, true) => .ok (.inst i, st)
    | _ => .fail
  | TId.sink_inst, [.inst i] =>
    let c := st.entryColor[i]!
    if c == 0 || st.color != some (c + 1) ||
        ctx.insts[i]!.results.any (fun v => st.demand[v]! != 0) then
      .unmodeled s!"invalid sink of instruction {i}"
    else .ok (.op .unit, { st with color := some c, sunk := st.sunk.set! i true })
  | TId.opportunistic_def, [.value v, .regs rs] =>
    let block? := st.current.map (fun i => st.instBlock[i]!)
    let defBlock? := (ctx.defInst? v).map (fun i => st.instBlock[i]!)
    if st.demand[v]! == 0 || block?.isNone || block? != defBlock? then
      .ok (.op .unit, st)
    else .ok (.op .unit,
      { st with opportunistic := st.opportunistic.set! v (some ⟨block?.getD 0, rs, st.demand[v]!⟩) })
  | TId.gen_return, [.regsVec rss] =>
    -- AArch64 assigns StructReturn returns to x8, just like the incoming
    -- StructReturn pointer. The legacy helper used x0 for every first return.
    let ps := if (sigRets ctx.func.sig).any (·.purpose == .sret) then some [.x 8]
      else retRegs rss.length
    match ps, rss.mapM (fun | [r] => some r | _ => none) with
    | some ps, some rs => .ok (.op .unit, { st with base := st.base.emit (.rets (rs.zip ps)) })
    | _, _ => .unmodeled "gen_return register count"
  | TId.gen_call_output, [.op (.sig sig)] =>
    -- Caller-side output registers are allocated for explicit CLIF results;
    -- the implicit StructReturn return is intentionally ignored by stock.
    let (rss, base) := sig.returns.foldl (init := ([], st.base)) fun (rs, base) _ =>
      let (r, base) := base.fresh .int
      (rs ++ [[r]], base)
    .ok (.regsVec rss, { st with base })
  | TId.gen_try_call_rets, [.op (.sig sig)] =>
    -- Stock allocates payloads separately, then aliases any payload whose fixed
    -- register also holds a return. Do this when the call is actually lowered.
    match retRegs sig.returns.length with
    | none => .unmodeled "try_call return count"
    | some ps =>
      let (rets, pays) := ctx.tryRegs
      let merged := ((payloadRegs sig.callConv).zip pays).foldl
        (init := Except.ok (st, ([] : List Reg))) fun acc (p, r) => do
          let (s, regs) ← acc
          if let some i := ps.idxOf? p then
            let some ret := rets[i]? | throw "try_call return register"
            pure (← s.setAlias r ret, regs ++ [ret])
          else pure (s, regs ++ [r])
      match merged with
      | .error e => .unmodeled e
      | .ok (s, regs) =>
        let extra := ((payloadRegs sig.callConv).zip regs).filter fun (p, _) => !ps.contains p
        .ok (.op (.callRets (ps.zip rets ++ extra)), s)
  | _, _ => delegate st

def sem (ctx : Ctx) : Isle.Sem V State where
  int := (Backend.sem ctx).int
  bool := (Backend.sem ctx).bool
  prim := (Backend.sem ctx).prim
  eq := (Backend.sem ctx).eq
  mkData := (Backend.sem ctx).mkData
  unData := (Backend.sem ctx).unData
  ctor := externCtor ctx
  extract t v st := Backend.externExtract ctx t v st.base

def runTerm (ctx : Ctx) (term : String) (args : List V) (st : State) :
    Except String (Option V × State × List RuleId) :=
  match Isle.Interp.run program (sem ctx) {} term args st with
  | .ok r => .ok (r.value, r.state, r.trace)
  | .error e => .error s!"ISLE {term}: {repr e}"

structure SourceMetadata where
  instBlock : Array Nat
  entryColor : Array Nat
  endColor : Array Nat
  args : Array (List Nat)

def sourceMetadata (ctx : Ctx) (ranges : Array (Nat × Nat)) : SourceMetadata := Id.run do
  let mut blocks := Array.replicate ctx.insts.size 0
  let mut colors := Array.replicate ctx.insts.size 0
  let mut ends := #[]
  let mut args := Array.replicate ctx.insts.size []
  let mut color := 0
  for (b, bi) in ctx.func.blocks.zipIdx do
    color := color + 1
    let (start, stop) := ranges[bi]!
    for (s, j) in b.body.zipIdx do
      let i := start + j
      blocks := blocks.set! i bi
      args := args.set! i (instArgs s.inst)
      if colored s.inst then
        colors := colors.set! i color
        color := color + 1
    let ti := stop - 1
    blocks := blocks.set! ti bi
    args := args.set! ti (termArgs b.term)
    colors := colors.set! ti color
    color := color + 1
    ends := ends.push color
  pure ⟨blocks, colors, ends, args⟩

/-- Complete source metadata around the already allocated register map. -/
def finishCtx (ctx : Ctx) (ranges : Array (Nat × Nat)) (allocation : Allocation) :
    Ctx × Array (Nat × Nat) × State :=
  let metadata := sourceMetadata ctx ranges
  let ctx := { ctx with valReg := allocation.valReg }
  let state : State := {
    base := allocation.base
    demand := Array.replicate allocation.valReg.size 0
    uses := useStates ctx metadata.args
    instBlock := metadata.instBlock
    entryColor := metadata.entryColor
    endColor := metadata.endColor
    tryRegs := allocation.tryRegs
    sunk := Array.replicate ctx.insts.size false
    opportunistic := Array.replicate allocation.valReg.size none }
  (ctx, ranges, state)

/-- Dense layout-order allocation, including separately allocated exception
returns and payloads at the corresponding terminator's position. -/
def buildCtx (f : Clif.Function) : Except String (Ctx × Array (Nat × Nat) × State) := do
  let (ctx, ranges, _) ← Backend.buildCtx f
  let requests ← allocationRequests f ranges
  pure (finishCtx ctx ranges (allocateRequests ctx.valTy.size ctx.insts.size requests))

inductive Node where
  | original (block : Nat)
  | edge (pred successorIndex target : Nat)
  deriving DecidableEq, Repr, Inhabited

def destinations : Clif.Terminator → List (Nat × List Clif.TryArg)
  | .jump bc => [(bc.block, bc.args.map .val)]
  | .brif _ t e => [(t.block, t.args.map .val), (e.block, e.args.map .val)]
  | .brTable _ d tbl => (d :: tbl).map fun bc => (bc.block, bc.args.map .val)
  | .tryCall _ _ et | .tryCallIndirect _ _ et => et.dests.map fun bc => (bc.block, bc.args)
  | _ => []

structure Order where
  nodes : Array Node
  successors : Array (Array Nat)
  deriving Inhabited, Repr

/-- Stock's lowered block order: reachable source RPO, with each source block's
critical edges immediately after it. Predecessor counts include duplicate edges
and unreachable predecessors, matching `BlockLoweringOrder::new`. -/
def blockOrder (f : Clif.Function) : Except String Order := do
  let source ← f.blocks.toArray.mapM fun b =>
    (destinations b.term).toArray.mapM fun (id, _) =>
      match f.blocks.findIdx? (·.id == id) with
      | some i => pure i
      | none => throw s!"unknown block{id}"
  let mut indegree := Array.replicate f.blocks.length 0
  for ss in source do
    for s in ss do indegree := indegree.modify s (· + 1)
  let mut nodes : Array Node := #[]
  for bi in rpo source do
    nodes := nodes.push (.original bi)
    let term := f.blocks[bi]!.term
    let force := match term with | .brTable .. | .tryCall .. | .tryCallIndirect .. => true | _ => false
    if force || source[bi]!.size > 1 then
      for (s, k) in source[bi]!.zipIdx do
        if indegree[s]! > 1 then nodes := nodes.push (.edge bi k s)
  let label (node : Node) : Except String Nat :=
    match nodes.findIdx? (· == node) with
    | some i => pure i
    | none => throw "missing lowered block"
  let successors ← nodes.mapM fun
    | .edge _ _ s => return #[← label (.original s)]
    | .original bi => source[bi]!.mapIdxM fun k s =>
      if nodes.contains (.edge bi k s) then label (.edge bi k s) else label (.original s)
  pure { nodes, successors }

inductive Decision where
  | emitted | omitted | sunk | opportunistic
  deriving DecidableEq, Repr, Inhabited

/-- A schedule entry records the call and its before/after states, including
emissions, demands, aliases and memory color. Omitted entries make no ISLE call. -/
structure Step where
  block : Nat
  inst : Nat
  decision : Decision
  before : State
  after : State
  results : List (List Reg) := []
  rules : List RuleId := []
  /-- Raw forward-ordered chunk before final alias resolution. -/
  emitted : Array MInst := #[]
  deriving Inhabited, DecidableEq

/-- One source instruction's backward-scan transition. Branch terminators are
scanned for their color after their separate lowering, producing no second step.
`emitted` is a forward-ordered prefix to prepend to the block's accumulated code. -/
structure Scan where
  state : State
  step : Option Step
  emitted : Array MInst := #[]
  deriving Inhabited, DecidableEq

/-- A backward-scan event, including the embedding used for this block. These
records are replay inputs; whole-function certification must also establish
their source context, order and connection to the assembled output. -/
structure ScanEvent where
  ctx : Ctx
  block : Nat
  inst : Nat
  termInst : Nat
  isBranch : Bool
  input : State
  output : Scan

structure ScanRecord where
  inst : Nat
  input : State
  output : Scan
  deriving Inhabited, DecidableEq

/-- A complete backward scan: records remain in scan order, while `code` keeps
each emitted chunk in forward order and puts earlier source chunks first. -/
structure BlockScan where
  state : State
  records : List ScanRecord
  code : Array MInst
  deriving Inhabited, DecidableEq

structure BlockScanEvent where
  ctx : Ctx
  block : Nat
  termInst : Nat
  isBranch : Bool
  indices : List Nat
  input : State
  output : BlockScan

structure Result where
  ctx : Ctx
  initial : State
  final : State
  order : Order
  code : VCode
  /-- One argument vector for each successor edge, in `order.successors` order. -/
  edgeArgs : Array (Array (Array Reg))
  schedule : Array Step
  scans : Array ScanEvent := #[]
  blockScans : Array BlockScanEvent := #[]

def commitOpportunisticValues (ctx : Ctx) (values : List Nat) (st : State) :
    Except String State :=
  values.foldlM (fun s v => do
    if let some o := s.opportunistic[v]! then
      let some dst := ctx.valueReg? v | throw s!"unknown v{v}"
      let [src] := o.regs | throw "multi-register opportunistic definition"
      let next ← s.setAlias dst src
      pure { next with opportunistic := next.opportunistic.set! v none }
    else pure s) st

def commitOpportunistic (ctx : Ctx) (block inst : Nat) (st : State) :
    Except String (Option State) := do
  let values := ctx.insts[inst]!.results
  if !values.all (fun v => st.demand[v]! == 0 ||
      (st.opportunistic[v]!).any (fun o => o.block == block && o.count == st.demand[v]!)) then
    return none
  return some (← commitOpportunisticValues ctx values st)

def branchArgs (ctx : Ctx) (st : State) (block index : Nat) :
    Except String (Array Reg × State) := do
  let b := ctx.func.blocks[block]!
  let some (id, args) := (destinations b.term)[index]? | throw "missing successor"
  let some target := ctx.func.block? id | throw s!"unknown block{id}"
  if args.length != target.params.length then throw s!"block{id}: argument count"
  let ti := (st.instBlock.findIdx? (· == block)).getD 0 + b.body.length
  let (rets, pays) := st.tryRegs[ti]!
  let nh := match b.term with
    | .tryCall _ _ et | .tryCallIndirect _ _ et => et.handlers.length
    | _ => 0
  let mut s := st
  let mut regs := #[]
  for a in args do
    let r ← match a with
      | .val v =>
        let some r := ctx.valueReg? v | throw s!"unknown value v{v}"
        s := s.mark v
        pure r
      | .ret i =>
        if index < nh then throw "try_call return on exception edge"
        let some r := rets[i]? | throw "try_call return index"
        pure r
      | .exn i =>
        if index == nh then throw "try_call payload on normal edge"
        let some r := pays[i]? | throw "try_call payload index"
        pure r
    regs := regs.push r
  pure (regs, s)

/-- Reset scan-local state without changing demands, aliases or allocations. -/
def scanState (st : State) (i : Nat) : State :=
  let st := { st with current := some i, base.emitted := #[] }
  if st.entryColor[i]! != 0 then { st with color := some st.entryColor[i]! } else st

/-- A successful root call, with its output aliases/copies installed. -/
structure Emission where
  state : State
  code : Array MInst
  results : List (List Reg)
  rules : List RuleId

/-- Bind selected outputs in order. Virtual results record aliases; physical
results append copies after the rule's emitted instruction sequence. -/
def bindResults (ctx : Ctx) (pairs : List (Nat × List Reg)) (next : State) :
    Except String (State × Array MInst) :=
  pairs.foldlM (fun (st, extra) (v, rs) => do
    let some vr := ctx.valueReg? v | throw s!"unknown value v{v}"
    match rs with
    | [r@(.vreg ..)] => pure (← st.setAlias vr r, extra)
    | [r] => pure (st, extra.push (.mov .size64 vr r))
    | _ => throw "multi-register result") (next, #[])

def emitInstruction (ctx : Ctx) (i : Nat) (before : State) : Except String Emission := do
  let info := ctx.insts[i]!
  let (out, next, fired) ← runTerm ctx "lower" [.inst i] before
  let some (.regsVec rss) := out | throw s!"no lowering rule for instruction {i}"
  if rss.length != info.results.length && !info.results.isEmpty then
    throw "lowering produced a wrong number of results"
  let (st, extra) ← bindResults ctx (info.results.zip rss) next
  pure ⟨st, st.base.emitted ++ extra, rss, fired⟩

def Emission.scan (emission : Emission) (block i : Nat) (before : State) : Scan :=
  ⟨emission.state,
    some ⟨block, i, .emitted, before, emission.state,
      emission.results, emission.rules, emission.code⟩, emission.code⟩

/-- The stock driver's single-instruction transition, shared by compilation and
schedule replay. `ctx` contains the current block's terminator and try-call data.
The returned step records the state immediately before and after its decision. -/
def scanInstruction (ctx : Ctx) (block i ti : Nat) (isBranch : Bool) (input : State) :
    Except String Scan := do
  if input.sunk[i]! then
    return ⟨input, some ⟨block, i, .sunk, input, input, [], [], #[]⟩, #[]⟩
  let before := scanState input i
  if i == ti && isBranch then return ⟨before, none, #[]⟩
  let info := ctx.insts[i]!
  let mandatory := if i == ti then true else info.clif.any mustLower
  if !mandatory && !info.results.any (fun v => before.demand[v]! != 0) then
    return ⟨before, some ⟨block, i, .omitted, before, before, [], [], #[]⟩, #[]⟩
  if before.entryColor[i]! == 0 && !mandatory then
    if let some next ← commitOpportunistic ctx block i before then
      return ⟨next, some ⟨block, i, .opportunistic, before, next, [], [], #[]⟩, #[]⟩
  let emission ← emitInstruction ctx i before
  pure (emission.scan block i before)

/-- Structural reference for a complete scan, independent of ISLE evaluation. -/
def runScansRef (exec : Nat → State → Except String Scan) :
    List Nat → State → Except String BlockScan
  | [], input => .ok ⟨input, [], #[]⟩
  | i :: rest, input => do
    let scan ← exec i input
    let tail ← runScansRef exec rest scan.state
    pure ⟨tail.state, ⟨i, input, scan⟩ :: tail.records, tail.code ++ scan.emitted⟩

/-- Tail-recursive implementation: avoid a native stack frame per instruction. -/
def runScansAux (exec : Nat → State → Except String Scan) :
    List Nat → State → List ScanRecord → Array MInst → Except String BlockScan
  | [], input, revRecords, code => .ok ⟨input, revRecords.reverse, code⟩
  | i :: rest, input, revRecords, code => do
    let scan ← exec i input
    runScansAux exec rest scan.state (⟨i, input, scan⟩ :: revRecords) (scan.emitted ++ code)

def runScans (exec : Nat → State → Except String Scan) (indices : List Nat) (input : State) :
    Except String BlockScan := runScansAux exec indices input [] #[]

def scanBlock (ctx : Ctx) (block ti : Nat) (isBranch : Bool) (indices : List Nat)
    (input : State) : Except String BlockScan :=
  runScans (fun i => scanInstruction ctx block i ti isBranch) indices input

/-- Outgoing argument collection in successor order. Critical-edge nodes take
ownership of their vectors when those nodes are lowered separately. -/
def outgoingStep (ctx : Ctx) (order : Order) (bi : Nat)
    (acc : State × Array (Array Reg)) (target : Nat × Nat) :
    Except String (State × Array (Array Reg)) := do
  match order.nodes[target.1]! with
  | .edge .. => pure (acc.1, acc.2.push #[])
  | _ =>
    let (args, next) ← branchArgs ctx acc.1 bi target.2
    pure (next, acc.2.push args)

def collectOutgoing (ctx : Ctx) (order : Order) (bi : Nat) (targets : Array Nat)
    (input : State) : Except String (State × Array (Array Reg)) :=
  targets.zipIdx.toList.foldlM (outgoingStep ctx order bi) (input, #[])

structure BranchEmission where
  state : State
  code : Array MInst
  step : Step
  rules : List RuleId

/-- Replace the final call with the stock exception-table terminator. -/
def branchCode (f : Clif.Function) (t : Clif.Terminator) (targets : Array Nat)
    (code : Array MInst) : Except String (Array MInst) := do
  match t with
  | .tryCall _ _ et | .tryCallIndirect _ _ et =>
    let (sig, items) ← exnTableOpnd f et
    let some info := tryInfoOf sig items targets.toList | throw "try_call successor count"
    let info := { info with rets := sig.returns.length }
    let some (.call c) := code.back? | throw "try_call lowering does not end in a call"
    pure (code.pop.push (.tryCall c info))
  | _ => pure code

/-- Lower the separately emitted branch terminator, retaining its real state
transition before collecting demands or scanning the body. -/
def emitBranch (ctx : Ctx) (f : Clif.Function) (t : Clif.Terminator)
    (bi ti : Nat) (targets : Array Nat) (input : State) : Except String BranchEmission := do
  let before := { input with current := some ti, color := none, base.emitted := #[] }
  let (out, next, fired) ← runTerm ctx "lower_branch" [.inst ti, .labels targets.toList] before
  if out.isNone then throw s!"no lowering rule for terminator {repr t}"
  let code ← branchCode f t targets next.base.emitted
  pure ⟨next, code, ⟨bi, ti, .emitted, before, next, [], fired, code⟩, fired⟩

structure LoweredBlockCore where
  state : State
  code : Array MInst
  outgoing : Array (Array Reg)
  branch : Option BranchEmission
  scan : BlockScanEvent

/-- All state-changing operations for one original block, in stock order:
branch root, outgoing demands, then complete backward scan. Entry argument
materialization and block assembly consume this result without changing state. -/
def lowerBlockCore (ctx : Ctx) (order : Order) (f : Clif.Function)
    (b : Clif.Block) (bi start stop : Nat) (data : V) (targets : Array Nat)
    (input : State) : Except String LoweredBlockCore := do
  let ti := stop - 1
  let termCtx := { ctx with
    insts := ctx.insts.set! ti ⟨data, [], [], none⟩
    tryRegs := input.tryRegs[ti]! }
  let isBranch := match b.term with | .ret .. | .trap .. => false | _ => true
  let branch ← if isBranch then
    some <$> emitBranch termCtx f b.term bi ti targets input else pure none
  let beforeEdges := branch.map (·.state) |>.getD input
  let (next, outgoing) ← collectOutgoing ctx order bi targets beforeEdges
  let beforeScan := { next with color := some next.endColor[bi]! }
  let indices := ((Array.range (stop - start)).map (start + ·)).reverse.toList
  let bodyScan ← scanBlock termCtx bi ti isBranch indices beforeScan
  pure ⟨bodyScan.state, bodyScan.code ++ (branch.map (·.code) |>.getD #[]), outgoing,
    branch, ⟨termCtx, bi, ti, isBranch, indices, beforeScan, bodyScan⟩⟩

/-- Mutable outputs of the reverse lowered-block traversal. -/
structure DriverState where
  state : State
  blocks : Array VBlock
  edgeArgs : Array (Array (Array Reg))
  schedule : Array Step
  scans : Array ScanEvent
  blockScans : Array BlockScanEvent
  rules : Array RuleId

/-- Entry materialization and source parameters do not change lowering state. -/
def assembleOriginalBlock (ctx : Ctx) (f : Clif.Function) (b : Clif.Block)
    (bi label : Nat) (targets : Array Nat) (outgoing : Array (Array Reg))
    (paramBytes : List Nat) (uses : Array UseState) (bodyCode : Array MInst) :
    Except String VBlock := do
  let mut code := bodyCode
  if bi == 0 then
    let (locs, _) ← sigArgLocs f.sig
    let mut pairs := []
    let mut loads := #[]
    for (((v, _), loc), bytes) in (b.params.zip locs).zip paramBytes do
      if uses[v]! == .unused then continue
      let some r := ctx.valueReg? v | throw s!"unknown value v{v}"
      match loc with
      | .reg p => pairs := pairs ++ [(r, p)]
      | .stack off => loads := loads.push (.load (loadOpOfBytes bytes) r (.fpOffset (16 + off)) trustedFlags)
    if !pairs.isEmpty then code := #[.args pairs] ++ loads ++ code
    else code := loads ++ code
  let params ← if bi == 0 then pure #[] else
    b.params.toArray.mapM fun (v, _) =>
      match ctx.valueReg? v with
      | some r => pure r
      | none => throw s!"unknown value v{v}"
  let args := if targets.size == 1 then outgoing[0]! else #[]
  pure { label, insts := code, params, branchArgs := args }

/-- Append diagnostics in their original scan order, retaining the core's state. -/
def recordCore (input : DriverState) (lowered : LoweredBlockCore) (bi stop : Nat) :
    DriverState :=
  let schedule := match lowered.branch with
    | some branch => input.schedule.push branch.step
    | none => input.schedule
  let rules := match lowered.branch with
    | some branch => input.rules ++ branch.rules.toArray
    | none => input.rules
  let records := lowered.scan.output.records.foldl (fun (schedule, scans, rules) record =>
    let scans := scans.push ⟨lowered.scan.ctx, bi, record.inst, stop - 1,
      lowered.scan.isBranch, record.input, record.output⟩
    match record.output.step with
    | some step => (schedule.push step, scans, rules ++ step.rules.toArray)
    | none => (schedule, scans, rules)) (schedule, input.scans, rules)
  { input with
    state := lowered.state
    schedule := records.1
    scans := records.2.1
    blockScans := input.blockScans.push lowered.scan
    rules := records.2.2 }

/-- One transition of the actual reverse block traversal. -/
def lowerNode (ctx : Ctx) (ranges : Array (Nat × Nat)) (order : Order)
    (f : Clif.Function) (paramBytes : List Nat) (label : Nat) (input : DriverState) :
    Except String DriverState := do
  let targets := order.successors[label]!
  match order.nodes[label]! with
  | .edge pred k _ =>
    let (args, next) ← branchArgs ctx input.state pred k
    pure { input with
      state := next
      blocks := input.blocks.set! label { label, insts := #[.jump targets[0]!], branchArgs := args },
      edgeArgs := input.edgeArgs.set! label #[args] }
  | .original bi =>
    let b := f.blocks[bi]!
    let (start, stop) := ranges[bi]!
    let data ← match b.term with
      | .tryCall .. | .tryCallIndirect .. => tryCallData f b.term
      | _ => termData (abiTerm f b.term)
    if b.term matches .ret .. && (sretRet f).isEmpty && sigRets f.sig != f.sig.returns then
      throw "sret parameter is not an entry-block parameter"
    let lowered ← lowerBlockCore ctx order f b bi start stop data targets input.state
    let block ← assembleOriginalBlock ctx f b bi label targets lowered.outgoing
      paramBytes lowered.state.uses lowered.code
    pure { recordCore input lowered bi stop with
      blocks := input.blocks.set! label block,
      edgeArgs := input.edgeArgs.set! label lowered.outgoing }

def lower (f : Clif.Function) : Except String Result := do
  if !aapcsConv f.sig.callConv then throw s!"calling convention {repr f.sig.callConv}"
  let paramBytes ← sigParamBytes f.sig
  if f.sig.returns.any (·.ty == .i128) then throw "i128 return value"
  if f.sig.params.any (·.purpose == .sret) && !f.sig.returns.isEmpty then
    throw "sret parameter together with return values"
  if (retRegs (sigRets f.sig).length).isNone then throw "more than 8 return values"
  let (ctx, ranges, initial) ← buildCtx f
  let order ← blockOrder f
  let driver0 : DriverState := {
    state := initial
    blocks := Array.replicate order.nodes.size default
    edgeArgs := Array.replicate order.nodes.size #[]
    schedule := #[], scans := #[], blockScans := #[], rules := #[] }
  let driver ← (Array.range order.nodes.size).reverse.toList.foldlM
    (fun input label => lowerNode ctx ranges order f paramBytes label input) driver0
  let st := driver.state
  let mut blocks := driver.blocks
  let mut edgeArgs := driver.edgeArgs
  let resolve := Backend.lowerFunction.resolve st.alias (st.alias.size + 1)
  blocks := blocks.map fun b => { b with
    insts := b.insts.map (·.mapRegs resolve)
    params := b.params.map resolve
    branchArgs := b.branchArgs.map resolve }
  edgeArgs := edgeArgs.map fun args => args.map fun rs => rs.map resolve
  let (_, slotBytes) := slotLayout f.slots
  pure {
    ctx := ctx
    initial := initial
    final := st
    order := order
    edgeArgs := edgeArgs
    schedule := driver.schedule
    scans := driver.scans
    blockScans := driver.blockScans
    code := { name := f.name, blocks, classes := st.base.classes,
              slotBytes, outgoing := st.base.outgoing, rulesFired := driver.rules } }

end Backend.Stock
