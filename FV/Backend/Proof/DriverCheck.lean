import FV.Backend.Isel
import FV.Compile.Subset
import Std.Data.HashMap.Basic
import Std.Data.HashSet.Basic

/-!
# The lowering validator (M7): `lowerCheck f vc`

An executable check, run after `lowerFunction f = .ok vc` (like `checkAlloc` after the
allocator), whose acceptance implies M7's lowering obligations (`LoweringObligations f vc`,
`loweringObligations_of_check` in `DriverCheckSound.lean`): the structure of the VCode
(`LowerShape`) and an SSA availability certificate (`Cert`).

The validator does not trust `lowerFunction`'s loops. It

1. runs `buildCtx f` and re-runs the ISLE lowering calls the way `lowerFunction` makes them
   (`lowBlocks`: per block, `lower` on every statement from the previous state with nothing
   emitted, then `lower`/`lower_branch` on the terminator in the terminator context, with the
   same edge-block labels), recording every call's states and results;
2. computes the alias resolution `gn` from the recorded result registers (`gnTable`, a table
   of the CLIF values' resolved vregs) and the class-preserving renaming `R = renOf gn`;
3. computes the available values `A` by a must-dataflow (`inFix`, `availOf`: a value is
   available at a block entry if it is available at the end of every predecessor; an untrusted
   worklist computation, whose result the certificate check validates);
4. checks, with `decide`/`all` over finite data, every field of `LowerShape` and `Cert` that is
   not true by construction: the context invariants (`CtxInv`), the VCode blocks are exactly
   the renamed recorded code (`vb.insts = pre ++ segments ++ terminator segment`), labels,
   parameters, branch arguments, edge blocks, and the local certificate conditions (operands
   available, results fresh and uniquely defined, no available value's register written by a
   statement's lowering, closure under definitions, edges, types).

The certificate check is near-linear: membership in `availOf f In bi j` is decided in constant
time (`Avail.mem`: hash sets of the entry values, a value's defining statement from
`ctx.defInst?`), and a condition on every value available before some statement of a block is
checked once per value, at the first such statement (`certBlockOk`).

This file is executable only (imports `FV.Backend.Isel`), so the compiler can run it.
-/

namespace Backend.Proof.Driver

open Backend

/-! ## Shapes shared with the proof (`LowerShape`) -/

/-- `lowerFunction`'s block index of block id `b`. -/
def blockIdx? (f : Clif.Function) (b : Clif.BlockId) : Option Nat := f.blocks.findIdx? (·.id == b)

/-- One statement's lowering: state before (nothing emitted), result registers, state after. -/
structure SLow where
  st : LState
  rss : List (List Reg)
  st' : LState

/-- What a `try_call` terminator's lowering records: its `try_call_info`, the exception table's
signature and item kinds (`exnTableOpnd`), the return/payload vregs (`tryRegsOf`, allocated
from the terminator's state) and the state after allocating them (the rule's start state). -/
structure TryLow where
  info : TryInfo
  sig : Clif.Signature
  items : List (Option Nat)
  regs : List Reg × List Reg
  st1 : LState

/-- One block's lowering. -/
structure BLow where
  /-- index of the block's first statement in `ctx.insts` -/
  start : Nat
  sl : List SLow
  /-- terminator: `InstructionData`, successor labels, states before/after -/
  data : V
  targets : List Label
  tst : LState
  tst' : LState
  /-- a `try_call` terminator's recorded lowering (`none` for the others) -/
  tl : Option TryLow

/-- `lowerFunction`'s `mov` for a result the rules returned in a real register. -/
def extraOf (results : List Nat) (rss : List (List Reg)) : List MInst :=
  (results.zip rss).filterMap fun (r, rs) => match rs with
    | [.vreg ..] => none
    | [out] => some (.mov .size64 (.vreg r .int) out)
    | _ => none

/-- The successors of a terminator (`lowerFunction`'s `dests`). -/
def dests : Clif.Terminator → List Clif.BlockCall
  | .jump bc => [bc]
  | .brif _ t e => [t, e]
  | .brTable _ d tbl => d :: tbl
  | _ => []

/-- The successor block ids of a terminator (a `try_call`'s: the handlers, then the normal
return). -/
def succIds : Clif.Terminator → List Clif.BlockId
  | .tryCall _ _ et | .tryCallIndirect _ _ et => et.dests.map (·.block)
  | t => (dests t).map (·.block)

/-- `lowerFunction`'s replacement of the call a `try_call` rule emits last by the `tryCall`
terminator (`tryFix`). -/
def fixTry : Option TryLow → List MInst → List MInst
  | some T, ms => tryFix T.info ms
  | none, ms => ms

/-- The context `lowerFunction` lowers a terminator in (its data filled in). -/
def termCtx (ctx : Ctx) (ti : Nat) (data : V) : Ctx :=
  { ctx with insts := ctx.insts.set! ti ⟨data, [], [], none⟩ }

/-- The ISLE root term and arguments `lowerFunction` uses for a terminator. -/
def termCall (t : Clif.Terminator) (ti : Nat) (targets : List Label) : String × List V :=
  match t with
  | .ret _ | .trap _ => ("lower", [.inst ti])
  | _ => ("lower_branch", [.inst ti, .labels targets])

/-- The value operands of a CLIF instruction. -/
def instArgs : Clif.Inst → List Clif.ValueId
  | .iconst .. | .stackAddr .. | .fence | .nop | .symbolValue .. | .tlsValue .. => []
  | .unary _ _ x | .bmask _ x | .extend _ _ x | .ireduce _ x | .isplit _ x
  | .load _ _ _ x _ | .atomicLoad _ _ x | .bitcast _ _ x | .trapz x _ | .trapnz x _ => [x]
  | .binary _ _ x y | .div _ _ x y | .overflow _ _ x y | .icmp _ _ x y
  | .uaddOverflowTrap _ x y _ | .iconcat _ x y | .store _ _ _ x y _ | .atomicRmw _ _ _ x y
  | .atomicStore _ _ x y => [x, y]
  | .carry _ _ x y z | .select _ x y z | .selectSpectreGuard _ x y z | .bitselect _ x y z
  | .atomicCas _ _ x y z => [x, y, z]
  | .call _ args => args
  | .callIndirect _ callee args => callee :: args
  | .funcAddr _ _ => []

/-- The value operands of a terminator. -/
def termArgs : Clif.Terminator → List Clif.ValueId
  | .jump bc => bc.args
  | .brif c t e => c :: t.args ++ e.args
  | .brTable x d tbl => x :: d.args ++ tbl.flatMap (·.args)
  | .ret xs => xs
  | .returnCall _ args => args
  | .trap _ => []
  | .tryCall _ args et => args ++ et.vals
  | .tryCallIndirect callee args et => callee :: args ++ et.vals

section
variable (f : Clif.Function) (vc : VCode) (ctx : Ctx) (st0 : LState) (R : Reg → Reg)
  (gn : Nat → Nat) (bl : List BLow)

/-- The VCode segment of statement `j` of block `bi`. -/
def seg (bi j : Nat) : List MInst :=
  match f.blocks[bi]?, bl[bi]? with
  | some B, some L =>
    match B.body[j]?, L.sl[j]? with
    | some stm, some sl => (sl.st'.emitted.toList ++ extraOf stm.results sl.rss).map (·.mapRegs R)
    | _, _ => []
  | _, _ => []

/-- The entry block's parameters with their locations and byte sizes (`sigArgLocs`,
`sigParamBytes`, zipped as `lowerFunction`'s `gen_arg_setup` zips them). -/
def entryParams (B : Clif.Block) : List (((Clif.ValueId × Clif.Ty) × ArgLoc) × Nat) :=
  (B.params.zip (locsOf f.sig)).zip (match sigParamBytes f.sig with | .ok b => b | .error _ => [])

/-- The `Args` pair of a register-passed parameter (x0.. in order, an `sret` parameter in x8). -/
def entryRegOf (q : ((Clif.ValueId × Clif.Ty) × ArgLoc) × Nat) : Option (Reg × Reg) :=
  match q.1.2 with
  | .reg p => some (R (.vreg q.1.1.1 .int), p)
  | .stack _ => none

/-- The load of a stack-passed parameter from the caller's outgoing area (`fp + 16 + off`:
above the saved fp/lr pair). -/
def entryLoadOf (q : ((Clif.ValueId × Clif.Ty) × ArgLoc) × Nat) : Option MInst :=
  match q.1.2 with
  | .stack off =>
    some (.load (loadOpOfBytes q.2) (R (.vreg q.1.1.1 .int)) (.fpOffset (16 + off)) trustedFlags)
  | .reg _ => none

/-- The `Args` pairs of the register-passed parameters. -/
def entryRegs (B : Clif.Block) : List (Reg × Reg) := (entryParams f B).filterMap (entryRegOf R)

/-- The loads of the stack-passed parameters. -/
def entryLoads (B : Clif.Block) : List MInst := (entryParams f B).filterMap (entryLoadOf R)

/-- The entry block's code before its statements (`gen_arg_setup`): the `Args` of the
register-passed parameters, then a load of each stack-passed one. -/
def pre (bi : Nat) : List MInst :=
  match bi, f.blocks[bi]? with
  | 0, some B => .args (entryRegs f R B) :: entryLoads f R B
  | _, _ => []

/-- The terminator's segment. -/
def tseg (bi : Nat) : List MInst :=
  match bl[bi]? with
  | some L => (fixTry L.tl L.tst'.emitted.toList).map (·.mapRegs R)
  | none => []

/-- Index in block `bi` where statement `j`'s segment starts. -/
def pos (bi j : Nat) : Nat :=
  (pre f R bi).length + ((List.range j).map fun j' => (seg f R bl bi j').length).sum

end

/-! ## Re-running the lowering calls -/

/-- The result registers of a `lower` call. -/
def regsOf : Option V → Option (List (List Reg))
  | some (.regsVec rss) => some rss
  | _ => none

/-- An ISLE call of the driver: `lower [.inst ii]` on a statement. -/
abbrev StmtCall := Nat → LState → Except String (Option V × LState × List Isle.RuleId)

/-- An ISLE call of the driver on a terminator (slot `ti`, data, terminator, targets). -/
abbrev TermCallF := Nat → V → Clif.Terminator → List Label → LState →
  Except String (Option V × LState × List Isle.RuleId)

/-- The driver's statement call in context `ctx`. -/
def stmtCall (ctx : Ctx) : StmtCall := fun ii s => runTerm ctx "lower" [.inst ii] s

/-- The driver's terminator call in context `ctx`. -/
def termCallF (ctx : Ctx) : TermCallF := fun ti data t targets s =>
  runTerm (termCtx ctx ti data) (termCall t ti targets).1 (termCall t ti targets).2 s

/-- An ISLE call of the driver on a `try_call` terminator (slot `ti`, data, return/payload
vregs, targets). -/
abbrev TryCallF := Nat → V → List Reg × List Reg → List Label → LState →
  Except String (Option V × LState × List Isle.RuleId)

/-- The context `lowerFunction` lowers a `try_call` in: its data filled in, its return and
payload vregs (`gen_try_call_rets`). -/
def tryCtx (ctx : Ctx) (ti : Nat) (data : V) (trs : List Reg × List Reg) : Ctx :=
  { termCtx ctx ti data with tryRegs := trs }

/-- The driver's `try_call` call in context `ctx`. -/
def tryCallF (ctx : Ctx) : TryCallF := fun ti data trs targets s =>
  runTerm (tryCtx ctx ti data trs) "lower_branch" [.inst ti, .labels targets] s

/-- `lower` on the statements `ss` (instructions `ii, ii+1, …`), each from the previous state
with nothing emitted (`lowerFunction`'s body loop). -/
def lowStmts (call : StmtCall) : Nat → List Clif.Stmt → LState → Option (List SLow × LState)
  | _, [], st => some ([], st)
  | ii, _ :: ss, st =>
    let s0 : LState := { st with emitted := #[] }
    match call ii s0 with
    | .ok (out, st', _) =>
      match regsOf out with
      | some rss =>
        (lowStmts call (ii + 1) ss { st' with emitted := #[] }).map fun (sls, stE) =>
          (⟨s0, rss, st'⟩ :: sls, stE)
      | none => none
    | .error _ => none

/-- Successor labels of a `brif`/`br_table` (edge blocks for arguments get fresh labels from
`nl`, in order). -/
def edgeTargets (f : Clif.Function) : List Clif.BlockCall → Nat → Option (List Label × Nat)
  | [], nl => some ([], nl)
  | bc :: bcs, nl =>
    match blockIdx? f bc.block with
    | none => none
    | some tl =>
      if bc.args.isEmpty then (edgeTargets f bcs nl).map fun (ts, nl') => (tl :: ts, nl')
      else (edgeTargets f bcs (nl + 1)).map fun (ts, nl') => (nl :: ts, nl')

/-- `lowerFunction`'s successor labels of a terminator. -/
def targetsOf (f : Clif.Function) (t : Clif.Terminator) (nl : Nat) : Option (List Label × Nat) :=
  match t with
  | .jump bc => (blockIdx? f bc.block).map fun tl => ([tl], nl)
  | t => edgeTargets f (dests t) nl

/-- `lowerFunction`'s successor labels of a `try_call`: an edge block for every successor
(labels from `nl`, in order). -/
def tryTargets (f : Clif.Function) (ds : List Clif.TryDest) (nl : Nat) : Option (List Label × Nat) :=
  if ds.all (fun d => (blockIdx? f d.block).isSome) then
    some ((List.range ds.length).map (nl + ·), nl + ds.length)
  else none

/-- The lowering of a terminator `t` at slot `ti` from state `tst` (next edge label `nl`), as
`lowerFunction` makes it: its data, successor labels, `try_call` record, final state and next
edge label. -/
def lowTerm (f : Clif.Function) (tcall : TermCallF) (ycall : TryCallF) (ti : Nat)
    (t : Clif.Terminator) (tst : LState) (nl : Nat) :
    Option (V × List Label × Option TryLow × LState × Nat) :=
  match t with
  | .tryCall _ _ et | .tryCallIndirect _ _ et =>
    match tryCallData f t, exnTableOpnd f et, tryTargets f et.dests nl with
    | .ok data, .ok (sig, items), some (targets, nl') =>
      match tryRegsOf sig tst with
      | some (trs, st1) =>
        match tryInfoOf sig items targets with
        | some info =>
          match ycall ti data trs targets { st1 with emitted := #[] } with
          | .ok (some _, tst', _) => some (data, targets, some ⟨info, sig, items, trs, st1⟩, tst', nl')
          | _ => none
        | none => none
      | none => none
    | _, _, _ => none
  | t =>
    match termData (abiTerm f t), targetsOf f t nl with
    | .ok data, some (targets, nl') =>
      match tcall ti data t targets tst with
      | .ok (some _, tst', _) => some (data, targets, none, tst', nl')
      | _ => none
    | _, _ => none

/-- The lowering of the blocks `Bs` (first instruction index `start`, state `st`, next edge
label `nl`), as `lowerFunction` makes it. -/
def lowBlocks (f : Clif.Function) (call : StmtCall) (tcall : TermCallF) (ycall : TryCallF) :
    Nat → List Clif.Block → LState → Nat → Option (List BLow)
  | _, [], _, _ => some []
  | start, B :: Bs, st, nl =>
    match lowStmts call start B.body st with
    | none => none
    | some (sls, stE) =>
      let ti := start + B.body.length
      let tst : LState := { stE with emitted := #[] }
      match lowTerm f tcall ycall ti B.term tst nl with
      | some (data, targets, tl, tst', nl') =>
        (lowBlocks f call tcall ycall (ti + 1) Bs { tst' with emitted := #[] } nl').map
          (⟨start, sls, data, targets, tst, tst', tl⟩ :: ·)
      | none => none

/-! ## Alias resolution -/

/-- The aliases `lowerFunction` records: result `r` ↦ the vreg `out` the rules returned. -/
def aliasOf (f : Clif.Function) (bl : List BLow) : List (Nat × Nat) :=
  (f.blocks.zip bl).flatMap fun (B, L) => (B.body.zip L.sl).flatMap fun (stm, sl) =>
    (stm.results.zip sl.rss).filterMap fun (r, rs) => match rs with
      | [.vreg out _] => some (r, out)
      | _ => none

/-- The aliases as a hash map (the first entry of a key wins, as `List.lookup`). -/
def aliasMap (al : List (Nat × Nat)) : Std.HashMap Nat Nat :=
  al.foldr (fun (r, o) m => m.insert r o) {}

/-- Follow the alias chain of `n` (at most `k` steps). -/
def chase (m : Std.HashMap Nat Nat) : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => match m[n]? with
    | some o => chase m k o
    | none => n

/-- The resolved vreg numbers of the CLIF values `0, …, lo - 1` (each alias chain followed at
most `al.length + 1` steps). -/
def gnTable (lo : Nat) (al : List (Nat × Nat)) : Array Nat :=
  let m := aliasMap al
  Array.ofFn (n := lo) fun i => chase m (al.length + 1) i

/-- The resolved vreg number of `n` (from `gnTable`): temporaries (beyond the table) are never
aliased. -/
def gnAt (t : Array Nat) (n : Nat) : Nat := if h : n < t.size then t[n] else n

/-- The class-preserving renaming of `gn`. -/
def renOf (gn : Nat → Nat) : Reg → Reg
  | .vreg n c => .vreg (gn n) c
  | r => r

/-! ## Available values -/

/-- Results of the statements before statement `j`. -/
def defsBefore (B : Clif.Block) (j : Nat) : List Clif.ValueId := (B.body.take j).flatMap (·.results)

/-- Results of statement `j` and the later ones. -/
def defsFrom (B : Clif.Block) (j : Nat) : List Clif.ValueId := (B.body.drop j).flatMap (·.results)

/-- The values available before statement `j` of block `bi`, given the values `In` available
at block entries: parameters, entry values and earlier results, minus the block's own later
results. -/
def availOf (f : Clif.Function) (In : Array (List Clif.ValueId)) (bi j : Nat) : List Clif.ValueId :=
  match f.blocks[bi]? with
  | some B => (B.params.map (·.1) ++ In.getD bi [] ++ defsBefore B j).filter
      fun x => decide (x ∉ defsFrom B j)
  | none => []

/-- The operands of the instruction defining `x` (`[]` for a value without one, such as a block
parameter): what the closure condition of `Cert` requires to be available along with `x`. -/
def defArgs (ctx : Ctx) (x : Clif.ValueId) : List Clif.ValueId :=
  match ctx.defInst? x with
  | some d => match ctx.insts[d]? with
    | some info => match info.clif with
      | some cl => instArgs cl
      | none => []
    | none => []
  | none => []

/-- The values available at the block entries: the greatest solution, below the candidates
(the values of `f` that are not a parameter of the block and not renamed onto one; nothing at
the entry block), of the must-dataflow — a value is available at a block entry if it is available at the end of every
predecessor (a `try_call`'s edges to its handlers included) and so are the operands of its
definition (the closure condition of `Cert`; on unreachable blocks, whose entry no predecessor
constrains, it removes the values computed from the block's own results, e.g. cg_clif's dead
cleanup blocks). Computed by a worklist over (block, value) pairs, each removed at most once.
Untrusted: `certOk` checks the certificate it induces. -/
def inFix (f : Clif.Function) (ctx : Ctx) (gn : Nat → Nat) : Array (List Clif.ValueId) := Id.run do
  let fb := f.blocks.toArray
  let nb := fb.size
  let nv := ctx.valDef.size
  -- block index of a block id (the first block with that id, as `blockIdx?`)
  let bim : Std.HashMap Clif.BlockId Nat :=
    fb.zipIdx.foldl (fun m (B, i) => m.insertIfNew B.id i) {}
  let succs : Array (List Nat) := fb.map fun B => (succIds B.term).filterMap (bim[·]?)
  let preds : Array (List Nat) := succs.zipIdx.foldl
    (fun ps (ss, bi) => ss.foldl (fun ps s => ps.modify s (bi :: ·)) ps) (Array.replicate nb [])
  let pars : Array (Std.HashSet Nat) := fb.map fun B => Std.HashSet.ofList (B.params.map (·.1))
  let defs : Array (Std.HashSet Nat) :=
    fb.map fun B => Std.HashSet.ofList (B.body.flatMap (·.results))
  -- the values of `f` (parameters and results)
  let isVal : Array Bool := fb.foldl (fun a B =>
    let a := B.params.foldl (fun a p => a.setIfInBounds p.1 true) a
    B.body.foldl (fun a s => s.results.foldl (fun a r => a.setIfInBounds r true) a) a)
    (Array.replicate nv false)
  -- users[y]: the values whose definition reads `y`
  let users : Array (List Nat) := (List.range nv).foldl (fun us z =>
    (defArgs ctx z).foldl (fun us y => us.modify y (z :: ·)) us) (Array.replicate nv [])
  -- `inB[tl * nv + x]`: `x` is (still) available at the entry of block `tl`
  let mut inB : ByteArray := ByteArray.mk (Array.replicate (nb * nv) 0)
  for tl in [1:nb] do
    let P := pars[tl]!
    for x in [0:nv] do
      if isVal[x]! && !P.contains x && !P.contains (gn x) then
        inB := inB.set! (tl * nv + x) 1
  let has (inB : ByteArray) (tl x : Nat) : Bool := x < nv && inB.get! (tl * nv + x) != 0
  -- the pairs violating a constraint in the start state
  let mut work : List (Nat × Nat) := []
  for tl in [1:nb] do
    for x in [0:nv] do
      if has inB tl x then
        let outOk := preds[tl]!.all fun p =>
          pars[p]!.contains x || defs[p]!.contains x || has inB p x
        let a0Ok := (defArgs ctx x).all fun y =>
          (pars[tl]!.contains y || has inB tl y) && !defs[tl]!.contains y
        if !(outOk && a0Ok) then work := (tl, x) :: work
  -- remove them; a removed value that is neither a parameter nor a result of block `tl` leaves
  -- the end of `tl` (so the entries of its successors) and `tl`'s entry (so its users there)
  while true do
    match work with
    | [] => break
    | (tl, x) :: rest =>
      work := rest
      if has inB tl x then
        inB := inB.set! (tl * nv + x) 0
        if !pars[tl]!.contains x && !defs[tl]!.contains x then
          for s in succs[tl]! do
            if has inB s x then work := (s, x) :: work
          for z in users[x]! do
            if has inB tl z then work := (tl, z) :: work
  return (Array.range nb).map fun tl => (List.range nv).filter (has inB tl)

/-! ## The checks -/

/-- The result-type check of one instruction (`ctxOk`): a call's from its callee's declaration,
a `call_indirect`'s from its signature declaration (`CtxInv.resTys`). -/
def ctxResTysOk (f : Clif.Function) (info : IInfo) (i : Clif.Inst) : Bool :=
  match i.resultTypes (fun r => (f.extern? r).map (·.sig)) (f.sigDecls.lookup ·) with
  | some tys => decide (info.resTys = tys.map CTy.ofClif) &&
      decide (info.results.length = tys.length)
  | none => false

/-- `CtxInv f ctx` (M4's context facts), decided. -/
def ctxOk (f : Clif.Function) (ctx : Ctx) : Bool :=
  decide (ctx.func = f) &&
  ctx.insts.toList.all (fun info => match info.clif with
    | some i =>
      Compile.instE i &&
        ((match instData f i with
            | .ok d => d == info.data
            | .error _ => false) &&
          ctxResTysOk f info i)
    | none => true) &&
  (List.range ctx.valReg.size).all (fun x => match ctx.valueReg? x with
    | some r => decide (r = .vreg x .int)
    | none => true) &&
  (List.range ctx.valTy.size).all (fun x => match ctx.valueType? x with
    | some _ => decide (ctx.valueReg? x = some (.vreg x .int))
    | none => true) &&
  (List.range ctx.valDef.size).all (fun x => match ctx.defInst? x with
    | some d => match ctx.insts[d]? with
      | some info => decide (x ∈ info.results) && info.clif.isSome
      | none => false
    | none => true) &&
  decide (ctx.slotOff = (slotLayout f.slots).1) &&
  -- result and value types are `i8..i64` (`eCTys`)
  ctx.insts.toList.all (fun info => info.resTys.all fun t =>
    [CTy.int 8, .int 16, .int 32, .int 64].any fun u => decide (t = u)) &&
  (List.range ctx.valTy.size).all (fun x => match ctx.valueType? x with
    | some t => [CTy.int 8, .int 16, .int 32, .int 64].any fun u => decide (t = u)
    | none => true) &&
  ctx.insts.toList.all (fun info => match info.clif with
    | some (.load _ _ _ x _) | some (.store _ _ _ _ x _) | some (.atomicLoad _ _ x)
    | some (.atomicStore _ _ _ x) | some (.atomicRmw _ _ _ x _) | some (.atomicCas _ _ x _ _) =>
      decide (ctx.valueType? x = some (.int 64))
    | _ => true)

/-- The successor facts of `LowerShape` for block `B` (lowering `L`). For a `try_call`: an edge
block per successor, and the normal return's (the last) holds the `jump` with the return's
arguments (`normArgReg`; the landing pads are not checked: the theorem covers the normal
return only). -/
def succOk (f : Clif.Function) (vc : VCode) (R : Reg → Reg) (B : Clif.Block) (L : BLow) : Bool :=
  match B.term with
  | .jump bc => match blockIdx? f bc.block with
    | some tl => decide (L.targets = [tl])
    | none => false
  | .tryCall _ _ et | .tryCallIndirect _ _ et => decide (L.targets.length = et.dests.length) &&
    match blockIdx? f et.normal.block, L.targets.getLast?, L.tl with
    | some tl, some tlab, some T => match vc.blocks[tlab]? with
      | some eb => decide (eb.insts = #[.jump tl]) && decide (eb.params = #[]) &&
          decide (eb.branchArgs = (et.normal.args.map (normArgReg R T.regs.1)).toArray) &&
          -- the normal return passes values and results only
          et.normal.args.all fun
            | .val _ => true
            | .ret i => decide (i < T.sig.returns.length)
            | .exn _ => false
      | none => false
    | _, _, _ => false
  | t => decide (L.targets.length = (dests t).length) &&
    ((dests t).zip L.targets).all fun (bc, tlab) => match blockIdx? f bc.block with
      | none => false
      | some tl =>
        if bc.args = [] then decide (tlab = tl) else
        match vc.blocks[tlab]? with
        | some eb => decide (eb.insts = #[.jump tl]) && decide (eb.params = #[]) &&
            decide (eb.branchArgs = (bc.args.map fun a => R (.vreg a .int)).toArray)
        | none => false

/-- The per-statement facts of `LowerShape`. -/
def stmtOk (ctx : Ctx) (st0 : LState) (gn : Nat → Nat) (ii : Nat) (stm : Clif.Stmt) (sl : SLow) :
    Bool :=
  (match ctx.insts[ii]? with
    | some info => decide (info.clif = some stm.inst) && decide (info.results = stm.results)
    | none => false) &&
  sl.st.emitted.isEmpty && decide (st0.nextVreg ≤ sl.st.nextVreg) &&
  (stm.results.zip sl.rss).all fun (r, rs) => match rs with
    | [.vreg out _] => decide (gn r = gn out)
    | _ => true

/-- The per-block facts of `LowerShape`. -/
def blockOk (f : Clif.Function) (vc : VCode) (ctx : Ctx) (st0 : LState) (R : Reg → Reg)
    (gn : Nat → Nat) (bl : List BLow) (bi : Nat) (B : Clif.Block) (L : BLow) : Bool :=
  match vc.blocks[bi]? with
  | none => false
  | some vb =>
    decide (L.sl.length = B.body.length) &&
    (List.range B.body.length).all (fun j => match B.body[j]?, L.sl[j]? with
      | some stm, some sl => stmtOk ctx st0 gn (L.start + j) stm sl
      | _, _ => false) &&
    L.tst.emitted.isEmpty && decide (st0.nextVreg ≤ L.tst.nextVreg) &&
    decide (vb.insts.toList = pre f R bi ++ ((List.range B.body.length).map (seg f R bl bi)).flatten ++
      tseg R bl bi) &&
    !(tseg R bl bi).isEmpty &&
    decide (vb.params = (if bi = 0 then #[] else (B.params.map fun p => Reg.vreg p.1 .int).toArray)) &&
    decide (vb.branchArgs = (match B.term with
      | .jump bc => (bc.args.map fun a => R (.vreg a .int)).toArray
      | _ => #[])) &&
    succOk f vc R B L &&
    (match ctx.insts[L.start + B.body.length]? with
      | some info => info.data == .op .unit && info.results.isEmpty && info.resTys.isEmpty &&
          info.clif.isNone
      | none => false)

/-- `LowerShape f vc ctx st0 (renOf gn) gn bl`, decided (the rest holds by construction). -/
def shapeOk (f : Clif.Function) (vc : VCode) (ctx : Ctx) (st0 : LState) (gn : Nat → Nat)
    (bl : List BLow) : Bool :=
  ctxOk f ctx && decide (ctx.valReg.size ≤ st0.nextVreg) &&
  f.blocks.all (fun B => B.params.all fun p => decide (gn p.1 = p.1)) &&
  decide (bl.length = f.blocks.length) && decide (f.blocks.length ≤ vc.blocks.size) &&
  (List.range vc.blocks.size).all (fun l => match vc.blocks[l]? with
    | some vb => decide (vb.label = l)
    | none => true) &&
  ((List.range f.blocks.length).all fun bi => match f.blocks[bi]?, bl[bi]? with
    | some B, some L => blockOk f vc ctx st0 (renOf gn) gn bl bi B L
    | _, _ => false) &&
  decide (st0.nextVreg ≤ f.freshValue)

/-- The successors the driver simulation enters: a branch's, and a `try_call`'s or
`try_call_indirect`'s normal return (`Clif.run` never takes an exception edge). -/
def edgeIds : Clif.Terminator → List Clif.BlockId
  | .tryCall _ _ et | .tryCallIndirect _ _ et => [et.normal.block]
  | t => (dests t).map (·.block)

/-- Membership in the values available in a block (`availOf f In bi`, `mem_avail`): the block's
first instruction index, its statements, and its parameters and entry values. -/
structure Avail where
  start : Nat
  body : Array Clif.Stmt
  ent : List Clif.ValueId
  entS : Std.HashSet Clif.ValueId

/-- The `Avail` of block `bi` (`B`, lowered as `L`). -/
def Avail.of (B : Clif.Block) (L : BLow) (In : Array (List Clif.ValueId)) (bi : Nat) : Avail :=
  let ent := B.params.map (·.1) ++ In.getD bi []
  { start := L.start, body := B.body.toArray, ent, entS := Std.HashSet.ofList ent }

/-- The statement of the block defining `x` (found from `ctx.defInst? x`; exact when every
statement's results are defined by its instruction, `DefsAt`). -/
def Avail.dpos (ctx : Ctx) (a : Avail) (x : Clif.ValueId) : Option Nat :=
  match ctx.defInst? x with
  | some d =>
    if a.start ≤ d then
      match a.body[d - a.start]? with
      | some stm => if x ∈ stm.results then some (d - a.start) else none
      | none => none
    else none
  | none => none

/-- `x` is available before statement `j`. -/
def Avail.mem (ctx : Ctx) (a : Avail) (j : Nat) (x : Clif.ValueId) : Bool :=
  match a.dpos ctx x with
  | some k => decide (k < j)
  | none => a.entS.contains x

/-- The first statement before which `x` is available (`0`: from the entry). -/
def Avail.first (ctx : Ctx) (a : Avail) (x : Clif.ValueId) : Nat :=
  match a.dpos ctx x with
  | some k => k + 1
  | none => 0

/-- The edge condition of `Cert.term` for an edge from a block (values `a`, `n` statements) to
block `b`. -/
def edgeOk (f : Clif.Function) (ctx : Ctx) (gn : Nat → Nat) (fb : Array Clif.Block)
    (bla : Array BLow) (In : Array (List Clif.ValueId)) (a : Avail) (n : Nat) (b : Clif.BlockId) :
    Bool :=
  match blockIdx? f b with
  | none => true
  | some tl => match fb[tl]?, bla[tl]? with
    | none, _ => true
    | some _, none => false
    | some TB, some TL =>
      let t := Avail.of TB TL In tl
      let ps : List Clif.ValueId := TB.params.map (·.1)
      let P := Std.HashSet.ofList ps
      decide ps.Nodup &&
      t.ent.all fun x => !(t.mem ctx 0 x) ||
        ((P.contains x || (defArgs ctx x).all fun y => !P.contains y) &&
          ((P.contains x && decide (ctx.defInst? x = none)) ||
            (!P.contains x && a.mem ctx n x && !P.contains (gn x))))

/-- The per-block conditions of `Cert` (statements, terminator, edges, closure), with the
available values as `Avail.mem`: the statements' results are defined by their instructions
(`DefsAt`), so a value is available from the statement after its definition in the block, or
from the entry; the conditions on every value available before some statement are checked once
per value, at the first such statement (for the clobber condition: the statements' fresh vreg
ranges are increasing, so a value's resolved vreg is outside the ranges of the statements from
that one on if it is below that statement's range or above the range of the block's last
statement). -/
def certBlockOk (f : Clif.Function) (ctx : Ctx) (st0 : LState) (gn : Nat → Nat)
    (fb : Array Clif.Block) (bla : Array BLow) (In : Array (List Clif.ValueId)) (bi : Nat)
    (B : Clif.Block) (L : BLow) : Bool :=
  let a := Avail.of B L In bi
  let n := B.body.length
  let sls := L.sl.toArray
  decide (L.sl.length = n) &&
  (List.range n).all (fun k => match a.body[k]?, sls[k]? with
    | some stm, some sl =>
      stm.results.all (fun r => decide (ctx.defInst? r = some (L.start + k))) &&
      decide stm.results.Nodup &&
      (instArgs stm.inst).all (a.mem ctx k) &&
      decide (sl.st.nextVreg ≤ sl.st'.nextVreg) &&
      (match sls[k + 1]? with
        | some sl' => decide (sl.st'.nextVreg ≤ sl'.st.nextVreg)
        | none => true)
    | _, _ => false) &&
  (a.ent ++ B.body.flatMap (·.results)).all (fun x =>
    decide (x < st0.nextVreg) &&
    (defArgs ctx x).all (fun y => a.mem ctx n y && decide (a.first ctx y ≤ a.first ctx x)) &&
    (match sls[a.first ctx x]?, sls[n - 1]? with
      | some sl, some last => decide (gn x < sl.st.nextVreg) || decide (last.st'.nextVreg ≤ gn x)
      | _, _ => true) &&
    !(decide (L.tst.nextVreg ≤ gn x) && decide (gn x < L.tst'.nextVreg))) &&
  (termArgs (abiTerm f B.term)).all (a.mem ctx n) &&
  (edgeIds B.term).all (fun b => decide (blockIdx? f b ≠ some 0) &&
    edgeOk f ctx gn fb bla In a n b)

/-- `Cert f ctx st0 gn bl (availOf f In)`, decided. -/
def certOk (f : Clif.Function) (ctx : Ctx) (st0 : LState) (gn : Nat → Nat) (bl : List BLow)
    (In : Array (List Clif.ValueId)) : Bool :=
  let fb := f.blocks.toArray
  let bla := bl.toArray
  (match fb[0]?, bla[0]? with
    | some B, some L =>
      let a := Avail.of B L In 0
      decide ((B.params.map (·.1)).Nodup) &&
        a.ent.all fun x => !(a.mem ctx 0 x) ||
          (decide (x ∈ B.params.map (·.1)) && decide (ctx.defInst? x = none))
    | some _, none => false
    | none, _ => true) &&
  (List.range fb.size).all (fun bi => match fb[bi]?, bla[bi]? with
    | some B, some L => certBlockOk f ctx st0 gn fb bla In bi B L
    | _, _ => true) &&
  (List.range ctx.insts.size).all (fun ii => match ctx.insts[ii]? with
    | some info => (List.range info.results.length).all fun m =>
        match info.results[m]?, info.resTys[m]? with
        | some r, some t => decide (ctx.valueType? r = some t)
        | _, _ => true
    | none => true) &&
  f.blocks.all (fun B => B.params.all fun q => decide (ctx.valueType? q.1 = some (CTy.ofClif q.2)))

/-- Every `br_table` index has an integer type of at most 32 bits (`BrIdxTyped`; Cranelift's
verifier requires `i32`), and every jump table has fewer than `2^32` entries (Cranelift's
jump tables are `u32`-sized; contract change #9). -/
def brIdxOk (f : Clif.Function) (ctx : Ctx) : Bool :=
  f.blocks.all fun B => match B.term with
    | .brTable x _ tbl => decide (tbl.length < 2 ^ 32) && match ctx.valueType? x with
      | some (.int w) => decide (w ≤ 32)
      | _ => false
    | _ => true

/-- The calls (`call`) of `f`'s statements pass at most `out` bytes on the stack, with a
well-formed stack-argument layout (`CallsStack`). -/
def callsStackOkB (f : Clif.Function) (out : Nat) : Bool :=
  f.blocks.all fun B => B.body.all fun st => match st.inst with
    | .call fn _ => match f.extern? fn with
      | some e => decide (stackBytes e.sig ≤ out) && stackLayoutOk e.sig
      | none => true
    | _ => true

/-- The signature's parameter locations and byte sizes compute, one per parameter (the entry
block's `Args` and loads, `pre`), and the register-passed parameters are in x0..x8. -/
def entryOkB (f : Clif.Function) : Bool :=
  (locsOf f.sig).length == f.sig.params.length &&
    (locsOf f.sig).all (fun l => match l with
      | .reg (.x n) => decide (n ≤ 8)
      | .reg _ => false
      | .stack _ => true) &&
    match sigParamBytes f.sig with
    | .ok _ => true
    | .error _ => false

/-- **The lowering validator.** Accepts `vc` iff it is the lowering of `f` in the structure
the driver proof needs, with an SSA availability certificate, and every `br_table` index has at most 32 bits;
the outgoing area holds every call's stack arguments and the entry's parameter locations compute. -/
def lowerCheck (f : Clif.Function) (vc : VCode) : Bool :=
  match buildCtx f with
  | .error _ => false
  | .ok (ctx, _, st0) =>
    match lowBlocks f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0
        f.blocks.length with
    | none => false
    | some bl =>
      let gn := gnAt (gnTable st0.nextVreg (aliasOf f bl))
      shapeOk f vc ctx st0 gn bl && certOk f ctx st0 gn bl (inFix f ctx gn) && brIdxOk f ctx &&
        -- a `tryCall` in the VCode only for a function with a `try_call`
        (f.blocks.any (·.term.isTry) || !vc.hasTryCall) &&
        -- the outgoing area holds every call's stack arguments; the entry's parameter locations
        (callsStackOkB f vc.outgoing && entryOkB f)

end Backend.Proof.Driver
