import FV.Backend.Isel
import FV.Compile.Subset

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
2. computes the alias resolution `gn` from the recorded result registers (`gnOf`) and the
   class-preserving renaming `R = renOf gn`;
3. computes the available values `A` by a must-dataflow (`inFix`, `availOf`: a value is
   available at a block entry if it is available at the end of every predecessor);
4. checks, with `decide`/`all` over finite data, every field of `LowerShape` and `Cert` that is
   not true by construction: the context invariants (`CtxInv`), the VCode blocks are exactly
   the renamed recorded code (`vb.insts = pre ++ segments ++ terminator segment`), labels,
   parameters, branch arguments, edge blocks, and the local certificate conditions (operands
   available, results fresh and uniquely defined, no available value's register written by a
   statement's lowering, closure under definitions, edges, types).

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
  | .iconst .. | .stackAddr .. | .fence | .nop | .symbolValue .. => []
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

/-- The entry block's `Args`. -/
def pre (bi : Nat) : List MInst :=
  match bi, f.blocks[bi]? with
  | 0, some B => [.args ((B.params.zipIdx).map fun ((v, _), k) => (R (.vreg v .int), .x k))]
  | _, _ => []

/-- The terminator's segment. -/
def tseg (bi : Nat) : List MInst :=
  match bl[bi]? with
  | some L => L.tst'.emitted.toList.map (·.mapRegs R)
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

/-- The lowering of the blocks `Bs` (first instruction index `start`, state `st`, next edge
label `nl`), as `lowerFunction` makes it. -/
def lowBlocks (f : Clif.Function) (call : StmtCall) (tcall : TermCallF) :
    Nat → List Clif.Block → LState → Nat → Option (List BLow)
  | _, [], _, _ => some []
  | start, B :: Bs, st, nl =>
    match lowStmts call start B.body st with
    | none => none
    | some (sls, stE) =>
      match termData B.term with
      | .error _ => none
      | .ok data =>
        match targetsOf f B.term nl with
        | none => none
        | some (targets, nl') =>
          let ti := start + B.body.length
          let tst : LState := { stE with emitted := #[] }
          match tcall ti data B.term targets tst with
          | .ok (out, tst', _) =>
            if out.isSome then
              (lowBlocks f call tcall (ti + 1) Bs { tst' with emitted := #[] } nl').map
                (⟨start, sls, data, targets, tst, tst'⟩ :: ·)
            else none
          | .error _ => none

/-! ## Alias resolution -/

/-- The aliases `lowerFunction` records: result `r` ↦ the vreg `out` the rules returned. -/
def aliasOf (f : Clif.Function) (bl : List BLow) : List (Nat × Nat) :=
  (f.blocks.zip bl).flatMap fun (B, L) => (B.body.zip L.sl).flatMap fun (stm, sl) =>
    (stm.results.zip sl.rss).filterMap fun (r, rs) => match rs with
      | [.vreg out _] => some (r, out)
      | _ => none

/-- Follow the alias chain of `n` (at most `k` steps). -/
def chase (al : List (Nat × Nat)) : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => match al.lookup n with
    | some m => chase al k m
    | none => n

/-- The resolved vreg number of `n`: temporaries (`≥ lo`) are never aliased. -/
def gnOf (lo : Nat) (al : List (Nat × Nat)) (n : Nat) : Nat :=
  if n < lo then chase al (al.length + 1) n else n

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
def availOf (f : Clif.Function) (In : List (List Clif.ValueId)) (bi j : Nat) : List Clif.ValueId :=
  match f.blocks[bi]? with
  | some B => (B.params.map (·.1) ++ In.getD bi [] ++ defsBefore B j).filter
      fun x => decide (x ∉ defsFrom B j)
  | none => []

/-- All values of `f` (parameters and results). -/
def allVals (f : Clif.Function) : List Clif.ValueId :=
  f.blocks.flatMap fun B => B.params.map (·.1) ++ B.body.flatMap (·.results)

/-- The blocks with an edge to block `tl`. -/
def predsOf (f : Clif.Function) (tl : Nat) : List Nat :=
  (List.range f.blocks.length).filter fun bi => match f.blocks[bi]? with
    | some B => (dests B.term).any fun bc => blockIdx? f bc.block == some tl
    | none => false

/-- The candidates for block `tl`'s entry values (not a parameter, not renamed onto one). -/
def entryCand (f : Clif.Function) (gn : Nat → Nat) (tl : Nat) : List Clif.ValueId :=
  if tl = 0 then [] else
  match f.blocks[tl]? with
  | some TB => (allVals f).filter fun x =>
      decide (x ∉ TB.params.map (·.1)) && decide (gn x ∉ TB.params.map (·.1))
  | none => []

/-- One round of the must-dataflow (the values available at every block end computed once). -/
def inStep (f : Clif.Function) (gn : Nat → Nat) (In : List (List Clif.ValueId)) :
    List (List Clif.ValueId) :=
  let outs : Array (List Clif.ValueId) := ((List.range f.blocks.length).map fun bi =>
    match f.blocks[bi]? with
    | some B => availOf f In bi B.body.length
    | none => []).toArray
  (List.range f.blocks.length).map fun tl =>
    (entryCand f gn tl).filter fun x => (predsOf f tl).all fun bi =>
      decide (x ∈ outs.getD bi [])

/-- Iterate to a fixpoint (at most `fuel` rounds). -/
def inIter (f : Clif.Function) (gn : Nat → Nat) : Nat → List (List Clif.ValueId) →
    List (List Clif.ValueId)
  | 0, In => In
  | k + 1, In =>
    let In' := inStep f gn In
    if In' == In then In else inIter f gn k In'

/-- The values available at the block entries (from "everything", descending). -/
def inFix (f : Clif.Function) (gn : Nat → Nat) : List (List Clif.ValueId) :=
  inIter f gn (f.blocks.length * ((allVals f).length + 1) + 2)
    ((List.range f.blocks.length).map (entryCand f gn))

/-! ## The checks -/

/-- The result-type check of one instruction (`ctxOk`). -/
def ctxResTysOk (f : Clif.Function) (info : IInfo) (i : Clif.Inst) : Bool :=
  match i.resultTypes (fun r => (f.extern? r).map (·.sig)) (f.sigDecls.lookup ·) with
  | some tys => decide (info.resTys = tys.map CTy.ofClif) &&
      decide (info.results.length = tys.length)
  | none => false

/-- Not a `func_addr` (outside the theorem, rust-route step 4: `CtxInv.noFA`). -/
def notFuncAddr : Clif.Inst → Bool
  | .funcAddr .. => false
  | _ => true

/-- `CtxInv f ctx` (M4's context facts), decided. -/
def ctxOk (f : Clif.Function) (ctx : Ctx) : Bool :=
  decide (ctx.func = f) &&
  ctx.insts.toList.all (fun info => match info.clif with
    | some i =>
      Compile.instE i && notFuncAddr i &&
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
    | some (.load _ _ _ x _) | some (.store _ _ _ _ x _) => decide (ctx.valueType? x = some (.int 64))
    | _ => true)

/-- The successor facts of `LowerShape` for block `B` (lowering `L`). -/
def succOk (f : Clif.Function) (vc : VCode) (R : Reg → Reg) (B : Clif.Block) (L : BLow) : Bool :=
  match B.term with
  | .jump bc => match blockIdx? f bc.block with
    | some tl => decide (L.targets = [tl])
    | none => false
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
  (List.range f.blocks.length).all fun bi => match f.blocks[bi]?, bl[bi]? with
    | some B, some L => blockOk f vc ctx st0 (renOf gn) gn bl bi B L
    | _, _ => false

/-- The closure condition: a tracked value's definition has tracked operands (for every
definition, which implies `Cert.closed` for the pure ones). -/
def closedOk (ctx : Ctx) (A : List Clif.ValueId) : Bool :=
  A.all fun x => match ctx.defInst? x with
    | some d => match ctx.insts[d]? with
      | some info => match info.clif with
        | some cl => (instArgs cl).all fun y => decide (y ∈ A)
        | none => true
      | none => true
    | none => true

/-- The edge condition of `Cert.term` for an edge from block `bi` (values `Aend` at its end) to
the target of `bc`. -/
def edgeOk (f : Clif.Function) (ctx : Ctx) (gn : Nat → Nat) (In : List (List Clif.ValueId))
    (Aend : List Clif.ValueId) (bc : Clif.BlockCall) : Bool :=
  match blockIdx? f bc.block with
  | none => true
  | some tl => match f.blocks[tl]? with
    | none => true
    | some TB =>
      decide ((TB.params.map (·.1)).Nodup) &&
      (availOf f In tl 0).all (fun x => decide (x ∈ TB.params.map (·.1)) ||
        match ctx.defInst? x with
        | some d => match ctx.insts[d]? with
          | some info => match info.clif with
            | some cl => (instArgs cl).all fun y => decide (y ∉ TB.params.map (·.1))
            | none => true
          | none => true
        | none => true) &&
      (availOf f In tl 0).all fun x =>
        (decide (x ∈ TB.params.map (·.1)) && decide (ctx.defInst? x = none)) ||
        (decide (x ∉ TB.params.map (·.1)) && decide (x ∈ Aend) &&
          decide (gn x ∉ TB.params.map (·.1)))

/-- The per-block conditions of `Cert` (statements, terminator, edges, closure). -/
def certBlockOk (f : Clif.Function) (ctx : Ctx) (st0 : LState) (gn : Nat → Nat)
    (In : List (List Clif.ValueId)) (bi : Nat) (B : Clif.Block) (L : BLow) : Bool :=
  let A := availOf f In bi
  (A B.body.length).all (fun x => decide (x < st0.nextVreg)) &&
  (List.range (B.body.length + 1)).all (fun j => closedOk ctx (A j)) &&
  (List.range B.body.length).all (fun j => match B.body[j]?, L.sl[j]? with
    | some stm, some sl =>
      (instArgs stm.inst).all (fun y => decide (y ∈ A j)) &&
      stm.results.all (fun r => decide (r ∉ A j) && decide (ctx.defInst? r = some (L.start + j))) &&
      decide stm.results.Nodup &&
      (A (j + 1)).all (fun x => decide (x ∈ A j) || decide (x ∈ stm.results)) &&
      (A j).all (fun x => !(decide (sl.st.nextVreg ≤ gn x) && decide (gn x < sl.st'.nextVreg)))
    | _, _ => false) &&
  (termArgs B.term).all (fun y => decide (y ∈ A B.body.length)) &&
  (A B.body.length).all (fun x => !(decide (L.tst.nextVreg ≤ gn x) && decide (gn x < L.tst'.nextVreg))) &&
  (dests B.term).all (fun bc => decide (blockIdx? f bc.block ≠ some 0) &&
    edgeOk f ctx gn In (A B.body.length) bc)

/-- `Cert f ctx st0 gn bl (availOf f In)`, decided. -/
def certOk (f : Clif.Function) (ctx : Ctx) (st0 : LState) (gn : Nat → Nat) (bl : List BLow)
    (In : List (List Clif.ValueId)) : Bool :=
  (match f.blocks[0]? with
    | some B => decide ((B.params.map (·.1)).Nodup) &&
        (availOf f In 0 0).all fun x => decide (x ∈ B.params.map (·.1)) &&
          decide (ctx.defInst? x = none)
    | none => true) &&
  (List.range f.blocks.length).all (fun bi => match f.blocks[bi]?, bl[bi]? with
    | some B, some L => certBlockOk f ctx st0 gn In bi B L
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

/-- **The lowering validator.** Accepts `vc` iff it is the lowering of `f` in the structure
the driver proof needs, with an SSA availability certificate, and every `br_table` index has at most 32 bits.
`f.sigDecls` must be empty: `sigN` declarations exist only for `call_indirect`, which is
outside the end-to-end theorem (`E2E.InSubset` via `Compile.functionE`), and the context
invariant `CtxInv` (M4) is stated with no signature declarations. -/
def lowerCheck (f : Clif.Function) (vc : VCode) : Bool :=
  f.sigDecls.isEmpty &&
  match buildCtx f with
  | .error _ => false
  | .ok (ctx, _, st0) =>
    match lowBlocks f (stmtCall ctx) (termCallF ctx) 0 f.blocks st0 f.blocks.length with
    | none => false
    | some bl =>
      let gn := gnOf st0.nextVreg (aliasOf f bl)
      shapeOk f vc ctx st0 gn bl && certOk f ctx st0 gn bl (inFix f gn) && brIdxOk f ctx

end Backend.Proof.Driver
