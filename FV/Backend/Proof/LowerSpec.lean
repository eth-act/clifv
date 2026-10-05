import FV.Backend.Proof.DriverCheckSound

/-!
# Completeness of `lowerCheck`: the shared definitions

`lowerCheck_complete` (`LowerComplete.lean`) proves that the lowering validator accepts every
output of `lowerFunction` on input satisfying two decidable conditions on `f` alone:

* `Dominated f`: SSA (every value defined once) and every use available at its position in the
  must-availability of `f` computed without renaming (`availIn f ctx = inFix f ctx id`), in the
  form the certificate uses (`availOf`); and no value available at a block's entry is computed
  directly from that block's parameters (true for every reachable block of SSA input, where a
  definition dominating the block cannot read the block's parameters);
* `LowerScope f`: subset E, a non-empty function whose entry block is no branch target, and a
  few declaration-level conditions the validator checks (`br_table` index width, atomic
  addresses, `try_call` return indices, stack-argument layouts of callees).

This file holds the definitions the parts of the proof share: the functional description of the
VCode `lowerFunction` builds (`vcBlocksOf`, from the recorded lowering `lowBlocks`), the alias
array (`aliasArr`), the values a statement's lowering may return (`Prov`), the dataflow
constraints (`FixOk`), well-founded aliases (`AliasWF`, `AliasPath`), and the conditions.
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof

/-! ## The VCode `lowerFunction` builds -/

/-- `lowerFunction`'s alias update for result `p.1` returned in vreg `p.2` (`set_vreg_alias`,
the array grown as needed). -/
def aliasStep (a : Array (Option Nat)) (p : Nat × Nat) : Array (Option Nat) :=
  let a := if a.size ≤ p.1 then a ++ Array.replicate (p.1 + 1 - a.size) none else a
  a.set! p.1 (some p.2)

/-- `lowerFunction`'s alias array after recording the aliases `al` in order. -/
def aliasArr (al : List (Nat × Nat)) : Array (Option Nat) := al.foldl aliasStep #[]

/-- `lowerFunction`'s final renaming of a block (`fixBlock`). -/
def fixBlock (R : Reg → Reg) (vb : VBlock) : VBlock :=
  { vb with insts := vb.insts.map (MInst.mapRegs R), branchArgs := vb.branchArgs.map R }

/-- The register `lowerFunction` passes for a `try_call` successor argument (`rets`, `pays`: the
call's return and payload vregs). -/
def tryEdgeArg (rets pays : List Reg) : Clif.TryArg → Reg
  | .val v => .vreg v .int
  | .ret i => rets.getD i .xzr
  | .exn i => pays.getD i .xzr

/-- Block `bi` (`B`, lowered as `L`) before alias resolution: the entry's argument setup, the
statements' segments, the terminator's segment; parameters and jump arguments. -/
def rawBlock (f : Clif.Function) (bl : List BLow) (bi : Nat) (B : Clif.Block) : VBlock :=
  { label := bi
    insts := (pre f id bi ++ ((List.range B.body.length).map (seg f id bl bi)).flatten ++
      tseg id bl bi).toArray
    params := if bi = 0 then #[] else (B.params.map fun p => Reg.vreg p.1 .int).toArray
    branchArgs := match B.term with
      | .jump bc => (bc.args.map fun a => Reg.vreg a .int).toArray
      | _ => #[] }

/-- The edge blocks `lowerFunction` creates for block `B` (lowered as `L`), in label order: one
per `try_call` successor, one per branch successor with arguments. -/
def edgeBlocks (f : Clif.Function) (B : Clif.Block) (L : BLow) : List VBlock :=
  match B.term, L.tl with
  | .tryCall _ _ et, some T | .tryCallIndirect _ _ et, some T =>
    (et.dests.zip L.targets).filterMap fun (td, l) => (blockIdx? f td.block).map fun tl =>
      { label := l, insts := #[.jump tl],
        branchArgs := (td.args.map (tryEdgeArg T.regs.1 T.regs.2)).toArray }
  | .jump _, _ => []
  | t, _ => ((dests t).zip L.targets).filterMap fun (bc, l) =>
    if bc.args.isEmpty then none else (blockIdx? f bc.block).map fun tl =>
      { label := l, insts := #[.jump tl], branchArgs := (bc.args.map fun a => Reg.vreg a .int).toArray }

/-- The blocks of `lowerFunction f`'s VCode, from the recorded lowering `bl`: the function's
blocks, then the edge blocks, renamed by the alias resolution. -/
def vcBlocksOf (f : Clif.Function) (bl : List BLow) : Array VBlock :=
  let a := aliasArr (aliasOf f bl)
  let R := lowerFunction.resolve a (a.size + 1)
  ((((f.blocks.zip bl).zipIdx.map fun (p : (Clif.Block × BLow) × Nat) => rawBlock f bl p.2 p.1.1) ++
      (f.blocks.zip bl).flatMap fun (p : Clif.Block × BLow) => edgeBlocks f p.1 p.2).map
    (fixBlock R)).toArray

/-- The outgoing area of `lowerFunction f`'s VCode: the final lowering state's. -/
def outOf (st0 : LState) (bl : List BLow) : Nat :=
  (bl.getLast?.map (·.tst'.outgoing)).getD st0.outgoing

/-- What `lowerFunction` checks on the way that `lowBlocks` does not record. -/
structure LoopFacts (f : Clif.Function) (ctx : Ctx) (bl : List BLow) : Prop where
  /-- a statement's lowering returns one register list per result (unless it has none), each a
  single register -/
  results : ∀ (bi : Nat) (B : Clif.Block) (L : BLow), f.blocks[bi]? = some B → bl[bi]? = some L →
    ∀ (j : Nat) (stm : Clif.Stmt) (sl : SLow), B.body[j]? = some stm → L.sl[j]? = some sl →
    (sl.rss.length = stm.results.length ∨ stm.results = []) ∧
    ∀ (r : Nat) (rs : List Reg), (r, rs) ∈ stm.results.zip sl.rss → ∃ x, rs = [x]
  /-- branch arguments: the target exists, a non-empty argument list matches its parameters,
  the arguments are values with registers -/
  args : ∀ B ∈ f.blocks, ∀ bc ∈ dests B.term, ∃ tb, f.block? bc.block = some tb ∧
    (bc.args ≠ [] → tb.params.length = bc.args.length) ∧
    ∀ a ∈ bc.args, ctx.valueReg? a = some (.vreg a .int)
  /-- `try_call` successors: the target exists, the argument count matches, values have
  registers, `retN` only on the normal return, `exnN` only on the handlers, in range -/
  tryArgs : ∀ (bi : Nat) (B : Clif.Block) (L : BLow) (et : Clif.ExnTable), f.blocks[bi]? = some B →
    bl[bi]? = some L → IsTryWith B.term et →
    ∃ T : TryLow, L.tl = some T ∧ ∀ (k : Nat) (td : Clif.TryDest), et.dests[k]? = some td →
      (∃ tb, f.block? td.block = some tb ∧ tb.params.length = td.args.length) ∧
      ∀ a ∈ td.args, match a with
        | .val v => ctx.valueReg? v = some (.vreg v .int)
        | .ret i => k = et.handlers.length ∧ i < T.regs.1.length
        | .exn i => k ≠ et.handlers.length ∧ i < T.regs.2.length
  /-- the `try_call` rule's code ends in the call `lowerFunction` turns into the `tryCall` -/
  tryLast : ∀ (bi : Nat) (B : Clif.Block) (L : BLow) (T : TryLow), f.blocks[bi]? = some B →
    bl[bi]? = some L → L.tl = some T → ∃ c, L.tst'.emitted.back? = some (.call c)
  /-- the entry block's parameter locations and byte sizes compute -/
  entry : f.blocks ≠ [] → ∃ locs n, sigArgLocs f.sig = .ok (locs, n)
  paramBytes : ∃ bytes, sigParamBytes f.sig = .ok bytes
  /-- a `return` of an `sret` signature has the struct pointer to return -/
  sret : ∀ B ∈ f.blocks, ∀ vs, B.term = .ret vs → sretRet f = [] → sigRets f.sig = f.sig.returns

/-! ## Statements: what their lowering may return -/

/-- The values whose registers the lowering of instruction `ii` may return: its operands, closed
under the operands and the results of each one's defining instruction (what the rules reach
through `def_inst`, `first_result`, … of an operand). -/
inductive Prov (ctx : Ctx) (ii : Nat) : Nat → Prop
  | arg {info : IInfo} {c : Clif.Inst} {y : Nat} : ctx.insts[ii]? = some info → info.clif = some c →
      y ∈ instArgs c → Prov ctx ii y
  | dep {n j : Nat} {info : IInfo} {c : Clif.Inst} {y : Nat} : Prov ctx ii n → ctx.defInst? n = some j →
      ctx.insts[j]? = some info → info.clif = some c → (y ∈ instArgs c ∨ y ∈ info.results) →
      Prov ctx ii y

/-! ## The dataflow -/

/-- The parameters of block `tl`. -/
def parsOf (f : Clif.Function) (tl : Nat) : List Clif.ValueId :=
  match f.blocks[tl]? with
  | some B => B.params.map (·.1)
  | none => []

/-- The results of the statements of block `tl`. -/
def defsOf (f : Clif.Function) (tl : Nat) : List Clif.ValueId :=
  match f.blocks[tl]? with
  | some B => B.body.flatMap (·.results)
  | none => []

/-- The successor block indices of block `p` (`succIds`: a `try_call`'s handlers included). -/
def succIdx (f : Clif.Function) (p : Nat) : List Nat :=
  match f.blocks[p]? with
  | some B => (succIds B.term).filterMap (blockIdx? f)
  | none => []

/-- The values of `f`: parameters and statement results, in layout order. -/
def valueDefs (f : Clif.Function) : List Clif.ValueId :=
  f.blocks.flatMap fun B => B.params.map (·.1) ++ B.body.flatMap (·.results)

/-! ## The context `buildCtx` builds -/

/-- The index of block `bi`'s first instruction in `buildCtx`'s table (block by block: the
statements, then a slot for the terminator). -/
def blockStart (f : Clif.Function) (bi : Nat) : Nat :=
  ((f.blocks.take bi).map (·.body.length + 1)).sum

/-- Facts about `buildCtx f = .ok (ctx, _, st0)`. -/
structure CtxFacts (f : Clif.Function) (ctx : Ctx) (st0 : LState) : Prop where
  size : st0.nextVreg = ctx.valDef.size ∧ ctx.valReg.size = ctx.valDef.size ∧
    ctx.valTy.size = ctx.valDef.size
  vals : ∀ x ∈ valueDefs f, x < st0.nextVreg ∧ ctx.valueReg? x = some (.vreg x .int)
  tryRegs : ctx.tryRegs = ([], [])
  insts : ctx.insts.size = blockStart f f.blocks.length
  stmt : ∀ bi B j stm, f.blocks[bi]? = some B → B.body[j]? = some stm →
    ∃ info, ctx.insts[blockStart f bi + j]? = some info ∧ info.clif = some stm.inst ∧
      info.results = stm.results
  term : ∀ bi B, f.blocks[bi]? = some B →
    ctx.insts[blockStart f bi + B.body.length]? = some (⟨.op .unit, [], [], none⟩ : IInfo)
  /-- with SSA input, a value's definition is its statement -/
  defs : (valueDefs f).Nodup → ∀ x d, ctx.defInst? x = some d ↔
    ∃ bi B j stm, f.blocks[bi]? = some B ∧ B.body[j]? = some stm ∧ x ∈ stm.results ∧
      d = blockStart f bi + j
  /-- with SSA input, the context types are the declared ones -/
  types : (valueDefs f).Nodup →
    (∀ (ii : Nat) (info : IInfo), ctx.insts[ii]? = some info → ∀ (m : Nat) r t,
      info.results[m]? = some r → info.resTys[m]? = some t → ctx.valueType? r = some t) ∧
    ∀ B ∈ f.blocks, ∀ q ∈ B.params, ctx.valueType? q.1 = some (CTy.ofClif q.2)

/-- `D tl x` (`x` available at the entry of block `tl`) satisfies `inFix`'s constraints:
candidates (not the entry block; a value of `f`, not a parameter of `tl` nor renamed onto one),
available at the end of every predecessor, operands of the definition available at the entry
and not defined in the block. -/
structure FixOk (f : Clif.Function) (ctx : Ctx) (gn : Nat → Nat) (D : Nat → Nat → Prop) : Prop where
  cand : ∀ tl x, D tl x → 1 ≤ tl ∧ tl < f.blocks.length ∧ x < ctx.valDef.size ∧ x ∈ valueDefs f ∧
    x ∉ parsOf f tl ∧ gn x ∉ parsOf f tl
  out : ∀ tl x, D tl x → ∀ p, tl ∈ succIdx f p → x ∈ parsOf f p ∨ x ∈ defsOf f p ∨ D p x
  clo : ∀ tl x, D tl x → ∀ y ∈ defArgs ctx x, (y ∈ parsOf f tl ∨ D tl y) ∧ y ∉ defsOf f tl

/-! ## Aliases -/

/-- Alias chains are well founded: an alias target that is itself aliased has a smaller rank. -/
def AliasWF (al : List (Nat × Nat)) : Prop :=
  ∃ rank : Nat → Nat, ∀ p ∈ al, ∀ q ∈ al, q.1 = p.2 → rank p.2 < rank p.1

/-- `y` is reached from `x` by following aliases. -/
inductive AliasPath (al : List (Nat × Nat)) : Nat → Nat → Prop
  | refl (x : Nat) : AliasPath al x x
  | step {x y z : Nat} : (x, y) ∈ al → AliasPath al y z → AliasPath al x z

/-! ## The conditions on the input -/

/-- The values available at the block entries computed from `f` alone (no renaming). -/
def availIn (f : Clif.Function) (ctx : Ctx) : Array (List Clif.ValueId) := inFix f ctx id

/-- **Dominance** (Cranelift's verifier: SSA, every use dominated by its definition), in the
form of the certificate: every value is defined once, every operand of a statement and of a
terminator is available there (`availOf` of the must-availability `availIn`), and no value
available at a block's entry (and not redefined in it) is computed from the block's
parameters. -/
structure Dominated (f : Clif.Function) : Prop where
  ssa : (valueDefs f).Nodup
  uses : ∀ ctx ranges st0, buildCtx f = .ok (ctx, ranges, st0) → ∀ bi B, f.blocks[bi]? = some B →
    (∀ j stm, B.body[j]? = some stm → ∀ y ∈ instArgs stm.inst, y ∈ availOf f (availIn f ctx) bi j) ∧
    ∀ y ∈ termArgs (abiTerm f B.term), y ∈ availOf f (availIn f ctx) bi B.body.length
  paramFree : ∀ ctx ranges st0, buildCtx f = .ok (ctx, ranges, st0) → ∀ tl x,
    x ∈ (availIn f ctx).getD tl [] → x ∉ defsOf f tl → ∀ y ∈ defArgs ctx x, y ∉ parsOf f tl

/-- **The other input conditions** of `lowerCheck_complete`. -/
structure LowerScope (f : Clif.Function) : Prop where
  /-- clif-subset-v2 E -/
  subsetE : Compile.functionE f = true
  nonempty : f.blocks ≠ []
  /-- the entry block is no branch target (Cranelift's verifier) -/
  noEntryPred : ∀ B ∈ f.blocks, ∀ b ∈ succIds B.term, blockIdx? f b ≠ some 0
  /-- `br_table` indices of at most 32 bits, tables of fewer than `2^32` entries
  (`brIdxOk`); atomic accesses at `i64` addresses (Cranelift's verifier) -/
  ctxFacts : ∀ ctx ranges st0, buildCtx f = .ok (ctx, ranges, st0) → brIdxOk f ctx = true ∧
    ∀ (ii : Nat) (info : IInfo) (inst : Clif.Inst) (x : Nat), ctx.insts[ii]? = some info →
      info.clif = some inst → memAddr? inst = some x → ctx.valueType? x = some (.int 64)
  /-- a `try_call`'s normal return passes return values of the callee's declared returns -/
  tryRet : ∀ B ∈ f.blocks, ∀ et, IsTryWith B.term et → ∀ sig, f.sigDecls.lookup et.sig = some sig →
    ∀ i, Clif.TryArg.ret i ∈ et.normal.args → i < sig.returns.length
  /-- the callees' stack-argument layouts are well formed (`stackLayoutOk`) -/
  stackLayout : (∀ B ∈ f.blocks, ∀ st ∈ B.body, ∀ fn args e, st.inst = .call fn args →
      f.extern? fn = some e → stackLayoutOk e.sig = true) ∧
    ∀ B ∈ f.blocks, ∀ fn args et e, B.term = .tryCall fn args et → f.extern? fn = some e →
      stackLayoutOk e.sig = true

end Backend.Proof.Driver
