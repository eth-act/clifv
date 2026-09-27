import FV.Backend.Proof.LowerFrame

/-!
# What `lowerFunction` builds, and the SSA certificate (M7 driver)

`LowerShape f vc …`: the structure of the VCode `lowerFunction f` returns, per CLIF block —
the entry `Args`, one segment per statement (the `lower` call's emitted code, renamed by the
alias resolution `R`), the terminator's segment (`lower`/`lower_branch`), block parameters,
jump arguments, edge blocks, labels = indices. (Obligation `lowerFunction_shape`: `lowerFunction f
= ok vc` implies it; open, see e2e.md.)

`Cert f … A`: an availability annotation `A bi j` (the values the driver tracks before statement
`j` of block `bi`) with local, checkable conditions: operands available, results fresh, no
available value's register is written by the lowering of the statement, closure under pure
definitions, edges. It holds for SSA input with `A` = the values whose definition strictly
dominates the point (obligation: a certificate checker, or a proof from SSA dominance).
-/

namespace Backend.Proof.Driver

open Backend

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

/-- **The structure of `lowerFunction f`'s VCode.** -/
structure LowerShape : Prop where
  hctx : ∃ ranges, buildCtx f = .ok (ctx, ranges, st0)
  ren : VRenaming R gn
  temps : ∀ n, st0.nextVreg ≤ n → gn n = n
  params : ∀ B ∈ f.blocks, ∀ p ∈ B.params, gn p.1 = p.1
  len : bl.length = f.blocks.length
  size : f.blocks.length ≤ vc.blocks.size
  labels : ∀ l (vb : VBlock), vc.blocks[l]? = some vb → vb.label = l
  /-- per block -/
  blk : ∀ bi B L, f.blocks[bi]? = some B → bl[bi]? = some L →
    ∃ vb, vc.blocks[bi]? = some vb ∧
    L.sl.length = B.body.length ∧
    -- statements
    (∀ j stm sl, B.body[j]? = some stm → L.sl[j]? = some sl →
      (∃ info, ctx.insts[L.start + j]? = some info ∧ info.clif = some stm.inst ∧
        info.results = stm.results) ∧
      sl.st.emitted = #[] ∧ st0.nextVreg ≤ sl.st.nextVreg ∧
      (∃ tr, runTerm ctx "lower" [.inst (L.start + j)] sl.st = .ok (some (.regsVec sl.rss), sl.st', tr)) ∧
      (∀ (k : Nat) r out cls, stm.results[k]? = some r → sl.rss[k]? = some [.vreg out cls] →
        gn r = gn out)) ∧
    -- terminator
    termData B.term = .ok L.data ∧ L.tst.emitted = #[] ∧ st0.nextVreg ≤ L.tst.nextVreg ∧
    (∃ out tr, runTerm (termCtx ctx (L.start + B.body.length) L.data)
        (termCall B.term (L.start + B.body.length) L.targets).1
        (termCall B.term (L.start + B.body.length) L.targets).2 L.tst = .ok (some out, L.tst', tr)) ∧
    -- code
    vb.insts.toList = pre f R bi ++ ((List.range B.body.length).map (seg f R bl bi)).flatten ++
      tseg R bl bi ∧
    tseg R bl bi ≠ [] ∧
    vb.params = (if bi = 0 then #[] else (B.params.map fun p => Reg.vreg p.1 .int).toArray) ∧
    vb.branchArgs = (match B.term with
      | .jump bc => (bc.args.map fun a => R (.vreg a .int)).toArray
      | _ => #[]) ∧
    -- successors
    (match B.term with
      | .jump bc => ∃ tl, blockIdx? f bc.block = some tl ∧ L.targets = [tl]
      | _ => L.targets.length = (dests B.term).length ∧
        ∀ (k : Nat) bc tlab, (dests B.term)[k]? = some bc → L.targets[k]? = some tlab →
          ∃ tl, blockIdx? f bc.block = some tl ∧
            (bc.args = [] → tlab = tl) ∧
            (bc.args ≠ [] → ∃ eb, vc.blocks[tlab]? = some eb ∧ eb.insts = #[.jump tl] ∧
              eb.params = #[] ∧ eb.branchArgs = (bc.args.map fun a => R (.vreg a .int)).toArray))

/-- **SSA availability certificate.** `A bi j`: values tracked before statement `j` of block
`bi` (`j = body.length`: at the terminator). -/
structure Cert (A : Nat → Nat → List Clif.ValueId) : Prop where
  /-- tracked values are CLIF values (below the temporaries) -/
  small : ∀ bi j x, x ∈ A bi j → x < st0.nextVreg
  /-- entry: only the entry block's parameters, pairwise distinct, not defined by instructions -/
  entry : ∀ B, f.blocks[0]? = some B → (B.params.map (·.1)).Nodup ∧
    ∀ x ∈ A 0 0, x ∈ B.params.map (·.1) ∧ ctx.defInst? x = none
  /-- closure: a tracked value's pure definition has tracked operands -/
  closed : ∀ bi j x d info cl, x ∈ A bi j → ctx.defInst? x = some d → ctx.insts[d]? = some info →
    info.clif = some cl → pureInst cl = true → ∀ y ∈ instArgs cl, y ∈ A bi j
  /-- statements -/
  stmt : ∀ bi B L j stm sl, f.blocks[bi]? = some B → bl[bi]? = some L → B.body[j]? = some stm →
    L.sl[j]? = some sl →
    (∀ y ∈ instArgs stm.inst, y ∈ A bi j) ∧
    (∀ r ∈ stm.results, r ∉ A bi j ∧ ctx.defInst? r = some (L.start + j)) ∧ stm.results.Nodup ∧
    (∀ x ∈ A bi (j + 1), x ∈ A bi j ∨ x ∈ stm.results) ∧
    (∀ x ∈ A bi j, ¬ (sl.st.nextVreg ≤ gn x ∧ gn x < sl.st'.nextVreg))
  /-- terminators and edges -/
  term : ∀ bi B L, f.blocks[bi]? = some B → bl[bi]? = some L →
    (∀ y ∈ termArgs B.term, y ∈ A bi B.body.length) ∧
    (∀ x ∈ A bi B.body.length, ¬ (L.tst.nextVreg ≤ gn x ∧ gn x < L.tst'.nextVreg)) ∧
    ∀ bc ∈ dests B.term, ∀ tl TB, blockIdx? f bc.block = some tl → f.blocks[tl]? = some TB →
      (TB.params.map (·.1)).Nodup ∧
      (∀ p ∈ TB.params, p.1 ∉ A bi B.body.length) ∧
      ∀ x ∈ A tl 0, (x ∈ TB.params.map (·.1) ∧ ctx.defInst? x = none) ∨
        (x ∉ TB.params.map (·.1) ∧ x ∈ A bi B.body.length ∧ gn x ∉ TB.params.map (·.1))

end Backend.Proof.Driver
