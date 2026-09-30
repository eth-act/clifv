import FV.Backend.Proof.LowerFrame

/-!
# What `lowerFunction` builds, and the SSA certificate (M7 driver)

`LowerShape f vc …`: the structure of the VCode `lowerFunction f` returns, per CLIF block —
the entry `Args`, one segment per statement (the `lower` call's emitted code, renamed by the
alias resolution `R`), the terminator's segment (`lower`/`lower_branch`), block parameters,
jump arguments, edge blocks, labels = indices (the shared definitions `seg`, `pre`, `tseg`, … are
in `DriverCheck.lean`). Discharged by the lowering validator: `lowerCheck f vc = true` implies it
(`DriverCheckSound.lean`).

`Cert f … A`: an availability annotation `A bi j` (the values the driver tracks before statement
`j` of block `bi`) with local, checkable conditions: operands available, results fresh, no
available value's register is written by the lowering of the statement, closure under pure
definitions, edges. It holds for SSA input with `A` = the values whose definition strictly
dominates the point; the validator computes `A` by a must-dataflow and checks the conditions.
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof

variable (f : Clif.Function) (vc : VCode) (ctx : Ctx) (st0 : LState) (R : Reg → Reg)
  (gn : Nat → Nat) (bl : List BLow)

/-- **The structure of `lowerFunction f`'s VCode.** -/
structure LowerShape : Prop where
  hctx : ∃ ranges, buildCtx f = .ok (ctx, ranges, st0)
  /-- M4's context invariants (`buildCtx` ⇒ `CtxInv`, the probe's gap) -/
  ctxInv : CtxInv f ctx
  ren : VRenaming R gn
  temps : ∀ n, st0.nextVreg ≤ n → gn n = n
  params : ∀ B ∈ f.blocks, ∀ p ∈ B.params, gn p.1 = p.1
  len : bl.length = f.blocks.length
  size : f.blocks.length ≤ vc.blocks.size
  /-- every value with a register is below the first temporary (`buildCtx`: `maxV`) -/
  valsBelow : ∀ x r, ctx.valueReg? x = some r → x < st0.nextVreg
  labels : ∀ l (vb : VBlock), vc.blocks[l]? = some vb → vb.label = l
  /-- the terminator's slot in `ctx.insts` is `buildCtx`'s placeholder -/
  tslot : ∀ (bi : Nat) (B : Clif.Block) (L : BLow), f.blocks[bi]? = some B → bl[bi]? = some L →
    ctx.insts[L.start + B.body.length]? = some (⟨.op .unit, [], [], none⟩ : IInfo)
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
    -- terminator (a `return` of an `sret` function also returns the struct pointer, `abiTerm`)
    L.tst.emitted = #[] ∧ st0.nextVreg ≤ L.tst.nextVreg ∧
    (B.term.isTry = false → L.tl = none ∧ termData (abiTerm f B.term) = .ok L.data ∧
      ∃ out tr, runTerm (termCtx ctx (L.start + B.body.length) L.data)
        (termCall B.term (L.start + B.body.length) L.targets).1
        (termCall B.term (L.start + B.body.length) L.targets).2 L.tst = .ok (some out, L.tst', tr)) ∧
    -- a `try_call`: its data, exception table, return/payload vregs (allocated from `L.tst`),
    -- `try_call_info`, and the `lower_branch` call from the state after the allocation
    (∀ fn args et, B.term = .tryCall fn args et → ∃ T, L.tl = some T ∧
      tryCallData f B.term = .ok L.data ∧ exnTableOpnd f et = .ok (T.sig, T.items) ∧
      tryRegsOf T.sig L.tst = some (T.regs, T.st1) ∧ tryInfoOf T.sig T.items L.targets = some T.info ∧
      ∃ out tr, runTerm (tryCtx ctx (L.start + B.body.length) L.data T.regs) "lower_branch"
        [.inst (L.start + B.body.length), .labels L.targets] { T.st1 with emitted := #[] } =
        .ok (some out, L.tst', tr)) ∧
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
      | .tryCall _ _ et => L.targets.length = et.dests.length ∧
        ∃ tl tlab T eb, blockIdx? f et.normal.block = some tl ∧ L.targets.getLast? = some tlab ∧
          L.tl = some T ∧ vc.blocks[tlab]? = some eb ∧ eb.insts = #[.jump tl] ∧ eb.params = #[] ∧
          eb.branchArgs = (et.normal.args.map (normArgReg R T.regs.1)).toArray ∧
          ∀ a ∈ et.normal.args, match a with
            | .val _ => True
            | .ret i => i < T.sig.returns.length
            | .exn _ => False
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
  /-- no edge targets the entry block (CLIF verifier rule) -/
  noEntry : ∀ (bi : Nat) (B : Clif.Block), f.blocks[bi]? = some B → ∀ b ∈ edgeIds B.term, blockIdx? f b ≠ some 0
  /-- terminators and edges (a `try_call`'s: to its normal return) -/
  term : ∀ bi B L, f.blocks[bi]? = some B → bl[bi]? = some L →
    (∀ y ∈ termArgs (abiTerm f B.term), y ∈ A bi B.body.length) ∧
    (∀ x ∈ A bi B.body.length, ¬ (L.tst.nextVreg ≤ gn x ∧ gn x < L.tst'.nextVreg)) ∧
    ∀ b ∈ edgeIds B.term, ∀ tl TB, blockIdx? f b = some tl → f.blocks[tl]? = some TB →
      (TB.params.map (·.1)).Nodup ∧
      (∀ x ∈ A tl 0, x ∉ TB.params.map (·.1) → ∀ d info cl, ctx.defInst? x = some d →
        ctx.insts[d]? = some info → info.clif = some cl → ∀ y ∈ instArgs cl,
          y ∉ TB.params.map (·.1)) ∧
      ∀ x ∈ A tl 0, (x ∈ TB.params.map (·.1) ∧ ctx.defInst? x = none) ∨
        (x ∉ TB.params.map (·.1) ∧ x ∈ A bi B.body.length ∧ gn x ∉ TB.params.map (·.1))
  /-- a statement result's context type is its declared type (`buildCtx` writes `valTy` for
  every definition, the last write wins: needs unique definitions) -/
  resTy : ∀ (ii : Nat) (info : IInfo), ctx.insts[ii]? = some info → ∀ (m : Nat) r t, info.results[m]? = some r →
    info.resTys[m]? = some t → ctx.valueType? r = some t
  /-- a block parameter's context type is its declared type -/
  paramTy : ∀ B ∈ f.blocks, ∀ q ∈ B.params, ctx.valueType? q.1 = some (CTy.ofClif q.2)

end Backend.Proof.Driver
