import FV.Backend.Proof.DriverCheckTyC
import FV.Backend.Proof.LowerContract

/-!
# Scope-generic typed shapes (#1002 part 2)

The typed lowering facts never depend on which instructions a context may contain, except where
a rule is matched. So the typed structures that carry an instruction scope are stated once over
an abstract scope `S : InstScope`: a predicate on lowering contexts with the two properties the
typed driver proofs need of it (filling in a terminator's data at `buildCtx`'s placeholder and
replacing the `try_call` vregs keep it).

* `InstScope`, `InstScope.ofInsts` (a scope given by a test on each CLIF instruction),
  `InstScope.tf` (`InstScopeTF`: `Compile.instETF`) and `InstScope.tfl` (`InstScopeTFL`:
  `Compile.instETFL`, an `f64const` from the literal pool also);
* `Driver.LowerShapeTCS S`: `LowerShapeTC` with the scope `S.P` (`LowerShapeTC.toS`: the
  instance at `InstScope.tf`).

The validator with the literal pool gives `LowerShapeTCS InstScope.tfl`
(`Driver.loweringTCF_of_check`). `LowerShapeTC` and its theorems are unchanged.
-/

namespace Backend.Proof

open Backend Backend.Proof.Driver

/-- **An instruction scope of the typed lowering contexts** (#1002 part 2): a predicate on
lowering contexts with the two properties the typed driver proofs need of it. -/
structure InstScope where
  /-- the contexts in the scope -/
  P : Ctx → Prop
  /-- filling in a terminator's data at `buildCtx`'s placeholder keeps the scope -/
  termCtxOk : ∀ (ctx : Ctx) (ti : Nat) (data : V),
    ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩ → P ctx → P (termCtx ctx ti data)
  /-- the `try_call` vregs do not matter -/
  tryRegsOk : ∀ (ctx : Ctx) (trs : List Reg × List Reg), P ctx → P { ctx with tryRegs := trs }

/-- **The scope of the contexts whose CLIF instructions pass `Q`.** -/
def InstScope.ofInsts (Q : Clif.Inst → Bool) : InstScope where
  P ctx := ∀ (ii : Nat) (info : IInfo) (inst : Clif.Inst), ctx.insts[ii]? = some info →
    info.clif = some inst → Q inst = true
  termCtxOk ctx ti data hph h ii info inst hi hc := by
    by_cases e : ii = ti
    · subst e; rw [termCtx_insts_self hph] at hi; cases hi; cases hc
    · rw [termCtx_insts_ne e] at hi; exact h ii info inst hi hc
  tryRegsOk _ _ h := h

/-- The scope with the proven float operations (`InstScopeTF`). -/
def InstScope.tf : InstScope := .ofInsts Compile.instETF

/-- The scope with the proven float operations and the literal pool (`InstScopeTFL`). -/
def InstScope.tfl : InstScope := .ofInsts Compile.instETFL

theorem InstScope.tf_P {ctx : Ctx} : InstScope.tf.P ctx ↔ InstScopeTF ctx := Iff.rfl

theorem InstScope.tfl_P {ctx : Ctx} : InstScope.tfl.P ctx ↔ InstScopeTFL ctx := Iff.rfl

end Backend.Proof

namespace Backend.Proof.Driver

open Backend Backend.Proof

section
variable (S : InstScope) (f : Clif.Function) (vc : VCode) (ctx : Ctx) (st0 : LState)
  (R : Reg → Reg) (gn : Nat → Nat) (bl : List BLow)

/-- **`LowerShapeTC` over the scope `S`** (#1002 part 2): the same facts, the context's
instructions in `S.P`. -/
structure LowerShapeTCS : Prop where
  hctx : ∃ ranges, buildCtx f = .ok (ctx, ranges, st0)
  ctxInvT : CtxInvT f ctx
  scope : S.P ctx
  ren : VRenaming R gn
  temps : ∀ n, st0.nextVreg ≤ n → gn n = n
  params : ∀ B ∈ f.blocks, ∀ p ∈ B.params, gn p.1 = p.1
  len : bl.length = f.blocks.length
  size : f.blocks.length ≤ vc.blocks.size
  valsBelow : ∀ x r, ctx.valueReg? x = some r → x < st0.nextVreg
  labels : ∀ l (vb : VBlock), vc.blocks[l]? = some vb → vb.label = l
  fresh : st0.nextVreg ≤ f.freshValue
  tslot : ∀ (bi : Nat) (B : Clif.Block) (L : BLow), f.blocks[bi]? = some B → bl[bi]? = some L →
    ctx.insts[L.start + B.body.length]? = some (⟨.op .unit, [], [], none⟩ : IInfo)
  blk : ∀ bi B L, f.blocks[bi]? = some B → bl[bi]? = some L →
    ∃ vb, vc.blocks[bi]? = some vb ∧
    L.sl.length = B.body.length ∧
    (∀ j stm sl, B.body[j]? = some stm → L.sl[j]? = some sl →
      (∃ info, ctx.insts[L.start + j]? = some info ∧ info.clif = some stm.inst ∧
        info.results = stm.results) ∧
      sl.st.emitted = #[] ∧ st0.nextVreg ≤ sl.st.nextVreg ∧
      (∃ tr, runTerm ctx "lower" [.inst (L.start + j)] sl.st = .ok (some (.regsVec sl.rss), sl.st', tr)) ∧
      (∀ (k : Nat) r out cls, stm.results[k]? = some r → sl.rss[k]? = some [.vreg out cls] →
        gn r = gn out)) ∧
    L.tst.emitted = #[] ∧ st0.nextVreg ≤ L.tst.nextVreg ∧
    (B.term.isTry = false → L.tl = none ∧ termData (abiTerm f B.term) = .ok L.data ∧
      ∃ out tr, runTerm (termCtx ctx (L.start + B.body.length) L.data)
        (termCall B.term (L.start + B.body.length) L.targets).1
        (termCall B.term (L.start + B.body.length) L.targets).2 L.tst = .ok (some out, L.tst', tr)) ∧
    (∀ et, IsTryWith B.term et → ∃ T, L.tl = some T ∧
      tryCallDataC f B.term = .ok L.data ∧ exnTableOpndC f et = .ok (T.sig, T.items) ∧
      tryRegsOfC T.sig L.tst = some (T.regs, T.st1) ∧ tryInfoOf T.sig T.items L.targets = some T.info ∧
      ∃ out tr, runTerm (tryCtx ctx (L.start + B.body.length) L.data T.regs) "lower_branch"
        [.inst (L.start + B.body.length), .labels L.targets] { T.st1 with emitted := #[] } =
        .ok (some out, L.tst', tr)) ∧
    vb.insts.toList = preT f ctx R bi ++ ((List.range B.body.length).map (segT f ctx R bl bi)).flatten ++
      tseg R bl bi ∧
    tseg R bl bi ≠ [] ∧
    vb.params = (if bi = 0 then #[] else (B.params.map fun p => vregOf ctx p.1).toArray) ∧
    vb.branchArgs = (match B.term with
      | .jump bc => (bc.args.map fun a => R (vregOf ctx a)).toArray
      | _ => #[]) ∧
    (match B.term with
      | .jump bc => ∃ tl, blockIdx? f bc.block = some tl ∧ L.targets = [tl]
      | .tryCall _ _ et | .tryCallIndirect _ _ et => L.targets.length = et.dests.length ∧
        ∃ tl tlab T eb, blockIdx? f et.normal.block = some tl ∧ L.targets.getLast? = some tlab ∧
          L.tl = some T ∧ vc.blocks[tlab]? = some eb ∧ eb.insts = #[.jump tl] ∧ eb.params = #[] ∧
          eb.branchArgs = (et.normal.args.map (normArgRegT ctx R T.regs.1)).toArray ∧
          ∀ a ∈ et.normal.args, match a with
            | .val _ => True
            | .ret i => i < T.sig.returns.length
            | .exn _ => False
      | _ => L.targets.length = (dests B.term).length ∧
        ∀ (k : Nat) bc tlab, (dests B.term)[k]? = some bc → L.targets[k]? = some tlab →
          ∃ tl, blockIdx? f bc.block = some tl ∧
            (bc.args = [] → tlab = tl) ∧
            (bc.args ≠ [] → ∃ eb, vc.blocks[tlab]? = some eb ∧ eb.insts = #[.jump tl] ∧
              eb.params = #[] ∧ eb.branchArgs = (bc.args.map fun a => R (vregOf ctx a)).toArray))

end

/-- `LowerShapeTC` is `LowerShapeTCS` at the scope with the proven float operations. -/
theorem LowerShapeTC.toS {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState}
    {R : Reg → Reg} {gn : Nat → Nat} {bl : List BLow} (h : LowerShapeTC f vc ctx st0 R gn bl) :
    LowerShapeTCS InstScope.tf f vc ctx st0 R gn bl :=
  ⟨h.hctx, h.ctxInvT, h.scope, h.ren, h.temps, h.params, h.len, h.size, h.valsBelow, h.labels,
    h.fresh, h.tslot, h.blk⟩

end Backend.Proof.Driver
