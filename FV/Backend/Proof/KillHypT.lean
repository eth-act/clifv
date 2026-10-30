import FV.Backend.Proof.KillAssemble
import FV.Backend.Proof.LowerLoopCtxT

/-!
# The killed-vreg facts of the ISLE runs over the typed scope: the statements (S11 slice 8)

`KillRunsHypT` and `TryDefsExactT`: `KillRunsHyp` (`KillBase.lean`) and `TryDefsExact`
(`KillAssemble.lean`) on input in the typed movement scope (`LowerScopeT` in place of
`LowerScope`). The facts are about vreg numbers only (fresh vregs killed, uses below the run's
counter, a `try_call`'s exact defs), so their statements do not change; proven in
`KillDriverT.lean` (`killRunsHypT`, `tryDefsExactT`).
-/

namespace Backend.Proof.Kill

open Backend Backend.Proof Backend.Proof.Driver Backend.Proof.Spill

/-- **`KillRunsHyp` over the typed scope**: on `Dominated`, `LowerScopeT`, `AbiSigsOk` input,
every ISLE run of the driver meets `RunKill` (and a statement's results `OutKill`), and a
`try_call`'s calls define only its result vregs. -/
def KillRunsHypT : Prop :=
  ∀ (f : Clif.Function) (ctx : Ctx) (ranges : Array (Nat × Nat)) (st0 : LState),
    Dominated f → LowerScopeT f → AbiSigsOk f → buildCtx f = .ok (ctx, ranges, st0) →
    (∀ ii info inst s out s' tr, ctx.insts[ii]? = some info → info.clif = some inst →
      ctx.valDef.size ≤ s.nextVreg →
      runTerm ctx "lower" [.inst ii] s = .ok (out, s', tr) →
      RunKill ctx.valDef.size s.nextVreg s s' ∧
        (info.results ≠ [] → OutKill ctx.valDef.size s.nextVreg s s' out)) ∧
    (∀ ti t data targets s out s' tr, ti < ctx.insts.size →
      ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩ → t.isTry = false →
      termData (abiTerm f t) = .ok data → ctx.valDef.size ≤ s.nextVreg →
      termCallF ctx ti data t targets s = .ok (out, s', tr) →
      RunKill ctx.valDef.size s.nextVreg s s') ∧
    (∀ ti t et data sig items lo trs st1 targets out s' tr, ti < ctx.insts.size →
      ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩ → IsTryWith t et → (∃ B ∈ f.blocks, B.term = t) →
      tryCallData f t = .ok data → exnTableOpnd f et = .ok (sig, items) →
      ctx.valDef.size ≤ lo.nextVreg → tryRegsOf sig lo = some (trs, st1) →
      tryCallF ctx ti data trs targets { st1 with emitted := #[] } = .ok (out, s', tr) →
      RunKill ctx.valDef.size st1.nextVreg { st1 with emitted := #[] } s' ∧
        ∀ m ∈ s'.emitted.toList, ∀ c, m = .call c → ∀ q ∈ c.defs, ∀ n cl, q.2 = .vreg n cl →
          q.2 ∈ trs.1 ∨ q.2 ∈ trs.2)

/-- **`TryDefsExact` over the typed scope**: a `try_call`'s call defines exactly its return and
payload vregs, in order. Over the declared returns since #587, as `TryDefsExact`: an `sret`
callee's struct pointer gets no vreg, so the pre-#587 `sigRets` count became false for it. -/
def TryDefsExactT : Prop :=
  ∀ (f : Clif.Function) (ctx : Ctx) (ranges : Array (Nat × Nat)) (st0 : LState),
    Dominated f → LowerScopeT f → AbiSigsOk f → buildCtx f = .ok (ctx, ranges, st0) →
    ∀ ti t et data sig items lo trs st1 targets out s' tr, ti < ctx.insts.size →
      ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩ → IsTryWith t et → (∃ B ∈ f.blocks, B.term = t) →
      tryCallData f t = .ok data → exnTableOpnd f et = .ok (sig, items) →
      ctx.valDef.size ≤ lo.nextVreg → tryRegsOf sig lo = some (trs, st1) →
      tryCallF ctx ti data trs targets { st1 with emitted := #[] } = .ok (out, s', tr) →
      ∀ m ∈ s'.emitted.toList, ∀ c, m = .call c →
        c.defs = callDefs (outDefs lo.nextVreg (max sig.returns.length 2))

/-- The typed facts give the integer ones (`LowerScope.toT`). -/
theorem KillRunsHypT.toInt (h : KillRunsHypT) : KillRunsHyp :=
  fun f ctx ranges st0 hd hs ha hb => h f ctx ranges st0 hd hs.toT ha hb

/-- The typed facts give the integer ones (`LowerScope.toT`). -/
theorem TryDefsExactT.toInt (h : TryDefsExactT) : TryDefsExact :=
  fun f ctx ranges st0 hd hs ha hb => h f ctx ranges st0 hd hs.toT ha hb

end Backend.Proof.Kill
