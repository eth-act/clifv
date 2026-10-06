import FV.Backend.Proof.LowerCover
import FV.Backend.EmitOk
namespace Backend.Proof.Driver
open Backend Isle
/-- Every statement's `lower` run emits only instructions with the emission conditions and no branch targets. -/
def StmtEmit (ctx : Ctx) : Prop :=
  ∀ ii info inst s out s' tr, ctx.insts[ii]? = some info → info.clif = some inst →
    runTerm ctx "lower" [.inst ii] s = .ok (out, s', tr) →
    ∃ ms : List MInst, s'.emitted = s.emitted ++ ms.toArray ∧ ∀ m ∈ ms, m.emitOk = true ∧ m.targets = []
/-- Every non-`try_call` terminator's run: the emission conditions; branch targets only on the last instruction. -/
def TermEmit (f : Clif.Function) (ctx : Ctx) : Prop :=
  ∀ ti t data targets s out s' tr, ti < ctx.insts.size →
    ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩ → t.isTry = false →
    termData (abiTerm f t) = .ok data →
    termCallF ctx ti data t targets s = .ok (out, s', tr) →
    ∃ ms : List MInst, s'.emitted = s.emitted ++ ms.toArray ∧ (∀ m ∈ ms, m.emitOk = true) ∧
      ∀ m ∈ ms.dropLast, m.targets = []
/-- Every `try_call` terminator's run: the emission conditions, no branch targets. -/
def TryEmit (f : Clif.Function) (ctx : Ctx) : Prop :=
  ∀ ti t data trs targets s out s' tr, ti < ctx.insts.size →
    ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩ → tryCallData f t = .ok data →
    tryCallF ctx ti data trs targets s = .ok (out, s', tr) →
    ∃ ms : List MInst, s'.emitted = s.emitted ++ ms.toArray ∧ ∀ m ∈ ms, m.emitOk = true ∧ m.targets = []
/-- The ISLE runs of the driver on `f`. -/
def IselEmit (f : Clif.Function) : Prop :=
  ∀ ctx ranges st0, buildCtx f = .ok (ctx, ranges, st0) → StmtEmit ctx ∧ TermEmit f ctx ∧ TryEmit f ctx
end Backend.Proof.Driver
