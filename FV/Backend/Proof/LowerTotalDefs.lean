import FV.Backend.Proof.LowerLoopCode

/-!
# Totality of the lowering: what the driver needs of the ISLE runs (V7)

`lowerFunction` (`FV/Backend/Isel.lean`) fails only at its own checks or when an ISLE run of
`lower`/`lower_branch` throws, returns no value, or returns registers of the wrong shape. The
driver's totality (`LowerTotal.lean`) takes the ISLE side as these three properties of the
lowering context; the ISLE progress analysis (`IselPrg*`) proves them for input in scope.

* `StmtProg ctx`: every statement's `lower` returns one single-register result per CLIF result;
* `TermProg f ctx`: every non-`try_call` terminator's `lower`/`lower_branch` returns a value;
* `TryProg f ctx`: every `try_call`'s `lower_branch` returns a value and its code ends in a call.
-/

namespace Backend.Proof.Driver

open Backend

/-- Every statement's `lower` run returns registers: one single register per CLIF result. -/
def StmtProg (ctx : Ctx) : Prop :=
  ∀ ii info inst s, ctx.insts[ii]? = some info → info.clif = some inst →
    ∃ rss s' tr, runTerm ctx "lower" [.inst ii] s = .ok (some (.regsVec rss), s', tr) ∧
      (info.results ≠ [] → rss.length = info.results.length ∧ ∀ rs ∈ rss, rs.length = 1)

/-- Every non-`try_call` terminator of `f` (at its placeholder slot `ti`, with one target per
successor) has a `lower`/`lower_branch` run that returns a value. -/
def TermProg (f : Clif.Function) (ctx : Ctx) : Prop :=
  ∀ ti t data targets s, ti < ctx.insts.size →
    ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩ → (∃ B ∈ f.blocks, B.term = t) →
    t.isTry = false → termData (abiTerm f t) = .ok data →
    targets.length = (destsOf t).length →
    ∃ v s' tr, termCallF ctx ti data t targets s = .ok (some v, s', tr)

/-- The exception table of a `try_call`/`try_call_indirect`. -/
def exnOf : Clif.Terminator → Option Clif.ExnTable
  | .tryCall _ _ et | .tryCallIndirect _ _ et => some et
  | _ => none

/-- Every `try_call` terminator of `f` (at its placeholder slot `ti`, with its return/payload
vregs `trs` from `tryRegsOf` and one target per exception-table item plus the continuation) has
a `lower_branch` run that returns a value and whose code ends in a call. -/
def TryProg (f : Clif.Function) (ctx : Ctx) : Prop :=
  ∀ ti t et data sig items trs st1 st2 targets s, ti < ctx.insts.size →
    ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩ → (∃ B ∈ f.blocks, B.term = t) →
    exnOf t = some et → tryCallData f t = .ok data → exnTableOpnd f et = .ok (sig, items) →
    tryRegsOf sig st1 = some (trs, st2) → targets.length = items.length + 1 →
    ∃ v s' tr c, tryCallF ctx ti data trs targets s = .ok (some v, s', tr) ∧
      s'.emitted.back? = some (.call c)

/-- The ISLE side of the driver's totality, for the context `buildCtx f` builds. -/
structure IselProg (f : Clif.Function) (ctx : Ctx) : Prop where
  stmt : StmtProg ctx
  term : TermProg f ctx
  try_ : TryProg f ctx

end Backend.Proof.Driver
