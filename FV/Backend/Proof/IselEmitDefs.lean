import FV.Backend.Proof.LowerCover
import FV.Backend.EmitOk

/-!
# Emission conditions of the ISLE lowering (V6c): the statements

* `EmSince s0 s`: every instruction emitted since `s0` has `MInst.emitOk` and no branch targets
  (the state invariant of the emission analysis, `IselEmitModel`); `EmLast s0 s`: the same, except
  that the last one may have branch targets (a terminator's run, `IselEmitLast`).
* `ExtendsWiden ctx`: every `uextend`/`sextend` of the context widens (CLIF's verifier rule; the
  run semantics rejects the others, `Clif.Run`). `extendsWidenB f` decides it on `buildCtx f`:
  the input condition the `uextend`/`sextend` rules (808, 819) need (`IselEmitHand`).
* `StmtEmit`/`TermEmit`/`TryEmit`/`IselEmit`: the ISLE runs of the driver emit only `emitOk`
  instructions, branch targets only on a terminator run's last instruction (`IselEmitDriver`).
-/

namespace Backend.Proof.Driver
open Backend Isle

/-- Every instruction emitted since `s0` has the emission conditions and no branch targets. -/
def EmSince (s0 s : LState) : Prop :=
  ∃ ms : List MInst, s.emitted = s0.emitted ++ ms.toArray ∧ ∀ m ∈ ms, m.emitOk = true ∧ m.targets = []

/-- Every instruction emitted since `s0` has the emission conditions; only the last one may have
branch targets. -/
def EmLast (s0 s : LState) : Prop :=
  ∃ ms : List MInst, s.emitted = s0.emitted ++ ms.toArray ∧ (∀ m ∈ ms, m.emitOk = true) ∧
    ∀ m ∈ ms.dropLast, m.targets = []

/-- Every `uextend`/`sextend` of the context widens: its operand has a type narrower than the
result's. -/
def ExtendsWiden (ctx : Ctx) : Prop :=
  ∀ (ii : Nat) (info : IInfo) (op : Clif.ExtendOp) (ty : Clif.Ty) (x : Nat), ctx.insts[ii]? = some info →
    info.clif = some (.extend op ty x) →
    ∃ t, ctx.valueType? x = some t ∧ t.bits < (CTy.ofClif ty).bits

/-- **The input condition of the extends**: every `uextend`/`sextend` widens (decided on the
context `buildCtx f`; vacuous if `buildCtx` fails). -/
def extendsWidenB (f : Clif.Function) : Bool :=
  match buildCtx f with
  | .ok (ctx, _, _) => ctx.insts.all fun info =>
    match info.clif with
    | some (.extend _ ty x) =>
      match ctx.valueType? x with
      | some t => decide (t.bits < (CTy.ofClif ty).bits)
      | none => false
    | _ => true
  | .error _ => true

/-- Every statement's `lower` run emits only instructions with the emission conditions and no
branch targets. -/
def StmtEmit (ctx : Ctx) : Prop :=
  ∀ ii info inst s out s' tr, ctx.insts[ii]? = some info → info.clif = some inst →
    runTerm ctx "lower" [.inst ii] s = .ok (out, s', tr) → EmSince s s'

/-- Every non-`try_call` terminator's run: the emission conditions; branch targets only on the
last instruction. -/
def TermEmit (f : Clif.Function) (ctx : Ctx) : Prop :=
  ∀ ti t data targets s out s' tr, ti < ctx.insts.size →
    ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩ → t.isTry = false →
    termData (abiTerm f t) = .ok data →
    termCallF ctx ti data t targets s = .ok (out, s', tr) → EmLast s s'

/-- Every `try_call` terminator's run: the emission conditions; branch targets only on the last
instruction. -/
def TryEmit (f : Clif.Function) (ctx : Ctx) : Prop :=
  ∀ ti t data trs targets s out s' tr, ti < ctx.insts.size →
    ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩ → tryCallData f t = .ok data →
    tryCallF ctx ti data trs targets s = .ok (out, s', tr) → EmLast s s'

/-- The ISLE runs of the driver on `f`. -/
def IselEmit (f : Clif.Function) : Prop :=
  ∀ ctx ranges st0, buildCtx f = .ok (ctx, ranges, st0) → StmtEmit ctx ∧ TermEmit f ctx ∧ TryEmit f ctx

end Backend.Proof.Driver
