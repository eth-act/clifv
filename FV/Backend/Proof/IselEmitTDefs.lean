module

public import FV.Backend.Proof.IselEmitDefs

@[expose] public section

/-!
# Emission conditions of the typed ISLE lowering (S11): the statements

* `BitcastsSameWidth ctx`: every `bitcast` of the context keeps the width (CLIF's verifier rule;
  the run semantics is stuck on the others, `Clif.Run`). `bitcastWidthB f` decides it on
  `buildCtx f`: the input condition the `bitcast` GPR → SIMD&FP rule (1083) needs, whose
  `mov_to_fpu` is at the operand's scalar size (`Size8` for an `i8`, not encodable).
* `TermEmitT`/`TryEmitT`/`IselEmitT`: `IselEmit` with the terminator clauses over the terminators
  of `f`'s blocks (`∀ B ∈ f.blocks`, as `FormsCoverCompleteT`'s `TermCovT`/`TryCovT`: the typed
  analysis takes a terminator's family from its block, `CovT.termFam_of`).
-/

namespace Backend.Proof.Driver
open Backend Isle

/-- Every `bitcast` of the context keeps the width: its operand has a type of the result type's
width. -/
def BitcastsSameWidth (ctx : Ctx) : Prop :=
  ∀ (ii : Nat) (info : IInfo) (ty : Clif.Ty) (fl : Clif.MemFlags) (x : Nat),
    ctx.insts[ii]? = some info → info.clif = some (.bitcast ty fl x) →
    ∃ t, ctx.valueType? x = some t ∧ t.bits = (CTy.ofClif ty).bits

/-- **The input condition of the bitcasts**: every `bitcast` keeps the width (decided on the
context `buildCtx f`; vacuous if `buildCtx` fails). -/
def bitcastWidthB (f : Clif.Function) : Bool :=
  match buildCtx f with
  | .ok (ctx, _, _) => ctx.insts.all fun info =>
    match info.clif with
    | some (.bitcast ty _ x) =>
      match ctx.valueType? x with
      | some t => t.bits == (CTy.ofClif ty).bits
      | none => false
    | _ => true
  | .error _ => true

/-- Every non-`try_call` terminator of `f`'s run (at its placeholder slot): the emission
conditions; branch targets only on the last instruction. -/
def TermEmitT (f : Clif.Function) (ctx : Ctx) : Prop :=
  ∀ B ∈ f.blocks, ∀ ti data targets s out s' tr, ti < ctx.insts.size →
    ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩ → B.term.isTry = false →
    termData (abiTerm f B.term) = .ok data →
    termCallF ctx ti data B.term targets s = .ok (out, s', tr) → EmLast s s'

/-- Every `try_call` terminator of `f`'s run (at its placeholder slot): the emission conditions;
branch targets only on the last instruction. -/
def TryEmitT (f : Clif.Function) (ctx : Ctx) : Prop :=
  ∀ B ∈ f.blocks, ∀ ti data trs targets s out s' tr, ti < ctx.insts.size →
    ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩ → tryCallData f B.term = .ok data →
    tryCallF ctx ti data trs targets s = .ok (out, s', tr) → EmLast s s'

/-- The ISLE runs of the driver on `f` (typed scope). -/
def IselEmitT (f : Clif.Function) : Prop :=
  ∀ ctx ranges st0, buildCtx f = .ok (ctx, ranges, st0) →
    StmtEmit ctx ∧ TermEmitT f ctx ∧ TryEmitT f ctx

/-- `BitcastsSameWidth` of the built context from the input condition. -/
theorem bitcastsSameWidth_of {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)}
    {st0 : LState} (hw : bitcastWidthB f = true) (hb : buildCtx f = .ok (ctx, ranges, st0)) :
    BitcastsSameWidth ctx := by
  intro ii info ty fl x hi hc
  unfold bitcastWidthB at hw
  rw [hb] at hw
  simp only at hw
  have h := (Array.all_eq_true_iff_forall_mem.mp hw) info (Array.mem_of_getElem? hi)
  rw [hc] at h
  simp only at h
  cases ht : ctx.valueType? x with
  | none => rw [ht] at h; cases h
  | some t => rw [ht] at h; exact ⟨t, rfl, by simpa using h⟩

end Backend.Proof.Driver
