import FVTest.Backend.FloatCtlRulesT
import FV.Backend.Proof.IselCtlCallF

/-!
Non-vacuity of the typed `call` family with `f32`/`f64` arguments and returns (S11e6, #419):
`buildCtx`'s contexts of functions calling float-taking callees are `CallCtxT` contexts
(`callCtxOkB`, `native_decide`, witness only), while `CtxInvT` fails on them (it types every
`call` argument as an integer), and the `call` roots of `lower` fire on their calls:

* `fCallF` calls `%g(f64, i64, f32) -> f64`: the call's fixed uses are v0 (the `f64`), x0 (the
  `i64`) and v1 (the `f32`), its def is v0 into a fresh float vreg (rule 1032, GOT + `blr`);
* `fCallStk` calls `%h` with nine `f64` arguments: the ninth is stored by `str d` at `[sp]`
  (`stackArgStore` of a float vreg) and the call returns an `f32` from v0.

`callRulesCorrectTFP_program` applies to both (`callF_roots_apply`).
`lake build FVTest.Backend.FloatCallF`.
-/

open Backend Backend.Proof Backend.Proof.Driver Isle.Aarch64

namespace FloatCallF

open FloatCtlT FloatCtlRulesT

/-- A call of a float-taking callee with mixed classes. -/
def fCallF : Clif.Function := fnOfText
  "function %c(f64, i64, f32) -> f64 {
    fn0 = %g(f64, i64, f32) -> f64
block0(v0: f64, v1: i64, v2: f32):
    v3 = call fn0(v0, v1, v2)
    return v3
}
"

/-- Nine `f64` arguments (the ninth passed on the stack), an `f32` return. -/
def fCallStk : Clif.Function := fnOfText
  "function %s(f64) -> f32 {
    fn0 = %h(f64, f64, f64, f64, f64, f64, f64, f64, f64) -> f32
block0(v0: f64):
    v1 = call fn0(v0, v0, v0, v0, v0, v0, v0, v0, v0)
    return v1
}
"

/-- The code `lower` emits for instruction `ii` of `f`'s context (`[]` if it fails). -/
def lowerCode (f : Clif.Function) (ii : Nat) : List MInst :=
  let (ctx, st) := ctxStOf f
  match runTerm ctx "lower" [.inst ii] st with
  | .ok (some _, st', _) => st'.emitted.toList
  | _ => []

/-- The `call` instructions of a code sequence. -/
def callsOf (ms : List MInst) : List CallInfo :=
  ms.filterMap fun | .call ci => some ci | _ => none

#guard (buildCtx fCallF).toBool && (buildCtx fCallStk).toBool
#guard (ctxStOf fCallF).1.insts[0]?.bind (·.clif) matches some (Clif.Inst.call ..)
-- `lower` fires the GOT + `blr` root (1032, a non-colocated extern) on the calls
#guard (lowerTrace fCallF 0).contains 1032 && (lowerTrace fCallStk 0).contains 1032
-- `fCallF`: the `f64` in v0, the `i64` in x0, the `f32` in v1; the `f64` result from v0
#guard (callsOf (lowerCode fCallF 0)).map (·.uses.map (·.2)) == [[.v 0, .x 0, .v 1]]
#guard (callsOf (lowerCode fCallF 0)).all fun ci =>
  ci.uses.map (·.1) == [.vreg 0 .float, .vreg 1 .int, .vreg 2 .float] &&
    ci.defs.map (·.1) == [.v 0] && ci.defs.all (·.2.homeCls == .float)
-- `fCallStk`: eight arguments in v0..v7, the ninth stored by `str d` at `[sp]`; the `f32` result
-- from v0
#guard (lowerCode fCallStk 0).any fun
  | .fpuStore .size64 (.vreg 0 .float) (.spOffset 0) _ => true
  | _ => false
#guard (callsOf (lowerCode fCallStk 0)).map (·.uses.map (·.2)) ==
  [(List.range 8).map Reg.v]
#guard (callsOf (lowerCode fCallStk 0)).all fun ci =>
  ci.defs.map (·.1) == [.v 0] && ci.defs.all (·.2.homeCls == .float)
-- `CtxInvT` fails on both (a `call` argument of float type), `CallCtxT` holds
#guard !ctxOkT fCallF (ctxStOf fCallF).1 && !ctxOkT fCallStk (ctxStOf fCallStk).1

theorem callCtx_fCallF : CallCtxT fCallF (ctxStOf fCallF).1 := callCtxOkB_sound (by native_decide)

theorem callCtx_fCallStk : CallCtxT fCallStk (ctxStOf fCallStk).1 :=
  callCtxOkB_sound (by native_decide)

/-- `CtxInvT` types the arguments of a `call` as integers, so it fails on `fCallF`'s context. -/
theorem not_ctxInvT_fCallF : ¬ CtxInvT fCallF (ctxStOf fCallF).1 := by
  intro h
  have hc0 : ((ctxStOf fCallF).1.insts[0]?.bind (·.clif)) = some (.call 0 [0, 1, 2]) := by
    native_decide
  have ht : (ctxStOf fCallF).1.valueType? 0 = some (.float 64) := by native_decide
  cases hi : (ctxStOf fCallF).1.insts[0]? with
  | none => rw [hi] at hc0; cases hc0
  | some info =>
    rw [hi] at hc0
    have := h.intOps 0 info _ hi hc0 0 (by simp [intArgs]) _ ht
    simp [eCTys] at this

/-- **The float `call` family applies to both contexts**: `CallCtxT` contexts whose instruction 0
is a `call` of an extern with an `f64` parameter, and rule 1032 (`rule_lower_2518`) is a `call`
root of `lower`, so `callRulesCorrectTFP_program` gives `CallRuleOkTFP` on them. -/
theorem callF_roots_apply :
    CallCtxT fCallF (ctxStOf fCallF).1 ∧ CallCtxT fCallStk (ctxStOf fCallStk).1 ∧
      (∃ fn args e, (ctxStOf fCallF).1.insts[0]?.bind (·.clif) = some (.call fn args) ∧
        fCallF.extern? fn = some e ∧ e.sig.params.any (·.ty == .f64) = true) ∧
      rule_lower_2518 ∈ program.rulesOf TId.lower ∧ callRootRule rule_lower_2518 = true :=
  ⟨callCtx_fCallF, callCtx_fCallStk,
    ⟨0, [0, 1, 2], (fCallF.extern? 0).get!, by native_decide, by native_decide, by native_decide⟩,
    mem_lower_2518, rfl⟩

/-- The family's conclusion for rule 1032 (every premise other than the context's is the run's). -/
theorem callF_rule_1032 : ∀ (Rd : BitVec 64 → Prop)
    (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop) (F : BitVec 64 → Prop)
    (isem : Sem) (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (exts : List Clif.ExtFunc)
    (sb : Nat) (syms : String → Option Nat) (outB : Nat),
    Refines F isem → MRStable F MR → MemRefinesR Rd F sb syms isem → MemRefinesFP Rd F sb isem →
    OutArgsOk F outB MR → CallsRefineP Pc F env exts MR isem →
    CallRuleOkTFP Rd Pc isem MR env cp exts outB program rule_lower_2518 :=
  fun Rd Pc F isem MR env cp exts sb syms outB hR hMR hMem hFP hout hCR =>
    callRulesCorrectTFP_program Rd Pc F isem MR env cp exts sb syms outB hR hMR hMem hFP hout hCR
      _ mem_lower_2518 rfl

end FloatCallF
