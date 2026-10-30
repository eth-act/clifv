import FVTest.Backend.FloatCtlT
import FV.Backend.Proof.DriverCheckT
import FV.Backend.Proof.IselCtlUnmatchTI
import FV.Backend.Proof.IselCtlTermTI
import FV.Backend.Proof.IselCtlBranchTI
import FV.Compile.TryArgClass

/-!
Non-vacuity of the typed control families (S11e5 Stage C, slice 5). `buildCtx`'s contexts of
functions with float values are typed contexts (`CtxT`, by `ctxOkT` and the scope checks,
`native_decide`, witness only) and not integer ones (`CtxInv` fails on a float value):

* `FloatCtlT.fCtl` (`(f64, i64, f32) -> f64`): the proven terminator and branch families give the
  driver's terminator calls (`termCallsT_of_rules` with `lowerTermRulesCorrectT_program`,
  `termUnmatchableT_program`, `branchRulesCorrectT_program`,
  `branchExcludedUnmatchableT_program`), and its `return v0` puts the `f64` in `v0`
  (`retRegsT` of the value classes);
* `fCall` (an integer `call` and `call_indirect` between float values): the call roots 1031 and
  1033 fire on its subset-E call instructions (`callRulesCorrectTP_program`,
  `indRulesCorrectTP_program`);
* `fTry` (an integer `try_call` in a function with a float parameter and return): the `try_call`
  root fires on its terminator, whose arguments are in integer positions (`TermIntPos`,
  `tryRulesCorrectTP_program`); the other roots of `lower_branch` do not
  (`tryUnmatchableT_program`).
`lake build FVTest.Backend.FloatCtlRulesT`.
-/

open Backend Backend.Proof Backend.Proof.Driver Isle.Aarch64

namespace FloatCtlRulesT

open FloatCtlT

/-- `buildCtx`'s context and initial state of a function (an empty context if it fails). -/
def ctxStOf (f : Clif.Function) : Ctx × LState :=
  match buildCtx f with
  | .ok (ctx, _, st) => (ctx, st)
  | .error _ => ({ func := f, insts := #[], valTy := #[], valDef := #[], valReg := #[], slotOff := [] },
      default)

/-- The rule ids `lower` fires on instruction `ii` of `f`'s context (`[]` if it fails). -/
def lowerTrace (f : Clif.Function) (ii : Nat) : List Isle.RuleId :=
  let (ctx, st) := ctxStOf f
  match runTerm ctx "lower" [.inst ii] st with
  | .ok (some _, _, tr) => tr
  | _ => []

/-- The scope check of a context (every instruction in `Compile.instET`). -/
def scopeOkB (ctx : Ctx) : Bool :=
  ctx.insts.toList.all fun info =>
    match info.clif with
    | some c => Compile.instET c
    | none => true

theorem instScopeT_of {ctx : Ctx} (h : scopeOkB ctx = true) : InstScopeT ctx := by
  intro ii info inst hi hc
  have hm := List.all_eq_true.mp h info (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hi))
  simp only [hc] at hm
  exact hm

/-- A typed context from the decided checks. -/
theorem ctxT_of {f : Clif.Function} {ctx : Ctx} (h1 : ctxOkT f ctx = true) (h2 : scopeOkB ctx = true)
    (h3 : Compile.functionET f = true) : CtxT f ctx :=
  CtxT.ofExterns (ctxOkT_sound h1) (instScopeT_of h2) (functionET_externs h3)

/-- A float-classed value rules out the integer invariant. -/
theorem not_ctxInv_of {f : Clif.Function} {ctx : Ctx} {x : Nat}
    (h : ctx.valueReg? x = some (.vreg x .float)) : ¬ CtxInv f ctx := fun hc => by
  have := hc.valueReg x _ h
  cases this

/-- The trivial memory relation is stable. -/
theorem mrStable_true : MRStable (fun _ => True) (fun _ _ (_ : Arm.ArmState) => True) :=
  fun _ _ _ _ _ _ => trivial

/-! ## Terminators: `fCtl` -/

-- float values have float vregs; `return v0` returns the `f64` in v0 (not x0)
#guard (buildCtx fCtl).toBool
#guard (ctxStOf fCtl).1.valueReg? 0 == some (.vreg 0 .float)
#guard (ctxStOf fCtl).1.valueReg? 1 == some (.vreg 1 .int)
#guard fCtl.blocks.any fun B => B.term == .ret [0]
#guard retRegsT ([0].map (valClassOf (ctxStOf fCtl).1)) 0 0 == [.v 0]

/-- **`fCtl`'s context is typed** … -/
theorem ctxT_fCtl : CtxT fCtl (ctxStOf fCtl).1 :=
  ctxT_of (by native_decide) (by native_decide) functionET_fCtl

/-- … **and not an integer one**. -/
theorem not_ctxInv_fCtl : ¬ CtxInv fCtl (ctxStOf fCtl).1 := not_ctxInv_of (x := 0) (by native_decide)

/-- **The typed terminator and branch families give the driver's terminator calls on `fCtl`'s
context** (class-aware returns, `LowerTermOkT`). -/
theorem termCallsT_fCtl : TermCallsT (ctxStOf fCtl).1 ispec (fun _ _ _ => True) :=
  termCallsT_of_rules lowerTermRulesCorrectT_program termUnmatchableT_program
    branchRulesCorrectT_program branchExcludedUnmatchableT_program refines_ispec mrStable_true
    ctxT_fCtl

/-! ## Calls: `fCall` -/

/-- An integer `call` and `call_indirect` between float values. -/
def fCall : Clif.Function := fnOfText
  "function %c(f64, i64) -> f64 {
    sig0 = (i64) -> i64
    fn0 = %g(i64) -> i64
block0(v0: f64, v1: i64):
    v2 = call fn0(v1)
    v3 = call_indirect sig0, v1(v2)
    v4 = bitcast.f64 v3
    v5 = select v1, v0, v4
    return v5
}
"

#guard Compile.functionET fCall && !Compile.functionE fCall
#guard (ctxStOf fCall).1.insts[0]?.bind (·.clif) matches some (Clif.Inst.call ..)
#guard (ctxStOf fCall).1.insts[1]?.bind (·.clif) matches some (Clif.Inst.callIndirect ..)
-- `lower` fires the GOT + `blr` root (1032, a non-colocated extern) and the `call_indirect` root
-- (1033) on them
#guard (lowerTrace fCall 0).contains 1032 && (lowerTrace fCall 1).contains 1033

theorem ctxT_fCall : CtxT fCall (ctxStOf fCall).1 :=
  ctxT_of (by native_decide) (by native_decide) (by native_decide)

theorem not_ctxInv_fCall : ¬ CtxInv fCall (ctxStOf fCall).1 :=
  not_ctxInv_of (x := 0) (by native_decide)

/-- **The call families' roots apply to `fCall`'s context**: its `call` (instruction 0) and
`call_indirect` (instruction 1) are subset-E instructions of a typed context, and rules 1032
(`rule_lower_2518`) and 1033 (`rule_lower_2529`) are call/indirect-call roots of `lower`, so
`callRulesCorrectTP_program`/`indRulesCorrectTP_program` give `CallRuleOkTP`/`IndRuleOkTP` on
them. -/
theorem call_roots_apply :
    CtxT fCall (ctxStOf fCall).1 ∧
      (∃ fn args, (ctxStOf fCall).1.insts[0]?.bind (·.clif) = some (.call fn args) ∧
        Compile.instE (.call fn args) = true) ∧
      (∃ sig c args, (ctxStOf fCall).1.insts[1]?.bind (·.clif) = some (.callIndirect sig c args) ∧
        Compile.instE (.callIndirect sig c args) = true) ∧
      rule_lower_2518 ∈ program.rulesOf TId.lower ∧ callRootRule rule_lower_2518 = true ∧
      rule_lower_2529 ∈ program.rulesOf TId.lower ∧ indRootRule rule_lower_2529 = true := by
  refine ⟨ctxT_fCall, ?_, ?_, mem_lower_2518, rfl, mem_lower_2529, rfl⟩
  · have h : (match (ctxStOf fCall).1.insts[0]?.bind (·.clif) with
        | some (.call _ _) => true
        | _ => false) = true := by native_decide
    split at h
    · rename_i fn args he
      exact ⟨fn, args, he, by
        have : ((ctxStOf fCall).1.insts[0]?.bind (·.clif)).all Compile.instE = true := by
          native_decide
        rw [he] at this; exact this⟩
    · cases h
  · have h : (match (ctxStOf fCall).1.insts[1]?.bind (·.clif) with
        | some (.callIndirect _ _ _) => true
        | _ => false) = true := by native_decide
    split at h
    · rename_i sig c args he
      exact ⟨sig, c, args, he, by
        have : ((ctxStOf fCall).1.insts[1]?.bind (·.clif)).all Compile.instE = true := by
          native_decide
        rw [he] at this; exact this⟩
    · cases h

/-! ## `try_call`: `fTry` -/

/-- An integer `try_call` in a function with a float parameter and return. -/
def fTry : Clif.Function := fnOfText
  "function %t(f64, i64) -> f64 tail {\n  sig0 = (i64) -> i64 tail\n  fn0 = %g(i64) -> i64 tail\n\nblock0(v0: f64, v1: i64):\n  try_call fn0(v1), sig0, block1(ret0), [ default: block2(exn0) ]\n\nblock1(v2: i64):\n  return v0\n\nblock2(v3: i64):\n  return v0\n}\n"

#guard Compile.functionET fTry && !Compile.functionE fTry && Compile.tryArgClassOk fTry
#guard fTry.blocks.any fun B => B.term matches .tryCall ..

theorem ctxT_fTry : CtxT fTry (ctxStOf fTry).1 :=
  ctxT_of (by native_decide) (by native_decide) (by native_decide)

theorem not_ctxInv_fTry : ¬ CtxInv fTry (ctxStOf fTry).1 :=
  not_ctxInv_of (x := 0) (by native_decide)

/-- **The `try_call` family's premises hold on `fTry`**: a typed context, the `try_call`'s
arguments in integer positions (`TermIntPos`), and rules 1034/1035 the `try_call` roots of
`lower_branch` (`tryRulesCorrectTP_program`; the other rules, `tryUnmatchableT_program`). -/
theorem try_root_applies :
    CtxT fTry (ctxStOf fTry).1 ∧
      (∃ B ∈ fTry.blocks, ∃ fn args et, B.term = .tryCall fn args et ∧
        TermIntPos (ctxStOf fTry).1 (.tryCall fn args et)) ∧
      rule_lower_2542 ∈ program.rulesOf TId.lower_branch ∧ tryRootRule rule_lower_2542 = true ∧
      rule_lower_2551 ∈ program.rulesOf TId.lower_branch ∧ tryRootRule rule_lower_2551 = true := by
  refine ⟨ctxT_fTry, ?_, mem_lower_branch_2542, rfl, mem_lower_branch_2551, rfl⟩
  obtain ⟨r, hb⟩ : ∃ r, buildCtx fTry = .ok ((ctxStOf fTry).1, r, (ctxStOf fTry).2) := by
    have hok : (buildCtx fTry).toBool = true := by native_decide
    unfold ctxStOf
    cases h : buildCtx fTry with
    | error e => rw [h] at hok; cases hok
    | ok q => obtain ⟨c, r, s⟩ := q; exact ⟨r, rfl⟩
  have hB : fTry.blocks[0]? = some fTry.blocks[0]! := by native_decide
  have hmem := List.mem_of_getElem? hB
  have ht : (fTry.blocks[0]!.term matches .tryCall ..) = true := by native_decide
  have hip := termIntPos_of_functionET (by native_decide) hb hmem
  generalize hterm : fTry.blocks[0]!.term = t at ht hip
  cases t with
  | tryCall fn args et => exact ⟨_, hmem, fn, args, et, hterm, hip⟩
  | _ => cases ht

end FloatCtlRulesT
