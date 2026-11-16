import FV.Backend.Proof.IselCovTFamCover
import FV.Backend.Proof.IselCtlCallF
import FV.Backend.Proof.StockCountSelected
import FV.Backend.Proof.StockRotateRegisterRequests
import FV.Backend.Proof.StockRotateSelectedValues
import FV.Backend.Proof.StockSelectParameterRootValues
import FV.Backend.Proof.StockSelectScalarDriverRuns

/-!
# Falsity witnesses for statements restated for `f16` (#35, layer 1)

`Clif.Ty.f16` is a float type (`isInt = false`, float register class) of width 16. Each statement
below held before the constructor existed and is false with it; it was restated under its name
(`ty ≠ .f16`, `isArithFloat`, or `∨ v.ty = .f16` in a conclusion). The other restated statements
carry their witness next to them (`*_old_false` in FV).

The `Stock` witnesses run the exported ISLE program (`Isle.Aarch64.program`) under stock's
lowering semantics on a context whose value `v0` is an `f16` in a float-class register:
`put_in_reg_zext32` accepts it (`fits_in_32`), so the narrow `clz`/`rotl`/`rotr` right-hand sides
succeed, and the old conclusion `ctx.valueType? x = some (.int w)` is false.
-/

open Backend Backend.Proof Backend.Proof.CovT Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open Backend.Stock Backend.Stock.Proof Backend.Stock.Proof.ScalarCount

set_option maxRecDepth 20000

namespace F16OldFalse

/-- A context of two values: `v0 : f16` (a float-class register), `v1 : i16`; no instructions. -/
def ctx16 : Ctx :=
  { func := default, insts := #[], valTy := #[some (.float 16), some (.int 16)],
    valDef := #[none, none], valReg := #[some (.vreg 0 .float), some (.vreg 1 .int)],
    slotOff := [] }

def val16 : Clif.Val := ⟨.f16, 0⟩

/-- A frame where `v0 = 0 : f16` and `v1 = 0 : i16`. -/
def frame16 : Clif.Frame :=
  { func := default, regs := fun x => if x = 0 then some val16 else if x = 1 then
      some ⟨.i16, 0⟩ else none, slots := [], body := [], term := default }

theorem frameTyped16 : FrameTyped ctx16 frame16 := by
  intro x t v ht hv
  rcases x with _ | _ | n
  · cases hv; cases ht; rfl
  · cases hv; cases ht; rfl
  · first | cases hv | simp [frame16, show n + 1 + 1 ≠ 0 by omega, show n + 1 + 1 ≠ 1 by omega] at hv

theorem dfgCons16 : DFGCons ctx16 frame16 := by
  refine ⟨fun x j info cl v hd => ?_, frameTyped16⟩
  exfalso
  rcases x with _ | _ | n <;> first | cases hd | simp [ctx16, Ctx.defInst?] at hd

theorem valueType16 : ctx16.valueType? 0 = some (.float 16) := rfl

theorem valClass16 : valClassOf ctx16 0 = .float := rfl

/-! ## `IselCovTFamCover.resF1`, `IselCtlCallF.float_of_valClassOf`, `argClasses_of_frame` -/

/-- `resF1` before `f16` (`h : ty.isFloat = true`) is false: `ty = f16`, a result of type
`.float 16`, and a family whose result types are `fCTys`. -/
theorem resF1_old_false :
    ¬ ∀ (info : IInfo) (ty : Clif.Ty), info.resTys = [CTy.ofClif ty] → ty.isFloat = true →
      ∀ (F : Fam), fCTys ⊆ F.res → fCTys ⊆ F.all →
        (∀ t ∈ info.resTys, t ∈ F.res ∧ t ∈ F.all) ∧
          info.resTys.head?.getD .invalid ∈ F.res := by
  intro h
  have := (h { data := default, results := [], resTys := [.float 16], clif := none } .f16 rfl rfl
    { res := fCTys, all := fCTys, data := default } (fun _ ht => ht) (fun _ ht => ht)).2
  simp [fCTys] at this

/-- `float_of_valClassOf` before `f16` (conclusion `v.ty = .f32 ∨ v.ty = .f64`) is false: an
`f16` frame value at a value of type `.float 16`. -/
theorem float_of_valClassOf_old_false :
    ¬ ∀ (ctx : Ctx) (fr : Clif.Frame), FrameTyped ctx fr → ∀ (x : Nat) (v : Clif.Val),
      fr.regs x = some v → valClassOf ctx x = .float → v.ty = .f32 ∨ v.ty = .f64 := by
  intro h
  rcases h ctx16 frame16 frameTyped16 0 val16 rfl valClass16 with h | h <;>
    exact absurd h (by decide)

/-- `argClasses_of_frame` before `f16` is false: the call argument `v0 : f16`. -/
theorem argClasses_of_frame_old_false :
    ¬ ∀ (ctx : Ctx) (fr : Clif.Frame), DFGCons ctx fr → ∀ (args : List Nat) (vals : List Clif.Val),
      fr.getMany args = .ok vals →
      ∀ (j : Nat) (v : Clif.Val) (x : Nat), vals[j]? = some v → args[j]? = some x →
        valClassOf ctx x = .float → v.ty = .f32 ∨ v.ty = .f64 := by
  intro h
  rcases h ctx16 frame16 dfgCons16 [0] [val16] rfl 0 val16 0 rfl rfl valClass16 with h | h <;>
    exact absurd h (by decide)

/-! ## The three `Stock` request lemmas -/

/-- An initial stock state for `ctx16`: two value vregs, no instructions. -/
def st16 : State :=
  { base := { nextVreg := 2, classes := #[.float, .int] }, demand := #[0, 0], uses := #[],
    instBlock := #[], entryColor := #[], endColor := #[], tryRegs := #[], sunk := #[],
    opportunistic := #[] }

/-- The run of a stock right-hand side succeeds (checked by evaluation). -/
theorem ok_of_check {r : Except Err (Option V × State × Array RuleId)}
    (h : (match r with | .ok (some _, _, _) => true | _ => false) = true) :
    ∃ out next trace, r = .ok (some out, next, trace) := by
  revert h
  rcases r with _ | ⟨_ | out, next, trace⟩ <;> simp

/-- Narrow `clz.i16` (`countRule false 16`) of the `f16` value `v0` runs (checked by evaluation). -/
theorem runClz_ok : ∃ out next trace,
    (evalExpr program (Stock.sem ctx16) {} (0+80) (countRule false 16).rhs (countEnv 16 0)).run
      (st16, #[]) = .ok (some out, next, trace) :=
  ok_of_check (by native_decide)

/-- `StockCountSelected.root_requests` (private) before `f16` (without `h16 : ty ≠ .f16`) is
false: `clz` at width 16 of the `f16` value `v0` runs, and `v0` is not of type `.int 16`. -/
theorem root_requests_old_false :
    ¬ ∀ (ctx : Ctx) (trailing : Bool) (w x n : Nat), IW w → ∀ (fr : Clif.Frame),
      DFGCons ctx fr → ∀ (ty : Clif.Ty), ty.width = w → ∀ (u : BitVec ty.width),
      fr.getAs x ty = .ok u → ∀ (st next : State) (out : V) (trace : Array RuleId),
      (evalExpr program (Stock.sem ctx) {} (n+80) (countRule trailing w).rhs
        (countEnv w x)).run (st,#[]) = .ok (some out,next,trace) →
      DemandAllowed ctx st x ∧ (∃ rx,ctx.valueReg? x = some rx) ∧
        (¬ trailing → w = 8 ∨ w = 16 → ctx.valueType? x = some (.int w)) := by
  intro h
  obtain ⟨out, next, trace, hrun⟩ := runClz_ok
  have := (h ctx16 false 16 0 0 (.inr (.inl rfl)) frame16 dfgCons16 .f16 rfl 0 rfl st16 next out
    trace hrun).2.2 (by decide) (.inr rfl)
  rw [valueType16] at this
  simp at this

/-- Narrow `rotl.i16` by a register (`rotateNarrowRule true false`) of the `f16` value `v0`
by `v1` runs (checked by evaluation). -/
theorem runRotlReg_ok : ∃ out next trace,
    (evalExpr program (Stock.sem ctx16) {} (0+160) (ScalarRotate.rotateNarrowRule true false).rhs
      (ScalarRotate.rotateNarrowEnv true 16 0 1)).run (st16, #[]) = .ok (some out, next, trace) :=
  ok_of_check (by native_decide)

/-- `stock_rotate_narrow_register_requests` before `f16` (without `h16 : ty ≠ .f16`) is false:
`rotl` at width 16 of the `f16` value `v0` runs. -/
theorem stock_rotate_narrow_register_requests_old_false :
    ¬ ∀ (p : Program), Data p → ∀ (ctx : Ctx) (left : Bool) (w x y n : Nat), (w = 8 ∨ w = 16) →
      ∀ (fr : Clif.Frame), DFGCons ctx fr → ∀ (ty : Clif.Ty), ty.width = w →
      ∀ (u : BitVec ty.width), fr.getAs x ty = .ok u →
      ∀ (st next : State) (tr trace : Array RuleId) (out : V),
      (evalExpr p (Stock.sem ctx) {} (n+160) (ScalarRotate.rotateNarrowRule left false).rhs
        (ScalarRotate.rotateNarrowEnv left w x y)).run (st,tr) = .ok (some out,next,trace) →
      ctx.valueType? x = some (.int w) ∧ DemandAllowed ctx st x ∧ DemandAllowed ctx st y ∧
        (∃ rx,ctx.valueReg? x = some rx) ∧ ∃ ry,ctx.valueReg? y = some ry := by
  intro h
  obtain ⟨out, next, trace, hrun⟩ := runRotlReg_ok
  have := (h program data_program ctx16 true 16 0 1 0 (.inr rfl) frame16 dfgCons16 .f16 rfl 0 rfl
    st16 next #[] trace out hrun).1
  rw [valueType16] at this
  simp at this

/-- Narrow `rotl.i16` by the immediate 3 (`rotateNarrowRule true true`) of the `f16` value `v0`
runs (checked by evaluation). -/
theorem runRotlImm_ok : ∃ out next trace,
    (evalExpr program (Stock.sem ctx16) {} (0+140) (ScalarRotate.rotateNarrowRule true true).rhs
      (env4 (.ty (.int 16)) (.value 0) (.int 3) (.op (.immShift 3)))).run (st16, #[]) =
        .ok (some out, next, trace) :=
  ok_of_check (by native_decide)

/-- `stock_rotate_narrow_immediate_requests` before `f16` (without `h16 : ty ≠ .f16`) is false:
`rotl` at width 16 by an immediate of the `f16` value `v0` runs. -/
theorem stock_rotate_narrow_immediate_requests_old_false :
    ¬ ∀ (p : Program), Data p → ∀ (ctx : Ctx) (left : Bool) (w x amount n : Nat),
      (w = 8 ∨ w = 16) → ∀ (constant : Int) (fr : Clif.Frame), DFGCons ctx fr →
      ∀ (ty : Clif.Ty), ty.width = w → ∀ (u : BitVec ty.width), fr.getAs x ty = .ok u →
      ∀ (st next : State) (tr trace : Array RuleId) (out : V),
      (evalExpr p (Stock.sem ctx) {} (n+140) (ScalarRotate.rotateNarrowRule left true).rhs
        (env4 (.ty (.int w)) (.value x) (.int constant) (.op (.immShift amount)))).run (st,tr) =
          .ok (some out,next,trace) →
      ctx.valueType? x = some (.int w) ∧ DemandAllowed ctx st x ∧
        ∃ rx,ctx.valueReg? x = some rx := by
  intro h
  obtain ⟨out, next, trace, hrun⟩ := runRotlImm_ok
  have := (h program data_program ctx16 true 16 0 3 0 (.inr rfl) 3 frame16 dfgCons16 .f16 rfl 0
    rfl st16 next #[] trace out hrun).1
  rw [valueType16] at this
  simp at this

/-! ## The select allocation lemmas

`ScalarSelect.stock_select_nonzero_actual_allocation` and
`ScalarSelect.stock_original_select_parameter_selected_allocation` depend on the condition type
`cty` only through `cty.width` in their premises, and conclude
`next.base.nextVreg = st.base.nextVreg + (if cty = .i16 then 2 else 1)`. At `cty = f16` their
premises are those at `cty = i16`, which an actual selection of `select.i16 v7, v31, v63` (`v7 : i16`
a parameter) satisfies; the restated theorems (premise `cty ≠ .f16`) at `i16` give `+ 2`, the old
text at `f16` would give `+ 1`. -/

/-- The stock lowering context of `scalarSelectFunction .i16 .i16`. -/
def selBuilt : Ctx × Array (Nat × Nat) × State := ScalarSelect.scalarSelectBuilt .i16 .i16

theorem selScope : LowerScope (ScalarSelect.scalarSelectFunction .i16 .i16) :=
  Driver.lowerScope_of (by rfl)

theorem selBuiltRun : Stock.buildCtx (ScalarSelect.scalarSelectFunction .i16 .i16) = .ok selBuilt :=
  rfl

theorem selInv : MappedCtxInv (ScalarSelect.scalarSelectFunction .i16 .i16) selBuilt.1 :=
  buildCtx_mappedInv selScope selBuiltRun

theorem selSource : selBuilt.1.insts[0]? = some selBuilt.1.insts[0]! := rfl

theorem selClif : selBuilt.1.insts[0]!.clif = some (.select .i16 7 31 63) := rfl

theorem selTyped : selBuilt.1.valueType? 7 = some (.int 16) := rfl

theorem selParameter : selBuilt.1.defInst? 7 = none := rfl

theorem selObserved :
    (Stock.runTerm selBuilt.1 "lower" [.inst 0] selBuilt.2.2).toOption.map
      (fun q => q.1.isSome) = some true := by
  native_decide

/-- The actual stock selection of the `select` (instruction 0). -/
theorem selSelection : ∃ out next trace,
    Nonempty (LowerSelection selBuilt.1 0 selBuilt.2.2 out next trace) := by
  have success := selObserved
  cases run : Stock.runTerm selBuilt.1 "lower" [.inst 0] selBuilt.2.2 with
  | error err => simp [run, Except.toOption] at success
  | ok q =>
    obtain ⟨out, next, trace⟩ := q
    cases out with
    | none => simp [run, Except.toOption] at success
    | some out => exact ⟨out, next, trace, stock_named_lower_selection run⟩

/-- `stock_original_select_parameter_selected_allocation` before `f16` (without
`h16 : cty ≠ .f16`) is false. -/
theorem stock_original_select_parameter_selected_allocation_old_false :
    ¬ ∀ {f : Clif.Function} {ctx : Ctx}
      (inv : MappedCtxInv f ctx) {cty ty : Clif.Ty}
      (conditionWidth : cty.width = 8 ∨ cty.width = 16 ∨ cty.width = 32 ∨ cty.width = 64)
      {i c x y : Nat} {info : IInfo} (source : ctx.insts[i]? = some info)
      (clif : info.clif = some (.select ty c x y))
      (typed : ctx.valueType? c = some (.int cty.width)) (parameter : ctx.defInst? c = none)
      {st next : State} {out : V} {rules : List RuleId}
      (selected : LowerSelection ctx i st out next rules),
      ∃ d,out = .regsVec [[.vreg d .int]] ∧ st.base.nextVreg ≤ d ∧ d < next.base.nextVreg ∧
        next.base.nextVreg = st.base.nextVreg+(if cty = .i16 then 2 else 1) := by
  intro h
  obtain ⟨out, next, trace, ⟨selected⟩⟩ := selSelection
  obtain ⟨_, -, -, -, old⟩ := h selInv (cty := .f16) (.inr (.inl rfl)) selSource selClif selTyped
    selParameter selected
  obtain ⟨_, -, -, -, new⟩ := ScalarSelect.stock_original_select_parameter_selected_allocation
    selInv (cty := .i16) (.inr (.inl rfl)) (by decide) selSource selClif selTyped selParameter
    selected
  rw [if_neg (by decide)] at old
  rw [if_pos rfl] at new
  omega

/-- `stock_select_nonzero_actual_allocation` before `f16` (without `h16 : cty ≠ .f16`) is
false. -/
theorem stock_select_nonzero_actual_allocation_old_false :
    ¬ ∀ {f : Clif.Function} {ctx : Ctx}
      (inv : MappedCtxInv f ctx) {cty ty : Clif.Ty}
      (conditionWidth : cty.width = 8 ∨ cty.width = 16 ∨ cty.width = 32 ∨ cty.width = 64)
      (width : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64)
      {c x y emitFuel selectFuel : Nat} (typed : ctx.valueType? c = some (.int cty.width))
      (enoughEmit : 220 ≤ emitFuel) (enoughSelect : 319 ≤ selectFuel)
      {st middle next : State} {tr emitterTrace trace : Array RuleId} {condition out : V}
      (emitter : ApplyInternal program (Stock.sem ctx) {} emitFuel 123 651 [.value c]
        (st,tr) condition (middle,emitterTrace))
      {consumerStart : Array RuleId}
      (consumer : ApplyInternal program (Stock.sem ctx) {} selectFuel 22 659
        [.ty (.int ty.width),condition,.value x,.value y] (middle,consumerStart) out (next,trace)),
      out = .regs [.vreg middle.base.nextVreg .int] ∧ st.base.nextVreg ≤ middle.base.nextVreg ∧
        next.base.nextVreg = st.base.nextVreg+(if cty = .i16 then 2 else 1) ∧
        next.base.nextVreg = middle.base.nextVreg+1 := by
  intro h
  obtain ⟨out, next, trace, ⟨selected⟩⟩ := selSelection
  obtain ⟨_,_,_,_,emitFuel,selectFuel,condition,middle,emitTrace,value,produced,selectTrace,
    enoughEmit,enoughSelect,emitter,consumer,-⟩ :=
    ScalarSelect.stock_original_select_selected_calls selInv selSource selClif selected
  obtain ⟨helperFuel,helperTrace,enough,nonzero⟩ :=
    ScalarSelect.stock_original_select_parameter_condition_calls selInv enoughEmit selParameter emitter
  have width := (ScalarSelect.stock_original_select_source_data selInv selSource selClif).1
  have old := (h selInv (cty := .f16) (.inr (.inl rfl)) width selTyped (by omega) enoughSelect
    nonzero consumer).2.2.1
  have new := (ScalarSelect.stock_select_nonzero_actual_allocation selInv (cty := .i16)
    (.inr (.inl rfl)) (by decide) width selTyped (by omega) enoughSelect nonzero consumer).2.2.1
  rw [if_neg (by decide)] at old
  rw [if_pos rfl] at new
  omega

end F16OldFalse
