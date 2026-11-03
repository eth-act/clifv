import FV.Backend.Proof.StockScanProgress
import FV.Backend.Proof.StockScalarNames
import FV.Backend.Proof.StockScalarCompleteBlock

/-!
# Stock lowering succeeds on the scalar route

For every function that the scalar classifier accepts and that meets the baseline input conditions
of the lowering (`functionE`, `dominatedB`, `lowerScopeB`, `extendsWidenB`, `iselInB`, `driverInB`),
`Stock.lower` succeeds. The proof composes the phases: the shape and the context build (P1), the
reduction of `Stock.lower` to the core lowering of the one `return` block (P2), and that core
lowering itself (P3/P4: `lowerBlockCore_ret_ok`, with the classifier's statement names). The ABI
read check of the resulting code (P5) is a separate obligation.
-/

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.ScanProgress
  Backend.Stock.Proof.LowerProjection
set_option autoImplicit false

/-- **`Stock.lower` succeeds on the scalar route.** -/
theorem stock_lower_scalar_ok {f : Clif.Function} (eligible : Scalar.productionEligible f = true)
    (hE : Compile.functionE f = true) (hdom : dominatedB f = true) (hs : lowerScopeB f = true)
    (hw : extendsWidenB f = true) (hin : Prg.iselInB f = true) (hdrv : driverInB f = true) :
    ∃ result, Stock.lower f = .ok result := by
  obtain ⟨b, xs, blocks, ret, hp, hr⟩ := productionEligible_shape eligible
  obtain ⟨⟨ctx, ranges, initial⟩, built⟩ := stock_buildCtx_ok hE hdom hdrv blocks ret
  obtain ⟨original, before, legacy, spec, view⟩ := buildCtx_source built
  have mapped := buildCtx_mappedInv (lowerScope_of hs) built
  have params : ∀ v ∈ b.params, (ctx.valueReg? v.1).isSome = true := by
    intro v hv
    have defined : v.1 ∈ valueDefs f := by
      simp only [valueDefs, blocks, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.mem_append, List.mem_map]
      exact .inl ⟨v, hv, rfl⟩
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (Prg.typed_of_def (ctxSpec_of legacy) defined)
    have typed : ctx.valueType? v.1 = some t := by
      show (ctx.valTy[v.1]?).join = some t
      rw [view.valTy]
      exact ht
    obtain ⟨n, hn⟩ := mapped.typedReg v.1 t typed
    rw [hn]
    rfl
  have block : f.blocks[0]? = some b := by rw [blocks]; rfl
  have rangeRun : ranges[0]? = some ranges[0]! := by
    have h := spec.ranges 0 b block
    rw [getElem!_def, h]
  have rets : sigRets f.sig = f.sig.returns := by
    have none : f.sig.params.find? (·.purpose == .sret) = none := by
      rw [List.find?_eq_none]
      intro q hm hsr
      have hn := List.all_eq_true.mp hp q hm
      simp only [Scalar.narrowAbiEligible, Bool.and_eq_true, beq_iff_eq] at hn hsr
      rw [hn.1] at hsr
      cases hsr
    simp only [sigRets, none]
  have noSretRet : sretRet f = [] := by
    simp only [sretRet, rets, bne_self_eq_false, Bool.false_eq_true, ite_false]
  obtain ⟨lowered, core⟩ := lowerBlockCore_ret_ok built hdom hs hw hin hdrv
    (productionEligible_names eligible) block ret rangeRun singleOrder (buildCtx_quiet built)
  rw [retData, noSretRet, List.append_nil] at core
  exact stock_lower_single_ret hdrv hp hr blocks ret built params core

private def lowerOkFixture : Clif.Function := {
  name := "stock_lower_scalar_ok"
  sig := { params := [⟨.i64,.none,.normal⟩,⟨.i64,.none,.normal⟩], returns := [⟨.i64,.none,.normal⟩] }
  blocks := [
    { id := 0, params := [(0, .i64), (1, .i64)],
      body := [⟨[2], .binary .imul .i64 0 1⟩, ⟨[3], .binary .iadd .i64 2 0⟩], term := .ret [3] }] }

private def lowerOkChecks : Bool :=
  Scalar.productionEligible lowerOkFixture && Compile.functionE lowerOkFixture &&
    dominatedB lowerOkFixture && lowerScopeB lowerOkFixture && extendsWidenB lowerOkFixture &&
    Prg.iselInB lowerOkFixture && driverInB lowerOkFixture

-- witness: native_decide (the fixed function's input-condition checks only)
private theorem lowerOkChecks_true : lowerOkChecks = true := by native_decide

/-- Non-vacuity: a real two-statement scalar function meets every premise, so `Stock.lower`
succeeds on it through `stock_lower_scalar_ok`. -/
theorem stock_lower_scalar_ok_witness : ∃ (f : Clif.Function) (result : Result),
    Scalar.productionEligible f = true ∧ Stock.lower f = .ok result := by
  have h := lowerOkChecks_true
  unfold lowerOkChecks at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨eligible, hE⟩, hdom⟩, hs⟩, hw⟩, hin⟩, hdrv⟩ := h
  obtain ⟨result, run⟩ := stock_lower_scalar_ok eligible hE hdom hs hw hin hdrv
  exact ⟨lowerOkFixture, result, eligible, run⟩

end Backend.Stock.Proof
