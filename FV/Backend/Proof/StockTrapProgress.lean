import FV.Backend.Proof.StockScanProgress
import FV.Backend.Proof.StockScalarNames
import FV.Backend.Proof.StockScalarCompleteBlock
import FV.Backend.Proof.StockControlShape

/-!
# Stock lowering succeeds on scalar blocks that end in `trap`

The trap root of `lower` (rule 964, `udf`) is not one of the diverging rules, so the baseline
progress analysis gives a baseline `lower` run of a `trap` slot on the Stock terminator context
(`stock_trap_backend`), and the guarded projection transports it to Stock
(`stock_runTerm_trap_ok`: the run emits `udf c` and keeps the scheduling fields). With the scan
lemmas of `StockScanProgress`, the core lowering of a scalar block that ends in `trap` succeeds
(`lowerBlockCore_trap_ok`), and so does `Stock.lower` on a one-block function of that shape
(`stock_lower_trap_ok`).
-/

namespace Backend.Stock.Proof.LowerProjection
open Backend Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64 Backend.Stock.Proof
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- The terminator data of `trap c`. -/
abbrev trapData (c : Clif.TrapCode) : V := instDataV "Trap" [opcodeV "Trap", .op (.trapCode c)]

theorem trapData_eq (c : Clif.TrapCode) :
    trapData c = .data 152 26 [.data 151 4 [], .op (.trapCode c)] := rfl

section Backend
open Backend.Proof.Prg

/-- **The baseline `lower` run of a `trap` on the Stock terminator context returns.** -/
theorem stock_trap_backend {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {st : State}
    (hb : Stock.buildCtx f = .ok (ctx,ranges,st)) (hdom : dominatedB f = true)
    (hs : lowerScopeB f = true) (hw : extendsWidenB f = true) (hin : iselInB f = true)
    {ti : Nat} (hph : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩) (c : Clif.TrapCode)
    (regs : List Reg × List Reg) (s : LState) :
    ∃ w s' tr, Backend.runTerm { termCtx ctx ti (trapData c) with tryRegs := regs } "lower"
      [.inst ti] s = .ok (some w, s', tr) := by
  have hP := stock_pinv_termCtx (stock_pinv hb hdom hs hw hin) hph (trapData c) regs
  have hself : ({ termCtx ctx ti (trapData c) with tryRegs := regs } : Ctx).insts[ti]? =
      some ⟨trapData c, [], [], none⟩ := termCtx_insts_self hph _
  have hinst : ∀ k fs, γ f { termCtx ctx ti (trapData c) with tryRegs := regs } (idat k fs)
      (trapData c) → γ f { termCtx ctx ti (trapData c) with tryRegs := regs } (termInst k fs)
        (.inst ti) :=
    fun k fs h => γ_inst hself (γ_ty_mem (by simp)) h (by simp)
  have hγ : γL f { termCtx ctx ti (trapData c) with tryRegs := regs }
      [termInst VIdx.InstructionData.Trap [opc VIdx.Opcode.Trap, .op .trapCode none]] [.inst ti] :=
    γL_cons' (hinst _ _ (γ_instDataV (by rfl) (γL_cons' (γ_opcodeV (by rfl))
      (γL_cons' (γ_op ⟨c, rfl⟩) γL_nil')))) γL_nil'
  have hq : (TId.lower, [termInst VIdx.InstructionData.Trap [opc VIdx.Opcode.Trap, .op .trapCode none]])
      ∈ termRoots := by
    dsimp only [termRoots]; iterate 2 apply List.mem_append_left
    apply List.mem_append_right
    exact List.mem_cons_self
  obtain ⟨e, he, hos, hfu⟩ := termRoot_entry hq
  obtain ⟨w, s', tr, hrun, -⟩ := root_run (model_of hP) (handOk hP rfl prgTab) prgTab_ok
    program_termByName_lower he hos hfu hγ s
  exact ⟨w, s', tr, hrun⟩

end Backend

set_option maxRecDepth 100000 in
/-- No diverging rule of `lower` has the `Trap` primary opcode. -/
theorem lower_trap_diverging : (program.rulesOf 686).all (fun r => !lowerDiverging.contains r.id ||
    (match sourceRuleOpcode program r with
      | some c => c != 4
      | none => false)) = true := by
  rw [data_program.r686]
  decide +kernel

/-- The diverging rules of `lower` cannot match a `trap` slot. -/
theorem trap_diverging_args_fail (ctx : Ctx) {ti : Nat} {c : Clif.TrapCode}
    (slot : ctx.insts[ti]? = some ⟨.data 152 26 [.data 151 4 [], .op (.trapCode c)], [], [], none⟩) :
    ∀ r ∈ program.rulesOf 686, r.id ∈ lowerDiverging →
      ArgsFail program (Backend.sem ctx) r [.inst ti] := by
  intro r hr hdiv
  have h := List.all_eq_true.mp lower_trap_diverging r hr
  simp only [List.contains_iff_mem.mpr hdiv, Bool.not_true, Bool.false_or] at h
  cases hc : sourceRuleOpcode program r with
  | none => rw [hc] at h; cases h
  | some code =>
    rw [hc] at h
    have ne : code ≠ 4 := by simpa using h
    exact argsFail_of_opcode hc slot rfl (Ne.symm ne)

/-- **Stock `lower` progress on a `trap`.** From a state with nothing sunk, Stock's `lower` run
of a `trap c` slot returns no registers and emits `udf c`. -/
theorem stock_runTerm_trap_ok (ctx : Ctx) {ti : Nat} {c : Clif.TrapCode}
    (slot : ctx.insts[ti]? = some ⟨.data 152 26 [.data 151 4 [], .op (.trapCode c)], [], [], none⟩)
    {st : State} (hst : NoSunk st)
    (hb : ∃ w s' tr, Backend.runTerm ctx "lower" [.inst ti] st.base = .ok (some w, s', tr)) :
    ∃ tr, Stock.runTerm ctx "lower" [.inst ti] st =
      .ok (some (.regsVec []), { st with base := st.base.emit (.udf c) }, tr) := by
  obtain ⟨w, s', tr, hb⟩ := hb
  obtain ⟨st', run, -, -⟩ := stock_runTerm_lower_of_backend ctx hst (trap_diverging_args_fail ctx slot) hb
  obtain ⟨hnext, hout, -⟩ := Control.stock_named_trap_shape slot run
  subst hnext hout
  exact ⟨tr, run⟩

end Backend.Stock.Proof.LowerProjection

namespace Backend.Stock.Proof.ScanProgress
open Backend Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64 Backend.Stock.Proof
  Backend.Stock.Proof.Coverage Backend.Stock.Proof.LowerProjection
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

private theorem getElem!_of_some {ctx : Ctx} {i : Nat} {info : IInfo}
    (source : ctx.insts[i]? = some info) : ctx.insts[i]! = info := by
  rw [getElem!_def, source]

/-- **Emission of a `trap` succeeds from a quiet state and keeps it quiet.** -/
theorem emit_trap_ok {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {st0 : State}
    (hb : Stock.buildCtx f = .ok (ctx, ranges, st0)) (hdom : dominatedB f = true)
    (hs : lowerScopeB f = true) (hw : extendsWidenB f = true) (hin : Prg.iselInB f = true)
    {ti : Nat} (hph : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩) (c : Clif.TrapCode)
    (regs : List Reg × List Reg) {before : State} (quiet : Quiet before) :
    ∃ e, emitInstruction { termCtx ctx ti (trapData c) with tryRegs := regs } ti before = .ok e ∧
      Quiet e.state := by
  have slot : ({ termCtx ctx ti (trapData c) with tryRegs := regs } : Ctx).insts[ti]? =
      some ⟨.data 152 26 [.data 151 4 [], .op (.trapCode c)], [], [], none⟩ := by
    rw [← trapData_eq]
    exact termCtx_insts_self hph _
  obtain ⟨w, s', tr, hback⟩ := stock_trap_backend hb hdom hs hw hin hph c regs before.base
  obtain ⟨trace, hrun⟩ := stock_runTerm_trap_ok _ slot quiet.unsunk ⟨w, s', tr, hback⟩
  refine ⟨⟨{ before with base := before.base.emit (.udf c) },
    (before.base.emit (.udf c)).emitted ++ #[], [], trace⟩, ?_, ?_⟩
  · unfold emitInstruction
    rw [getElem!_of_some slot]
    simp only [hrun, bind, Except.bind, List.isEmpty_nil, Bool.not_true, Bool.and_false,
      Bool.false_eq_true, ↓reduceIte, List.zip_nil_left]
    rfl
  · exact ⟨fun j => quiet.unsunk j, fun v => quiet.empty v⟩

private theorem placeholder {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial))
    {bi : Nat} {b : Clif.Block} (block : f.blocks[bi]? = some b) :
    ctx.insts[blockStart f bi + b.body.length]? = some ⟨.op .unit, [], [], none⟩ := by
  obtain ⟨original, before, legacy, spec, view⟩ := buildCtx_source build
  rw [view.insts]
  exact spec.facts.term bi b block

private theorem clean_stock {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial)) : Cov.Clean (sourceIdentityCtx ctx) := by
  obtain ⟨original, before, legacy, spec, view⟩ := buildCtx_source build
  intro i info lookup
  change ctx.insts[i]? = some info at lookup
  rw [view.insts] at lookup
  exact Cov.clean_of_build legacy i info lookup

/-- **The core lowering of a scalar block that ends in `trap` succeeds from a quiet state.** -/
theorem lowerBlockCore_trap_ok {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)}
    {st0 : State} (hb : Stock.buildCtx f = .ok (ctx, ranges, st0)) (hdom : dominatedB f = true)
    (hs : lowerScopeB f = true) (hw : extendsWidenB f = true) (hin : Prg.iselInB f = true)
    (scalar : ∀ cl, Prg.InstOf f cl → ScalarNames cl)
    {bi : Nat} {b : Clif.Block} (block : f.blocks[bi]? = some b) {c : Clif.TrapCode}
    (htrap : b.term = .trap c) {range : Nat × Nat} (rangeRun : ranges[bi]? = some range)
    (order : Order) {input : State} (quiet : Quiet input) :
    ∃ lowered, lowerBlockCore ctx order f b bi range.1 range.2 (trapData c) #[] input =
      .ok lowered := by
  obtain ⟨original, before, legacy, spec, view⟩ := buildCtx_source hb
  have rangeEq := spec.ranges bi b block
  rw [rangeRun] at rangeEq
  have endEq : range.2 - 1 = blockStart f bi + b.body.length := by cases rangeEq; omega
  have ph : ctx.insts[range.2 - 1]? = some ⟨.op .unit, [], [], none⟩ := by
    rw [endEq]; exact placeholder hb block
  have clean : Cov.Clean (sourceIdentityCtx { termCtx ctx (range.2 - 1) (trapData c) with
      tryRegs := input.tryRegs[range.2 - 1]! }) :=
    Cov.clean_termCtx (clean_stock hb) (t := .trap c) rfl (range.2 - 1)
  have steps : ∀ i ∈ (((Array.range (range.2 - range.1)).map (range.1 + ·)).reverse.toList),
      ∀ before, Quiet before → ∃ e, emitInstruction { termCtx ctx (range.2 - 1) (trapData c) with
        tryRegs := input.tryRegs[range.2 - 1]! } i before = .ok e ∧ Quiet e.state := by
    intro i member before q
    by_cases terminal : i = range.2 - 1
    · subst terminal
      exact emit_trap_ok hb hdom hs hw hin ph c _ q
    · obtain ⟨lo, hi⟩ := stock_backward_indices_mem member
      cases rangeEq
      have index : i - blockStart f bi < b.body.length := by simp only at lo hi terminal; omega
      cases statement : b.body[i - blockStart f bi]? with
      | none => have outside := List.getElem?_eq_none_iff.mp statement; omega
      | some stm =>
        obtain ⟨info, lookup, clif, -⟩ := spec.facts.stmt bi b _ stm block statement
        have offset : blockStart f bi + (i - blockStart f bi) = i := by simp only at lo; omega
        rw [offset] at lookup
        have source : ({ termCtx ctx (blockStart f bi + b.body.length + 1 - 1) (trapData c) with
            tryRegs := input.tryRegs[blockStart f bi + b.body.length + 1 - 1]! } : Ctx).insts[i]? =
              some info := by
          change (Driver.termCtx ctx _ (trapData c)).insts[i]? = some info
          rw [termCtx_insts_ne terminal, view.insts]
          exact lookup
        exact emit_stmt_ok hb hdom hs hw hin scalar ph (trapData c) _ clean source clif q
  obtain ⟨out, hscan, -⟩ := scanBlock_ok (block := bi) (isBranch := false) _ steps
    (input := { input with color := some input.endColor[bi]! })
    ⟨fun j => quiet.unsunk j, fun v => quiet.empty v⟩
  have hscan' : scanBlock { ctx with insts := ctx.insts.set! (range.2 - 1) ⟨trapData c, [], [], none⟩, tryRegs := input.tryRegs[range.2 - 1]! }
      bi (range.2 - 1) false
      (((Array.range (range.2 - range.1)).map (range.1 + ·)).reverse.toList)
      { input with color := some input.endColor[bi]! } = .ok out := hscan
  cases hcore : lowerBlockCore ctx order f b bi range.1 range.2 (trapData c) #[] input with
  | ok lowered => exact ⟨lowered, rfl⟩
  | error e =>
    exfalso
    unfold lowerBlockCore at hcore
    have hout : collectOutgoing ctx order bi #[] input = .ok (input, #[]) := rfl
    simp only [htrap, pure, Except.pure, bind, Except.bind, ↓reduceIte, Bool.false_eq_true,
      Option.map_none, Option.getD_none, hout, hscan'] at hcore
    cases hcore

end Backend.Stock.Proof.ScanProgress

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.ScanProgress
  Backend.Stock.Proof.LowerProjection
set_option autoImplicit false

theorem blockOrder_single_trap {f : Clif.Function} {b : Clif.Block} {c : Clif.TrapCode}
    (blocks : f.blocks = [b]) (htrap : b.term = .trap c) : blockOrder f = .ok singleOrder := by
  obtain ⟨id,params,cold,body,term⟩ := b
  simp only at htrap
  subst htrap
  unfold blockOrder
  rw [blocks]
  cbv

theorem stock_buildCtx_ok_trap {f : Clif.Function} (hE : Compile.functionE f = true)
    (hdom : dominatedB f = true) (hdrv : driverInB f = true)
    {b : Clif.Block} {c : Clif.TrapCode} (blocks : f.blocks = [b]) (htrap : b.term = .trap c) :
    ∃ result, Stock.buildCtx f = .ok result := by
  have hssa : (valueDefs f).Nodup := by
    simp only [dominatedB,Bool.and_eq_true] at hdom; exact nodupB_sound hdom.1
  simp only [driverInB,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq] at hdrv
  obtain ⟨ctx,ranges,st0,hb⟩ := buildCtx_ok hE hssa fun B hB s hs => (hdrv.2 B hB).1 s hs
  rw [buildCtx_functionE_domain hE hb]
  simp only [allocationRequests,blocks,List.zipIdx_cons,List.zipIdx_nil,List.mapM_cons,
    List.mapM_nil,blockAllocationRequests,exceptionReservation,htrap,bind,Except.bind,pure,
    Except.pure]
  exact ⟨_,rfl⟩

theorem lowerNode_single_trap {ctx : Ctx} {ranges : Array (Nat × Nat)} {f : Clif.Function}
    {bytes : List Nat} {input : DriverState} {b : Clif.Block} {c : Clif.TrapCode}
    (blocks : f.blocks = [b]) (htrap : b.term = .trap c)
    (hargs : ∃ locs n, sigArgLocs f.sig = .ok (locs,n))
    (params : ∀ v ∈ b.params, (ctx.valueReg? v.1).isSome = true)
    {lowered : LoweredBlockCore}
    (core : lowerBlockCore ctx singleOrder f b 0 ranges[0]!.1 ranges[0]!.2
      (trapData c) #[] input.state = .ok lowered) :
    ∃ d, lowerNode ctx ranges singleOrder f bytes 0 input = .ok d := by
  have h1 : (#[Node.original 0] : Array Node)[0]! = .original 0 := rfl
  have h2 : ([b] : List Clif.Block)[0]! = b := rfl
  have h3 : (#[#[]] : Array (Array Nat))[0]! = #[] := rfl
  obtain ⟨vb,hvb⟩ := assembleOriginalBlock_entry_ok (ctx := ctx) (b := b) (label := 0)
    (outgoing := lowered.outgoing) (bytes := bytes) (uses := lowered.state.uses) (code := lowered.code)
    hargs params
  simp only [singleOrder] at core
  unfold lowerNode
  simp only [singleOrder,blocks,h1,h2,h3,htrap,termData,abiTerm,Bool.false_and,Bool.false_eq_true,
    ite_false,bind,Except.bind,pure,Except.pure,core,hvb]
  exact ⟨_,rfl⟩

/-- On one block that ends in `trap`, `Stock.lower` succeeds when the block's core lowering
succeeds from the initial state. -/
theorem stock_lower_single_trap {f : Clif.Function} (hdrv : driverInB f = true)
    (hp : f.sig.params.all Scalar.narrowAbiEligible = true)
    (hr : f.sig.returns.all Scalar.narrowAbiEligible = true)
    {b : Clif.Block} {c : Clif.TrapCode} (blocks : f.blocks = [b]) (htrap : b.term = .trap c)
    {ctx : Ctx} {ranges : Array (Nat × Nat)} {initial : State}
    (built : Stock.buildCtx f = .ok (ctx, ranges, initial))
    (params : ∀ v ∈ b.params, (ctx.valueReg? v.1).isSome = true)
    {lowered : LoweredBlockCore}
    (core : lowerBlockCore ctx singleOrder f b 0 ranges[0]!.1 ranges[0]!.2
      (trapData c) #[] initial = .ok lowered) :
    ∃ result, Stock.lower f = .ok result := by
  obtain ⟨conv,⟨bytes,hbytes⟩,wide,sret,eight⟩ := stock_prechecks hdrv hp hr
  unfold Stock.lower
  simp only [conv,Bool.not_true,Bool.false_eq_true,ite_false,hbytes,wide,sret,Bool.false_and,
    blockOrder_single_trap blocks htrap,built,bind,Except.bind,pure,Except.pure]
  have none8 : (retRegs (sigRets f.sig).length).isNone = false := by
    cases h : retRegs (sigRets f.sig).length <;> simp_all
  have range1 : (Array.range singleOrder.nodes.size).reverse.toList = [0] := rfl
  have hargs : ∃ locs n, sigArgLocs f.sig = .ok (locs,n) := sigArgLocs_ok hbytes
  obtain ⟨d,hd⟩ := lowerNode_single_trap (bytes := bytes)
    (input := { state := initial, blocks := Array.replicate singleOrder.nodes.size default, edgeArgs := Array.replicate singleOrder.nodes.size #[], schedule := #[], scans := #[], blockScans := #[], rules := #[] })
    blocks htrap hargs params core
  simp only [none8,Bool.false_eq_true,ite_false,range1,List.foldlM_cons,List.foldlM_nil,hd,bind,
    Except.bind,pure,Except.pure]
  exact ⟨_,rfl⟩

/-- **`Stock.lower` succeeds on one-block scalar functions that end in `trap`.** -/
theorem stock_lower_trap_ok {f : Clif.Function} {b : Clif.Block} {c : Clif.TrapCode}
    (blocks : f.blocks = [b]) (htrap : b.term = .trap c)
    (body : ∀ s ∈ b.body, Scalar.maskMixedBodyEligible s = true)
    (hp : f.sig.params.all Scalar.narrowAbiEligible = true)
    (hr : f.sig.returns.all Scalar.narrowAbiEligible = true)
    (hE : Compile.functionE f = true) (hdom : dominatedB f = true) (hs : lowerScopeB f = true)
    (hw : extendsWidenB f = true) (hin : Prg.iselInB f = true) (hdrv : driverInB f = true) :
    ∃ result, Stock.lower f = .ok result := by
  obtain ⟨⟨ctx, ranges, initial⟩, built⟩ := stock_buildCtx_ok_trap hE hdom hdrv blocks htrap
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
  have scalar : ∀ cl, Prg.InstOf f cl → ScalarNames cl := by
    intro cl ⟨B, hB, s, hs', hcl⟩
    subst hcl
    rw [blocks, List.mem_singleton] at hB
    subst hB
    exact scalarNames_of (mask_scalar (body s hs'))
  have block : f.blocks[0]? = some b := by rw [blocks]; rfl
  have rangeRun : ranges[0]? = some ranges[0]! := by
    have h := spec.ranges 0 b block
    rw [getElem!_def, h]
  obtain ⟨lowered, core⟩ := lowerBlockCore_trap_ok built hdom hs hw hin scalar block htrap rangeRun
    singleOrder (buildCtx_quiet built)
  exact stock_lower_single_trap hdrv hp hr blocks htrap built params core

private def trapFixture : Clif.Function := {
  name := "stock_lower_trap_ok"
  sig := { params := [⟨.i64,.none,.normal⟩,⟨.i64,.none,.normal⟩], returns := [⟨.i64,.none,.normal⟩] }
  blocks := [
    { id := 0, params := [(0, .i64), (1, .i64)],
      body := [⟨[2], .binary .imul .i64 0 1⟩, ⟨[3], .binary .iadd .i64 2 0⟩], term := .trap (.user 9) }] }

private def trapChecks : Bool :=
  trapFixture.sig.params.all Scalar.narrowAbiEligible && trapFixture.sig.returns.all Scalar.narrowAbiEligible &&
    Compile.functionE trapFixture && dominatedB trapFixture && lowerScopeB trapFixture &&
    extendsWidenB trapFixture && Prg.iselInB trapFixture && driverInB trapFixture

-- witness: native_decide (the fixed function's input-condition checks only)
private theorem trapChecks_true : trapChecks = true := by native_decide

/-- Non-vacuity: a real two-statement scalar function that ends in `trap` meets every premise, so
`Stock.lower` succeeds on it through `stock_lower_trap_ok`. -/
theorem stock_lower_trap_ok_witness : ∃ (f : Clif.Function) (b : Clif.Block) (c : Clif.TrapCode)
    (result : Result), f.blocks = [b] ∧ b.term = .trap c ∧ Stock.lower f = .ok result := by
  have h := trapChecks_true
  unfold trapChecks at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hp, hr⟩, hE⟩, hdom⟩, hs⟩, hw⟩, hin⟩, hdrv⟩ := h
  have body : ∀ s ∈ (trapFixture.blocks[0]!).body, Scalar.maskMixedBodyEligible s = true := by
    intro s hs'
    simp only [trapFixture, List.getElem!_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at hs'
    rcases hs' with rfl | rfl <;> decide
  obtain ⟨result, run⟩ := stock_lower_trap_ok (b := trapFixture.blocks[0]!) rfl rfl body hp hr hE hdom
    hs hw hin hdrv
  exact ⟨trapFixture, _, _, result, rfl, rfl, run⟩

end Backend.Stock.Proof
