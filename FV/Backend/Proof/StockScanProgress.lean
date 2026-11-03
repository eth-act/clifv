import FV.Backend.Proof.StockLowerOutputs
import FV.Backend.Proof.StockRetProgress
import FV.Backend.Proof.StockCoverageScans
import FV.Backend.Proof.StockBlockScan
import FV.Backend.Proof.StockBlockRanges

/-!
# Progress of Stock's scan over a scalar `return` block

From a quiet scheduling state (nothing sunk, no remembered definition), every scan step of a
scalar block succeeds and keeps the state quiet: a sunk instruction never occurs, an omitted or
committed step keeps the state, and an emitted step runs the instruction's `lower` root
(`stock_runTerm_lower_ok` for a statement, `stock_runTerm_ret_ok` for the `return`) and aliases each
result value to its int vreg (`bindResults`). So the backward scan of a `return` block and the
block's core lowering succeed (`lowerBlockCore_ret_ok`).
-/

namespace Backend.Stock.Proof.ScanProgress
open Backend Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64 Backend.Stock.Proof
  Backend.Stock.Proof.Coverage Backend.Stock.Proof.LowerProjection
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- The scheduling invariant of a scalar scan: nothing is sunk and nothing is remembered. -/
structure Quiet (st : State) : Prop where
  unsunk : NoSunk st
  empty : NoOpportunity st

/-- Successful context construction starts quiet. -/
theorem buildCtx_quiet {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)}
    {initial : State} (build : Stock.buildCtx f = .ok (ctx, ranges, initial)) : Quiet initial := by
  refine ⟨?_, buildCtx_noOpportunity build⟩
  unfold Stock.buildCtx at build
  cases legacy : Backend.buildCtx f with
  | error e => simp only [legacy, bind, Except.bind] at build; cases build
  | ok result =>
    rcases result with ⟨original, ranges, before⟩
    simp only [legacy, bind, Except.bind] at build
    by_cases hc : (original.valTy.toList.any fun o => o.any (·.valClass != .int)) = true
    · simp only [hc, ↓reduceIte] at build
      simp [throw, throwThe, MonadExceptOf.throw] at build
    simp only [hc, Bool.false_eq_true, ↓reduceIte, pure, Except.pure] at build
    cases requestRun : allocationRequests f ranges with
    | error e => simp only [requestRun, bind, Except.bind] at build; cases build
    | ok requests =>
      simp only [requestRun, bind, Except.bind, pure, Except.pure] at build
      cases build
      intro i
      change (Array.replicate original.insts.size false)[i]! = false
      by_cases inside : i < original.insts.size <;>
        simp [getElem!_def, Array.getElem?_replicate, inside] <;> rfl

private theorem scanState_frame (st : State) (i : Nat) :
    (scanState st i).sunk = st.sunk ∧ (scanState st i).opportunistic = st.opportunistic := by
  unfold scanState
  dsimp only
  split <;> exact ⟨rfl, rfl⟩

private theorem marks_frame (st : State) (ys : List Nat) :
    (ys.foldl State.mark st).sunk = st.sunk ∧
      (ys.foldl State.mark st).opportunistic = st.opportunistic := by
  induction ys generalizing st with
  | nil => exact ⟨rfl, rfl⟩
  | cons y ys ih => exact ih (st.mark y)

private theorem commitValues_empty (ctx : Ctx) (values : List Nat) (st : State)
    (empty : NoOpportunity st) : commitOpportunisticValues ctx values st = .ok st := by
  unfold commitOpportunisticValues
  induction values with
  | nil => rfl
  | cons v values ih =>
    rw [List.foldlM_cons]
    simp only [empty v, pure, Except.pure, bind, Except.bind]
    exact ih

/-- With no remembered definition, a commit attempt keeps the state or declines. -/
private theorem commit_quiet (ctx : Ctx) (block i : Nat) {st : State} (empty : NoOpportunity st) :
    ∃ r, commitOpportunistic ctx block i st = .ok r ∧ (r = none ∨ r = some st) := by
  cases h : commitOpportunistic ctx block i st with
  | error e =>
    exfalso
    unfold commitOpportunistic at h
    dsimp only at h
    split at h
    · cases h
    · rw [commitValues_empty ctx _ st empty] at h
      cases h
  | ok r =>
    refine ⟨r, rfl, ?_⟩
    unfold commitOpportunistic at h
    dsimp only at h
    split at h
    · cases h
      exact .inl rfl
    · rw [commitValues_empty ctx _ st empty] at h
      cases h
      exact .inr rfl

/-- **A scan step succeeds from a quiet state** when emission succeeds from quiet states and keeps
them quiet. -/
theorem scan_ok {ctx : Ctx} {block i ti : Nat} {isBranch : Bool} {input : State}
    (quiet : Quiet input)
    (emits : ∀ before, Quiet before → ∃ e, emitInstruction ctx i before = .ok e ∧ Quiet e.state) :
    ∃ output, scanInstruction ctx block i ti isBranch input = .ok output ∧ Quiet output.state := by
  have normalized : Quiet (scanState input i) := by
    obtain ⟨sunkEq, tableEq⟩ := scanState_frame input i
    exact ⟨fun j => by rw [sunkEq]; exact quiet.unsunk j, fun v => by rw [tableEq]; exact quiet.empty v⟩
  obtain ⟨e, he, qe⟩ := emits _ normalized
  have unsunk : input.sunk[i]! = false := quiet.unsunk i
  obtain ⟨r, c, hr⟩ := commit_quiet ctx block i normalized.empty
  unfold scanInstruction
  rcases hr with rfl | rfl
  all_goals
    simp only [unsunk, Bool.false_eq_true, ↓reduceIte, c, he, bind, Except.bind, pure, Except.pure]
    repeat' split
  all_goals first
    | exact ⟨_, rfl, normalized⟩
    | exact ⟨_, rfl, qe⟩

/-- `bindResults` succeeds on int-vreg results of values with int vregs, keeping the scheduling
fields. -/
theorem bindResults_ok (ctx : Ctx) (pairs : List (Nat × List Reg)) (next : State)
    (ok : ∀ p ∈ pairs, (∃ n, ctx.valueReg? p.1 = some (.vreg n .int)) ∧ ∃ m, p.2 = [.vreg m .int]) :
    ∃ st extra, bindResults ctx pairs next = .ok (st, extra) ∧ st.sunk = next.sunk ∧
      st.opportunistic = next.opportunistic := by
  induction pairs generalizing next with
  | nil => exact ⟨next, #[], rfl, rfl, rfl⟩
  | cons p rest ih =>
    obtain ⟨⟨n, hv⟩, m, hr⟩ := ok p (List.mem_cons_self ..)
    obtain ⟨st1, h1, s1, o1⟩ : ∃ st1, next.setAlias (.vreg n .int) (.vreg m .int) = .ok st1 ∧
        st1.sunk = next.sunk ∧ st1.opportunistic = next.opportunistic := ⟨_, rfl, rfl, rfl⟩
    obtain ⟨st, extra, h, s, o⟩ := ih st1 (fun q hq => ok q (List.mem_cons_of_mem _ hq))
    refine ⟨st, extra, ?_, s.trans s1, o.trans o1⟩
    obtain ⟨v, rs⟩ := p
    simp only at hv hr
    subst hr
    unfold bindResults at h ⊢
    rw [List.foldlM_cons]
    simp only [hv, h1, bind, Except.bind, pure, Except.pure]
    exact h

private theorem getElem!_of_some {ctx : Ctx} {i : Nat} {info : IInfo}
    (source : ctx.insts[i]? = some info) : ctx.insts[i]! = info := by
  rw [getElem!_def, source]

private theorem mapM_some {α β : Type} {g : α → Option β} :
    ∀ (xs : List α), (∀ x ∈ xs, (g x).isSome) → ∃ ys, xs.mapM g = some ys ∧ ys.length = xs.length
  | [], _ => ⟨[], rfl, rfl⟩
  | x :: xs, h => by
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (h x (List.mem_cons_self ..))
    obtain ⟨ys, hys, hlen⟩ := mapM_some xs (fun z hz => h z (List.mem_cons_of_mem _ hz))
    refine ⟨y :: ys, ?_, by simp [hlen]⟩
    simp [List.mapM_cons, hy, hys]

/-- **Emission of a scalar statement succeeds from a quiet state and keeps it quiet.** -/
theorem emit_stmt_ok {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {st0 : State}
    (hb : Stock.buildCtx f = .ok (ctx, ranges, st0)) (hdom : dominatedB f = true)
    (hs : lowerScopeB f = true) (hw : extendsWidenB f = true) (hin : Prg.iselInB f = true)
    (scalar : ∀ cl, Prg.InstOf f cl → ScalarNames cl)
    {ti : Nat} (hph : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩) (data : V)
    (regs : List Reg × List Reg)
    (clean : Cov.Clean (sourceIdentityCtx { termCtx ctx ti data with tryRegs := regs }))
    {i : Nat} {info : IInfo} {inst : Clif.Inst}
    (source : ({ termCtx ctx ti data with tryRegs := regs } : Ctx).insts[i]? = some info)
    (clif : info.clif = some inst) {before : State} (quiet : Quiet before) :
    ∃ e, emitInstruction { termCtx ctx ti data with tryRegs := regs } i before = .ok e ∧
      Quiet e.state := by
  have hP : Prg.PInv f { termCtx ctx ti data with tryRegs := regs } :=
    stock_pinv_termCtx (stock_pinv hb hdom hs hw hin) hph data regs
  have mapped : MappedCtxInv f { termCtx ctx ti data with tryRegs := regs } :=
    ((buildCtx_mappedInv (lowerScope_of hs) hb).termCtx hph data).withTryRegs regs
  obtain ⟨rss, st', tr, hrun, hshape, hkeep⟩ :=
    stock_runTerm_lower_ok hb hdom hs hw hin scalar hph data regs source clif quiet.unsunk
  have table := statement_noOpportunity mapped clean source clif hrun
  have noLoad : ∀ (j : Nat) (info : IInfo) (cl : Clif.Inst),
      ({ termCtx ctx ti data with tryRegs := regs } : Ctx).insts[j]? = some info → info.clif = some cl →
      (instNames cl).1 ≠ "LoadNoOffset" ∧ (instNames cl).1 ≠ "Load" :=
    fun j info cl hj hc => (scalar cl (hP.clifOf j info cl hj hc)).noLoad
  have pairs : ∀ p ∈ info.results.zip rss,
      (∃ n, ({ termCtx ctx ti data with tryRegs := regs } : Ctx).valueReg? p.1 = some (.vreg n .int)) ∧
        ∃ m, p.2 = [.vreg m .int] := by
    intro p hp
    have hres : info.results ≠ [] := by
      intro empty
      rw [empty] at hp
      cases hp
    obtain ⟨-, lengths⟩ := hshape hres
    have outs := stock_stmt_int_out mapped clean noLoad source clif (scalar inst (hP.clifOf i info inst source clif))
      hres hrun
    obtain ⟨v, rs⟩ := p
    have hv := List.of_mem_zip hp
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (hP.resTyped i info source v hv.1)
    refine ⟨mapped.typedReg v t ht, ?_⟩
    have one := lengths rs hv.2
    match rs, one with
    | [r], _ =>
      obtain ⟨m, hm⟩ := outs [r] hv.2 r (List.mem_singleton_self r)
      exact ⟨m, by rw [hm]⟩
  obtain ⟨st, extra, hbind, sunkEq, tableEq⟩ := bindResults_ok _ _ st' pairs
  refine ⟨⟨st, st.base.emitted ++ extra, rss, tr⟩, ?_, ?_⟩
  · unfold emitInstruction
    rw [getElem!_of_some source]
    simp only [hrun, bind, Except.bind]
    have count : (rss.length != info.results.length && !info.results.isEmpty) = false := by
      by_cases hres : info.results = []
      · simp [hres]
      · simp [(hshape hres).1, hres]
    simp only [count, Bool.false_eq_true, ↓reduceIte, hbind, pure, Except.pure]
  · refine ⟨fun j => ?_, fun v => ?_⟩
    · show st.sunk[j]! = false
      rw [sunkEq]
      exact hkeep j
    · show st.opportunistic[v]! = none
      rw [tableEq, table]
      exact quiet.empty v

/-- **Emission of a `return` succeeds from a quiet state and keeps it quiet.** -/
theorem emit_ret_ok {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {st0 : State}
    (hb : Stock.buildCtx f = .ok (ctx, ranges, st0)) (hdom : dominatedB f = true)
    (hs : lowerScopeB f = true) (hw : extendsWidenB f = true) (hin : Prg.iselInB f = true)
    (hdrv : driverInB f = true) {ti : Nat} (hph : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩)
    {B : Clif.Block} (hB : B ∈ f.blocks) {xs : List Nat} (hret : B.term = .ret xs)
    (regs : List Reg × List Reg) {before : State} (quiet : Quiet before) :
    ∃ e, emitInstruction { termCtx ctx ti (retData f xs) with tryRegs := regs } ti before = .ok e ∧
      Quiet e.state := by
  obtain ⟨original, st1, hold, -, view⟩ := buildCtx_source hb
  have mapped : MappedCtxInv f { termCtx ctx ti (retData f xs) with tryRegs := regs } :=
    ((buildCtx_mappedInv (lowerScope_of hs) hb).termCtx hph _).withTryRegs regs
  have slot : ({ termCtx ctx ti (retData f xs) with tryRegs := regs } : Ctx).insts[ti]? =
      some ⟨.data 152 18 [.data 151 7 [], .values (xs ++ sretRet f)], [], [], none⟩ := by
    rw [← retData_eq]
    exact termCtx_insts_self hph _
  have typed : ∀ y ∈ xs ++ sretRet f,
      (({ termCtx ctx ti (retData f xs) with tryRegs := regs } : Ctx).valueReg? y).isSome := by
    intro y hy
    have h := Prg.termArgs_typed hold hdom hB (x := y) (by rw [hret]; simpa [abiTerm, Driver.termArgs] using hy)
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp h
    have ht' : ({ termCtx ctx ti (retData f xs) with tryRegs := regs } : Ctx).valueType? y = some t := by
      show (ctx.valTy[y]?).join = some t
      rw [view.valTy]
      exact ht
    obtain ⟨n, hn⟩ := mapped.typedReg y t ht'
    rw [hn]
    rfl
  obtain ⟨rs, hrs, hlen⟩ := mapM_some _ typed
  have hTI := Prg.termIsel_of hin hB
  rw [hret] at hTI
  have hv : xs.length = f.sig.returns.length := by simpa [Prg.termIselB] using hTI
  have h8 : f.sig.returns.length ≤ 8 := by
    simp only [driverInB, Bool.and_eq_true, decide_eq_true_eq] at hdrv; exact hdrv.1.2
  have hm := Prg.ret_len hv h8
  have func : ({ termCtx ctx ti (retData f xs) with tryRegs := regs } : Ctx).func = f := mapped.func
  obtain ⟨ps, pins⟩ : ∃ ps, returnPins ({ termCtx ctx ti (retData f xs) with tryRegs := regs } : Ctx).func
      rs.length = some ps := by
    rw [func]
    unfold returnPins
    split
    · exact ⟨_, rfl⟩
    · unfold retRegs
      rw [ite_eq_left_iff.mpr (fun h => absurd (by omega) h)]
      exact ⟨_, rfl⟩
  obtain ⟨w, s', tr, hback⟩ := stock_ret_backend hb hdom hs hw hin hdrv hph hB hret regs before.base
  obtain ⟨trace, hrun⟩ := stock_runTerm_ret_ok _ slot quiet.unsunk ⟨w, s', tr, hback⟩ hrs pins
  obtain ⟨sunkEq, tableEq⟩ := marks_frame before (xs ++ sretRet f)
  refine ⟨⟨{ (xs ++ sretRet f).foldl State.mark before with
      base := ((xs ++ sretRet f).foldl State.mark before).base.emit (.rets (rs.zip ps)) },
    ((xs ++ sretRet f).foldl State.mark before).base.emit (.rets (rs.zip ps)) |>.emitted |>.append #[],
    [], trace⟩, ?_, ?_⟩
  · unfold emitInstruction
    rw [getElem!_of_some slot]
    simp only [hrun, bind, Except.bind, List.isEmpty_nil, Bool.not_true, Bool.and_false,
      Bool.false_eq_true, ↓reduceIte, List.zip_nil_left]
    rfl
  · refine ⟨fun j => ?_, fun v => ?_⟩
    · show (List.foldl State.mark before (xs ++ sretRet f)).sunk[j]! = false
      rw [sunkEq]
      exact quiet.unsunk j
    · show (List.foldl State.mark before (xs ++ sretRet f)).opportunistic[v]! = none
      rw [tableEq]
      exact quiet.empty v

/-- **A scan over instructions whose emission succeeds from quiet states succeeds.** -/
theorem scanBlock_ok {c : Ctx} {block ti : Nat} {isBranch : Bool} :
    ∀ (indices : List Nat),
      (∀ i ∈ indices, ∀ before, Quiet before → ∃ e, emitInstruction c i before = .ok e ∧ Quiet e.state) →
      ∀ {input : State}, Quiet input →
        ∃ out, scanBlock c block ti isBranch indices input = .ok out ∧ Quiet out.state := by
  intro indices step input quiet
  unfold scanBlock
  rw [runScans_ref]
  induction indices generalizing input with
  | nil => exact ⟨_, rfl, quiet⟩
  | cons i rest ih =>
    obtain ⟨scan, hscan, qscan⟩ := scan_ok (block := block) (ti := ti) (isBranch := isBranch) quiet
      (step i (List.mem_cons_self ..))
    obtain ⟨out, hout, qout⟩ := ih (fun j hj => step j (List.mem_cons_of_mem _ hj)) qscan
    refine ⟨⟨out.state, ⟨i, input, scan⟩ :: out.records, out.code ++ scan.emitted⟩, ?_, qout⟩
    simp only [runScansRef, hscan, hout, bind, Except.bind, pure, Except.pure]

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

/-- **The core lowering of a scalar `return` block succeeds from a quiet state**: no branch, no
outgoing arguments, and the backward scan of its body and `return`. -/
theorem lowerBlockCore_ret_ok {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)}
    {st0 : State} (hb : Stock.buildCtx f = .ok (ctx, ranges, st0)) (hdom : dominatedB f = true)
    (hs : lowerScopeB f = true) (hw : extendsWidenB f = true) (hin : Prg.iselInB f = true)
    (hdrv : driverInB f = true) (scalar : ∀ cl, Prg.InstOf f cl → ScalarNames cl)
    {bi : Nat} {b : Clif.Block} (block : f.blocks[bi]? = some b) {xs : List Nat}
    (hret : b.term = .ret xs) {range : Nat × Nat} (rangeRun : ranges[bi]? = some range)
    (order : Order) {input : State} (quiet : Quiet input) :
    ∃ lowered, lowerBlockCore ctx order f b bi range.1 range.2 (retData f xs) #[] input =
      .ok lowered := by
  obtain ⟨original, before, legacy, spec, view⟩ := buildCtx_source hb
  have rangeEq := spec.ranges bi b block
  rw [rangeRun] at rangeEq
  have endEq : range.2 - 1 = blockStart f bi + b.body.length := by cases rangeEq; omega
  have ph : ctx.insts[range.2 - 1]? = some ⟨.op .unit, [], [], none⟩ := by
    rw [endEq]; exact placeholder hb block
  have hB : b ∈ f.blocks := List.mem_of_getElem? block
  have clean : Cov.Clean (sourceIdentityCtx { termCtx ctx (range.2 - 1) (retData f xs) with
      tryRegs := input.tryRegs[range.2 - 1]! }) :=
    Cov.clean_termCtx (clean_stock hb) (t := abiTerm f (.ret xs)) rfl (range.2 - 1)
  have steps : ∀ i ∈ (((Array.range (range.2 - range.1)).map (range.1 + ·)).reverse.toList),
      ∀ before, Quiet before → ∃ e, emitInstruction { termCtx ctx (range.2 - 1) (retData f xs) with
        tryRegs := input.tryRegs[range.2 - 1]! } i before = .ok e ∧ Quiet e.state := by
    intro i member before q
    by_cases terminal : i = range.2 - 1
    · subst terminal
      exact emit_ret_ok hb hdom hs hw hin hdrv ph hB hret _ q
    · obtain ⟨lo, hi⟩ := stock_backward_indices_mem member
      cases rangeEq
      have index : i - blockStart f bi < b.body.length := by simp only at lo hi terminal; omega
      cases statement : b.body[i - blockStart f bi]? with
      | none => have outside := List.getElem?_eq_none_iff.mp statement; omega
      | some stm =>
        obtain ⟨info, lookup, clif, -⟩ := spec.facts.stmt bi b _ stm block statement
        have offset : blockStart f bi + (i - blockStart f bi) = i := by simp only at lo; omega
        rw [offset] at lookup
        have source : ({ termCtx ctx (blockStart f bi + b.body.length + 1 - 1) (retData f xs) with
            tryRegs := input.tryRegs[blockStart f bi + b.body.length + 1 - 1]! } : Ctx).insts[i]? =
              some info := by
          change (Driver.termCtx ctx _ (retData f xs)).insts[i]? = some info
          rw [termCtx_insts_ne terminal, view.insts]
          exact lookup
        exact emit_stmt_ok hb hdom hs hw hin scalar ph (retData f xs) _ clean source clif q
  obtain ⟨out, hscan, -⟩ := scanBlock_ok (block := bi) (isBranch := false) _ steps
    (input := { input with color := some input.endColor[bi]! })
    ⟨fun j => quiet.unsunk j, fun v => quiet.empty v⟩
  have hscan' : scanBlock { ctx with insts := ctx.insts.set! (range.2 - 1) ⟨retData f xs, [], [], none⟩, tryRegs := input.tryRegs[range.2 - 1]! }
      bi (range.2 - 1) false
      (((Array.range (range.2 - range.1)).map (range.1 + ·)).reverse.toList)
      { input with color := some input.endColor[bi]! } = .ok out := hscan
  cases hcore : lowerBlockCore ctx order f b bi range.1 range.2 (retData f xs) #[] input with
  | ok lowered => exact ⟨lowered, rfl⟩
  | error e =>
    exfalso
    unfold lowerBlockCore at hcore
    have hout : collectOutgoing ctx order bi #[] input = .ok (input, #[]) := rfl
    simp only [hret, pure, Except.pure, bind, Except.bind, ↓reduceIte, Bool.false_eq_true,
      Option.map_none, Option.getD_none, hout, hscan'] at hcore
    cases hcore

private def scanFixture : Clif.Function := {
  name := "stock_scan_progress"
  sig := { params := [⟨.i64,.none,.normal⟩,⟨.i64,.none,.normal⟩], returns := [⟨.i64,.none,.normal⟩] }
  blocks := [
    { id := 0, params := [(0, .i64), (1, .i64)], body := [⟨[2], .binary .iadd .i64 0 1⟩], term := .ret [2] }] }

private def scanChecks : Bool :=
  dominatedB scanFixture && lowerScopeB scanFixture && extendsWidenB scanFixture &&
    Prg.iselInB scanFixture && driverInB scanFixture &&
  match Stock.buildCtx scanFixture with
  | .error _ => false
  | .ok (_, ranges, _) => ranges[0]?.isSome

-- witness: native_decide (one fixed context build and its scope checks only)
private theorem scanChecks_true : scanChecks = true := by native_decide

private theorem scanFixture_names : ∀ cl, Prg.InstOf scanFixture cl → ScalarNames cl := by
  intro cl ⟨B, hB, s, hs, hcl⟩
  simp only [scanFixture, List.mem_cons, List.not_mem_nil, or_false] at hB
  subst hB
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  subst hs
  subst hcl
  refine ⟨by decide, ?_, ?_⟩
  · intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl <;> decide
  · intro h
    exfalso
    rcases h with h | h <;> simp [instNames, binaryOpcode] at h

/-- Non-vacuity: a real scalar `return` block has a successful core lowering for every block
order, through `lowerBlockCore_ret_ok`. -/
theorem lowerBlockCore_ret_ok_witness :
    ∃ (f : Clif.Function) (ctx : Ctx) (ranges : Array (Nat × Nat)) (st0 : State) (b : Clif.Block)
      (xs : List Nat) (range : Nat × Nat),
      Stock.buildCtx f = .ok (ctx, ranges, st0) ∧ f.blocks[0]? = some b ∧ b.term = .ret xs ∧
      ranges[0]? = some range ∧ ∀ order, ∃ lowered,
        lowerBlockCore ctx order f b 0 range.1 range.2 (retData f xs) #[] st0 = .ok lowered := by
  have h := scanChecks_true
  unfold scanChecks at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hdom, hs⟩, hw⟩, hin⟩, hdrv⟩, h⟩ := h
  cases hb : Stock.buildCtx scanFixture with
  | error message => rw [hb] at h; cases h
  | ok triple =>
    obtain ⟨ctx, ranges, st0⟩ := triple
    rw [hb] at h
    obtain ⟨range, hr⟩ := Option.isSome_iff_exists.mp h
    have block : scanFixture.blocks[0]? = some scanFixture.blocks[0]! := rfl
    refine ⟨scanFixture, ctx, ranges, st0, _, [2], range, hb, block, rfl, hr, fun order => ?_⟩
    exact lowerBlockCore_ret_ok hb hdom hs hw hin hdrv scanFixture_names block rfl hr order
      (buildCtx_quiet hb)

end Backend.Stock.Proof.ScanProgress
