import FV.Backend.Proof.StockAluRecordValues
import FV.Backend.Proof.StockAllocationFlow
import FV.Backend.Proof.StockCoverageBlock

/-! Fixed demand-array extent through actual Stock lowering. -/
namespace Backend.Stock.Proof.Extent
open Backend.Proof Backend.Proof.Driver Backend.Proof.Flow Backend.Stock.Proof.Coverage Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private def fields (st : State) := st.demand.size
private def ExtentEq (st next : State) := fields next = fields st
private theorem extent_refl (st : State) : ExtentEq st st := rfl
private theorem extent_trans {a b c : State} (ab : ExtentEq a b) (bc : ExtentEq b c) : ExtentEq a c := bc.trans ab
private theorem fields_rel {st next : State} (h : fields next = fields st) : ExtentEq st next := h
private theorem mark_fields (st : State) (x : Nat) : fields (st.mark x) = fields st := Array.size_modify
private theorem marks_fields (st : State) (vs : List Nat) : fields (vs.foldl State.mark st) = fields st := by
  induction vs generalizing st with
  | nil => rfl
  | cons v vs ih => exact (ih (st.mark v)).trans (mark_fields st v)

private theorem setAlias_fields {st next : State} {dst src : Reg}
    (h : st.setAlias dst src = .ok next) : fields next = fields st := by
  cases dst <;> cases src <;>
    simp only [State.setAlias, bind, Except.bind, pure, Except.pure,
      throw, throwThe, MonadExceptOf.throw] at h
  all_goals repeat' first | (solve | cases h) | (solve | cases h; rfl) | split at h

private def tryAliasStep (ps rets : List Reg) (acc : Except String (State × List Reg))
    (pair : Reg × Reg) : Except String (State × List Reg) := do
  let (s, regs) ← acc
  let (p, r) := pair
  if let some i := ps.idxOf? p then
    let some ret := rets[i]? | throw "try_call return register"
    pure (← s.setAlias r ret, regs ++ [ret])
  else pure (s, regs ++ [r])

private theorem try_fold_error (ps rets : List Reg) (pairs : List (Reg × Reg)) (e : String) :
    pairs.foldl (tryAliasStep ps rets) (.error e) = .error e := by
  induction pairs with
  | nil => rfl
  | cons pair pairs ih => exact ih

private theorem try_fold_fields (ps rets : List Reg) (pairs : List (Reg × Reg))
    (st : State) (regs : List Reg) {next : State} {out : List Reg}
    (h : pairs.foldl (tryAliasStep ps rets) (.ok (st, regs)) = .ok (next, out)) :
    fields next = fields st := by
  induction pairs generalizing st regs with
  | nil => cases h; rfl
  | cons pair pairs ih =>
    rw [List.foldl_cons] at h
    cases hs : tryAliasStep ps rets (.ok (st, regs)) pair with
    | error e => rw [hs, try_fold_error] at h; cases h
    | ok result =>
      rcases result with ⟨middle, rs⟩
      rw [hs] at h
      have hm : fields middle = fields st := by
        unfold tryAliasStep at hs
        simp only [bind, Except.bind] at hs
        cases hi : ps.idxOf? pair.1 with
        | none => simp only [hi, pure, Except.pure] at hs; cases hs; rfl
        | some i =>
          simp only [hi] at hs
          cases hr : rets[i]? with
          | none => simp only [hr] at hs; cases hs
          | some r =>
            simp only [hr] at hs
            cases ha : st.setAlias pair.2 r with
            | error e => rw [ha] at hs; cases hs
            | ok q =>
              rw [ha] at hs
              simp only [pure, Except.pure] at hs
              cases hs
              exact setAlias_fields ha
      exact (ih middle rs h).trans hm


private theorem delegate_alloc {ctx : Ctx} {t : Term} {args : List V}
    {st next : State} {v : V}
    (h : (match Backend.externCtor ctx t args st.base with
      | .ok (v, base) => ExtResult.ok (v, { st with base })
      | .fail => ExtResult.fail
      | .unmodeled e => ExtResult.unmodeled e) = ExtResult.ok (v, next)) :
    ExtentEq st next := by
  cases call : Backend.externCtor ctx t args st.base with
  | fail => rw [call] at h; cases h
  | unmodeled e => rw [call] at h; cases h
  | ok pair =>
    rcases pair with ⟨value, base⟩
    rw [call] at h
    cases h
    rfl

/-- Successful actual constructors preserve demand-array size, including all
scalar/list requests and reserved-payload alias folds. -/
theorem ctor_demand_size {ctx : Ctx} {t : Term} {args : List V}
    {st next : State} {v : V} (h : Stock.externCtor ctx t args st = .ok (v, next)) :
    next.demand.size = st.demand.size := by
  unfold Stock.externCtor at h
  split at h
  all_goals dsimp only at h
  all_goals try solve | exact delegate_alloc h
  all_goals repeat' first
    | (solve | cases h <;> exact extent_refl st)
    | (solve | cases h; exact fields_rel (mark_fields st _))
    | (solve | exact extent_trans (fields_rel (mark_fields st _)) (delegate_alloc h))
    | (solve | exact extent_trans (fields_rel (marks_fields st _)) (delegate_alloc h))
    | (solve | cases h; rfl)
    | split at h
  all_goals
    rename_i _ _ sig _ _ ps _ _ s regs step
    cases h
    exact fields_rel (try_fold_fields ps ctx.tryRegs.1
      ((payloadRegs sig.callConv).zip ctx.tryRegs.2) st [] step)

/-- Full actual term evaluation preserves the allocated demand-array extent. -/
theorem apply_demand_size {p : Program} {ctx : Ctx} {cfg : Config}
    {n ty t : Nat} {args : List V} {st next : State} {tr tr' : Array RuleId} {out : Option V}
    (h : (applyTerm p (Stock.sem ctx) cfg n ty t args).run (st, tr) =
      .ok (out, next, tr')) : next.demand.size = st.demand.size :=
  (presAt extent_refl (fun _ _ _ => extent_trans)
    (fun _ _ _ _ _ => ctor_demand_size) n).apply ty t args st tr out next tr' h

theorem named_demand_size {ctx : Ctx} {term : String} {args : List V}
    {st next : State} {out : Option V} {trace : List RuleId}
    (h : Stock.runTerm ctx term args st = .ok (out, next, trace)) :
    next.demand.size = st.demand.size := by
  unfold Stock.runTerm at h
  cases hr : Isle.Interp.run program (Stock.sem ctx) {} term args st with
  | error e => rw [hr] at h; cases h
  | ok result =>
    rw [hr] at h
    cases h
    unfold Isle.Interp.run at hr
    cases ht : program.termByName? term with
    | none => simp only [ht] at hr; cases hr
    | some t =>
      simp only [ht] at hr
      cases ha : (applyTerm program (Stock.sem ctx) {} (Config.fuel ({} : Config))
          t.ret t.id args).run (st, #[]) with
      | error e => simp only [ha, bind, Except.bind] at hr; cases hr
      | ok result =>
        rcases result with ⟨out, next, trace⟩
        simp only [ha, bind, Except.bind, pure, Except.pure] at hr
        cases hr
        exact apply_demand_size ha

private theorem fold_fields_eq {α β γ : Type} (field : α → γ)
    (step : α → β → Except String α)
    (hs : ∀ a b next, step a b = .ok next → field next = field a)
    (xs : List β) {a next : α} (h : xs.foldlM step a = .ok next) :
    field next = field a := by
  induction xs generalizing a with
  | nil => cases h; rfl
  | cons x xs ih =>
    rw [List.foldlM_cons] at h
    cases he : step a x with
    | error e => simp only [he, bind, Except.bind] at h; cases h
    | ok middle =>
      simp only [he, bind, Except.bind] at h
      exact (ih h).trans (hs a x middle he)

private theorem binding_fields {ctx : Ctx} {pairs : List (Nat × List Reg)}
    {st next : State} {copies : Array MInst}
    (h : bindResults ctx pairs st = .ok (next, copies)) : fields next = fields st := by
  unfold bindResults at h
  apply fold_fields_eq (fun a : State × Array MInst => fields a.1) _ ?_ pairs h
  intro acc pair next he
  rcases acc with ⟨s, code⟩
  rcases pair with ⟨v, rs⟩
  dsimp only at he
  cases hm : ctx.valueReg? v with
  | none => simp only [hm] at he; cases he
  | some r =>
    simp only [hm] at he
    split at he
    · rename_i _ n cls
      cases ha : s.setAlias r (.vreg n cls) with
      | error e => simp only [ha, bind, Except.bind] at he; cases he
      | ok q =>
        simp only [ha, bind, Except.bind, pure, Except.pure] at he
        cases he
        exact setAlias_fields ha
    · cases he; rfl
    · cases he

private theorem emitted_alloc {ctx : Ctx} {i : Nat} {st : State}
    {emission : Emission}
    (h : emitInstruction ctx i st = .ok emission) : ExtentEq st emission.state := by
  unfold emitInstruction at h
  cases hr : Stock.runTerm ctx "lower" [.inst i] st with
  | error e => simp only [hr, bind, Except.bind] at h; cases h
  | ok root =>
    rcases root with ⟨out, next, trace⟩
    simp only [hr, bind, Except.bind] at h
    cases out with
    | none => cases h
    | some out =>
      cases out <;> try (cases h)
      rename_i rss
      dsimp only at h
      split at h
      · cases h
      · cases hb : bindResults ctx (ctx.insts[i]!.results.zip rss) next with
        | error e => simp only [hb] at h; cases h
        | ok result =>
          rcases result with ⟨final, copies⟩
          simp only [hb, pure, Except.pure] at h
          cases h
          exact extent_trans (named_demand_size hr) (fields_rel (binding_fields hb))


private theorem commit_fields {ctx : Ctx} {block i : Nat} {st next : State}
    (h : commitOpportunistic ctx block i st = .ok (some next)) : fields next = fields st := by
  have values {values : List Nat} {a b : State}
      (h : commitOpportunisticValues ctx values a = .ok b) : fields b = fields a := by
    unfold commitOpportunisticValues at h
    apply fold_fields_eq fields _ ?_ values h
    intro a v b he
    split at he
    · split at he
      · rename_i dst hdst
        split at he
        · rename_i src _
          cases hs : a.setAlias dst src with
          | error e => simp only [hs, bind, Except.bind] at he; cases he
          | ok q =>
            simp only [hs, bind, Except.bind, pure, Except.pure] at he
            cases he
            exact setAlias_fields (next := q) hs
        · cases he
      · cases he
    · cases he; rfl
  unfold commitOpportunistic at h
  dsimp only at h
  split at h
  · cases h
  · cases hv : commitOpportunisticValues ctx (ctx.insts[i]!.results) st with
    | error e => simp only [hv, bind, Except.bind] at h; cases h
    | ok q =>
      simp only [hv, bind, Except.bind, pure, Except.pure] at h
      cases h
      exact values hv

private theorem scan_state_fields (st : State) (i : Nat) : fields (scanState st i) = fields st := by
  unfold scanState
  dsimp only
  split <;> rfl

/-- Actual scans preserve demand-array size in every decision path. -/
theorem scan_demand_size {ctx : Ctx} {block i ti : Nat} {branch : Bool}
    {st : State} {output : Scan}
    (h : scanInstruction ctx block i ti branch st = .ok output) : output.state.demand.size = st.demand.size := by
  have refl : ExtentEq st (scanState st i) := fields_rel (scan_state_fields st i)
  have emit (h : (emitInstruction ctx i (scanState st i) >>= fun e =>
      pure (e.scan block i (scanState st i))) = .ok output) : output.state.demand.size = st.demand.size := by
    cases he : emitInstruction ctx i (scanState st i) with
    | error e => simp only [he, bind, Except.bind] at h; cases h
    | ok e =>
      simp only [he, bind, Except.bind, pure, Except.pure] at h
      cases h
      exact extent_trans refl (emitted_alloc he)
  unfold scanInstruction at h
  dsimp only at h
  generalize hm : (if i == ti then true else ctx.insts[i]!.clif.any mustLower) = mandatory at h
  split at h
  · cases h; exact extent_refl _
  · split at h
    · cases h; exact refl
    · split at h
      · cases h; exact refl
      · split at h
        · cases hc : commitOpportunistic ctx block i (scanState st i) with
          | error e => simp only [hc, bind, Except.bind] at h; cases h
          | ok result =>
            simp only [hc, bind, Except.bind] at h
            cases result with
            | none => exact emit h
            | some q =>
              cases h
              exact extent_trans refl (fields_rel (commit_fields hc))
        · exact emit h

/-- Complete tail-recursive scans preserve demand-array size. -/
theorem scanBlock_demand_size {ctx : Ctx} {block ti : Nat} {branch : Bool}
    {indices : List Nat} {st : State} {output : BlockScan}
    (h : scanBlock ctx block ti branch indices st = .ok output) : output.state.demand.size = st.demand.size := by
  have cert := runScans_spec h
  clear h
  induction cert with
  | nil st => exact extent_refl _
  | cons head rest ih => exact extent_trans (scan_demand_size head) ih


private theorem forIn_frame {α β γ : Type} (field : α → γ)
    (step : β → α → Except String (ForInStep α))
    (keeps : ∀ x a b, step x a = .ok (.yield b) → field b = field a)
    (no_break : ∀ x a b, step x a ≠ .ok (.done b))
    (xs : List β) {a next : α} (h : forIn xs a step = .ok next) :
    field next = field a := by
  induction xs generalizing a with
  | nil => simp only [List.forIn_nil, pure, Except.pure] at h; cases h; rfl
  | cons x xs ih =>
    rw [List.forIn_cons] at h
    cases call : step x a with
    | error e => simp only [call, bind, Except.bind] at h; cases h
    | ok result =>
      cases result with
      | done b => exact False.elim (no_break x a b call)
      | yield b =>
        simp only [call, bind, Except.bind] at h
        exact (ih h).trans (keeps x a b call)

private def argStep (ctx : Ctx) (rets pays : List Reg) (index nh : Nat)
    (arg : Clif.TryArg) (acc : State × Array Reg) :
    Except String (ForInStep (State × Array Reg)) := do
  match arg with
  | .val v =>
    let some r := ctx.valueReg? v | throw s!"unknown value v{v}"
    pure (.yield (acc.1.mark v, acc.2.push r))
  | .ret i =>
    if index < nh then throw "try_call return on exception edge"
    let some r := rets[i]? | throw "try_call return index"
    pure (.yield (acc.1, acc.2.push r))
  | .exn i =>
    if index == nh then throw "try_call payload on normal edge"
    let some r := pays[i]? | throw "try_call payload index"
    pure (.yield (acc.1, acc.2.push r))

private theorem arg_frame (ctx : Ctx) (rets pays : List Reg) (index nh : Nat)
    (arg : Clif.TryArg) (a b : State × Array Reg)
    (h : argStep ctx rets pays index nh arg a = .ok (.yield b)) :
    fields b.1 = fields a.1 := by
  cases arg <;> unfold argStep at h
  all_goals repeat' first | (solve | cases h <;> simp only [fields, State.mark, Array.size_modify]) | split at h

private theorem arg_no_break (ctx : Ctx) (rets pays : List Reg) (index nh : Nat)
    (arg : Clif.TryArg) (a b : State × Array Reg) :
    argStep ctx rets pays index nh arg a ≠ .ok (.done b) := by
  intro h
  cases arg <;> unfold argStep at h
  all_goals repeat' first | (solve | cases h) | split at h

private theorem branch_frame {ctx : Ctx} {st next : State} {block index : Nat}
    {args : Array Reg} (h : branchArgs ctx st block index = .ok (args, next)) :
    fields next = fields st := by
  unfold branchArgs at h
  dsimp only at h
  split at h
  · rename_i id values lookup
    split at h
    · rename_i target found
      split at h
      · cases h
      · let ti := (st.instBlock.findIdx? (· == block)).getD 0 + ctx.func.blocks[block]!.body.length
        let reservations := st.tryRegs[ti]!
        let nh := match ctx.func.blocks[block]!.term with
          | .tryCall _ _ et | .tryCallIndirect _ _ et => et.handlers.length
          | _ => 0
        change (do
          let result ← forIn values (st, #[]) (argStep ctx reservations.1 reservations.2 index nh)
          pure (result.2, result.1)) = .ok (args, next) at h
        cases loop : forIn values (st, #[]) (argStep ctx reservations.1 reservations.2 index nh) with
        | error e => simp only [loop, bind, Except.bind] at h; cases h
        | ok result =>
          simp only [loop, bind, Except.bind, pure, Except.pure] at h
          cases h
          exact forIn_frame (fun a : State × Array Reg => fields a.1) _
            (arg_frame ctx reservations.1 reservations.2 index nh)
            (arg_no_break ctx reservations.1 reservations.2 index nh) values loop
    · cases h
  · cases h

private theorem outgoing_frame {ctx : Ctx} {order : Order} {bi : Nat} {targets : Array Nat}
    {st next : State} {outgoing : Array (Array Reg)}
    (h : collectOutgoing ctx order bi targets st = .ok (next, outgoing)) :
    fields next = fields st := by
  unfold collectOutgoing at h
  apply fold_fields_eq (fun a : State × Array (Array Reg) => fields a.1) _ ?_ _ h
  intro acc target result step
  unfold outgoingStep at step
  split at step
  · cases step; rfl
  · cases call : branchArgs ctx acc.1 bi target.2 with
    | error e => simp only [call, bind, Except.bind] at step; cases step
    | ok pair =>
      rcases pair with ⟨regs, state⟩
      simp only [call, bind, Except.bind, pure, Except.pure] at step
      cases step
      exact branch_frame call


private theorem branch_preserves {f : Clif.Function} {ctx : Ctx}
    {t : Clif.Terminator} {bi ti : Nat} {targets : Array Nat}
    {input : State} {output : BranchEmission}
    (run : emitBranch ctx f t bi ti targets input = .ok output) :
    fields output.state = fields input := by
  unfold emitBranch at run
  dsimp only at run
  let before : State := {input with current := some ti, color := none, base.emitted := #[]}
  change ((do
    let (out, next, fired) ← Stock.runTerm ctx "lower_branch" [.inst ti, .labels targets.toList] before
    if out.isNone then throw s!"no lowering rule for terminator {repr t}"
    let code ← branchCode f t targets next.base.emitted
    pure ⟨next, code, ⟨bi, ti, .emitted, before, next, [], fired, code⟩, fired⟩) :
      Except String BranchEmission) = .ok output at run
  cases root : Stock.runTerm ctx "lower_branch" [.inst ti, .labels targets.toList] before with
  | error e => simp only [root, bind, Except.bind] at run; cases run
  | ok result =>
    rcases result with ⟨out, next, fired⟩
    simp only [root, bind, Except.bind] at run
    split at run
    · cases run
    · cases code : branchCode f t targets next.base.emitted with
      | error e => simp only [code] at run; cases run
      | ok instructions =>
        simp only [code, pure, Except.pure] at run
        cases run
        have kept := named_demand_size root
        exact kept

private theorem scan_records {ctx : Ctx} {block ti : Nat} {branch : Bool}
    {indices : List Nat} {st : State} {output : BlockScan}
    (h : scanBlock ctx block ti branch indices st = .ok output) :
    ∀ record ∈ output.records, fields record.input = fields st ∧ fields record.output.state = fields st := by
  have cert := runScans_spec h
  clear h
  induction cert with
  | nil st => simp
  | cons head rest ih =>
    intro record member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨rfl, scan_demand_size head⟩
    · obtain ⟨before, after⟩ := ih record member
      exact ⟨before.trans (scan_demand_size head), after.trans (scan_demand_size head)⟩

private theorem core_size {ctx : Ctx} {order : Order} {f : Clif.Function}
    {b : Clif.Block} {bi start stop : Nat} {data : V} {targets : Array Nat}
    {input : State} {output : LoweredBlockCore}
    (run : lowerBlockCore ctx order f b bi start stop data targets input = .ok output) :
    fields output.state = fields input ∧ fields output.scan.input = fields input ∧
      ∀ record ∈ output.scan.output.records,
        fields record.input = fields input ∧ fields record.output.state = fields input := by
  let ti := stop - 1
  let termCtx : Ctx := {Driver.termCtx ctx ti data with tryRegs := input.tryRegs[ti]!}
  let branchCall : Except String (Option BranchEmission) :=
    if blockBranch b.term then some <$> emitBranch termCtx f b.term bi ti targets input else pure none
  have branch_keeps {br : Option BranchEmission} (call : branchCall = .ok br) :
      fields (br.map (fun (e : BranchEmission) => e.state) |>.getD input) = fields input := by
    unfold branchCall at call
    split at call
    · cases emitted : emitBranch termCtx f b.term bi ti targets input with
      | error e => simp only [emitted, Functor.map, Except.map] at call; cases call
      | ok e =>
        simp only [emitted, Functor.map, Except.map] at call
        cases call
        exact branch_preserves emitted
    · cases call; rfl
  have normal : lowerBlockCore ctx order f b bi start stop data targets input = ((do
    let br ← branchCall
    let edge ← collectOutgoing ctx order bi targets (br.map (fun (e : BranchEmission) => e.state) |>.getD input)
    let next := edge.1
    let outgoing := edge.2
    let beforeScan := {next with color := some next.endColor[bi]!}
    let indices := ((Array.range (stop - start)).map (start + ·)).reverse.toList
    let bodyScan ← scanBlock termCtx bi ti (blockBranch b.term) indices beforeScan
    pure ⟨bodyScan.state, bodyScan.code ++ (br.map (fun (e : BranchEmission) => e.code) |>.getD #[]), outgoing,
      br, ⟨termCtx, bi, ti, blockBranch b.term, indices, beforeScan, bodyScan⟩⟩) : Except String LoweredBlockCore) := by
    unfold lowerBlockCore
    dsimp only [branchCall, blockBranch, termCtx, ti]
    split <;> simp_all only [blockBranch, termCtx, ti] <;> rfl
  rw [normal] at run
  cases call : branchCall with
  | error e => simp only [call, bind, Except.bind] at run; cases run
  | ok br =>
    simp only [call, bind, Except.bind] at run
    cases edges : collectOutgoing ctx order bi targets (br.map (fun (e : BranchEmission) => e.state) |>.getD input) with
    | error e => simp only [edges, bind, Except.bind] at run; cases run
    | ok pair =>
      rcases pair with ⟨next, outgoing⟩
      simp only [edges, bind, Except.bind] at run
      have edgeSize : fields next = fields input := (outgoing_frame edges).trans (branch_keeps call)
      let beforeScan : State := {next with color := some next.endColor[bi]!}
      let indices := ((Array.range (stop - start)).map (start + ·)).reverse.toList
      have beforeSize : fields beforeScan = fields input := edgeSize
      change (scanBlock termCtx bi ti (blockBranch b.term) indices beforeScan >>= fun bodyScan =>
        pure (⟨bodyScan.state, bodyScan.code ++ (br.map (fun (e : BranchEmission) => e.code) |>.getD #[]), outgoing,
          br, ⟨termCtx, bi, ti, blockBranch b.term, indices, beforeScan, bodyScan⟩⟩ : LoweredBlockCore)) = .ok output at run
      cases scan : scanBlock termCtx bi ti (blockBranch b.term) indices beforeScan with
      | error e => simp only [scan, bind, Except.bind] at run; cases run
      | ok body =>
        simp only [scan, bind, Except.bind, pure, Except.pure] at run
        cases run
        refine ⟨(scanBlock_demand_size scan).trans beforeSize, beforeSize, ?_⟩
        intro record member
        obtain ⟨a, b⟩ := scan_records scan record member
        exact ⟨a.trans beforeSize, b.trans beforeSize⟩

private def RecordsExtent (cap : Nat) (events : Array BlockScanEvent) : Prop :=
  ∀ event ∈ events.toList, fields event.input = cap ∧
    ∀ record ∈ event.output.records, fields record.input = cap ∧ fields record.output.state = cap

private theorem node_size {ctx : Ctx} {ranges : Array (Nat × Nat)} {order : Order}
    {f : Clif.Function} {params : List Nat} {label cap : Nat} {input output : DriverState}
    (size : fields input.state = cap)
    (run : lowerNode ctx ranges order f params label input = .ok output) :
    fields output.state = cap ∧ (RecordsExtent cap input.blockScans → RecordsExtent cap output.blockScans) := by
  cases node : order.nodes[label]! with
  | edge pred k target =>
    unfold lowerNode at run
    simp only [node] at run
    cases call : branchArgs ctx input.state pred k with
    | error e => simp only [call, bind, Except.bind] at run; cases run
    | ok pair =>
      rcases pair with ⟨args, next⟩
      simp only [call, bind, Except.bind, pure, Except.pure] at run
      cases run
      exact ⟨(branch_frame call).trans size, fun old => old⟩
  | original bi =>
    let b := f.blocks[bi]!
    let start := (ranges[bi]!).1
    let stop := (ranges[bi]!).2
    let reject : Bool := (match b.term with | .ret .. => true | _ => false) &&
      (sretRet f).isEmpty && (sigRets f.sig != f.sig.returns)
    have normal : lowerNode ctx ranges order f params label input = (do
      let data ← blockData f b.term
      if reject then throw "sret parameter is not an entry-block parameter"
      let core ← lowerBlockCore ctx order f b bi start stop data order.successors[label]! input.state
      let block ← assembleOriginalBlock ctx f b bi label order.successors[label]!
        core.outgoing params core.state.uses core.code
      pure {recordCore input core bi stop with
        blocks := input.blocks.set! label block
        edgeArgs := input.edgeArgs.set! label core.outgoing}) := by
      unfold lowerNode
      simp only [node]
      dsimp only [blockData, reject, b, start, stop]
      split <;> simp_all only [reject] <;> rfl
    rw [normal] at run
    cases dataRun : blockData f b.term with
    | error e => simp only [dataRun, bind, Except.bind] at run; cases run
    | ok data =>
      simp only [dataRun, bind, Except.bind] at run
      split at run
      · cases run
      · cases coreRun : lowerBlockCore ctx order f b bi start stop data
            order.successors[label]! input.state with
        | error e => simp only [coreRun, bind, Except.bind] at run; cases run
        | ok core =>
          simp only [coreRun, bind, Except.bind] at run
          cases assembled : assembleOriginalBlock ctx f b bi label order.successors[label]!
              core.outgoing params core.state.uses core.code with
          | error e => simp only [assembled, bind, Except.bind] at run; cases run
          | ok block =>
            simp only [assembled, bind, Except.bind, pure, Except.pure] at run
            cases run
            obtain ⟨after, before, records⟩ := core_size coreRun
            refine ⟨after.trans size, ?_⟩
            intro old
            change RecordsExtent cap (input.blockScans.push core.scan)
            intro event member
            simp only [Array.toList_push, List.mem_append, List.mem_singleton] at member
            rcases member with member | rfl
            · exact old event member
            · refine ⟨before.trans size, ?_⟩
              intro record member
              obtain ⟨a, b⟩ := records record member
              exact ⟨a.trans size, b.trans size⟩

private theorem nodes_size {ctx : Ctx} {ranges : Array (Nat × Nat)} {order : Order}
    {f : Clif.Function} {params labels : List Nat} {cap : Nat} {input output : DriverState}
    (size : fields input.state = cap) (records : RecordsExtent cap input.blockScans)
    (run : labels.foldlM (fun input label => lowerNode ctx ranges order f params label input) input = .ok output) :
    fields output.state = cap ∧ RecordsExtent cap output.blockScans := by
  induction labels generalizing input with
  | nil => cases run; exact ⟨size, records⟩
  | cons label labels ih =>
    rw [List.foldlM_cons] at run
    cases step : lowerNode ctx ranges order f params label input with
    | error e => simp only [step, bind, Except.bind] at run; cases run
    | ok next =>
      simp only [step, bind, Except.bind] at run
      have preserved := node_size size step
      exact ih preserved.1 (preserved.2 records) run

/-- Every actual retained record has the initially allocated demand extent at
both endpoints. Successful driver execution derives this without a size certificate. -/
theorem lower_record_demand_size {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) :
    ∀ event ∈ result.blockScans.toList, ∀ record ∈ event.output.records,
      record.input.demand.size = result.ctx.valTy.size ∧ record.output.state.demand.size = result.ctx.valTy.size := by
  unfold Stock.lower at run
  dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind, Except.bind, pure, Except.pure] at run
    | split at run
  cases run
  rename_i _ _ params _ _ _ _ _ source build _ order _ _ driver traversed
  have initialized := buildCtx_demand_size build
  let initialDriver : DriverState := {
    state := source.2.2
    blocks := Array.replicate order.nodes.size default
    edgeArgs := Array.replicate order.nodes.size #[]
    schedule := #[], scans := #[], blockScans := #[], rules := #[] }
  have invariant := nodes_size (input := initialDriver) (output := driver)
    (cap := source.1.valTy.size) initialized (by simp [RecordsExtent, initialDriver]) traversed
  intro event events record records
  exact (invariant.2 event events).2 record records

private theorem build_map_size {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {st : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, st)) : ctx.valReg.size = ctx.valTy.size := by
  obtain ⟨original, _, requests, _, _, he⟩ := buildCtx_allocation build
  have stepSize (a : Allocation) (request : AllocationRequest) :
      (a.step request).valReg.size = a.valReg.size := by cases request <;> simp [Allocation.step]
  have foldSize : ∀ (rs : List AllocationRequest) (a : Allocation),
      (rs.foldl Allocation.step a).valReg.size = a.valReg.size := by
    intro rs
    induction rs with
    | nil => intro a; rfl
    | cons r rs ih => intro a; exact (ih (a.step r)).trans (stepSize a r)
  have hr := congrArg (fun q => q.1.valReg.size) he
  have ht := congrArg (fun q => q.1.valTy.size) he
  rw [hr, ht]
  simpa only [finishCtx, allocateRequests, Allocation.initial, Array.size_replicate] using
    foldSize requests (Allocation.initial original.valTy.size original.insts.size)

private theorem map_bound {ctx : Ctx} {x : Nat} {r : Reg}
    (mapped : ctx.valueReg? x = some r) : x < ctx.valReg.size := by
  by_cases bound : x < ctx.valReg.size
  · exact bound
  · unfold Ctx.valueReg? at mapped
    rw [Array.getElem?_eq_none (Nat.le_of_not_lt bound)] at mapped
    cases mapped

/-- Every actually mapped source value is in bounds in both demand arrays of
every retained record. Sparse source numbering is distinct from dense vreg numbering. -/
theorem lower_mapped_demand_bounds {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {x : Nat} {r : Reg} (mapped : event.ctx.valueReg? x = some r) :
    x < record.input.demand.size ∧ x < record.output.state.demand.size := by
  have actualMap := mapped
  rw [(stock_lower_record_context run scope events).2.1 x] at actualMap
  obtain ⟨ranges, params, earlier, suffix, starting, finishing, before, after,
    label, bi, data, core, build, ordered, initial, empty, parts, folded,
    final, prefixRun, nodeRun, suffixRun, node, coreRun, eventEq, stateEq⟩ :=
    stock_lower_blockScanOrigin run events
  have bound : x < result.ctx.valTy.size := by
    rw [← build_map_size build]
    exact map_bound actualMap
  obtain ⟨inputSize, outputSize⟩ := lower_record_demand_size run event events record records
  rw [inputSize, outputSize]
  exact ⟨bound, bound⟩

private theorem scans_execute {exec : Nat → State → Except String Scan}
    {indices : List Nat} {input : State} {output : BlockScan}
    (cert : ScansSpec exec indices input output) :
    ∀ record ∈ output.records, exec record.inst record.input = .ok record.output := by
  induction cert with
  | nil input => simp
  | cons head rest ih =>
    intro record member
    rcases List.mem_cons.mp member with rfl | member
    · exact head
    · exact ih record member

/-- Successful nonempty marking paths and an actual retained sparse-ID add
record inhabit all demand-size and map-bound contracts. -/
theorem demand_extent_witness :
    Stock.externCtor sinkCtx T.mark_value_used [.value 0] sinkState = .ok (.op .unit, sinkState.mark 0) ∧
    (applyTerm program (Stock.sem sinkCtx) {} 1 T.mark_value_used.ret T.mark_value_used.id [.value 0]).run
      (sinkState, #[]) = .ok (some (.op .unit), sinkState.mark 0, #[]) ∧
    Stock.runTerm sinkCtx "mark_value_used" [.value 0] sinkState = .ok (some (.op .unit), sinkState.mark 0, []) ∧
    (sinkState.mark 0).demand.size = sinkState.demand.size ∧
    ∃ (f : Clif.Function) (result : Result) (event : BlockScanEvent) (record : ScanRecord),
      Stock.lower f = .ok result ∧ LowerScope f ∧ event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧
      record.input.demand.size = result.ctx.valTy.size ∧ record.output.state.demand.size = result.ctx.valTy.size ∧
      100 < record.input.demand.size ∧ 100 < record.output.state.demand.size := by
  obtain ⟨ctor, helper, named, _⟩ := stock_demand_mono_witness
  have ctorSize := ctor_demand_size ctor
  have helperSize := apply_demand_size helper
  have namedSize := named_demand_size named
  obtain ⟨result, event, record, step, run, scope, ssa, events, records, current, recorded, emitted, _, _, _⟩ :=
    stock_lower_record_fresh_result_witness
  obtain ⟨ranges, params, earlier, suffix, starting, finishing, before, after,
    label, bi, data, core, build, ordered, initial, empty, parts, folded,
    final, prefixRun, nodeRun, suffixRun, node, coreRun, eventEq, stateEq⟩ :=
    stock_lower_blockScanOrigin run events
  have scanRun := (stock_lowerBlockCore_scanOrigin coreRun).2.2.2.2.2
  have scanSize := scanBlock_demand_size scanRun
  have individual : ∀ r ∈ event.output.records,
      scanInstruction event.ctx event.block r.inst event.termInst event.isBranch r.input = .ok r.output := by
    rw [eventEq]
    exact scans_execute (runScans_spec scanRun)
  have recordSize := scan_demand_size (individual record records)
  obtain ⟨original, st0, old, spec, view⟩ := buildCtx_source build
  have bounded : 100 < result.ctx.valTy.size := by
    rw [view.valTy, spec.facts.size.2.2, ← spec.facts.size.1]
    exact (spec.facts.vals 100 (by decide +kernel)).1
  obtain ⟨r, hm⟩ := Option.isSome_iff_exists.mp ((buildCtx_value_domain build 100 bounded).mpr (by decide +kernel))
  have mapped : event.ctx.valueReg? 100 = some r := by
    rw [(stock_lower_record_context run scope events).2.1 100]
    exact hm
  obtain ⟨a, b⟩ := lower_record_demand_size run event events record records
  have bounds := lower_mapped_demand_bounds run scope events records mapped
  exact ⟨ctor, helper, named, ctorSize, _, result, event, record, run, scope, events, records, a, b, bounds⟩

end Backend.Stock.Proof.Extent
