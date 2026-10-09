import FV.Backend.Proof.StockScanFrontiers

/-! Allocation and alias bounds through actual branch, block, and driver transitions. -/
namespace Backend.Stock.Proof
open Backend.Proof Isle Isle.Interp Isle.Aarch64
attribute [local irreducible] Isle.Aarch64.program
set_option maxRecDepth 4096

private def frame (st : State) := (st.base.nextVreg, st.tryRegs, st.alias)

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
    frame b.1 = frame a.1 := by
  cases arg <;> unfold argStep at h
  all_goals repeat' first | (solve | cases h <;> rfl) | split at h

private theorem arg_no_break (ctx : Ctx) (rets pays : List Reg) (index nh : Nat)
    (arg : Clif.TryArg) (a b : State × Array Reg) :
    argStep ctx rets pays index nh arg a ≠ .ok (.done b) := by
  intro h
  cases arg <;> unfold argStep at h
  all_goals repeat' first | (solve | cases h) | split at h

private theorem branch_frame {ctx : Ctx} {st next : State} {block index : Nat}
    {args : Array Reg} (h : branchArgs ctx st block index = .ok (args, next)) :
    frame next = frame st := by
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
          exact forIn_frame (fun a : State × Array Reg => frame a.1) _
            (arg_frame ctx reservations.1 reservations.2 index nh)
            (arg_no_break ctx reservations.1 reservations.2 index nh) values loop
    · cases h
  · cases h

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


private theorem outgoing_frame {ctx : Ctx} {order : Order} {bi : Nat} {targets : Array Nat}
    {st next : State} {outgoing : Array (Array Reg)}
    (h : collectOutgoing ctx order bi targets st = .ok (next, outgoing)) :
    frame next = frame st := by
  unfold collectOutgoing at h
  apply fold_fields_eq (fun a : State × Array (Array Reg) => frame a.1) _ ?_ _ h
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

private def Within (cap : Nat) (reservations : Array (List Reg × List Reg)) (st : State) : Prop :=
  st.alias.size ≤ cap ∧ cap ≤ st.base.nextVreg ∧ st.tryRegs = reservations

private theorem frame_within {cap : Nat} {reservations : Array (List Reg × List Reg)}
    {st next : State} (bound : Within cap reservations st) (same : frame next = frame st) :
    Within cap reservations next := by
  have fresh := congrArg Prod.fst same
  have regs := congrArg (fun x => x.2.1) same
  have aliases := congrArg (fun x => x.2.2) same
  change next.base.nextVreg = st.base.nextVreg at fresh
  change next.tryRegs = st.tryRegs at regs
  change next.alias = st.alias at aliases
  exact ⟨by rw [aliases]; exact bound.1, by rw [fresh]; exact bound.2.1,
    regs.trans bound.2.2⟩

private theorem eval_within {ctx : Ctx} {term : String} {args : List V}
    {st next : State} {out : Option V} {trace : List RuleId} {cap : Nat}
    {reservations : Array (List Reg × List Reg)}
    (payloads : ∀ r ∈ ctx.tryRegs.2, ∃ n, r = .vreg n .int ∧ n < cap)
    (bound : Within cap reservations st)
    (h : Stock.runTerm ctx term args st = .ok (out, next, trace)) :
    Within cap reservations next := by
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
        have alloc := stock_apply_allocationLe ha
        exact ⟨stock_apply_aliasBelow payloads bound.1 ha,
          Nat.le_trans bound.2.1 alloc.1, alloc.2.trans bound.2.2⟩

private theorem slot_payloads {cap : Nat} {reservations : Array (List Reg × List Reg)}
    (bound : ∀ (i : Nat) (rs : List Reg × List Reg), reservations[i]? = some rs → ∀ r ∈ rs.1 ++ rs.2,
      ∃ n, r = .vreg n .int ∧ n < cap) (i : Nat) :
    ∀ r ∈ reservations[i]!.2, ∃ n, r = .vreg n .int ∧ n < cap := by
  intro r mem
  cases lookup : reservations[i]? with
  | none =>
    simp only [getElem!_def, lookup] at mem
    change r ∈ ([] : List Reg) at mem
    cases mem
  | some rs =>
    simp only [getElem!_def, lookup] at mem
    exact bound i rs lookup r (List.mem_append_right _ mem)

private theorem branch_within {ctx : Ctx} {f : Clif.Function} {t : Clif.Terminator}
    {bi ti : Nat} {targets : Array Nat} {st : State} {output : BranchEmission} {cap : Nat}
    {reservations : Array (List Reg × List Reg)}
    (payloads : ∀ r ∈ ctx.tryRegs.2, ∃ n, r = .vreg n .int ∧ n < cap)
    (bound : Within cap reservations st)
    (h : emitBranch ctx f t bi ti targets st = .ok output) :
    Within cap reservations output.state := by
  unfold emitBranch at h
  dsimp only at h
  let before := { st with current := some ti, color := none, base.emitted := #[] }
  have initial : Within cap reservations before := frame_within bound rfl
  change ((do
    let (out, next, fired) ← Stock.runTerm ctx "lower_branch" [.inst ti, .labels targets.toList] before
    if out.isNone then throw s!"no lowering rule for terminator {repr t}"
    let code ← branchCode f t targets next.base.emitted
    pure ⟨next, code, ⟨bi, ti, .emitted, before, next, [], fired, code⟩, fired⟩) : Except String BranchEmission) = .ok output at h
  cases root : Stock.runTerm ctx "lower_branch" [.inst ti, .labels targets.toList] before with
  | error e => simp only [root, bind, Except.bind] at h; cases h
  | ok result =>
    rcases result with ⟨out, next, fired⟩
    simp only [root, bind, Except.bind] at h
    split at h
    · cases h
    · cases code : branchCode f t targets next.base.emitted with
      | error e => simp only [code] at h; cases h
      | ok instructions =>
        simp only [code, pure, Except.pure] at h
        cases h
        exact eval_within payloads initial root

private theorem block_within {ctx : Ctx} {order : Order} {f : Clif.Function} {b : Clif.Block}
    {bi start stop : Nat} {data : V} {targets : Array Nat} {st : State}
    {output : LoweredBlockCore} {cap : Nat} {reservations : Array (List Reg × List Reg)}
    (mapped : ∀ x r, ctx.valueReg? x = some r → ∃ n, r = .vreg n .int ∧ n < cap)
    (reserved : ∀ (i : Nat) (rs : List Reg × List Reg), reservations[i]? = some rs → ∀ r ∈ rs.1 ++ rs.2,
      ∃ n, r = .vreg n .int ∧ n < cap)
    (bound : Within cap reservations st)
    (h : lowerBlockCore ctx order f b bi start stop data targets st = .ok output) :
    Within cap reservations output.state ∧
      (∀ r ∈ output.scan.output.records, cap ≤ r.input.base.nextVreg) := by
  let ti := stop - 1
  let termCtx := { ctx with
    insts := ctx.insts.set! ti ⟨data, [], [], none⟩
    tryRegs := st.tryRegs[ti]! }
  let branch : Bool := match b.term with | .ret .. | .trap .. | .returnCall .. => false | _ => true
  let branchCall : Except String (Option BranchEmission) :=
    if branch then some <$> emitBranch termCtx f b.term bi ti targets st else pure none
  have payloads : ∀ r ∈ termCtx.tryRegs.2, ∃ n, r = .vreg n .int ∧ n < cap := by
    change ∀ r ∈ st.tryRegs[ti]!.2, _
    rw [bound.2.2]
    exact slot_payloads reserved ti
  have mapping : ∀ x r, termCtx.valueReg? x = some r → ∃ n, r = .vreg n .int ∧ n < cap := mapped
  have branch_keeps {result : Option BranchEmission} (call : branchCall = .ok result) :
      Within cap reservations (result.map (·.state) |>.getD st) := by
    unfold branchCall at call
    split at call
    · cases emitted : emitBranch termCtx f b.term bi ti targets st with
      | error e => simp only [emitted, Functor.map, Except.map] at call; cases call
      | ok e =>
        simp only [emitted, Functor.map, Except.map] at call
        cases call
        exact branch_within payloads bound emitted
    · cases call; exact bound
  have normal : lowerBlockCore ctx order f b bi start stop data targets st = ((do
    let br ← branchCall
    let edge ← collectOutgoing ctx order bi targets (br.map (·.state) |>.getD st)
    let next := edge.1
    let outgoing := edge.2
    let beforeScan := { next with color := some next.endColor[bi]! }
    let indices := ((Array.range (stop - start)).map (start + ·)).reverse.toList
    let bodyScan ← scanBlock termCtx bi ti branch indices beforeScan
    pure ⟨bodyScan.state, bodyScan.code ++ (br.map (·.code) |>.getD #[]), outgoing,
      br, ⟨termCtx, bi, ti, branch, indices, beforeScan, bodyScan⟩⟩) : Except String LoweredBlockCore) := by
    unfold lowerBlockCore
    dsimp only [branchCall, branch, termCtx, ti]
    split <;> simp_all only [branch, termCtx, ti] <;> rfl
  rw [normal] at h
  cases call : branchCall with
  | error e => simp only [call, bind, Except.bind] at h; cases h
  | ok br =>
    simp only [call, bind, Except.bind] at h
    cases edges : collectOutgoing ctx order bi targets (br.map (·.state) |>.getD st) with
    | error e => simp only [edges] at h; cases h
    | ok result =>
      rcases result with ⟨next, outgoing⟩
      simp only [edges] at h
      have edgeBound := frame_within (branch_keeps call) (outgoing_frame edges)
      let before := { next with color := some next.endColor[bi]! }
      let indices := ((Array.range (stop - start)).map (start + ·)).reverse.toList
      have beforeBound : Within cap reservations before := frame_within edgeBound rfl
      change (scanBlock termCtx bi ti branch indices before >>= fun bodyScan =>
        pure (⟨bodyScan.state, bodyScan.code ++ (br.map (·.code) |>.getD #[]), outgoing,
          br, ⟨termCtx, bi, ti, branch, indices, before, bodyScan⟩⟩ : LoweredBlockCore)) = .ok output at h
      cases scan : scanBlock termCtx bi ti branch indices before with
      | error e => simp only [scan, bind, Except.bind] at h; cases h
      | ok body =>
        simp only [scan, bind, Except.bind, pure, Except.pure] at h
        cases h
        have alloc := stock_scanBlock_allocationLe scan
        exact ⟨⟨stock_scanBlock_aliasBelow payloads mapping beforeBound.1 scan,
          Nat.le_trans beforeBound.2.1 alloc.1, alloc.2.trans beforeBound.2.2⟩,
          stock_scanBlock_frontiers beforeBound.2.1 scan⟩

private def ScanFrontiers (cap : Nat) (scans : Array ScanEvent) : Prop :=
  ∀ event ∈ scans.toList, cap ≤ event.input.base.nextVreg

private def recordStep (ctx : Ctx) (bi ti : Nat) (branch : Bool)
    (acc : Array Step × Array ScanEvent × Array RuleId) (record : ScanRecord) :=
  let scans := acc.2.1.push ⟨ctx, bi, record.inst, ti, branch, record.input, record.output⟩
  match record.output.step with
  | some step => (acc.1.push step, scans, acc.2.2 ++ step.rules.toArray)
  | none => (acc.1, scans, acc.2.2)

private theorem recordStep_scans (ctx : Ctx) (bi ti : Nat) (branch : Bool)
    (acc : Array Step × Array ScanEvent × Array RuleId) (record : ScanRecord) :
    (recordStep ctx bi ti branch acc record).2.1 =
      acc.2.1.push ⟨ctx, bi, record.inst, ti, branch, record.input, record.output⟩ := by
  unfold recordStep
  split <;> rfl

private theorem record_fold {cap : Nat} (ctx : Ctx) (bi ti : Nat) (branch : Bool)
    (records : List ScanRecord) (acc : Array Step × Array ScanEvent × Array RuleId)
    (old : ScanFrontiers cap acc.2.1)
    (inputs : ∀ r ∈ records, cap ≤ r.input.base.nextVreg) :
    ScanFrontiers cap (records.foldl (recordStep ctx bi ti branch) acc).2.1 := by
  induction records generalizing acc with
  | nil => exact old
  | cons record records ih =>
    apply ih _ ?_ (fun r mem => inputs r (by simp [mem]))
    rw [recordStep_scans]
    intro event mem
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at mem
    rcases mem with mem | rfl
    · exact old event mem
    · exact inputs record (by simp)

private theorem core_frontiers {cap : Nat} {input : DriverState} {lowered : LoweredBlockCore}
    {bi stop : Nat} (old : ScanFrontiers cap input.scans)
    (inputs : ∀ r ∈ lowered.scan.output.records, cap ≤ r.input.base.nextVreg) :
    ScanFrontiers cap (recordCore input lowered bi stop).scans := by
  unfold recordCore
  dsimp only
  split <;> exact record_fold _ _ _ _ _ _ old inputs

private theorem node_within {ctx : Ctx} {ranges : Array (Nat × Nat)} {order : Order}
    {f : Clif.Function} {paramBytes : List Nat} {label : Nat} {input output : DriverState}
    {cap : Nat} {reservations : Array (List Reg × List Reg)}
    (mapped : ∀ x r, ctx.valueReg? x = some r → ∃ n, r = .vreg n .int ∧ n < cap)
    (reserved : ∀ (i : Nat) (rs : List Reg × List Reg), reservations[i]? = some rs →
      ∀ r ∈ rs.1 ++ rs.2, ∃ n, r = .vreg n .int ∧ n < cap)
    (bound : Within cap reservations input.state)
    (h : lowerNode ctx ranges order f paramBytes label input = .ok output) :
    Within cap reservations output.state := by
  unfold lowerNode at h
  dsimp only at h
  repeat' first
    | (solve | cases h)
    | (solve | cases h; exact frame_within bound (branch_frame (by assumption)))
    | (solve | cases h; exact (block_within mapped reserved bound (by assumption)).1)
    | simp only [bind, Except.bind, pure, Except.pure] at h
    | split at h
private theorem node_frontiers {ctx : Ctx} {ranges : Array (Nat × Nat)} {order : Order}
    {f : Clif.Function} {paramBytes : List Nat} {label : Nat} {input output : DriverState}
    {cap : Nat} {reservations : Array (List Reg × List Reg)}
    (mapped : ∀ x r, ctx.valueReg? x = some r → ∃ n, r = .vreg n .int ∧ n < cap)
    (reserved : ∀ (i : Nat) (rs : List Reg × List Reg), reservations[i]? = some rs →
      ∀ r ∈ rs.1 ++ rs.2, ∃ n, r = .vreg n .int ∧ n < cap)
    (bound : Within cap reservations input.state) (old : ScanFrontiers cap input.scans)
    (h : lowerNode ctx ranges order f paramBytes label input = .ok output) :
    ScanFrontiers cap output.scans := by
  unfold lowerNode at h
  dsimp only at h
  repeat' first
    | (solve | cases h)
    | (solve | cases h; exact old)
    | (solve | cases h; apply core_frontiers old; exact (block_within mapped reserved bound (by assumption)).2)
    | simp only [bind, Except.bind, pure, Except.pure] at h
    | split at h

private theorem fold_bound {α β : Type} (P : α → Prop)
    (step : α → β → Except String α)
    (keeps : ∀ a b next, P a → step a b = .ok next → P next)
    (xs : List β) {a next : α} (bound : P a)
    (h : xs.foldlM step a = .ok next) : P next := by
  induction xs generalizing a with
  | nil => cases h; exact bound
  | cons x xs ih =>
    rw [List.foldlM_cons] at h
    cases call : step a x with
    | error e => simp only [call, bind, Except.bind] at h; cases h
    | ok middle =>
      simp only [call, bind, Except.bind] at h
      exact ih (keeps a x middle bound call) h


private theorem initial_within {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {st : State}
    (h : Stock.buildCtx f = .ok (ctx, ranges, st)) : Within st.base.nextVreg st.tryRegs st := by
  obtain ⟨original, st0, requests, _, _, result⟩ := buildCtx_allocation h
  have state := congrArg (fun p : Ctx × Array (Nat × Nat) × State => p.2.2) result
  change st = _ at state
  rw [state]
  exact ⟨Nat.zero_le _, Nat.le_refl _, rfl⟩

private theorem initial_maps {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {st : State}
    (h : Stock.buildCtx f = .ok (ctx, ranges, st)) :
    ∀ x r, ctx.valueReg? x = some r → ∃ n, r = .vreg n .int ∧ n < st.base.nextVreg := by
  have allocated := buildCtx_allocated h
  intro x r map
  obtain ⟨n, reg, _⟩ := allocated.2.2.1 x r map
  exact ⟨n, reg, allocated.1 x n (by rwa [← reg])⟩

private theorem traversal_initial {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)}
    {order : Order} {params : List Nat} {labels : List Nat} {input output : DriverState}
    (build : Stock.buildCtx f = .ok (ctx, ranges, input.state))
    (h : labels.foldlM (fun input label => lowerNode ctx ranges order f params label input) input =
      .ok output) : Within input.state.base.nextVreg input.state.tryRegs output.state := by
  apply fold_bound (fun d : DriverState => Within input.state.base.nextVreg input.state.tryRegs d.state)
    _ ?_ labels (initial_within build) h
  intro a label next bound step
  exact node_within (initial_maps build) (buildCtx_reservedBelow build) bound step

private theorem traversal_frontiers {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)}
    {order : Order} {params : List Nat} {labels : List Nat} {input output : DriverState}
    (build : Stock.buildCtx f = .ok (ctx, ranges, input.state))
    (old : ScanFrontiers input.state.base.nextVreg input.scans)
    (h : labels.foldlM (fun input label => lowerNode ctx ranges order f params label input) input =
      .ok output) : ScanFrontiers input.state.base.nextVreg output.scans := by
  have invariant := fold_bound
    (fun d : DriverState => Within input.state.base.nextVreg input.state.tryRegs d.state ∧
      ScanFrontiers input.state.base.nextVreg d.scans)
    (fun d label => lowerNode ctx ranges order f params label d)
    (fun a label next bound step =>
      ⟨node_within (initial_maps build) (buildCtx_reservedBelow build) bound.1 step,
        node_frontiers (initial_maps build) (buildCtx_reservedBelow build) bound.1 bound.2 step⟩)
    labels ⟨initial_within build, old⟩ h
  exact invariant.2

/-- Every successful whole stock driver bounds its final aliases by the initial
allocation frontier, grows the fresh frontier, and retains exception reservations.
All premises are facts of the actual run; no additional acceptance check is needed. -/
theorem stock_lower_allocationBounds {f : Clif.Function} {result : Result}
    (h : Stock.lower f = .ok result) :
    result.final.alias.size ≤ result.initial.base.nextVreg ∧
      result.initial.base.nextVreg ≤ result.final.base.nextVreg ∧
      result.final.tryRegs = result.initial.tryRegs := by
  unfold Stock.lower at h
  dsimp only at h
  repeat' first
    | (solve | cases h)
    | (solve | cases h; apply traversal_initial <;> assumption)
    | simp only [bind, Except.bind, pure, Except.pure] at h
    | split at h
  cases h
  rename_i _ _ params _ _ _ _ _ source build _ order _ _ driver run
  exact traversal_initial (output := driver) build run

/-- Final aliases fit below every actual recorded instruction-scan input's
fresh frontier, even when aliases are installed later in reverse lowering. -/
theorem stock_lower_scanAliasBounds {f : Clif.Function} {result : Result}
    (h : Stock.lower f = .ok result) :
    ∀ event ∈ result.scans.toList, result.final.alias.size ≤ event.input.base.nextVreg := by
  have final := stock_lower_allocationBounds h
  unfold Stock.lower at h
  dsimp only at h
  repeat' first
    | (solve | cases h)
    | simp only [bind, Except.bind, pure, Except.pure] at h
    | split at h
  cases h
  rename_i _ _ params _ _ _ _ _ source build _ order _ _ driver run
  have frontier := traversal_frontiers (output := driver) build (by simp [ScanFrontiers]) run
  intro event mem
  exact Nat.le_trans final.1 (frontier event mem)

private def emptyFunction : Clif.Function := { name := "allocation_bounds", sig := {}, blocks := [] }
private def emptySource : Ctx := {
  func := emptyFunction
  insts := #[]
  valTy := #[]
  valDef := #[]
  valReg := #[]
  slotOff := [] }
private def emptyBuilt := finishCtx emptySource #[] (Allocation.initial 0 0)
private def emptyResult : Result := {
  ctx := emptyBuilt.1
  initial := emptyBuilt.2.2
  final := emptyBuilt.2.2
  order := ⟨#[], #[]⟩
  code := {
    name := emptyFunction.name
    blocks := #[]
    classes := emptyBuilt.2.2.base.classes
    slotBytes := 0
    outgoing := 0
    rulesFired := #[] }
  edgeArgs := #[]
  schedule := #[] }

/-- A successful actual whole-driver run witnesses the unconditional output
bounds. Nonempty allocation and scan transitions are separately witnessed in
StockAliasBounds, StockScanBounds and StockAllocationFlow. -/
theorem stock_lower_allocationBounds_witness :
    Stock.lower emptyFunction = .ok emptyResult ∧
      emptyResult.initial.base.nextVreg = 192 ∧
      emptyResult.final.alias.size ≤ emptyResult.initial.base.nextVreg ∧
      emptyResult.initial.base.nextVreg ≤ emptyResult.final.base.nextVreg ∧
      emptyResult.final.tryRegs = emptyResult.initial.tryRegs := by
  have run : Stock.lower emptyFunction = .ok emptyResult := by cbv
  exact ⟨run, rfl, stock_lower_allocationBounds run⟩

/-- A successful actual whole-driver run inhabits the theorem's sole run
premise. The nonempty per-record witness is stock_scanBlock_frontiers_witness. -/
theorem stock_lower_scanAliasBounds_witness :
    Stock.lower emptyFunction = .ok emptyResult ∧
      (∀ event ∈ emptyResult.scans.toList,
        emptyResult.final.alias.size ≤ event.input.base.nextVreg) := by
  have run := stock_lower_allocationBounds_witness.1
  exact ⟨run, stock_lower_scanAliasBounds run⟩

end Backend.Stock.Proof
