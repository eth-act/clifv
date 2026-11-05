import FV.Backend.Proof.StockRecordIntervals
import FV.Backend.Proof.StockOutgoingFrame

/-! The branch interval of every retained block scan, with the label of its node (#140, CB-14b).

A copy of `StockBranchIntervals` (CB-12b) whose traversal invariant also records the label of the
actual traversal core: the node at that label is the original block of the scan, and the targets
of the core are the successors of that label (`stock_lower_labelled_branch_gap`). With the
uniqueness of original labels, the traversal core of a retained block scan has the targets of
every node of its block. So a branch emission whose allocation is fixed only for some targets,
like a `br_table` of at most 4096 targets, still has the branch interval of
`stock_lower_available_alias_outside_branch`
(`stock_lower_available_alias_outside_labelled_branch`). -/

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitBranch scanBlock

private theorem intervals_mono {lo hi a b : Nat} {records : List ScanRecord}
    (h : RecordIntervals a b records) (left : lo ≤ a) (right : b ≤ hi) : RecordIntervals lo hi records := by
  refine ⟨?_, h.ordered⟩
  intro r member
  have bound := h.bounds r member
  exact ⟨Nat.le_trans left bound.1, bound.2.1, Nat.le_trans bound.2.2 right⟩

private theorem intervals_append {lo mid hi : Nat} {first second : List ScanRecord}
    (left : lo ≤ mid) (right : mid ≤ hi)
    (a : RecordIntervals lo mid first) (b : RecordIntervals mid hi second) :
    RecordIntervals lo hi (first ++ second) := by
  refine ⟨?_, List.pairwise_append.mpr ⟨a.ordered, b.ordered, ?_⟩⟩
  · intro r member
    rcases List.mem_append.mp member with fromFirst | fromSecond
    · exact (intervals_mono a (Nat.le_refl lo) right).bounds r fromFirst
    · exact (intervals_mono b left (Nat.le_refl hi)).bounds r fromSecond
  · intro r member s other
    exact Nat.le_trans (a.bounds r member).2.2 (b.bounds s other).1

private theorem scan_intervals {ctx : Ctx} {block ti : Nat} {branch : Bool}
    {indices : List Nat} {input : State} {output : BlockScan}
    (run : scanBlock ctx block ti branch indices input = .ok output) :
    input.base.nextVreg ≤ output.state.base.nextVreg ∧
      RecordIntervals input.base.nextVreg output.state.base.nextVreg output.records := by
  unfold scanBlock at run
  have cert := runScans_spec run
  clear run
  induction cert with
  | nil st => exact ⟨Nat.le_refl _, ⟨by simp, .nil⟩⟩
  | @cons i indices input scan tail head rest ih =>
    have own := (stock_scan_allocationLe head).1
    refine ⟨Nat.le_trans own ih.1, ⟨?_, ?_⟩⟩
    · intro r member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨Nat.le_refl _, own, ih.1⟩
      · exact (intervals_mono ih.2 own (Nat.le_refl _)).bounds r member
    · exact List.Pairwise.cons
        (fun r member => (ih.2.bounds r member).1) ih.2.ordered

private theorem forIn_frontier {α β : Type} (field : α → Nat)
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

private theorem arg_frontier (ctx : Ctx) (rets pays : List Reg) (index nh : Nat)
    (arg : Clif.TryArg) (a b : State × Array Reg)
    (h : argStep ctx rets pays index nh arg a = .ok (.yield b)) :
    b.1.base.nextVreg = a.1.base.nextVreg := by
  cases arg <;> unfold argStep at h
  all_goals repeat' first | (solve | cases h <;> rfl) | split at h

private theorem arg_no_break (ctx : Ctx) (rets pays : List Reg) (index nh : Nat)
    (arg : Clif.TryArg) (a b : State × Array Reg) :
    argStep ctx rets pays index nh arg a ≠ .ok (.done b) := by
  intro h
  cases arg <;> unfold argStep at h
  all_goals repeat' first | (solve | cases h) | split at h

private theorem branch_frontier {ctx : Ctx} {st next : State} {block index : Nat}
    {args : Array Reg} (h : branchArgs ctx st block index = .ok (args, next)) :
    next.base.nextVreg = st.base.nextVreg := by
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
          exact forIn_frontier (fun a : State × Array Reg => a.1.base.nextVreg) _
            (arg_frontier ctx reservations.1 reservations.2 index nh)
            (arg_no_break ctx reservations.1 reservations.2 index nh) values loop
    · cases h
  · cases h

private theorem named_alloc {ctx : Ctx} {term : String} {args : List V}
    {st next : State} {out : Option V} {trace : List RuleId}
    (h : Stock.runTerm ctx term args st = .ok (out, next, trace)) :
    AllocationLe st next := by
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
        exact stock_apply_allocationLe ha

private theorem branch_mono {ctx : Ctx} {f : Clif.Function} {t : Clif.Terminator}
    {bi ti : Nat} {targets : Array Nat} {input : State} {output : BranchEmission}
    (run : emitBranch ctx f t bi ti targets input = .ok output) :
    input.base.nextVreg ≤ output.state.base.nextVreg := by
  unfold emitBranch at run
  dsimp only at run
  let before := { input with current := some ti, color := none, base.emitted := #[] }
  change ((do
    let (out, next, fired) ← Stock.runTerm ctx "lower_branch" [.inst ti, .labels targets.toList] before
    if out.isNone then throw s!"no lowering rule for terminator {repr t}"
    let code ← branchCode f t targets next.base.emitted
    pure ⟨next, code, ⟨bi, ti, .emitted, before, next, [], fired, code⟩, fired⟩) : Except String BranchEmission) = .ok output at run
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
        exact (named_alloc root).1

/-- The actual core: the branch emission and the outgoing arguments end at the scan input, and the
body records lie between the scan input and the core output. -/
private theorem core_gap {f : Clif.Function} {ctx : Ctx}
    {second : Clif.Block} {bi start stop : Nat}
    {order : Order} {data : V} {targets : Array Nat} {input : State} {output : LoweredBlockCore}
    (run : lowerBlockCore ctx order f second bi start stop data targets input = .ok output) :
    input.base.nextVreg ≤ output.scan.input.base.nextVreg ∧
      output.scan.input.base.nextVreg ≤ output.state.base.nextVreg ∧
      RecordIntervals output.scan.input.base.nextVreg output.state.base.nextVreg output.scan.output.records := by
  let ti := stop - 1
  let selected := { Driver.termCtx ctx ti data with tryRegs := input.tryRegs[ti]! }
  let branch : Bool := match second.term with | .ret .. | .trap .. | .returnCall .. => false | _ => true
  let branchCall : Except String (Option BranchEmission) :=
    if branch then some <$> emitBranch selected f second.term bi ti targets input else pure none
  have branchKeeps {br : Option BranchEmission} (call : branchCall = .ok br) :
      input.base.nextVreg ≤ ((br.map (·.state)).getD input).base.nextVreg := by
    unfold branchCall at call
    split at call
    · cases emitted : emitBranch selected f second.term bi ti targets input with
      | error e => simp only [emitted, Functor.map, Except.map] at call; cases call
      | ok e =>
        simp only [emitted, Functor.map, Except.map] at call
        cases call
        exact branch_mono emitted
    · cases call; exact Nat.le_refl _
  have normal : lowerBlockCore ctx order f second bi start stop data targets input = (do
      let br ← branchCall
      let (next, outgoing) ← collectOutgoing ctx order bi targets (br.map (·.state) |>.getD input)
      let before := { next with color := some next.endColor[bi]! }
      let indices := ((Array.range (stop - start)).map (start + ·)).reverse.toList
      let body ← scanBlock selected bi ti branch indices before
      pure ⟨body.state, body.code ++ (br.map (·.code) |>.getD #[]), outgoing,
        br, ⟨selected, bi, ti, branch, indices, before, body⟩⟩) := by
    unfold lowerBlockCore
    dsimp only [branchCall, branch, selected, ti, Driver.termCtx]
    split <;> simp_all only [branch, selected, ti] <;> rfl
  rw [normal] at run
  cases call : branchCall with
  | error e => simp only [call, bind, Except.bind] at run; cases run
  | ok br =>
    simp only [call, bind, Except.bind] at run
    cases edges : collectOutgoing ctx order bi targets (br.map (·.state) |>.getD input) with
    | error e => simp only [edges] at run; cases run
    | ok pair =>
      rcases pair with ⟨next, outgoing⟩
      simp only [edges] at run
      let before := { next with color := some next.endColor[bi]! }
      let indices := ((Array.range (stop - start)).map (start + ·)).reverse.toList
      have keeps : input.base.nextVreg ≤ before.base.nextVreg := by
        have frontier := congrArg LState.nextVreg (outgoing_base_extent edges).1
        change next.base.nextVreg = ((br.map (·.state)).getD input).base.nextVreg at frontier
        change input.base.nextVreg ≤ next.base.nextVreg
        rw [frontier]
        exact branchKeeps call
      change (scanBlock selected bi ti branch indices before >>= fun body =>
        pure (⟨body.state, body.code ++ (br.map (·.code) |>.getD #[]), outgoing,
          br, ⟨selected, bi, ti, branch, indices, before, body⟩⟩ : LoweredBlockCore)) = .ok output at run
      cases scan : scanBlock selected bi ti branch indices before with
      | error e => simp only [scan, bind, Except.bind] at run; cases run
      | ok body =>
        simp only [scan, bind, Except.bind, pure, Except.pure] at run
        cases run
        have intervals := scan_intervals scan
        exact ⟨keeps, intervals.1, intervals.2⟩

/-- The traversal invariant: the retained records are ordered and bounded, and every retained
block scan has an actual core whose branch interval no retained record meets. -/
private def Gaps (ctx : Ctx) (order : Order) (f : Clif.Function) (cap : Nat) (d : DriverState) : Prop :=
  cap ≤ d.state.base.nextVreg ∧
  RecordIntervals cap d.state.base.nextVreg (retainedRecords d.blockScans) ∧
  ∀ event ∈ d.blockScans.toList, ∃ (label start stop : Nat) (data : V)
      (input : State) (core : LoweredBlockCore),
    order.nodes[label]? = some (.original event.block) ∧
    lowerBlockCore ctx order f f.blocks[event.block]! event.block start stop data order.successors[label]! input
      = .ok core ∧
    core.scan = event ∧ cap ≤ input.base.nextVreg ∧ input.base.nextVreg ≤ event.input.base.nextVreg ∧
    event.input.base.nextVreg ≤ d.state.base.nextVreg ∧
    ∀ r ∈ retainedRecords d.blockScans, r.output.state.base.nextVreg ≤ input.base.nextVreg ∨
      event.input.base.nextVreg ≤ r.input.base.nextVreg

private theorem node_gaps {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)}
    {order : Order} {params : List Nat} {label : Nat} {input output : DriverState}
    {cap : Nat} (old : Gaps ctx order f cap input) (bound : label < order.nodes.size)
    (run : lowerNode ctx ranges order f params label input = .ok output) :
    Gaps ctx order f cap output := by
  cases node : order.nodes[label]! with
  | edge pred k target =>
    unfold lowerNode at run
    simp only [node] at run
    cases args : branchArgs ctx input.state pred k with
    | error e => simp only [args, bind, Except.bind] at run; cases run
    | ok pair =>
      rcases pair with ⟨args, next⟩
      simp only [args, bind, Except.bind, pure, Except.pure] at run
      cases run
      have frontier := branch_frontier args
      refine ⟨?_, ?_, ?_⟩
      · change cap ≤ next.base.nextVreg
        rw [frontier]; exact old.1
      · change RecordIntervals cap next.base.nextVreg (retainedRecords input.blockScans)
        rw [frontier]; exact old.2.1
      · intro event member
        obtain ⟨label', start, stop, data, coreInput, core, labelled, coreRun, scanEq, capped, below, within,
          disjoint⟩ := old.2.2 event member
        refine ⟨label', start, stop, data, coreInput, core, labelled, coreRun, scanEq, capped, below, ?_, disjoint⟩
        change event.input.base.nextVreg ≤ next.base.nextVreg
        rw [frontier]; exact within
  | original bi =>
    let b := f.blocks[bi]!
    let start := ranges[bi]!.1
    let stop := ranges[bi]!.2
    let fetchData : Except String V := match b.term with
      | .tryCall .. | .tryCallIndirect .. => tryCallData f b.term
      | _ => termData (abiTerm f b.term)
    let reject : Bool := (match b.term with | .ret .. => true | _ => false) &&
      (sretRet f).isEmpty && (sigRets f.sig != f.sig.returns)
    have normal : lowerNode ctx ranges order f params label input = (do
        let data ← fetchData
        if reject then throw "sret parameter is not an entry-block parameter"
        let lowered ← lowerBlockCore ctx order f b bi start stop data order.successors[label]! input.state
        let assembled ← assembleOriginalBlock ctx f b bi label order.successors[label]!
          lowered.outgoing params lowered.state.uses lowered.code
        pure { recordCore input lowered bi stop with
          blocks := input.blocks.set! label assembled,
          edgeArgs := input.edgeArgs.set! label lowered.outgoing }) := by
      unfold lowerNode
      simp only [node]
      dsimp only [fetchData, reject, b, start, stop]
      split <;> simp_all only [reject] <;> rfl
    rw [normal] at run
    cases dataRun : fetchData with
    | error e => simp only [dataRun, bind, Except.bind] at run; cases run
    | ok data =>
      simp only [dataRun, bind, Except.bind] at run
      split at run
      · cases run
      · cases core : lowerBlockCore ctx order f b bi start stop data order.successors[label]! input.state with
        | error e => simp only [core] at run; cases run
        | ok lowered =>
          simp only [core] at run
          cases assembled : assembleOriginalBlock ctx f b bi label order.successors[label]!
              lowered.outgoing params lowered.state.uses lowered.code with
          | error e => simp only [assembled] at run; cases run
          | ok block =>
            simp only [assembled, pure, Except.pure] at run
            cases run
            obtain ⟨keeps, scanMono, intervals⟩ := core_gap core
            have atBlock : lowered.scan.block = bi := (stock_lowerBlockCore_scanOrigin core).2.2.1
            have records : retainedRecords (input.blockScans.push lowered.scan) =
                retainedRecords input.blockScans ++ lowered.scan.output.records := by
              rw [retainedRecords, retainedRecords, Array.toList_push, List.flatMap_append,
                List.flatMap_cons, List.flatMap_nil, List.append_nil]
            have grows : input.state.base.nextVreg ≤ lowered.state.base.nextVreg := Nat.le_trans keeps scanMono
            refine ⟨Nat.le_trans old.1 grows, ?_, ?_⟩
            · change RecordIntervals cap lowered.state.base.nextVreg
                (retainedRecords (input.blockScans.push lowered.scan))
              rw [records]
              exact intervals_append old.1 grows old.2.1 (intervals_mono intervals keeps (Nat.le_refl _))
            · intro event member
              change event ∈ (input.blockScans.push lowered.scan).toList at member
              change ∃ (label' start stop : Nat) (data : V) (coreInput : State)
                  (core : LoweredBlockCore),
                order.nodes[label']? = some (.original event.block) ∧
                lowerBlockCore ctx order f f.blocks[event.block]! event.block start stop data order.successors[label']!
                  coreInput = .ok core ∧
                core.scan = event ∧ cap ≤ coreInput.base.nextVreg ∧
                coreInput.base.nextVreg ≤ event.input.base.nextVreg ∧
                event.input.base.nextVreg ≤ lowered.state.base.nextVreg ∧
                ∀ r ∈ retainedRecords (input.blockScans.push lowered.scan),
                  r.output.state.base.nextVreg ≤ coreInput.base.nextVreg ∨
                    event.input.base.nextVreg ≤ r.input.base.nextVreg
              rw [records]
              rw [Array.toList_push] at member
              rcases List.mem_append.mp member with earlier | current
              · obtain ⟨label', start', stop', data', coreInput, core', labelled, coreRun, scanEq, capped, below,
                  within, disjoint⟩ := old.2.2 event earlier
                refine ⟨label', start', stop', data', coreInput, core', labelled, coreRun, scanEq, capped, below,
                  Nat.le_trans within grows, ?_⟩
                intro r recorded
                rcases List.mem_append.mp recorded with oldRecord | newRecord
                · exact disjoint r oldRecord
                · exact Or.inr (Nat.le_trans within (Nat.le_trans keeps (intervals.bounds r newRecord).1))
              · rw [List.mem_singleton] at current
                subst current
                refine ⟨label, start, stop, data, input.state, lowered, ?_, ?_, rfl, old.1, keeps,
                  scanMono, ?_⟩
                · rw [atBlock,Array.getElem?_eq_getElem bound]
                  simp only [getElem!_def,Array.getElem?_eq_getElem bound,Option.getD_some] at node
                  rw [node]
                · rw [atBlock]; exact core
                · intro r recorded
                  rcases List.mem_append.mp recorded with oldRecord | newRecord
                  · exact Or.inl (old.2.1.bounds r oldRecord).2.2
                  · exact Or.inr (intervals.bounds r newRecord).1

private theorem traversal_gaps {ctx : Ctx} {ranges : Array (Nat × Nat)}
    {order : Order} {f : Clif.Function} {params labels : List Nat} {input output : DriverState}
    {cap : Nat} (old : Gaps ctx order f cap input) (bounded : ∀ label ∈ labels, label < order.nodes.size)
    (run : labels.foldlM (fun d label => lowerNode ctx ranges order f params label d) input = .ok output) :
    Gaps ctx order f cap output := by
  induction labels generalizing input with
  | nil => cases run; exact old
  | cons label labels ih =>
    rw [List.foldlM_cons] at run
    cases call : lowerNode ctx ranges order f params label input with
    | error e => simp only [call, bind, Except.bind] at run; cases run
    | ok next =>
      simp only [call, bind, Except.bind] at run
      exact ih (node_gaps old (bounded label (List.mem_cons_self ..)) call)
        (fun label' member => bounded label' (List.mem_cons_of_mem _ member)) run

/-- **The branch interval of every retained block scan.** The actual traversal core of a retained
block scan starts at or above the initial frontier, and every retained record, of any block, ends
at or below the core input or starts at or above the scan input. The branch emission of the block
allocates in this gap, before the outgoing arguments and the body scan. -/
theorem stock_lower_labelled_branch_gap {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent} (member : event ∈ result.blockScans.toList) :
    ∃ (label start stop : Nat) (data : V) (input : State) (core : LoweredBlockCore),
      result.order.nodes[label]? = some (.original event.block) ∧
      lowerBlockCore result.ctx result.order f f.blocks[event.block]! event.block start stop data
        result.order.successors[label]! input = .ok core ∧
      core.scan = event ∧ result.initial.base.nextVreg ≤ input.base.nextVreg ∧
      input.base.nextVreg ≤ event.input.base.nextVreg ∧
      ∀ r ∈ retainedRecords result.blockScans, r.output.state.base.nextVreg ≤ input.base.nextVreg ∨
        event.input.base.nextVreg ≤ r.input.base.nextVreg := by
  unfold Stock.lower at run
  dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind, Except.bind, pure, Except.pure] at run
    | split at run
  cases run
  rename_i _ built hbuild _ order horder _ driver hdriver
  have initial : Gaps built.1 order f built.2.2.base.nextVreg
      {state := built.2.2, blocks := Array.replicate order.nodes.size default,
        edgeArgs := Array.replicate order.nodes.size #[], schedule := #[],
        scans := #[], blockScans := #[], rules := #[]} :=
    ⟨Nat.le_refl _, ⟨by simp [retainedRecords], .nil⟩, by simp⟩
  have bounded : ∀ label ∈ (Array.range order.nodes.size).reverse.toList, label < order.nodes.size := by
    intro label member
    simpa using member
  obtain ⟨label, start, stop, data, input, core, labelled, coreRun, scanEq, capped, below, _, disjoint⟩ :=
    (traversal_gaps initial bounded hdriver).2.2 event member
  exact ⟨label, start, stop, data, input, core, labelled, coreRun, scanEq, capped, below, disjoint⟩

private theorem entries_iff {a : Array (Option Nat)} {key target : Nat} :
    (key, target) ∈ finalAliasEntries a ↔ (a[key]?).join = some target := by
  constructor
  · intro member
    obtain ⟨n, _, mapped⟩ := List.mem_filterMap.mp member
    cases lookup : (a[n]?).join with
    | none => simp only [lookup, Option.map_none] at mapped; cases mapped
    | some value =>
      simp only [lookup, Option.map_some, Option.some.injEq, Prod.mk.injEq] at mapped
      rcases mapped with ⟨rfl, rfl⟩
      exact lookup
  · intro entry
    have inside : key < a.size := by
      apply Nat.lt_of_not_ge
      intro outside
      rw [Array.getElem?_eq_none outside] at entry
      cases entry
    exact List.mem_filterMap.mpr ⟨key, List.mem_range.mpr inside, by rw [entry]; rfl⟩

private theorem entries_faithful (a : Array (Option Nat)) :
    Faithful (finalAliasEntries a) (fun key => (a[key]?).join) := by
  constructor
  · intro key target entry; exact entries_iff.mpr entry
  · intro key absent target member
    have entry := entries_iff.mp member
    rw [absent] at entry
    cases entry

private theorem resolver_path {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (key : Nat) :
    AliasPath (finalAliasEntries result.final.alias) key (aliasNum result.final.alias key) := by
  obtain ⟨rank, decrease⟩ := stock_lower_alias_wellFounded run scope dominated
  have contains : ∀ p ∈ finalAliasEntries result.final.alias,
      p.1 ∈ List.range result.final.alias.size := by
    intro p member
    obtain ⟨key, inside, mapped⟩ := List.mem_filterMap.mp member
    cases lookup : (result.final.alias[key]?).join with
    | none => simp only [lookup, Option.map_none] at mapped; cases mapped
    | some target =>
      simp only [lookup, Option.map_some, Option.some.injEq] at mapped
      subst p
      exact inside
  have count := chainCount_le (finalAliasEntries result.final.alias) rank
    (List.range result.final.alias.size) key
  simp only [List.length_range] at count
  exact (chaseF_end (entries_faithful result.final.alias) decrease contains
    (result.final.alias.size + 1) key (by omega)).1

/-- **The resolved register of an available value is outside the branch interval of every
block.** For every retained block scan, its actual traversal core has an input at or above the
initial frontier, and the resolved register of any value available at any source point is below
the core input or at or above the scan input. -/
theorem stock_lower_available_alias_outside_labelled_branch {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (member : event ∈ result.blockScans.toList) :
    ∃ (label start stop : Nat) (data : V) (input : State) (core : LoweredBlockCore),
      result.order.nodes[label]? = some (.original event.block) ∧
      lowerBlockCore result.ctx result.order f f.blocks[event.block]! event.block start stop data
        result.order.successors[label]! input = .ok core ∧
      core.scan = event ∧ result.initial.base.nextVreg ≤ input.base.nextVreg ∧
      input.base.nextVreg ≤ event.input.base.nextVreg ∧
      ∀ {bi j x key : Nat},x ∈ availOf f (availIn f result.ctx) bi j →
        result.ctx.valueReg? x = some (.vreg key .int) →
        aliasNum result.final.alias key < input.base.nextVreg ∨
          event.input.base.nextVreg ≤ aliasNum result.final.alias key := by
  obtain ⟨label, start, stop, data, input, core, labelled, coreRun, scanEq, capped, below, disjoint⟩ :=
    stock_lower_labelled_branch_gap run member
  refine ⟨label, start, stop, data, input, core, labelled, coreRun, scanEq, capped, below, ?_⟩
  intro bi j x key available mapped
  by_cases low : aliasNum result.final.alias key < result.initial.base.nextVreg
  · exact Or.inl (Nat.lt_of_lt_of_le low capped)
  · have fresh : result.initial.base.nextVreg ≤ aliasNum result.final.alias key := Nat.le_of_not_gt low
    obtain ⟨ownerEvent, producer, info, y, sourceKey, ownerMem, producerMem,
      source, defines, sourceMap, ownerAvailable, lower, upper⟩ :=
      stock_lower_source_path_fresh_origin run scope dominated available mapped
        (resolver_path run scope dominated key) fresh
    rcases disjoint producer (List.mem_flatMap.mpr ⟨ownerEvent, ownerMem, producerMem⟩) with before | after
    · exact Or.inl (Nat.lt_of_lt_of_le upper before)
    · exact Or.inr (Nat.le_trans after lower)

end Backend.Stock.Proof
