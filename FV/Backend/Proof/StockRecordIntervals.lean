import FV.Backend.Proof.StockAliasAvailable

/-! Actual retained record allocation intervals follow the driver traversal. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitBranch scanBlock

/-- Bounds and chronological ordering of actual retained record intervals. -/
structure RecordIntervals (lo hi : Nat) (records : List ScanRecord) : Prop where
  bounds : ∀ r ∈ records, lo ≤ r.input.base.nextVreg ∧
    r.input.base.nextVreg ≤ r.output.state.base.nextVreg ∧ r.output.state.base.nextVreg ≤ hi
  ordered : records.Pairwise (fun r s => r.output.state.base.nextVreg ≤ s.input.base.nextVreg)

private theorem intervals_nil (lo hi : Nat) : RecordIntervals lo hi [] :=
  ⟨by simp, .nil⟩
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
  | nil st => exact ⟨Nat.le_refl _, intervals_nil _ _⟩
  | @cons i indices input scan tail head rest ih =>
    have own := (stock_scan_allocationLe head).1
    refine ⟨Nat.le_trans own ih.1, ⟨?_, ?_⟩⟩
    · intro r member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨Nat.le_refl _, own, ih.1⟩
      · exact (intervals_mono ih.2 own (Nat.le_refl _)).bounds r member
    · exact List.Pairwise.cons
        (fun r member => (ih.2.bounds r member).1) ih.2.ordered

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

private theorem core_intervals {f : Clif.Function} {ctx : Ctx}
    {second : Clif.Block} {start stop : Nat}
    {order : Order} {data : V} {targets : Array Nat} {input : State} {output : LoweredBlockCore}
    (run : lowerBlockCore ctx order f second bi start stop data targets input = .ok output) :
    input.base.nextVreg ≤ output.state.base.nextVreg ∧
      RecordIntervals input.base.nextVreg output.state.base.nextVreg output.scan.output.records := by
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
        have frontier := congrArg Prod.fst (outgoing_frame edges)
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
        exact ⟨Nat.le_trans keeps intervals.1,
          intervals_mono intervals.2 keeps (Nat.le_refl _)⟩

/-- Retained source records in diagnostic traversal order. -/
def retainedRecords (events : Array BlockScanEvent) : List ScanRecord :=
  events.toList.flatMap (fun event => event.output.records)
private def DriverIntervals (cap : Nat) (d : DriverState) : Prop :=
  cap ≤ d.state.base.nextVreg ∧ RecordIntervals cap d.state.base.nextVreg (retainedRecords d.blockScans)

private theorem node_intervals {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)}
    {order : Order} {params : List Nat} {label : Nat} {input output : DriverState}
    {cap : Nat} (old : DriverIntervals cap input)
    (run : lowerNode ctx ranges order f params label input = .ok output) :
    DriverIntervals cap output := by
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
      have frontier := congrArg Prod.fst (branch_frame args)
      change next.base.nextVreg = input.state.base.nextVreg at frontier
      simpa only [DriverIntervals, frontier] using old
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
            have intervals := core_intervals core
            refine ⟨Nat.le_trans old.1 intervals.1, ?_⟩
            change RecordIntervals cap lowered.state.base.nextVreg
              (retainedRecords (input.blockScans.push lowered.scan))
            rw [retainedRecords, Array.toList_push, List.flatMap_append,
              List.flatMap_cons, List.flatMap_nil, List.append_nil]
            exact intervals_append old.1 intervals.1 old.2 intervals.2

private theorem traversal_intervals {ctx : Ctx} {ranges : Array (Nat × Nat)}
    {order : Order} {f : Clif.Function} {params labels : List Nat} {input output : DriverState}
    {cap : Nat} (old : DriverIntervals cap input)
    (run : labels.foldlM (fun d label => lowerNode ctx ranges order f params label d) input = .ok output) :
    DriverIntervals cap output := by
  induction labels generalizing input with
  | nil => cases run; exact old
  | cons label labels ih =>
    rw [List.foldlM_cons] at run
    cases call : lowerNode ctx ranges order f params label input with
    | error e => simp only [call, bind, Except.bind] at run; cases run
    | ok next =>
      simp only [call, bind, Except.bind] at run
      exact ih (node_intervals old call) run

/-- Actual retained record intervals are bounded and ordered across the whole
reverse traversal, including original and synthetic critical-edge nodes. -/
theorem stock_lower_record_intervals {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) :
    RecordIntervals result.initial.base.nextVreg result.final.base.nextVreg
      (retainedRecords result.blockScans) := by
  unfold Stock.lower at run
  dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind, Except.bind, pure, Except.pure] at run
    | split at run
  cases run
  rename_i _ built hbuild _ order horder _ driver hdriver
  have initial : DriverIntervals built.2.2.base.nextVreg
      {state := built.2.2, blocks := Array.replicate order.nodes.size default,
        edgeArgs := Array.replicate order.nodes.size #[], schedule := #[],
        scans := #[], blockScans := #[], rules := #[]} :=
    ⟨Nat.le_refl _, intervals_nil _ _⟩
  exact (traversal_intervals initial hdriver).2

private theorem ordered_either {records : List ScanRecord}
    (ordered : records.Pairwise (fun r s => r.output.state.base.nextVreg ≤ s.input.base.nextVreg))
    {r s : ScanRecord} (first : r ∈ records) (second : s ∈ records) (different : r ≠ s) :
    r.output.state.base.nextVreg ≤ s.input.base.nextVreg ∨
      s.output.state.base.nextVreg ≤ r.input.base.nextVreg := by
  obtain ⟨i, ith⟩ := List.getElem?_of_mem first
  obtain ⟨j, jth⟩ := List.getElem?_of_mem second
  obtain ⟨ibound, ieq⟩ := List.getElem?_eq_some_iff.mp ith
  obtain ⟨jbound, jeq⟩ := List.getElem?_eq_some_iff.mp jth
  rcases Nat.lt_trichotomy i j with before | same | after
  · have order := List.Pairwise.rel_getElem_of_lt ibound jbound ordered before
    rw [ieq, jeq] at order
    exact Or.inl order
  · subst j
    rw [ieq] at jeq
    exact (different jeq).elim
  · have order := List.Pairwise.rel_getElem_of_lt jbound ibound ordered after
    rw [jeq, ieq] at order
    exact Or.inr order

/-- Distinct actual retained records have disjoint half-open allocation intervals,
regardless of which source block was lowered first. -/
theorem stock_lower_record_intervals_disjoint {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {r s : ScanRecord}
    (first : r ∈ retainedRecords result.blockScans) (second : s ∈ retainedRecords result.blockScans)
    (different : r ≠ s) :
    r.output.state.base.nextVreg ≤ s.input.base.nextVreg ∨
      s.output.state.base.nextVreg ≤ r.input.base.nextVreg :=
  ordered_either (stock_lower_record_intervals run).ordered first second different

private theorem retained_mem {events : Array BlockScanEvent} {event : BlockScanEvent} {record : ScanRecord}
    (member : event ∈ events.toList) (recorded : record ∈ event.output.records) :
    record ∈ retainedRecords events :=
  List.mem_flatMap.mpr ⟨event, member, recorded⟩

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
    AliasPath (finalAliasEntries result.final.alias) key (aliasNum result.final.alias key) ∧
      (result.final.alias[aliasNum result.final.alias key]?).join = none := by
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
  exact chaseF_end (entries_faithful result.final.alias) decrease contains
    (result.final.alias.size + 1) key (by omega)

private theorem available_definition_other {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent} {producer : ScanRecord} {info : IInfo}
    (eventMem : event ∈ result.blockScans.toList)
    (source : result.ctx.insts[producer.inst]? = some info) {x bi j : Nat}
    (defines : x ∈ info.results) (available : x ∈ availOf f (availIn f result.ctx) bi j)
    {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm) :
    producer.inst ≠ blockStart f bi + j := by
  intro same
  obtain ⟨ranges, params, earlier, suffix, starting, finishing, before, after,
    label, blockId, data, core, build, _⟩ := stock_lower_blockScanOrigin run eventMem
  obtain ⟨original, initial, old, spec, view⟩ := buildCtx_source build
  obtain ⟨currentInfo, currentLookup, _, currentResults⟩ := spec.facts.stmt bi b j stm block statement
  have current : result.ctx.insts[blockStart f bi + j]? = some currentInfo := by
    rw [view.insts]; exact currentLookup
  rw [← same, source] at current
  cases current
  have member : x ∈ stm.results := by rwa [← currentResults]
  exact ((mem_av block).mp available).2 ⟨j, stm, Nat.le_refl _, statement, member⟩

/-- The resolved register of any source-available value lies outside the actual
current statement's allocation interval. Fresh origins are available definitions;
SSA availability excludes the current definition, and traversal order separates
their intervals. No extra noninterference certificate is assumed. -/
theorem stock_lower_available_alias_outside_record {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (eventMem : event ∈ result.blockScans.toList) (recordMem : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j) {x key : Nat}
    (available : x ∈ availOf f (availIn f result.ctx) bi j)
    (mapped : result.ctx.valueReg? x = some (.vreg key .int)) :
    aliasNum result.final.alias key < record.input.base.nextVreg ∨
      record.output.state.base.nextVreg ≤ aliasNum result.final.alias key := by
  let endpoint := aliasNum result.final.alias key
  by_cases below : endpoint < result.initial.base.nextVreg
  · exact Or.inl (Nat.lt_of_lt_of_le below
      (stock_lower_blockScanInitialFrontier run event eventMem record recordMem))
  · have fresh : result.initial.base.nextVreg ≤ endpoint := Nat.le_of_not_gt below
    obtain ⟨ownerEvent, producer, info, y, sourceKey, ownerMem, producerMem,
      source, defines, sourceMap, ownerAvailable, lower, upper⟩ :=
      stock_lower_source_path_fresh_origin run scope dominated available mapped
        (resolver_path run scope dominated key).1 fresh
    have other : producer.inst ≠ record.inst := by
      rw [current]
      exact available_definition_other run ownerMem source defines ownerAvailable block statement
    have different : producer ≠ record := fun same => other (congrArg ScanRecord.inst same)
    rcases stock_lower_record_intervals_disjoint run (retained_mem ownerMem producerMem)
        (retained_mem eventMem recordMem) different with before | after
    · exact Or.inl (Nat.lt_of_lt_of_le upper before)
    · exact Or.inr (Nat.le_trans after lower)

/-- A fresh-only fragment for an actual source record preserves the resolved
registers of all source-available values. This connects the derived interval
exclusion to the existing machine execution frame theorem. -/
theorem stock_lower_available_fresh_frame {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (eventMem : event ∈ result.blockScans.toList) (recordMem : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j) {x key : Nat}
    (available : x ∈ availOf f (availIn f result.ctx) bi j)
    (mapped : result.ctx.valueReg? x = some (.vreg key .int))
    {W : Type} {sem : ISem CV W} {ms : List MInst} {regs next : Nat → CV} {w w' : W}
    (defs : ∀ m ∈ ms, ∀ d ∈ vdefs m,
      record.input.base.nextVreg ≤ d ∧ d < record.output.state.base.nextVreg)
    (executed : seqRun sem ms regs w = some (.fall next w')) :
    next (aliasNum result.final.alias key) = regs (aliasNum result.final.alias key) := by
  have outside := stock_lower_available_alias_outside_record run scope dominated eventMem recordMem block statement current available mapped
  apply seqRun_fall_frame ?_ executed
  intro m member defined
  have inside := defs m member _ defined
  omega

attribute [local semireducible] Isle.Aarch64.program Stock.runTerm emitBranch scanBlock

private def twoConstants : Clif.Function := {
  name := "record_intervals_two_constants"
  sig := {returns := [⟨.i64, .none, .normal⟩, ⟨.i64, .none, .normal⟩], callConv := some .systemV}
  blocks := [{id := 0, body := [⟨[0], .iconst .i64 7⟩, ⟨[1], .iconst .i64 9⟩], term := .ret [0, 1]}] }
private theorem exampleScope : LowerScope twoConstants := lowerScope_of (by decide +kernel)
private theorem exampleDominated : Dominated twoConstants := by
  constructor
  · decide +kernel
  · intro ctx ranges st build bi b block
    cases bi with
    | zero =>
      simp [twoConstants] at block; subst b
      constructor
      · intro j stm statement y member
        rcases j with _ | (_ | j) <;> simp at statement
        all_goals subst stm; simp [Backend.Proof.Driver.instArgs] at member
      · intro y member
        change y ∈ [0, 1] at member
        change y ∈ ((availIn twoConstants ctx).getD 0 [] ++ [0, 1]).filter
          (fun x => decide (x ∉ ([] : List Nat)))
        simp only [List.mem_filter, decide_eq_true_eq, List.not_mem_nil, not_false_eq_true, and_true]
        exact List.mem_append_right _ member
    | succ bi => simp [twoConstants] at block
  · intro ctx ranges st build tl x available notLocal y member
    cases tl <;> simp [parsOf, twoConstants]
private theorem firstAvailable (ctx : Ctx) : (0 : Nat) ∈ availOf twoConstants (availIn twoConstants ctx) 0 1 := by
  change 0 ∈ ((availIn twoConstants ctx).getD 0 [] ++ [0]).filter (fun x => decide (x ∉ [1]))
  simp
private def exampleCode : MInst := .movWide .movZ (.vreg 194 .int) ⟨9, 0⟩ .size64
private def exampleRegs (n : Nat) : CV := if n = 195 then 7 else 0
private def exampleNext : Nat → CV := vdefUpd (exampleCode.operands.toOption.getD #[]) [9] exampleRegs
private theorem exampleRun : seqRun ispec [exampleCode] exampleRegs Arm.ArmState.default =
    some (.fall exampleNext Arm.ArmState.default) := rfl

set_option maxRecDepth 20000 in
private theorem exampleObserved : (Stock.lower twoConstants).toOption.map (fun result =>
    (result.ctx.valueReg? 0, result.initial.base.nextVreg, (result.final.alias[192]?).join,
      result.blockScans.toList.any (fun event => event.output.records.any (fun record => record.inst == 0)),
      result.blockScans.toList.any (fun event => event.output.records.any (fun record => record.inst == 1 &&
        record.input.base.nextVreg == 194 && record.output.state.base.nextVreg == 195 &&
        decide (record.output.emitted = #[exampleCode]))))) =
    some (some (.vreg 192 .int), 194, some 195, true, true) := by
  decide +kernel

/-- A real two-constant run has two distinct retained source records. The earlier
source value is allocated above the current fragment: MOVZ9 writes194 while the
available first result resolves to195 and remains7. This exercises the upper
side of noninterference, not just the below-frontier case. -/
theorem stock_lower_record_intervals_witness :
    ∃ (f : Clif.Function) (result : Result) (event other : BlockScanEvent)
      (record producer : ScanRecord),
      Stock.lower f = .ok result ∧ LowerScope f ∧ Dominated f ∧
      event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧ record.inst = 1 ∧
      other ∈ result.blockScans.toList ∧ producer ∈ other.output.records ∧ producer.inst = 0 ∧
      record.output.emitted = #[exampleCode] ∧
      RecordIntervals result.initial.base.nextVreg result.final.base.nextVreg (retainedRecords result.blockScans) ∧
      (record.output.state.base.nextVreg ≤ producer.input.base.nextVreg ∨
        producer.output.state.base.nextVreg ≤ record.input.base.nextVreg) ∧
      aliasNum result.final.alias 192 = 195 ∧
      (aliasNum result.final.alias 192 < record.input.base.nextVreg ∨
        record.output.state.base.nextVreg ≤ aliasNum result.final.alias 192) ∧
      seqRun ispec record.output.emitted.toList exampleRegs Arm.ArmState.default =
        some (.fall exampleNext Arm.ArmState.default) ∧
      exampleNext 194 = 9 ∧ exampleRegs (aliasNum result.final.alias 192) = 7 ∧
      exampleNext (aliasNum result.final.alias 192) = exampleRegs (aliasNum result.final.alias 192) := by
  have observed := exampleObserved
  cases run : Stock.lower twoConstants with
  | error e => simp only [run, Except.toOption, Option.map_none] at observed; cases observed
  | ok result =>
    simp only [run, Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at observed
    obtain ⟨mapped, initial, entry, first, second⟩ := observed
    obtain ⟨other, otherMem, producer, producerMem, producerInst⟩ :=
      (by simpa only [List.any_eq_true, beq_iff_eq] using first :
        ∃ event ∈ result.blockScans.toList, ∃ record ∈ event.output.records, record.inst = 0)
    obtain ⟨event, eventMem, record, recordMem, currentInst, lower, upper, code⟩ :=
      (by simpa only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] using second :
        ∃ event ∈ result.blockScans.toList, ∃ record ∈ event.output.records,
          record.inst = 1 ∧ record.input.base.nextVreg = 194 ∧ record.output.state.base.nextVreg = 195 ∧
          record.output.emitted = #[exampleCode])
    have block : twoConstants.blocks[0]? = some twoConstants.blocks[0]! := rfl
    have statement : twoConstants.blocks[0]!.body[1]? = some (⟨[1], .iconst .i64 9⟩ : Clif.Stmt) := rfl
    have current : record.inst = blockStart twoConstants 0 + 1 := currentInst
    have available := firstAvailable result.ctx
    have resolved : aliasNum result.final.alias 192 = 195 :=
      stock_lower_freshAlias_resolves run (by rw [initial]; decide) 192 entry
    have defs : ∀ m ∈ record.output.emitted.toList, ∀ d ∈ vdefs m,
        record.input.base.nextVreg ≤ d ∧ d < record.output.state.base.nextVreg := by
      rw [code]
      intro m member d defined
      simp only [List.toList_toArray, List.mem_singleton] at member
      subst m
      have actual : vdefs exampleCode = [194] := rfl
      simp only [actual, List.mem_singleton] at defined
      subst d
      rw [lower, upper]
      decide
    have executed : seqRun ispec record.output.emitted.toList exampleRegs Arm.ArmState.default =
        some (.fall exampleNext Arm.ArmState.default) := by rw [code]; exact exampleRun
    have different : record ≠ producer := by
      intro same
      have equality := congrArg ScanRecord.inst same
      rw [currentInst, producerInst] at equality
      cases equality
    exact ⟨twoConstants, result, event, other, record, producer, run, exampleScope, exampleDominated,
      eventMem, recordMem, currentInst, otherMem, producerMem, producerInst, code,
      stock_lower_record_intervals run,
      stock_lower_record_intervals_disjoint run (retained_mem eventMem recordMem) (retained_mem otherMem producerMem) different,
      resolved, stock_lower_available_alias_outside_record run exampleScope exampleDominated eventMem recordMem block statement current available mapped,
      executed, rfl, by rw [resolved]; rfl,
      stock_lower_available_fresh_frame run exampleScope exampleDominated eventMem recordMem block statement current available mapped defs executed⟩

end Backend.Stock.Proof
