import FV.Backend.Proof.StockSourceAliasRank

/-! Locate producing scan records for aliases installed on actual source mappings. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitBranch scanBlock

private theorem normalized_alias (st : State) (i : Nat) :
    (scanState st i).alias = st.alias := by
  unfold scanState
  dsimp only
  split <;> rfl

private theorem scan_none_alias {ctx : Ctx} {block i ti : Nat} {branch : Bool}
    {st : State} {output : Scan}
    (run : scanInstruction ctx block i ti branch st = .ok output)
    (none : output.step = none) : output.state.alias = st.alias := by
  have rejectEmission (h : (emitInstruction ctx i (scanState st i) >>= fun e =>
      pure (e.scan block i (scanState st i))) = .ok output) : False := by
    cases call : emitInstruction ctx i (scanState st i) with
    | error e => simp only [call, bind, Except.bind] at h; cases h
    | ok e =>
      simp only [call, bind, Except.bind, pure, Except.pure] at h
      cases h
      cases none
  unfold scanInstruction at run
  dsimp only at run
  generalize mandatoryEq : (if i == ti then true else ctx.insts[i]!.clif.any mustLower) = mandatory at run
  split at run
  · cases run; cases none
  · split at run
    · cases run; exact normalized_alias st i
    · split at run
      · cases run; cases none
      · split at run
        · cases call : commitOpportunistic ctx block i (scanState st i) with
          | error e => simp only [call, bind, Except.bind] at run; cases run
          | ok result =>
            simp only [call, bind, Except.bind] at run
            cases result with
            | none => exact (rejectEmission run).elim
            | some q => cases run; cases none
        · exact (rejectEmission run).elim

private theorem scan_key_origin {f : Clif.Function} {source ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State} {slot x key : Nat}
    (build : Stock.buildCtx f = .ok (source, ranges, initial))
    (mapped : source.valueReg? x = some (.vreg key .int))
    (values : ∀ y, ctx.valueReg? y = source.valueReg? y)
    (reserved : ctx.tryRegs = initial.tryRegs[slot]!)
    {block i ti target : Nat} {branch : Bool} {st : State} {output : Scan}
    (run : scanInstruction ctx block i ti branch st = .ok output)
    (entry : (output.state.alias[key]?).join = some target) :
    (st.alias[key]?).join = some target ∨
      ∃ step, output.step = some step ∧ x ∈ ctx.insts[i]!.results := by
  by_cases defines : x ∈ ctx.insts[i]!.results
  · cases recorded : output.step with
    | none =>
      left
      rw [scan_none_alias run recorded] at entry
      exact entry
    | some step => exact Or.inr ⟨step, rfl, defines⟩
  · exact Or.inl ((stock_scan_sourceAliasEntry build mapped values reserved defines run).symm.trans entry)

private theorem block_key_origin {f : Clif.Function} {source ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State} {slot x key : Nat}
    (build : Stock.buildCtx f = .ok (source, ranges, initial))
    (mapped : source.valueReg? x = some (.vreg key .int))
    (values : ∀ y, ctx.valueReg? y = source.valueReg? y)
    (reserved : ctx.tryRegs = initial.tryRegs[slot]!)
    {block ti target : Nat} {indices : List Nat} {branch : Bool} {st : State} {output : BlockScan}
    (run : scanBlock ctx block ti branch indices st = .ok output)
    (entry : (output.state.alias[key]?).join = some target) :
    (st.alias[key]?).join = some target ∨
      ∃ record ∈ output.records, ∃ step, record.output.step = some step ∧
        x ∈ ctx.insts[record.inst]!.results ∧
        (record.output.state.alias[key]?).join = some target := by
  unfold scanBlock at run
  have cert := runScans_spec run
  clear run
  induction cert with
  | nil st => exact Or.inl entry
  | @cons i indices input scan tail head rest ih =>
    rcases ih entry with inherited | ⟨record, member, step, recorded, defines, installed⟩
    · rcases scan_key_origin build mapped values reserved head inherited with old | ⟨step, recorded, defines⟩
      · exact Or.inl old
      · exact Or.inr ⟨⟨i, input, scan⟩, List.mem_cons_self .., step, recorded, defines, inherited⟩
    · exact Or.inr ⟨record, List.mem_cons_of_mem _ member, step, recorded, defines, installed⟩

private theorem selected_results_source {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial))
    {ti i x : Nat} {data : V} {reserved : List Reg × List Reg}
    (defines : x ∈ ({ Driver.termCtx ctx ti data with tryRegs := reserved }).insts[i]!.results) :
    ∃ info inst, ctx.insts[i]? = some info ∧ info.clif = some inst ∧ x ∈ info.results := by
  have ordinary : x ∈ ctx.insts[i]!.results := by
    change x ∈ (Driver.termCtx ctx ti data).insts[i]!.results at defines
    by_cases different : i ≠ ti
    · simp only [getElem!_def, termCtx_insts_ne different data] at defines
      simpa only [getElem!_def] using defines
    · have same : i = ti := Classical.not_not.mp different
      subst i
      change x ∈ (ctx.insts.set! ti ⟨data, [], [], none⟩)[ti]!.results at defines
      simp only [getElem!_def, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self] at defines
      by_cases inside : ti < ctx.insts.size <;> simp only [inside, ite_true, ite_false] at defines
      all_goals cases defines
  cases lookup : ctx.insts[i]? with
  | none => simp only [getElem!_def, lookup] at ordinary; cases ordinary
  | some info =>
    have member : x ∈ info.results := by simpa only [getElem!_def, lookup, Option.getD_some] using ordinary
    obtain ⟨original, before, old, spec, view⟩ := buildCtx_source build
    have oldLookup : original.insts[i]? = some info := by rw [← view.insts]; exact lookup
    have table := Array.mem_toList_iff.mpr (Array.mem_of_getElem? oldLookup)
    rcases spec.insts info table with placeholder | ⟨b, block, stm, statement, same⟩
    · rw [placeholder] at member; cases member
    · subst info
      exact ⟨_, stm.inst, rfl, rfl, member⟩

/-- A retained source record with an installed result alias. Emission is derived
separately from actual record execution and the original input conditions. -/
def SourceAliasRecord (ctx : Ctx) (event : BlockScanEvent) (x key target : Nat) : Prop :=
  ∃ record ∈ event.output.records, ∃ (step : Step) (info : IInfo) (inst : Clif.Inst),
    record.output.step = some step ∧ ctx.insts[record.inst]? = some info ∧
    info.clif = some inst ∧ x ∈ info.results ∧
    (record.output.state.alias[key]?).join = some target

private theorem core_key_origin {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial)) {x key : Nat}
    (mapped : ctx.valueReg? x = some (.vreg key .int))
    {b : Clif.Block} {bi start stop : Nat} {order : Order} {data : V} {targets : Array Nat}
    {input : State} {core : LoweredBlockCore}
    (reservations : input.tryRegs = initial.tryRegs)
    (run : lowerBlockCore ctx order f b bi start stop data targets input = .ok core)
    {target : Nat} (entry : (core.state.alias[key]?).join = some target) :
    (input.alias[key]?).join = some target ∨ SourceAliasRecord ctx core.scan x key target := by
  obtain ⟨stateEq, context, block, term, indices, scanned⟩ := stock_lowerBlockCore_scanOrigin run
  have scanEntry : (core.scan.output.state.alias[key]?).join = some target := by rw [← stateEq]; exact entry
  have values : ∀ y, core.scan.ctx.valueReg? y = ctx.valueReg? y := by rw [context]; intro y; rfl
  have reserved : core.scan.ctx.tryRegs = initial.tryRegs[stop - 1]! := by simp only [context, reservations]
  rcases block_key_origin build mapped values reserved scanned scanEntry with old |
      ⟨record, member, step, recorded, defines, installed⟩
  · have frame := stock_lowerBlockCore_scanAliasEntry build mapped reservations run
    exact Or.inl (frame.symm.trans old)
  · rw [context] at defines
    obtain ⟨info, inst, lookup, original, defined⟩ := selected_results_source build defines
    exact Or.inr ⟨record, member, step, info, inst, recorded, lookup, original, defined, installed⟩

private def DriverSourceRecords (ctx : Ctx) (d : DriverState) : Prop :=
  ∀ x key target, ctx.valueReg? x = some (.vreg key .int) →
    (d.state.alias[key]?).join = some target →
    ∃ event ∈ d.blockScans.toList, SourceAliasRecord ctx event x key target

private theorem node_records {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial)) 
    {order : Order} {params : List Nat} {label : Nat} {input output : DriverState}
    (reservations : input.state.tryRegs = initial.tryRegs)
    (old : DriverSourceRecords ctx input)
    (run : lowerNode ctx ranges order f params label input = .ok output) :
    DriverSourceRecords ctx output := by
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
      intro x key target mapped entry
      have frame := stock_branchArgs_alias args
      obtain ⟨event, member, produced⟩ := old x key target mapped
        (by simpa only [frame] using entry)
      exact ⟨event, member, produced⟩
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
            intro x key target mapped entry
            rcases core_key_origin build mapped reservations core entry with inherited | produced
            · obtain ⟨event, member, record⟩ := old x key target mapped inherited
              refine ⟨event, ?_, record⟩
              change event ∈ (input.blockScans.push lowered.scan).toList
              rw [Array.toList_push]
              exact List.mem_append_left _ member
            · refine ⟨lowered.scan, ?_, produced⟩
              change lowered.scan ∈ (input.blockScans.push lowered.scan).toList
              rw [Array.toList_push]
              exact List.mem_append_right _ (List.mem_singleton_self _)

private theorem traversal_records {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial))
    {order : Order} {params labels : List Nat} {input output : DriverState}
    (bound : input.state.alias.size ≤ initial.base.nextVreg ∧
      initial.base.nextVreg ≤ input.state.base.nextVreg ∧ input.state.tryRegs = initial.tryRegs)
    (old : DriverSourceRecords ctx input)
    (run : labels.foldlM (fun d label => lowerNode ctx ranges order f params label d) input = .ok output) :
    DriverSourceRecords ctx output := by
  induction labels generalizing input with
  | nil => cases run; exact old
  | cons label labels ih =>
    rw [List.foldlM_cons] at run
    cases call : lowerNode ctx ranges order f params label input with
    | error e => simp only [call, bind, Except.bind] at run; cases run
    | ok next =>
      simp only [call, bind, Except.bind] at run
      exact ih (stock_lowerNode_allocationBounds build bound call)
        (node_records build bound.2.2 old call) run

/-- Every installed alias on an actual source mapping has a retained producing
source scan record in the successful whole Stock run. No record-coverage premise
or accepted-program certificate is supplied by the caller. -/
theorem stock_lower_source_alias_record {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {x key target : Nat}
    (mapped : result.ctx.valueReg? x = some (.vreg key .int))
    (entry : (result.final.alias[key]?).join = some target) :
    ∃ event ∈ result.blockScans.toList, SourceAliasRecord result.ctx event x key target := by
  unfold Stock.lower at run
  dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind, Except.bind, pure, Except.pure] at run
    | split at run
  cases run
  rename_i _ built hbuild _ order horder _ driver hdriver
  have initial : built.2.2.alias = #[] := by
    obtain ⟨original, before, requests, _, _, same⟩ := buildCtx_allocation hbuild
    exact congrArg (fun p : Ctx × Array (Nat × Nat) × State => p.2.2.alias) same
  have bound : built.2.2.alias.size ≤ built.2.2.base.nextVreg ∧
      built.2.2.base.nextVreg ≤ built.2.2.base.nextVreg ∧ built.2.2.tryRegs = built.2.2.tryRegs :=
    ⟨by rw [initial]; exact Nat.zero_le _, Nat.le_refl _, rfl⟩
  have empty : DriverSourceRecords built.1
      {state := built.2.2, blocks := Array.replicate order.nodes.size default,
        edgeArgs := Array.replicate order.nodes.size #[], schedule := #[],
        scans := #[], blockScans := #[], rules := #[]} := by
    intro x key target mapped entry
    rw [initial] at entry
    cases entry
  exact traversal_records hbuild bound empty hdriver x key target mapped entry

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

private theorem record_execute {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) {record : ScanRecord}
    (records : record ∈ event.output.records) :
    scanInstruction event.ctx event.block record.inst event.termInst event.isBranch record.input =
      .ok record.output := by
  obtain ⟨ranges, params, earlier, suffix, starting, finishing, before, after,
    label, bi, data, core, build, ordered, initial, empty, parts, folded,
    final, prefixRun, nodeRun, suffixRun, node, coreRun, eventEq, stateEq⟩ :=
    stock_lower_blockScanOrigin run events
  rw [eventEq] at records ⊢
  have actual := (stock_lowerBlockCore_scanOrigin coreRun).2.2.2.2.2
  unfold scanBlock at actual
  exact scans_execute (runScans_spec actual) record records

private theorem scan_sunk_state {ctx : Ctx} {block i ti : Nat} {branch : Bool}
    {st : State} {output : Scan} {step : Step}
    (run : scanInstruction ctx block i ti branch st = .ok output)
    (recorded : output.step = some step) (decision : step.decision = .sunk) : output.state = st := by
  have rejectEmission (h : (emitInstruction ctx i (scanState st i) >>= fun e =>
      pure (e.scan block i (scanState st i))) = .ok output) : False := by
    cases call : emitInstruction ctx i (scanState st i) with
    | error e => simp only [call, bind, Except.bind] at h; cases h
    | ok e =>
      simp only [call, bind, Except.bind, pure, Except.pure] at h
      cases h; cases recorded; cases decision
  unfold scanInstruction at run
  dsimp only at run
  generalize mandatoryEq : (if i == ti then true else ctx.insts[i]!.clif.any mustLower) = mandatory at run
  split at run
  · cases run; rfl
  · split at run
    · cases run; cases recorded
    · split at run
      · cases run; cases recorded; cases decision
      · split at run
        · cases call : commitOpportunistic ctx block i (scanState st i) with
          | error e => simp only [call, bind, Except.bind] at run; cases run
          | ok result =>
            simp only [call, bind, Except.bind] at run
            cases result with
            | none => exact (rejectEmission run).elim
            | some q => cases run; cases recorded; cases decision
        · exact (rejectEmission run).elim

/-- Every installed source alias comes from a real emitting source record.
Omitted/sunk records cannot install it, and the actual scope excludes remembered
binding. All record-coverage and execution facts are derived from the run. -/
theorem stock_lower_source_alias_emitted_record {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (ssa : (valueDefs f).Nodup)
    {x key target : Nat} (mapped : result.ctx.valueReg? x = some (.vreg key .int))
    (entry : (result.final.alias[key]?).join = some target) :
    ∃ (event : BlockScanEvent) (record : ScanRecord) (step : Step) (info : IInfo) (inst : Clif.Inst),
      event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧
      record.output.step = some step ∧ step.decision = .emitted ∧
      result.ctx.insts[record.inst]? = some info ∧ info.clif = some inst ∧ x ∈ info.results ∧
      (record.output.state.alias[key]?).join = some target := by
  obtain ⟨event, eventMem, record, recordMem, step, info, inst,
    recorded, source, original, defines, installed⟩ := stock_lower_source_alias_record run mapped entry
  have actual := record_execute run eventMem recordMem
  have absent := stock_lower_record_inputNoAlias run
    (fun h => scope.nonempty (List.length_eq_zero_iff.mp h)) ssa eventMem recordMem source defines mapped
  have emitted : step.decision = .emitted := by
    cases decision : step.decision with
    | emitted => rfl
    | opportunistic => exact (Coverage.lower_record_noOpportunistic scope run eventMem recordMem recorded decision).elim
    | sunk =>
      rw [scan_sunk_state actual recorded decision, absent] at installed
      cases installed
    | omitted =>
      obtain ⟨_, _, _, _, _, _, _, _, stateEq⟩ := scan_omitted actual recorded decision
      rw [stateEq, normalized_alias, absent] at installed
      cases installed
  exact ⟨event, record, step, info, inst, eventMem, recordMem, recorded, emitted,
    source, original, defines, installed⟩

/-- An installed source-to-source alias in the actual final array, with an
aliased target. This definition requires no scan-record certificate. -/
def FinalSourceAlias (result : Result) (x y : Nat) : Prop :=
  ∃ key target next, result.ctx.valueReg? x = some (.vreg key .int) ∧
    result.ctx.valueReg? y = some (.vreg target .int) ∧
    (result.final.alias[key]?).join = some target ∧ (result.final.alias[target]?).join = some next

/-- The real driver supplies the producing record for every final source edge. -/
theorem stock_lower_final_source_alias_recorded {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (ssa : (valueDefs f).Nodup)
    {x y : Nat} (edge : FinalSourceAlias result x y) : RecordedSourceAlias result x y := by
  obtain ⟨key, target, next, mapped, targetMapped, entry, targetEntry⟩ := edge
  obtain ⟨event, record, step, info, inst, eventMem, recordMem, recorded,
    emitted, source, original, defines, installed⟩ := stock_lower_source_alias_emitted_record run scope ssa mapped entry
  exact ⟨event, record, step, info, inst, key, target, next, eventMem, recordMem, recorded,
    emitted, source, original, defines, mapped, targetMapped, entry, targetEntry⟩

/-- Nonempty source-alias paths in the actual final array. -/
inductive FinalSourcePath (result : Result) : Nat → Nat → Prop where
  | single {x y : Nat} (edge : FinalSourceAlias result x y) : FinalSourcePath result x y
  | cons {x y z : Nat} (head : FinalSourceAlias result x y)
      (tail : FinalSourcePath result y z) : FinalSourcePath result x z

/-- Actual final source-alias paths strictly decrease the inherited rank;
all producing-record hypotheses are discharged by whole-driver construction. -/
theorem stock_lower_final_source_chain_rank {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {x y : Nat} (path : FinalSourcePath result x y) :
    sourceAliasRank result.ctx y < sourceAliasRank result.ctx x := by
  have recorded : RecordedSourcePath result x y := by
    induction path with
    | single edge => exact .single (stock_lower_final_source_alias_recorded run scope dominated.ssa edge)
    | cons head tail ih => exact .cons (stock_lower_final_source_alias_recorded run scope dominated.ssa head) ih
  exact stock_recorded_source_chain_rank run scope dominated recorded

/-- Source aliases in the actual complete final map cannot cycle. -/
theorem stock_lower_final_source_chain_noCycle {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (x : Nat) : ¬ FinalSourcePath result x x := by
  intro path
  exact Nat.lt_irrefl _ (stock_lower_final_source_chain_rank run scope dominated path)

/-- A real constant/two-reduction run has two source edges in its final map.
Producing-record coverage, emission, full-map rank and no-cycle results are
inhabited together by that run, rather than assumed per-edge certificates. -/
theorem stock_lower_final_source_chain_witness :
    ∃ (f : Clif.Function) (result : Result),
      Stock.lower f = .ok result ∧ LowerScope f ∧ Dominated f ∧
      FinalSourceAlias result 2 1 ∧ FinalSourceAlias result 1 0 ∧
      FinalSourcePath result 2 0 ∧ sourceAliasRank result.ctx 0 < sourceAliasRank result.ctx 2 ∧
      ¬ FinalSourcePath result 2 2 ∧
      (∀ x key target, result.ctx.valueReg? x = some (.vreg key .int) →
        (result.final.alias[key]?).join = some target →
        ∃ event ∈ result.blockScans.toList, SourceAliasRecord result.ctx event x key target) ∧
      (∀ x key target, result.ctx.valueReg? x = some (.vreg key .int) →
        (result.final.alias[key]?).join = some target →
        ∃ (event : BlockScanEvent) (record : ScanRecord) (step : Step) (info : IInfo) (inst : Clif.Inst),
          event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧
          record.output.step = some step ∧ step.decision = .emitted ∧
          result.ctx.insts[record.inst]? = some info ∧ info.clif = some inst ∧ x ∈ info.results ∧
          (record.output.state.alias[key]?).join = some target) := by
  obtain ⟨f, result, scope, dominated, run, first, second, fresh, edge2, edge1, path, rank1, rank2, noCycle⟩ :=
    stock_recorded_source_chain_witness
  have forget {x y : Nat} (edge : RecordedSourceAlias result x y) : FinalSourceAlias result x y := by
    obtain ⟨event, record, step, info, inst, key, target, next, events, records, recorded, emitted,
      source, original, defines, mapped, targetMapped, entry, targetEntry⟩ := edge
    exact ⟨key, target, next, mapped, targetMapped, entry, targetEntry⟩
  have fullPath : FinalSourcePath result 2 0 := .cons (forget edge2) (.single (forget edge1))
  exact ⟨f, result, run, scope, dominated, forget edge2, forget edge1, fullPath,
    stock_lower_final_source_chain_rank run scope dominated fullPath,
    stock_lower_final_source_chain_noCycle run scope dominated 2,
    fun _ _ _ mapped entry => stock_lower_source_alias_record run mapped entry,
    fun _ _ _ mapped entry => stock_lower_source_alias_emitted_record run scope dominated.ssa mapped entry⟩

end Backend.Stock.Proof
