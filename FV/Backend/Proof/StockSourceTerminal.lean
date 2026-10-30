import FV.Backend.Proof.StockDriverBounds
import FV.Backend.Proof.StockNodeAliasConnection
import FV.Backend.Proof.StockAliasSemantics

/-! Source registers with no statement definition remain final alias terminals.
This includes block parameters; the construction/SSA facts discharge exclusion. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
section Preservation
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitBranch scanBlock

private theorem undefined_results {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial)) (ssa : (valueDefs f).Nodup)
    {x : Nat} (undefined : ctx.defInst? x = none) (i : Nat) : x ∉ ctx.insts[i]!.results := by
  intro member
  obtain ⟨original, before, legacy, spec, view⟩ := buildCtx_source build
  cases lookup : ctx.insts[i]? with
  | none => simp only [getElem!_def, lookup] at member; cases member
  | some info =>
    have inResults : x ∈ info.results := by simpa only [getElem!_def, lookup, Option.getD_some] using member
    have oldLookup : original.insts[i]? = some info := by rw [← view.insts]; exact lookup
    have inTable : info ∈ original.insts.toList := Array.mem_toList_iff.mpr (Array.mem_of_getElem? oldLookup)
    rcases spec.insts info inTable with placeholder | ⟨b, blockMember, stm, statementMember, same⟩
    · rw [placeholder] at inResults; cases inResults
    · subst info
      obtain ⟨bi, block⟩ := List.getElem?_of_mem blockMember
      obtain ⟨j, statement⟩ := List.getElem?_of_mem statementMember
      have defined : original.defInst? x = some (blockStart f bi + j) :=
        (spec.facts.defs ssa x _).mpr ⟨bi, b, j, stm, block, statement, inResults, rfl⟩
      have sameDef : ctx.defInst? x = original.defInst? x := by simp only [Ctx.defInst?, view.valDef]
      rw [← sameDef, undefined] at defined
      cases defined

private theorem undefined_term_results {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial)) (ssa : (valueDefs f).Nodup)
    {x : Nat} (undefined : ctx.defInst? x = none) (ti i : Nat) (data : V) :
    x ∉ (Driver.termCtx ctx ti data).insts[i]!.results := by
  by_cases different : i ≠ ti
  · simp only [getElem!_def, termCtx_insts_ne different data]
    simpa only [getElem!_def] using undefined_results build ssa undefined i
  · have same : i = ti := Classical.not_not.mp different
    subst i
    show x ∉ (ctx.insts.set! ti ⟨data, [], [], none⟩)[ti]!.results
    simp only [getElem!_def, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self]
    by_cases inside : ti < ctx.insts.size <;> simp only [inside, ite_true, ite_false]
    all_goals exact List.not_mem_nil

private theorem source_payloads_apart {f : Clif.Function} {source ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State} {slot x key : Nat}
    (build : Stock.buildCtx f = .ok (source, ranges, initial))
    (mapped : source.valueReg? x = some (.vreg key .int))
    (reserved : ctx.tryRegs = initial.tryRegs[slot]!) :
    ∀ r ∈ ctx.tryRegs.2, ∀ c, r ≠ .vreg key c := by
  intro r member c same
  rw [reserved] at member
  cases entry : initial.tryRegs[slot]? with
  | none => simp only [getElem!_def, entry] at member; cases member
  | some rs =>
    have mem : r ∈ rs.1 ++ rs.2 := by
      apply List.mem_append.mpr
      right
      simpa only [getElem!_def, entry, Option.getD_some] using member
    have separate := buildCtx_valueReservedDisjoint build x (.vreg key .int) mapped slot rs entry r mem
    obtain ⟨k, reg, _⟩ := buildCtx_reservedBelow build slot rs entry r mem
    subst r
    cases reg
    exact separate rfl

private theorem core_entry {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial))
    (ssa : (valueDefs f).Nodup) {x key bi : Nat}
    (undefined : ctx.defInst? x = none) (mapped : ctx.valueReg? x = some (.vreg key .int))
    {second : Clif.Block} {start stop : Nat}
    {order : Order} {data : V} {targets : Array Nat} {input : State} {output : LoweredBlockCore}
    (reservations : input.tryRegs = initial.tryRegs)
    (run : lowerBlockCore ctx order f second bi start stop data targets input = .ok output) :
    (output.state.alias[key]?).join = (input.alias[key]?).join := by
  let ti := stop - 1
  let selected := { Driver.termCtx ctx ti data with tryRegs := input.tryRegs[ti]! }
  let branch : Bool := match second.term with | .ret .. | .trap .. | .returnCall .. => false | _ => true
  let branchCall : Except String (Option BranchEmission) :=
    if branch then some <$> emitBranch selected f second.term bi ti targets input else pure none
  have payloads : ∀ r ∈ selected.tryRegs.2, ∀ c, r ≠ .vreg key c :=
    source_payloads_apart (slot := ti) build mapped (by simp only [selected, reservations])
  have branchKeeps {br : Option BranchEmission} (call : branchCall = .ok br) :
      (((br.map (·.state)).getD input).alias[key]?).join = (input.alias[key]?).join := by
    unfold branchCall at call
    split at call
    · cases emitted : emitBranch selected f second.term bi ti targets input with
      | error e => simp only [emitted, Functor.map, Except.map] at call; cases call
      | ok e =>
        simp only [emitted, Functor.map, Except.map] at call
        cases call
        exact stock_emitBranch_aliasEntry payloads emitted
    · cases call; rfl
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
      have keeps : (next.alias[key]?).join = (input.alias[key]?).join := by
        rw [stock_collectOutgoing_alias edges]
        exact branchKeeps call
      change (scanBlock selected bi ti branch indices before >>= fun body =>
        pure (⟨body.state, body.code ++ (br.map (·.code) |>.getD #[]), outgoing,
          br, ⟨selected, bi, ti, branch, indices, before, body⟩⟩ : LoweredBlockCore)) = .ok output at run
      cases scan : scanBlock selected bi ti branch indices before with
      | error e => simp only [scan, bind, Except.bind] at run; cases run
      | ok body =>
        simp only [scan, bind, Except.bind, pure, Except.pure] at run
        cases run
        have scanned := stock_scanBlock_sourceAliasEntry
          (ctx := selected) (slot := ti) build mapped (fun _ => rfl)
          (by simp only [selected, reservations])
          (fun i _ => undefined_term_results build ssa undefined ti i data) scan
        exact scanned.trans keeps

private theorem node_entry {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial)) (ssa : (valueDefs f).Nodup)
    {x key : Nat} (undefined : ctx.defInst? x = none) (mapped : ctx.valueReg? x = some (.vreg key .int))
    {order : Order} {params : List Nat} {label : Nat} {input output : DriverState}
    (reservations : input.state.tryRegs = initial.tryRegs)
    (run : lowerNode ctx ranges order f params label input = .ok output) :
    (output.state.alias[key]?).join = (input.state.alias[key]?).join := by
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
      rw [stock_branchArgs_alias args]
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
            exact core_entry build ssa undefined mapped reservations core

private theorem traversal_entry {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial)) (ssa : (valueDefs f).Nodup)
    {x key : Nat} (undefined : ctx.defInst? x = none) (mapped : ctx.valueReg? x = some (.vreg key .int))
    {order : Order} {params labels : List Nat} {input output : DriverState}
    (bound : input.state.alias.size ≤ initial.base.nextVreg ∧
      initial.base.nextVreg ≤ input.state.base.nextVreg ∧ input.state.tryRegs = initial.tryRegs)
    (run : labels.foldlM (fun d label => lowerNode ctx ranges order f params label d) input = .ok output) :
    (output.state.alias[key]?).join = (input.state.alias[key]?).join := by
  induction labels generalizing input with
  | nil => cases run; rfl
  | cons label labels ih =>
    rw [List.foldlM_cons] at run
    cases call : lowerNode ctx ranges order f params label input with
    | error e => simp only [call, bind, Except.bind] at run; cases run
    | ok next =>
      simp only [call, bind, Except.bind] at run
      exact (ih (stock_lowerNode_allocationBounds build bound call) run).trans
        (node_entry build ssa undefined mapped bound.2.2 call)

/-- An actually mapped source value with no statement definition (including
block parameters) stays unaliased through successful whole Stock lowering. -/
theorem stock_lower_undefinedSource_terminal {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (ssa : (valueDefs f).Nodup) {x key : Nat}
    (undefined : result.ctx.defInst? x = none)
    (mapped : result.ctx.valueReg? x = some (.vreg key .int)) :
    (result.final.alias[key]?).join = none ∧ aliasNum result.final.alias key = key := by
  unfold Stock.lower at run
  dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind, Except.bind, pure, Except.pure] at run
    | split at run
  cases run
  rename_i _ built hbuild _ order horder _ driver hdriver
  change built.1.defInst? x = none at undefined
  change built.1.valueReg? x = some (.vreg key .int) at mapped
  have initial : built.2.2.alias = #[] := by
    obtain ⟨original, before, requests, _, _, same⟩ := buildCtx_allocation hbuild
    have state := congrArg (fun p : Ctx × Array (Nat × Nat) × State => p.2.2.alias) same
    exact state
  have bound : built.2.2.alias.size ≤ built.2.2.base.nextVreg ∧
      built.2.2.base.nextVreg ≤ built.2.2.base.nextVreg ∧ built.2.2.tryRegs = built.2.2.tryRegs :=
    ⟨by rw [initial]; exact Nat.zero_le _, Nat.le_refl _, rfl⟩
  have kept := traversal_entry hbuild ssa undefined mapped bound hdriver
  change (driver.state.alias[key]?).join = (built.2.2.alias[key]?).join at kept
  have absent : (driver.state.alias[key]?).join = none := by rw [kept, initial]; rfl
  exact ⟨absent, chaseF_none absent _⟩

end Preservation
private def parameterFunction : Clif.Function := {
  name := "source_parameter_terminal"
  sig := {params := [⟨.i64, .none, .normal⟩], returns := [⟨.i8, .none, .normal⟩], callConv := some .systemV}
  blocks := [{id := 0, params := [(0, .i64)], body := [⟨[1], .iconst .i8 9⟩], term := .ret [1]}] }
private theorem parameter_ssa : (valueDefs parameterFunction).Nodup := by decide
private theorem parameter_observed :
    (Stock.lower parameterFunction).toOption.map (fun r =>
      (r.ctx.valueReg? 0, r.ctx.defInst? 0, (r.final.alias[192]?).join,
        (r.final.alias[193]?).join, r.code.blocks.size)) =
      some (some (.vreg 192 .int), none, none, some 194, 1) := by decide +kernel

/-- A real parameter remains unaliased while a real emitted constant installs
193→194, so the final-terminal premises do not describe an empty alias map. -/
theorem stock_lower_undefinedSource_terminal_witness :
    ∃ (f : Clif.Function) (result : Result),
      (valueDefs f).Nodup ∧ Stock.lower f = .ok result ∧ result.code.blocks.size = 1 ∧
      result.ctx.valueReg? 0 = some (.vreg 192 .int) ∧ result.ctx.defInst? 0 = none ∧
      (result.final.alias[193]?).join = some 194 ∧ (result.final.alias[192]?).join = none ∧
      aliasNum result.final.alias 192 = 192 := by
  have observed := parameter_observed
  cases run : Stock.lower parameterFunction with
  | error e => simp only [run, Except.toOption, Option.map_none] at observed; cases observed
  | ok result =>
    simp only [run, Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at observed
    obtain ⟨mapped, undefined, absent, installed, blocks⟩ := observed
    have terminal := stock_lower_undefinedSource_terminal run parameter_ssa undefined mapped
    exact ⟨parameterFunction, result, parameter_ssa, run, blocks, mapped, undefined, installed,
      terminal.1, terminal.2⟩

/-- The actual final resolver transports an already-held parameter value
unchanged; final terminality is derived from lowering and source SSA. -/
theorem stock_lower_undefinedSource_value {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (ssa : (valueDefs f).Nodup) {x key : Nat}
    (undefined : result.ctx.defInst? x = none)
    (mapped : result.ctx.valueReg? x = some (.vreg key .int))
    {sourceValue : Clif.Val} {regs : Nat → CV} (held : VHolds sourceValue (regs key)) :
    VHolds sourceValue (regs (aliasNum result.final.alias key)) := by
  rw [(stock_lower_undefinedSource_terminal run ssa undefined mapped).2]
  exact held

/-- A real final parameter mapping and an inhabited i64 value demonstrate value
transport while a different source definition has a fresh installed alias. -/
theorem stock_lower_undefinedSource_value_witness :
    ∃ (f : Clif.Function) (result : Result) (regs : Nat → CV),
      (valueDefs f).Nodup ∧ Stock.lower f = .ok result ∧
      result.ctx.valueReg? 0 = some (.vreg 192 .int) ∧ result.ctx.defInst? 0 = none ∧
      (result.final.alias[193]?).join = some 194 ∧
      VHolds (.ofInt .i64 7) (regs 192) ∧
      VHolds (.ofInt .i64 7) (regs (aliasNum result.final.alias 192)) := by
  obtain ⟨f, result, ssa, run, blocks, mapped, undefined, installed, absent, terminal⟩ :=
    stock_lower_undefinedSource_terminal_witness
  let regs : Nat → CV := fun _ => BitVec.ofNat 128 7
  have held : VHolds (.ofInt .i64 7) (regs 192) := by rfl
  exact ⟨f, result, regs, ssa, run, mapped, undefined, installed, held,
    stock_lower_undefinedSource_value run ssa undefined mapped held⟩

end Backend.Stock.Proof
