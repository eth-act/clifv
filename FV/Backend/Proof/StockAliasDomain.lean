import FV.Backend.Proof.StockReservedTerminal
import FV.Backend.Proof.StockSourceAliasRecords

/-! Only source mappings and reserved payloads can be final alias keys. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
section Preservation
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitBranch scanBlock

private def NotSource (ctx : Ctx) (key : Nat) : Prop :=
  ∀ x, ctx.valueReg? x ≠ some (.vreg key .int)
private def NotPayload (initial : State) (key : Nat) : Prop :=
  ∀ (slot : Nat) (rs : List Reg × List Reg), initial.tryRegs[slot]? = some rs →
    (.vreg key .int) ∉ rs.2

private theorem payloads_apart {f : Clif.Function} {source ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State} {slot key : Nat}
    (build : Stock.buildCtx f = .ok (source, ranges, initial))
    (excluded : NotPayload initial key) (reserved : ctx.tryRegs = initial.tryRegs[slot]!) :
    ∀ r ∈ ctx.tryRegs.2, ∀ c, r ≠ .vreg key c := by
  intro r member c equal
  rw [reserved] at member
  cases lookup : initial.tryRegs[slot]? with
  | none => simp only [getElem!_def, lookup] at member; cases member
  | some rs =>
    have mem : r ∈ rs.2 := by simpa only [getElem!_def, lookup, Option.getD_some] using member
    obtain ⟨n, reg, _⟩ := buildCtx_reservedBelow build slot rs lookup r (List.mem_append_right _ mem)
    have classes : (.int : RegClass) = c := (Reg.vreg.inj (reg.symm.trans equal)).2
    subst c
    exact excluded slot rs lookup (equal ▸ mem)

private theorem sources_apart {f : Clif.Function} {source ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State} {key : Nat}
    (build : Stock.buildCtx f = .ok (source, ranges, initial))
    (excluded : NotSource source key) (values : ∀ x, ctx.valueReg? x = source.valueReg? x) :
    ∀ x r, ctx.valueReg? x = some r → ∀ c, r ≠ .vreg key c := by
  intro x r mapped c equal
  rw [values] at mapped
  obtain ⟨n, reg, _⟩ := (buildCtx_allocated build).2.2.1 x r mapped
  have classes : (.int : RegClass) = c := (Reg.vreg.inj (reg.symm.trans equal)).2
  subst c
  exact excluded x (mapped.trans (congrArg some equal))

private theorem core_entry {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial))
    {key : Nat} (sourceExcluded : NotSource ctx key) (payloadExcluded : NotPayload initial key)
    {bi : Nat}
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
    payloads_apart (slot := ti) build payloadExcluded (by simp only [selected, reservations])
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
        have scanned := stock_scanBlock_aliasEntry payloads
          (fun i _ x _ r mapping c => sources_apart (ctx := selected) build sourceExcluded
            (fun _ => rfl) x r mapping c) scan
        exact scanned.trans keeps

private theorem node_entry {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial)) 
    {key : Nat} (sourceExcluded : NotSource ctx key) (payloadExcluded : NotPayload initial key)
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
            exact core_entry build sourceExcluded payloadExcluded reservations core

private theorem traversal_entry {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial)) 
    {key : Nat} (sourceExcluded : NotSource ctx key) (payloadExcluded : NotPayload initial key)
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
        (node_entry build sourceExcluded payloadExcluded bound.2.2 call)


private theorem excluded_alias_none {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {key : Nat}
    (sourceExcluded : NotSource result.ctx key) (payloadExcluded : NotPayload result.initial key) :
    (result.final.alias[key]?).join = none := by
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
  have kept := traversal_entry hbuild sourceExcluded payloadExcluded bound hdriver
  change (driver.state.alias[key]?).join = (built.2.2.alias[key]?).join at kept
  rw [kept, initial]
  rfl

/-- The actual final alias domain contains only mapped source registers and
initially reserved payload registers. Construction discharges all key exclusions;
no input alias-domain check or new source restriction is assumed. -/
theorem stock_lower_alias_key_origin {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {key target : Nat}
    (entry : (result.final.alias[key]?).join = some target) :
    (∃ x, result.ctx.valueReg? x = some (.vreg key .int)) ∨
    (∃ (slot : Nat) (rs : List Reg × List Reg), result.initial.tryRegs[slot]? = some rs ∧
      (.vreg key .int) ∈ rs.2) := by
  classical
  by_cases source : ∃ x, result.ctx.valueReg? x = some (.vreg key .int)
  · exact Or.inl source
  · by_cases payload : ∃ (slot : Nat) (rs : List Reg × List Reg),
        result.initial.tryRegs[slot]? = some rs ∧ (.vreg key .int) ∈ rs.2
    · exact Or.inr payload
    · have absent := excluded_alias_none run
        (fun x mapped => source ⟨x, mapped⟩)
        (fun slot rs lookup member => payload ⟨slot, rs, lookup, member⟩)
      rw [absent] at entry
      cases entry

end Preservation
/-- Real source and try-call payload aliases inhabit both classes of the
actual final alias domain. The source case reuses the complete reduction chain. -/
theorem stock_lower_alias_key_origin_witness :
    (∃ (f : Clif.Function) (result : Result) (key target : Nat),
      Stock.lower f = .ok result ∧ result.ctx.valueReg? 2 = some (.vreg key .int) ∧
      (result.final.alias[key]?).join = some target ∧
      ((∃ x, result.ctx.valueReg? x = some (.vreg key .int)) ∨
        (∃ (slot : Nat) (rs : List Reg × List Reg), result.initial.tryRegs[slot]? = some rs ∧
          (.vreg key .int) ∈ rs.2))) ∧
    (∃ (f : Clif.Function) (result : Result),
      Stock.lower f = .ok result ∧
      result.initial.tryRegs[1]? = some ([.vreg 193 .int], [.vreg 194 .int, .vreg 195 .int]) ∧
      (result.final.alias[194]?).join = some 193 ∧
      ((∃ x, result.ctx.valueReg? x = some (.vreg 194 .int)) ∨
        (∃ (slot : Nat) (rs : List Reg × List Reg), result.initial.tryRegs[slot]? = some rs ∧
          (.vreg 194 .int) ∈ rs.2))) := by
  constructor
  · obtain ⟨f, result, run, scope, dominated, edge2, edge1, path, rank, noCycle, covers, emits⟩ :=
      stock_lower_final_source_chain_witness
    obtain ⟨key, target, next, mapped, targetMapped, entry, targetEntry⟩ := edge2
    exact ⟨f, result, key, target, run, mapped, entry, stock_lower_alias_key_origin run entry⟩
  · obtain ⟨f, result, run, lookup, entry, resolves⟩ := stock_lower_reservedReturn_resolves_witness
    exact ⟨f, result, run, lookup, entry, stock_lower_alias_key_origin run entry⟩

end Backend.Stock.Proof
