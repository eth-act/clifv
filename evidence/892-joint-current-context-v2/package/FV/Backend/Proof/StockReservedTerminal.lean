import FV.Backend.Proof.StockDriverBounds
import FV.Backend.Proof.StockNodeAliasConnection
import FV.Backend.Proof.StockAliasSemantics

/-! Initial exception return registers are disjoint from every payload destination.
Derive reserved alias endpoints from construction, rather than a new input check. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- All return reservations are separate from all payload reservations, even
across different slots and overwritten exception requests. -/
def ReturnsPayloadsDisjoint (a : Allocation) : Prop :=
  ∀ (i : Nat) (rs : List Reg × List Reg), a.tryRegs[i]? = some rs → ∀ (j : Nat) (qs : List Reg × List Reg), a.tryRegs[j]? = some qs →
    ∀ r ∈ rs.1, ∀ q ∈ qs.2, r ≠ q

private theorem initial_separate (values instructions : Nat) :
    ReturnsPayloadsDisjoint (Allocation.initial values instructions) := by
  intro i rs lookup j qs other r member q payload
  by_cases inside : i < instructions <;> simp [Allocation.initial, inside] at lookup
  subst rs
  cases member

private theorem step_separate {a : Allocation} (old : ReturnsPayloadsDisjoint a)
    (bound : ReservedRegsBelow a) (request : AllocationRequest) :
    ReturnsPayloadsDisjoint (a.step request) := by
  intro i rs lookup j qs other r member q payload
  cases request with
  | value x => exact old i rs lookup j qs other r member q payload
  | exception slot rets pays =>
    simp only [Allocation.step, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds] at lookup other
    by_cases left : i = slot
    · subst i
      by_cases inside : slot < a.tryRegs.size
      · simp only [inside, ite_true, Option.some.injEq] at lookup
        subst rs
        simp only [List.mem_map, List.mem_range] at member
        obtain ⟨n, nb, rfl⟩ := member
        by_cases right : j = slot
        · subst j
          simp only [inside, ite_true, Option.some.injEq] at other
          subst qs
          simp only [List.mem_map, List.mem_range] at payload
          obtain ⟨m, mb, rfl⟩ := payload
          intro equal
          simp only [Reg.vreg.injEq] at equal
          omega
        · simp only [Ne.symm right, ite_false] at other
          obtain ⟨m, reg, below⟩ := bound j qs other q (List.mem_append_right _ payload)
          subst q
          intro equal
          simp only [Reg.vreg.injEq] at equal
          omega
      · simp only [inside, ite_false] at lookup; cases lookup
    · simp only [Ne.symm left, ite_false] at lookup
      by_cases right : j = slot
      · subst j
        by_cases inside : slot < a.tryRegs.size
        · simp only [inside, ite_true, Option.some.injEq] at other
          subst qs
          simp only [List.mem_map, List.mem_range] at payload
          obtain ⟨m, mb, rfl⟩ := payload
          obtain ⟨n, reg, below⟩ := bound i rs lookup r (List.mem_append_left _ member)
          subst r
          intro equal
          simp only [Reg.vreg.injEq] at equal
          omega
        · simp only [inside, ite_false] at other; cases other
      · simp only [Ne.symm right, ite_false] at other
        exact old i rs lookup j qs other r member q payload

/-- The actual request fold keeps all return and payload reservations separate. -/
theorem allocateRequests_returnsPayloadsDisjoint (values instructions : Nat)
    (requests : List AllocationRequest) :
    ReturnsPayloadsDisjoint (allocateRequests values instructions requests) := by
  have reversed (qs : List AllocationRequest) :
      ReturnsPayloadsDisjoint (allocateRequests values instructions qs.reverse) := by
    induction qs with
    | nil => exact initial_separate values instructions
    | cons request qs ih =>
      rw [List.reverse_cons]
      have step := step_separate ih (allocateRequests_reservedBelow values instructions qs.reverse) request
      simpa only [allocateRequests, List.foldl_append, List.foldl_cons, List.foldl_nil] using step
  simpa only [List.reverse_reverse] using reversed requests.reverse

/-- Successful actual context construction derives return/payload separation
for every reservation slot consumed by later lowering. -/
theorem buildCtx_returnsPayloadsDisjoint {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial)) :
    ∀ (i : Nat) (rs : List Reg × List Reg), initial.tryRegs[i]? = some rs → ∀ (j : Nat) (qs : List Reg × List Reg), initial.tryRegs[j]? = some qs →
      ∀ r ∈ rs.1, ∀ q ∈ qs.2, r ≠ q := by
  obtain ⟨original, before, requests, _, _, same⟩ := buildCtx_allocation build
  have separated := allocateRequests_returnsPayloadsDisjoint original.valTy.size original.insts.size requests
  have state := congrArg (fun p : Ctx × Array (Nat × Nat) × State => p.2.2.tryRegs) same
  rw [state]
  exact separated

section Preservation
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitBranch scanBlock

private theorem return_payloads_apart {f : Clif.Function} {source ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State} {owner slot key : Nat} {rs : List Reg × List Reg}
    (build : Stock.buildCtx f = .ok (source, ranges, initial))
    (lookup : initial.tryRegs[owner]? = some rs) (member : (.vreg key .int) ∈ rs.1)
    (reserved : ctx.tryRegs = initial.tryRegs[slot]!) :
    ∀ r ∈ ctx.tryRegs.2, ∀ c, r ≠ .vreg key c := by
  intro r payload c equal
  rw [reserved] at payload
  cases other : initial.tryRegs[slot]? with
  | none => simp only [getElem!_def, other] at payload; cases payload
  | some qs =>
    have pay : r ∈ qs.2 := by simpa only [getElem!_def, other, Option.getD_some] using payload
    have separate := buildCtx_returnsPayloadsDisjoint build owner rs lookup slot qs other
      (.vreg key .int) member r pay
    obtain ⟨n, reg, _⟩ := buildCtx_reservedBelow build slot qs other r (List.mem_append_right _ pay)
    have classes : (.int : RegClass) = c := (Reg.vreg.inj (reg.symm.trans equal)).2
    subst c
    exact separate equal.symm

private theorem return_source_apart {f : Clif.Function} {source ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State} {owner key : Nat} {rs : List Reg × List Reg}
    (build : Stock.buildCtx f = .ok (source, ranges, initial))
    (lookup : initial.tryRegs[owner]? = some rs) (member : (.vreg key .int) ∈ rs.1)
    (values : ∀ x, ctx.valueReg? x = source.valueReg? x) :
    ∀ x r, ctx.valueReg? x = some r → ∀ c, r ≠ .vreg key c := by
  intro x r mapped c equal
  rw [values] at mapped
  obtain ⟨n, reg, _⟩ := (buildCtx_allocated build).2.2.1 x r mapped
  have classes : (.int : RegClass) = c := (Reg.vreg.inj (reg.symm.trans equal)).2
  subst c
  exact buildCtx_valueReservedDisjoint build x r mapped owner rs lookup
    (.vreg key .int) (List.mem_append_left _ member) equal

private theorem core_entry {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial))
     {owner key bi : Nat} {rs : List Reg × List Reg}
    (lookup : initial.tryRegs[owner]? = some rs) (member : (.vreg key .int) ∈ rs.1)
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
    return_payloads_apart (slot := ti) build lookup member (by simp only [selected, reservations])
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
          (fun i _ x _ r mapping c => return_source_apart (ctx := selected) build lookup member
            (fun _ => rfl) x r mapping c) scan
        exact scanned.trans keeps

private theorem node_entry {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial)) 
    {owner key : Nat} {rs : List Reg × List Reg}
    (lookup : initial.tryRegs[owner]? = some rs) (member : (.vreg key .int) ∈ rs.1)
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
            exact core_entry build lookup member reservations core

private theorem traversal_entry {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial)) 
    {owner key : Nat} {rs : List Reg × List Reg}
    (lookup : initial.tryRegs[owner]? = some rs) (member : (.vreg key .int) ∈ rs.1)
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
        (node_entry build lookup member bound.2.2 call)


/-- Actual initial exception return reservations remain unaliased and are final
resolver endpoints throughout successful whole Stock lowering. -/
theorem stock_lower_reservedReturn_terminal {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {owner key : Nat} {rs : List Reg × List Reg}
    (lookup : result.initial.tryRegs[owner]? = some rs) (member : (.vreg key .int) ∈ rs.1) :
    (result.final.alias[key]?).join = none ∧ aliasNum result.final.alias key = key := by
  unfold Stock.lower at run
  dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind, Except.bind, pure, Except.pure] at run
    | split at run
  cases run
  rename_i _ built hbuild _ order horder _ driver hdriver
  change built.2.2.tryRegs[owner]? = some rs at lookup
  have initial : built.2.2.alias = #[] := by
    obtain ⟨original, before, requests, _, _, same⟩ := buildCtx_allocation hbuild
    exact congrArg (fun p : Ctx × Array (Nat × Nat) × State => p.2.2.alias) same
  have bound : built.2.2.alias.size ≤ built.2.2.base.nextVreg ∧
      built.2.2.base.nextVreg ≤ built.2.2.base.nextVreg ∧ built.2.2.tryRegs = built.2.2.tryRegs :=
    ⟨by rw [initial]; exact Nat.zero_le _, Nat.le_refl _, rfl⟩
  have kept := traversal_entry hbuild lookup member bound hdriver
  change (driver.state.alias[key]?).join = (built.2.2.alias[key]?).join at kept
  have absent : (driver.state.alias[key]?).join = none := by rw [kept, initial]; rfl
  exact ⟨absent, chaseF_none absent _⟩

end Preservation

private def separationAllocation : Allocation :=
  allocateRequests 1 2 [.value 0, .exception 0 1 2, .exception 1 2 1, .exception 0 1 1]

/-- Nonempty overwritten and cross-slot reservations inhabit separation. -/
theorem allocateRequests_returnsPayloadsDisjoint_witness :
    separationAllocation.tryRegs[0]? = some ([.vreg 199 .int], [.vreg 200 .int]) ∧
    separationAllocation.tryRegs[1]? = some ([.vreg 196 .int, .vreg 197 .int], [.vreg 198 .int]) ∧
    ReturnsPayloadsDisjoint separationAllocation :=
  ⟨rfl, rfl, allocateRequests_returnsPayloadsDisjoint _ _ _⟩

private def reservedSignature : Clif.Signature := {
  returns := [⟨.i8, .none, .normal⟩], callConv := some .systemV }
private def reservedTable : Clif.ExnTable := {sig := 0, normal := ⟨1, [.ret 0, .val 0]⟩}
private def reservedFunction : Clif.Function := {
  name := "reserved_return_terminal"
  sig := reservedSignature
  sigDecls := [(0, reservedSignature)]
  externs := [(0, {name := "callee", sig := reservedSignature})]
  blocks := [
    {id := 0, body := [⟨[0], .iconst .i8 9⟩], term := .tryCall 0 [] reservedTable},
    {id := 1, params := [(1, .i8), (2, .i8)], term := .ret [2]}] }
private def reservedBuilt : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx reservedFunction).toOption.getD (sinkCtx, #[], sinkState)
private theorem reserved_build : Stock.buildCtx reservedFunction = .ok reservedBuilt := rfl
private theorem reserved_observed : (Stock.lower reservedFunction).toOption.map (fun r =>
    (r.initial.tryRegs[1]?, (r.final.alias[193]?).join, (r.final.alias[194]?).join, r.code.blocks.size)) =
      some (some ([.vreg 193 .int], [.vreg 194 .int, .vreg 195 .int]), none, some 193, 2) := by
  decide +kernel

/-- A real successfully built try-call context has populated return/payload
slots; all slot-pair separations follow from construction. -/
theorem buildCtx_returnsPayloadsDisjoint_witness :
    ∃ (f : Clif.Function) (ctx : Ctx) (ranges : Array (Nat × Nat)) (initial : State),
      Stock.buildCtx f = .ok (ctx, ranges, initial) ∧
      initial.tryRegs[1]? = some ([.vreg 193 .int], [.vreg 194 .int, .vreg 195 .int]) ∧
      (∀ (i : Nat) (rs : List Reg × List Reg), initial.tryRegs[i]? = some rs →
        ∀ (j : Nat) (qs : List Reg × List Reg), initial.tryRegs[j]? = some qs →
          ∀ r ∈ rs.1, ∀ q ∈ qs.2, r ≠ q) :=
  ⟨reservedFunction, reservedBuilt.1, reservedBuilt.2.1, reservedBuilt.2.2, reserved_build, rfl,
    buildCtx_returnsPayloadsDisjoint reserved_build⟩

/-- Real try-call lowering aliases payload194 to return193, while the return
remains unaliased and terminal in the actual final map. -/
theorem stock_lower_reservedReturn_terminal_witness :
    ∃ (f : Clif.Function) (result : Result),
      Stock.lower f = .ok result ∧ result.code.blocks.size = 2 ∧
      result.initial.tryRegs[1]? = some ([.vreg 193 .int], [.vreg 194 .int, .vreg 195 .int]) ∧
      (result.final.alias[194]?).join = some 193 ∧ (result.final.alias[193]?).join = none ∧
      aliasNum result.final.alias 193 = 193 := by
  have observed := reserved_observed
  cases run : Stock.lower reservedFunction with
  | error e => simp only [run, Except.toOption, Option.map_none] at observed; cases observed
  | ok result =>
    simp only [run, Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at observed
    obtain ⟨lookup, absent, payload, blocks⟩ := observed
    have terminal := stock_lower_reservedReturn_terminal run (key := 193) lookup (by simp)
    exact ⟨reservedFunction, result, run, blocks, lookup, payload, terminal.1, terminal.2⟩

/-- A source or payload alias to a reserved return resolves to that actual
return register; terminality comes from the whole lowering run. -/
theorem stock_lower_reservedReturn_resolves {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {owner key : Nat} {rs : List Reg × List Reg}
    (lookup : result.initial.tryRegs[owner]? = some rs) (member : (.vreg key .int) ∈ rs.1)
    {sourceKey : Nat} (entry : (result.final.alias[sourceKey]?).join = some key) :
    aliasNum result.final.alias sourceKey = key := by
  have absent := (stock_lower_reservedReturn_terminal run lookup member).1
  change chaseF (fun k => (result.final.alias[k]?).join) (result.final.alias.size + 1) sourceKey = key
  rw [chaseF, entry]
  exact chaseF_none absent _

/-- The real overlapping return/payload pair supplies an installed incoming
alias and a populated reservation slot for final resolution. -/
theorem stock_lower_reservedReturn_resolves_witness :
    ∃ (f : Clif.Function) (result : Result),
      Stock.lower f = .ok result ∧
      result.initial.tryRegs[1]? = some ([.vreg 193 .int], [.vreg 194 .int, .vreg 195 .int]) ∧
      (result.final.alias[194]?).join = some 193 ∧ aliasNum result.final.alias 194 = 193 := by
  obtain ⟨f, result, run, blocks, lookup, payload, absent, terminal⟩ :=
    stock_lower_reservedReturn_terminal_witness
  exact ⟨f, result, run, lookup, payload,
    stock_lower_reservedReturn_resolves run (key := 193) lookup (by simp) payload⟩

/-- An already-held reserved-return value is also held through every actual
final alias into that return. No independent resolver equation is assumed. -/
theorem stock_lower_reservedReturn_value {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {owner key : Nat} {rs : List Reg × List Reg}
    (lookup : result.initial.tryRegs[owner]? = some rs) (member : (.vreg key .int) ∈ rs.1)
    {sourceKey : Nat} (entry : (result.final.alias[sourceKey]?).join = some key)
    {regs : Nat → CV} {value : Clif.Val} (held : VHolds value (regs key)) :
    VHolds value (regs (aliasNum result.final.alias sourceKey)) := by
  rw [stock_lower_reservedReturn_resolves run lookup member entry]
  exact held

/-- A real return/payload alias and inhabited i8 value demonstrate final-map
transport. This does not yet prove execution produces the reserved return value. -/
theorem stock_lower_reservedReturn_value_witness :
    ∃ (f : Clif.Function) (result : Result) (regs : Nat → CV),
      Stock.lower f = .ok result ∧
      result.initial.tryRegs[1]? = some ([.vreg 193 .int], [.vreg 194 .int, .vreg 195 .int]) ∧
      (result.final.alias[194]?).join = some 193 ∧ VHolds (.ofInt .i8 7) (regs 193) ∧
      VHolds (.ofInt .i8 7) (regs (aliasNum result.final.alias 194)) := by
  obtain ⟨f, result, run, lookup, payload, resolves⟩ := stock_lower_reservedReturn_resolves_witness
  let regs : Nat → CV := fun _ => BitVec.ofNat 128 7
  have held : VHolds (.ofInt .i8 7) (regs 193) := rfl
  exact ⟨f, result, regs, run, lookup, payload, held,
    stock_lower_reservedReturn_value run lookup (by simp) payload held⟩

end Backend.Stock.Proof

