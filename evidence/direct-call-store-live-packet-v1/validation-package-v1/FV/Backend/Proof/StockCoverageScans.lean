import FV.Backend.Proof.StockCoverageTerms
import FV.Backend.Proof.StockBlockScan

/-! Compose the real scan transitions with the checked Stock root proofs.
The empty-table invariant is internal proof state, not a new compiler check. -/
namespace Backend.Stock.Proof.Coverage
open Backend.Proof Backend.Proof.Driver Backend.Proof.Cov Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- No source value has a remembered opportunistic definition. -/
def NoOpportunity (st : State) : Prop := ∀ v : Nat, st.opportunistic[v]! = none

/-- Successful actual context construction starts with no remembered definitions. -/
theorem buildCtx_noOpportunity {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial)) : NoOpportunity initial := by
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
      intro v
      change (Array.replicate (allocateRequests original.valTy.size original.insts.size requests).valReg.size
        (none : Option Opportunistic))[v]! = none
      by_cases inside : v < (allocateRequests original.valTy.size original.insts.size requests).valReg.size <;>
        simp [getElem!_def, Array.getElem?_replicate, inside] <;> rfl

private theorem scanState_table (st : State) (i : Nat) :
    (scanState st i).opportunistic = st.opportunistic := by
  unfold scanState
  dsimp only
  split <;> rfl

private theorem commitValues_empty (ctx : Ctx) (values : List Nat) (st : State)
    (empty : NoOpportunity st) : commitOpportunisticValues ctx values st = .ok st := by
  unfold commitOpportunisticValues
  induction values with
  | nil => rfl
  | cons v values ih =>
    rw [List.foldlM_cons]
    simp only [empty v, pure, Except.pure, bind, Except.bind]
    exact ih

private theorem commit_empty {ctx : Ctx} {block i : Nat} {st next : State}
    (empty : NoOpportunity st) (run : commitOpportunistic ctx block i st = .ok (some next)) :
    next = st := by
  unfold commitOpportunistic at run
  dsimp only at run
  split at run
  · cases run
  · rw [commitValues_empty ctx _ st empty] at run
    simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq, Option.some.injEq] at run
    exact run.symm

private theorem scan_empty {ctx : Ctx} {block i ti : Nat} {isBranch : Bool}
    (emitPreserves : ∀ before emission, NoOpportunity before →
      emitInstruction ctx i before = .ok emission → NoOpportunity emission.state)
    {input : State} {output : Scan} (empty : NoOpportunity input)
    (run : scanInstruction ctx block i ti isBranch input = .ok output) :
    NoOpportunity output.state := by
  have normalized : NoOpportunity (scanState input i) := by
    intro v
    rw [scanState_table]
    exact empty v
  have emitted (h : (emitInstruction ctx i (scanState input i) >>= fun e =>
      pure (e.scan block i (scanState input i))) = .ok output) : NoOpportunity output.state := by
    cases hr : emitInstruction ctx i (scanState input i) with
    | error e => simp only [hr, bind, Except.bind] at h; cases h
    | ok emission =>
      simp only [hr, bind, Except.bind, pure, Except.pure] at h
      cases h
      exact emitPreserves _ _ normalized hr
  by_cases sunk : input.sunk[i]! = true
  · simp only [scanInstruction, sunk, ite_true] at run
    cases run; exact empty
  · simp only [scanInstruction, sunk, ite_false] at run
    by_cases skipped : (i == ti && isBranch) = true
    · simp only [skipped, ite_true] at run
      cases run; exact normalized
    · simp only [skipped, ite_false] at run
      cases mandatory : (if i == ti then true else ctx.insts[i]!.clif.any mustLower) <;>
        simp only [mandatory] at run
      all_goals
        by_cases omitted : (! (if i == ti then true else ctx.insts[i]!.clif.any mustLower) &&
          !ctx.insts[i]!.results.any (fun v => (scanState input i).demand[v]! != 0)) = true
        · simp only [mandatory] at omitted
          simp only [omitted, ite_true] at run
          cases run; exact normalized
        · simp only [mandatory] at omitted
          simp only [omitted, ite_false] at run
          by_cases committing : ((scanState input i).entryColor[i]! == 0 &&
              !(if i == ti then true else ctx.insts[i]!.clif.any mustLower)) = true
          · simp only [mandatory] at committing
            simp only [committing, ite_true] at run
            cases hc : commitOpportunistic ctx block i (scanState input i) with
            | error e => simp only [hc, bind, Except.bind] at run; cases run
            | ok result =>
              simp only [hc, bind, Except.bind] at run
              cases result with
              | none => exact emitted run
              | some next =>
                have eq := commit_empty normalized hc
                cases run
                rw [eq]
                exact normalized
          · simp only [mandatory] at committing
            simp only [committing, ite_false] at run
            exact emitted run

/-- Source-body scans retain an empty remembered table through omission,
sinking, commit attempts and real instruction emission. -/
theorem scan_source_noOpportunity {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) (clean : Clean (sourceIdentityCtx ctx))
    {block i ti : Nat} {isBranch : Bool} {info : IInfo} {inst : Clif.Inst}
    (source : ctx.insts[i]? = some info) (original : info.clif = some inst)
    {input : State} {output : Scan} (empty : NoOpportunity input)
    (run : scanInstruction ctx block i ti isBranch input = .ok output) :
    NoOpportunity output.state := by
  apply scan_empty (fun before emission hb hr => ?_) empty run
  intro v
  rw [emission_noOpportunity mapped clean source original hr]
  exact hb v

/-- The metadata shape needed for a scan slot: original source, a branch slot
that is skipped during body scanning, or real return/trap term data. -/
def ScanSlot (ctx : Ctx) (i ti : Nat) (isBranch : Bool) : Prop :=
  (∃ info inst, ctx.insts[i]? = some info ∧ info.clif = some inst) ∨
  (i = ti ∧ isBranch = true) ∨
  (∃ t data, retOrTrap t = true ∧ Backend.termData t = .ok data ∧
    ctx.insts[i]? = some ⟨data, [], [], none⟩)

private theorem scan_slot_empty {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) (clean : Clean (sourceIdentityCtx ctx))
    {block i ti : Nat} {isBranch : Bool} (slot : ScanSlot ctx i ti isBranch)
    {input : State} {output : Scan} (empty : NoOpportunity input)
    (run : scanInstruction ctx block i ti isBranch input = .ok output) :
    NoOpportunity output.state := by
  rcases slot with ⟨info, inst, source, original⟩ | branch | ⟨t, data, retTrap, dataRun, source⟩
  · exact scan_source_noOpportunity mapped clean source original empty run
  · obtain ⟨eq, br⟩ := branch
    subst i
    subst isBranch
    by_cases sunk : input.sunk[ti]! = true
    · simp only [scanInstruction, sunk, ite_true] at run
      cases run; exact empty
    · simp only [scanInstruction, sunk, ite_false, beq_self_eq_true, Bool.true_and, ite_true] at run
      cases run
      intro v
      rw [scanState_table]
      exact empty v
  · apply scan_empty (fun before emission hb hr => ?_) empty run
    intro v
    rw [emission_retTrap_noOpportunity mapped clean retTrap dataRun source hr]
    exact hb v

/-- A complete actual backward scan preserves emptiness. Slot metadata is a
proof premise to derive from real block construction, not an accepted-input gate. -/
theorem scanBlock_noOpportunity {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) (clean : Clean (sourceIdentityCtx ctx))
    {block ti : Nat} {isBranch : Bool} {indices : List Nat}
    (slots : ∀ i ∈ indices, ScanSlot ctx i ti isBranch)
    {input : State} {output : BlockScan} (empty : NoOpportunity input)
    (run : scanBlock ctx block ti isBranch indices input = .ok output) :
    NoOpportunity output.state := by
  have cert := runScans_spec run
  clear run
  induction cert with
  | nil input => exact empty
  | @cons i indices input scan tail head rest ih =>
    apply ih
    · intro k member
      exact slots k (List.mem_cons_of_mem i member)
    · exact scan_slot_empty mapped clean (slots i (List.mem_cons_self)) empty head

/-- Every actual record in a complete backward scan has empty remembered
state at both its input and output, including emitted, omitted and sunk records. -/
theorem scanBlock_records_noOpportunity {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) (clean : Clean (sourceIdentityCtx ctx))
    {block ti : Nat} {isBranch : Bool} {indices : List Nat}
    (slots : ∀ i ∈ indices, ScanSlot ctx i ti isBranch)
    {input : State} {output : BlockScan} (empty : NoOpportunity input)
    (run : scanBlock ctx block ti isBranch indices input = .ok output) :
    ∀ record ∈ output.records, NoOpportunity record.input ∧ NoOpportunity record.output.state := by
  have cert := runScans_spec run
  clear run
  induction cert with
  | nil input => simp
  | @cons i indices input scan tail head rest ih =>
    have first := scan_slot_empty mapped clean (slots i (List.mem_cons_self)) empty head
    intro record member
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · exact ⟨empty, first⟩
    · exact ih (fun k hk => slots k (List.mem_cons_of_mem i hk)) first record member

private def scanFunction : Clif.Function := {
  name := "stock_scan_preservation"
  sig := {params := [⟨.i64, .none, .normal⟩], returns := [⟨.i8, .none, .normal⟩]}
  blocks := [{id := 5, params := [(7, .i64)], body := [⟨[2], .iconst .i8 9⟩], term := .ret [2]}] }
private def scanBuilt : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx scanFunction).toOption.getD (sinkCtx, #[], sinkState)
private def scanData : V := (Backend.termData (.ret [2])).toOption.getD (.op .unit)
private def scanCtx : Ctx := Driver.termCtx scanBuilt.1 1 scanData
private def returnBefore : State := scanState scanBuilt.2.2 1
private def returnAfter : State :=
  {returnBefore.mark 2 with base := returnBefore.base.emit (.rets [(.vreg 193 .int, .x 0)])}
private def returnEmission : Emission :=
  ⟨returnAfter, #[.rets [(.vreg 193 .int, .x 0)]], [], [77, 1037]⟩
private def constantBefore : State := scanState returnAfter 0
private def constantCode : MInst := .movWide .movZ (.vreg 194 .int) ⟨9, 0⟩ .size32
private def constantRootAfter : State :=
  {constantBefore with base := (constantBefore.base.fresh .int).2.emit constantCode}
private def constantAfter : State :=
  {constantRootAfter with alias := aliasStep constantRootAfter.alias (193, 194)}
private def constantEmission : Emission :=
  ⟨constantAfter, #[constantCode], [[.vreg 194 .int]], [78, 124, 322, 1, 582]⟩
private def returnScan : Scan := returnEmission.scan 0 1 returnBefore
private def constantScan : Scan := constantEmission.scan 0 0 constantBefore
private def scanOutput : BlockScan :=
  ⟨constantAfter, [⟨1, scanBuilt.2.2, returnScan⟩, ⟨0, returnAfter, constantScan⟩],
    #[constantCode, .rets [(.vreg 193 .int, .x 0)]]⟩
private theorem scan_build : Stock.buildCtx scanFunction = .ok scanBuilt := rfl
private theorem scan_scope : LowerScope scanFunction := lowerScope_of (by decide +kernel)
private theorem return_root : Stock.runTerm scanCtx "lower" [.inst 1] returnBefore =
    .ok (some (.regsVec []), returnAfter, [77, 1037]) := rfl
private theorem constant_root : Stock.runTerm scanCtx "lower" [.inst 0] constantBefore =
    .ok (some (.regsVec [[.vreg 194 .int]]), constantRootAfter, [78, 124, 322, 1, 582]) := rfl
private theorem return_emission : emitInstruction scanCtx 1 returnBefore = .ok returnEmission := by
  unfold emitInstruction
  rw [return_root]
  rfl
private theorem constant_emission : emitInstruction scanCtx 0 constantBefore = .ok constantEmission := by
  unfold emitInstruction
  rw [constant_root]
  rfl
private theorem return_scan : scanInstruction scanCtx 0 1 1 false scanBuilt.2.2 = .ok returnScan := by
  change (emitInstruction scanCtx 1 returnBefore >>= fun e => pure (e.scan 0 1 returnBefore)) = _
  rw [return_emission]
  rfl
private theorem constant_scan : scanInstruction scanCtx 0 0 1 false returnAfter = .ok constantScan := by
  change (emitInstruction scanCtx 0 constantBefore >>= fun e => pure (e.scan 0 0 constantBefore)) = _
  rw [constant_emission]
  rfl
private theorem scan_run : scanBlock scanCtx 0 1 false [1, 0] scanBuilt.2.2 = .ok scanOutput := by
  change runScans (fun i => scanInstruction scanCtx 0 i 1 false) [1, 0] scanBuilt.2.2 = _
  rw [runScans_ref, runScansRef, return_scan]
  change (do
    let tail ← runScansRef (fun i => scanInstruction scanCtx 0 i 1 false) [0] returnAfter
    pure (⟨tail.state, ⟨1, scanBuilt.2.2, returnScan⟩ :: tail.records, tail.code ++ returnScan.emitted⟩ : BlockScan)) = _
  rw [runScansRef, constant_scan]
  rfl

private theorem clean_stock {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial)) : Clean (sourceIdentityCtx ctx) := by
  obtain ⟨original, before, legacy, spec, view⟩ := buildCtx_source build
  intro i info lookup
  change ctx.insts[i]? = some info at lookup
  rw [view.insts] at lookup
  exact Cov.clean_of_build legacy i info lookup

private theorem scan_mapped : MappedCtxInv scanFunction scanCtx :=
  (buildCtx_mappedInv scan_scope scan_build).termCtx (by rfl) scanData
private theorem scan_clean : Clean (sourceIdentityCtx scanCtx) :=
  clean_termCtx (clean_stock scan_build) (show Backend.termData (.ret [2]) = .ok scanData by rfl) 1
private theorem scan_slots : ∀ i ∈ [1, 0], ScanSlot scanCtx i 1 false := by
  intro i member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact .inr (.inr ⟨.ret [2], scanData, rfl, rfl, rfl⟩)
  · exact .inl ⟨scanCtx.insts[0]!, .iconst .i8 9, rfl, rfl⟩

/-- A real successful build initializes the invariant on a nonempty function. -/
theorem buildCtx_noOpportunity_witness :
    ∃ (f : Clif.Function) (ctx : Ctx) (ranges : Array (Nat × Nat)) (initial : State),
      f.blocks.length = 1 ∧ Stock.buildCtx f = .ok (ctx, ranges, initial) ∧
      ctx.insts.size = 2 ∧ NoOpportunity initial :=
  ⟨scanFunction, scanBuilt.1, scanBuilt.2.1, scanBuilt.2.2, rfl, scan_build, rfl,
    buildCtx_noOpportunity scan_build⟩

/-- The complete real scan emits both a demanded constant and a return, installs
its source alias, and preserves the invariant across two actual transitions. -/
theorem scanBlock_noOpportunity_witness :
    ∃ (f : Clif.Function) (ctx : Ctx) (initial : State) (output : BlockScan),
      MappedCtxInv f ctx ∧ Clean (sourceIdentityCtx ctx) ∧
      (∀ i ∈ [1, 0], ScanSlot ctx i 1 false) ∧ NoOpportunity initial ∧
      scanBlock ctx 0 1 false [1, 0] initial = .ok output ∧ output.records.length = 2 ∧
      output.code.size = 2 ∧ (output.state.alias[193]?).join = some 194 ∧
      NoOpportunity output.state :=
  ⟨scanFunction, scanCtx, scanBuilt.2.2, scanOutput, scan_mapped, scan_clean, scan_slots,
    buildCtx_noOpportunity scan_build, scan_run, rfl, rfl, rfl,
    scanBlock_noOpportunity scan_mapped scan_clean scan_slots
      (buildCtx_noOpportunity scan_build) scan_run⟩

/-- The body record in that complete scan is a demanded, actually emitted
instruction; it independently inhabits the single-source-scan theorem. -/
theorem scan_source_noOpportunity_witness :
    ∃ (f : Clif.Function) (ctx : Ctx) (info : IInfo) (input : State) (output : Scan),
      MappedCtxInv f ctx ∧ Clean (sourceIdentityCtx ctx) ∧
      ctx.insts[0]? = some info ∧ info.clif = some (.iconst .i8 9) ∧ NoOpportunity input ∧
      scanInstruction ctx 0 0 1 false input = .ok output ∧ output.emitted.size = 1 ∧
      (output.state.alias[193]?).join = some 194 ∧ NoOpportunity output.state := by
  let record := scanOutput.records[1]!
  have actual : scanInstruction scanCtx 0 0 1 false record.input = .ok record.output := constant_scan
  have empty : NoOpportunity record.input := by
    intro v
    change scanBuilt.2.2.opportunistic[v]! = none
    exact buildCtx_noOpportunity scan_build v
  exact ⟨scanFunction, scanCtx, scanCtx.insts[0]!, record.input, record.output,
    scan_mapped, scan_clean, rfl, rfl, empty, actual, rfl, rfl,
    scan_source_noOpportunity scan_mapped scan_clean rfl rfl empty actual⟩

/-- The existing real demanded-constant/return scan supplies two actual records,
with emitted code and an installed source alias; both endpoints are inhabited. -/
theorem scanBlock_records_noOpportunity_witness :
    ∃ (f : Clif.Function) (ctx : Ctx) (input : State) (output : BlockScan),
      MappedCtxInv f ctx ∧ Clean (sourceIdentityCtx ctx) ∧
      (∀ i ∈ [1, 0], ScanSlot ctx i 1 false) ∧ NoOpportunity input ∧
      scanBlock ctx 0 1 false [1, 0] input = .ok output ∧ output.records.length = 2 ∧
      output.code.size = 2 ∧ (output.state.alias[193]?).join = some 194 ∧
      (∀ record ∈ output.records, NoOpportunity record.input ∧ NoOpportunity record.output.state) := by
  obtain ⟨f, ctx, input, output, mapped, clean, slots, empty, run, records, code, alias, final⟩ :=
    scanBlock_noOpportunity_witness
  exact ⟨f, ctx, input, output, mapped, clean, slots, empty, run, records, code, alias,
    scanBlock_records_noOpportunity mapped clean slots empty run⟩

end Backend.Stock.Proof.Coverage
