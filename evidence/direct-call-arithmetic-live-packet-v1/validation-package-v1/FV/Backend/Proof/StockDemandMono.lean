import FV.Backend.Proof.StockFreshRecordValues

/-! Successful Stock interpreter execution never removes source-register demand. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program

private def demandFields (st : State) := st.demand
private def DemandMono (st next : State) := ∀ (x : Nat), st.demand[x]! ≤ next.demand[x]!
private theorem mono_refl (st : State) : DemandMono st st := fun _ => Nat.le_refl _
private theorem mono_trans {a b c : State} (ab : DemandMono a b) (bc : DemandMono b c) :
    DemandMono a c := fun x => Nat.le_trans (ab x) (bc x)
private theorem mark_mono (st : State) (v : Nat) : DemandMono st (st.mark v) := by
  intro x
  by_cases equal : x = v
  · subst x
    by_cases bounded : v < st.demand.size
    · rw [(mark_demand st v bounded).1]
      omega
    · change st.demand[v]! ≤ (st.demand.modify v (· + 1))[v]!
      have small : ¬ v < (st.demand.modify v (· + 1)).size := by simpa only [Array.size_modify] using bounded
      simp only [getElem!_def, Array.getElem?_eq_none (Nat.le_of_not_lt bounded),
        Array.getElem?_eq_none (Nat.le_of_not_lt small), Option.getD_none]
      exact Nat.le_refl _
  · rw [mark_other st v x equal]
    exact Nat.le_refl _
private theorem marks_mono (st : State) (vs : List Nat) : DemandMono st (vs.foldl State.mark st) := by
  induction vs generalizing st with
  | nil => exact mono_refl st
  | cons v vs ih => exact mono_trans (mark_mono st v) (ih (st.mark v))

private theorem setAlias_demandFields {st next : State} {dst src : Reg}
    (h : st.setAlias dst src = .ok next) : demandFields next = demandFields st := by
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

private theorem try_fold_demandFields (ps rets : List Reg) (pairs : List (Reg × Reg))
    (st : State) (regs : List Reg) {next : State} {out : List Reg}
    (h : pairs.foldl (tryAliasStep ps rets) (.ok (st, regs)) = .ok (next, out)) :
    demandFields next = demandFields st := by
  induction pairs generalizing st regs with
  | nil => cases h; rfl
  | cons pair pairs ih =>
    rw [List.foldl_cons] at h
    cases hs : tryAliasStep ps rets (.ok (st, regs)) pair with
    | error e => rw [hs, try_fold_error] at h; cases h
    | ok result =>
      rcases result with ⟨middle, rs⟩
      rw [hs] at h
      have hm : demandFields middle = demandFields st := by
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
              exact setAlias_demandFields ha
      exact (ih middle rs h).trans hm


private theorem delegate_demandFields {ctx : Ctx} {t : Term} {args : List V}
    {st next : State} {v : V}
    (h : (match Backend.externCtor ctx t args st.base with
      | .ok (v, base) => ExtResult.ok (v, { st with base })
      | .fail => ExtResult.fail
      | .unmodeled e => ExtResult.unmodeled e) = ExtResult.ok (v, next)) :
    next.demand = st.demand := by
  cases call : Backend.externCtor ctx t args st.base with
  | fail => rw [call] at h; cases h
  | unmodeled e => rw [call] at h; cases h
  | ok pair =>
    rcases pair with ⟨value, base⟩
    rw [call] at h
    cases h
    rfl

/-- Every successful actual constructor preserves all existing demand counts,
including scalar/vector requests, sinking, calls and reserved-payload aliasing. -/
theorem stock_ctor_demand_mono {ctx : Ctx} {t : Term} {args : List V}
    {st next : State} {v : V} (h : Stock.externCtor ctx t args st = .ok (v, next)) :
    ∀ (x : Nat), st.demand[x]! ≤ next.demand[x]! := by
  change DemandMono st next
  unfold Stock.externCtor at h
  split at h
  all_goals dsimp only at h
  all_goals try solve |
    have same := delegate_demandFields h
    intro x
    rw [same]
  all_goals repeat' first
    | (solve | cases h <;> exact mono_refl st)
    | (solve | cases h <;> exact mark_mono st _)
    | (solve |
        have same := delegate_demandFields h
        intro x
        rw [same]
        exact mark_mono st _ x)
    | (solve |
        have same := delegate_demandFields h
        intro x
        rw [same]
        exact marks_mono st _ x)
    | split at h
  all_goals
    rename_i _ _ sig _ _ ps _ _ s regs step
    cases h
    have same := try_fold_demandFields ps ctx.tryRegs.1
      ((payloadRegs sig.callConv).zip ctx.tryRegs.2) st [] step
    change next.demand = st.demand at same
    intro x
    rw [same]
    exact Nat.le_refl _

/-- Nested evaluation retains demand through the existing generic interpreter
state-preservation proof, without restricting the selected rule family. -/
theorem stock_apply_demand_mono {p : Program} {ctx : Ctx} {cfg : Config}
    {n ty t : Nat} {args : List V} {st next : State} {tr tr' : Array RuleId} {out : Option V}
    (run : (applyTerm p (Stock.sem ctx) cfg n ty t args).run (st, tr) = .ok (out, next, tr')) :
    ∀ (x : Nat), st.demand[x]! ≤ next.demand[x]! :=
  (presAt (R := DemandMono) mono_refl (fun _ _ _ => mono_trans)
    (fun _ _ _ _ _ h => stock_ctor_demand_mono h) n).apply ty t args st tr out next tr' run

private theorem fold_demandFields_eq {α β γ : Type} (field : α → γ)
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

private theorem binding_demandFields {ctx : Ctx} {pairs : List (Nat × List Reg)}
    {st next : State} {copies : Array MInst}
    (h : bindResults ctx pairs st = .ok (next, copies)) : demandFields next = demandFields st := by
  unfold bindResults at h
  apply fold_demandFields_eq (fun a : State × Array MInst => demandFields a.1) _ ?_ pairs h
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
        exact setAlias_demandFields ha
    · cases he; rfl
    · cases he

/-- Actual result binding changes aliases/copy code without changing source demand. -/
theorem stock_bindResults_demand {ctx : Ctx} {pairs : List (Nat × List Reg)}
    {st next : State} {copies : Array MInst}
    (run : bindResults ctx pairs st = .ok (next,copies)) : next.demand = st.demand :=
  binding_demandFields run

/-- A nonempty virtual binding preserves a populated demand array while
installing an actual source-to-result alias. -/
theorem stock_bindResults_demand_witness :
    ∃ (ctx : Ctx) (st next : State), st.demand = #[1,2] ∧
      bindResults ctx [(0,[.vreg 194 .int])] st = .ok (next,#[]) ∧ next.demand = st.demand := by
  let ctx : Ctx := {sinkCtx with valReg := #[some (.vreg 192 .int)]}
  let st : State := {sinkState with demand := #[1,2]}
  have actual := bindResults_virtual ctx st [(0,192,194)] (by
    intro p member
    have equal := List.mem_singleton.mp member
    subst p
    rfl)
  simp only [List.map_cons,List.map_nil,List.foldl_cons,List.foldl_nil] at actual
  exact ⟨ctx,st,_,rfl,actual,stock_bindResults_demand actual⟩

/-- Successful actual named lowering preserves every existing demand count. -/
theorem stock_named_demand_mono {ctx : Ctx} {term : String} {args : List V}
    {st next : State} {out : Option V} {trace : List RuleId}
    (h : Stock.runTerm ctx term args st = .ok (out, next, trace)) :
    ∀ (x : Nat), st.demand[x]! ≤ next.demand[x]! := by
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
        exact stock_apply_demand_mono ha

private theorem emitted_demand {ctx : Ctx} {i : Nat} {st : State}
    {emission : Emission}
    (h : emitInstruction ctx i st = .ok emission) : DemandMono st emission.state := by
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
          have same : final.demand = next.demand := binding_demandFields hb
          intro x
          rw [same]
          exact stock_named_demand_mono hr x


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


/-- Demand preservation for an actually retained emitted record follows from
its real normalized scan/emitter call, for every selected family. -/
theorem stock_lower_record_demand_mono {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted) :
    ∀ (x : Nat), record.input.demand[x]! ≤ record.output.state.demand[x]! := by
  obtain ⟨emission, call, output⟩ := stock_emitted_scan (record_execute run events records) recorded emitted
  have mono := emitted_demand call
  intro x
  rw [output]
  change record.input.demand[x]! ≤ emission.state.demand[x]!
  have count := mono x
  simpa only [scanState_demands] using count

attribute [local semireducible] Isle.Aarch64.program
set_option maxRecDepth 20000

/-- Actual scalar marking inhabits constructor/helper/named-root contracts.
A complete add lowering inhabits retained-record demand preservation. -/
theorem stock_demand_mono_witness :
    Stock.externCtor sinkCtx T.mark_value_used [.value 0] sinkState =
      .ok (.op .unit, sinkState.mark 0) ∧
    (applyTerm program (Stock.sem sinkCtx) {} 1 T.mark_value_used.ret T.mark_value_used.id [.value 0]).run
      (sinkState, #[]) = .ok (some (.op .unit), sinkState.mark 0, #[]) ∧
    Stock.runTerm sinkCtx "mark_value_used" [.value 0] sinkState =
      .ok (some (.op .unit), sinkState.mark 0, []) ∧
    (sinkState.mark 0).demand[0]! = 1 ∧
    (∀ (x : Nat), sinkState.demand[x]! ≤ (sinkState.mark 0).demand[x]! ∧
      sinkState.demand[x]! ≤ (sinkState.mark 0).demand[x]! ∧ sinkState.demand[x]! ≤ (sinkState.mark 0).demand[x]!) ∧
    ∃ (f : Clif.Function) (result : Result) (event : BlockScanEvent) (record : ScanRecord) (step : Step),
      Stock.lower f = .ok result ∧ event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧
      record.output.step = some step ∧ step.decision = .emitted ∧ record.inst = 0 ∧
      ∀ (x : Nat), record.input.demand[x]! ≤ record.output.state.demand[x]! := by
  have ctor : Stock.externCtor sinkCtx T.mark_value_used [.value 0] sinkState =
      .ok (.op .unit, sinkState.mark 0) := rfl
  have helper : (applyTerm program (Stock.sem sinkCtx) {} 1 T.mark_value_used.ret T.mark_value_used.id [.value 0]).run
      (sinkState, #[]) = .ok (some (.op .unit), sinkState.mark 0, #[]) := rfl
  have named : Stock.runTerm sinkCtx "mark_value_used" [.value 0] sinkState =
      .ok (some (.op .unit), sinkState.mark 0, []) := rfl
  have counts := stock_ctor_demand_mono ctor
  have countsHelper := stock_apply_demand_mono helper
  have countsNamed := stock_named_demand_mono named
  obtain ⟨result, event, record, step, run, scope, ssa, events, records, current, recorded, emitted, _, _, _⟩ :=
    stock_lower_record_fresh_result_witness
  exact ⟨ctor, helper, named, rfl, fun x => ⟨counts x, countsHelper x, countsNamed x⟩,
    _, result, event, record, step, run, events, records, recorded, emitted, current,
    stock_lower_record_demand_mono run events records recorded emitted⟩

end Backend.Stock.Proof
