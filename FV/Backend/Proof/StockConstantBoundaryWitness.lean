import FV.Backend.Proof.StockRecordContext
import FV.Backend.Proof.LowerCertBase
import FV.Backend.Proof.LowerDecide
import FV.Backend.Proof.StockScanSemantics

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

private def exampleFunction : Clif.Function := {
  name := "constant_record_values"
  sig := { params := [⟨.i64, .none, .normal⟩], returns := [⟨.i64, .none, .normal⟩, ⟨.i8, .none, .normal⟩], callConv := some .systemV }
  blocks := [{id := 0, params := [(7, .i64)], body := [⟨[2], .iconst .i8 9⟩], term := .ret [7, 2]}] }
private theorem exampleScope : LowerScope exampleFunction := lowerScope_of (by decide +kernel)
private theorem exampleDominated : Dominated exampleFunction := by
  constructor
  · decide +kernel
  · intro ctx ranges st build bi b block
    cases bi with
    | zero =>
      simp [exampleFunction] at block
      subst b
      constructor
      · intro j stm statement y member
        cases j <;> simp at statement
        subst stm
        simp [Backend.Proof.Driver.instArgs] at member
      · intro y member
        change y ∈ [7, 2] at member
        change y ∈ (([7] ++ (availIn exampleFunction ctx).getD 0 [] ++ [2]).filter
          (fun x => decide (x ∉ ([] : List Nat))))
        simp only [List.mem_filter, decide_eq_true_eq, List.not_mem_nil, not_false_eq_true, and_true]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl <;> simp
    | succ bi => simp [exampleFunction] at block
  · intro ctx ranges st build tl x available notLocal y member
    have bounds := (inFix_fixOk (f := exampleFunction) (ctx := ctx) (gn := id)).cand tl x available
    have length : exampleFunction.blocks.length = 1 := rfl
    omega
private def exampleFrame : Clif.Frame := {
  func := exampleFunction
  regs := fun x => if x = 2 then some (.ofInt .i8 77)
    else if x = 7 then some (.ofInt .i64 11) else none
  slots := [], body := [⟨[2], .iconst .i8 9⟩], term := .ret [7, 2] }
private def exampleRegs (n : Nat) : CV := if n = 192 then 11 else 0
private theorem exampleAvailable (ctx : Ctx) :
    ∀ y, y ∈ availOf exampleFunction (availIn exampleFunction ctx) 0 0 ↔ y = 7 := by
  intro y
  have entryEmpty : y ∉ (availIn exampleFunction ctx).getD 0 [] := by
    intro member
    have bounded := (inFix_fixOk (f := exampleFunction) (ctx := ctx) (gn := id)).cand 0 y member
    omega
  rw [mem_av (show exampleFunction.blocks[0]? = some
    ({id := 0, params := [(7, .i64)], body := [⟨[2], .iconst .i8 9⟩], term := .ret [7, 2]} : Clif.Block) from rfl)]
  constructor
  · intro required
    rcases required.1 with param | entry | ⟨k, stm, earlier, _, _⟩
    · exact List.mem_singleton.mp param
    · exact False.elim (entryEmpty entry)
    · omega
  · intro equal
    subst y
    refine ⟨Or.inl (by simp), ?_⟩
    intro ⟨k, stm, _, statement, member⟩
    cases k <;> simp at statement
    subst stm
    simp at member

private theorem exampleObserved : (Stock.lower exampleFunction).toOption.map (fun result =>
    (aliasNum result.final.alias 192, aliasNum result.final.alias 193,
      result.blockScans.toList.any (fun event => event.output.records.any (fun record =>
        record.inst == 0 && record.input.base.nextVreg == 194 &&
        record.input.demand[2]! != 0 &&
        record.output.step.any (fun step => step.decision == .emitted) &&
        decide ((event.ctx.insts[0]?).map (fun info => (info.clif, info.results)) =
          some (some (.iconst .i8 9), [2])) &&
        decide (event.ctx.valueReg? 7 = some (.vreg 192 .int)) &&
        decide (event.ctx.valueReg? 2 = some (.vreg 193 .int)))))) = some (192, 194, true) := by
  decide +kernel


/-- Reusable inhabited boundary for the saved constant record. The stale result
and live parameter are retained; consumers derive selection receipts themselves. -/
theorem stock_lower_constant_record_boundary_witness :
    ∃ (f : Clif.Function) (result : Result) (event : BlockScanEvent) (record : ScanRecord)
      (b : Clif.Block) (info : IInfo) (step : Step) (fr fr' : Clif.Frame) (ρ : Nat → CV),
      Stock.lower f = .ok result ∧ LowerScope f ∧ Dominated f ∧
      event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧
      f.blocks[0]? = some b ∧
      b.body[0]? = some (⟨[2],.iconst .i8 9⟩ : Clif.Stmt) ∧
      record.inst = blockStart f 0 + 0 ∧
      event.ctx.insts[record.inst]? = some info ∧ info.clif = some (.iconst .i8 9) ∧
      info.results = [2] ∧ event.ctx.valueReg? 2 = some (.vreg 193 .int) ∧
      record.output.step = some step ∧ step.decision = .emitted ∧
      SourceInstResult Clif.Env.empty {funcs := []} event.ctx record.inst
        (fr,Clif.Mem.empty) (fr',Clif.Mem.empty) ∧
      ValuesHeld (fun y => Demanded record.output.state y ∧
        y ∈ availOf f (availIn f result.ctx) 0 0) event.ctx fr
          (fun k => ρ (aliasNum result.final.alias k)) := by
  have observed := exampleObserved
  cases run : Stock.lower exampleFunction with
  | error e => simp only [run, Except.toOption, Option.map_none] at observed; cases observed
  | ok result =>
    simp only [run, Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at observed
    obtain ⟨parameterResolved, resultResolved, found⟩ := observed
    obtain ⟨event, events, record, records, current, frontier, demanded, selected, infoData, parameterMap, resultMap⟩ :=
      (by simpa only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, decide_eq_true_eq, and_assoc] using found :
        ∃ event ∈ result.blockScans.toList, ∃ record ∈ event.output.records,
          record.inst = 0 ∧ record.input.base.nextVreg = 194 ∧ record.input.demand[2]! ≠ 0 ∧
          record.output.step.any (fun step => step.decision == .emitted) = true ∧
          (event.ctx.insts[0]?).map (fun info => (info.clif, info.results)) = some (some (.iconst .i8 9), [2]) ∧
          event.ctx.valueReg? 7 = some (.vreg 192 .int) ∧ event.ctx.valueReg? 2 = some (.vreg 193 .int))
    obtain ⟨step, recorded, emitted⟩ := (by simpa only [Option.any_eq_true, beq_iff_eq] using selected :
      ∃ step, record.output.step = some step ∧ step.decision = .emitted)
    obtain ⟨info, source, clif, results⟩ := (by
      simpa only [Option.map_eq_some_iff, Prod.mk.injEq] using infoData :
        ∃ info, event.ctx.insts[0]? = some info ∧ info.clif = some (.iconst .i8 9) ∧ info.results = [2])
    have context := (stock_lower_record_context run exampleScope events).1
    have held : ValuesHeld (fun y => Demanded record.output.state y ∧
        y ∈ availOf exampleFunction (availIn exampleFunction result.ctx) 0 0) event.ctx exampleFrame
          (fun k => exampleRegs (aliasNum result.final.alias k)) := by
      intro y required val lookup
      have equal := (exampleAvailable result.ctx y).mp required.2
      subst y
      change some (Clif.Val.ofInt .i64 11) = some val at lookup
      cases lookup
      refine ⟨192, parameterMap, ?_⟩
      change VHolds (.ofInt .i64 11) (exampleRegs (aliasNum result.final.alias 192))
      rw [parameterResolved]
      unfold VHolds exampleRegs
      decide +kernel
    let fr' : Clif.Frame := {exampleFrame with regs := exampleFrame.regs.set 2 (.ofInt .i8 9), body := []}
    have sourceStep : SourceInstResult Clif.Env.empty {funcs := []} event.ctx record.inst
        (exampleFrame, Clif.Mem.empty) (fr', Clif.Mem.empty) :=
      ⟨info, .iconst .i8 9, [.ofInt .i8 9], exampleFrame.regs.set 2 (.ofInt .i8 9), [],
        by simpa only [current] using source, clif, by rw [results]; rfl,
        rfl, by rw [results]; rfl, rfl⟩
    exact ⟨exampleFunction,result,event,record,exampleFunction.blocks[0]!,info,step,
      exampleFrame,fr',exampleRegs,run,exampleScope,exampleDominated,events,records,
      rfl,rfl,by simpa only [blockStart,List.take_zero,List.map_nil,List.sum_nil,Nat.zero_add] using current,
      by simpa only [current] using source,clif,results,resultMap,recorded,emitted,sourceStep,held⟩

end Backend.Stock.Proof
