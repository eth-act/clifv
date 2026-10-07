import FV.Backend.Proof.StockScan

/-!
Complete backward-scan certificates. `ScansSpec` records every requested source
instruction, the state chain, and forward assembly of its emitted chunks.
The producer's tail recursion refines a structural reference. Replay certifies
that reference from the same local transition checker used for single scans.
-/

namespace Backend.Stock.Proof

attribute [local irreducible] scanInstruction emitInstruction runTerm Isle.Aarch64.program

inductive ScansSpec (exec : Nat → State → Except String Scan) :
    List Nat → State → BlockScan → Prop where
  | nil (input : State) : ScansSpec exec [] input ⟨input, [], #[]⟩
  | cons {i : Nat} {indices : List Nat} {input : State} {scan : Scan} {tail : BlockScan}
      (head : exec i input = .ok scan) (rest : ScansSpec exec indices scan.state tail) :
      ScansSpec exec (i :: indices) input
        ⟨tail.state, ⟨i, input, scan⟩ :: tail.records, tail.code ++ scan.emitted⟩

def StateChain : State → List ScanRecord → State → Prop
  | input, [], final => final = input
  | input, record :: records, final =>
      record.input = input ∧ StateChain record.output.state records final

theorem ScansSpec.chain {exec : Nat → State → Except String Scan} {indices : List Nat}
    {input : State} {output : BlockScan} (h : ScansSpec exec indices input output) :
    StateChain input output.records output.state := by
  induction h with
  | nil input => rfl
  | cons head rest ih => exact ⟨rfl, ih⟩

theorem runScansAux_ref (exec : Nat → State → Except String Scan) (indices : List Nat)
    (input : State) (revRecords : List ScanRecord) (code : Array MInst) :
    runScansAux exec indices input revRecords code =
      match runScansRef exec indices input with
      | .error e => .error e
      | .ok result => .ok ⟨result.state, revRecords.reverse ++ result.records, result.code ++ code⟩ := by
  induction indices generalizing input revRecords code with
  | nil => simp only [runScansAux, runScansRef, List.append_nil, Array.empty_append]
  | cons i indices ih =>
    rw [runScansAux, runScansRef]
    cases he : exec i input with
    | error e => simp only [bind, Except.bind]
    | ok scan =>
      simp only [bind, Except.bind]
      rw [ih]
      cases hr : runScansRef exec indices scan.state with
      | error e => rfl
      | ok result =>
        simp only [pure, Except.pure, List.reverse_cons, List.append_assoc,
          List.cons_append, List.nil_append, Array.append_assoc]

theorem runScans_ref (exec : Nat → State → Except String Scan) (indices : List Nat)
    (input : State) : runScans exec indices input = runScansRef exec indices input := by
  rw [runScans, runScansAux_ref]
  cases hr : runScansRef exec indices input <;>
    simp only [List.reverse_nil, List.nil_append, Array.append_empty]

theorem runScansRef_spec {exec : Nat → State → Except String Scan} {indices : List Nat}
    {input : State} {output : BlockScan}
    (h : runScansRef exec indices input = .ok output) : ScansSpec exec indices input output := by
  induction indices generalizing input output with
  | nil => cases h; exact .nil input
  | cons i indices ih =>
    rw [runScansRef] at h
    cases he : exec i input with
    | error e => simp only [he, bind, Except.bind] at h; cases h
    | ok scan =>
      simp only [he, bind, Except.bind] at h
      cases ht : runScansRef exec indices scan.state with
      | error e => simp only [ht] at h; cases h
      | ok tail =>
        simp only [ht] at h
        cases h
        exact .cons he (ih ht)

theorem ScansSpec.runScansRef {exec : Nat → State → Except String Scan} {indices : List Nat}
    {input : State} {output : BlockScan} (h : ScansSpec exec indices input output) :
    runScansRef exec indices input = .ok output := by
  induction h with
  | nil input => rfl
  | cons head rest ih =>
    rw [Backend.Stock.runScansRef]
    simp only [head, ih, bind, Except.bind]
    rfl

theorem runScans_spec {exec : Nat → State → Except String Scan} {indices : List Nat}
    {input : State} {output : BlockScan} (h : runScans exec indices input = .ok output) :
    ScansSpec exec indices input output :=
  runScansRef_spec (by rwa [runScans_ref] at h)

theorem ScansSpec.order {exec : Nat → State → Except String Scan} {indices : List Nat}
    {input : State} {output : BlockScan} (h : ScansSpec exec indices input output) :
    output.records.map (·.inst) = indices := by
  induction h with
  | nil input => rfl
  | cons head rest ih => simp only [List.map_cons, ih]

theorem ScansSpec.code {exec : Nat → State → Except String Scan} {indices : List Nat}
    {input : State} {output : BlockScan} (h : ScansSpec exec indices input output) :
    output.code.toList = output.records.reverse.flatMap (fun r => r.output.emitted.toList) := by
  induction h with
  | nil input => rfl
  | cons head rest ih =>
    simp only [Array.toList_append, ih, List.reverse_cons, List.flatMap_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem replayScans_complete {exec : Nat → State → Except String Scan}
    {check : Nat → State → Scan → Bool}
    (hcheck : ∀ i input scan, exec i input = .ok scan → check i input scan = true)
    {indices : List Nat} {input : State} {output : BlockScan}
    (h : ScansSpec exec indices input output) :
    replayScans check indices input output.records = some (output.state, output.code) := by
  induction h with
  | nil input => rfl
  | @cons i indices input scan tail head rest ih =>
    rw [replayScans]
    have hrefl : decide (input ≠ input) = false := by simp
    simp only [bne_self_eq_false, hrefl, hcheck i input scan head, Bool.not_true,
      Bool.false_or, Bool.false_eq_true, ite_false, ih, bind, Option.bind]

theorem replayScans_sound {exec : Nat → State → Except String Scan}
    {check : Nat → State → Scan → Bool}
    (hcheck : ∀ i input scan, check i input scan = true → exec i input = .ok scan)
    {indices : List Nat} {input final : State} {records : List ScanRecord} {code : Array MInst}
    (h : replayScans check indices input records = some (final, code)) :
    ScansSpec exec indices input ⟨final, records, code⟩ := by
  induction indices generalizing input records final code with
  | nil =>
    cases records with
    | cons record records => cases h
    | nil => cases h; exact .nil input
  | cons i indices ih =>
    cases records with
    | nil => cases h
    | cons record records =>
      rcases record with ⟨ri, rin, scan⟩
      rw [replayScans] at h
      split at h
      · cases h
      · rename_i good
        simp only [Bool.or_eq_true, bne_iff_ne, decide_eq_true_eq, Bool.not_eq_true'] at good
        have hi : ri = i := Classical.byContradiction fun hn => good (Or.inl (Or.inl hn))
        have hin : rin = input := Classical.byContradiction fun hn => good (Or.inl (Or.inr hn))
        have hc : check i input scan = true := by
          cases hb : check i input scan with
          | true => rfl
          | false => exact False.elim (good (Or.inr hb))
        subst ri
        subst rin
        cases ht : replayScans check indices scan.state records with
        | none => simp only [ht, bind, Option.bind] at h; cases h
        | some pair =>
          rcases pair with ⟨last, tailCode⟩
          simp only [ht, bind, Option.bind] at h
          cases h
          exact .cons (hcheck i input scan hc) (ih ht)

theorem replayScansAux_ref (check : Nat → State → Scan → Bool) (indices : List Nat)
    (input : State) (records : List ScanRecord) (code : Array MInst) :
    replayScansAux check indices input records code =
      (replayScans check indices input records).map (fun (final, emitted) => (final, emitted ++ code)) := by
  induction indices generalizing input records code with
  | nil => cases records <;> simp only [replayScansAux, replayScans, Option.map, Array.empty_append]
  | cons i indices ih =>
    cases records with
    | nil => rfl
    | cons record records =>
      rw [replayScansAux, replayScans]
      split
      · rfl
      · rw [ih]
        cases ht : replayScans check indices record.output.state records with
        | none => rfl
        | some pair =>
          rcases pair with ⟨last, tailCode⟩
          simp only [bind, Option.bind, Option.map, Array.append_assoc]

theorem replayScansTail_ref (check : Nat → State → Scan → Bool) (indices : List Nat)
    (input : State) (records : List ScanRecord) :
    replayScansTail check indices input records = replayScans check indices input records := by
  rw [replayScansTail, replayScansAux_ref]
  cases hr : replayScans check indices input records with
  | none => rfl
  | some pair => rcases pair with ⟨last, code⟩; simp only [Option.map, Array.append_empty]

theorem checkScans_complete {exec : Nat → State → Except String Scan}
    {check : Nat → State → Scan → Bool}
    (hcheck : ∀ i input scan, exec i input = .ok scan → check i input scan = true)
    {indices : List Nat} {input : State} {output : BlockScan}
    (h : runScans exec indices input = .ok output) :
    checkScans check indices input output = true := by
  simp only [checkScans, replayScansTail_ref, replayScans_complete hcheck (runScans_spec h), decide_true]

theorem checkScans_sound {exec : Nat → State → Except String Scan}
    {check : Nat → State → Scan → Bool}
    (hcheck : ∀ i input scan, check i input scan = true → exec i input = .ok scan)
    {indices : List Nat} {input : State} {output : BlockScan}
    (h : checkScans check indices input output = true) :
    runScans exec indices input = .ok output := by
  simp only [checkScans, replayScansTail_ref, decide_eq_true_eq] at h
  have hs := replayScans_sound hcheck h
  rw [runScans_ref]
  exact hs.runScansRef

theorem checkBlockScan_complete {ctx : Ctx} {block ti : Nat} {isBranch : Bool}
    {indices : List Nat} {input : State} {output : BlockScan}
    (h : scanBlock ctx block ti isBranch indices input = .ok output) :
    checkBlockScan ctx block ti isBranch indices input output = true :=
  checkScans_complete (exec := fun i => scanInstruction ctx block i ti isBranch)
    (check := fun i => checkScan ctx block i ti isBranch)
    (fun _ _ _ hs => checkScan_complete hs) h

theorem checkBlockScan_sound {ctx : Ctx} {block ti : Nat} {isBranch : Bool}
    {indices : List Nat} {input : State} {output : BlockScan}
    (h : checkBlockScan ctx block ti isBranch indices input output = true) :
    scanBlock ctx block ti isBranch indices input = .ok output :=
  checkScans_sound (exec := fun i => scanInstruction ctx block i ti isBranch)
    (check := fun i => checkScan ctx block i ti isBranch)
    (fun _ _ _ hs => checkScan_sound hs) h

theorem blockScanEvent_complete (event : BlockScanEvent)
    (hsource : scanSource? event.ctx.func event.block =
      some ⟨event.termInst, event.isBranch, event.indices⟩)
    (h : scanBlock event.ctx event.block event.termInst event.isBranch event.indices
      event.input = .ok event.output) : event.check = true := by
  simp only [BlockScanEvent.check, hsource, decide_true, Bool.true_and]
  exact checkBlockScan_complete h

theorem blockScanEvent_sound {event : BlockScanEvent} (h : event.check = true) :
    scanSource? event.ctx.func event.block =
      some ⟨event.termInst, event.isBranch, event.indices⟩ ∧
    scanBlock event.ctx event.block event.termInst event.isBranch event.indices
      event.input = .ok event.output := by
  cases hs : scanSource? event.ctx.func event.block with
  | none => simp only [BlockScanEvent.check, hs, Bool.false_eq_true] at h
  | some source =>
    simp only [BlockScanEvent.check, hs, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨congrArg some h.1, checkBlockScan_sound h.2⟩

theorem blockScanEvent_reject_source {event : BlockScanEvent}
    (h : scanSource? event.ctx.func event.block ≠
      some ⟨event.termInst, event.isBranch, event.indices⟩) : event.check = false := by
  cases hc : event.check with
  | false => rfl
  | true => exact False.elim (h (blockScanEvent_sound hc).1)

/-- Any alteration of the complete output (records, final state or code) fails
replay when the local checker is sound. -/
theorem checkScans_reject {exec : Nat → State → Except String Scan}
    {check : Nat → State → Scan → Bool}
    (hcheck : ∀ i input scan, check i input scan = true → exec i input = .ok scan)
    {indices : List Nat} {input : State} {actual output : BlockScan}
    (h : runScans exec indices input = .ok actual) (hne : actual ≠ output) :
    checkScans check indices input output = false := by
  cases hc : checkScans check indices input output with
  | false => rfl
  | true => exact False.elim (hne (Except.ok.inj (h.symm.trans (checkScans_sound hcheck hc))))

/-! Concrete witnesses have two transitions and two instructions per chunk.
They exercise state chaining and the reversal of chunks without reversing the
instructions within a chunk. The stock fixture uses previously sunk producers,
so neither fixture evaluates the generated ISLE program. -/

private def toyScan (i : Nat) (input : State) : Scan :=
  ⟨{ input with current := some i }, none, #[.jump (2 * i), .jump (2 * i + 1)]⟩

private def toyExec (i : Nat) (input : State) : Except String Scan := .ok (toyScan i input)

private def toyCheck (i : Nat) (input : State) (scan : Scan) : Bool :=
  decide (toyScan i input = scan)

private def toyOutput : BlockScan :=
  let first := toyScan 2 unusedInput
  let last := toyScan 1 first.state
  ⟨last.state, [⟨2, unusedInput, first⟩, ⟨1, first.state, last⟩], last.emitted ++ first.emitted⟩

private theorem toyCheck_complete (i : Nat) (input : State) (scan : Scan)
    (h : toyExec i input = .ok scan) : toyCheck i input scan = true := by
  cases h
  simp only [toyCheck, decide_true]

private theorem toyCheck_sound (i : Nat) (input : State) (scan : Scan)
    (h : toyCheck i input scan = true) : toyExec i input = .ok scan := by
  simp only [toyCheck, decide_eq_true_eq] at h
  exact congrArg Except.ok h

private theorem toySpec : ScansSpec toyExec [2, 1] unusedInput toyOutput :=
  ScansSpec.cons (exec := toyExec) (i := 2) (scan := toyScan 2 unusedInput)
    (tail := ⟨(toyScan 1 (toyScan 2 unusedInput).state).state,
      [⟨1, (toyScan 2 unusedInput).state, toyScan 1 (toyScan 2 unusedInput).state⟩],
      (toyScan 1 (toyScan 2 unusedInput).state).emitted⟩) rfl
    (ScansSpec.cons (exec := toyExec) (i := 1)
      (scan := toyScan 1 (toyScan 2 unusedInput).state)
      (tail := ⟨(toyScan 1 (toyScan 2 unusedInput).state).state, [], #[]⟩) rfl (.nil _))

private theorem toyRef : runScansRef toyExec [2, 1] unusedInput = .ok toyOutput :=
  toySpec.runScansRef

private theorem toyRun : runScans toyExec [2, 1] unusedInput = .ok toyOutput := by
  rw [runScans_ref]
  exact toyRef

theorem runScansAux_ref_witness :
    runScansAux toyExec [2, 1] unusedInput toyOutput.records.reverse #[.jump 99] =
      .ok ⟨toyOutput.state, toyOutput.records ++ toyOutput.records,
        toyOutput.code ++ #[.jump 99]⟩ := by
  rw [runScansAux_ref, toyRef, List.reverse_reverse]

theorem runScans_ref_witness :
    runScans toyExec [2, 1] unusedInput = runScansRef toyExec [2, 1] unusedInput ∧
    runScans toyExec [2, 1] unusedInput = .ok toyOutput :=
  ⟨runScans_ref _ _ _, toyRun⟩

theorem runScansRef_spec_witness :
    runScansRef toyExec [2, 1] unusedInput = .ok toyOutput ∧
    ScansSpec toyExec [2, 1] unusedInput toyOutput :=
  ⟨toyRef, runScansRef_spec toyRef⟩

theorem ScansSpec.runScansRef_witness :
    ScansSpec toyExec [2, 1] unusedInput toyOutput ∧
    Backend.Stock.runScansRef toyExec [2, 1] unusedInput = .ok toyOutput :=
  ⟨toySpec, toySpec.runScansRef⟩

theorem runScans_spec_witness :
    runScans toyExec [2, 1] unusedInput = .ok toyOutput ∧
    ScansSpec toyExec [2, 1] unusedInput toyOutput :=
  ⟨toyRun, runScans_spec toyRun⟩

theorem ScansSpec.order_witness :
    ScansSpec toyExec [2, 1] unusedInput toyOutput ∧
    toyOutput.records.map (·.inst) = [2, 1] :=
  ⟨toySpec, toySpec.order⟩

theorem ScansSpec.chain_witness :
    StateChain unusedInput toyOutput.records toyOutput.state ∧
    toyOutput.records[1]!.input.current = some 2 ∧
    toyOutput.records[1]!.output.state.current = some 1 :=
  ⟨toySpec.chain, rfl, rfl⟩

theorem ScansSpec.code_witness :
    toyOutput.code.toList = toyOutput.records.reverse.flatMap (fun r => r.output.emitted.toList) ∧
    toyOutput.code = #[.jump 2, .jump 3, .jump 4, .jump 5] ∧
    toyOutput.state.current = some 1 :=
  ⟨toySpec.code, rfl, rfl⟩

theorem replayScans_complete_witness :
    (∀ i input scan, toyExec i input = .ok scan → toyCheck i input scan = true) ∧
    replayScans toyCheck [2, 1] unusedInput toyOutput.records =
      some (toyOutput.state, toyOutput.code) :=
  ⟨toyCheck_complete, replayScans_complete toyCheck_complete toySpec⟩

theorem replayScans_sound_witness :
    (∀ i input scan, toyCheck i input scan = true → toyExec i input = .ok scan) ∧
    ScansSpec toyExec [2, 1] unusedInput toyOutput :=
  ⟨toyCheck_sound, replayScans_sound toyCheck_sound replayScans_complete_witness.2⟩

theorem replayScansAux_ref_witness :
    replayScansAux toyCheck [2, 1] unusedInput toyOutput.records #[.jump 99] =
      some (toyOutput.state, toyOutput.code ++ #[.jump 99]) := by
  rw [replayScansAux_ref, replayScans_complete_witness.2]
  rfl

theorem replayScansTail_ref_witness :
    replayScansTail toyCheck [2, 1] unusedInput toyOutput.records =
      replayScans toyCheck [2, 1] unusedInput toyOutput.records ∧
    replayScansTail toyCheck [2, 1] unusedInput toyOutput.records =
      some (toyOutput.state, toyOutput.code) :=
  ⟨replayScansTail_ref _ _ _ _, by rw [replayScansTail_ref]; exact replayScans_complete_witness.2⟩

theorem checkScans_complete_witness :
    runScans toyExec [2, 1] unusedInput = .ok toyOutput ∧
    checkScans toyCheck [2, 1] unusedInput toyOutput = true :=
  ⟨toyRun, checkScans_complete toyCheck_complete toyRun⟩

theorem checkScans_sound_witness :
    checkScans toyCheck [2, 1] unusedInput toyOutput = true ∧
    runScans toyExec [2, 1] unusedInput = .ok toyOutput :=
  ⟨checkScans_complete_witness.2, checkScans_sound toyCheck_sound checkScans_complete_witness.2⟩

theorem checkScans_reject_witness :
    checkScans toyCheck [2, 1] unusedInput { toyOutput with records := toyOutput.records.tail } = false ∧
    checkScans toyCheck [2, 1] unusedInput { toyOutput with records := toyOutput.records.reverse } = false ∧
    checkScans toyCheck [2, 1] unusedInput
      { toyOutput with state := { toyOutput.state with current := some 9 } } = false ∧
    checkScans toyCheck [2, 1] unusedInput
      { toyOutput with code := #[.jump 5, .jump 4, .jump 3, .jump 2] } = false :=
  ⟨checkScans_reject toyCheck_sound toyRun
      (fun h => (by decide : (2 : Nat) ≠ 1) (congrArg (fun r => r.records.length) h)),
   checkScans_reject toyCheck_sound toyRun
      (fun h => (by decide : (2 : Nat) ≠ 1) (congrArg (fun r => r.records.head!.inst) h)),
   checkScans_reject toyCheck_sound toyRun
      (fun h => (by decide : (some 1 : Option Nat) ≠ some 9) (congrArg (fun r => r.state.current) h)),
   checkScans_reject toyCheck_sound toyRun
      (fun h => (by decide : ([2, 3, 4, 5] : List Nat) ≠ [5, 4, 3, 2])
        (congrArg (fun r => r.code.toList.map (fun | .jump n => n | _ => 0)) h))⟩

private def sunkInput : State := { unusedInput with sunk := #[true, true] }

private def sunkScan (i : Nat) : Scan :=
  ⟨sunkInput, some ⟨0, i, .sunk, sunkInput, sunkInput, [], [], #[]⟩, #[]⟩

private def sunkOutput : BlockScan :=
  ⟨sunkInput, [⟨1, sunkInput, sunkScan 1⟩, ⟨0, sunkInput, sunkScan 0⟩], #[]⟩

private theorem sunkRun : scanBlock unusedCtx 0 2 false [1, 0] sunkInput = .ok sunkOutput := by
  unfold scanBlock
  rw [runScans_ref]
  exact (ScansSpec.cons (exec := fun i => scanInstruction unusedCtx 0 i 2 false)
    (i := 1) (scan := sunkScan 1)
    (tail := ⟨sunkInput, [⟨0, sunkInput, sunkScan 0⟩], #[]⟩)
    (scan_sunk unusedCtx 0 1 2 false sunkInput rfl)
    (ScansSpec.cons (exec := fun i => scanInstruction unusedCtx 0 i 2 false)
      (i := 0) (scan := sunkScan 0) (tail := ⟨sunkInput, [], #[]⟩)
      (scan_sunk unusedCtx 0 0 2 false sunkInput rfl) (.nil _))).runScansRef

theorem checkBlockScan_complete_witness :
    scanBlock unusedCtx 0 2 false [1, 0] sunkInput = .ok sunkOutput ∧
    checkBlockScan unusedCtx 0 2 false [1, 0] sunkInput sunkOutput = true :=
  ⟨sunkRun, checkBlockScan_complete sunkRun⟩

theorem checkBlockScan_sound_witness :
    checkBlockScan unusedCtx 0 2 false [1, 0] sunkInput sunkOutput = true ∧
    scanBlock unusedCtx 0 2 false [1, 0] sunkInput = .ok sunkOutput :=
  ⟨checkBlockScan_complete_witness.2, checkBlockScan_sound checkBlockScan_complete_witness.2⟩

private def eventFunction : Clif.Function := {
  name := "block_scan_witness"
  sig := default
  blocks := [{
    id := 7
    params := [(1, .i64)]
    body := [⟨[0], .load .load .i8 { trapCode := none } 1 0⟩]
    term := .jump ⟨7, [1]⟩ }] }

private def eventCtx : Ctx := { unusedCtx with
  func := eventFunction
  insts := unusedCtx.insts.push ⟨.op .unit, [], [], none⟩ }

private def eventInput : State := { unusedInput with sunk := #[true, false] }

private def eventBefore : State := scanState eventInput 1

private def eventOutput : BlockScan :=
  ⟨eventBefore,
    [⟨1, eventInput, ⟨eventBefore, none, #[]⟩⟩,
     ⟨0, eventBefore,
       ⟨eventBefore, some ⟨0, 0, .sunk, eventBefore, eventBefore, [], [], #[]⟩, #[]⟩⟩], #[]⟩

private def sourceEvent : BlockScanEvent :=
  ⟨eventCtx, 0, 1, true, [1, 0], eventInput, eventOutput⟩

private theorem sourceEvent_run :
    scanBlock eventCtx 0 1 true [1, 0] eventInput = .ok eventOutput := by
  unfold scanBlock
  rw [runScans_ref]
  exact (ScansSpec.cons (exec := fun i => scanInstruction eventCtx 0 i 1 true)
    (i := 1) (scan := ⟨eventBefore, none, #[]⟩)
    (tail := ⟨eventBefore,
      [⟨0, eventBefore,
        ⟨eventBefore, some ⟨0, 0, .sunk, eventBefore, eventBefore, [], [], #[]⟩, #[]⟩⟩], #[]⟩)
    (by unfold scanInstruction; rfl)
    (ScansSpec.cons (exec := fun i => scanInstruction eventCtx 0 i 1 true)
      (i := 0)
      (scan := ⟨eventBefore, some ⟨0, 0, .sunk, eventBefore, eventBefore, [], [], #[]⟩, #[]⟩)
      (tail := ⟨eventBefore, [], #[]⟩)
      (scan_sunk eventCtx 0 0 1 true eventBefore rfl) (.nil _))).runScansRef

theorem blockScanEvent_complete_witness :
    scanSource? eventCtx.func 0 = some ⟨1, true, [1, 0]⟩ ∧
    scanBlock eventCtx 0 1 true [1, 0] eventInput = .ok eventOutput ∧
    sourceEvent.check = true :=
  ⟨by decide, sourceEvent_run,
    blockScanEvent_complete sourceEvent (by decide) sourceEvent_run⟩

theorem blockScanEvent_sound_witness :
    sourceEvent.check = true ∧
    scanSource? sourceEvent.ctx.func sourceEvent.block =
      some ⟨sourceEvent.termInst, sourceEvent.isBranch, sourceEvent.indices⟩ ∧
    scanBlock sourceEvent.ctx sourceEvent.block sourceEvent.termInst sourceEvent.isBranch
      sourceEvent.indices sourceEvent.input = .ok sourceEvent.output :=
  ⟨blockScanEvent_complete_witness.2.2, blockScanEvent_sound blockScanEvent_complete_witness.2.2⟩

theorem blockScanEvent_reject_source_witness :
    ({ sourceEvent with indices := [1] } : BlockScanEvent).check = false ∧
    ({ sourceEvent with termInst := 2 } : BlockScanEvent).check = false ∧
    ({ sourceEvent with isBranch := false } : BlockScanEvent).check = false ∧
    ({ sourceEvent with block := 1 } : BlockScanEvent).check = false :=
  ⟨blockScanEvent_reject_source (by decide), blockScanEvent_reject_source (by decide),
    blockScanEvent_reject_source (by decide), blockScanEvent_reject_source (by decide)⟩

end Backend.Stock.Proof
