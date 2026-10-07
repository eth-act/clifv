import FV.Backend.Lowering.StockReplay
import FV.Backend.Proof.StockPolicy

/-!
Local replay and policy facts for backward scanning. Replay acceptance certifies
the complete transition, including emitted code and all scheduling state. These
lemmas are ingredients of the replacement schedule proof; they do not assert
whole-function semantic refinement.
-/

namespace Backend.Stock.Proof

attribute [local irreducible] emitInstruction runTerm Isle.Aarch64.program

theorem checkScan_complete {ctx : Ctx} {block i ti : Nat} {isBranch : Bool}
    {input : State} {output : Scan}
    (h : scanInstruction ctx block i ti isBranch input = .ok output) :
    checkScan ctx block i ti isBranch input output = true := by
  simp only [checkScan, h, decide_true]

theorem checkScan_sound {ctx : Ctx} {block i ti : Nat} {isBranch : Bool}
    {input : State} {output : Scan}
    (h : checkScan ctx block i ti isBranch input output = true) :
    scanInstruction ctx block i ti isBranch input = .ok output := by
  cases hs : scanInstruction ctx block i ti isBranch input with
  | error e => simp only [checkScan, hs, Bool.false_eq_true] at h
  | ok actual =>
    simp only [checkScan, hs, decide_eq_true_eq] at h
    subst actual
    rfl

theorem scanState_idempotent (input : State) (i : Nat) :
    scanState (scanState input i) i = scanState input i := by
  cases hc : input.entryColor[i]! != 0 <;>
    simp only [scanState, hc, Bool.false_eq_true, ite_false, ite_true]

theorem scanState_demands (input : State) (i : Nat) :
    (scanState input i).demand = input.demand := by
  unfold scanState
  dsimp only
  split <;> rfl

/-- Omission cannot remove a terminator, a mandatory effect, or a result with
outstanding register demand. Its state change is only scan normalization. -/
theorem scan_omitted {ctx : Ctx} {block i ti : Nat} {isBranch : Bool}
    {input : State} {output : Scan} {step : Step}
    (h : scanInstruction ctx block i ti isBranch input = .ok output)
    (hs : output.step = some step) (hd : step.decision = .omitted) :
    i ≠ ti ∧ ctx.insts[i]!.clif.any mustLower = false ∧
    (∀ v ∈ ctx.insts[i]!.results, input.demand[v]! = 0) ∧
    step.before = scanState input i ∧ step.after = step.before ∧
    step.results = [] ∧ step.rules = [] ∧ output.emitted = #[] := by
  have rejectEmission (before : State)
      (he : (emitInstruction ctx i before >>= fun e => pure (e.scan block i before)) =
        .ok output) : False := by
    cases hr : emitInstruction ctx i before with
    | error e => simp only [hr, bind, Except.bind] at he; cases he
    | ok emission =>
      simp only [hr, bind, Except.bind] at he
      cases he
      cases hs
      cases hd
  by_cases hsink : input.sunk[i]! = true
  · simp only [scanInstruction, hsink, ite_true] at h
    cases h
    cases hs
    cases hd
  · simp only [scanInstruction, hsink] at h
    by_cases hti : i = ti
    · subst ti
      cases isBranch <;>
        simp only [beq_self_eq_true, Bool.true_and, Bool.false_eq_true, ite_false,
          ite_true, Bool.not_true, Bool.false_and, Bool.and_false] at h
      · exact False.elim (rejectEmission (scanState input i) h)
      · cases h; cases hs
    · have hbeq : (i == ti) = false := by
        cases he : i == ti
        · rfl
        · simp only [beq_iff_eq] at he
          exact False.elim (hti he)
      simp only [hbeq, Bool.false_and, Bool.false_eq_true, ite_false] at h
      split at h
      · rename_i eligible
        cases h
        cases hs
        simp only [Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false] at eligible
        refine ⟨hti, eligible.1, ?_, rfl, rfl, rfl, rfl, rfl⟩
        intro v hv
        have hv0 := eligible.2 v hv
        exact Classical.byContradiction fun hne =>
          hv0 (by simpa only [scanState_demands, bne_iff_ne] using hne)
      · split at h
        · cases hc : commitOpportunistic ctx block i (scanState input i) with
          | error e => simp only [hc, bind, Except.bind] at h; cases h
          | ok result =>
            simp only [hc, bind, Except.bind] at h
            cases result with
            | some next => cases h; cases hs; cases hd
            | none => exact False.elim (rejectEmission (scanState input i) h)
        · exact False.elim (rejectEmission (scanState input i) h)

theorem scan_sunk (ctx : Ctx) (block i ti : Nat) (isBranch : Bool) (input : State)
    (h : input.sunk[i]! = true) :
    scanInstruction ctx block i ti isBranch input =
      .ok ⟨input, some ⟨block, i, .sunk, input, input, [], [], #[]⟩, #[]⟩ := by
  simp only [scanInstruction, h, ite_true]
  rfl

/-- A demanded result cannot have an accepted omitted transition, even when
the supplied certificate claims empty code and a successful result. -/
theorem checkScan_reject_demanded {ctx : Ctx} {block i ti v : Nat} {isBranch : Bool}
    {input : State} {output : Scan} {step : Step}
    (hs : output.step = some step) (hd : step.decision = .omitted)
    (hv : v ∈ ctx.insts[i]!.results) (hne : input.demand[v]! ≠ 0) :
    checkScan ctx block i ti isBranch input output = false := by
  cases hc : checkScan ctx block i ti isBranch input output with
  | false => rfl
  | true =>
    exact False.elim (hne ((scan_omitted (checkScan_sound hc) hs hd).2.2.1 v hv))

/-- Neither a terminator nor a mandatory effect can have an accepted omitted
transition. This guard is independent of whether its outputs are used. -/
theorem checkScan_reject_mandatory {ctx : Ctx} {block i ti : Nat} {isBranch : Bool}
    {input : State} {output : Scan} {step : Step}
    (hs : output.step = some step) (hd : step.decision = .omitted)
    (hm : i = ti ∨ ctx.insts[i]!.clif.any mustLower = true) :
    checkScan ctx block i ti isBranch input output = false := by
  cases hc : checkScan ctx block i ti isBranch input output with
  | false => rfl
  | true =>
    have facts := scan_omitted (checkScan_sound hc) hs hd
    cases hm with
    | inl he => exact False.elim (facts.1 he)
    | inr he => rw [facts.2.1] at he; cases he

theorem checkScan_reject_code {ctx : Ctx} {block i ti : Nat} {isBranch : Bool}
    {input : State} {actual output : Scan}
    (h : scanInstruction ctx block i ti isBranch input = .ok actual)
    (hcode : actual.emitted ≠ output.emitted) :
    checkScan ctx block i ti isBranch input output = false := by
  cases hc : checkScan ctx block i ti isBranch input output with
  | false => rfl
  | true =>
    have heq := Except.ok.inj (h.symm.trans (checkScan_sound hc))
    exact False.elim (hcode (congrArg Scan.emitted heq))

/-! An unused nontrapping load may be omitted, whereas a sunk load records its
prior sink and leaves the state untouched. These witnesses make no ISLE call. -/

def unusedCtx : Ctx := { sinkCtx with
  insts := #[⟨.op .unit, [0], [.int 8], some (.load .load .i8 { trapCode := none } 1 0)⟩] }

def unusedInput : State := { sinkState with current := none }

def unusedOutput : Scan :=
  let st := scanState unusedInput 0
  ⟨st, some ⟨0, 0, .omitted, st, st, [], [], #[]⟩, #[]⟩

def unusedStep : Step := (unusedOutput.step).getD default

theorem checkScan_complete_witness :
    scanInstruction unusedCtx 0 0 1 false unusedInput = .ok unusedOutput ∧
    checkScan unusedCtx 0 0 1 false unusedInput unusedOutput = true :=
  ⟨rfl, checkScan_complete (show scanInstruction unusedCtx 0 0 1 false unusedInput =
    .ok unusedOutput from rfl)⟩

theorem checkScan_sound_witness :
    checkScan unusedCtx 0 0 1 false unusedInput unusedOutput = true ∧
    scanInstruction unusedCtx 0 0 1 false unusedInput = .ok unusedOutput :=
  ⟨checkScan_complete_witness.2, checkScan_sound checkScan_complete_witness.2⟩

theorem scanState_idempotent_witness :
    scanState (scanState unusedInput 0) 0 = scanState unusedInput 0 ∧
    (scanState unusedInput 0).current = some 0 ∧
    (scanState unusedInput 0).color = some 1 :=
  ⟨scanState_idempotent _ _, rfl, rfl⟩

theorem scanState_demands_witness :
    (scanState unusedInput 0).demand = unusedInput.demand ∧ unusedInput.demand = #[0, 0] :=
  ⟨scanState_demands _ _, rfl⟩

theorem scan_omitted_witness :
    (0 : Nat) ≠ 1 ∧ unusedCtx.insts[0]!.clif.any mustLower = false ∧
    (∀ v ∈ unusedCtx.insts[0]!.results, unusedInput.demand[v]! = 0) ∧
    unusedStep.before = scanState unusedInput 0 ∧ unusedStep.after = unusedStep.before ∧
    unusedStep.results = [] ∧ unusedStep.rules = [] ∧ unusedOutput.emitted = #[] :=
  scan_omitted checkScan_complete_witness.1 (show unusedOutput.step = some unusedStep from rfl)
    (show unusedStep.decision = .omitted from rfl)

theorem scan_sunk_witness :
    sinkNext.sunk[0]! = true ∧
    scanInstruction sinkCtx 0 0 1 false sinkNext =
      .ok ⟨sinkNext, some ⟨0, 0, .sunk, sinkNext, sinkNext, [], [], #[]⟩, #[]⟩ :=
  ⟨rfl, scan_sunk _ _ _ _ _ _ rfl⟩

theorem checkScan_reject_demanded_witness :
    checkScan unusedCtx 0 0 1 false { unusedInput with demand := #[1, 0] } unusedOutput = false :=
  checkScan_reject_demanded (show unusedOutput.step = some unusedStep from rfl)
    (show unusedStep.decision = .omitted from rfl) (v := 0)
    (show 0 ∈ unusedCtx.insts[0]!.results from by decide) (by decide)

theorem checkScan_reject_mandatory_witness :
    checkScan sinkCtx 0 0 1 false unusedInput unusedOutput = false ∧
    checkScan unusedCtx 0 0 0 false unusedInput unusedOutput = false :=
  ⟨checkScan_reject_mandatory (show unusedOutput.step = some unusedStep from rfl)
      (show unusedStep.decision = .omitted from rfl) (Or.inr rfl),
    checkScan_reject_mandatory (show unusedOutput.step = some unusedStep from rfl)
      (show unusedStep.decision = .omitted from rfl) (Or.inl rfl)⟩

theorem checkScan_reject_code_witness :
    checkScan unusedCtx 0 0 1 false unusedInput
      { unusedOutput with emitted := #[.jump 0] } = false :=
  checkScan_reject_code checkScan_complete_witness.1 (by decide)

end Backend.Stock.Proof
