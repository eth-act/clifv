import FV.Backend.Proof.StockAcquireOpportunisticColors

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitInstruction

private theorem bind_success {α β : Type} {value : Except String α} {next : α → Except String β} {output : β}
    (run : (value >>= next) = .ok output) : ∃ input,value = .ok input ∧ next input = .ok output := by
  cases value with
  | error message => cases run
  | ok input => exact ⟨input,rfl,run⟩

/-- Actual normalization preserves the original entry-color table. -/
theorem scanState_entry_colors (input : State) (inst : Nat) :
    (scanState input inst).entryColor = input.entryColor := by
  unfold scanState
  dsimp only
  split <;> rfl

/-- Uncolored actual source positions retain the active source frontier. -/
theorem scanState_color_zero (input : State) (inst : Nat) (zero : input.entryColor[inst]! = 0) :
    (scanState input inst).color = input.color := by simp [scanState,zero]

/-- Colored actual source positions reset the active frontier to their original source color. -/
theorem scanState_color_positive (input : State) (inst : Nat) (positive : input.entryColor[inst]! ≠ 0) :
    (scanState input inst).color = some input.entryColor[inst]! := by simp [scanState,positive]

/-- Actual nonemitting scans preserve the normalized color through all omission and opportunistic paths. -/
theorem scan_no_emission_color {ctx : Ctx} {block inst termInst : Nat} {isBranch : Bool}
    {input : State} {output : Scan}
    (notSunk : input.sunk[inst]! = false)
    (run : scanInstruction ctx block inst termInst isBranch input = .ok output)
    (noEmission : ∀ step,output.step = some step → step.decision ≠ .emitted) :
    output.state.color = (scanState input inst).color := by
  have rejectEmission (actual : (emitInstruction ctx inst (scanState input inst) >>= fun emission =>
      pure (emission.scan block inst (scanState input inst))) = .ok output) : False := by
    obtain ⟨emission,called,finished⟩ := bind_success actual
    have equal := Except.ok.inj finished
    have recorded : output.step = some ⟨block,inst,.emitted,scanState input inst,emission.state,
        emission.results,emission.rules,emission.code⟩ := by rw [← equal]; rfl
    exact noEmission _ recorded rfl
  simp only [scanInstruction,notSunk,Bool.false_eq_true,ite_false] at run
  dsimp only at run
  generalize mandatoryEq : (if inst == termInst then true else ctx.insts[inst]!.clif.any mustLower) = mandatory at run
  split at run
  · exact congrArg (fun scan : Scan => scan.state.color) (Except.ok.inj run).symm
  · split at run
    · exact congrArg (fun scan : Scan => scan.state.color) (Except.ok.inj run).symm
    · split at run
      · obtain ⟨choice,called,finished⟩ := bind_success run
        cases choice with
        | none => exact False.elim (rejectEmission finished)
        | some next =>
          have equal := Except.ok.inj finished
          exact (congrArg (fun scan : Scan => scan.state.color) equal).symm.trans
            (congrArg Prod.snd (opportunistic_color_fields called))
      · exact False.elim (rejectEmission run)

end Backend.Stock.Proof.Acquire810
