import FV.Backend.Proof.StockAliasSemantics
import FV.Backend.Proof.LowerDecide

/-! Shared actual logical-run fixtures; reused by helper, root and record witnesses. -/
namespace Backend.Stock.Proof.LogicalSemantics
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
inductive LogicalForm where
  | registers | immediateRight | immediateLeft | shiftRight | shiftLeft
  deriving DecidableEq
def formX : LogicalForm → Nat
  | .registers | .immediateRight => 7
  | .immediateLeft => 31
  | .shiftRight => 32
  | .shiftLeft => 63
def formY : LogicalForm → Nat
  | .registers | .immediateRight => 31
  | .immediateLeft => 7
  | .shiftRight => 63
  | .shiftLeft => 32
def formValueX : LogicalForm → Nat
  | .registers | .immediateRight => 7
  | .immediateLeft => 255
  | .shiftRight => 5
  | .shiftLeft => 56
def formValueY : LogicalForm → Nat
  | .registers => 5
  | .immediateRight => 255
  | .immediateLeft => 7
  | .shiftRight => 56
  | .shiftLeft => 5
def formRule : LogicalForm → RuleId
  | .registers => rule_inst_3916.id
  | .immediateRight => rule_inst_3920.id
  | .immediateLeft => rule_inst_3923.id
  | .shiftRight => rule_inst_3928.id
  | .shiftLeft => rule_inst_3931.id
def formFunction (form : LogicalForm) : Clif.Function := {
  name := "logical_values"
  sig := {
    params := if form = .registers ∨ form = .shiftRight ∨ form = .shiftLeft then [⟨.i64,.none,.normal⟩,⟨.i64,.none,.normal⟩] else [⟨.i64,.none,.normal⟩]
    returns := [⟨.i64,.none,.normal⟩]
    callConv := some .systemV }
  blocks := [{
    id := 0
    params := match form with
      | .registers => [(7,.i64),(31,.i64)]
      | .immediateRight | .immediateLeft => [(7,.i64)]
      | .shiftRight | .shiftLeft => [(7,.i64),(32,.i64)]
    body := (match form with
      | .registers => []
      | .immediateRight | .immediateLeft => [⟨[31],.iconst .i64 255⟩]
      | .shiftRight | .shiftLeft => [⟨[31],.iconst .i64 3⟩,⟨[63],.binary .ishl .i64 7 31⟩]) ++
        [⟨[100],.binary .bor .i64 (formX form) (formY form)⟩]
    term := .ret [100]}] }
def formBuilt (form : LogicalForm) : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx (formFunction form)).toOption.getD (sinkCtx,#[],sinkState)
theorem formScope (form : LogicalForm) : LowerScope (formFunction form) :=
  lowerScope_of (by cases form <;> decide +kernel)
theorem formBuild (form : LogicalForm) : Stock.buildCtx (formFunction form) = .ok (formBuilt form) := by
  cases form <;> rfl
theorem formInv (form : LogicalForm) : MappedCtxInv (formFunction form) (formBuilt form).1 :=
  buildCtx_mappedInv (formScope form) (formBuild form)
def formFrame (form : LogicalForm) : Clif.Frame := {
  func := formFunction form
  regs := fun x => if x = 7 then some (.ofInt .i64 7) else
    match form with
    | .registers => if x = 31 then some (.ofInt .i64 5) else none
    | .immediateRight | .immediateLeft => if x = 31 then some (.ofInt .i64 255) else none
    | .shiftRight | .shiftLeft => if x = 32 then some (.ofInt .i64 5) else if x = 31 then some (.ofInt .i64 3)
        else if x = 63 then some (.ofInt .i64 56) else none
  slots := [],body := [],term := .ret [100] }
def formRegs (form : LogicalForm) (n : Nat) : CV :=
  if n = 192 then 7 else if n = 193 ∧ (form = .registers ∨ form = .shiftRight ∨ form = .shiftLeft) then 5 else 0
def formDemand (form : LogicalForm) : Array Nat :=
  (Array.replicate 101 0).modify 7 (· + 1) |>.modify
    (if form = .registers then 31 else if form = .shiftRight ∨ form = .shiftLeft then 32 else 7)
      (fun n => if form = .immediateRight ∨ form = .immediateLeft then n else n + 1)

theorem formDFG (form : LogicalForm) : DFGCons (formBuilt form).1 (formFrame form) := by
  constructor
  · intro x j info cl v defined found original pure lookup
    by_cases param : x = 7
    · subst x
      have absent : (formBuilt form).1.defInst? 7 = none := by cases form <;> rfl
      rw [absent] at defined; cases defined
    · by_cases thirtyone : x = 31
      · subst x
        cases form with
        | registers => change none = some j at defined; cases defined
        | immediateRight | immediateLeft | shiftRight | shiftLeft =>
          all_goals
            change some 0 = some j at defined
            cases defined
            obtain ⟨bound,equal⟩ := Array.getElem?_eq_some_iff.mp found
            subst info
            cases original
            cases lookup
            exact ⟨[_],fun cm => rfl,rfl⟩
      · by_cases shifted : x = 63
        · subst x
          cases form with
          | registers | immediateRight | immediateLeft => change none = some j at defined; cases defined
          | shiftRight | shiftLeft =>
            all_goals
              change some 1 = some j at defined
              cases defined
              obtain ⟨bound,equal⟩ := Array.getElem?_eq_some_iff.mp found
              subst info
              cases original
              cases lookup
              exact ⟨[_],fun cm => rfl,rfl⟩
        · by_cases leaf : x = 32
          · subst x
            have absent : (formBuilt form).1.defInst? 32 = none := by cases form <;> rfl
            rw [absent] at defined; cases defined
          · cases form <;> simp [formFrame,param,thirtyone,shifted,leaf] at lookup
  · intro x t v typed lookup
    by_cases present : x = 7 ∨ x = 31 ∨ x = 32 ∨ x = 63
    · rcases present with rfl | rfl | rfl | rfl
      all_goals
        cases form
        all_goals
          first
          | (change none = some t at typed; cases typed)
          | (change some (.int 64) = some t at typed; cases typed; cases lookup; rfl)
    · simp only [not_or] at present
      cases form <;> simp [formFrame,present.1,present.2.1,present.2.2.1,present.2.2.2] at lookup

theorem formExtent (form : LogicalForm) (x : Nat) (r : Reg)
    (mapped : (formBuilt form).1.valueReg? x = some r) : x < (formBuilt form).2.2.demand.size := by
  by_cases large : 101 ≤ x
  · have outside : (formBuilt form).1.valReg.size ≤ x := by cases form <;> change 101 ≤ x <;> exact large
    change ((formBuilt form).1.valReg[x]?).join = some r at mapped
    rw [Array.getElem?_eq_none outside] at mapped
    cases mapped
  · have size : (formBuilt form).2.2.demand.size = 101 := by cases form <;> rfl
    rw [size]; omega

section WitnessRuns
attribute [local semireducible] Isle.Aarch64.program
theorem formRun (form : LogicalForm) :
    ((applyTerm program (Stock.sem (formBuilt form).1) {} 60 27 565
      [.data 59 2 [],.ty (.int 64),.value (formX form),.value (formY form)]).run
        ((formBuilt form).2.2,#[])).toOption.any (fun result => result.1.isSome &&
          decide (result.2.1.demand = formDemand form) && decide (result.2.2.back? = some (formRule form))) = true := by
  cases form <;> decide +kernel
end WitnessRuns

theorem formHeld (form : LogicalForm) {after : State} (demand : after.demand = formDemand form) :
    ValuesHeld (Demanded after) (formBuilt form).1 (formFrame form)
      (fun n => formRegs form (aliasNum #[] n)) := by
  intro x needed val lookup
  by_cases seven : x = 7
  · subst x
    change some (.ofInt .i64 7) = some val at lookup
    cases lookup
    refine ⟨192,?_,?_⟩
    · cases form <;> rfl
    · cases form <;> unfold VHolds <;> decide +kernel
  · by_cases thirtyone : x = 31
    · subst x
      cases form with
      | registers =>
        change some (.ofInt .i64 5) = some val at lookup
        cases lookup
        exact ⟨193,rfl,by unfold VHolds; decide +kernel⟩
      | immediateRight | immediateLeft | shiftRight | shiftLeft =>
        all_goals
          rw [Demanded,demand] at needed
          change 0 ≠ 0 at needed
          exact False.elim (needed rfl)
    · by_cases thirtytwo : x = 32
      · subst x
        cases form with
        | registers | immediateRight | immediateLeft => cases lookup
        | shiftRight | shiftLeft =>
          all_goals
            change some (.ofInt .i64 5) = some val at lookup
            cases lookup
            exact ⟨193,rfl,by unfold VHolds; decide +kernel⟩
      · by_cases sixtythree : x = 63
        · subst x
          cases form with
          | registers | immediateRight | immediateLeft => cases lookup
          | shiftRight | shiftLeft =>
            all_goals
              rw [Demanded,demand] at needed
              change 0 ≠ 0 at needed
              exact False.elim (needed rfl)
        · cases form <;> simp [formFrame,seven,thirtyone,thirtytwo,sixtythree] at lookup


end Backend.Stock.Proof.LogicalSemantics
