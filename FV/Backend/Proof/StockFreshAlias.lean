module

public import FV.Backend.Proof.StockRecordedFlow
public import FV.Backend.Proof.StockDriverBounds

@[expose] public section

/-! Fresh targets of actual Stock lowering are terminal in its final alias map.
These facts discharge the fresh alternative of final recorded alias origins;
source-register chains and reserved-value semantics remain separate obligations. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver

/-- The real driver's final resolver leaves every fresh register unchanged.
The alias-domain bound comes from successful lowering, not a new program premise. -/
theorem stock_lower_freshAlias_terminal {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {n : Nat}
    (fresh : result.initial.base.nextVreg ≤ n) :
    (result.final.alias[n]?).join = none ∧ aliasNum result.final.alias n = n := by
  have outside : result.final.alias.size ≤ n :=
    Nat.le_trans (stock_lower_allocationBounds run).1 fresh
  have absent : (result.final.alias[n]?).join = none := by
    rw [Array.getElem?_eq_none outside]
    rfl
  exact ⟨absent, chaseF_none absent _⟩

/-- Inhabited by the actual nonempty emitted-call driver witness already used
for final alias origins; no new native certificate is introduced. -/
theorem stock_lower_freshAlias_terminal_witness :
    ∃ (f : Clif.Function) (result : Result) (event : BlockScanEvent)
      (record : ScanRecord) (step : Step),
      Stock.lower f = .ok result ∧ f.blocks.length ≠ 0 ∧
      event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧
      record.output.step = some step ∧ step.decision = .emitted ∧
      (result.final.alias[result.initial.base.nextVreg]?).join = none ∧
      aliasNum result.final.alias result.initial.base.nextVreg = result.initial.base.nextVreg := by
  obtain ⟨result, event, record, step, target, scope, dominated, nonempty, run,
    events, records, index, recorded, emitted, rest⟩ :=
    stock_lower_emitted_record_finalAliasOrigins_noInherited_witness
  refine ⟨_, result, event, record, step, run, nonempty, events, records, recorded, emitted, ?_⟩
  exact stock_lower_freshAlias_terminal run (Nat.le_refl _)


/-- A source key bound to a fresh final target resolves to that target in the
actual whole-driver resolver. Freshness and the observed entry replace a
caller-supplied resolver equality. -/
theorem stock_lower_freshAlias_resolves {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {n : Nat}
    (fresh : result.initial.base.nextVreg ≤ n) :
    ∀ key, (result.final.alias[key]?).join = some n →
      aliasNum result.final.alias key = n := by
  intro key entry
  have absent := (stock_lower_freshAlias_terminal run fresh).1
  change chaseF (fun k => (result.final.alias[k]?).join) (result.final.alias.size + 1) key = n
  rw [chaseF, entry]
  exact chaseF_none absent _

private def freshValueFunction : Clif.Function := {
  name := "fresh_value_witness"
  sig := { returns := [⟨.i8, .none, .normal⟩], callConv := some .systemV }
  blocks := [{ id := 0, params := [], body := [⟨[0], .iconst .i8 7⟩], term := .ret [0] }] }

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem freshValue_observed :
    (Stock.lower freshValueFunction).toOption.map (fun r =>
      (r.initial.base.nextVreg, (r.final.alias[192]?).join,
        r.blockScans.toList.any (fun e => e.output.records.any (fun record =>
          record.inst == 0 && record.output.step.any (fun step => step.decision == .emitted))))) =
      some (193, some 193, true) := by
  decide +kernel

/-- A real constant-source definition has an installed alias to a fresh target
and a nonempty emitted record. This witnesses the lookup and freshness premises,
not just a conditional property on an unbound key. -/
theorem stock_lower_freshAlias_resolves_witness :
    ∃ (f : Clif.Function) (result : Result) (key target : Nat),
      Stock.lower f = .ok result ∧ f.blocks.length ≠ 0 ∧
      result.initial.base.nextVreg ≤ target ∧
      (result.final.alias[key]?).join = some target ∧
      aliasNum result.final.alias key = target ∧
      result.blockScans.toList.any (fun e => e.output.records.any (fun record =>
        record.inst == 0 && record.output.step.any (fun step => step.decision == .emitted))) = true := by
  have observed := freshValue_observed
  cases run : Stock.lower freshValueFunction with
  | error error =>
    simp only [run, Except.toOption, Option.map_none] at observed
    cases observed
  | ok result =>
    simp only [run, Except.toOption, Option.map_some] at observed
    have eq := Option.some.inj observed
    have initial : result.initial.base.nextVreg = 193 := congrArg Prod.fst eq
    have entry : (result.final.alias[192]?).join = some 193 := congrArg (fun p => p.2.1) eq
    have fresh : result.initial.base.nextVreg ≤ 193 := Nat.le_of_eq initial
    exact ⟨freshValueFunction, result, 192, 193, run, by decide, fresh, entry,
      stock_lower_freshAlias_resolves run fresh 192 entry, congrArg (fun p => p.2.2) eq⟩

/-- A value produced at a fresh target is held at every source key actually
bound to it by the final driver map. This is the value-semantic use of the
resolver fact; no independent alias-resolution equation is assumed. -/
theorem stock_lower_freshAlias_value {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {n : Nat}
    (fresh : result.initial.base.nextVreg ≤ n) :
    ∀ key, (result.final.alias[key]?).join = some n →
      ∀ (ρ : Nat → Backend.Proof.CV) (v : Clif.Val),
        VHolds v (ρ n) → VHolds v (ρ (aliasNum result.final.alias key)) := by
  intro key entry ρ v held
  rw [stock_lower_freshAlias_resolves run fresh key entry]
  exact held

/-- A real bound source key holds the witnessed constant value through the
actual resolver; both the alias lookup and the value premise are inhabited. -/
theorem stock_lower_freshAlias_value_witness :
    ∃ (f : Clif.Function) (result : Result) (key target : Nat)
      (ρ : Nat → CV) (v : Clif.Val),
      Stock.lower f = .ok result ∧ f.blocks.length ≠ 0 ∧
      result.initial.base.nextVreg ≤ target ∧
      (result.final.alias[key]?).join = some target ∧
      VHolds v (ρ target) ∧ VHolds v (ρ (aliasNum result.final.alias key)) := by
  obtain ⟨f, result, key, target, run, nonempty, fresh, entry, resolves, emitted⟩ :=
    stock_lower_freshAlias_resolves_witness
  let ρ : Nat → CV := fun _ => BitVec.ofNat 128 7
  let v : Clif.Val := Clif.Val.ofInt .i8 7
  have held : VHolds v (ρ target) := by rfl
  exact ⟨f, result, key, target, ρ, v, run, nonempty, fresh, entry, held,
    stock_lower_freshAlias_value run fresh key entry ρ v held⟩

end Backend.Stock.Proof
