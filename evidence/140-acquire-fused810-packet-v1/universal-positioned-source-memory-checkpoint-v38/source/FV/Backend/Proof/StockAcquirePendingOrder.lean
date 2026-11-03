import FV.Backend.Proof.StockPolicy

namespace Backend.Stock.Proof.Acquire810
open Isle Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

/-- Internal execution evidence for actual sinks and color-preserving helper steps.
The relation records deferred effects. It is not an input acceptance condition. -/
inductive PendingSinks (ctx : Ctx) : State → List Nat → State → Prop where
  | nil (state : State) : PendingSinks ctx state [] state
  | sink {before middle after : State} {producer : Nat} {rest : List Nat}
      (actual : Stock.externCtor ctx T.sink_inst [.inst producer] before = .ok (.op .unit,middle))
      (tail : PendingSinks ctx middle rest after) : PendingSinks ctx before (producer::rest) after
  | frame {before middle after : State} {rest : List Nat}
      (entries : middle.entryColor = before.entryColor) (color : middle.color = before.color)
      (tail : PendingSinks ctx middle rest after) : PendingSinks ctx before rest after

/-- All pending sinks retain the actual source metadata array. -/
theorem PendingSinks.entryColors {ctx : Ctx} {before after : State} {pending : List Nat}
    (trace : PendingSinks ctx before pending after) : after.entryColor = before.entryColor := by
  induction trace with
  | nil => rfl
  | sink actual tail ih =>
    have frame := (sink_accepted actual).2.2.2.2
    rw [ih,frame]
  | frame entries color tail ih => exact ih.trans entries

/-- The actual frontier decreases once for every deferred colored effect. -/
theorem PendingSinks.color_distance {ctx : Ctx} {before after : State} {pending : List Nat}
    (trace : PendingSinks ctx before pending after) {final : Nat} (color : after.color = some final) :
    before.color = some (final+pending.length) := by
  induction trace with
  | nil => simpa using color
  | @sink before middle after producer rest actual tail ih =>
    have accepted := sink_accepted actual
    have middleColor : middle.color = some before.entryColor[producer]! := by
      rw [accepted.2.2.2.2]
    have same : before.entryColor[producer]! = final+rest.length :=
      Option.some.inj (middleColor.symm.trans (ih color))
    rw [accepted.2.1,same]
    congr 1
  | frame entries unchanged tail ih => exact unchanged.symm.trans (ih color)

/-- Every pending effect occupies its exact descending source-color interval. -/
theorem PendingSinks.member_color_bounds {ctx : Ctx} {before after : State} {pending : List Nat}
    (trace : PendingSinks ctx before pending after) {final : Nat} (color : after.color = some final) :
    ∀ producer ∈ pending,final ≤ before.entryColor[producer]! ∧
      before.entryColor[producer]! < final+pending.length := by
  induction trace with
  | nil => simp
  | @sink before middle after producer rest actual tail ih =>
    have accepted := sink_accepted actual
    have frame := accepted.2.2.2.2
    have middleColor : middle.color = some before.entryColor[producer]! := by rw [frame]
    have same : before.entryColor[producer]! = final+rest.length :=
      Option.some.inj (middleColor.symm.trans (tail.color_distance color))
    intro index member
    rcases List.mem_cons.mp member with rfl | member
    · rw [same]
      simp only [List.length_cons]
      omega
    · have bounds := ih color index member
      have entries : middle.entryColor = before.entryColor := by rw [frame]
      rw [entries] at bounds
      simp only [List.length_cons]
      omega
  | frame entries unchanged tail ih =>
    intro index member
    have bounds := ih color index member
    rwa [entries] at bounds

/-- Actual sink order is strict reverse source-color order, including multiple pending loads. -/
theorem PendingSinks.ordered {ctx : Ctx} {before after : State} {pending : List Nat}
    (trace : PendingSinks ctx before pending after) {final : Nat} (color : after.color = some final) :
    pending.Pairwise (fun left right => before.entryColor[right]! < before.entryColor[left]!) := by
  induction trace with
  | nil => exact List.Pairwise.nil
  | @sink before middle after producer rest actual tail ih =>
    have accepted := sink_accepted actual
    have frame := accepted.2.2.2.2
    have entries : middle.entryColor = before.entryColor := by rw [frame]
    have middleColor : middle.color = some before.entryColor[producer]! := by rw [frame]
    have same : before.entryColor[producer]! = final+rest.length :=
      Option.some.inj (middleColor.symm.trans (tail.color_distance color))
    apply List.pairwise_cons.mpr
    constructor
    · intro index member
      have bounds := tail.member_color_bounds color index member
      rw [entries] at bounds
      omega
    · simpa only [entries] using ih color
  | frame entries unchanged tail ih => simpa only [entries] using ih color

/-- Actual pending effects cannot name the same producer twice. -/
theorem PendingSinks.distinct {ctx : Ctx} {before after : State} {pending : List Nat}
    (trace : PendingSinks ctx before pending after) {final : Nat} (color : after.color = some final) :
    pending.Nodup := by
  exact List.Pairwise.imp (fun {a b} less same => by subst b; omega) (trace.ordered color)

end Backend.Stock.Proof.Acquire810
