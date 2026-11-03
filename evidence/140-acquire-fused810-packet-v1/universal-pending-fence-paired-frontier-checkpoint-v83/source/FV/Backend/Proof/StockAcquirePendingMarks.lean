import FV.Backend.Proof.StockAcquirePendingSourceOrder

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

/-- Actual sink execution with complete sunk-array persistence in every frame. -/
inductive PendingMarks (ctx : Ctx) : State → List Nat → State → Prop where
  | nil (state : State) : PendingMarks ctx state [] state
  | sink {before middle after : State} {producer : Nat} {rest : List Nat}
      (actual : Stock.externCtor ctx T.sink_inst [.inst producer] before = .ok (.op .unit,middle))
      (tail : PendingMarks ctx middle rest after) : PendingMarks ctx before (producer::rest) after
  | frame {before middle after : State} {rest : List Nat}
      (entries : middle.entryColor = before.entryColor) (color : middle.color = before.color)
      (sunk : middle.sunk = before.sunk) (tail : PendingMarks ctx middle rest after) :
      PendingMarks ctx before rest after

/-- Forgetting the stronger frame retains every existing pending trace theorem. -/
theorem PendingMarks.forget {ctx : Ctx} {before after : State} {pending : List Nat}
    (trace : PendingMarks ctx before pending after) : PendingSinks ctx before pending after := by
  induction trace with
  | nil state => exact .nil state
  | sink actual tail ih => exact .sink actual ih
  | frame entries color sunk tail ih => exact .frame entries color ih

/-- Actual stronger traces compose without limiting the number of pending loads. -/
theorem PendingMarks.append {ctx : Ctx} {before middle after : State} {left right : List Nat}
    (first : PendingMarks ctx before left middle) (second : PendingMarks ctx middle right after) :
    PendingMarks ctx before (left++right) after := by
  induction first with
  | nil => exact second
  | sink actual tail ih => exact .sink actual (ih second)
  | frame entries color sunk tail ih => exact .frame entries color sunk (ih second)

/-- Actual source metadata remains unchanged throughout the stronger trace. -/
theorem PendingMarks.entryColors {ctx : Ctx} {before after : State} {pending : List Nat}
    (trace : PendingMarks ctx before pending after) : after.entryColor = before.entryColor :=
  trace.forget.entryColors

/-- The complete final sunk array is exactly the ordered fold of actual sink updates. -/
theorem PendingMarks.sunk_exact {ctx : Ctx} {before after : State} {pending : List Nat}
    (trace : PendingMarks ctx before pending after) :
    after.sunk = pending.foldl (fun bits producer => bits.set! producer true) before.sunk := by
  induction trace with
  | nil => rfl
  | sink actual tail ih =>
    rw [ih,(sink_accepted actual).2.2.2.2]
    rfl
  | frame entries color sunk tail ih =>
    rw [ih,sunk]

/-- Actual sink execution never changes the extent of the sunk array. -/
theorem PendingMarks.sunk_size {ctx : Ctx} {before after : State} {pending : List Nat}
    (trace : PendingMarks ctx before pending after) : after.sunk.size = before.sunk.size := by
  induction trace with
  | nil => rfl
  | sink actual tail ih =>
    rw [ih,(sink_accepted actual).2.2.2.2]
    simp
  | frame entries color sunk tail ih => rw [ih,sunk]

private theorem set_true_keeps_mark (bits : Array Bool) (producer target : Nat)
    (marked : bits[target]! = true) : (bits.set! producer true)[target]! = true := by
  by_cases same : producer = target
  · subst producer
    by_cases inside : target < bits.size
    · simp [Array.set!_eq_setIfInBounds,inside]
    · simp [getElem!_def,Array.getElem?_eq_none (Nat.le_of_not_lt inside)] at marked
  · rw [Array.getElem!_set!_ne _ _ _ _ same]
    exact marked

/-- Later actual sinks cannot clear an earlier deferred source mark. -/
theorem PendingMarks.marked_mono {ctx : Ctx} {before after : State} {pending : List Nat}
    (trace : PendingMarks ctx before pending after) (target : Nat)
    (marked : before.sunk[target]! = true) : after.sunk[target]! = true := by
  revert marked
  induction trace with
  | nil => intro marked; exact marked
  | sink actual tail ih =>
    intro marked
    apply ih
    rw [(sink_accepted actual).2.2.2.2]
    exact set_true_keeps_mark _ _ _ marked
  | frame entries color sunk tail ih =>
    intro marked
    apply ih
    rwa [sunk]

/-- The stronger trace retains the proved reverse source-color order. -/
theorem PendingMarks.ordered {ctx : Ctx} {before after : State} {pending : List Nat}
    (trace : PendingMarks ctx before pending after) {final : Nat} (color : after.color = some final) :
    pending.Pairwise (fun left right => before.entryColor[right]! < before.entryColor[left]!) :=
  trace.forget.ordered color

end Backend.Stock.Proof.Acquire810
