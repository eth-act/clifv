import FV.Backend.Proof.StockAcquireEligibilityReadSources

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

/-- An internal semantic property of a derived source instruction; source faults remain permitted. -/
def SourceReadFrame (ctx : Ctx) (producer : Nat) : Prop :=
  ∀ (env : Clif.Env) (p : Clif.Program) (before after : Clif.Frame × Clif.Mem),
    SourceInstResult env p ctx producer before after → after.2 = before.2

/-- A derived pending trace retains its original source memory frame at every actual sink. -/
inductive ReadPendingMarks (ctx : Ctx) : State → List Nat → State → Prop where
  | nil (state : State) : ReadPendingMarks ctx state [] state
  | sink {before middle after : State} {producer : Nat} {rest : List Nat}
      (actual : Stock.externCtor ctx T.sink_inst [.inst producer] before = .ok (.op .unit,middle))
      (source : SourceReadFrame ctx producer) (tail : ReadPendingMarks ctx middle rest after) :
      ReadPendingMarks ctx before (producer::rest) after
  | frame {before middle after : State} {rest : List Nat}
      (entries : middle.entryColor = before.entryColor) (color : middle.color = before.color)
      (sunk : middle.sunk = before.sunk) (tail : ReadPendingMarks ctx middle rest after) :
      ReadPendingMarks ctx before rest after

/-- The stronger read trace preserves every previous exact-mark theorem. -/
theorem ReadPendingMarks.forget {ctx : Ctx} {before after : State} {pending : List Nat}
    (trace : ReadPendingMarks ctx before pending after) : PendingMarks ctx before pending after := by
  induction trace with
  | nil state => exact .nil state
  | sink actual source tail ih => exact .sink actual ih
  | frame entries color sunk tail ih => exact .frame entries color sunk ih

/-- General pending groups compose without a singleton restriction. -/
theorem ReadPendingMarks.append {ctx : Ctx} {before middle after : State} {left right : List Nat}
    (first : ReadPendingMarks ctx before left middle) (second : ReadPendingMarks ctx middle right after) :
    ReadPendingMarks ctx before (left++right) after := by
  induction first with
  | nil => exact second
  | sink actual source tail ih => exact .sink actual source (ih second)
  | frame entries color sunk tail ih => exact .frame entries color sunk (ih second)

/-- Every actual source step named by the read trace preserves memory on success. -/
theorem ReadPendingMarks.source_memory {ctx : Ctx} {before after : State} {pending : List Nat}
    (trace : ReadPendingMarks ctx before pending after) :
    ∀ producer ∈ pending,SourceReadFrame ctx producer := by
  induction trace with
  | nil => simp
  | sink actual source tail ih =>
    intro producer member
    rcases List.mem_cons.mp member with rfl | member
    · exact source
    · exact ih producer member
  | frame entries color sunk tail ih => exact ih

/-- Actual program evaluation must derive this relation before consumers use its source frames. -/
def ReadPendingExecution (ctx : Ctx) (before after : State) : Prop :=
  ∃ pending,ReadPendingMarks ctx before pending after

end Backend.Stock.Proof.Acquire810
