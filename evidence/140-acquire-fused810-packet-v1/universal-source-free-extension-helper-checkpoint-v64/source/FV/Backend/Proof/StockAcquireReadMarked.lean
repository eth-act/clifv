import FV.Backend.Proof.StockAcquireReadIntervalCoverage

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Isle
set_option autoImplicit false
set_option Elab.async false

/-- This internal source view retains every original statement slot. -/
def SourceSlotsPreserved (original current : Ctx) : Prop :=
  ∀ (slot : Nat) (info : IInfo) (inst : Clif.Inst),original.insts[slot]? = some info →
    info.clif = some inst → current.insts[slot]? = some info

/-- A derived source view transfers successful read frames back to the original source context. -/
theorem SourceReadFrame.of_source_view {original current : Ctx} (view : SourceSlotsPreserved original current)
    {producer : Nat} (read : SourceReadFrame current producer) : SourceReadFrame original producer := by
  intro env p before after executed
  obtain ⟨info,inst,values,regs,rest,installed,source,body,evaluated,updated,frame⟩ := executed
  exact read env p before after ⟨info,inst,values,regs,rest,view producer info inst installed source,
    source,body,evaluated,updated,frame⟩

/-- Installing actual terminator data retains every original statement slot. -/
theorem source_slots_termCtx {ctx : Ctx} {ti : Nat}
    (placeholder : ctx.insts[ti]? = some ⟨.op .unit,[],[],none⟩) (data : V) :
    SourceSlotsPreserved ctx (Driver.termCtx ctx ti data) := by
  intro slot info inst installed source
  by_cases same : slot = ti
  · subst slot
    have equal := Option.some.inj (installed.symm.trans placeholder)
    rw [equal] at source
    cases source
  · rw [termCtx_insts_ne same data]
    exact installed

/-- Exception reservations preserve the same original statement view. -/
theorem SourceSlotsPreserved.withTryRegs {original current : Ctx} (view : SourceSlotsPreserved original current)
    (reservations : List Reg × List Reg) : SourceSlotsPreserved original {current with tryRegs := reservations} := by
  intro slot info inst installed source
  exact view slot info inst installed source

/-- Marked original slots carry source read frames; no statement about fault absence is included. -/
def ReadMarked (original : Ctx) (state : State) : Prop :=
  ∀ producer,state.sunk[producer]! = true → SourceReadFrame original producer

/-- Actual initial construction derives the original read-mark invariant from its empty mark array. -/
theorem buildCtx_read_marked {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {initial : State}
    (built : Stock.buildCtx f = .ok (ctx,ranges,initial)) : ReadMarked ctx initial := by
  intro producer marked
  have empty := SinkRules.build_ctx_sunk_false built producer
  rw [empty] at marked
  cases marked

/-- Steps with unchanged marks retain the complete original read-mark invariant. -/
theorem ReadMarked.of_sunk_eq {ctx : Ctx} {before after : State} (read : ReadMarked ctx before)
    (same : after.sunk = before.sunk) : ReadMarked ctx after := by
  intro producer marked
  exact read producer (by rwa [same] at marked)

/-- Actual classified sinks preserve original read marks across changed scan contexts. -/
theorem ReadPendingMarks.preserves_read_marked {original current : Ctx} {before after : State}
    {pending : List Nat} (view : SourceSlotsPreserved original current)
    (trace : ReadPendingMarks current before pending after) (prior : ReadMarked original before) :
    ReadMarked original after := by
  intro producer marked
  rw [trace.forget.sunk_exact] at marked
  rcases sunk_fold_marked before.sunk pending producer marked with inherited | member
  · exact prior producer inherited
  · exact (trace.source_memory producer member).of_source_view view

end Backend.Stock.Proof.Acquire810
