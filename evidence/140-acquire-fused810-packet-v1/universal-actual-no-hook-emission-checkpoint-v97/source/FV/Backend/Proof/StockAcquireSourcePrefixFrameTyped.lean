import FV.Backend.Proof.StockAcquireSourceFrameTypedStep

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Real source steps preserve the original function through complete finite prefixes. -/
theorem source_steps_function {ctx : Ctx} {env : Clif.Env} {program : Clif.Program}
    {indices : List Nat} {before after : Clif.Frame × Clif.Mem}
    (steps : SourceSteps (SourceInstResult env program ctx) indices before after) : after.1.func = before.1.func := by
  induction steps with
  | nil => rfl
  | cons head tail ih => exact ih.trans (source_inst_result_function head)

/-- Original SSA and actual source outcomes propagate frame typing across every real body prefix. -/
theorem stock_lower_source_body_prefix_frame_typed {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {original : Ctx} {ranges : Array (Nat × Nat)} {initial : LState}
    (built : Backend.buildCtx f = .ok (original,ranges,initial))
    {bi : Nat} {block : Clif.Block} (blockAt : f.blocks[bi]? = some block)
    {env : Clif.Env} {program : Clif.Program} {start count : Nat} {before after : Clif.Frame × Clif.Mem}
    (inside : start+count ≤ block.body.length) (body : before.1.body = block.body.drop start)
    (function : before.1.func = f) (typed : FrameTyped event.ctx before.1)
    (steps : SourceSteps (SourceInstResult env program event.ctx) (List.range' (blockStart f bi+start) count) before after) :
    FrameTyped event.ctx after.1 := by
  have view := stock_lower_event_build_source_slots run scope events built
  have slots : ∀ j stm,block.body[j]? = some stm →
      ∃ info,event.ctx.insts[blockStart f bi+j]? = some info ∧ info.clif = some stm.inst ∧ info.results = stm.results := by
    intro j stm statement
    obtain ⟨info,installed,source,results⟩ := (ctxSpec_of built).facts.stmt bi block j stm blockAt statement
    exact ⟨info,view _ info stm.inst installed source,source,results⟩
  induction count generalizing start before with
  | zero => cases steps;exact typed
  | succ count ih =>
    rw [List.range'_succ] at steps
    cases steps with
    | @cons inst indices before middle after head tail =>
      have bound : start < block.body.length := by omega
      let stm := block.body[start]
      have statement : block.body[start]? = some stm := List.getElem?_eq_getElem bound
      obtain ⟨info,installed,source,results⟩ := slots start stm statement
      have nodup : info.results.Nodup := by rw [results];exact stmt_nodup dominated.ssa blockAt statement
      have nextTyped := stock_lower_source_inst_frame_typed run scope dominated events installed source nodup function typed head
      have nextFunction := (source_inst_result_function head).trans function
      have nextBody : middle.1.body = block.body.drop (start+1) := by
        exact source_steps_body_prefix slots (count := 1) (by omega) body (.cons head (.nil middle))
      have nextSteps : SourceSteps (SourceInstResult env program event.ctx)
          (List.range' (blockStart f bi+(start+1)) count) middle after := by
        simpa only [Nat.add_assoc] using tail
      exact ih (start := start+1) (by omega) nextBody nextFunction nextTyped nextSteps

end Backend.Stock.Proof.Acquire810
