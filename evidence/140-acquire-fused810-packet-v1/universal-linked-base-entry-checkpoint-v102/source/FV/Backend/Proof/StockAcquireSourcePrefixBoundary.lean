import FV.Backend.Proof.StockAcquireWholeEffectBindings

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- A real indexed source execution supplies both exact prefix and residual execution. -/
theorem source_steps_append_split {S : Type} {step : Nat → S → S → Prop}
    {left right : List Nat} {before after : S} (steps : SourceSteps step (left++right) before after) :
    ∃ middle,SourceSteps step left before middle ∧ SourceSteps step right middle after := by
  induction left generalizing before with
  | nil => exact ⟨before,.nil before,steps⟩
  | cons inst left ih =>
    cases steps with
    | cons head tail =>
      obtain ⟨middle,first,second⟩ := ih tail
      exact ⟨middle,.cons head first,second⟩

/-- Actual indexed source steps derive the exact remaining original body at every prefix boundary. -/
theorem source_steps_body_prefix {ctx : Ctx} {block : Clif.Block} {base : Nat}
    (slots : ∀ j stm,block.body[j]? = some stm →
      ∃ info,ctx.insts[base+j]? = some info ∧ info.clif = some stm.inst ∧ info.results = stm.results)
    {env : Clif.Env} {program : Clif.Program} {start count : Nat} {before after : Clif.Frame × Clif.Mem}
    (inside : start+count ≤ block.body.length) (body : before.1.body = block.body.drop start)
    (steps : SourceSteps (SourceInstResult env program ctx) (List.range' (base+start) count) before after) :
    after.1.body = block.body.drop (start+count) := by
  induction count generalizing start before with
  | zero => cases steps;simpa only [Nat.add_zero] using body
  | succ count ih =>
    rw [List.range'_succ] at steps
    cases steps with
    | @cons inst indices before middle after head tail =>
      have bound : start < block.body.length := by omega
      let stm := block.body[start]
      have statement : block.body[start]? = some stm := List.getElem?_eq_getElem bound
      obtain ⟨info,installed,source,results⟩ := slots start stm statement
      obtain ⟨actual,original,values,regs,rest,found,clif,remaining,evaluated,updated,frame⟩ := head
      have infoEq := Option.some.inj (found.symm.trans installed)
      subst actual
      have instEq := Option.some.inj (clif.symm.trans source)
      subst original
      have expected : before.1.body = stm::block.body.drop (start+1) := by
        rw [body,List.drop_eq_getElem_cons bound]
      have remaining' : before.1.body = stm::rest := by simpa only [results] using remaining
      have tailEq := (List.cons.inj (remaining'.symm.trans expected)).2
      have nextBody : middle.1.body = block.body.drop (start+1) := by rw [frame,tailEq]
      have nextSteps : SourceSteps (SourceInstResult env program ctx) (List.range' (base+(start+1)) count) middle after := by
        simpa only [Nat.add_assoc] using tail
      have next := ih (start := start+1) (by omega) nextBody nextSteps
      simpa only [Nat.add_assoc,Nat.add_comm 1 count] using next

end Backend.Stock.Proof.Acquire810
