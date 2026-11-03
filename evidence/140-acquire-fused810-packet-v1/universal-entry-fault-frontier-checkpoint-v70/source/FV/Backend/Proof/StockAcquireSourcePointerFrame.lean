import FV.Backend.Proof.StockAcquireGuardedPointerValue
import FV.Backend.Proof.StockScanSemantics

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- An internal frame property derived from original source availability. -/
def PointerUnwritten (pointer : Nat) (body : List Clif.Stmt) : Prop :=
  ∀ stm ∈ body, pointer ∉ stm.results

/-- Actual successful source steps preserve the pointer across arbitrary memory effects. -/
theorem source_inst_pointer_frame {env : Clif.Env} {p : Clif.Program} {ctx : Ctx} {i pointer : Nat}
    {before after : Clif.Frame × Clif.Mem}
    (step : SourceInstResult env p ctx i before after)
    (safe : PointerUnwritten pointer before.1.body) :
    after.1.regs pointer = before.1.regs pointer ∧ PointerUnwritten pointer after.1.body := by
  obtain ⟨info,inst,values,regs,rest,installed,source,body,evaluated,updated,frame⟩ := step
  have headSafe : pointer ∉ info.results :=
    safe ⟨info.results,inst⟩ (by rw [body]; exact List.mem_cons_self ..)
  have kept := setMany_other updated headSafe
  constructor
  · rw [frame]
    exact kept
  · rw [frame]
    intro stm member
    exact safe stm (by rw [body]; exact List.mem_cons_of_mem _ member)

/-- A complete actual source prefix retains the pointer through calls, loads, stores and other effects. -/
theorem source_steps_pointer_frame {env : Clif.Env} {p : Clif.Program} {ctx : Ctx} {pointer : Nat}
    {indices : List Nat} {before after : Clif.Frame × Clif.Mem}
    (steps : SourceSteps (SourceInstResult env p ctx) indices before after)
    (safe : PointerUnwritten pointer before.1.body) :
    after.1.regs pointer = before.1.regs pointer ∧ PointerUnwritten pointer after.1.body := by
  revert safe
  induction steps with
  | nil state => intro safe; exact ⟨rfl,safe⟩
  | cons head tail ih =>
    intro safe
    obtain ⟨kept,safeTail⟩ := source_inst_pointer_frame head safe
    obtain ⟨tailKept,safeAfter⟩ := ih safeTail
    exact ⟨tailKept.trans kept,safeAfter⟩

/-- Existing source availability derives the absence of later pointer definitions internally. -/
theorem available_pointer_unwritten {f : Clif.Function} {In : Array (List Clif.ValueId)}
    {bi j pointer : Nat} {block : Clif.Block} (blockAt : f.blocks[bi]? = some block)
    (available : pointer ∈ availOf f In bi j) : PointerUnwritten pointer (block.body.drop j) := by
  have future := ((mem_av blockAt).mp available).2
  intro stm member written
  obtain ⟨offset,found⟩ := List.mem_iff_getElem?.mp member
  rw [List.getElem?_drop] at found
  exact future ⟨j+offset,stm,by omega,found,written⟩

/-- The original source boundary supplies the pointer frame equality across any actual prefix. -/
theorem available_source_prefix_pointer {f : Clif.Function} {In : Array (List Clif.ValueId)}
    {bi j pointer : Nat} {block : Clif.Block} (blockAt : f.blocks[bi]? = some block)
    (available : pointer ∈ availOf f In bi j) {env : Clif.Env} {p : Clif.Program} {ctx : Ctx}
    {indices : List Nat} {before after : Clif.Frame × Clif.Mem}
    (body : before.1.body = block.body.drop j)
    (steps : SourceSteps (SourceInstResult env p ctx) indices before after) :
    after.1.regs pointer = before.1.regs pointer := by
  have safe : PointerUnwritten pointer before.1.body := by
    rw [body]
    exact available_pointer_unwritten blockAt available
  exact (source_steps_pointer_frame steps safe).1

end Backend.Stock.Proof.Acquire810
