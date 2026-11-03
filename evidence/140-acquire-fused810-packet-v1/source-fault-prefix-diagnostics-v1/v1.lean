import FV.Backend.Proof.StockAcquireActualSourceSliceMemory

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- An actual source instruction reaches its genuine semantic trap with its original flags. -/
def SourceInstFault (env : Clif.Env) (p : Clif.Program) (ctx : Ctx) (slot : Nat)
    (before : Clif.Frame × Clif.Mem) (code : Clif.TrapCode) : Prop :=
  ∃ info inst rest,ctx.insts[slot]? = some info ∧ info.clif = some inst ∧
    before.1.body = ⟨info.results,inst⟩::rest ∧ instOutcome env p before.1 before.2 inst = .trap code

/-- Successful read prefixes retain the exact memory at the first genuine source trap. -/
theorem source_first_trap_read_memory {env : Clif.Env} {p : Clif.Program} {ctx : Ctx}
    {indices : List Nat} {before : Clif.Frame × Clif.Mem} {code : Clif.TrapCode}
    (failed : SourceTrapSteps (SourceInstResult env p ctx) (SourceInstFault env p ctx) indices before code)
    (reads : ∀ slot ∈ indices,SourceReadFrame ctx slot) :
    ∃ (front : List Nat) (slot : Nat) (suffix : List Nat) (atFault : Clif.Frame × Clif.Mem),
      indices = front++slot::suffix ∧ SourceSteps (SourceInstResult env p ctx) front before atFault ∧
      SourceInstFault env p ctx slot atFault code ∧ atFault.2 = before.2 := by
  revert reads
  induction failed with
  | @here slot rest state code failed =>
    intro reads
    exact ⟨[],slot,rest,state,rfl,.nil _,failed,rfl⟩
  | @next inst rest state next code head tail ih =>
    intro reads
    have kept := reads inst (List.mem_cons_self ..) env p state next head
    obtain ⟨front,slot,suffix,atFault,parts,executed,failed,memory⟩ :=
      ih (fun target member => reads target (List.mem_cons_of_mem _ member))
    exact ⟨inst::front,slot,suffix,atFault,by rw [parts];rfl,.cons head executed,failed,memory.trans kept⟩

end Backend.Stock.Proof.Acquire810
