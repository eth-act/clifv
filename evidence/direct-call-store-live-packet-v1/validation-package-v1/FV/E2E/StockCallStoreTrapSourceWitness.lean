import FV.E2E.StockCallStoreSourceWitness

namespace E2E.CallStoreTrapSourceWitness
open Backend Backend.Proof Backend.Proof.Driver CallStoreFixture CallStoreSourceWitness
set_option autoImplicit false
set_option Elab.async false

/-- This extra callee fixture does not replace the preserved arithmetic callee. -/
def trappingCallee : Clif.Function := {callee with
  blocks := [{id := 0,params := [(101,.i64)],body := [],term := .trap (.user 1)}]}
def trappingProgram : Clif.Program := {funcs := [caller,trappingCallee]}

/-- The original caller reaches the actual callee trap before its default-flag store.
Both arguments and the initial memory remain arbitrary. -/
theorem actual_source_callee_trap (pointer word : BitVec 64) (memory : Clif.Mem) :
    ∃ enteredFrame enteredMemory,
      Clif.enterFunc caller [value pointer,value word] memory = .ok (enteredFrame,enteredMemory) ∧
      enteredFrame.func = caller ∧
      enteredFrame.body = [⟨[31],.call 0 [11]⟩,⟨[],.store .store .i64 {} 31 7 8⟩] ∧
      Clif.runLoop Clif.Env.empty trappingProgram 2 ⟨enteredFrame,[],enteredMemory⟩ =
        .trapped (.user 1) := by
  exact ⟨{frame pointer word with slots := (Clif.enterSlots caller memory).1},
    (Clif.enterSlots caller memory).2,rfl,rfl,rfl,rfl⟩

end E2E.CallStoreTrapSourceWitness
