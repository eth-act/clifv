import FV.E2E.StockCallStoreSourceWitness

namespace E2E.CallStoreTrapSourceWitness
open Backend Backend.Proof Backend.Proof.Driver CallStoreFixture CallStoreSourceWitness
set_option autoImplicit false
set_option Elab.async false

/-- This extra callee fixture does not replace the preserved arithmetic callee. -/
def trappingCallee : Clif.Function := {callee with
  blocks := [{id := 0,params := [(101,.i64)],body := [],term := .trap .user1}]}
def trappingProgram : Clif.Program := {funcs := [caller,trappingCallee]}

/-- The original caller reaches the actual callee trap before its default-flag store.
Both arguments and the initial memory remain arbitrary. -/
theorem actual_source_callee_trap (pointer word : BitVec 64) (memory : Clif.Mem) :
    Clif.enterFunc caller [value pointer,value word] memory = .ok (frame pointer word,memory) ∧
    Clif.runLoop Clif.Env.empty trappingProgram 2 ⟨frame pointer word,[],memory⟩ =
      .trapped .user1 := by
  exact ⟨rfl,rfl⟩

end E2E.CallStoreTrapSourceWitness
