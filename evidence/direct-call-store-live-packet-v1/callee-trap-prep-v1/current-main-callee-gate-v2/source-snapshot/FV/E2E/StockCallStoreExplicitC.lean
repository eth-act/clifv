import FV.E2E.TrapCallClifRun
import FV.Clif.MemTrap

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- The existing callee-trap-only premise excludes memory traps; fault-aware variants remain separate. -/
theorem no_memory_trap_of_explicitC {env : Clif.Env} {p : Clif.Program} {initial current : Clif.State}
    (explicit : TrapsExplicitC env p initial) {code : Clif.TrapCode} {address bytes : Nat}
    (reached : Reach env p initial current)
    (memoryTrap : Clif.MemTrapAt env p current code address bytes) : False := by
  obtain ⟨step,invalid,statement,rest,body,access⟩ := memoryTrap
  have allowed := explicit.stmt current code statement rest reached step body
  obtain ⟨results,inst⟩ := statement
  cases access <;> simp [explicitTrapInst,CallInst] at allowed

end E2E
