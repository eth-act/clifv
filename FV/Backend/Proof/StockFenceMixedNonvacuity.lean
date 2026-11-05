import FV.Backend.Proof.StockFenceMixedDomain
import FV.Backend.Proof.StockFenceAccessWitness

namespace Backend.Stock.Proof.FenceFixture
open Backend.Proof Backend.Proof.Driver MemoryFaults
set_option autoImplicit false
set_option Elab.async false

def completeMemory : Clif.Mem := {allocs := [⟨0,24,false⟩],bytes := fun _ => some 0}

private theorem returned_of_values (out : Clif.Outcome) {vals : List Clif.Val}
    (observed : out.returnedVals? = some vals) : ∃ mem,out = .returned vals mem := by
  cases out with
  | returned values mem => exact ⟨mem,by cases observed; rfl⟩
  | trapped code => cases observed
  | stuck message => cases observed
  | outOfFuel => cases observed

private def trapCode (out : Clif.Outcome) : Option Clif.TrapCode :=
  match out with
  | .trapped code => some code
  | _ => none

private theorem trapped_of_code (out : Clif.Outcome) {code : Clif.TrapCode}
    (observed : trapCode out = some code) : out = .trapped code := by
  cases out with
  | trapped actual => cases observed; rfl
  | returned values mem => cases observed
  | stuck message => cases observed
  | outOfFuel => cases observed

private theorem return_observed :
    (Clif.runLoop {} ⟨[],[],[function]⟩ 8 ⟨faultEntry 0 1,[],completeMemory⟩).returnedVals? =
      some [Clif.Val.ofNat .i64 0] := by native_decide -- witness: native_decide

private theorem division_observed :
    trapCode (Clif.runLoop {} ⟨[],[],[function]⟩ 6 ⟨faultEntry 0 0,[],completeMemory⟩) =
      some .intDivz := by native_decide -- witness: native_decide

/-- All seven statements execute and the unchanged complete mixed function returns. -/
theorem mixed_complete_return :
    ∃ mem,Clif.runLoop {} ⟨[],[],[function]⟩ 8 ⟨faultEntry 0 1,[],completeMemory⟩ =
      .returned [Clif.Val.ofNat .i64 0] mem :=
  returned_of_values _ return_observed

/-- Both fences precede the real zero-divisor trap after the computed store. -/
theorem mixed_complete_division_trap :
    Clif.runLoop {} ⟨[],[],[function]⟩ 6 ⟨faultEntry 0 0,[],completeMemory⟩ = .trapped .intDivz :=
  trapped_of_code _ division_observed

/-- One unchanged complete input inhabits the universal return and fault-aware domain. -/
theorem mixed_complete_domain_witness :
    DomainWithAccessTraps function ∧
      SourceEntry function (faultArguments 0 1) (faultEntry 0 1) ∧
      (∃ mem,Clif.runLoop {} ⟨[],[],[function]⟩ 8 ⟨faultEntry 0 1,[],completeMemory⟩ =
        .returned [Clif.Val.ofNat .i64 0] mem) ∧
      Clif.runLoop {} ⟨[],[],[function]⟩ 6 ⟨faultEntry 0 0,[],completeMemory⟩ = .trapped .intDivz ∧
      Clif.runLoop {} ⟨[],[],[function]⟩ 1 ⟨faultEntry 0 1,[],Clif.Mem.empty⟩ = .trapped .heapOob :=
  ⟨mixed_domain_with_access_traps,fault_source_entry 0 1,mixed_complete_return,
    mixed_complete_division_trap,unallocated_first_access_traps 0 1 {} ⟨[],[],[function]⟩⟩

end Backend.Stock.Proof.FenceFixture
