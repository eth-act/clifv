import FV.E2E.PreparedReturnPinCallsWitness
import FV.E2E.SrcScopeDefs
import FV.E2E.SretCopyHeapBoundary
import FV.Backend.Proof.StockMemorySretCopyBodyWitness

namespace E2E.SretHeapBoundary
open Backend Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- The unchanged parsed capture inhabits source entry and the complete symbolic copy outcome. -/
theorem captured_symbolic_entry (contents : Nat → BitVec 8) (syms : String → Option Nat)
    (initial : Arm.ArmState) (env : Clif.Env) (program : Clif.Program) :
    ∃ (cs : Clif.State) (w : Arm.ArmState) (cm : Clif.Mem),
      ClifEntry Stock.Memory.StoreRoots.ComputedFixture.function arguments cs ∧
      MemRel reserved syms cs.mem w ∧
      ArgsAtEntry reserved Stock.Memory.StoreRoots.ComputedFixture.function.sig arguments w ∧
      Clif.runLoop env program 12 cs = .returned [] cm ∧
      (∀ k < 16,cm.bytes (0x400000+k) = some (contents k)) ∧
      (∀ k < 16,cm.bytes (0x500000+k) = some (contents k)) := by
  have same : Stock.Memory.StoreRoots.ComputedFixture.function =
      Source.function "_RNxC7fv_demo11HawPMC3YC2b" := by
    rw [Stock.Memory.SretCopy.Fixture.captured_sret_source_shape_witness]
    rfl
  rw [same]
  exact ⟨entryState (Source.function "_RNxC7fv_demo11HawPMC3YC2b") Source.first (heap contents syms),
    machine contents initial,Source.copied contents syms,
    Source.entry _ contents syms,machine_memory_relation contents syms initial,
    entry_arguments contents initial,Source.returns_exact _ contents syms env program,
    fun _ bound => Source.copied_byte contents syms bound,
    fun _ bound => Source.copied_source_byte contents syms bound⟩

end E2E.SretHeapBoundary


namespace E2E.SretHeapBoundary
open Backend Backend.Proof Backend.Proof.Driver E2E.LinkCheck
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def originalProgram : Clif.Program := PreparedReturnPinCallsWitness.input.srcProg
private def originalCaller : Clif.Function := PreparedReturnPinCallsWitness.input.funcs[1]!.src

-- witness: native_decide (the two unchanged parsed functions only)
private theorem original_program : originalProgram = Caller.program := by native_decide
-- witness: native_decide (the unchanged parsed caller only)
private theorem original_caller : originalCaller = Caller.function := by native_decide

/-- The unchanged mixed source jointly inhabits entry, heap, ABI arguments, and the full byte outcome. -/
theorem captured_mixed_symbolic_entry (contents : Nat → BitVec 8) (syms : String → Option Nat)
    (initial : Arm.ArmState) (env : Clif.Env) :
    ∃ (cs : Clif.State) (w : Arm.ArmState) (cm : Clif.Mem),
      ClifEntry originalCaller arguments cs ∧ MemRel reserved syms cs.mem w ∧
      ArgsAtEntry reserved originalCaller.sig arguments w ∧
      Clif.runLoop env originalProgram 16 cs = .returned [] cm ∧
      (∀ k < 16,cm.bytes (0x400000+k) = some (contents k)) ∧
      (∀ k < 16,cm.bytes (0x500000+k) = some (contents k)) := by
  rw [original_program,original_caller]
  exact Caller.symbolic_entry contents syms initial env

end E2E.SretHeapBoundary

