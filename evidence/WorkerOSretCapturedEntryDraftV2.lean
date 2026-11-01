import FV.E2E.SretCopyExecBoundary
import FV.Link.ReturnPinRetryWitness

namespace E2E.SretCapturedEntry
open Backend Backend.Proof Backend.Proof.Driver E2E.LinkCheck E2E.SemanticBinary
open E2E.SretHeapBoundary E2E.SretExecBoundary
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def input (cleanup : Bool) : SemanticStackBound.CompilerInput :=
  Link.ReturnPinCompilerWith.input Link.ReturnPinRetryWitness.lower
    (Link.ReturnPinRetryWitness.spec cleanup) cleanup
private def file (cleanup : Bool) : ByteArray := Link.ReturnPinRetryWitness.file cleanup
private def segments (cleanup : Bool) : List Elf.Phdr :=
  (Elf.phdrs (Elf.fileRd (file cleanup))).getD []
private def budget (cleanup : Bool) : Nat :=
  frameDrop (art (input cleanup) Caller.function).af + (input cleanup).D * 15
private def staticChecks (cleanup : Bool) : Bool :=
  decide (prog (input cleanup) = Caller.program) &&
  (tabOf (input cleanup).results).all
    (fun e => decide (e.2.base.toNat + 4 * e.2.fb.words.size ≤ 0x300000)) &&
  decide (budget cleanup ≤ 4096) &&
  decide (Elf.phdrs (Elf.fileRd (file cleanup)) = some (segments cleanup)) &&
  (segments cleanup).all (fun p => decide (p.vaddr + p.memsz ≤ 0x300000)) &&
  decide ((Link.ReturnPinRetryWitness.spec cleanup).data = [])

attribute [local irreducible] input file segments budget staticChecks

-- witness: native_decide (static facts for the two original complete linked images only)
private theorem static_checks (cleanup : Bool) : staticChecks cleanup = true := by
  cases cleanup <;> native_decide

private theorem static_facts (cleanup : Bool) :
    prog (input cleanup) = Caller.program ∧
    (tabOf (input cleanup).results).all
      (fun e => decide (e.2.base.toNat + 4 * e.2.fb.words.size ≤ 0x300000)) = true ∧
    budget cleanup ≤ 4096 ∧
    Elf.phdrs (Elf.fileRd (file cleanup)) = some (segments cleanup) ∧
    (∀ p ∈ segments cleanup,p.vaddr + p.memsz ≤ 0x300000) ∧
    (Link.ReturnPinRetryWitness.spec cleanup).data = [] := by
  simpa only [staticChecks,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,and_assoc] using static_checks cleanup

private theorem image_bound (cleanup : Bool) {a : BitVec 64} (inside : img (input cleanup) a) :
    a.toNat < 0x300000 :=
  ProductionBoundaryWitness.image_bound (by decide) (static_facts cleanup).2.1 inside

/-- The exact original linked caller has a complete executable entry for arbitrary source bytes. -/
-- witness: native_decide (only the fixed images' static facts; all heap contents remain symbolic)
theorem captured_entry (cleanup : Bool) (contents : Nat → BitVec 8) :
    ∃ r : Arm.ArmState,
      OutsideCall (input cleanup) (BinCheck.roByte (input cleanup)
        (Link.ReturnPinRetryWitness.spec cleanup).data) Caller.function (budget cleanup) r arguments
        (heap contents (fun name => (input cleanup).syms.lookup name)) ∧
      ClifRun (input cleanup) closedBase Caller.function r arguments
        (entryState Caller.function Caller.first (heap contents (fun name => (input cleanup).syms.lookup name))) ∧
      (imageOf (file cleanup)).Intact r ∧
      Clif.runLoop closedBase.env (prog (input cleanup)) 16
        (entryState Caller.function Caller.first (heap contents (fun name => (input cleanup).syms.lookup name))) =
        .returned [] (Source.copied contents (fun name => (input cleanup).syms.lookup name)) := by
  let memory : BitVec 64 → BitVec 8 := fun a => (Elf.loadMem (file cleanup) a).getD 0
  let r := machine contents (art (input cleanup) Caller.function).base memory
  refine ⟨r,?_,?_,?_,?_⟩
  · apply outside_call rfl (static_facts cleanup).2.2.1 (fun _ code => image_bound cleanup code)
    intro a range
    rw [(static_facts cleanup).2.2.2.2.2]
    rfl
  · apply clif_run (input cleanup) closedBase ?_ contents memory
    intro f member
    rw [(static_facts cleanup).1] at member
    simp only [Caller.program,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> rfl
  · exact image_intact (static_facts cleanup).2.2.2.1
      (fun p member _ => (static_facts cleanup).2.2.2.2.1 p member) contents _
  · rw [(static_facts cleanup).1]
    exact Caller.returns_exact contents _ closedBase.env

end E2E.SretCapturedEntry

#print axioms E2E.SretCapturedEntry.captured_entry
