import FV.Link.ReturnPinExeWith
import FV.Link.ReturnPinCompileWith
import FV.Link.ReturnPinRetryWitness
import FV.E2E.ReturnPinExecWitness
import FV.E2E.PreparedReturnPinCallsWitness

namespace Link.ReturnPinCompilerWitness
open Backend E2E E2E.LinkCheck E2E.SemanticBinary
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

abbrev lower := ReturnPinRetryWitness.lower
abbrev initial := ReturnPinRetryWitness.initial
abbrev spec := ReturnPinRetryWitness.spec
abbrev file0 := ReturnPinRetryWitness.file0
abbrev file := ReturnPinRetryWitness.file

def input (cleanup : Bool) : SemanticStackBound.CompilerInput :=
  ReturnPinCompilerWith.input lower (spec cleanup) cleanup


theorem compiler_success (cleanup : Bool) :
    ReturnPinCompilerWith.attempt lower (spec cleanup) (file0 cleanup) cleanup = .ok (file cleanup) :=
  ReturnPinRetryWitness.compiler_success cleanup

/-- Preserve the exact original source records through placement and actual compilation. -/
theorem original_source (cleanup : Bool) :
    (input cleanup).funcs = PreparedReturnPinCallsWitness.input.funcs := by
  rfl

attribute [local irreducible] input

-- witness: native_decide (the old physical return contract rejects both complete mixed programs)
theorem old_rejected (cleanup : Bool) : SemanticStackBound.okB (input cleanup) = false := by
  cases cleanup <;> native_decide

private def stockChecks (cleanup : Bool) : Bool :=
  (prog (input cleanup)).funcs.all fun f => match Stock.lower f with
  | .error _ => false
  | .ok result => decide ((art (input cleanup) f).vc = result.code)

attribute [local irreducible] stockChecks

-- witness: native_decide (actual Stock artifacts for both unchanged mixed functions)
theorem actual_stock (cleanup : Bool) : stockChecks cleanup = true := by
  cases cleanup <;> native_decide

-- witness: native_decide (the complete unchanged mixed source contains no TLS instruction)
theorem no_tls (cleanup : Bool) : (prog (input cleanup)).funcs.all (fun f => !hasTls f) = true := by
  cases cleanup <;> native_decide

theorem contract (cleanup : Bool) :
    (SemanticStackBound.ofInput (input cleanup) closedBase (img (input cleanup))).OkSemanticReturnPins := by
  have checked := (ReturnPinCompilerWith.attempt_spec (compiler_success cleanup)).1
  have base : BaseOk (SemanticStackBound.ofInput (input cleanup) closedBase (img (input cleanup))) :=
    baseOk_closedR fun f member => by
      simpa only [Bool.not_eq_true'] using List.all_eq_true.mp (no_tls cleanup) f member
  exact ReturnPinBinary.okB_sound checked base (fun _ h => h)

end Link.ReturnPinCompilerWitness

namespace Link.ReturnPinCompilerWitness
open Backend E2E E2E.LinkCheck E2E.SemanticBinary
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def caller : Clif.Function := PreparedReturnPinCallsWitness.input.funcs[1]!.func

def initialMachine (cleanup : Bool) : Arm.ArmState :=
  let image := file cleanup
  Arm.w .PC (art (input cleanup) caller).base
    (Arm.w (.GPR 31#5) 0x1000000#64
      (Arm.w (.GPR 30#5) 0x8000000#64
        (Arm.w (.GPR 0#5) 0x400000#64 (Arm.w (.GPR 1#5) 0x500000#64
          {Arm.ArmState.default with mem := fun address => ite (0x500000 ≤ address.toNat ∧ address.toNat < 0x500010) (BitVec.ofNat 8 (address.toNat - 0x500000 + 1)) ((Elf.loadMem image address).getD 0)}))))

def executeImage (image : ByteArray) : Nat → Arm.ArmState → Arm.ArmState
  | 0,state => state
  | fuel+1,state => if Arm.r .PC state = 0x8000000#64 then state
      else executeImage image fuel (E2E.SemanticExecBytes.realStep image state)

def execute (cleanup : Bool) : Nat → Arm.ArmState → Arm.ArmState := executeImage (file cleanup)

def runtimeChecks (cleanup : Bool) : Bool :=
  let final := execute cleanup 100 (initialMachine cleanup)
  decide (Arm.r .ERR final = .None) && decide (Arm.r .PC final = 0x8000000#64) &&
  decide (spv final = 0x1000000#64) && decide (xreg 8 final = 0x400000#64) &&
  (List.range 16).all (fun i => decide (final.mem (BitVec.ofNat 64 (0x400000+i)) = BitVec.ofNat 8 (i+1))) &&
  (List.range 16).all (fun i => decide (final.mem (BitVec.ofNat 64 (0x500000+i)) = BitVec.ofNat 8 (i+1)))


-- witness: native_decide (actual encoded mixed ELF, two fixed heaps, and both cleanup modes)
theorem actual_mixed_execution : (runtimeChecks false && runtimeChecks true) = true := by native_decide

end Link.ReturnPinCompilerWitness
