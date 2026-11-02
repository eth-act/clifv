namespace Link.ReturnPinCompilerWitness
open Backend E2E E2E.LinkCheck E2E.SemanticBinary
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def caller : Clif.Function := PreparedReturnPinCallsWitness.input.funcs[1]!.func

def initialMachine (cleanup : Bool) : Arm.ArmState :=
  Arm.w .PC (art (input cleanup) caller).base
    (Arm.w (.GPR 31#5) 0x1000000#64
      (Arm.w (.GPR 30#5) 0x8000000#64
        (Arm.w (.GPR 0#5) 0x400000#64 (Arm.w (.GPR 1#5) 0x500000#64
          {Arm.ArmState.default with mem := fun address =>
            if 0x500000 ≤ address.toNat && address.toNat < 0x500010 then
              BitVec.ofNat 8 (address.toNat - 0x500000 + 1)
            else (Elf.loadMem (file cleanup) address).getD 0}))))

def execute (cleanup : Bool) : Nat → Arm.ArmState → Arm.ArmState
  | 0,state => state
  | fuel+1,state => if Arm.r .PC state = 0x8000000#64 then state
      else execute cleanup fuel (E2E.SemanticExecBytes.realStep (file cleanup) state)

def runtimeChecks (cleanup : Bool) : Bool :=
  let final := execute cleanup 100 (initialMachine cleanup)
  decide (Arm.r .ERR final = .None) && decide (Arm.r .PC final = 0x8000000#64) &&
  decide (spv final = 0x1000000#64) && decide (xreg 8 final = 0x400000#64) &&
  (List.range 16).all (fun i => decide (final.mem (BitVec.ofNat 64 (0x400000+i)) = BitVec.ofNat 8 (i+1))) &&
  (List.range 16).all (fun i => decide (final.mem (BitVec.ofNat 64 (0x500000+i)) = BitVec.ofNat 8 (i+1)))

#eval (runtimeChecks false,runtimeChecks true)

-- witness: native_decide (actual encoded mixed ELF, two fixed heaps, and both cleanup modes)
theorem actual_mixed_execution : (runtimeChecks false && runtimeChecks true) = true := by native_decide

#print axioms actual_mixed_execution
end Link.ReturnPinCompilerWitness
