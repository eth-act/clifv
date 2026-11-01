import FV.E2E.LinkReturnPinsWitness
import FV.E2E.LinkReturnPinProgram

namespace E2E.LinkReturnPinProgramWitness
open Backend Backend.Proof Backend.Proof.Driver LinkWitness
set_option autoImplicit false
set_option Elab.async false

/-- All original system conditions jointly inhabit the shared program theorem.
The retained linked fixture contains both a caller and a callee. -/
theorem ordinary_program_contract_witness :
    ∃ (system : LinkSys) (κ : Nat → Clif.Function → Nat),
      system.OkReturnPins (fun _ => .ordinary) ∧ system.Budget κ ∧
      (∀ M, system.ThmReturnPins (fun _ => .ordinary) κ M) ∧
      fG ∈ system.P.funcs ∧ fH ∈ system.P.funcs := by
  let system := (L fun _ => True).std
  have old : (L fun _ => True).Ok := L_ok _ (fun _ _ => trivial)
  have ordinary : system.OkSemanticNI := (old.withCrun _).toSemanticNI
  have checked := ordinary.toReturnPins
  haveI : system.CrunOk := (L fun _ => True).crunOk_std old
  have budget := system.budget_K_return_pins checked
  refine ⟨system,(fun M _ => system.K M),checked,budget,
    system.thm_return_pins checked budget,?_,?_⟩
  · change fG ∈ P.funcs
    simp [P]
  · change fH ∈ P.funcs
    simp [P]

/-- The shared model makes the retained successful call with a nonzero result.
The full original system contract accompanies the actual source run. -/
theorem successful_shared_call_witness :
    ∃ (system : LinkSys) (κ : Nat → Clif.Function → Nat) (M : Nat)
      (F : BitVec 64 → Prop) (w : Arm.ArmState) (memory : Clif.Mem)
      (cs : Clif.State) (cm : Clif.Mem) (values : List CV) (next : Arm.ArmState),
      system.OkReturnPins (fun _ => .ordinary) ∧
      Clif.initState system.P fH.name [⟨.i64,41⟩] memory = .ok cs ∧
      system.crun M cs = .returned [⟨.i64,42⟩] cm ∧
      system.progXMode (fun _ => .ordinary) κ M F fH [41] w = some (values,next) ∧
      values.length = 1 ∧ PrefixHold [⟨.i64,42⟩] values := by
  obtain ⟨old,cs,cm,values,next,entered,returned,called,_,arity,held⟩ :=
    LinkReturnPinsWitness.successful_program_call_witness
  exact ⟨_,_,_,_,_,_,cs,cm,values,next,old.toSemanticNI.toReturnPins,
    entered,returned,called,arity,held⟩

/-- The unchanged sret capture compiles in both modes and checks its actual return register.
The same checker rejects x0 and accepts a call that ignores the implicit result. -/
theorem checked_sret_calls_witness (cleanup : Bool) :
    let f := Backend.Stock.Memory.StoreRoots.ComputedFixture.function
    ∃ (result : Stock.Result) (prepared : VCode) (allocated : RFunc) (frame : AFunc)
      (assembly : FnAsm) (binary : FnBin),
      Stock.lower f = .ok result ∧
      ReturnPinMode.checked f result.code = .stockABI ∧
      CompiledSemanticReturnPins f 0 result.code prepared allocated frame assembly binary .stockABI ∧
      ReturnPinCheck.check [(.x 8,.vreg 0 .int)] f result.code = true ∧
      ReturnPinCheck.check [(.x 0,.vreg 0 .int)] f result.code = false ∧
      ReturnPinCheck.check [] f result.code = true := by
  let f := Backend.Stock.Memory.StoreRoots.ComputedFixture.function
  obtain ⟨result,prepared,allocated,frame,assembly,binary,lowered,_,mode,artifact,_,_⟩ :=
    CompiledSemanticReturnPinsWitness.checked_sret_pins_witness cleanup
  have pins : ReturnPinCheck.pins f result.code = [.x 8] := by
    rw [returnPinCheck_pins,mode]
    exact LinkReturnPinsWitness.sret_prefix_witness.1
  refine ⟨result,prepared,allocated,frame,assembly,binary,lowered,mode,?_,?_,?_,
    returnPinCheck_ignored f result.code⟩
  · simpa only [mode] using artifact
  · unfold ReturnPinCheck.check
    change decide ((_ : List Reg).take (ReturnPinCheck.pins f result.code).length =
      (ReturnPinCheck.pins f result.code).take 1) = true
    rw [pins]
    decide +kernel
  · unfold ReturnPinCheck.check
    change decide ((_ : List Reg).take (ReturnPinCheck.pins f result.code).length =
      (ReturnPinCheck.pins f result.code).take 1) = false
    rw [pins]
    decide +kernel

end E2E.LinkReturnPinProgramWitness
