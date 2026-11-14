import FV.E2E.StockMemoryMachine
import FV.Backend.StockMemorySinkEffects

/-! The machine consumer of the sinking load/extension class. The checked code has
only ABI copies, loads, acquiring loads and returns, none of which has a separate
value specification, so the production value consumer runs the concrete semantics. -/
namespace E2E.StockMemory
open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup
set_option autoImplicit false
set_option Elab.async false

/-- The plain memory whitelist is part of the sinking-class whitelist. -/
theorem sinkEffectsOnly_of_effectsOnly {vc : VCode} (checked : effectsOnly vc = true) :
    Backend.Stock.Memory.sinkEffectsOnly vc = true := by
  apply List.all_eq_true.mpr
  intro vb member
  apply List.all_eq_true.mpr
  intro i present
  have blocks := List.all_eq_true.mp checked vb member
  have good := List.all_eq_true.mp blocks i present
  cases i <;> simp_all [Backend.Stock.Memory.effectInstruction,Backend.Stock.Memory.sinkEffectInstruction]

/-- Sinking-class code calls no TLS helper. -/
theorem sinkEffectsOnly_noTls {vc : VCode} (checked : Backend.Stock.Memory.sinkEffectsOnly vc = true) :
    vc.hasTls = false := by
  rw [VCode.hasTls,Array.any_eq_false']
  intro vb member
  apply Bool.eq_false_iff.mp
  apply Array.any_eq_false'.mpr
  intro i present
  have blocks := List.all_eq_true.mp checked vb (Array.mem_toList_iff.mpr member)
  have good := List.all_eq_true.mp blocks i (Array.mem_toList_iff.mpr present)
  cases i <;> simp_all [Backend.Stock.Memory.sinkEffectInstruction]

private theorem sink_spec_instruction {vc : VCode}
    (checked : Backend.Stock.Memory.sinkEffectsOnly vc = true)
    {b k : Nat} {vb : VBlock} {i : MInst}
    (block : vc.blocks[b]? = some vb) (inst : vb.insts[k]? = some i) :
    specForm i = false := by
  have blocks := List.all_eq_true.mp checked vb (by simpa using Array.mem_of_getElem? block)
  have instruction := List.all_eq_true.mp blocks i (by simpa using Array.mem_of_getElem? inst)
  cases i <;> simp_all [Backend.Stock.Memory.sinkEffectInstruction,specForm,pureForm,cmpForm]

private theorem sink_value_star {vc : VCode}
    (checked : Backend.Stock.Memory.sinkEffectsOnly vc = true)
    {F : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem} {s t : VConf CV Arm.ArmState}
    (path : Star (VStep vc (csem F fc X)) s t) : Star (VStep vc (valueSem F fc X)) s t := by
  induction path with
  | refl => exact .refl _
  | step first rest ih =>
    refine .step ?_ ih
    cases first with
    | step block inst operands run arity next =>
      refine .step block inst operands ?_ arity next
      simpa only [valueSem,sink_spec_instruction checked block inst,Bool.false_eq_true,ite_false] using run

/-- On checked sinking-class code, the production value consumer executes exactly the
concrete run, including its final world and ABI output tuple. -/
theorem sink_return_value {vc : VCode} (checked : Backend.Stock.Memory.sinkEffectsOnly vc = true)
    {F : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem} {vs : VState CV Arm.ArmState}
    {us : List (Reg × Reg)} {outs : List CV} {world : Arm.ArmState}
    (returned : VRetFrom vc (csem F fc X) vs us outs world) :
    VRetFrom vc (valueSem F fc X) vs us outs world := by
  obtain ⟨b,k,ρ,w,vb,ops,results,path,block,inst,operands,values,run⟩ := returned
  refine ⟨b,k,ρ,w,vb,ops,results,sink_value_star checked path,block,inst,operands,values,?_⟩
  simpa only [valueSem,sink_spec_instruction checked block inst,Bool.false_eq_true,ite_false] using run

/-- Actual sinking-class Stock returns use the existing checked allocation,
cleanup/preparation, encoding and machine consumer with exact value semantics. -/
theorem sink_machine_return {f : Clif.Function} {args : List Clif.Val}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin} {k : Nat}
    {cleanup : Bool} (effects : Backend.Stock.Memory.sinkEffectsOnly vc = true)
    (prep : prepCheck (Stock.Arithmetic.stage cleanup vc) vcp = true)
    (check : checkAlloc vcp rf = .ok ()) (alloc : lowerRFunc vcp rf = .ok af)
    (emit : emitFunc k af = .ok fa) (layout : fa.layout = .ok fb)
    {X : ExtSem} {K : Nat} {F Z : BitVec 64 → Prop}
    (frame : ∀ a, F a → Z a) (covered : FormsCovered ⟨fa.k,af.slotBase⟩ vcp)
    {w final reference : Arm.ArmState} (arguments : ArgsAtEntry F f.sig args w)
    (worlds : SameWorld Z final reference)
    {ρ : Nat → CV} {us : List (Reg × Reg)} {outs : List CV}
    (returned : VReturns vc (csem F ⟨fa.k,af.slotBase⟩ X) ρ w us outs final)
    (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState)
    (entry : ActEntry vcp rf af fa fb K F G X H base ra s w) :
    ∃ n, ActRet ra Z G us outs reference s (runX (ArmStepX X H fa) n s) ∧
      PostTrace fa af base (ArmStepX X H fa) s n ∧
      ∀ i < n, actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
        (runX (ArmStepX X H fa) i s) := by
  have valueRun := sink_return_value effects returned
  let t := final
  have finalWorld := worlds
  have prepared := StockArithmeticStage_returns prep valueRun
  have machine := regLevelCorrect_worldX_value check alloc emit layout
    (X := X) (H := H) (K := K) (G := G) (gv := GotV vcp)
    covered entry.abi entry.stack entry.gfree (by rw [entry.hF]; exact entry.calls)
    (by rw [entry.hF]; exact entry.tries) (by rw [entry.hF]; exact entry.tls)
    (by rw [entry.hF]; exact entry.body) ρ
  rw [entry.hF] at machine
  obtain ⟨n,⟨h1,h2,h3,h4,h5,h6,h7⟩,h8⟩ :=
    machine.1 us outs t (vReturns_gotV_value prepared)
  refine ⟨n,⟨h1,h2,?_,?_,h5,h6⟩,h7,h8⟩
  · intro a outside
    rw [h3 a (fun hf => outside (frame a hf))]
    exact finalWorld.2.1 a outside
  · intro field unmasked fp sp
    rw [h4 field unmasked fp sp]
    exact finalWorld.1 field unmasked

end E2E.StockMemory
