import FV.Backend.Proof.LowerValueRelations
import FV.E2E.ABIReadOnlyTransport

namespace E2E.ABIReadOnly
open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup
set_option autoImplicit false
set_option Elab.async false

/-- Read-only checked code has no branch, trap or effectful control outcome. -/
theorem step_control {sig : Clif.Signature} {b k : Nat} {i : MInst}
    (checked : Backend.ABIReadOnly.instruction sig b k i = true)
    {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {us outs : List CV}
    {w w' : Arm.ArmState} {ctl : Ctl}
    (executed : sem F ctx X i us w = some (outs,w',ctl)) : ctl = .next ∨ ctl = .ret := by
  rcases instruction_cases checked with pure | ⟨pairs,rfl,_⟩ |
      ⟨op,key,off,fl,rfl,hop,_⟩ | ⟨pairs,rfl⟩
  · have hs : mspec ctx.slotBase i us w = some (outs,w',ctl) := by
      cases i <;> simpa only [sem,valueSem,specForm_of_pure pure,↓reduceIte] using executed
    exact .inl (mspec_pure pure hs).2
  · simp [sem,valueSem,specForm, pureForm, cmpForm, Bool.false_or,csem] at executed
    exact .inl executed.2.2.symm
  · simp only [sem,mspec,hop,ite_false,Option.map_eq_some_iff,Prod.mk.injEq] at executed
    obtain ⟨a,_,_,_,control⟩ := executed
    exact .inl control.symm
  · simp [sem,valueSem,specForm, pureForm, cmpForm, Bool.false_or,csem] at executed
    exact .inr executed.2.2.symm

/-- Realize one unchanged-world step by the shipped value semantics. The only
world-dependent reads are original ABI reads validated by the executable check. -/
theorem step_realize {sig : Clif.Signature} {args : List Clif.Val}
    (types : args.map (·.ty) = sig.params.map (·.ty))
    {b k : Nat} {i : MInst} (checked : Backend.ABIReadOnly.instruction sig b k i = true)
    {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {w t : Arm.ArmState}
    (arguments : ArgsAtEntry F sig args w) (worlds : SameWorld F t w)
    (entry : k = 0 → t = w) {us outs : List CV} {ctl : Ctl}
    (executed : sem F ctx X i us w = some (outs,w,ctl)) :
    ∃ t', valueSem F ctx X i us t = some (outs,t',ctl) ∧ SameWorld F t' w := by
  rcases instruction_cases checked with pure | ⟨pairs,rfl,_,zero,_⟩ |
      ⟨op,key,off,fl,rfl,hop,read⟩ | ⟨pairs,rfl⟩
  · have hs : mspec ctx.slotBase i us w = some (outs,w,ctl) := by
      cases i <;> simpa only [sem,valueSem,specForm_of_pure pure,↓reduceIte] using executed
    have noMem : i.isMemAcc = false := by cases i <;> simp_all [pureForm,MInst.isMemAcc]
    obtain ⟨t',run,related⟩ := mspec_lockstep noMem worlds.symm hs
    have fixed := (mspec_pure pure run).1
    subst t'
    refine ⟨t,?_,worlds⟩
    simp only [valueSem,specForm_of_pure pure,↓reduceIte]
    exact run
  · have same := entry zero
    subst t
    exact ⟨w,by simpa [sem] using executed,SameWorld.refl F w⟩
  · obtain ⟨slot,v,member,offset,width⟩ := stackRead_argument types read
    have abi := arguments (.stack slot) v member
    have fp : Arm.r (.GPR 29#5) t = Arm.r (.GPR 29#5) w :=
      worlds.1 (.GPR 29#5) (by simp [Masked])
    have avoids : Avoids F op.bytes (Arm.r (.GPR 29#5) w + BitVec.ofInt 64 off) := by
      intro j hj
      rw [offset]
      exact abi.1 j (by omega)
    have data := loadVal_congr op worlds.2.1 avoids
    cases us with
    | nil =>
      have source : outs = [ofX (loadVal op (Arm.r (.GPR 29#5) w + BitVec.ofInt 64 off) w)] ∧
          ctl = .next := by
        simpa [sem,mspec,hop,amodeAddr,eq_comm] using executed
      obtain ⟨t',run,related⟩ :=
        (memRefines_valueSem F ctx X (syms := fun _ => none) rfl
          (fun _ _ h => by cases h)).1 op key (.fpOffset off) fl [] t
          (Arm.r (.GPR 29#5) w + BitVec.ofInt 64 off) hop
          (by simp [amodeAddr,fp]) avoids
      refine ⟨t',?_,related.trans worlds⟩
      simpa only [source.1,source.2,data] using run
    | cons a us => simp [sem,mspec,hop,amodeAddr] at executed
  · refine ⟨t,?_,worlds⟩
    simp [sem,valueSem,specForm, pureForm, cmpForm, Bool.false_or,csem] at executed ⊢
    exact executed

/-- The original read-only configuration has its initial world; the realized
configuration has the same PC/virtual values and a related concrete world.
Only PC zero may still read physical ABI argument registers. -/
def Related (F : BitVec 64 → Prop) (w : Arm.ArmState)
    (c d : VConf CV Arm.ArmState) : Prop :=
  ∃ t, c.mapW (fun _ => w) = c ∧ d = c.mapW (fun _ => t) ∧ SameWorld F t w ∧
    ∀ vs, c = .run vs → vs.k = 0 → t = w

private theorem realize_step {sig : Clif.Signature} {args : List Clif.Val}
    (types : args.map (·.ty) = sig.params.map (·.ty))
    {vc : VCode} (checked : Backend.ABIReadOnly.check sig vc = true)
    {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {w : Arm.ArmState}
    (arguments : ArgsAtEntry F sig args w)
    {c c' d : VConf CV Arm.ArmState} (related : Related F w c d)
    (step : VStep vc (sem F ctx X) c c') :
    ∃ d', VStep vc (valueSem F ctx X) d d' ∧ Related F w c' d' := by
  obtain ⟨t,fixed,rfl,worlds,entry⟩ := related
  cases step with
  | @step b k ρ w0 vb i ops outs w1 ctl target hb hi hops run arity successor =>
    have eq : w0 = w := by
      have state := VConf.run.inj fixed
      exact (congrArg VState.w state).symm
    subst w0
    have supported := checked_instruction checked hb hi
    have unchanged := step_world supported run
    subst w1
    obtain ⟨t',realized,related'⟩ := step_realize types supported arguments worlds
      (entry _ rfl) run
    refine ⟨c'.mapW (fun _ => t'),
      VStep.step hb hi hops realized arity (vnext_map vc (fun _ => t') successor),?_⟩
    have control := step_control supported run
    cases successor with
    | next hk =>
      refine ⟨t',rfl,rfl,related',?_⟩
      intro vs eq zero
      cases eq
      change k + 1 = 0 at zero
      omega
    | goto => rcases control with control | control <;> cases control
    | ret => exact ⟨t',rfl,rfl,related',fun vs eq => by cases eq⟩
    | halt => rcases control with control | control <;> cases control

/-- The checked allocator's existing value semantics realizes the complete
unchanged-world execution, with identical virtual definitions and return pins. -/
theorem star_realize {sig : Clif.Signature} {args : List Clif.Val}
    (types : args.map (·.ty) = sig.params.map (·.ty))
    {vc : VCode} (checked : Backend.ABIReadOnly.check sig vc = true)
    {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {w : Arm.ArmState}
    (arguments : ArgsAtEntry F sig args w)
    {c c' d : VConf CV Arm.ArmState} (related : Related F w c d)
    (path : Star (VStep vc (sem F ctx X)) c c') :
    ∃ d', Star (VStep vc (valueSem F ctx X)) d d' ∧ Related F w c' d' := by
  induction path generalizing d with
  | refl => exact ⟨d,.refl _,related⟩
  | step first rest ih =>
    obtain ⟨d1,first',related'⟩ := realize_step types checked arguments related first
    obtain ⟨d',tail,final⟩ := ih related'
    exact ⟨d',.step first' tail,final⟩

/-- A complete read-only return is realized by the existing checked machine
consumer's semantics, preserving full output values and the original world
outside the activation frame. -/
theorem return_realize {sig : Clif.Signature} {args : List Clif.Val}
    (types : args.map (·.ty) = sig.params.map (·.ty))
    {vc : VCode} (checked : Backend.ABIReadOnly.check sig vc = true)
    {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {w : Arm.ArmState}
    (arguments : ArgsAtEntry F sig args w)
    {ρ : Nat → CV} {us : List (Reg × Reg)} {outs : List CV} {world : Arm.ArmState}
    (returned : VReturns vc (sem F ctx X) ρ w us outs world) :
    ∃ t, VReturns vc (valueSem F ctx X) ρ w us outs t ∧ SameWorld F t w := by
  obtain ⟨b,k,ρ1,w1,vb,ops,results,path,hb,hi,hops,values,run⟩ := returned
  have initial : Related F w (.run ⟨0,0,ρ,w⟩) (.run ⟨0,0,ρ,w⟩) :=
    ⟨w,rfl,rfl,SameWorld.refl F w,fun _ _ _ => rfl⟩
  obtain ⟨d,path',t,fixed,equal,worlds,entry⟩ := star_realize types checked arguments initial path
  have same : w1 = w := by
    have state := VConf.run.inj fixed
    exact (congrArg VState.w state).symm
  subst w1
  have unchanged := step_world (checked_instruction checked hb hi) run
  subst world
  obtain ⟨t',realized,related⟩ := step_realize types (checked_instruction checked hb hi)
    arguments worlds (entry _ rfl) run
  refine ⟨t',⟨b,k,ρ1,t,vb,ops,results,?_,hb,hi,hops,values,realized⟩,related⟩
  simpa only [equal,VConf.mapW] using path'

end E2E.ABIReadOnly
