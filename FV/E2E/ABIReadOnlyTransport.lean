import FV.E2E.Lockstep
import FV.E2E.ABIReadOnlySem
import FV.E2E.ABIReadOnlyCheck
import FV.E2E.Pair

namespace E2E.ABIReadOnly
open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup
set_option autoImplicit false
set_option Elab.async false

/-- The full VCode check supplies an indexed instruction fact. -/
theorem checked_instruction {sig : Clif.Signature} {vc : VCode}
    (checked : Backend.ABIReadOnly.check sig vc = true) {b k : Nat} {vb : VBlock} {i : MInst}
    (block : vc.blocks[b]? = some vb) (inst : vb.insts[k]? = some i) :
    Backend.ABIReadOnly.instruction sig b k i = true := by
  have bm : (vb,b) ∈ vc.blocks.toList.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr (by simpa using block)
  have im : (i,k) ∈ vb.insts.toList.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr (by simpa using inst)
  exact List.all_eq_true.mp (List.all_eq_true.mp checked (vb,b) bm) (i,k) im

private theorem pure_sem {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {i : MInst}
    (pure : pureForm i = true) (us : List CV) (w : Arm.ArmState) :
    sem F ctx X i us w = mspec ctx.slotBase i us w := by
  cases i <;> simp only [sem,valueSem,specForm_of_pure pure,↓reduceIte]

/-- Every checked instruction leaves the abstract world unchanged. -/
theorem step_world {sig : Clif.Signature} {b k : Nat} {i : MInst}
    (checked : Backend.ABIReadOnly.instruction sig b k i = true)
    {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {us outs : List CV}
    {w w' : Arm.ArmState} {ctl : Ctl}
    (executed : sem F ctx X i us w = some (outs,w',ctl)) : w' = w := by
  rcases instruction_cases checked with pure | ⟨pairs,rfl,_⟩ | ⟨op,key,off,fl,rfl,hop,_⟩ | ⟨pairs,rfl⟩
  · rw [pure_sem pure] at executed
    exact (mspec_pure pure executed).1
  · simp only [sem,valueSem,specForm, pureForm, cmpForm, Bool.false_or,csem,Bool.false_eq_true,↓reduceIte,Option.some.injEq,Prod.mk.injEq] at executed
    exact executed.2.1.symm
  · simp only [sem,mspec,hop,ite_false,Option.map_eq_some_iff,Prod.mk.injEq] at executed
    obtain ⟨a,_,_,world,_⟩ := executed
    exact world.symm
  · simp only [sem,valueSem,specForm, pureForm, cmpForm, Bool.false_or,csem,Bool.false_eq_true,↓reduceIte,Option.some.injEq,Prod.mk.injEq] at executed
    exact executed.2.1.symm

/-- One read-only step transfers the exact outputs and control between worlds
with the original ABI argument-register and stack-byte agreement. -/
theorem step_transport {sig : Clif.Signature} {args : List Clif.Val}
    (types : args.map (·.ty) = sig.params.map (·.ty))
    {b k : Nat} {i : MInst} (checked : Backend.ABIReadOnly.instruction sig b k i = true)
    {F Z : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {w w' : Arm.ArmState}
    (worlds : SameWorld Z w w')
    (registers : ∀ r v, (.reg r,v) ∈ (locsOf sig).zip args → regVal w' r = regVal w r)
    (stack : ∀ (off : Nat) (v : Clif.Val), (.stack off,v) ∈ (locsOf sig).zip args → ∀ j < v.ty.bytes,
      w'.mem (Arm.r (.GPR 29#5) w + BitVec.ofInt 64 (16+(off : Int)) + BitVec.ofNat 64 j) =
      w.mem (Arm.r (.GPR 29#5) w + BitVec.ofInt 64 (16+(off : Int)) + BitVec.ofNat 64 j))
    {us outs : List CV} {ctl : Ctl}
    (executed : sem F ctx X i us w = some (outs,w,ctl)) :
    sem F ctx X i us w' = some (outs,w',ctl) := by
  rcases instruction_cases checked with pure | ⟨pairs,rfl,_,_,reads⟩ |
      ⟨op,key,off,fl,rfl,hop,read⟩ | ⟨pairs,rfl⟩
  · rw [pure_sem pure] at executed ⊢
    have noMem : i.isMemAcc = false := by cases i <;> simp_all [pureForm,MInst.isMemAcc]
    obtain ⟨next,run,_⟩ := mspec_lockstep noMem worlds executed
    have same : next = w' := (mspec_pure pure run).1
    rwa [same] at run
  · have same : pairs.map (fun p => regVal w' p.2) = pairs.map (fun p => regVal w p.2) := by
      apply List.map_congr_left
      intro pair member
      obtain ⟨v,found⟩ := registerRead_argument types (List.all_eq_true.mp reads pair member)
      exact registers pair.2 v found
    simp [sem,valueSem,specForm, pureForm, cmpForm, Bool.false_or,csem,same] at executed ⊢
    exact executed
  · obtain ⟨slot,v,member,offset,width⟩ := stackRead_argument types read
    have fp : Arm.r (.GPR 29#5) w' = Arm.r (.GPR 29#5) w :=
      (worlds.1 (.GPR 29#5) (by simp [Masked])).symm
    have data : loadVal op (Arm.r (.GPR 29#5) w + BitVec.ofInt 64 off) w' =
        loadVal op (Arm.r (.GPR 29#5) w + BitVec.ofInt 64 off) w := by
      have bytes := read_mem_bytes_congr (s := w') (t := w) op.bytes
        (Arm.r (.GPR 29#5) w + BitVec.ofInt 64 off)
        (fun j hj => by rw [offset]; exact stack slot v member j (by omega))
      simp only [loadVal,bytes]
    cases us with
    | nil =>
      simp [sem,mspec,hop,amodeAddr,fp,data] at executed ⊢
      exact executed
    | cons a us => simp [sem,mspec,hop,amodeAddr] at executed
  · simp [sem,valueSem,specForm, pureForm, cmpForm, Bool.false_or,csem] at executed ⊢
    exact executed

private def worldOf : VConf CV Arm.ArmState → Arm.ArmState
  | .run s => s.w
  | .ret _ w => w
  | .halt w => w

/-- Whole checked executions retain the initial world and transfer with the
same virtual values. The proof never selects a second initial register file. -/
theorem star_transport {sig : Clif.Signature} {args : List Clif.Val}
    (types : args.map (·.ty) = sig.params.map (·.ty))
    {vc : VCode} (checked : Backend.ABIReadOnly.check sig vc = true)
    {F Z : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {w w' : Arm.ArmState}
    (worlds : SameWorld Z w w')
    (registers : ∀ r v, (.reg r,v) ∈ (locsOf sig).zip args → regVal w' r = regVal w r)
    (stack : ∀ (off : Nat) (v : Clif.Val), (.stack off,v) ∈ (locsOf sig).zip args → ∀ j < v.ty.bytes,
      w'.mem (Arm.r (.GPR 29#5) w + BitVec.ofInt 64 (16+(off : Int)) + BitVec.ofNat 64 j) =
      w.mem (Arm.r (.GPR 29#5) w + BitVec.ofInt 64 (16+(off : Int)) + BitVec.ofNat 64 j))
    {c c' : VConf CV Arm.ArmState}
    (path : Star (VStep vc (sem F ctx X)) c c') (initial : worldOf c = w) :
    Star (VStep vc (sem F ctx X)) (c.mapW (fun _ => w')) (c'.mapW (fun _ => w')) ∧
      worldOf c' = w := by
  induction path with
  | refl => exact ⟨.refl _,initial⟩
  | @step c next final first rest ih =>
    cases first with
    | @step b k ρ w0 vb i ops outs w1 ctl target hb hi hops run arity successor =>
      change w0 = w at initial
      subst w0
      have supported := checked_instruction checked hb hi
      have fixed := step_world supported run
      subst w1
      have other := step_transport types supported worlds registers stack run
      have mapped := VStep.step hb hi hops other arity
        (vnext_map vc (fun _ => w') successor)
      have nextWorld : worldOf next = w := by cases successor <;> rfl
      obtain ⟨tail,finalWorld⟩ := ih nextWorld
      exact ⟨.step mapped tail,finalWorld⟩

/-- Returned executions transfer the same ABI pins and full output values,
including all high bits, from the one internally chosen initial virtual file. -/
theorem return_transport {sig : Clif.Signature} {args : List Clif.Val}
    (types : args.map (·.ty) = sig.params.map (·.ty))
    {vc : VCode} (checked : Backend.ABIReadOnly.check sig vc = true)
    {F Z : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {w w' : Arm.ArmState}
    (worlds : SameWorld Z w w')
    (registers : ∀ r v, (.reg r,v) ∈ (locsOf sig).zip args → regVal w' r = regVal w r)
    (stack : ∀ (off : Nat) (v : Clif.Val), (.stack off,v) ∈ (locsOf sig).zip args → ∀ j < v.ty.bytes,
      w'.mem (Arm.r (.GPR 29#5) w + BitVec.ofInt 64 (16+(off : Int)) + BitVec.ofNat 64 j) =
      w.mem (Arm.r (.GPR 29#5) w + BitVec.ofInt 64 (16+(off : Int)) + BitVec.ofNat 64 j))
    {ρ : Nat → CV} {us : List (Reg × Reg)} {outs : List CV} {world : Arm.ArmState}
    (returned : VReturns vc (sem F ctx X) ρ w us outs world) :
    world = w ∧ VReturns vc (sem F ctx X) ρ w' us outs w' := by
  obtain ⟨b,k,ρ1,w1,vb,ops,results,path,hb,hi,hops,values,run⟩ := returned
  obtain ⟨other,same⟩ := star_transport types checked worlds registers stack path rfl
  change w1 = w at same
  subst w1
  have fixed := step_world (checked_instruction checked hb hi) run
  subst world
  exact ⟨rfl,⟨b,k,ρ1,w',vb,ops,results,other,hb,hi,hops,values,
    step_transport types (checked_instruction checked hb hi) worlds registers stack run⟩⟩

end E2E.ABIReadOnly
