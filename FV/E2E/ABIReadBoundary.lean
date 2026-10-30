import FV.E2E.StockArithmeticStage
import FV.E2E.LinkWorld
import FV.E2E.DeadCleanupRegLevelX
import FV.E2E.DeadCleanupGot
import FV.E2E.ABIReadFlagsSteps

/-! Reusable execution/ABI transport from instruction-level read-boundary proofs. -/
namespace E2E.ABIReadBoundary
open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup E2E.MixedFlagBoundary
set_option autoImplicit false
set_option Elab.async false

structure Model where
  instruction : Clif.Signature → Nat → Nat → MInst → Bool
  eval : (BitVec 64 → Prop) → FnCtx → ExtSem → Sem
  frame : ∀ {sig : Clif.Signature} {b k : Nat} {i : MInst}
    (checked : instruction sig b k i = true)
    {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem}
    {us outs : List CV} {w t : Arm.ArmState} {ctl : Ctl}
    (run : eval F ctx X i us w = some (outs,t,ctl)),
    FlagFrame w t ∧ (ctl = .next ∨ ctl = .ret)
  transport : ∀ {sig : Clif.Signature} {args : List Clif.Val}
    (types : args.map (·.ty) = sig.params.map (·.ty))
    {b k : Nat} {i : MInst}
    (checked : instruction sig b k i = true)
    {F Z : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem}
    {initial initial' w w' : Arm.ArmState}
    (current : FlagFrame initial w) (other : FlagFrame initial' w')
    (worlds : SameWorld Z w w')
    (registers : ∀ r v, (.reg r,v) ∈ (locsOf sig).zip args →
      regVal initial' r = regVal initial r)
    (stack : ∀ (off : Nat) (v : Clif.Val), (.stack off,v) ∈ (locsOf sig).zip args →
      ∀ j < v.ty.bytes,
      initial'.mem (Arm.r (.GPR 29#5) initial + BitVec.ofInt 64 (16+(off : Int)) + BitVec.ofNat 64 j) =
      initial.mem (Arm.r (.GPR 29#5) initial + BitVec.ofInt 64 (16+(off : Int)) + BitVec.ofNat 64 j))
    {us outs : List CV} {t : Arm.ArmState} {ctl : Ctl}
    (run : eval F ctx X i us w = some (outs,t,ctl)),
    ∃ t', eval F ctx X i us w' = some (outs,t',ctl) ∧ SameWorld Z t t'
  realize : ∀ {sig : Clif.Signature} {args : List Clif.Val}
    (types : args.map (·.ty) = sig.params.map (·.ty))
    {b k : Nat} {i : MInst}
    (checked : instruction sig b k i = true)
    {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem}
    {initial w t final : Arm.ArmState} (frame : FlagFrame initial w)
    (arguments : ArgsAtEntry F sig args initial) (worlds : SameWorld F t w)
    (entry : k = 0 → t = w) {us outs : List CV} {ctl : Ctl}
    (executed : eval F ctx X i us w = some (outs,final,ctl)),
    ∃ actual, valueSem F ctx X i us t = some (outs,actual,ctl) ∧ SameWorld F actual final

def Model.check (model : Model) (sig : Clif.Signature) (vc : VCode) : Bool :=
  vc.blocks.toList.zipIdx.all fun (block,b) =>
    block.insts.toList.zipIdx.all fun (i,k) => model.instruction sig b k i

variable {model : Model}

theorem checked_step_frame {sig : Clif.Signature} {b k : Nat} {i : MInst}
    (checked : model.instruction sig b k i = true)
    {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem}
    {us outs : List CV} {w t : Arm.ArmState} {ctl : Ctl}
    (run : model.eval F ctx X i us w = some (outs,t,ctl)) :
    FlagFrame w t ∧ (ctl = .next ∨ ctl = .ret) := by
  exact model.frame checked run

theorem checked_step_transport {sig : Clif.Signature} {args : List Clif.Val}
    (types : args.map (·.ty) = sig.params.map (·.ty))
    {b k : Nat} {i : MInst}
    (checked : model.instruction sig b k i = true)
    {F Z : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem}
    {initial initial' w w' : Arm.ArmState}
    (current : FlagFrame initial w) (other : FlagFrame initial' w')
    (worlds : SameWorld Z w w')
    (registers : ∀ r v, (.reg r,v) ∈ (locsOf sig).zip args →
      regVal initial' r = regVal initial r)
    (stack : ∀ (off : Nat) (v : Clif.Val), (.stack off,v) ∈ (locsOf sig).zip args →
      ∀ j < v.ty.bytes,
      initial'.mem (Arm.r (.GPR 29#5) initial + BitVec.ofInt 64 (16+(off : Int)) + BitVec.ofNat 64 j) =
      initial.mem (Arm.r (.GPR 29#5) initial + BitVec.ofInt 64 (16+(off : Int)) + BitVec.ofNat 64 j))
    {us outs : List CV} {t : Arm.ArmState} {ctl : Ctl}
    (run : model.eval F ctx X i us w = some (outs,t,ctl)) :
    ∃ t', model.eval F ctx X i us w' = some (outs,t',ctl) ∧ SameWorld Z t t' := by
  exact model.transport types checked current other worlds registers stack run

theorem checked_instruction {sig : Clif.Signature} {vc : VCode}
    (checked : model.check sig vc = true) {b k : Nat} {vb : VBlock} {i : MInst}
    (block : vc.blocks[b]? = some vb) (inst : vb.insts[k]? = some i) :
    model.instruction sig b k i = true := by
  have bm : (vb,b) ∈ vc.blocks.toList.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr (by simpa using block)
  have im : (i,k) ∈ vb.insts.toList.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr (by simpa using inst)
  exact List.all_eq_true.mp (List.all_eq_true.mp checked (vb,b) bm) (i,k) im

def Related (Z : BitVec 64 → Prop) (initial initial' : Arm.ArmState)
    (c d : VConf CV Arm.ArmState) : Prop :=
  ∃ w w', c.mapW (fun _ => w) = c ∧ d = c.mapW (fun _ => w') ∧
    FlagFrame initial w ∧ FlagFrame initial' w' ∧ SameWorld Z w w'

/-- Whole checked executions transfer one proof-internal virtual file; no
second file, final flags or execution callback is assumed. -/
theorem star_transport {sig : Clif.Signature} {args : List Clif.Val}
    (types : args.map (·.ty) = sig.params.map (·.ty))
    {vc : VCode} (checked : model.check sig vc = true)
    {F Z : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem}
    {initial initial' : Arm.ArmState}
    (registers : ∀ r v, (.reg r,v) ∈ (locsOf sig).zip args →
      regVal initial' r = regVal initial r)
    (stack : ∀ (off : Nat) (v : Clif.Val), (.stack off,v) ∈ (locsOf sig).zip args →
      ∀ j < v.ty.bytes,
      initial'.mem (Arm.r (.GPR 29#5) initial + BitVec.ofInt 64 (16+(off : Int)) + BitVec.ofNat 64 j) =
      initial.mem (Arm.r (.GPR 29#5) initial + BitVec.ofInt 64 (16+(off : Int)) + BitVec.ofNat 64 j))
    {c c' d : VConf CV Arm.ArmState} (related : Related Z initial initial' c d)
    (path : Star (VStep vc (model.eval F ctx X)) c c') :
    ∃ d', Star (VStep vc (model.eval F ctx X)) d d' ∧ Related Z initial initial' c' d' := by
  induction path generalizing d with
  | refl => exact ⟨d,.refl _,related⟩
  | @step c next final first rest ih =>
    obtain ⟨w,w',fixed,rfl,current,other,worlds⟩ := related
    cases first with
    | @step b k ρ w0 vb i ops outs t ctl target hb hi hops run arity successor =>
      have eq : w0 = w := by
        have state := VConf.run.inj fixed
        exact (congrArg VState.w state).symm
      subst w0
      have supported := checked_instruction checked hb hi
      obtain ⟨t',executed,postWorlds⟩ := checked_step_transport types supported
        current other worlds registers stack run
      have post := (checked_step_frame supported run).1
      have post' := (checked_step_frame supported executed).1
      have mapped := VStep.step hb hi hops executed arity
        (vnext_map vc (fun _ => t') successor)
      have relation : Related Z initial initial' next (next.mapW (fun _ => t')) := by
        refine ⟨t,t',?_,rfl,current.trans post,other.trans post',postWorlds⟩
        cases successor <;> rfl
      obtain ⟨d',tail,final⟩ := ih relation
      exact ⟨d',.step mapped tail,final⟩


/-- Transfer the complete returned ABI values with one initial virtual file.
Final flags are related outputs, never a caller-provided or unchanged-world premise. -/
theorem return_transport {sig : Clif.Signature} {args : List Clif.Val}
    (types : args.map (·.ty) = sig.params.map (·.ty))
    {vc : VCode} (checked : model.check sig vc = true)
    {F Z : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem}
    {initial initial' : Arm.ArmState} (worlds : SameWorld Z initial initial')
    (registers : ∀ r v, (.reg r,v) ∈ (locsOf sig).zip args →
      regVal initial' r = regVal initial r)
    (stack : ∀ (off : Nat) (v : Clif.Val), (.stack off,v) ∈ (locsOf sig).zip args →
      ∀ j < v.ty.bytes,
      initial'.mem (Arm.r (.GPR 29#5) initial + BitVec.ofInt 64 (16+(off : Int)) + BitVec.ofNat 64 j) =
      initial.mem (Arm.r (.GPR 29#5) initial + BitVec.ofInt 64 (16+(off : Int)) + BitVec.ofNat 64 j))
    {ρ : Nat → CV} {us : List (Reg × Reg)} {outs : List CV} {world : Arm.ArmState}
    (returned : VReturns vc (model.eval F ctx X) ρ initial us outs world) :
    ∃ world', VReturns vc (model.eval F ctx X) ρ initial' us outs world' ∧ SameWorld Z world world' := by
  obtain ⟨b,k,ρ1,w1,vb,ops,results,path,hb,hi,hops,values,run⟩ := returned
  have initialRelation : Related Z initial initial'
      (.run ⟨0,0,ρ,initial⟩) (.run ⟨0,0,ρ,initial'⟩) :=
    ⟨initial,initial',rfl,rfl,FlagFrame.refl _,FlagFrame.refl _,worlds⟩
  obtain ⟨d,path',w,w',fixed,equal,current,other,related⟩ :=
    star_transport types checked registers stack initialRelation path
  have same : w1 = w := by
    have state := VConf.run.inj fixed
    exact (congrArg VState.w state).symm
  subst w1
  obtain ⟨world',executed,finalWorlds⟩ := checked_step_transport types
    (checked_instruction checked hb hi) current other related registers stack run
  exact ⟨world',⟨b,k,ρ1,w',vb,ops,results,
    by simpa only [equal,VConf.mapW] using path',hb,hi,hops,values,executed⟩,finalWorlds⟩



namespace Realize
theorem step_realize {sig : Clif.Signature} {args : List Clif.Val}
    (types : args.map (·.ty) = sig.params.map (·.ty))
    {b k : Nat} {i : MInst}
    (checked : model.instruction sig b k i = true)
    {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem}
    {initial w t final : Arm.ArmState} (frame : FlagFrame initial w)
    (arguments : ArgsAtEntry F sig args initial) (worlds : SameWorld F t w)
    (entry : k = 0 → t = w) {us outs : List CV} {ctl : Ctl}
    (executed : model.eval F ctx X i us w = some (outs,final,ctl)) :
    ∃ actual, valueSem F ctx X i us t = some (outs,actual,ctl) ∧ SameWorld F actual final := by
  exact model.realize types checked frame arguments worlds entry executed

def Related (F : BitVec 64 → Prop) (initial : Arm.ArmState)
    (c d : VConf CV Arm.ArmState) : Prop :=
  ∃ w t, c.mapW (fun _ => w) = c ∧ d = c.mapW (fun _ => t) ∧
    FlagFrame initial w ∧ SameWorld F t w ∧
    ∀ vs, c = .run vs → vs.k = 0 → t = w

private theorem realize_step {sig : Clif.Signature} {args : List Clif.Val}
    (types : args.map (·.ty) = sig.params.map (·.ty))
    {vc : VCode} (checked : model.check sig vc = true)
    {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {initial : Arm.ArmState}
    (arguments : ArgsAtEntry F sig args initial)
    {c c' d : VConf CV Arm.ArmState} (related : Related F initial c d)
    (step : VStep vc (model.eval F ctx X) c c') :
    ∃ d', VStep vc (valueSem F ctx X) d d' ∧ Related F initial c' d' := by
  obtain ⟨w,t,fixed,rfl,frame,worlds,entry⟩ := related
  cases step with
  | @step b k ρ w0 vb i ops outs w1 ctl target hb hi hops run arity successor =>
    have eq : w0 = w := by
      have state := VConf.run.inj fixed
      exact (congrArg VState.w state).symm
    subst w0
    have supported := checked_instruction checked hb hi
    obtain ⟨t',realized,related'⟩ := step_realize types supported frame arguments worlds (entry _ rfl) run
    have preserved := (checked_step_frame supported run).1
    refine ⟨c'.mapW (fun _ => t'),
      VStep.step hb hi hops realized arity (vnext_map vc (fun _ => t') successor),?_⟩
    have control := (checked_step_frame supported run).2
    cases successor with
    | next hk =>
      refine ⟨w1,t',rfl,rfl,frame.trans preserved,related',?_⟩
      intro vs eq zero
      cases eq
      change k+1=0 at zero
      omega
    | goto => rcases control with control | control <;> cases control
    | ret => exact ⟨w1,t',rfl,rfl,frame.trans preserved,related',fun vs eq => by cases eq⟩
    | halt => rcases control with control | control <;> cases control

theorem star_realize {sig : Clif.Signature} {args : List Clif.Val}
    (types : args.map (·.ty) = sig.params.map (·.ty))
    {vc : VCode} (checked : model.check sig vc = true)
    {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {initial : Arm.ArmState}
    (arguments : ArgsAtEntry F sig args initial)
    {c c' d : VConf CV Arm.ArmState} (related : Related F initial c d)
    (path : Star (VStep vc (model.eval F ctx X)) c c') :
    ∃ d', Star (VStep vc (valueSem F ctx X)) d d' ∧ Related F initial c' d' := by
  induction path generalizing d with
  | refl => exact ⟨d,.refl _,related⟩
  | step first rest ih =>
    obtain ⟨d1,first',related'⟩ := realize_step types checked arguments related first
    obtain ⟨d',tail,final⟩ := ih related'
    exact ⟨d',.step first' tail,final⟩

/-- Complete realization preserves exact virtual definitions/ABI pins and the
actual final flags, without requiring the final source world to equal entry. -/
theorem return_realize {sig : Clif.Signature} {args : List Clif.Val}
    (types : args.map (·.ty) = sig.params.map (·.ty))
    {vc : VCode} (checked : model.check sig vc = true)
    {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {initial : Arm.ArmState}
    (arguments : ArgsAtEntry F sig args initial)
    {ρ : Nat → CV} {us : List (Reg × Reg)} {outs : List CV} {world : Arm.ArmState}
    (returned : VReturns vc (model.eval F ctx X) ρ initial us outs world) :
    ∃ t, VReturns vc (valueSem F ctx X) ρ initial us outs t ∧ SameWorld F t world := by
  obtain ⟨b,k,ρ1,w1,vb,ops,results,path,hb,hi,hops,values,run⟩ := returned
  have start : Related F initial (.run ⟨0,0,ρ,initial⟩) (.run ⟨0,0,ρ,initial⟩) :=
    ⟨initial,initial,rfl,rfl,FlagFrame.refl _,SameWorld.refl _ _,fun _ _ _ => rfl⟩
  obtain ⟨d,path',w,t,fixed,equal,frame,worlds,entry⟩ := star_realize types checked arguments start path
  have same : w1 = w := by
    have state := VConf.run.inj fixed
    exact (congrArg VState.w state).symm
  subst w1
  obtain ⟨t',realized,related⟩ := step_realize types (checked_instruction checked hb hi)
    frame arguments worlds (entry _ rfl) run
  exact ⟨t',⟨b,k,ρ1,t,vb,ops,results,
    by simpa only [equal,VConf.mapW] using path',hb,hi,hops,values,realized⟩,related⟩
end Realize

theorem machine_return {f : Clif.Function} {args : List Clif.Val}
    (types : args.map (·.ty) = f.sig.params.map (·.ty))
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin} {k : Nat}
    {cleanup : Bool} (readOnly : model.check f.sig vc = true)
    (prep : prepCheck (Stock.Arithmetic.stage cleanup vc) vcp = true)
    (check : checkAlloc vcp rf = .ok ()) (alloc : lowerRFunc vcp rf = .ok af)
    (emit : emitFunc k af = .ok fa) (layout : fa.layout = .ok fb)
    {X : ExtSem} {K : Nat} {F Z : BitVec 64 → Prop}
    (frame : ∀ a, F a → Z a) (covered : FormsCovered ⟨fa.k,af.slotBase⟩ vcp)
    {w final reference : Arm.ArmState} (arguments : ArgsAtEntry F f.sig args w)
    (worlds : SameWorld Z final reference)
    {ρ : Nat → CV} {us : List (Reg × Reg)} {outs : List CV}
    (returned : VReturns vc (model.eval F ⟨fa.k,af.slotBase⟩ X) ρ w us outs final)
    (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState)
    (entry : ActEntry vcp rf af fa fb K F G X H base ra s w) :
    ∃ n, ActRet ra Z G us outs reference s (runX (ArmStepX X H fa) n s) ∧
      PostTrace fa af base (ArmStepX X H fa) s n ∧
      ∀ i < n, actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
        (runX (ArmStepX X H fa) i s) := by
  obtain ⟨t,valueRun,related⟩ := Realize.return_realize types readOnly arguments returned
  have finalWorld := (SameWorld.mono frame related).trans worlds
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


end E2E.ABIReadBoundary
