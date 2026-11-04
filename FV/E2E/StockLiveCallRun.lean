import FV.E2E.StockLiveCallReady
import FV.E2E.StockLiveCallTail
import FV.E2E.StockResultCallPair
import FV.Backend.Proof.DeadCleanupAdapter

namespace Backend.Stock.LiveCall
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof E2E Backend.DeadCleanup
set_option autoImplicit false
set_option Elab.async false

variable {f : Clif.Function} {result : Stock.Result} {env : Clif.Env} {fr : Clif.Frame}
  {cm outMem : Clif.Mem} {Γ : Rel} {fc : FnCtx} {X : ExtSem} {initial : Arm.ArmState}

def Ready.sumValue (source : Ready f result env fr cm outMem Γ fc X initial) (output : CV) : CV :=
  resX .size64 (opnd .size64 output + opnd .size64 (source.values source.live))

theorem Ready.sum_holds (source : Ready f result env fr cm outMem Γ fc X initial) {output : CV}
    (returned : VHolds ⟨.i64,source.returnedWord⟩ output) :
    VHolds ⟨.i64,source.returnedWord+source.liveWord⟩ (source.sumValue output) :=
  LiveCallArithmetic.sum_holds returned source.liveHeld

/-- Both semantic worlds use the same proved call/add/return kernel. -/
theorem Ready.virtual_return (source : Ready f result env fr cm outMem Γ fc X initial)
    {start before after : Arm.ArmState} {output : CV}
    (preRun : seqRun (valueSem Γ.F fc X) source.prelude source.seed start = some (.fall source.values before))
    (called : X.call (some source.ext.name) [source.values source.live] before = some ([output],after)) :
    ∃ final,VReturns result.code (valueSem Γ.F fc X) source.seed start
      (retPairs [(source.sum,.x 0)]) [source.sumValue output] final ∧ SameWorld Γ.F final after := by
  apply execute_tail (refines_valueSem Γ.F fc X) (fun _ _ _ => rfl)
    source.placed source.separate source.code preRun
  change (X.call (some source.ext.name) [source.values source.live] before).map
    (fun pair => (pair.1,pair.2,Ctl.next)) = _
  rw [called]
  rfl

/-- The actual call keeps arbitrary returned memory; the arithmetic uses the preserved parameter. -/
theorem Ready.execute (source : Ready f result env fr cm outMem Γ fc X initial)
    {args : List Clif.Val} (types : args.map (·.ty) = f.sig.params.map (·.ty))
    (arguments : ArgsAtEntry Γ.F f.sig args initial) {c : BitVec 64}
    (memory : RelW Γ f c fr.slots cm initial)
    (calls : XCallsOk env (f.externs.map (·.2)) (RelW Γ f c) X) :
    ∃ before output after final,
      seqRun (valueSem Γ.F fc X) source.prelude source.seed initial = some (.fall source.values before) ∧
      SameWorld Γ.F before initial ∧ RelW Γ f c fr.slots cm before ∧
      X.call (some source.ext.name) [source.values source.live] before = some ([output],after) ∧
      VHolds ⟨.i64,source.returnedWord⟩ output ∧ RelW Γ f c fr.slots source.after after ∧
      SameWorld Γ.F final after ∧ VReturns result.code (valueSem Γ.F fc X) source.seed initial
        (retPairs [(source.sum,.x 0)]) [source.sumValue output] final := by
  obtain ⟨_,before,preRun,related⟩ := ABIReadOnly.seqRun_fall_realize types arguments (SameWorld.refl Γ.F initial)
    (b := 0) (start := 0) (by simpa only [Nat.zero_add] using source.reads) (fun _ => rfl) source.preRun
  have beforeMemory := mrStable_relW Γ f c fr.slots cm initial before (SameWorld.nf related) memory
  obtain ⟨actual,after,called,arity,held,mem⟩ := calls source.ext source.member source.callee fr.slots cm before
    (some source.ext.name) [source.values source.live] [source.values source.live]
    [⟨.i64,source.liveWord⟩] [⟨.i64,source.returnedWord⟩] source.after source.found (Or.inl ⟨rfl,rfl⟩)
    (source.arguments before) beforeMemory source.sourceReturned (by rw [source.returns]; rfl)
  rw [source.returns] at arity
  cases actual with
  | nil => cases arity
  | cons output tail =>
    have empty : tail = [] := by simpa using arity
    subst tail
    obtain ⟨final,returns,same⟩ := source.virtual_return preRun called
    exact ⟨before,output,after,final,preRun,related,beforeMemory,called,
      held.2 0 _ _ rfl rfl,mem,same,returns⟩

/-- Original XNI pairs the callee effects and preserves the actual post-call arithmetic result. -/
theorem Ready.execute_other (source : Ready f result env fr cm outMem Γ fc X initial)
    {args : List Clif.Val} (types : args.map (·.ty) = f.sig.params.map (·.ty))
    (arguments : ArgsAtEntry Γ.F f.sig args initial) {c : BitVec 64}
    {before after reference : Arm.ArmState} {output : CV}
    (related : SameWorld Γ.F before initial) (memory : RelW Γ f c fr.slots cm before)
    (called : X.call (some source.ext.name) [source.values source.live] before = some ([output],after))
    (referenceWorld : SameWorld Γ.F reference after)
    (calls : XCallsOk env (f.externs.map (·.2)) (RelW Γ f c) X)
    (ni : XNI Γ.F Γ.syms (f.externs.map (·.2)) (indSigs f) c
      (CallLg env (f.externs.map (·.2)) (indSigs f)) X)
    {Z : BitVec 64 → Prop} (covers : ∀ a,Γ.F a → Z a) {other : Arm.ArmState}
    (otherMemory : RelW Γ f c fr.slots cm other) (worlds : SameWorld Z initial other)
    (registers : ∀ r val,(.reg r,val) ∈ (locsOf f.sig).zip args → regVal other r = regVal initial r)
    (stack : ∀ (off : Nat) (val : Clif.Val),(.stack off,val) ∈ (locsOf f.sig).zip args → ∀ j < val.ty.bytes,
      other.mem (Arm.r (.GPR 29#5) initial + BitVec.ofInt 64 (16+(off : Int)) + BitVec.ofNat 64 j) =
      initial.mem (Arm.r (.GPR 29#5) initial + BitVec.ofInt 64 (16+(off : Int)) + BitVec.ofNat 64 j)) :
    ∃ final,SameWorld Z final reference ∧ RelW Γ f c fr.slots source.after final ∧
      VReturns result.code (valueSem Γ.F fc X) source.seed other
        (retPairs [(source.sum,.x 0)]) [source.sumValue output] final := by
  have otherArguments := ABIReadOnly.arguments_transport arguments worlds registers stack
  have transferred := (ABIReadOnly.seqRun_fall_transport types worlds registers stack
    (b := 0) (start := 0) (by simpa only [Nat.zero_add] using source.reads) source.preRun).2
  obtain ⟨_,otherBefore,otherRun,otherRelated⟩ := ABIReadOnly.seqRun_fall_realize types otherArguments
    (SameWorld.refl Γ.F other) (b := 0) (start := 0)
    (by simpa only [Nat.zero_add] using source.reads) (fun _ => rfl) transferred
  have beforeMemory := mrStable_relW Γ f c fr.slots cm other otherBefore (SameWorld.nf otherRelated) otherMemory
  have beforeWorlds : SameWorld Z before otherBefore :=
    (SameWorld.mono covers related).trans (worlds.trans (SameWorld.mono covers otherRelated).symm)
  obtain ⟨paired,firstOut,otherOut,firstCall,otherCall,held,firstMemory,finalMemory,finalWorlds⟩ :=
    result_call_pair calls ni source.member source.returns source.found source.sourceReturned memory beforeMemory
      (source.arguments before) (source.arguments otherBefore) covers beforeWorlds
  have equal := Prod.mk.inj (Option.some.inj (firstCall.symm.trans called))
  have sameOutput : paired = output := List.cons.inj equal.1 |>.1
  have sameWorld : firstOut = after := equal.2
  subst paired
  subst firstOut
  obtain ⟨final,returns,remainingWorld⟩ := source.virtual_return otherRun otherCall
  have finalRelated := mrStable_relW Γ f c fr.slots source.after otherOut final
    remainingWorld.nf finalMemory
  have same : SameWorld Z final reference :=
    (SameWorld.mono covers remainingWorld).trans
      (finalWorlds.symm.trans (SameWorld.mono covers referenceWorld).symm)
  exact ⟨final,same,finalRelated,returns⟩

end Backend.Stock.LiveCall
