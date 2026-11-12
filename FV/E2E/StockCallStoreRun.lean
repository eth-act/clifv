import FV.Backend.Proof.StockCallStoreAddress
import FV.E2E.StockCallStoreReady
import FV.E2E.StockCallStoreTail
import FV.E2E.StockResultCallPair
import FV.Backend.Proof.DeadCleanupAdapter

namespace Backend.Stock.CallStore
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof E2E Backend.DeadCleanup
set_option autoImplicit false
set_option Elab.async false

variable {f : Clif.Function} {result : Stock.Result} {env : Clif.Env} {fr : Clif.Frame}
  {cm outMem : Clif.Mem} {Γ : Rel} {fc : FnCtx} {X : ExtSem} {initial : Arm.ArmState}

def Ready.writeWorld (source : Ready f result env fr cm outMem Γ fc X initial)
    (output : CV) (after : Arm.ArmState) : Arm.ArmState :=
  Arm.write_mem_bytes 8 (BitVec.ofNat 64 (Clif.effAddr source.pointerValue 8))
    ((lo64 output).setWidth 64) after

/-- The same store kernel handles both semantic worlds and the actual post-call memory. -/
theorem Ready.virtual_return (source : Ready f result env fr cm outMem Γ fc X initial)
    {start before after : Arm.ArmState} {output : CV} {c : BitVec 64}
    (slot : fc.slotBase = Γ.slotOff)
    (symbols : ∀ n b,Γ.syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (preRun : seqRun (valueSem Γ.F fc X) source.prelude source.seed start = some (.fall source.values before))
    (called : X.call (some source.ext.name) [source.values source.argument] before = some ([output],after))
    (held : VHolds ⟨.i64,source.returnedWord⟩ output)
    (memory : RelW Γ f c fr.slots source.after after) :
    ∃ final,VReturns result.code (valueSem Γ.F fc X) source.seed start
      (retPairs [(source.called,.x 0)]) [output] final ∧
      SameWorld Γ.F final (source.writeWorld output after) ∧
      RelW Γ f c fr.slots source.stored final := by
  have calledStep : valueSem Γ.F fc X
      (.call ⟨.sym source.ext.name,retPairs [(source.argument,.x 0)],callDefs [(.x 0,source.called)]⟩)
      ([(source.argument,Reg.x 0)].map (source.values ·.1)) before = some ([output],after,.next) := by
    change (X.call (some source.ext.name) [source.values source.argument] before).map
      (fun pair => (pair.1.take 1,pair.2,Ctl.next)) = _
    rw [called]
    rfl
  have memorySem := memRefines_valueSem Γ.F fc X slot symbols
  obtain ⟨pv,final,found,returned,world,mem⟩ := execute_tail
    (mrStable_relW Γ f c) (Stock.Memory.store_refines_of_mem memorySem) (memRelOk_relW Γ f c)
    (fun _ _ _ => rfl) source.placed source.separate source.code preRun calledStep
    (by rwa [source.storeSlots]) source.little
    (by intro bits read; have same := Clif.Res.ok.inj (source.valueRead.symm.trans read); subst bits; exact held)
    (by intro pointer found; have same := Option.some.inj (found.symm.trans source.pointerRead)
        subst pointer; exact CallStoreResult.pointer_address source.pointerHeld source.pointerType after)
    source.sourceStore
  have same := Option.some.inj (found.symm.trans source.pointerRead)
  subst pv
  exact ⟨final,returned,world,by rwa [source.storeSlots] at mem⟩

/-- The actual call keeps arbitrary returned memory; the arithmetic uses the preserved parameter. -/
theorem Ready.execute (source : Ready f result env fr cm outMem Γ fc X initial)
    {args : List Clif.Val} (types : args.map (·.ty) = f.sig.params.map (·.ty))
    (arguments : ArgsAtEntry Γ.F f.sig args initial) {c : BitVec 64}
    (memory : RelW Γ f c fr.slots cm initial)
    (slot : fc.slotBase = Γ.slotOff)
    (symbols : ∀ n b,Γ.syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (calls : XCallsOk env (f.externs.map (·.2)) (RelW Γ f c) X) :
    ∃ before output after final,
      seqRun (valueSem Γ.F fc X) source.prelude source.seed initial = some (.fall source.values before) ∧
      SameWorld Γ.F before initial ∧ RelW Γ f c fr.slots cm before ∧
      X.call (some source.ext.name) [source.values source.argument] before = some ([output],after) ∧
      VHolds ⟨.i64,source.returnedWord⟩ output ∧ RelW Γ f c fr.slots source.after after ∧
      SameWorld Γ.F final (source.writeWorld output after) ∧
      RelW Γ f c fr.slots source.stored final ∧ VReturns result.code (valueSem Γ.F fc X) source.seed initial
        (retPairs [(source.called,.x 0)]) [output] final := by
  obtain ⟨_,before,preRun,related⟩ := ABIReadOnly.seqRun_fall_realize types arguments (SameWorld.refl Γ.F initial)
    (b := 0) (start := 0) (by simpa only [Nat.zero_add] using source.reads) (fun _ => rfl) source.preRun
  have beforeMemory := mrStable_relW Γ f c fr.slots cm initial before (SameWorld.nf related) memory
  obtain ⟨actual,after,called,arity,held,mem⟩ := calls source.ext source.member source.callee fr.slots cm before
    (some source.ext.name) [source.values source.argument] [source.values source.argument]
    [⟨.i64,source.liveWord⟩] [⟨.i64,source.returnedWord⟩] source.after source.found (Or.inl ⟨rfl,rfl⟩)
    (source.arguments before) beforeMemory source.sourceReturned (by rw [source.returns]; rfl)
  rw [source.returns] at arity
  cases actual with
  | nil => cases arity
  | cons output tail =>
    have empty : tail = [] := by simpa using arity
    subst tail
    obtain ⟨final,returns,same,stored⟩ := source.virtual_return slot symbols preRun called
      (held.2 0 _ _ rfl rfl) mem
    exact ⟨before,output,after,final,preRun,related,beforeMemory,called,
      held.2 0 _ _ rfl rfl,mem,same,stored,returns⟩

/-- Original XNI pairs the callee effects and preserves the actual post-call arithmetic result. -/
theorem Ready.execute_other (source : Ready f result env fr cm outMem Γ fc X initial)
    {args : List Clif.Val} (types : args.map (·.ty) = f.sig.params.map (·.ty))
    (arguments : ArgsAtEntry Γ.F f.sig args initial) {c : BitVec 64}
    {before after reference : Arm.ArmState} {output : CV}
    (related : SameWorld Γ.F before initial) (memory : RelW Γ f c fr.slots cm before)
    (called : X.call (some source.ext.name) [source.values source.argument] before = some ([output],after))
    (referenceWorld : SameWorld Γ.F reference (source.writeWorld output after))
    (slot : fc.slotBase = Γ.slotOff)
    (symbols : ∀ n b,Γ.syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (calls : XCallsOk env (f.externs.map (·.2)) (RelW Γ f c) X)
    (ni : XNI Γ.F Γ.syms (f.externs.map (·.2)) (indSigs f) c
      (CallLg env (f.externs.map (·.2)) (indSigs f)) X)
    {Z : BitVec 64 → Prop} (covers : ∀ a,Γ.F a → Z a) {other : Arm.ArmState}
    (otherMemory : RelW Γ f c fr.slots cm other) (worlds : SameWorld Z initial other)
    (registers : ∀ r val,(.reg r,val) ∈ (locsOf f.sig).zip args → regVal other r = regVal initial r)
    (stack : ∀ (off : Nat) (val : Clif.Val),(.stack off,val) ∈ (locsOf f.sig).zip args → ∀ j < val.ty.bytes,
      other.mem (Arm.r (.GPR 29#5) initial + BitVec.ofInt 64 (16+(off : Int)) + BitVec.ofNat 64 j) =
      initial.mem (Arm.r (.GPR 29#5) initial + BitVec.ofInt 64 (16+(off : Int)) + BitVec.ofNat 64 j)) :
    ∃ final,SameWorld Z final reference ∧ RelW Γ f c fr.slots source.stored final ∧
      VReturns result.code (valueSem Γ.F fc X) source.seed other
        (retPairs [(source.called,.x 0)]) [output] final := by
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
  obtain ⟨final,returns,remainingWorld,finalRelated⟩ := source.virtual_return slot symbols otherRun otherCall held finalMemory
  have same : SameWorld Z final reference :=
    (SameWorld.mono covers remainingWorld).trans
      ((SameWorld.write_mem_bytes finalWorlds _ _ _).symm.trans (SameWorld.mono covers referenceWorld).symm)
  exact ⟨final,same,finalRelated,returns⟩

end Backend.Stock.CallStore
