import FV.E2E.ReturnPinBinary
import FV.E2E.ProductionBoundaryWitness
import FV.E2E.PreparedReturnPinCallsWitness

namespace E2E.ReturnPinBinaryWitness
open Backend Backend.Proof Backend.Proof.Driver E2E.LinkCheck E2E.SemanticBinary
open E2E.ReturnPinBinary
set_option autoImplicit false
set_option Elab.async false
abbrev original := ProductionBoundaryWitness.input

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
-- witness: native_decide (the original complete fixture in both cleanup modes only)
theorem old_checked (cleanup : Bool) : SemanticStackBound.okB (original cleanup) = true := by
  cases cleanup <;> native_decide

theorem checked (cleanup : Bool) : ReturnPinBinary.okB (original cleanup) = true :=
  ReturnPinBinary.okB_previous (old_checked cleanup)

theorem ordinary_facts (cleanup : Bool) : BinaryBoundaryFacts.Facts (original cleanup) :=
  BinaryBoundaryFacts.of_semantic (SemanticStackBound.okB_sound (old_checked cleanup)
    (SemanticBinary.baseOk_F (F' := img (original cleanup)) (ProductionBoundaryWitness.base_ok cleanup))
    (fun _ h => h))

theorem outside (cleanup : Bool) (word : BitVec 64) :
    SemanticBinary.OutsideCall (original cleanup)
      (BinCheck.roByte (original cleanup) (ProductionBoundaryWitness.spec cleanup).data)
      ProductionBoundaryWitness.f (SemanticStackBound.stackFn (original cleanup) ProductionBoundaryWitness.f)
      (ProductionBoundaryWitness.machine cleanup word) [ProductionBoundaryWitness.argument word]
      (ProductionBoundaryWitness.entered cleanup) := by
  have old := ProductionBoundaryWitness.outside_call cleanup word
  exact ⟨old.pc,old.err,old.ra,old.spAligned,old.stack,old.stackFree,old.args,old.bytes,
    old.image,old.valid,old.symbols⟩

theorem source_run (cleanup : Bool) (word : BitVec 64) :
    SemanticBinary.ClifRun (original cleanup) closedBase ProductionBoundaryWitness.f
      (ProductionBoundaryWitness.machine cleanup word) [ProductionBoundaryWitness.argument word]
      (ProductionBoundaryWitness.cs cleanup word) := by
  have old := ProductionBoundaryWitness.clif_run cleanup word
  exact ⟨old.entry,old.slots,old.place⟩

theorem binary_facts (cleanup : Bool) :
    ReturnPinBinary.BinFacts (original cleanup) (SemanticBinary.imageOf (ProductionBoundaryWitness.file cleanup))
      (BinCheck.RelocAtWithResults (original cleanup) (original cleanup).results)
      (BinCheck.roByte (original cleanup) (ProductionBoundaryWitness.spec cleanup).data) :=
  ReturnPinBinary.binFacts_of_checks (checked cleanup)
    (Link.ProductionImageProof.bin_ok (Link.ProductionCompiler.attempt_spec
      (ProductionBoundaryWitness.compiler_success cleanup)).2)

theorem intact (cleanup : Bool) (word : BitVec 64) :
    (SemanticBinary.imageOf (ProductionBoundaryWitness.file cleanup)).Intact
      (ProductionBoundaryWitness.machine cleanup word) := ProductionBoundaryWitness.intact cleanup word

theorem complete_model_run (cleanup : Bool) (word : BitVec 64) :
    ArmRefines (art (original cleanup) ProductionBoundaryWitness.f).fb
      (art (original cleanup) ProductionBoundaryWitness.f).base
      (xreg 30 (ProductionBoundaryWitness.machine cleanup word))
      ((sys (original cleanup) closedBase).mach 3 ProductionBoundaryWitness.f)
      (modelOf (original cleanup) ProductionBoundaryWitness.f (ProductionBoundaryWitness.machine cleanup word))
      (.returned [ProductionBoundaryWitness.argument word] (ProductionBoundaryWitness.cm cleanup)) ∧
    (∀ a,(modelOf (original cleanup) ProductionBoundaryWitness.f
      (ProductionBoundaryWitness.machine cleanup word)).mem a ≠
      (ProductionBoundaryWitness.machine cleanup word).mem a →
        BinCheck.RelocAtWithResults (original cleanup) (original cleanup).results a) ∧
    (sys (original cleanup) closedBase).RunGoodL 3 ProductionBoundaryWitness.f
      (modelOf (original cleanup) ProductionBoundaryWitness.f (ProductionBoundaryWitness.machine cleanup word)) := by
  have base : BaseOk (sys (original cleanup) closedBase) := ProductionBoundaryWitness.base_ok cleanup
  have found : (prog (original cleanup)).func? ProductionBoundaryWitness.name = some ProductionBoundaryWitness.f :=
    ProductionBoundaryWitness.program_find cleanup
  have contract : (SemanticStackBound.ofInput (original cleanup) closedBase (img (original cleanup))).OkSemanticReturnPins :=
    ReturnPinBinary.okB_sound (checked cleanup) (baseOk_F base) (fun _ h => h)
  have returned := ProductionBoundaryWitness.source_returns cleanup word
  have traps := ReturnPinBinary.trapsExplicit_of_run contract (Clif.Program.func?_some found).1
    (source_run cleanup word).entry (outside cleanup word).symbols returned
  have good : SemanticStackBound.goodN (original cleanup) ProductionBoundaryWitness.name = true :=
    (ProductionBoundaryWitness.concrete_facts cleanup).2.2.1
  have result := ReturnPinBinary.binary_correctX (binary_facts cleanup) closedBase base good found 3
    (intact cleanup word) (outside cleanup word) (source_run cleanup word) traps
  rw [returned] at result
  exact ⟨result.1,result.2.1,result.2.2 (Or.inl ⟨_,_,rfl⟩)⟩

/-- Keep the original complete captured source and the proved Stock caller. -/
def mixed (cleanup : Bool) : SemanticStackBound.CompilerInput :=
  {toLinkInput := PreparedReturnPinCallsWitness.input,cleanup,lower := Stock.VoidCall.NI.lowerValidated}

def mixedChecks (cleanup : Bool) : Bool :=
  ReturnPinBinary.okB (mixed cleanup) && !SemanticStackBound.okB (mixed cleanup) &&
  (prog (mixed cleanup)).funcs.all (fun f => !hasTls f) &&
  SemanticStackBound.goodN (mixed cleanup) (mixed cleanup).funcs[1]!.func.name

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
-- witness: native_decide (the unchanged complete mixed source in both cleanup modes only)
theorem mixed_checks : (mixedChecks false && mixedChecks true) = true := by native_decide

attribute [local irreducible] mixed

theorem mixed_contract (cleanup : Bool) :
    (SemanticStackBound.ofInput (mixed cleanup) closedBase (img (mixed cleanup))).OkSemanticReturnPins := by
  have rows := Bool.and_eq_true_iff.mp mixed_checks
  have row : mixedChecks cleanup = true := by cases cleanup <;> first | exact rows.1 | exact rows.2
  simp only [mixedChecks,Bool.and_eq_true,and_assoc] at row
  have base : BaseOk (SemanticStackBound.ofInput (mixed cleanup) closedBase (img (mixed cleanup))) :=
    baseOk_closedR fun f member => by
      simpa only [Bool.not_eq_true'] using List.all_eq_true.mp row.2.2.1 f member
  exact ReturnPinBinary.okB_sound row.1 base (fun _ h => h)

end E2E.ReturnPinBinaryWitness

namespace E2E.ReturnPinBinaryWitness
open Backend Backend.Proof Backend.Proof.Driver E2E.LinkCheck E2E.SemanticBinary
set_option autoImplicit false
set_option Elab.async false

theorem depth (cleanup : Bool) (word : BitVec 64) :
    Clif.DepthLe closedBase.env (prog (original cleanup)) 0 (ProductionBoundaryWitness.cs cleanup word) :=
  Clif.depthLe_of_depthB 4 _ (by rfl)

theorem outside_budget (cleanup : Bool) (word : BitVec 64) (N : Nat) (bound : N ≤ 4096) :
    SemanticBinary.OutsideCall (original cleanup)
      (BinCheck.roByte (original cleanup) (ProductionBoundaryWitness.spec cleanup).data)
      ProductionBoundaryWitness.f N (ProductionBoundaryWitness.machine cleanup word)
      [ProductionBoundaryWitness.argument word] (ProductionBoundaryWitness.entered cleanup) where
  pc := (outside cleanup word).pc
  err := (outside cleanup word).err
  ra := (outside cleanup word).ra
  spAligned := (outside cleanup word).spAligned
  stack := by
    rw [ProductionBoundaryWitness.machine_sp]
    change N ≤ 0x1000000
    omega
  stackFree := by
    intro a image below
    have limit := ProductionBoundaryWitness.image_bound (by decide)
      (ProductionBoundaryWitness.concrete_facts cleanup).2.2.2 image
    rw [ProductionBoundaryWitness.machine_sp] at below
    change a.toNat < 0x1000000 ∧ 0x1000000 ≤ a.toNat + N at below
    omega
  args := (outside cleanup word).args
  bytes := (outside cleanup word).bytes
  image := (outside cleanup word).image
  valid := by
    intro a n valid
    simp [ProductionBoundaryWitness.entered,ProductionBoundaryWitness.f,Clif.StockPrologueSource.source,
      Clif.enterSlots,Clif.bumpSlots,ProductionBoundaryWitness.cm,Clif.Mem.valid,Clif.Mem.empty] at valid
  symbols := (outside cleanup word).symbols

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
-- witness: native_decide (two fixed compiled frame budgets only; with the probes' `pbMax`, #581)
theorem depth_budget (cleanup : Bool) :
    frameDrop (art (original cleanup) ProductionBoundaryWitness.f).af +
      ((original cleanup).D*3 + pbMax (original cleanup)) ≤ 4096 := by
  cases cleanup <;> native_decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
-- witness: native_decide (#581: the fixture's frames are below 4 KiB, so its program has no
-- stack probes and the `pbMax` added to the budgets above is 0; the input of all three
-- return-pin witnesses, `ReturnPinExecWitness` and `Link.ReturnPinExeSourceWitness` included)
theorem pbMax_zero (cleanup : Bool) : pbMax (original cleanup) = 0 := by
  cases cleanup <;> native_decide

end E2E.ReturnPinBinaryWitness

namespace E2E.ReturnPinBinaryWitness
open Backend Backend.Proof Backend.Proof.Driver E2E.LinkCheck E2E.SemanticBinary
set_option autoImplicit false
set_option Elab.async false

def ModelReturn (cleanup : Bool) (word : BitVec 64) (M : Nat) : Prop :=
  ArmRefines (art (original cleanup) ProductionBoundaryWitness.f).fb
    (art (original cleanup) ProductionBoundaryWitness.f).base
    (xreg 30 (ProductionBoundaryWitness.machine cleanup word))
    ((sys (original cleanup) closedBase).mach M ProductionBoundaryWitness.f)
    (modelOf (original cleanup) ProductionBoundaryWitness.f (ProductionBoundaryWitness.machine cleanup word))
    (.returned [ProductionBoundaryWitness.argument word] (ProductionBoundaryWitness.cm cleanup)) ∧
  (∀ a,(modelOf (original cleanup) ProductionBoundaryWitness.f
    (ProductionBoundaryWitness.machine cleanup word)).mem a ≠
    (ProductionBoundaryWitness.machine cleanup word).mem a →
      BinCheck.RelocAtWithResults (original cleanup) (original cleanup).results a) ∧
  (sys (original cleanup) closedBase).RunGoodL M ProductionBoundaryWitness.f
    (modelOf (original cleanup) ProductionBoundaryWitness.f (ProductionBoundaryWitness.machine cleanup word))

theorem depth_model_run (cleanup : Bool) (word : BitVec 64) : ModelReturn cleanup word 3 := by
  have base : BaseOk (sys (original cleanup) closedBase) := ProductionBoundaryWitness.base_ok cleanup
  have found := ProductionBoundaryWitness.program_find cleanup
  have contract : (SemanticStackBound.ofInput (original cleanup) closedBase (img (original cleanup))).OkSemanticReturnPins :=
    ReturnPinBinary.okB_sound (checked cleanup) (baseOk_F base) (fun _ h => h)
  have returned := ProductionBoundaryWitness.source_returns cleanup word
  have traps := ReturnPinBinary.trapsExplicit_of_run contract (Clif.Program.func?_some found).1
    (source_run cleanup word).entry (outside cleanup word).symbols returned
  have entry := outside_budget cleanup word _ (depth_budget cleanup)
  have result := ReturnPinBinary.binary_correct_depthX (binary_facts cleanup) closedBase base found 3
    (intact cleanup word) entry (source_run cleanup word) traps
  rw [returned] at result
  exact ⟨result.1,result.2.1,result.2.2 (Or.inl ⟨_,_,rfl⟩)⟩

theorem peak_model_run (cleanup : Bool) (word : BitVec 64) : ModelReturn cleanup word 0 := by
  have base : BaseOk (sys (original cleanup) closedBase) := ProductionBoundaryWitness.base_ok cleanup
  have found := ProductionBoundaryWitness.program_find cleanup
  have contract : (SemanticStackBound.ofInput (original cleanup) closedBase (img (original cleanup))).OkSemanticReturnPins :=
    ReturnPinBinary.okB_sound (checked cleanup) (baseOk_F base) (fun _ h => h)
  have returned := ProductionBoundaryWitness.source_returns cleanup word
  have bounded := depth cleanup word
  have traps := ReturnPinBinary.trapsExplicit_of_runD contract (Clif.Program.func?_some found).1
    (source_run cleanup word).entry (outside cleanup word).symbols bounded returned
  have budget : frameDrop (art (original cleanup) ProductionBoundaryWitness.f).af +
      ((original cleanup).D*0 + pbMax (original cleanup)) ≤ 4096 := by
    have bound := depth_budget cleanup
    omega
  have entry := outside_budget cleanup word _ budget
  have result := ReturnPinBinary.binary_correct_peakX (binary_facts cleanup) closedBase base found 3 0
    (intact cleanup word) entry (source_run cleanup word) bounded traps
  rw [returned] at result
  exact ⟨result.1,result.2.1,result.2.2 (Or.inl ⟨_,_,rfl⟩)⟩

end E2E.ReturnPinBinaryWitness
