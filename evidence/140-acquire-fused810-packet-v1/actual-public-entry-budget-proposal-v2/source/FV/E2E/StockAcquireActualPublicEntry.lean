import FV.E2E.BinaryBoundaryFacts

namespace E2E.StockAcquirePending
open Backend Backend.Proof Backend.Proof.Driver E2E.LinkCheck E2E.SemanticBinary
set_option autoImplicit false
set_option Elab.async false

/-- Reducing the reserved stack retains the original outside-call conditions. -/
theorem actual_outsideCall_mono {I : SemanticStackBound.CompilerInput}
    {roB : BitVec 64 → Option (BitVec 8)} {f : Clif.Function} {N n : Nat}
    {r : Arm.ArmState} {args : List Clif.Val} {cm : Clif.Mem}
    (call : OutsideCall I roB f N r args cm) (bound : n ≤ N) :
    OutsideCall I roB f n r args cm := by
  have below : ∀ a,StackBelow n (spv r) a → StackBelow N (spv r) a := by
    intro a h
    exact ⟨h.1,Nat.le_trans h.2 (Nat.add_le_add_left bound _)⟩
  refine ⟨call.pc,call.err,call.ra,call.spAligned,Nat.le_trans bound call.stack,
    fun a code h => call.stackFree a code (below a h),call.args,call.bytes,call.image,?_,call.symbols⟩
  intro a bytes valid
  obtain ⟨fits,rest⟩ := call.valid a bytes valid
  exact ⟨fits,fun k hk => ⟨(rest k hk).1,fun h => (rest k hk).2 (below _ h)⟩⟩

/-- The existing finite-budget admission fixes the hybrid bound at every depth. -/
theorem actual_input_entry_budget {I : SemanticStackBound.CompilerInput} {B : BaseEnv}
    {F : BitVec 64 → Prop} {name : String} {f : Clif.Function}
    (named : (prog I).func? name = some f) (finite : SemanticStackBound.goodN I name = true)
    (M : Nat) :
    frameDrop (art I f).af +
      (SemanticStackBound.ofInput I B F).hybrid (SemanticStackBound.budO I)
        (SemanticStackBound.budMax I) M f = SemanticStackBound.stackFn I f := by
  unfold SemanticStackBound.goodN at finite
  rw [named] at finite
  obtain ⟨budget,found⟩ := Option.isSome_iff_exists.1 finite
  simp only [LinkSys.hybrid,found,SemanticStackBound.stackFn,SemanticStackBound.bud,Option.getD_some]

/-- The actual input supplies the original machine entry from its outside-call boundary.
The artifact, image and prepared argument registers all come from the same checked input. -/
theorem actual_input_machEntry {I : SemanticStackBound.CompilerInput} {B : BaseEnv}
    {modes : Clif.Function → ReturnPinMode} (checked : (sys I B).OkReturnPins modes)
    {f : Clif.Function} (member : f ∈ (prog I).funcs) {K : Nat} {r : Arm.ArmState}
    {roB : BitVec 64 → Option (BitVec 8)} {args : List Clif.Val} {cs : Clif.State}
    (readonly : ∀ a b,roB a = some b → r.mem a = b)
    (call : OutsideCall I roB f (frameDrop (art I f).af+K) r args cs.mem)
    (source : ClifRun I B f r args cs)
    {κ : Nat → Clif.Function → Nat} {M : Nat} (budget : κ M f = K) :
    (sys I B).MachEntry κ M f (worldF I f K r) (img I) (xreg 30 r)
      (modelOf I f r) (bodyOf (art I f).af (modelOf I f r)) := by
  obtain ⟨abi,stack,free,image,body,arguments,avoid,related,place⟩ :=
    BinaryBoundaryFacts.premises (B := B) (BinaryBoundaryFacts.of_returnPins checked)
      member readonly call source
  have bodyW := body.w (worldF I f K r) (fun reg arg =>
    (checked.argRegs f member).2.1 reg (checked.entryRegs f member reg arg))
  refine ⟨abi.toCall,?_,?_,?_,fun _ h => h,image,bodyW⟩
  · simpa only [budget] using stack
  · simpa only [budget] using free
  · change frameWG (κ M f) (RAFrame.compute (art I f).vcp (art I f).rf).intBase
      (RAFrame.compute (art I f).vcp (art I f).rf).size (art I f).af (img I) (modelOf I f r) = _
    rw [budget]
    rfl

/-- The original finite-budget check removes the internal entry-budget certificate. -/
theorem actual_input_machEntry_finite {I : SemanticStackBound.CompilerInput} {B : BaseEnv}
    {modes : Clif.Function → ReturnPinMode} (checked : (sys I B).OkReturnPins modes)
    {name : String} {f : Clif.Function} (named : (prog I).func? name = some f)
    (finite : SemanticStackBound.goodN I name = true) {r : Arm.ArmState}
    {roB : BitVec 64 → Option (BitVec 8)} {args : List Clif.Val} {cs : Clif.State}
    (readonly : ∀ a b,roB a = some b → r.mem a = b)
    (call : OutsideCall I roB f (SemanticStackBound.stackFn I f) r args cs.mem)
    (source : ClifRun I B f r args cs) (M : Nat) :
    (sys I B).MachEntry ((sys I B).hybrid (SemanticStackBound.budO I) (SemanticStackBound.budMax I))
      M f (worldF I f (SemanticStackBound.bud I f) r) (img I) (xreg 30 r)
      (modelOf I f r) (bodyOf (art I f).af (modelOf I f r)) := by
  have member : f ∈ (prog I).funcs := (Clif.Program.func?_some named).1
  have budget := actual_input_entry_budget (B := B) (F := fun _ => False) named finite M
  have equal : (sys I B).hybrid (SemanticStackBound.budO I) (SemanticStackBound.budMax I) M f =
      SemanticStackBound.bud I f := Nat.add_left_cancel budget
  exact actual_input_machEntry checked member readonly call source equal

end E2E.StockAcquirePending
