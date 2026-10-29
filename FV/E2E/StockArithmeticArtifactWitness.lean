module

public import FV.E2E.StockArithmeticArtifact
public import FV.Backend.LinearScan
public import FV.Backend.Proof.LowerDecide
public import FV.Backend.Lowering.StockD0

@[expose] public section

namespace E2E.StockArithmeticArtifactWitness
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

/-- A nonempty arithmetic function with an unused argument and an explicit
source stack slot. The source slot's address remains a caller choice. -/
def function : Clif.Function := {
  name := "stock_semantic_artifact"
  sig := {
    params := List.replicate 3 ⟨.i64,.none,.normal⟩
    returns := [⟨.i64,.none,.normal⟩]
    callConv := some .systemV }
  slots := [(7,⟨8,some 8⟩)]
  blocks := [{
    id := 0
    params := [(0,.i64),(1,.i64),(2,.i64)]
    body := [⟨[3],.binary .iadd .i64 0 1⟩]
    term := .ret [3] }] }

private def checks : Bool :=
  dominatedB function && lowerScopeB function && sigAbiOk function.sig &&
  match Stock.lower function with
  | .error _ => false
  | .ok result =>
    !lowerCheck function (Stock.D0.compact function.name result) &&
    match Backend.prepare result.code with
    | .error _ => false
    | .ok vcp =>
      prepCheck result.code vcp &&
      match leanAlloc vcp with
      | .error _ => false
      | .ok rf =>
        (checkAlloc vcp rf).isOk &&
        match lowerRFunc vcp rf with
        | .error _ => false
        | .ok af =>
          match emitFunc 0 af with
          | .error _ => false
          | .ok fa => formsCoveredB ⟨fa.k,af.slotBase⟩ vcp && fa.layout.isOk

/-- Fixed compiler data only: the raw Stock path completes every stage while
the compact Stock output is rejected by the legacy lowering validator. -/
theorem checks_true : checks = true := by native_decide

/-- Joint inhabitation of the actual raw Stock/Lean allocator/emission/layout
contract, beyond the legacy checker domain. -/
theorem compiled_exists :
    Dominated function ∧ LowerScope function ∧ sigAbiOk function.sig = true ∧
    ∃ result vcp rf af fa fb, CompiledStockArithmetic function 0 result vcp rf af fa fb ∧
      leanAlloc vcp = .ok rf ∧ FormsCovered ⟨fa.k,af.slotBase⟩ vcp ∧
      lowerCheck function (Stock.D0.compact function.name result) = false := by
  have h := checks_true
  simp only [checks,Bool.and_eq_true] at h
  obtain ⟨⟨⟨dominated,scope⟩,abi⟩,h⟩ := h
  refine ⟨dominated_of dominated,lowerScope_of scope,abi,?_⟩
  cases lowered : Stock.lower function with
  | error message => simp [lowered] at h
  | ok result =>
    simp only [lowered,Bool.and_eq_true,Bool.not_eq_true'] at h
    obtain ⟨legacy,h⟩ := h
    cases prepared : Backend.prepare result.code with
    | error message => simp [prepared] at h
    | ok vcp =>
      simp only [prepared,Bool.and_eq_true] at h
      obtain ⟨prepOk,h⟩ := h
      cases allocated : leanAlloc vcp with
      | error message => simp [allocated] at h
      | ok rf =>
        simp only [allocated,Bool.and_eq_true] at h
        obtain ⟨checked,h⟩ := h
        cases physical : lowerRFunc vcp rf with
        | error message => simp [physical] at h
        | ok af =>
          cases emitted : emitFunc 0 af with
          | error message => simp [physical,emitted] at h
          | ok fa =>
            simp only [physical,emitted,Bool.and_eq_true] at h
            obtain ⟨covered,layoutOk⟩ := h
            cases layout : fa.layout with
            | error message => rw [layout] at layoutOk; change false = true at layoutOk; cases layoutOk
            | ok fb =>
              have check : checkAlloc vcp rf = .ok () := by
                cases check : checkAlloc vcp rf with
                | error message => rw [check] at checked; change false = true at checked; cases checked
                | ok value => cases value; rfl
              exact ⟨result,vcp,rf,af,fa,fb,
                ⟨lowered,prepared,prepOk,check,physical,emitted,layout⟩,
                allocated,(formsCoveredB_iff _ _).mp covered,legacy⟩

def frame (u v unused : BitVec 64) (slot : Nat) : Clif.Frame := {
  func := function
  regs := ((Clif.Regs.empty.set 0 ⟨.i64,u⟩).set 1 ⟨.i64,v⟩).set 2 ⟨.i64,unused⟩
  slots := [(7,slot)]
  body := function.blocks[0]!.body
  term := .ret [3] }

/-- The original production entry contract holds for arbitrary source slot
addresses and all three values, including the parameter omitted by Stock. -/
theorem source_entry (u v unused : BitVec 64) (slot : Nat) :
    ClifEntry function [⟨.i64,u⟩,⟨.i64,v⟩,⟨.i64,unused⟩] ⟨frame u v unused slot,[],Clif.Mem.empty⟩ := by
  refine ⟨rfl,rfl,rfl,?_,rfl⟩
  exact ⟨function.blocks[0]!,rfl,rfl,rfl,rfl,rfl⟩

theorem source_returns (u v unused : BitVec 64) (slot : Nat) :
    Clif.runLoop Clif.Env.empty {funcs := []} 2 ⟨frame u v unused slot,[],Clif.Mem.empty⟩ =
      .returned [⟨.i64,u+v⟩] Clif.Mem.empty := rfl

/-- The concrete non-legacy artifact instantiates the full machine consumer
for every argument value and original ABI activation, with no caller-selected
virtual file or executable enterSlots condition. -/
theorem consumer_witness :
    ∃ result vcp rf af fa fb,
      CompiledStockArithmetic function 0 result vcp rf af fa fb ∧
      lowerCheck function (Stock.D0.compact function.name result) = false ∧
      ∀ (X : ExtSem) (H : ArmHooks) (K : Nat),
      (∀ s, CalleeOk
        (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite) →
      (vcp.hasTryCall = true → ∀ s, CalleeTryOk
        (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite) →
      (vcp.hasTls = true → ∀ s, TlsOk
        (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H) →
      ∀ (u v unused : BitVec 64) (slot : Nat) (base ra : BitVec 64) (s w : Arm.ArmState),
      AbiEntry fb base ra s → StackAvail K af s → BodyEntry af s w →
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
        (fun _ => none),af.slotBase,(RAFrame.compute vcp rf).intBase⟩
        function [(7,slot)] Clif.Mem.empty w →
      ArgsAtEntry (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s)
        function.sig [⟨.i64,u⟩,⟨.i64,v⟩,⟨.i64,unused⟩] w →
      ArmRefines fb base ra (ArmStepX X H fa) s (.returned [⟨.i64,u+v⟩] Clif.Mem.empty) := by
  obtain ⟨dominated,scope,abi,result,vcp,rf,af,fa,fb,compiled,_,covered,legacy⟩ := compiled_exists
  refine ⟨result,vcp,rf,af,fa,fb,compiled,legacy,?_⟩
  intro X H K callees tries tls u v unused slot base ra s w activation stack bodyEntry memory arguments
  have family : ∀ stm ∈ function.blocks[0]!.body, ∃ subtract : Bool, ∃ ty x y,
      stm.inst = .binary (if subtract then .isub else .iadd) ty x y := by
    intro stm member
    have equal : stm = ⟨[3],.binary .iadd .i64 0 1⟩ := List.mem_singleton.mp member
    subst stm
    exact ⟨false,.i64,0,1,rfl⟩
  have semantics := backend_correct_stock_arithmetic compiled scope dominated abi
    (b := function.blocks[0]!) rfl family (xs := [3]) rfl rfl covered callees tries tls
    activation stack bodyEntry (source_entry u v unused slot)
    (env := Clif.Env.empty) (cp := {funcs := []})
    (syms := fun _ => none) (by intro n b h; cases h) memory arguments 2
  simpa only [source_returns] using semantics

end E2E.StockArithmeticArtifactWitness
