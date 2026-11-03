import FV.E2E.UnwindReachSource
import FV.E2E.MemTrapStatement

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver
set_option autoImplicit false

/-- Internal memory coverage retains the actual unwind stack and handler tables. -/
def MapFaultsFromX (mp : ArmFault.MemMap) (env : Clif.XEnv)
    (program : Clif.Program) (initial : Clif.XState) : Prop :=
  ∀ xs code address size, ReachX env program initial xs →
    Clif.MemTrapAt env.toEnv program xs.s code address size →
    ∃ offset < size, mp (BitVec.ofNat 64 (address + offset)) = .none

/-- Entry coverage uses the unchanged initial source state. -/
def MapFaultsX (mp : ArmFault.MemMap) (env : Clif.XEnv)
    (program : Clif.Program) (initial : Clif.State) : Prop :=
  MapFaultsFromX mp env program initial.toX

/-- An actual continuation retains caught-handler contexts and post-unwind memory. -/
theorem MapFaultsFromX.at_reached {mp : ArmFault.MemMap} {env : Clif.XEnv}
    {program : Clif.Program} {initial current : Clif.XState}
    (mapped : MapFaultsFromX mp env program initial)
    (reached : ReachX env program initial current) :
    MapFaultsFromX mp env program current := by
  intro xs code address size path trapped
  exact mapped xs code address size (reached.trans path) trapped

theorem MapFaultsX.at_reachedX {mp : ArmFault.MemMap} {env : Clif.XEnv}
    {program : Clif.Program} {initial : Clif.State} {current : Clif.XState}
    (mapped : MapFaultsX mp env program initial)
    (reached : ReachX env program initial.toX current) :
    MapFaultsFromX mp env program current :=
  mapped.at_reached reached

/-- This specialization is valid when the actual continuation has no unwind frames. -/
theorem MapFaultsX.at_reached {mp : ArmFault.MemMap} {env : Clif.XEnv}
    {program : Clif.Program} {initial current : Clif.State}
    (mapped : MapFaultsX mp env program initial)
    (reached : ReachX env program initial.toX current.toX) :
    MapFaultsX mp env program current :=
  mapped.at_reachedX reached

/-- Keep every old try/indirect clause while allowing mapped statement faults. -/
structure TrapsExplicitMX (env : Clif.XEnv) (program : Clif.Program)
    (initial : Clif.State) : Prop where
  stmt : ∀ xs code statement rest, ReachX env program initial.toX xs →
    Clif.step env.toEnv program xs.s = .trapped code →
    xs.s.frame.body = statement :: rest →
    explicitTrapInst statement.inst = true ∨
      ∃ address size, Clif.MemTrapAt env.toEnv program xs.s code address size
  tryCall : ∀ xs code fn args table, ReachX env program initial.toX xs →
    Clif.step env.toEnv program xs.s = .trapped code → xs.s.frame.body = [] →
    xs.s.frame.term = .tryCall fn args table →
    ∀ block ∈ initial.frame.func.blocks, block.term ≠ .tryCall fn args table
  tryCallInd : ∀ xs code callee args table, ReachX env program initial.toX xs →
    Clif.step env.toEnv program xs.s = .trapped code → xs.s.frame.body = [] →
    xs.s.frame.term = .tryCallIndirect callee args table →
    ∀ block ∈ initial.frame.func.blocks, block.term ≠ .tryCallIndirect callee args table
  indirect : ∀ xs statement rest signature callee args, ReachX env program initial.toX xs →
    xs.s.frame.body = statement :: rest → statement.inst = .callIndirect signature callee args →
    (∃ block ∈ initial.frame.func.blocks, statement ∈ block.body) → ∀ value,
    xs.s.frame.get callee = .ok value → ∀ function ∈ program.funcs,
    xs.s.mem.symbols function.name ≠ some value.toNat
  tryIndirect : ∀ xs callee args table, ReachX env program initial.toX xs →
    xs.s.frame.body = [] → xs.s.frame.term = .tryCallIndirect callee args table →
    (∃ block ∈ initial.frame.func.blocks, block.term = .tryCallIndirect callee args table) →
    ∀ value, xs.s.frame.get callee = .ok value → ∀ function ∈ program.funcs,
    xs.s.mem.symbols function.name ≠ some value.toNat

theorem TrapsExplicitX.toMX {env : Clif.XEnv} {program : Clif.Program}
    {initial : Clif.State} (admitted : TrapsExplicitX env program initial) :
    TrapsExplicitMX env program initial :=
  ⟨fun xs code statement rest reached trapped body =>
    .inl (admitted.stmt xs code statement rest reached trapped body),
    admitted.tryCall, admitted.tryCallInd, admitted.indirect, admitted.tryIndirect⟩

end E2E
