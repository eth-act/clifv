import FV.E2E.UnwindReachSource
import FV.E2E.MemTrapStatement

namespace E2E
set_option autoImplicit false

/-- Internal memory coverage over the actual unwind run, including caught-handler paths. -/
def MapFaultsX (mp : ArmFault.MemMap) (env : Clif.XEnv)
    (program : Clif.Program) (initial : Clif.State) : Prop :=
  ∀ xs code address size, ReachX env program initial.toX xs →
    Clif.MemTrapAt env.toEnv program xs.s code address size →
    ∃ offset < size, mp (BitVec.ofNat 64 (address + offset)) = .none

/-- This internal continuation keeps the actual post-unwind source memory. -/
theorem MapFaultsX.at_reached {mp : ArmFault.MemMap} {env : Clif.XEnv}
    {program : Clif.Program} {initial current : Clif.State}
    (mapped : MapFaultsX mp env program initial)
    (reached : ReachX env program initial.toX current.toX) :
    MapFaultsX mp env program current := by
  intro xs code address size path trapped
  exact mapped xs code address size (reached.trans path) trapped

/-- Keep every old try/indirect clause while allowing mapped statement faults. -/
structure TrapsExplicitMX (env : Clif.XEnv) (program : Clif.Program)
    (initial : Clif.State) : Prop where
  stmt : ∀ xs code statement rest, ReachX env program initial.toX xs →
    Clif.step env.toEnv program xs.s = .trapped code →
    xs.s.frame.body = statement :: rest →
    explicitTrapInst statement.inst = true ∨ Clif.memTrapInst statement.inst = true
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
