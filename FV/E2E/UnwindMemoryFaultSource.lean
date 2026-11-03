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

namespace UnwindMemoryWitness

private def statement (store : Bool) : Clif.Stmt :=
  if store then ⟨[],.store .store .i64 {} 1 0 0⟩
  else ⟨[2],.load .load .i64 {} 0 0⟩

private def function (store : Bool) : Clif.Function := {
  name := "unwind_memory_statement"
  sig := {params := [{ty := .i64},{ty := .i64}]}
  blocks := [{id := 0,params := [(0,.i64),(1,.i64)],body := [statement store],term := .ret []}] }

private def state (store : Bool) : Clif.State := {
  frame := {
    func := function store
    regs := (Clif.Regs.empty.set 0 ⟨.i64,0⟩).set 1 ⟨.i64,42⟩
    slots := [],body := [statement store],term := .ret []}
  callers := [],mem := Clif.Mem.empty }

private def program (store : Bool) : Clif.Program := {funcs := [function store]}

private theorem memory_event (store : Bool) :
    Clif.MemTrapAt Clif.Env.empty (program store) (state store) .heapOob 0 8 := by
  cases store with
  | false => exact ⟨rfl,rfl,⟨statement false,[],rfl,.load (pv := ⟨.i64,0⟩) rfl⟩⟩
  | true => exact ⟨rfl,rfl,⟨statement true,[],rfl,.store (pv := ⟨.i64,0⟩) rfl⟩⟩

private theorem reached_entry (store : Bool) {xs : Clif.XState}
    (reached : ReachX Clif.Env.empty.toX (program store) (state store).toX xs) :
    xs = (state store).toX := by
  cases reached with
  | refl => rfl
  | step next _ =>
    have trapped : Clif.stepX Clif.Env.empty.toX (program store) (state store).toX =
        .trapped .heapOob := by cases store <;> rfl
    rw [trapped] at next
    cases next

private theorem admitted (store : Bool) :
    TrapsExplicitMX Clif.Env.empty.toX (program store) (state store) := by
  constructor
  · intro xs code inst rest reached trapped body
    have same := reached_entry store reached
    subst xs
    have event := memory_event store
    have codeEq : code = .heapOob := Clif.StepResult.trapped.inj
      (trapped.symm.trans (by simpa only [Clif.Env.toX_toEnv,Clif.State.toX] using event.1))
    subst code
    exact .inr ⟨0,8,by simpa only [Clif.Env.toX_toEnv,Clif.State.toX] using event⟩
  · intro xs code fn args table reached trapped body term block member
    have same := reached_entry store reached
    subst xs
    cases body
  · intro xs code callee args table reached trapped body term block member
    have same := reached_entry store reached
    subst xs
    cases body
  · intro xs inst rest signature callee args reached body call member value found g inside
    have same := reached_entry store reached
    subst xs
    change [statement store] = inst :: rest at body
    have instEq : statement store = inst := (List.cons.inj body).1
    subst inst
    cases store <;> cases call
  · intro xs callee args table reached body term member value found g inside
    have same := reached_entry store reached
    subst xs
    cases body

/-- A default-flag ordinary load inhabits the new memory statement clause. -/
theorem default_load_admitted :
    TrapsExplicitMX Clif.Env.empty.toX (program false) (state false) ∧
    Clif.MemTrapAt Clif.Env.empty (program false) (state false) .heapOob 0 8 :=
  ⟨admitted false,memory_event false⟩

/-- A default-flag ordinary store inhabits the same clause. -/
theorem default_store_admitted :
    TrapsExplicitMX Clif.Env.empty.toX (program true) (state true) ∧
    Clif.MemTrapAt Clif.Env.empty (program true) (state true) .heapOob 0 8 :=
  ⟨admitted true,memory_event true⟩

end UnwindMemoryWitness

end E2E
