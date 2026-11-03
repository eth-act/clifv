import FV.Backend.Proof.StockAcquireScanPrefixMachine
import FV.Backend.Proof.StockSelectScanRefines

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Exact successful source reads captured at actual sunk records. The list stays general. -/
structure SunkReadSnapshot (ctx : Ctx) (env : Clif.Env) (program : Clif.Program) where
  record : ScanRecord
  before : Clif.Frame × Clif.Mem
  after : Clif.Frame × Clif.Mem
  marked : record.input.sunk[record.inst]! = true
  source : SourceInstResult env program ctx record.inst before after
  read : SourceReadFrame ctx record.inst

/-- A sunk source fault stays explicit. No successful snapshot replaces this branch. -/
structure SunkFaultSnapshot (ctx : Ctx) (env : Clif.Env) (program : Clif.Program) where
  record : ScanRecord
  before : Clif.Frame × Clif.Mem
  code : Clif.TrapCode
  marked : record.input.sunk[record.inst]! = true
  source : SourceInstFault env program ctx record.inst before code
  read : SourceReadFrame ctx record.inst

/-- Successful capture preserves precisely the original source memory. -/
theorem SunkReadSnapshot.memory {ctx : Ctx} {env : Clif.Env} {program : Clif.Program}
    (captured : SunkReadSnapshot ctx env program) : captured.after.2 = captured.before.2 :=
  captured.read env program captured.before captured.after captured.source

/-- Only results belonging to captured original sunk producers are suspended. -/
def SuspendedReadResult {ctx : Ctx} {env : Clif.Env} {program : Clif.Program}
    (snapshots : List (SunkReadSnapshot ctx env program)) (value : Nat) : Prop :=
  ∃ captured ∈ snapshots,value ∈ ctx.insts[captured.record.inst]!.results

/-- The additive relation retains every demanded available value outside the exact captured results. -/
def PendingValuesHeld {ctx : Ctx} {env : Clif.Env} {program : Clif.Program}
    (snapshots : List (SunkReadSnapshot ctx env program)) (demand : Nat → Prop)
    (frame : Clif.Frame) (regs : Nat → CV) : Prop :=
  ∀ value,demand value → ¬SuspendedReadResult snapshots value → ValueHeld ctx frame regs value

/-- The empty frontier recovers the full existing value relation. -/
theorem pending_values_nil {ctx : Ctx} {env : Clif.Env} {program : Clif.Program}
    {demand : Nat → Prop} {frame : Clif.Frame} {regs : Nat → CV} :
    PendingValuesHeld (ctx := ctx) (env := env) (program := program) [] demand frame regs ↔
      ValuesHeld demand ctx frame regs := by
  constructor
  · intro held value required
    exact held value required (by rintro ⟨captured,member,_⟩;cases member)
  · intro held value required _
    exact held value required

/-- Appending captures cannot remove an already recorded suspended result. -/
theorem suspended_read_result_append_left {ctx : Ctx} {env : Clif.Env} {program : Clif.Program}
    {first second : List (SunkReadSnapshot ctx env program)} {value : Nat}
    (member : SuspendedReadResult first value) : SuspendedReadResult (first++second) value := by
  obtain ⟨captured,present,result⟩ := member
  exact ⟨captured,List.mem_append_left _ present,result⟩

/-- A newly captured read suspends exactly its original result names. -/
theorem suspended_read_result_append_last {ctx : Ctx} {env : Clif.Env} {program : Clif.Program}
    (snapshots : List (SunkReadSnapshot ctx env program)) (captured : SunkReadSnapshot ctx env program)
    {value : Nat} (result : value ∈ ctx.insts[captured.record.inst]!.results) :
    SuspendedReadResult (snapshots++[captured]) value :=
  ⟨captured,List.mem_append_right _ (List.mem_singleton_self _),result⟩

/-- The source-indexed invariant adds captured reads without changing GuardedScanRel. -/
def PendingGuardedScanRel (f : Clif.Function) (result : Result) (ctx : Ctx) (bi : Nat)
    (env : Clif.Env) (program : Clif.Program) (MR : MemRelT)
    (snapshots : List (SunkReadSnapshot ctx env program)) (st : State) (s : SourcePoint)
    (regs : Nat → CV) (world : Arm.ArmState) : Prop :=
  s.2.1.func = f ∧ DFGCons ctx (restrict s.2.1 (availOf f (availIn f result.ctx) bi s.1)) ∧
    MR s.2.1.slots s.2.2 world ∧
    PendingValuesHeld snapshots (fun value => Demanded st value ∧ value ∈ availOf f (availIn f result.ctx) bi s.1)
      s.2.1 (fun key => regs (aliasNum result.final.alias key))

/-- At an empty frontier the old guarded invariant remains exact. -/
theorem pending_guarded_nil {f : Clif.Function} {result : Result} {ctx : Ctx} {bi : Nat}
    {env : Clif.Env} {program : Clif.Program} {MR : MemRelT} {st : State} {s : SourcePoint}
    {regs : Nat → CV} {world : Arm.ArmState} :
    PendingGuardedScanRel f result ctx bi env program MR [] st s regs world ↔
      GuardedScanRel f result ctx bi MR st s regs world := by
  simp only [PendingGuardedScanRel,GuardedScanRel,pending_values_nil]

end Backend.Stock.Proof.Acquire810
