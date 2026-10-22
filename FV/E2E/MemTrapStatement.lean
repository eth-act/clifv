import FV.E2E.Statement
import FV.Clif.MemTrap
import FV.ArmFault.Step

/-!
# The run premises and the observable of a memory trap (A3, #412, slice F2)

`docs/plans/memfault.md`, "Premises of the new theorems". The old theorems take
`TrapsExplicit` (no load, store or atomic traps) and, for the source run, `Opt.Legal.NoMemTrap`.
The memory-trap variants (`*_memtrap`) take instead:

* **`TrapsExplicitM`**: `TrapsExplicit` whose statement clause also allows the memory traps of
  `Clif.memTrapInst` (`atomic_rmw`, `atomic_cas`, lowered to the LL/SC loops); every
  `TrapsExplicit` is one (`TrapsExplicit.toM`);
* **`MapFaults mp`** (about the process's memory map `mp`, `ArmFault.MemMap`): every memory trap
  of a reachable state (`Clif.MemTrapAt … c a n`) has a byte in `[a, a + n)` that `mp` does
  not map at all (`Perm.none`: neither readable nor writable, so the access's first instruction,
  the loop's `ldaxr`, faults). Discharged by the null page: Linux maps nothing below
  `vm.mmap_min_addr` (at least one page) and `Clif.Mem.next` starts at `0x10000`.

The observable of a memory trap is **`TrapAtF mp`**: the machine stops at a trap site of the
function's table with the CLIF code (`TrapAt`), and its next instruction faults under `mp`
(`ArmFault.Faults`: a byte of the precise footprint of its step is not allowed). On the
fault-aware step `ArmFault.stepF mp` that state is followed by the fault (`stepF_fault`).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- **The run premises with memory traps** (`TrapsExplicit` widened): a statement traps only if
it is an explicitly trapping instruction or a memory instruction of `Clif.memTrapInst`
(`atomic_rmw`, `atomic_cas`); the other clauses are `TrapsExplicit`'s. -/
structure TrapsExplicitM (env : Clif.Env) (p : Clif.Program) (cs : Clif.State) : Prop where
  stmt : ∀ s c st rest, Reach env p cs s → Clif.step env p s = .trapped c →
    s.frame.body = st :: rest → explicitTrapInst st.inst = true ∨ Clif.memTrapInst st.inst = true
  tryCall : ∀ s c fn args et, Reach env p cs s → Clif.step env p s = .trapped c →
    s.frame.body = [] → s.frame.term = .tryCall fn args et →
    ∀ B ∈ cs.frame.func.blocks, B.term ≠ .tryCall fn args et
  tryCallInd : ∀ s c callee args et, Reach env p cs s → Clif.step env p s = .trapped c →
    s.frame.body = [] → s.frame.term = .tryCallIndirect callee args et →
    ∀ B ∈ cs.frame.func.blocks, B.term ≠ .tryCallIndirect callee args et
  indirect : ∀ s st rest sig callee args, Reach env p cs s → s.frame.body = st :: rest →
    st.inst = .callIndirect sig callee args → (∃ B ∈ cs.frame.func.blocks, st ∈ B.body) → ∀ cv,
    s.frame.get callee = .ok cv → ∀ g ∈ p.funcs, s.mem.symbols g.name ≠ some cv.toNat
  tryIndirect : ∀ s callee args et, Reach env p cs s → s.frame.body = [] →
    s.frame.term = .tryCallIndirect callee args et →
    (∃ B ∈ cs.frame.func.blocks, B.term = .tryCallIndirect callee args et) → ∀ cv,
    s.frame.get callee = .ok cv → ∀ g ∈ p.funcs, s.mem.symbols g.name ≠ some cv.toNat

/-- `TrapsExplicit` is the special case without memory traps. -/
theorem TrapsExplicit.toM {env : Clif.Env} {p : Clif.Program} {cs : Clif.State}
    (h : TrapsExplicit env p cs) : TrapsExplicitM env p cs :=
  ⟨fun s c st rest hr hs hb => .inl (h.stmt s c st rest hr hs hb), h.tryCall, h.tryCallInd,
    h.indirect, h.tryIndirect⟩

/-- **The memory map forbids every memory trap's access**: at every reachable state where the
step traps at a memory instruction with access `[a, a + n)` outside the CLIF allocations
(`Clif.MemTrapAt`), some byte of the access is unmapped (`Perm.none`). -/
def MapFaults (mp : ArmFault.MemMap) (env : Clif.Env) (p : Clif.Program) (cs : Clif.State) :
    Prop :=
  ∀ s c a n, Reach env p cs s → Clif.MemTrapAt env p s c a n →
    ∃ k < n, mp (BitVec.ofNat 64 (a + k)) = .none

/-- `MapFaults` holds for every map when the run has no memory trap. -/
theorem MapFaults.of_noMemTrap {mp : ArmFault.MemMap} {env : Clif.Env} {p : Clif.Program}
    {cs : Clif.State} (h : ∀ s c a n, Reach env p cs s → ¬ Clif.MemTrapAt env p s c a n) :
    MapFaults mp env p cs :=
  fun s c a n hr hm => absurd hm (h s c a n hr)

/-- **The observable of a memory trap**: the machine is at a trap site of the function with code
`c` (`TrapAt`) and its next step faults under the memory map `mp`. -/
def TrapAtF (mp : ArmFault.MemMap) (fb : FnBin) (base : BitVec 64) (c : Clif.TrapCode)
    (s : Arm.ArmState) : Prop :=
  TrapAt fb base c s ∧ ArmFault.Faults mp s

/-- On the fault-aware step the state after a `TrapAtF` state is the memory fault, everything
else unchanged. -/
theorem TrapAtF.stepF {mp : ArmFault.MemMap} {fb : FnBin} {base : BitVec 64} {c : Clif.TrapCode}
    {s : Arm.ArmState} (h : TrapAtF mp fb base c s) :
    ArmFault.stepF mp s = Arm.write_err ArmFault.memFault s :=
  ArmFault.stepF_fault h.2

end E2E
