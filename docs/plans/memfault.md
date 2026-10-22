# A3 (#412): memory-access faults under the theorems

Plan of 2026-10-22, base main 729900af. Branch prefix `agent/memfault`. Gap A3/B2 of the gap
audit (the trap theorems assume the source run's `NoMemTrap`). One PR per slice; old theorems
keep their premises, new results get new names, every new top-level theorem a witness.

## Status

| Slice | State |
| --- | --- |
| F0 | this plan |
| F1 | done: `FV/ArmFault/Step.lean` (`stepF`, `runF_eq_run`, `runF_fault`, …), witnesses `FV/ArmFault/Witness.lean`, `scripts/arm-fault-cosim.sh` 152 forms, 30 400 vectors (20 577 faults), 0 failures (`docs/contracts/arm.md`, "Memory faults") |
| F2 | done: `FV/Clif/MemTrap.lean` (`Access`, `MemTrapAt`, `memTrapInst` = `atomic_rmw`/`atomic_cas`, `memTrapAt_of_trapped`, `evalInst_notrap`), `FV/E2E/MemTrapStatement.lean` (`TrapsExplicitM`, `TrapsExplicit.toM`, `MapFaults`, `TrapAtF`), witness `FV/Clif/MemTrapWitness.lean` (`atomic_rmw` at address 0 traps `heap_oob`) |
| F3 | done: `FV/Backend/Proof/IselMemTrap.lean` (`AtomicLowered`, `loopTrap?`, `atomic_rules_filter`, `atomicLowered_runTerm`: the `lower` call on an `atomic_rmw`/`atomic_cas` emits its single LL/SC loop with the CLIF address vreg and flags), `FV/Backend/Proof/LowerSimMemTrap.lean` (`VMemTrapFrom`, `RunPremM`, `stmt_memtrap`, `reach_match`, `driver_memtrap`: a CLIF trap is an explicit VCode trap or the run reaches the trapping atomic's loop, code and address kept). Design change: no `csemF`; the VCode semantics is unchanged and the memory trap is an observable (`VMemTrapFrom`) refined to the Arm state at the loop's `ldaxr` |
| F4–F7 (weak chain) | done: the per-function conclusion on the existing total-memory machine, no `MapRel` premise (parent's decision 2026-10-22). `FV/E2E/RegLevelMemTrap.lean` (`TrapAtM`, `haltLoop`, `loop_ldaxr`, `regLevel_memtrap_world_value`, `trapAtF_of_trapAtM`), `FV/Backend/Proof/PrepareMemTrap.lean` (`memTraps_prune`, `memTraps_prep`), `FV/E2E/WorldMemTrap.lean` (`backend_correct_worldX_cleanup_memtrap`), `FV/E2E/LinkMemTrap.lean` (`RunGoodLB`, `backend_correct_program_memtrap_{core,budget,peak}`), `FV/E2E/DeadCleanupExecMemTrap.lean` (`ExecTrapM`, `act_simNB`, `binary_correct_exec_memtrap{,_peak}`), `FV/Link/DeadCleanupExeMemTrap.lean` (`compileExe_correct_memtrap{,_peak}`, `compileExe_correct_source_memtrap{,_peak}`), `FV/Front/RawExeMemTrap.lean` (`bundle_correct_{source,raw}_memtrap{,_peak}`), witness `FV/Link/DeadCleanupExeMemTrapWitness.lean` (`atomic_cas` at address 0 under `nullMap`). **Claim**: if the run reaches the trapping atomic, its `ldaxr` faults under the map; it does not say that no earlier access faulted. Only traps of the entry function's own atomics (callees return; `TrapsExplicitM` of the linked environment). docs/contracts/e2e.md "Memory traps of trapping atomics" |
| F8 | open: the `MapRel`-based variants on `stepF` (a per-state invariant: every earlier access of the run touches only mapped memory), as new theorem variants |

## Where we are

* **`Clif.run`** (`FV/Clif/Mem.lean` `checkAccess`, `FV/Clif/Run.lean`): an access whose bytes are
  not inside one live allocation traps with the flags' trap code (default `heap_oob`) and is
  `stuck` if the access is `notrap`; a misaligned `aligned` access, a misaligned atomic and a store
  into read-only data are `stuck`. This is the Cranelift interpreter's behaviour
  (`cranelift/interpreter/src/step.rs` `memerror_to_trap`: out of bounds traps with the flags'
  code; `notrap` "should not trap").
* **The Arm model** (`FV/Arm`): memory is total (`read_mem`/`write_mem` never fail). The only
  `StateError.Fault` is the SP-alignment check of loads/stores with base `sp`.
* **The theorems.** Returning runs need no premise about memory traps
  (`memTrapFree_of_returned`). Trapping runs take two:
  * `TrapsExplicit.stmt`/`TrapsExplicitC.stmt` (`FV/E2E/Statement.lean:268-277`,
    `FV/E2E/TrapCallClifRun.lean:124-128`): only an explicitly trapping instruction traps
    (`explicitTrapInst`: `div`), so no load, store or atomic traps. Used by the isel contract
    (`LowerInstOk.run`, `.trap c` clause, `FV/Backend/Proof/IselContract.lean:745-751`) and by every
    layer above.
  * `Opt.Legal.NoMemTrap` (`FV/Opt/Proof/LegalSim.lean:1736-1742`): no reachable source state
    traps at a load or store (the i128 legalisation splits accesses). It appears in the trap
    halves of `Front.bundle_correct_raw{,_peak}` (`FV/Front/RawExe.lean:59-62,100-103`) and the
    `compileExe_correct_source*` theorems.
* **The trap tables already hold the memory sites.** The emitter attaches the access's trap
  code to every load/store/`ldar`/`stlr`/`ldaxr`/`stlxr` line (`FV/Backend/Asm.lean:312-341,
  374-377,436-437,472-475`), and `FnAsm.layout_traps` (`FV/Backend/Proof/EncodeLayout.lean`)
  proves the table lists exactly the lines with a code. This mirrors Cranelift
  (`isa/aarch64/inst/emit.rs`: `sink.add_trap(trap_code)` before each access with a code).
  `E2E.TrapAt` (`FV/E2E/Statement.lean:451-455`) is "at a site of the table with code `c`".
* **What cg_clif emits** (measured on the `*.unopt.clif` dumps of examples/deps, survey and
  fv-demo, 30,844 functions): every `load` (429,339), `store` (26,250), `atomic_load` (36) and
  `atomic_store` (36) is `notrap`; only `atomic_cas` (225) and `atomic_rmw` (213) carry the
  default code `heap_oob`. For Rust programs the memory traps of `Clif.run` are therefore the
  trapping atomics'; an out-of-bounds plain access is `stuck` (undefined behaviour, no claim).

## What Cranelift guarantees

* `MemFlags::notrap` (`cranelift/codegen/src/ir/memflags.rs`): "the memory is accessible", the
  access never traps; otherwise the access *may* trap and, if it does, the embedder reports its
  trap code. Cranelift inserts **no check** for a plain or atomic access: the "trap" is the
  hardware's synchronous Data Abort (Linux: `SIGSEGV`, or `SIGBUS`), and the trap table entry
  (offset, code) lets the embedder's signal handler name it. cranelift-object (cg_clif's object
  writer) does not emit the table (no use of `MachBuffer::traps` in `cranelift/object` or
  `cranelift/module`): in a cg_clif executable a memory trap is a fatal signal at the access.
* Consequently `Clif.run`'s trap is allocation-granular while the hardware's fault is page- and
  permission-granular: an access outside every CLIF allocation but inside mapped memory does
  **not** fault, it reads or writes whatever is there. No compiler that, like Cranelift, emits no
  bounds check can refine an arbitrary `heap_oob` trap. The refinement of a memory trap is
  therefore conditional on the process's memory map: the trapping access touches a byte the
  map forbids. That premise is about the process, outside the compiler (like `OutsideCall`).

## Design

### Arm: a fault-aware step on the precise footprints (F1; no change to `FV/Arm`)

`FV/Concurrency/ArmInstFoot.lean` (T2h) already gives every instruction its precise memory
footprint: `instEvs ai s` (the events of `exec_inst ai` at `s`: address, size, direction) with
`footprint_exec_inst`, and `stepEvs s` with `footprint_stepi`. The fault model uses these events
as the instruction's access set:

* `ArmFault.Perm` (`none | ro | rw`), a **memory map** `MemMap := BitVec 64 → Perm`;
  `MemMap.Allows mp d a`: a read needs `ro`/`rw`, a write `rw`, a barrier event nothing.
* `InstFaults mp ai s`: some byte of an event of `instEvs ai s` is not allowed (decidable);
  `Faults mp s` the same for `stepEvs s`.
* `execF mp ai s := if InstFaults mp ai s then write_err memFault s else exec_inst ai s`,
  `stepF mp s` likewise over `stepi`; `memFault := StateError.Fault "memory fault"` (distinct from
  the SP-alignment `Fault` messages). A synchronous Data Abort is precise: PC, registers and
  memory are those before the instruction (a page-crossing store's partial write is CONSTRAINED
  UNPREDICTABLE in the Arm ARM; no theorem observes memory after a trap). The process then gets
  the signal at that PC, which is what `TrapAt` names.
* Theorems: `execF_of_not`/`stepF_of_not` (no fault: the old step), `stepF_fault` (the fault
  state: error `memFault`, everything else unchanged), `runF_eq_run` (a run without a faulting
  step is `Arm.run`), `faults_of_byte` (an event byte not allowed faults), `not_faults_of_allowed`,
  `faults_anti` (a larger map faults less), `memFault_ne_*` (a fault is not one of the model's other
  errors).
* Not modelled (documented): alignment faults of exclusives on mapped memory (CLIF makes a
  misaligned atomic `stuck`), instruction-fetch faults (the program is separate from memory),
  changes of the map (fixed per run; outside code that remaps is outside the theorems).
* Oracle: a fault co-simulation (`arm-fault-cosim`, `FVTest/Arm/Cosim/Fault*.lean`). Each test
  executes one load/store/pair/exclusive whose access lies around a `PROT_NONE` page and a
  read-only page of the test program (`mprotect` at start-up); a `SIGSEGV`/`SIGBUS` handler dumps
  the signal context like the existing `SIGILL` handler. Compared with `stepF`: fault or not, and
  on a fault the unchanged registers, PC and memory (on no fault the existing comparison).

### CLIF: no semantic change (F2)

`Clif.run` stays as it is (oracle-checked). New, in `FV/Clif/MemTrap.lean`:

* `MemTrapAt env p s c a n d`: the next statement of `s` is a load, store or atomic whose access
  is `[a, a + n)` in direction `d`, and `step` traps with `c` because `¬ s.mem.valid a n`;
  `trapped_cases`: a trapping statement is an explicitly trapping one, a call whose callee traps,
  or `MemTrapAt`.
* `TrapsExplicitM` (and `TrapsExplicitCM`): `TrapsExplicit`(`C`) with the statement clause
  `explicitTrapInst st.inst ∨ memTrapInst st.inst`; `TrapsExplicit → TrapsExplicitM`.

### Backend layers: a probe semantics (F3–F4)

The precedent is S10e's proof-only probe semantics (`LowerSimURaise.probe`). Every layer from
VCode down is generic in the instruction semantics `ISem`, and `VTrapFrom` already means "the run
reaches an instruction that halts with `trapCode? i = some c`":

* `trapCodeM? i`: `trapCode?` plus the memory instructions' flags code (`load`, `store`,
  `loadAcquire`, `storeRelease`, `fpuLoad`/`fpuStore`, the LL/SC loops).
* `csemF mp` (`FV/Backend/Proof/RegallocCSemF.lean`): `csem`, except that a memory instruction
  whose Arm lines fault under `mp` (`execF`) halts. On a world where nothing faults it is `csem`
  (`csemF_eq`), so the existing realisation proofs carry over line by line; the new case is the
  halting one, realised by the Arm state at the faulting line (`TrapAtF` below).
* Isel (F3): the memory rules' trap case. Under `MapRel mp` (every CLIF-valid byte allowed with
  its permission, the frame `rw`) and `MapFaults mp` (the trapping access has a forbidden byte),
  a CLIF memory trap at `[a, a+n)` makes the lowered instruction sequence halt at its access under
  `csemF mp` with the same code: the address computation is the `.ok` case's (`MemRulesCorrectRT`
  and the atomic rules), the halt is `faults_of_byte`. This adds the `.trap` clause for
  `memTrapInst` to a new contract `LowerInstOkM` (rule proofs registered like Floats' new rules:
  coordinate with the registry owner).
* Allocation, prologue/epilogue, emission (F4): generic in the semantics, instantiated with
  `csemF`; `FnAsm.layout_traps` gives the site.

### The observables and the machines (F5–F6)

* `TrapAtF mp fb base c s`: `TrapAt fb base c s` and the instruction at the site faults under
  `mp` (`InstFaults`). Under `stepF` the next state is the fault.
* Per function: `ExecRefinesF` = `ExecRefines` with `TrapAtF` in the `.trapped` case, on the
  machine whose `realStep` is `execF mp` (`stepFX`); calls and TLS run by the same hooks (the
  hooks get the map unchanged).
* Linked program and executable: `TrapIn` gets the `site` clause with `TrapAtF`; the rest of
  S9c/S9d's induction is unchanged (a faulting activation stops like a `udf` one).

### Premises of the new theorems

* `MapRel mp` (with the run): every byte valid in the CLIF memory of a reachable state is allowed
  (`rw` unless the allocation is read-only), and the stack region the theorem already reserves
  (`OutsideCall.stack`: `stackFn` resp. `frameDrop + D·d`) is `rw`. Then the compiled code's other
  accesses (spills, frame, outgoing arguments, CLIF-valid data) never fault: the old simulation
  runs on `stepFX` unchanged (`runF_eq_run` per step).
* `MapFaults mp` (replaces `NoMemTrap` and the memory part of `TrapsExplicit`): every memory trap
  of the source run, `MemTrapAt … c a n d`, has a byte of `[a, a+n)` that `mp` does not allow in
  direction `d`. Discharged e.g. by the null page: Linux maps nothing below `vm.mmap_min_addr`
  (at least one page; 65536 on common distributions), and `Clif.Mem.next` starts at 65536, so an
  access to address 0 is both a CLIF trap and a fault (the witnesses use it).
* Legalisation: legalised i128 accesses are split; `NoMemTrap` stays for the i128-typed accesses
  only (`NoMemTrap128`, F7): cg_clif emits no trapping i128 access, so the premise is vacuous on
  the measured corpora.

## New theorems (old ones unchanged)

| Slice | Files | Results |
| --- | --- | --- |
| F1 | `FV/ArmFault/{Step,Witness}.lean`, `FVTest/Arm/Cosim/Fault*.lean` | `ArmFault.stepF_of_not`, `stepF_fault`, `runF_eq_run`, `faults_of_byte`; witness: `ldr x0, [x1]` with `x1 = 0` faults, with a mapped `x1` it is `stepi` |
| F2 | `FV/Clif/MemTrap.lean` | `MemTrapAt`, `trapped_cases`, `TrapsExplicitM`, `trapsExplicitM_of`; witness: `atomic_rmw` at address 0 traps `heap_oob` |
| F3 | `FV/Backend/Proof/IselMemTrap*.lean` | `LowerInstOkM` for the memory and atomic rules, `driver_correctM` |
| F4 | `FV/E2E/RegLevelMemTrap.lean`, `FV/E2E/WorldMemTrap.lean` | delivered (weak chain, no `MapRel`, existing machine): `regLevel_memtrap_world_value`, `backend_correct_worldX_cleanup_memtrap` (per function, the world theorem the linked program applies: `TrapsExplicitM`, `MapFaults` ⇒ `TrapAtM`). The planned standalone `backend_correct_final_cleanup_memtrap` (AbiEntry form) is not separate: the linked-program chain uses the world form |
| F5 | `FV/E2E/LinkMemTrap.lean` | delivered: `backend_correct_program_memtrap{_core,_budget,_peak}` (`TrapAtM` and `RunGoodLB`) |
| F6 | `FV/E2E/DeadCleanupExecMemTrap.lean`, `FV/Link/DeadCleanupExeMemTrap.lean` | delivered: `binary_correct_exec_memtrap{,_peak}`, `Link.DeadCleanup.compileExe_correct_memtrap{,_peak}` (`ExecRefinesM`, `ExecTrapM`) |
| F7 | `FV/Link/DeadCleanupExeMemTrap.lean`, `FV/Front/RawExeMemTrap.lean`, witness `FV/Link/DeadCleanupExeMemTrapWitness.lean` | delivered: `compileExe_correct_source_memtrap{,_peak}`, `Front.bundle_correct_{source,raw}_memtrap{,_peak}`: the trap halves with `TrapsExplicitM ∧ MapFaults mp` instead of `TrapsExplicit`; `NoMemTrap` of the source run stays (it forbids load/store traps only; atomic traps are allowed) |
| F8 | open | the `MapRel` variants on `stepF`: no earlier access of the run faults |

## Size [INFERENCE]

| Slice | Size | Notes |
| --- | --- | --- |
| F1 | M (≈600 lines Lean + cosim harness) | built on `ArmInstFoot`; no rebuild of existing modules |
| F2 | S | |
| F3 | L | every memory/atomic rule's trap case (address agreement is the `.ok` proof's), float loads/stores included |
| F4 | L | `csemF` realisation: the new halting case per memory line; the rest by `csemF_eq` |
| F5–F6 | M | S9c/S9d's inductions with `TrapAtF` |
| F7 | M | legalisation with traps restricted to non-i128 accesses |

Overall XL, as the audit estimated; F1–F2 are independent of the rest and land first.

## F8: no earlier access faults (design, 2026-10-22)

F4–F7 (merged, #440) say: if the run reaches the trapping atomic, its `ldaxr` faults under `mp`.
F8 adds, as new variants, that the run on the fault-aware machine gets there: no step before the
trap state faults (`¬ ArmFault.Faults mp` at every earlier state of the activation and of the
activations it calls), so `ArmFault.runF mp` agrees with the run up to the trap state
(`runF_eq_run`) and its next step is the fault. Premise `MapRel mp` (with the run): every byte
valid in the CLIF memory of a reachable state is readable (`ro`/`rw`) and writable unless the
allocation is read-only, the stack region the theorem reserves (`OutsideCall.stack`) is `rw`, the
code words and the GOT slots are readable.

The obligation is a per-step footprint invariant: every access of every line the run executes is
allowed. The accesses split three ways:

1. **CLIF memory instructions** (`load`, `store`, `atomic_*` lines; `MemRefines`): the address is
   the CLIF access's. The existing guarded semantics `csemG`/`valueSemG` (`FV/E2E/Guarded.lean`,
   `FV/E2E/DeadCleanupGuarded.lean`) already restricts the reads of the memory forms to a
   predicate `Rd` (`GuardR`, `MemRefinesR`) and is proven through isel for the D2 read facts. F8a:
   add a write guard `GuardW Wr` (stores, the LL/SC loops' `stlxr`) with `MemRefinesRW`, and
   instantiate `Rd`/`Wr` with `mp`'s permissions; the rules discharge the guards from `MemRel`
   and CLIF validity, `MapRel` turns validity into permission.
2. **Frame accesses** (spills, reloads, prologue/epilogue pairs, outgoing arguments, stack slots):
   inside the activation's frame region `F` (`FrameKeep`, `frameW`), which lies in the reserved
   stack region, `rw` by `MapRel`. F8b: an `RL.AccessOk` per-state fact next to
   `RL.ReadsAt` (D2), proven per realised form like `ReadsAt` (`LinesReads` with reads and writes:
   `ArmInstFoot.instEvs` per emitted line form).
3. **Code and GOT reads** (jump tables, `adrp`/`ldr` GOT pairs): readable by `MapRel`'s code/GOT
   clause.

Then F8c: `RL.GoodX` with `AccessOk` through the linked-program induction (`RunGoodLB`) and the
executable transfer (`StepOk` gets the footprint fact, `Sim` keeps it: same registers, memory
agreeing outside relocated bytes), and F8d: the `_memtrapF` variants on the fault-aware machines
(`ArmFault.stepF` per function; the executable machine with `execF` at its processor steps, hook
steps unchanged). Size [INFERENCE]: F8a M, F8b L (every realised form, the bulk), F8c M, F8d S.

## Related, not in this plan

* **Stack overflow** (`stk_ovf`, DEFERRED "divergence or stack overflow"): with `stepF` a stack
  overflow is a fault at the first access into the guard page; stating it needs the stack-depth
  semantics of that gap.
* Multi-threaded memory (T2): faults are per-thread events of the same footprints; the
  per-thread refinement (T2h) can take `execF` later.
* `SIGBUS`/alignment faults of mapped exclusives; read-only data stores (CLIF: `stuck`, no claim).
