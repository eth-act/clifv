# A3 (#412): memory-access faults under the theorems

Plan of 2026-10-22, base main 729900af. Branch prefix `agent/memfault`. Gap A3/B2 of the gap
audit (the trap theorems assume the source run's `NoMemTrap`). One PR per slice; old theorems
keep their premises, new results get new names, every new top-level theorem a witness.

## Status

| Slice | State |
| --- | --- |
| F0 | this plan |
| F1 | done: `FV/ArmFault/Step.lean` (`stepF`, `runF_eq_run`, `runF_fault`, …), witnesses `FV/ArmFault/Witness.lean`, `scripts/arm-fault-cosim.sh` 152 forms, 30 400 vectors (20 577 faults), 0 failures (`docs/contracts/arm.md`, "Memory faults") |
| F2–F7 | open (below) |

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
| F4 | `FV/Backend/Proof/RegallocCSemF.lean`, `FV/E2E/RegLevelF*.lean` | `realizes_allF`, `backend_correct_final_cleanup_memtrap` (per function: `TrapsExplicitM`, `MapRel`, `MapFaults` ⇒ `ExecRefinesF`) |
| F5 | `FV/E2E/LinkTrapCallF*.lean` | `backend_correct_program_memtrap{,_budget,_peak}` (`TrapInF`) |
| F6 | `FV/E2E/DeadCleanupExecTrapF.lean`, `FV/Link/DeadCleanupExeTrapF.lean` | `Link.DeadCleanup.compileExe_correct_memtrap{,_peak}` |
| F7 | `FV/Link/DeadCleanupExeSourceF.lean`, `FV/Front/RawExeMemTrap.lean` | `compileExe_correct_source_memtrap{,_peak}`, `Front.bundle_correct_raw_memtrap{,_peak}`: the trap halves with `MapRel`/`MapFaults`/`NoMemTrap128` instead of `NoMemTrap` and the memory part of `TrapsExplicit` |

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

## Related, not in this plan

* **Stack overflow** (`stk_ovf`, DEFERRED "divergence or stack overflow"): with `stepF` a stack
  overflow is a fault at the first access into the guard page; stating it needs the stack-depth
  semantics of that gap.
* Multi-threaded memory (T2): faults are per-thread events of the same footprints; the
  per-thread refinement (T2h) can take `execF` later.
* `SIGBUS`/alignment faults of mapped exclusives; read-only data stores (CLIF: `stuck`, no claim).
