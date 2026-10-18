# T2 (#38): atomics on a multi-core memory model

Today `E2E.backend_correct_final` covers `atomic_load`/`atomic_store`/`atomic_rmw`/`atomic_cas`/`fence`
on a single-core Arm model (`docs/decisions/arm-model.md`, "Atomics"): `ldar`/`stlr` are plain
accesses, an exclusive store always succeeds, `dmb` is a no-op. That is sound for `Clif.run`, which
has one thread, and says nothing about a second core. This plan adds a memory-model-aware statement
next to it. It leaves the existing Arm model semantics and theorems untouched.

## 1. What Cranelift and cg_clif emit (the fragment)

* **Source contract.** Rust's model is C++20's. cg_clif ignores the ordering argument of every
  atomic intrinsic: `atomic_load`/`atomic_store`/`atomic_xchg`/`atomic_cxchg{,weak}`/`atomic_x*`
  become CLIF `atomic_load`/`atomic_store`/`atomic_rmw`/`atomic_cas`, and both `atomic_fence*` and
  `atomic_singlethreadfence*` become `fence` (`rustc_codegen_cranelift/src/intrinsics/mod.rs`,
  `FIXME use a compiler fence once Cranelift supports it`). `i128` atomics are rejected.
* **CLIF semantics.** Cranelift has no formal memory model. Its instruction docs
  (`cranelift/codegen/meta/src/shared/instructions.rs`) say every atomic operation "is sequentially
  consistent and creates happens-before edges that order normal (non-atomic) loads and stores", and
  `fence` keeps "loads [and] stores of any kind" from moving across it. So the CLIF contract is the
  C++20/RC11 model restricted to `seq_cst` atomics, plain (non-atomic) accesses, and `seq_cst` fences.
  cg_clif strengthening Rust's `Relaxed`/`Acquire`/`Release` accesses to this model is sound by
  monotonicity: every behaviour of the stronger accesses is one of the weaker accesses.
* **Arm code** (`has_lse = 0`, cg_clif's flags; `FV/Backend/Asm.lean`, `MInst.lines`):

  | CLIF | Arm (Cranelift `emit.rs`) |
  | --- | --- |
  | `load`/`store` | `ldr*`/`str*` (plain) |
  | `atomic_load` | `ldar{b,h,}` |
  | `atomic_store` | `stlr{b,h,}` |
  | `atomic_rmw` | `l: ldaxr; <alu>; stlxr w24; cbnz w24, l` |
  | `atomic_cas` | `l: ldaxr; cmp; b.ne out; stlxr w24; cbnz w24, l; out:` |
  | `fence` | `dmb ish` |

  Between the `ldaxr` and the `stlxr` of a loop there is no other memory access.

  **LSE (`has_lse = 1`) is not emitted in our configuration**: cg_clif sets `has_lse` only through
  `-Ctarget-cpu` (`native` or a CPU preset; `-Ctarget-feature` is ignored), `cargo fv` passes
  none, and every bundle says `target aarch64 has_lse=0`; the Lean backend implements only the
  non-LSE lowering. With `has_lse` Cranelift emits `ld<op>al` for `atomic_rmw` (all but `nand`,
  `xchg`) and `casal` for `atomic_cas`; their events are an `A` read and an `L` write paired by
  `rmw` (`amo`), the kinds and pairing of a successful LL/SC iteration, so the execution-level
  theorems cover them unchanged (`FV/Concurrency/Lse.lean`, `Lse.lse_maps`).

## 2. The models (decision)

**Executions.** Axiomatic, herd/cat style, in the formulation of the Arm ARM (B2.3) and
Pulte et al., *Simplifying ARM concurrency* (POPL 2018). An execution over an event type `E`:
thread `tid`, direction `R`/`W`/`F`, location `loc`, program order `po`, reads-from `rf`,
coherence `co`, `rmw` (exclusive pair / atomic update); `fr = rf⁻¹;co`; `com = rf ∪ co ∪ fr`.
Well-formedness `Exec.Wf`: `po` a strict order within a thread, total on each thread; `rf` from a
write to a read of the same location, functional and total on reads (initial writes are events);
`co` a strict total order on the writes of each location; `rmw` relates a read to its write, same
thread and location, `po`-adjacent. Locations are abstract (no mixed-size accesses: Rust's atomics
of a type are accessed at that type; a mixed-size model, Flur et al. POPL 2017, is T2i, #317).

**Arm side: the Armv8 axiomatic model, restricted to the fragment.** Event kinds `plainR`, `plainW`,
`acqR` (`ldar`), `relW` (`stlr`), `acqXR` (`ldaxr`), `relXW` (`stlxr`), `dmb` (`dmb ish`, a full
barrier). `A = acqR ∪ acqXR`, `L = relW ∪ relXW`.

* internal: `acyclic(po-loc ∪ rf ∪ co ∪ fr)`;
* atomic: `rmw ∩ (fre; coe) = ∅`;
* external: `acyclic(ob)`, `ob = obs ∪ aob ∪ bob`, `obs = rfe ∪ coe ∪ fre`, `aob = rmw`,
  `bob = po;[dmb];po ∪ [L];po;[A] ∪ [A];po ∪ po;[L]`.

These are clauses of the official `aarch64.cat`; the omitted ones (`dob` dependencies, the
`rfi;[A|Q]` part of `aob`, `po;[L];coi`, `dmb.ld`/`dmb.st`, `Q`, `isb`) only *add* order. This is a
theorem (T2g): `FV/Concurrency/Armv8Full.lean` states the whole model (`Armv8Full.Consistent`,
every clause, over all load/store/barrier kinds and any `addr`/`data`/`ctrl` dependencies), and
`Armv8Full.consistent_frag` shows that an execution of the fragment's kinds consistent for it is
`Armv8.Consistent`. So every theorem of the form "every consistent execution …" proven here holds
for real Armv8 (`Mapping.armv8full_to_clif`, `armv8full_to_clifF`). The cost: tests that rely on
dependencies are allowed here but forbidden by Armv8: `MP+dmb+addr`
(`FVTest/Concurrency/LitmusFull.lean`: `mp_dmb_addr_frag` consistent, `mp_dmb_addr_full` not).

**CLIF side (the Cranelift contract).** Kinds `naR`, `naW`, `scR`, `scW`, `fence`; `At = scR ∪ scW`.
`sw = [scW];rf;[scR]`, `hb = (po ∪ sw)⁺`, `eco = com⁺`.

* coherence: `irreflexive(hb; eco?)` (RC11);
* atomicity: `rmw ∩ (fr; co) = ∅`;
* SC atomics: `acyclic((po ∪ com)|At)`.

A *race* is a pair of distinct conflicting events (same location, one a write, not both atomic)
unordered by `hb`. RC11's `acyclic(po ∪ rf)` (no out-of-thin-air) is deliberately not part of the
contract: Armv8 does not provide it for plain accesses, and a load-buffering cycle through plain
accesses is a race, undefined behaviour in Rust.

**How this composes with the single-thread refinement.** The bridge is DRF-SC: for a program
race-free in every consistent execution, every consistent execution is sequentially consistent,
and an SC execution is an interleaving in which every read sees the latest write to its location
(`Prog.replay`: a run of the multi-threaded machine). Each thread's slice of an interleaving is a
run of that thread against a memory that other threads change between its steps. That is *not*
what `Clif.run` and `E2E.backend_correct_final` describe (a run without interference, and no
statement about the compiled code's intermediate footprint): the per-thread step needs an
event-level refinement with interference, the contract `ProgE2E.Realizes` of §3c (T2h).

## 3. Theorem shape (done: T2a–T2c)

Execution level (`FV/Concurrency/*`, root `FV/Concurrency.lean`; no dependency on the existing
proofs, the Arm model of `FV/Arm` unchanged):

1. `Concurrency.Armv8.atomics_sc` — in an Armv8-consistent execution of the fragment, the acquire
   and release accesses are SC: `acyclic((po ∪ com)|(A ∪ L))`.
2. `Concurrency.Mapping.armv8_to_clif` — **compilation correctness of the mapping** (C11 → Armv8
   style, Lahav et al. PLDI 2017, Podkopaev et al. POPL 2019): if an Arm execution is the image of a
   CLIF execution under the table of §1 and is Armv8-consistent, then the CLIF execution (the Arm
   execution restricted to the source events `S`) is consistent for the Cranelift contract
   (`ClifMM.Consistent`). `Compiled`: each CLIF event's kind maps to its Arm kind (`Maps`) and CLIF
   reads read from CLIF writes (`rf_src`, where the single-thread frame separation enters). The
   other Arm events are unconstrained (failed LL/SC iterations' `ldaxr`s, the code's own GOT,
   jump-table and frame accesses). Per-operation lemmas: `ob_acq`/`ob_rel`/`ob_rel_acq`
   (`ldar`/`ldaxr`, `stlr`/`stlxr`, release-then-acquire), `ob_dmb` (`fence` ↦ `dmb ish` orders
   every pair across it), `hb_shape` (`hb ⊆ po ∪ po?;[L];ob⁺;[A];po?`), `coherence`, `atomicity`
   (the exclusive pair: the atomic axiom, SC per location and `po`-adjacency).
3. `Concurrency.ClifMM.drf_sc` — DRF-SC for an execution: consistent and race-free ⇒
   `acyclic(po ∪ com)`.
4. `Concurrency.Mapping.armv8_drf_sc` — 2 + 3: a race-free CLIF execution compiled to Arm is SC.
5. `Concurrency.Exec.sc_interleaving`, `Concurrency.Mapping.armv8_interleaving` — a finite SC
   execution has a rank (interleaving position) increasing along `po ∪ com` in which every read
   reads the latest same-location write before it, and no same-location write falls between the
   two halves of an `rmw`.

Code level (`FV/Concurrency/Code.lean`): `insnKind` classifies `Backend.Insn` by memory-event
kind. `lines_kinds`: for every `MInst`, the kinds of `MInst.lines`' output are `akinds m`
(`loadAcquire` ↦ `[acqR]`, `storeRelease` ↦ `[relW]`, `atomicRmwLoop`/`atomicCasLoop` ↦
`[acqXR, relXW]`, `fence` ↦ `[dmb]`, the other memory instructions one plain kind, the rest none);
`ordered_only_atomic`: acquire/release/exclusive/barrier kinds come only from those;
`memInsns_rmwLoopLines`/`memInsns_casLoopLines`: the loops' memory instructions are exactly
`ldaxr x27, [x25]` and `stlxr w24, …, [x25]` at the same size (so `po`-adjacent);
`kinds_prologueLines`/`kinds_epilogueLines`/`kinds_relaxLines`: frame code is plain, branch
relaxation keeps the kinds. The CLIF → `MInst` step is `FV/Backend/Proof/IselAtomic.lean`.

Non-vacuity: `Concurrency.Witness.incX_*` (two LL/SC increments with a failed iteration, every
premise of theorems 1–5 kernel-decided) and `mp_*` (message passing with plain data, race-freedom
through release/acquire), `Code.lines_kinds_witness`. Axioms: `scripts/audit/concurrency.lean`
(40 theorems, standard axioms only; the model theorems use none or `Classical.choice` for the
ranks).

## 3b. Thread level (done: T2d)

`FV/Concurrency/ArmThread.lean` (on `FV/Concurrency/ArmFootprint.lean`): one thread of the Arm
model run against a memory it shares. `TStep P f` steps a single-core machine `f` (`Arm.stepi`, or
the E2E machine `ArmStepX X H fa`) with a label of **events** (`Ev`: kind, address, size, bytes):

* a step's events form a **footprint** (`Footprint f s evs`): run on any memory holding the read
  events' bytes, the step writes exactly the write events and leaves the same registers. A read's
  bytes are the environment's choice (the memory model decides which are consistent). The
  semantics is sound by construction; precise footprints are lemmas: non-memory instructions
  have none (`ArmFoot.exec_nonldst`: every non-load/store class commutes with replacing the
  memory, `ArmFoot.stepi_setMem`), `ldar`/`ldxr`/`ldaxr` read and `stlr`/`stxr`/`stlxr` write
  their one access (`footprint_load_excl`, `footprint_store_excl`). Kinds come from the decoded
  instruction (`cls`, `Cls.kind`: `dmb`/`dsb` over all accesses is the full barrier);
* the **exclusive monitor** (`Mon`) is armed by `ldxr`/`ldaxr` and disarmed by `stxr`/`stlxr` and
  `clrex`; a store exclusive succeeds (an `f` step, a write event, `Rs := 0`) when the policy
  allows (`Policy.arm`: monitor armed), or **fails** (`TStep.xfail`: no event, `Rs := 1`), at any
  time under `Policy.arm`.

The single-core model is the special case `Policy.sc` (never fails) against SC memory (`SCRun`:
every read returns the current memory's bytes): `step_sc`, `run_sc`, `run_sc_stepi` (such a run is
`Arm.run`), and conversely `exists_step_sc`/`exists_run_sc` (every run of `f` is one, with
whole-memory footprints). Non-vacuity: `ArmThread.Witness.retry_run`, Cranelift's `atomic_rmw`
loop as emitted (`ldaxr x27, [x25]; add; stlxr w24, x28, [x25]; cbnz w24`) reads `5` (an
`acqXR` event, monitor armed), its `stlxr` fails and `cbnz` branches back to the `ldaxr`;
`retry_succ` is the successful `stlxr` (a `relXW` event of the sum). `no_xfail_sc`: the
single-core monitor never fails.

## 3c. Program level (done: T2e; contract open: T2h)

**Why `backend_correct_final` does not compose per thread** (both findings matter to anyone
extending the E2E theorems to threads):

1. *No interference.* It is a whole-run theorem: `Clif.runLoop` reads its own memory, and an
   extern call's result is a function of its arguments and the memory (`Clif.Env.extern`). Other
   threads' writes between a thread's steps (an atomic load in a spin loop, message passing) are
   not expressible, neither on the CLIF nor on the Arm side (`ArmStepX`, hooks only at calls).
2. *No footprint.* It says nothing about the memory the compiled code touches before it returns
   (only the final `MemAgree`), so even threads that never communicate cannot be composed: a
   transient write to another thread's data is not excluded.

So the program-level statement takes the per-thread *event-level* refinement as an explicit
contract, and discharging it needs the backend layers re-proven with interference (T2h, #311).

**Files.** `FV/Concurrency/Program.lean`: thread semantics `TSem` with memory events, the
interleaving machine `MStep`/`MRun` over a memory interface `MemI`, executions of programs
(`Traces.exec`: initial writes `init q` and positions `thr i j k`), `drf_sc_init` (DRF-SC with
initial writes, which race with nothing), `sc_of_rank_on`. `FV/Concurrency/Replay.lean`: **replay**
— a finite SC execution (reads read their writes' values, no partially overlapping accesses,
steps are single events or atomic updates, initial writes `co`-first) is a run of the interleaving
machine whose final memory holds the `co`-last writes (greedy on the *step rank*, the largest
interleaving rank of a thread's events so far). `FV/Concurrency/ClifThread.lean`: the
**multi-threaded `Clif.run`** `MTStep`/`MTRun` (threads share the bytes; allocation metadata is
per thread; extern calls that touch memory have no step; `tls_value` is the image's instance), the
CLIF thread event semantics `CStep` (events by statement: `naR`/`naW`/`scR`/`scW`/`fence`, sizes
fixed, so the footprint pins the addresses), `mrun_mt`. `FV/Concurrency/ProgramE2E.lean`:

* `ATStep`: the Arm threads (`ArmThread.TStep` of each thread's machine under `Policy.arm`);
* `RaceFreeProg`: every execution of the CLIF program consistent for the Cranelift contract is
  race-free. **This is the C++20/Rust definition of a program without undefined behaviour** (a
  data race in any consistent execution is UB), so no prefix argument is needed — which would fail
  here anyway: neither the contract nor the Arm fragment excludes load-buffering cycles through
  plain accesses (no `dob`, no `acyclic(po ∪ rf)`, §2);
* `Realizes` (**the contract**): the CLIF traces embed into the Arm traces (`φ` preserving program
  order, thread, direction, location, size, value, initial writes; kinds by `Maps`); CLIF reads read
  from CLIF writes (frame separation); atomic updates are `rmw`-paired; outcomes related by `Obs`;
* `program_correct`: Armv8-consistent Arm execution + `Realizes` + `RaceFreeProg` ⇒ the CLIF
  execution is SC (`wfC`, `consistentC` = theorem 2 along `φ`, `drf_sc_init`), and the
  multi-threaded `Clif.run` reaches the CLIF threads' final states with the `co`-last values in
  memory and the outcomes `Obs`.

Non-vacuity (`FV/Concurrency/ProgramWitness.lean`): `mp_replay` (message passing replayed, final
`x = y = 1`), `ret_correct` (`program_correct` for two returning threads, race-freedom proven
over all executions of the program, `ret_raceFree`).

## 3d. Rust orderings and cg_clif's strengthening (done: T2f)

`FV/Concurrency/RC11.lean`: RC11 (Lahav et al. PLDI 2017; C++20's model after P0668) with every
ordering (`RKind`: plain, `R o`/`W o`/`F o` for `o ∈ rlx/acq/rel/acqrel/sc`): release sequences,
`sw` through release/acquire accesses and fences, `hb`, coherence, atomicity, `psc`
(`psc_base ∪ psc_F`), no-thin-air (`Consistent`; `ConsistentNoNTA` is C++20). The contract of §2
gives `fence` no meaning, which is too weak for the strengthening: store buffering with SC fences
and plain accesses is contract-consistent but RC11-inconsistent (`Witness.sbf_contract`,
`sbf_not_rc11`). `ClifMM.ConsistentF` adds Cranelift's documented semantics (every atomic and fence
SC: RC11's `psc` with all of them `seq_cst`).

* `RC11.hb_strength`: RC11's `hb` is in the contract's `hb` of the strengthened kinds;
* `RC11.strength_sound`: a `ConsistentF` execution of the strengthened program is RC11-consistent
  without no-thin-air for the original orderings (every behaviour of the CLIF program is one of
  the Rust program); `RC11.raceFree_strength`: RC11 race-freedom gives the contract's;
* `RC11.strength_sound_drf`: for race-free executions the plain contract suffices (DRF-SC gives
  even RC11 with no-thin-air);
* `Mapping.armv8_to_clifF` (`FV/Concurrency/ArmFence.lean`): Armv8-consistent compiled executions
  satisfy `ConsistentF` (`fence` ↦ `dmb ish`): `R = ob ∪ [dmb];po ∪ po;[dmb]` is acyclic
  (`Armv8.R_acyclic`) and every `psc` edge is an `R⁺` path (`Mapping.Hom.psc_R`, for any map
  `Hom` preserving `rf`/`co` and `po` between the events `V` that matter: accesses, atomics and
  fences; positions without events are bypassed, `Mapping.plus_restr`).

Witnesses (`FV/Concurrency/RC11Witness.lean`): `sbf_*`; `mpf_*` (message passing through
`fence(Release)`/`fence(Acquire)` and relaxed atomics, compiled to `str; dmb; stlr ‖ ldar; dmb;
ldr`: `ConsistentF`, RC11-consistent with the weak orderings, RC11- and contract-race-free);
`incX_consistentF`.

**Program level** (`FV/Concurrency/ProgramE2EF.lean`):

* `consistentCF`: the CLIF execution of `program_correct` satisfies `ConsistentF` (`Hom` along
  `φ` on the CLIF events; `φ` need not preserve program order on positions without events, which
  is impossible in general: a CLIF step can compile to no instruction, so a CLIF thread can have
  more event-free steps between two events than its Arm code);
* `RaceFreeProgF`: race-freedom in every `ConsistentF` execution whose `rmw` pairs exactly the
  two-event steps (`StepShape`; `rmw_sc`: those are `atomic_rmw`/`atomic_cas` reads and writes);
* `program_correctF`: `program_correct` with `RaceFreeProgF` (weaker than `RaceFreeProg`,
  `raceFreeProgF_of_raceFreeProg`);
* `RustRaceFree` (the Rust program, orderings `ord` that cg_clif strengthens to the CLIF kinds, is
  race-free in every C++20-consistent execution) implies `RaceFreeProgF`
  (`raceFreeProgF_of_rust`), and `program_correct_rust` is the composition: **from Rust
  race-freedom to the multi-threaded `Clif.run`, under the per-thread contract `Realizes`**.

Witnesses (`FV/Concurrency/ProgramFWitness.lean`): `ret_correctF`, `ret_rustRaceFree`,
`ret_correct_rust` (the two returning threads of `ret_correct`).

## 3e. Discharging `Realizes` (T2h, #311): plan, layers 0 and 1 done

`Realizes` (§3c) is a property of a whole execution. It splits per thread into one obligation,
which each backend layer proves *with interference*, plus a composition. The approach is
CASCompCert's (Jiang et al., PLDI 2019), specialised to event traces: footprint-preserving
simulations under a rely (other threads write shared locations between steps) and a guarantee
(a thread writes only shared locations through source-level events, and private locations
otherwise). The single-threaded theorems (`E2E.backend_correct_final` and its layers) stay as
they are; the per-thread layers are new files.

* **Layer 0: reduction and composition (done, `FV/Concurrency/ThreadRefine.lean`).**
  `ThreadRefine.Refines MK Priv pairT trS trT ψ` is the per-thread obligation. The target trace
  `trT` is any run of the thread against shared memory, so its reads return arbitrary values:
  interference is in the statement. It realizes the source run `trS` through a position map `ψ`
  that is strictly increasing on source events:
  * same direction, location, size and value, with kinds related by `MK`;
  * the footprint guarantee: source events never access `Priv`, and target writes outside the
    image write `Priv` (frame, spills, saved registers); target reads outside the image (a failed
    LL/SC iteration's `ldaxr`) may read anything;
  * atomic updates map to the target's atomic pairs `pairT`, and back.

  `realizes_of_threads` assembles the threads' refinements and outcomes into `Realizes`, given
  that:
  * the Arm execution's `rmw` are the threads' pairs;
  * the CLIF initial locations are a prefix of the Arm ones, the rest private, with the same
    initial values.

  `Refines.trans` composes layers through an intermediate level whose atomic updates are its
  two-event steps (`StepPair`; kinds compose, private sets unite). Witnesses
  (`FV/Concurrency/ThreadRefineWitness.lean`):
  * `ret_threads`, `ret_correct_threads`: `program_correct` with `Realizes` *derived*;
  * `refines_spill`: an atomic load realized by a private spill and an `ldar`;
  * `refines_trans_spill`.
* **Layer 1: event semantics of VCode (done, `FV/Concurrency/ArmInstFoot.lean`,
  `FV/Concurrency/VCodeThread.lean`).**
  * Every Arm instruction has a precise footprint, as a function of the state
    (`ArmInstFoot.instEvs`, `footprint_exec_inst`; for `stepi`: `stepEvs`, `footprint_stepi`, with
    the kinds of `ArmThread.KindsOk`, `kindsOk_stepEvs`). The T2d footprints covered only
    `ldar`/`ldaxr`/`stlr`/`stlxr`; now every load/store class has its access (single register,
    pair, literal, exclusive).
  * Footprints of multi-instruction steps use sequential agreement (`SAgrees`: a read sees the
    step's earlier writes) and compose (`ofoot_seq`, `ofoot_execLines`).
  * `csem`'s precise footprint `cEvs` (the canonical run's events, the LL/SC loop body's, none for
    the control forms); `ifoot_csem`: every instruction but calls has it.
  * `VTStep vc sem ev`: the VCode thread step on the world patched with the read events' bytes,
    whose events are the instruction's precise footprint (`ev`). **Precision matters**: with
    arbitrary footprints (any `evs` satisfying `Footprint`, as `ArmThread.TStep` allows) a step
    could carry a read and a write-back of a location it does not touch, a write to a shared
    location that no layer can account for. The Arm traces of the final theorem need the same
    restriction (labels equal to `stepEvs` of the patched state).
  * Witnesses (`VCodeThreadWitness.lean`): `ldar_vtstep` (an `ldar` reading the environment's `5`
    while its own memory holds `0`), `cEvs_ldar`, `stepEvs_ldaxr`.
* **Layer 2: isel with interference.** The per-statement simulation of the M7 driver (the step
  lemmas behind `IselSim`) as `Refines` from `ClifThread.CStep` to the VCode event semantics. A
  CLIF memory statement lowers to one memory `MInst` with the same event. The memory relation
  `MemRel` must be stable under the rely: both sides receive the same writes at shared locations,
  and `MemRel` is the identity there.
* **Layer 3: `prepare`.** Block reordering and edge splitting: the traces are equal up to inserted
  jumps, which have no events, so `ψ` only shifts step indices.
* **Layer 4: register level.** `RegLevelCorrect` as `Refines` from VCode to `ATStep`:
  * kinds by `MInst.lines` (`Code.lines_kinds`);
  * frame, spill and prologue accesses in `F s` (= `Priv`; the stack is per thread);
  * atomic loops: failed iterations are extra reads, and the successful `ldaxr`/`stlxr` pair is
    the monitor pair `pairT`.
* **Backward from forward.** The layers are forward per-step simulations; `Refines` is
  backward (from the actual Arm trace to a CLIF run). The bridge is determinism of each level
  given its read values (receptiveness): the source run is the one reading the target's values.
* **Widening** (§3c): extern calls that touch memory, per-thread allocation metadata,
  `tls_value`.

**#38 stays open until layers 1–4 discharge `Realizes`.** Until then `program_correct*` compose
the memory-model layer with the per-thread contract, and the single-core assumption stays in
the trusted base of `E2E.backend_correct_final`.

## 4. Testing (the oracle)

qemu is not weak-memory faithful (TCG on an x86 host is close to TSO), so it cannot show that a
relaxed outcome is possible; herd7's `aarch64.cat` verdicts are the oracle.

* `FVTest/Concurrency/Litmus.lean`: MP, MP+rel, MP+rel+acq, MP+dmbs, SB, SB+rel+acq, SB+dmbs, LB,
  LB+acq+rel, 2+2W, 2+2W+rels, IRIW, IRIW+acqs, CoRR and two LL/SC increments, on the emitted
  instructions, with herd7's Armv8 verdict for each: 10 forbidden outcomes proven inconsistent, 7
  allowed ones proven consistent (each candidate execution is well-formed). The model and herd7
  agree on all of them; they differ only on dependency tests (§2), which the table lists.
* `scripts/litmus-qemu.sh [iterations]` (`tools/litmus/litmus.rs`): the same tests plus Cranelift's
  `atomic_cas` loop, as `asm!` threads in an aarch64 musl binary under `qemu-aarch64-static`;
  every observed outcome must be allowed (observed ⊆ allowed; exit 1 otherwise). This checks the
  model is not too strong.

## 5. Sub-issues

| Id | Item | State |
| --- | --- | --- |
| T2a (#299) | Execution graphs, the Armv8 fragment, the Cranelift contract, theorems 1–5 (`FV/Concurrency/*`) | **done** |
| T2b (#300) | Code-level classification of `Backend.Insn`/`MInst.lines` (`FV/Concurrency/Code.lean`) | **done** |
| T2c (#301) | Litmus tests in Lean + qemu harness | **done** |
| T2d (#302) | Per-thread event semantics of the Arm model: the run of one thread as a trace of memory events with an exclusive monitor (failing `stlxr`, the `cbnz` retry); the existing single-core model is that semantics against an SC memory with a monitor that never fails | **done** |
| T2e (#303) | Program level: multi-threaded `Clif.run` (`ClifThread.MTRun`), program-level DRF-SC (race-freedom in every contract-consistent execution, initial writes `co`-first), replay of SC executions as interleaving runs, and the program-level statement `ProgE2E.program_correct` with the per-thread contract `Realizes` (§3c) | **done** |
| T2h (#311) | Discharge `Realizes`: the per-thread event-level refinement of compiled code (isel/prepare/register-level layers re-proven as footprint-preserving simulations with interference; §3e) | layer 0 **done** (`ThreadRefine`: reduction `realizes_of_threads`, composition `Refines.trans`); layer 1 **done** (precise footprints `ArmInstFoot`, VCode thread semantics `VCodeThread.VTStep`); layers 2–4 open |
| T2f (#304) | Rust/C++20 (RC11 with all orderings) → the Cranelift contract: cg_clif's ordering strengthening as a theorem (§3d), and the program-level chain `program_correct_rust` | **done** |
| T2g (#305) | Widening: LSE atomics (`has_lse`: not emitted in our configuration, covered by the table, `Lse.lse_maps`), the full `aarch64.cat` (`Armv8Full`, monotonicity `consistent_frag`), `i128` atomics (rejected by cg_clif) | **done** |
| T2i (#317) | Mixed-size accesses (a mixed-size model instead of `NoOverlap`) | open |

The existing single-core assumption stays in the trusted base of `E2E.backend_correct_final`, and
#38 stays open, until T2h is done (§3c: T2e composes the memory-model layer with an explicit
per-thread contract that `backend_correct_final` does not imply). T2a–T2c replace "a multi-core memory model is a project of its own" by a proven
mapping at the execution level: every Armv8 execution of Cranelift's atomics code is consistent
for the Cranelift contract, and SC (an interleaving) when the program is race-free.
