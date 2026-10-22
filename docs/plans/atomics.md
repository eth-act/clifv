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

## 3e. Discharging `Realizes` (T2h, #311): plan, layers 0, 1, 3 and 4a done

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
    LL/SC iteration's `ldaxr`) may read anything. **Barriers are exempt** (`Refines.shared`:
    only events with direction other than `.F`): a barrier accesses no memory (the Arm `dmb`
    event `ArmInstFoot.dmbEv` has address 0, size 0 and no bytes), so it cannot touch private
    data, and no layer needs to keep address 0 out of the private set (the layer-4b private set
    is the frame `R.F`, which may contain it). `realizes_of_threads` uses `shared` only for
    reads (and `PrivCoh.ownWrites_of_refines` only at writes), which are never barriers;
    `Refines.trans` and `Img`/`RefA` (layer 4b) carry the same exemption;
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
* **Layer 1b: event kinds of VCode (done, `FV/Concurrency/VCodeEvents.lean`).**
  * `instEvs_kinds`: an emitted `Insn`'s events have its kind `Code.insnKind` (at most one; none
    without memory kind, `instEvs_none`), through the encoder's fields (`aiKind_armFields`).
  * `linesEvs_kinds`, `straightEvs_kinds`, **`cEvs_kinds`**: a VCode instruction's event kinds
    under `csem` are a sublist of its table entry `Code.akinds` (the LL/SC loops' body
    `[acqXR, relXW]`, a failed `atomic_cas` comparison only `acqXR`); `cEvs_nil`: no events
    without memory kinds; `akinds_assign`: allocation keeps the kinds.
* **Precise Arm labels (finding 1; done, `FV/Concurrency/ArmPrecise.lean`).** `Precise s l`: the
  label is `stepEvs` on `s` with some memory (or a failing store exclusive); `ATStepP`:
  `ATStep` with precise labels (a restriction: `runs_of_P`, so `program_correct*` apply).
  `instEvs_setMem`/`stepEvs_setMem`: the footprint on another memory is the same accesses with
  that memory's bytes (`reread`); `exists_precise_step`: precise steps are receptive (every
  memory the environment provides has its step).
* **Private coherence (finding 2; done, `FV/Concurrency/PrivCoh.lean`).** The prologue's
  `stp`/epilogue's `ldp` of fp/lr and spill reloads read the thread's stack; in an arbitrary
  trace these reads return anything. `PrivCoh Priv init tr`: every read of `Priv` reads the
  latest earlier write of the trace there (or `init`). `privCoh_of_consistent`: in a
  well-formed execution that is SC per location (Armv8's `internal`), with `co`-first initial
  writes, reads reading their writes' values and no partial overlap, **if only thread `i` writes
  `Priv i`, thread `i`'s trace is `PrivCoh (Priv i)`**. `realizes_of_threads_priv`: the reduction
  with one private set per thread.

  **Explicit program-level premise: no thread writes another thread's private set.** It is a
  hypothesis of `privCoh_of_consistent`/`realizes_of_threads_priv`, not a theorem, for two
  reasons. (1) Deriving it from the per-thread refinements is circular: thread `i`'s guarantee
  (`ownWrites_of_refines`: it writes only `Priv i` and its source events' locations) holds only
  if its reads of `Priv i` are coherent, and that coherence needs every other thread's guarantee
  first. (2) There is no order to break the circle by induction: the fragment allows load
  buffering through plain accesses (no dependency ordering, §2), so a consistent execution need
  not have a prefix in which all threads behaved. It is a property of the program (its stacks
  are disjoint and nobody else writes them), as in CASCompCert's rely/guarantee premise.
* **Layer 2: isel with interference (done from a match: `IselRefines.isel_refines`).** The per-statement simulation of the M7
  driver (`LowerSim.stmt_step`, behind `IselSim`) as `Refines` from `ClifThread.CStep` to the
  VCode event semantics. `stmt_step` does not reveal which addresses the VCode segment accesses
  (finding 3). Two ways to recover them:
  1. *Per-statement frame.* Instantiate the driver per statement with the frame set `F_t` = every
     address outside the CLIF event's bytes and the CLIF memory restricted to those bytes; 2a
     then places every VCode event in the event's bytes. This needs `LowerInstOk` for
     `csem F_t` and a memory relation whose valid bytes are the event's, i.e. the whole M4
     contract (`instCalls_of_rules`: `CallsRefine`, `OutArgsOk`, … at `F_t`) re-established per
     statement.
  2. *By variation (chosen).* Keep the function's `F` and `stmt_step` as they are. Changing one
     valid CLIF byte on both sides keeps the match (`MemRelOk.store`). A byte of the CLIF access
     that no VCode event covers changes the CLIF result (a loaded value, or the byte a store
     leaves) but not the VCode one (the segment's footprint), so it contradicts the match after
     the step: the CLIF access lies within the VCode event, and with equal sizes it *is* the
     event (address, size, bytes).

  The steps of 2:
  * **2b (segment as a forward run; done, `FV/Concurrency/SegRun.lean`):** `vtrun_patch`: a
    thread run of steps without events, one step with events `evs` and steps without events
    (a statement's segment) is the forward `VStep` run from the start patched once with `evs`'
    read bytes (`patchC`): instructions without events neither read nor change the memory
    (`vstep_setMem`). So `stmt_step`, run from the patched state, describes the thread's
    segment. Witness: `ldar_patch`.
  * **2c (segment shape, translation validation; done, `FV/Concurrency/SegShape.lean`):**
    semantics cannot exclude an extra memory instruction that writes a location back with its
    old value (every state is unchanged, but the trace has an extra, racy event), so the
    number, kinds and sizes of each statement's memory instructions are checked on the
    lowering. `segShape inst seg`: the instructions with memory kinds (`memInsts`, by
    `Code.akinds`) are exactly one of the kinds of `inst`'s events under `Maps` (`load` →
    `[plainR]`, `store` → `[plainW]`, `atomic_load` → `ldar` `[acqR]`, `atomic_store` → `stlr`
    `[relW]`, `atomic_rmw`/`atomic_cas` → the LL/SC loop `[acqXR, relXW]`, `fence` → `dmb`) and of
    its access size (`memBytes`); every other statement's code has none. **`segShapeCheck f`**
    runs it on every statement's `lower` output of the driver's lowering (`buildCtx`,
    `lowBlocks`, as `lowerCheckT` computes it); **`segShape_segT`**: it then holds on the code
    the validated VCode contains for the statement (`segT`; renaming keeps kinds and sizes, the
    result copies are moves). Witness (`SegShapeWitness.lean`, `native_decide`):
    `atomics_segShape`, a function with `atomic_load`, `atomic_store`, `atomic_rmw`,
    `atomic_cas`, `fence`, `load` and `store`. Entry code (`preT`) and terminator code (`tseg`)
    are not checked yet (their memory instructions are reads: incoming stack arguments, jump
    tables).
  * **2d (addresses by variation; done, `FV/Concurrency/IselVary.lean`, `IselFoot.lean`,
    `IselClif.lean`):** `store_touched`/`load_touched`: from `LowerInstOk` and `MemRelOk`, no
    byte of a store's or a load-like statement's CLIF access is `Untouched` by its code's
    `seqRun`. **`untouched_of_runOut`** (the footprint lemma): a byte outside every event of a
    run whose instructions step with precise footprints (`RunOut`: `IFoot` at each instruction
    reached) is `Untouched` — changing it keeps the events' agreement and commutes with their
    writes (`sagrees_out`, `applyW_out`, `ifoot_out`); hence `store_in_events`/
    `load_in_events`. The CLIF facts (`StoreFacts`/`LoadFacts`: the outcome on every memory
    with the same allocations, and a load's first result determining its bytes) follow from one
    successful run for `load`, `store`, `atomic_load`, `atomic_store`, `atomic_rmw` and
    `atomic_cas` (`*_facts`; loads little-endian, `readBits_inj`; an `atomic_cas` not on
    read-only data, since its store would be stuck where the comparison succeeds).
    **`access_in_events`**: every byte of a memory statement's CLIF access (`access`: effective
    address and size, the location and size of its `CStep` events) lies in an event of the run
    of its lowered code. Witnesses (`IselClifWitness.lean`): `untouched_ldar` (the `ldar` at
    `0x8000` under `csem`), `atomicLoad_facts0`, `store_facts0`. Open: `access_in_events` on a
    statement of a compiled function (its `LowerInstOk` from `instCalls_of_rules`, `RunOut`
    from `ifoot_csem` along the run), part of 2e.
    *From touched to the covering event (`IselCover.lean`):* `cover_of_not_runOut`: under
    `RunFoot` (every instruction the run reaches steps with footprint `ev`), a byte that is not
    outside every event lies in an event of an instruction the run reaches (`RunAt`);
    `addr_eq_of_cover`: an `n`-byte event covering every byte of `[a, a + n)` (no wrap-around,
    `MemRelOk.valid`) starts at `a`. Witnesses (`IselCoverWitness.lean`): `cover_ldar` (no
    footprint of the `ldar` avoids `0x8000`: with that byte changed it loads `5`, not `0`),
    `addr_eq_cover8`.
    *Event sizes (`VCodeSize.lean`):* `cEvs_size`: the footprint `cEvs` of a successful `csem`
    step of a memory instruction is one access of its size `SegShape.memBytes` (straight-line
    forms at `AMode.addr`/x0, the LL/SC loops at x25; `straightEvs_size`); `addr_eq_of_oneAcc`:
    such events covering every byte of `[a, a + n)` are at `a`. Witnesses
    (`VCodeSizeWitness.lean`): `ldar_oneAcc`, `ldar_at`.
  * **2e (assembly; done from a match):** the CLIF run reading the bytes the VCode run read
    (receptiveness of `CStep`), `ψ` mapping each CLIF event to its segment's memory event,
    `Refines` with `Priv` = the frame (the segment's other writes: outgoing call arguments).
    * *CLIF thread steps (done, `FV/Concurrency/ClifCStep.lean`):* `cstep_of_eval` (a statement
      whose outcome on every byte memory agreeing with its read events is the same values and
      memory with its write events applied is a `CStep`), and from one successful `Clif.step`
      the `CStep` of `load` (`naR` read of its access), `store` (`naW` write of the value's bytes
      `valB`), `atomic_load`/`atomic_store` (`scR`/`scW`), `atomic_rmw` (read, write of the new
      value), `atomic_cas` (read, and the write when the comparison succeeds) and `fence`.
      Witnesses (`ClifCStepWitness.lean`): `cstep_atomicLoad0`, `cstep_store0`,
      `cstep_atomicCas0`.
    * *Assembly pieces (done):* footprint premises along the run (`SegFoot.csem_keep`,
      `runFoot_csem`); `VStep` determinism and counted driver matches exposing the segment's
      endpoint (`IselStep.vstep_det`, `vtrun_patchN`, `stmt_matchN`, `term_matchN`); a thread
      walking a stretch without events (`IselSeg.vtrun_walk`, `vtrun_follow`); the match after
      patching both memories (`IselSeg.mr_patch`, `mr_own`); the static per-statement check
      (`IselCheck.threadCheck`, `obligations_of_threadCheck`); CLIF steps without events
      (`ClifCStepTerm.cstep_pure`, `cstep_term`, `done_of_step`); traces to `Refines`
      (`CorrRefine.refines_of_corr`); the induction (`IselThread.simRes_of_seg`, `pure_seg`,
      `term_seg`); the memory instruction's events are the CLIF access
      (`IselVar.events_at_access`, with `CEvsInv.cEvs_mapRegs`/`cEvs_setMem_atA` and
      `IselMemAux`'s event shapes); the end of a memory segment (`IselMemSeg.mem_complete`).
      Witnesses: `SegFootWitness`, `IselMemAuxWitness`, `CEvsInvWitness`, and
      `IselThreadWitnessData.driverHypA` (the driver hypothesis of the compiled atomics function).
    * *The memory statement's segment (done, `FV/Concurrency/IselMemMain.lean`,
      `IselMemLower.lean`):* **`mem_seg`**: the thread walks to the statement's one memory
      instruction; the CLIF memory holding the bytes the thread read at the access
      (`MemRelOk.store` on both sides, `match_mem`) steps (`step_next_of`) and the driver's step
      from the patched pair (`stmt_matchN`) is the thread's segment (`mem_complete`). Reads hold
      the patched bytes (`SAgrees`), writes the bytes the memory relation pins after the segment
      (`bytes_of_mr`, the post-instructions keep memory: `seqRun_nomem`); an `atomic_cas` writes
      exactly when its loop does (`cas_cmp`, the loop comparing with the expected value's vreg).
      `casOkB` now also pins an `atomic_rmw`'s loop to integer vregs (`intV`), which fixes its
      uses and so its two events (`cEvs_rmw_shape`).
    * **The layer-2 theorem (done, `FV/Concurrency/IselRefines.lean`):** `seg_res` (every
      segment from a match: terminator, pure or memory statement) and **`isel_refines`**: from a
      `Driver.Match`, every `VTRun` of the VCode under `csem`/`cEvs` is realized up to a prefix
      after which the CLIF thread has no step or is at an `atomic_cas` on read-only data
      (`IselThread.Stop`) by a `CRun`, with `Refines Maps (fun _ => False) (StepPair …)`.
      Witness (`IselRefinesWitness.lean`): `isel_refines_fA`, every premise but the match and
      the run discharged on the real lowering of the atomics function `fA` (`driverHypA`,
      `memRelOk_relW`, `X0_tls`).
    * *From the function's entry (done, `FV/Concurrency/IselEntry.lean`):* `entry_matchN`
      (`LowerSim.entry_step` with the entry code exposed: the `Args` step, then the stack-argument
      loads) and **`isel_refines_entry`**: the layer-2 refinement for a VCode thread run from
      `⟨0, 0, ρ₀, w₀⟩` (where layers 3 and 4a start), for functions whose parameters are all in
      registers (the entry code is one `Args`, without events; stack-argument loads are reads
      not yet covered). Witness: `isel_refines_entry_fA` (`fA_reg`).
    * open: the composition with layers 3, 4a, 4b.

  Outside the multi-threaded scope (no `CStep`, or two VCode events per CLIF event): `i128`
  loads/stores (two `ldr`/`str`, a mixed-size question, T2i #317) and `stack_load`/
  `stack_store` (no event, but they touch the bytes).
  * **2a (done, `FV/Concurrency/VCodeAddr.lean`, `VCodeAddrAtomic.lean`, `VCodeFrame.lean`):
    `VCodeAddr.cEvs_avoid`: when `csem F` steps, every event of its footprint `cEvs` avoids
    `F`.** The canonical run's one event of a load/store (GPR and SIMD&FP, every covered
    addressing mode, including `memFinalize`'s `x16` offsets: `memFinalize_evs`) is at
    `AMode.addr` with the access size, i.e. the access `MInst.accesses` that `straightSem`
    checks (`straight_avoid_of`); `ldar`/`stlr` access x0 (`ldar_evs`, `stlr_evs`); `dmb ish`'s
    event has size 0; every event of the LL/SC loop bodies is at x25, the address operand that
    `loopSem` checks (`rmwBody_evs`, `casHead_evs`, `casStore_evs`). Witness
    (`VCodeFrameWitness.lean`): `ldar_avoid`, the `ldar` of 8 bytes at `0x8000` under the frame
    of every address outside them.
* **Layer 3: `prepare` (done, `FV/Concurrency/PrepThread.lean`).** `VTRun`: runs of the VCode
  thread semantics. `prep_back`: a step of the prepared code from a matched configuration
  (`PMatch`: counterpart block, same vreg file and world; a branch into an edge block pends until
  the edge block's `jump`) is matched by a step of the original with the same events, or has no
  event. **`prep_refines`**: a run of the prepared code from the entry, reading any bytes, is
  realized by a run of the original reading the same bytes (`Thin`: equal up to steps without
  events, hence `Refines` with equal events, `refines_of_thin`), returning or trapping alike;
  `prep_refines_csem` for `csem`/`cEvs` (events invariant under retargeting, `cEvs_setTargets`;
  none at a `goto`, `csem_goto`).
* **Layer 4a: register allocation (done, `FV/Concurrency/AllocThread.lean`).** The allocated
  code's abstract semantics (`MStep`: location store, moves, the instructions under the same
  `sem`) against VCode. `MTStep`: its thread step (an instruction item's events are its precise
  footprint on the patched world, a move has none). `alloc_back`: the allocation checker's
  backward simulation (`sim_step_at`) lifted to events (the uses are equal, `op_sound`);
  **`alloc_refines`**: if `checkAlloc vc rf` accepts, a run of the allocated code from the entry,
  reading any bytes, is realized by a VCode thread run with the same events up to the moves.
* **Layer 4b: the Arm machine against the allocated code (open; run level done).**
  `RegLevelCorrect` as `Refines` from the allocated code to `ATStepP`:
  * **run level (done, `FV/Concurrency/ArmAllocThread.lean`)**: `PRun P f ok`, precise Arm
    thread runs whose steps satisfy `ok` (e.g. reads of the private set return the thread's own
    bytes), deterministic given the labels; `MonPair`, the Arm trace's monitor pairs (an `ldaxr`
    and a later successful `stlxr` with no exclusive event in between: a failed iteration's
    `ldaxr` pairs with nothing); `ItemSim`, the per-item obligation (from related states, every
    precise Arm run completes the item — the source step's events are events of the Arm segment,
    in order, its other writes private, an atomic update `[acqXR, relXW]` a monitor pair, the
    states after related; an item without Arm instructions decreases a measure — or ends inside
    it, or the source has terminated). **`refines_of_itemSim`**: under `ItemSim`, every precise
    Arm run from related states realizes a source run with
    `Refines (·=·) Priv (MonPair trT)` on the prefix up to the source's termination (`pair_inv`
    from the step shapes: a `relXW` is the second event of an atomic update). Witness
    (`ArmAllocThreadWitness.lean`): `refines_ldaxr`, the `ldaxr` of `ArmThread.Witness` reading
    the environment's `5` against a one-step source (`itemSim` holds for every precise run).
  * **segments (done, `ArmAllocSeg.lean`, `ArmAllocLines.lean`, `ArmAllocItem.lean`)**: a
    precise run whose reads return the thread's own bytes is the single-core run (`prun_own`;
    without events: `prun_nil`); a segment with one read is the single-core run **from the state
    patched with the read's bytes** (`prun_one_read`); the machine's steps through laid-out
    straight-line lines execute the encoded instructions and have the lines' events
    (`step_execLines`, `segEvs_execLines`, none without memory kinds: `nomem_execLines`); `Q`
    survives patching both sides outside `R.F` (`q_patch`); `realizes_op_lines` is
    `realizes_op_next` with the item's lines exposed. Witness (`ArmAllocSegWitness.lean`):
    `one_read_ldaxr`.
  * **event-free items (done, `ArmAllocStraight.lean`)**: `itemSim_noev`, `ItemSim` for
    `RelQ = Q ∧ AInv`, the allocated code's thread step (`SrcStep`: `MTStep` under `R.sem`,
    events `cEvs R.F R.ctx`), `Priv = PrivA R` (the addresses outside the world, `R.F`) and
    `Done` (returned, trapped, or no step: undefined behaviour), for functions whose
    instructions have no memory kind (`NoEvScope`: covered straight-line forms without access,
    `args`, `rets`, `udf`) and whose allocation has no moves (`NoMoves`); **`arm_alloc_refines_noev`**:
    their precise Arm runs from `Q`-related states realize `MTRun`s with
    `Refines (·=·) (PrivA R) (MonPair trT)` up to `Done`. A step ending the function is matched
    with no Arm step (the epilogue and the Arm run after it are the caller's). Witness
    (`ArmAllocWitness.lean`): `noev_premises`, the compiled `args; rets` loaded at `0x10000`
    (`R.Wf`, scope, a `Q`-related state after the prologue, `q_init`); its layout is evaluated
    in the kernel without the hash map of `labelOffsets` (`labelOffsets_one`, `layoutAt`).
  * open: `ItemSim` for the items with events (loads, stores, `ldar`/`stlr`, `dmb`, the LL/SC
    loops), moves (spill slots: reads of `Priv` under `PrivCoh`), branches (a measure for the
    fall-through `jump`s, which emit no instruction), calls; the prologue (from the ABI entry).
    Needed per form: **receptiveness** (the allocated code steps on every read value once it
    steps on one: the pc and error of a load do not depend on the loaded bytes) and **event
    equality** (the allocated instruction's Arm events are the canonical run's `cEvs`, address
    and bytes);
  * kinds by `MInst.lines` (`Code.lines_kinds`, `VCodeEvents.cEvs_kinds`);
  * frame, spill and prologue accesses in `F s` (= `Priv`; the stack is per thread), read under
    `PrivCoh`;
  * atomic loops: failed iterations are extra reads, and the successful `ldaxr`/`stlxr` pair is
    the monitor pair `pairT`;
  * the canonical run (`cEvs`) and the allocated instruction's run access the same bytes: the
    per-instruction proofs (`OperandsSound`) give whole-state results only, so this needs either
    event-level versions of them or an argument from `OperandsSound` on every memory.
* **Backward from forward.** The layers are forward per-step simulations; `Refines` is
  backward (from the actual Arm trace to a CLIF run). The bridge is determinism of each level
  given its read values (receptiveness): the source run is the one reading the target's values
  (layer 3: `prep_back`; the Arm level: `ArmPrecise.stepEvs_setMem`).
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
| T2h (#311) | Discharge `Realizes`: the per-thread event-level refinement of compiled code (isel/prepare/register-level layers re-proven as footprint-preserving simulations with interference; §3e) | layer 0 **done** (`ThreadRefine`: reduction `realizes_of_threads`, composition `Refines.trans`); layer 1 **done** (precise footprints `ArmInstFoot`, VCode thread semantics `VCodeThread.VTStep`); layer 1b **done** (event kinds `VCodeEvents.cEvs_kinds`); precise Arm labels (`ArmPrecise`) and private coherence (`PrivCoh.privCoh_of_consistent`) **done**; layer 3 **done** (`PrepThread.prep_refines_csem`); layer 4a **done** (`AllocThread.alloc_refines`); layer 4b run level and event-free items **done** (`ArmAllocThread.refines_of_itemSim`, `arm_alloc_refines_noev`); layer 2 steps 2a–2d **done** (`VCodeAddr.cEvs_avoid`, `SegRun.vtrun_patch`, `SegShape.segShapeCheck`, `IselClif.access_in_events`); 2e and 4b's items with events open |
| T2f (#304) | Rust/C++20 (RC11 with all orderings) → the Cranelift contract: cg_clif's ordering strengthening as a theorem (§3d), and the program-level chain `program_correct_rust` | **done** |
| T2g (#305) | Widening: LSE atomics (`has_lse`: not emitted in our configuration, covered by the table, `Lse.lse_maps`), the full `aarch64.cat` (`Armv8Full`, monotonicity `consistent_frag`), `i128` atomics (rejected by cg_clif) | **done** |
| T2i (#317) | Mixed-size accesses (a mixed-size model instead of `NoOverlap`) | open |

The existing single-core assumption stays in the trusted base of `E2E.backend_correct_final`, and
#38 stays open, until T2h is done (§3c: T2e composes the memory-model layer with an explicit
per-thread contract that `backend_correct_final` does not imply). T2a–T2c replace "a multi-core memory model is a project of its own" by a proven
mapping at the execution level: every Armv8 execution of Cranelift's atomics code is consistent
for the Cranelift contract, and SC (an interleaving) when the program is race-free.
