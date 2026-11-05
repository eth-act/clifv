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
thread and location, `po`-adjacent among the events: no element `po`-between the two halves
accesses memory or holds an event (`Exec.ev`, fences included). Locations are abstract (no
mixed-size accesses: Rust's atomics of a type are accessed at that type; a mixed-size model, Flur
et al. POPL 2017, is T2i, #317).

*Why `ev` (T2m, #311).* Executions built from traces (`Traces.exec`) index events by program
position `.thr i j k` (thread, step, slot); every `PEv` is an element of `E`, also the empty slots
after a step's events (`dir = F`, `ev` false). The first `Wf` required immediacy over every
element, so the empty slot `.thr i j 1` after an `ldaxr`'s single event lay `po`-between it and the
`stlxr` of a later step: no execution with a successful Arm LL/SC pair was well formed and
`realizes_compiled` was vacuous for them. Armv8's `rmw` relates the exclusive pair through program
order among events, and empty positions are not events, so `Wf.rmw_imm` now skips elements that
neither access memory nor hold an event (a `dmb` between the pair still breaks it:
`Litmus.gap_fence_not_wf`; the empty slot does not: `Litmus.gap_empty_wf`). `Exec.ev` defaults to
all elements, so for executions on abstract events nothing changes. The first definition is kept
as `Exec.WfStrict` (`WfStrict.wf : WfStrict → Wf`); every theorem taking `Wf` (DRF-SC, mapping
soundness, `program_correct*`, `realizes_*`) holds for the new `Wf` (their proofs used immediacy
only for a `co`-related write, `Armv8.atomicity`).

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
    * the composition with layers 3, 4a, 4b: see *Composition* below.

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
  * **`dmb`, `ldar`, `stlr` (done, `ArmAllocMem.lean`)**: `fence_op` (the Arm's one step has
    `dmbEv`, the source step's); `oneEv_op` for the straight-line forms with one Arm instruction
    (`OneEvForm`): **event equality** on every memory (`OneEvForm.ev`; `ldar_form`, `stlr_form`
    by `exclEvs_regs`: same address register value, same data bytes) and **receptiveness**
    (`straightSem_one`: the canonical instruction's pc, error and program do not depend on the
    memory, `ctlIndep_excl`), `Q` after both sides patched with the Arm's bytes (`q_patch`);
    `MemScope` (event-free, `fence`, covered `ldar`/`stlr`) and **`arm_alloc_refines_mem`**
    (`arm_alloc_refines_noev`'s conclusion, `NoMoves` kept); `exists_prun_line`: a precise
    one-step run at every unhooked line. Witness (`ArmAllocMemWitness.lean`): `mem_premises`
    (the compiled `args; fence; rets` with a hand-written move-free allocation: `R.Wf`,
    `MemScope`, not `NoEvScope`, `Q ∧ AInv` at `MConf.init`), `dmb_run`/`dmb_refines` (the
    one-step run through the `dmb ish` with its barrier event, refined).
  * **moves (done, `ArmAllocMove.lean`, `MoveEvs.lean`)**: the run condition **`OkPriv`** (a
    step's reads at private addresses, `PrivA`, return the thread's own bytes, its state's
    memory; `PrivCoh` is its justification at the program level); `moveLines_evs`,
    `moveLines_noStx` (every Arm event of a checked move's lines is in the frame, `FrameOk.inF`/
    `tmpF`; no line is a store exclusive; `moveCodeOk`); `prun_priv` (a precise run under
    `OkPriv` through private-only single-core steps is the single-core run); `move_op` (the
    per-item obligation at a move: the move's lines, `Q` after them, private writes, no source
    event); `itemSim_of_op_ok` (`itemSim_of_op` without `NoMoves`, for instruction items proven
    under any run condition); **`arm_alloc_refines_mv`** (`arm_alloc_refines_mem` without
    `NoMoves`, runs under `OkPriv`). Witness (`RealizeWitness.lean`): `mv_premises`, the CLIF
    `fence; return` as the pipeline compiles it (lowering, `prepare`, `spillAlloc`: 18 saves,
    the fence, 18 restores, the return), its allocation with moves.
  * **LL/SC loops (done, `ArmLoopRun.lean`, `ArmLoopSpec.lean`, `ArmAllocLoop.lean`,
    `ArmAllocLoopMem.lean`)**: `RetryLoop` (the shape of a retry loop on the machine: an `ldaxr`
    at a head, event-free steps, then an exit or a store exclusive whose failure leads back to a
    head through the `cbnz`); **`retry_run`, the measure on the Arm run** (induction on the run's
    length, a failed iteration taking `p + 2` steps): a precise run from a head writes nothing, or
    is failed iterations (reads only: interference between retries is the environment's bytes)
    and a final iteration ending at the exit or a successful `stlxr`; `img_pair`/`img_one`: the
    final `ldaxr` read and successful `stlxr` write are the image of the atomic update (a monitor
    pair). `LoopInv`, the loop-head invariant (the item's start up to the scratch registers, the
    flags when the loop sets them, and the atomic's bytes); `rmw_retry`/`cas_retry`: the emitted
    loops are retry loops; **`rmw_op`, `cas_op`**: the per-item obligation (the source step on the
    world patched with the final read, `Q` after the `cbnz` or the `b.ne` exit; the per-case
    facts `rmwBody_dep`/`casHead_dep`: the flags and x27 after the body depend only on x25, x26,
    the loaded bytes and, without a comparison, the flags); `MemScopeL`, **`arm_alloc_refines_loop`**
    (`arm_alloc_refines_mv` with the loops). Witness: `ArmAllocLoopWitness.lean`.
  * **block-ending branches (done, `ArmAllocBranch.lean`)**: `realizes_gotoE` (`realizes_goto`
    with the branch lines' steps event-free and no store exclusive, `NoEvSteps`); the measure
    (since #553, ranked configurations): layer 4b runs on `RConf` (a configuration paired with
    a rank; `SrcStepR`, `RelQR`, `DoneR`, `μR c = c.2`), the rank of a `Q` witness (`QR`, `RkC`:
    the lines after the segment of the block whose code runs, `segEnd`, then the remaining items,
    then the forwarding steps `QEd` of a `QE` entry). Source steps without an Arm step decrease
    it: an item without lines, a branch `MachBuffer` removed (the target's label line is after
    the segment, `qe_entry_rk`), a forwarding block's `jump` (one forwarding step less). No
    measure on configurations alone exists: a forwarding block `st: jump b` whose `b` was removed
    and a block `b: jump st` kept as `b st` give `Q` at `b` (entered through `st`) and at `st` at
    the same state, with zero-step source steps `b → st → b`; a witness's forwarding steps are
    bounded by the number of blocks (`qed_short`). (Before #553: the block rank
    `(#blocks - b) · K + remaining items` with the fall-through to block `b + 1`.) `goto_op(R)`;
    `MemScopeB` (`MemScopeL` and the branches), `itemSim_br`, **`arm_alloc_refines_br`**
    (`arm_alloc_refines_loop`'s conclusion, ranks dropped by `SRun.fst`). Witness
    (`ArmAllocBranchWitness.lean`): `br_premises` (`args; jump 1` / `rets`, the `jump`'s `b`
    removed by `MachBuffer`).
  * **calls: the linking induction (composition done, `CallCompose.lean`)**. `csem`'s `call`
    step has no events, but the callee's Arm code accesses memory. **Decision**: the thread's Arm
    machine runs the callee's code (no hook), and the callee's events are matched through the
    **callee's own refinement**, composed with the caller's along the call, as the linking
    induction does for single-threaded runs (`E2E.ExecBytes.Reach`: the callee's activation at
    depth `M`); an external callee's events are given by a trusted event contract.
    * `XClosed` (every successful `stlxr` event of a segment follows an `ldaxr` event of it: no
      monitor pair crosses into the segment, `monPair_left`/`monPair_right`); **`Refines.app`**:
      refinements of consecutive Arm segments compose (`appMap`), the atomic updates the whole
      trace's monitor pairs; `Realized env p Priv ls k c c'` (the first `k` labels realize a
      `CRun` from `c` to `c'`, `Refines Maps Priv`, exclusive-closed), `Realized.trans`.
    * `FunReal`: the **function contract** of an activation entered in `u` with the CLIF state
      `c` (its frame pushed): every precise run under `ok` realizes a prefix that is the whole
      run, ends in `E`, or ends where the activation has returned (`Ret`). `SegOk`: the segment
      obligation of a function's activation with invariant `Inv` — the run realizes a prefix that
      ends, returns, or ends (after at least the `bl`) at the entry of a callee (`Ent`), from whose
      every return (`Ret` of the callee) `Inv` holds again.
    * **`link_compose`**: segment obligations for the program's functions and function contracts
      for the external ones give `FunReal` for every activation of every function (strong
      induction on the run's length; the callee's realized prefix is spliced between the
      caller's segments by `Realized.trans`). `realizes_linked`: `realizes_compiled` for threads
      given by such contracts.
    * **Trusted outside-code contract `ExtEvContract`** (a premise, `link_compose_ext`): for
      every external callee entered in `u` with `c` running its CLIF-level specification, every
      precise run of the thread's machine realizes (`Realized`) a CLIF-level run of the
      specification — **its Arm events are those of that CLIF event trace**, with `Maps` kinds,
      in order, the CLIF events outside the thread's private set, its other writes private, its
      atomic updates monitor pairs — on a prefix that is the whole run, ends in `E`, or ends at
      its return (`Ret`), and **the writes of that prefix avoid the caller's private set `Fr u`**.
      Code outside the program (libc, the runtime) is not compiled by us; this contract is what
      the theorems assume of it, like `CalleeOk` for single-threaded runs.
    * Witness (`CallComposeWitness.lean`): `linked_sE`, the linking induction on a halted
      `stepi` thread whose caller enters an external callee at every step (its `SegOk`,
      `segOk_caller`; the callee's contract proven, `extContract`): every run is realized
      entirely.
    * The end condition `E` of `FunReal`/`SegOk`/`ExtEvContract` is a predicate on the realized
      Arm prefix and the CLIF state, closed under prefixing with the caller's part (`hE` of
      `link_compose`), so that a callee's realization may end where its own Arm prefix drives
      its allocated code to its end.
    * **A compiled callee's contract (done, `CallThread.lean`, `ClifLift.lean`,
      `ArmProgram.lean`)**: `CompiledE` (a compiled activation entered at its ABI entry, scope
      `MemScopeLS`, the pipeline facts after the prologue), **`thread_compiled_entry`** (layer
      4b from the ABI entry, `arm_alloc_refines_entryQ`, composed with layers 2–4a by
      `ThreadCompose.arm_isel_refinesE'`, which keeps the prefix length at layer 4b's end: the
      realized prefix is the whole run, ends where the CLIF thread stops, or drives the allocated
      code to its end, `DoneBy`, refined by exactly that prefix); `ClifLift` (the callee's CLIF
      run under the caller's suspended frames, `pushC`: `step_pushC`, `cstep_pushC`,
      `crun_pushC`, a final return step to the bottom frame dropped, `cstep_ret_nil`);
      `ArmFoot.stepi_program` (no Arm step changes the program field, so a linked machine
      dispatching on it runs the callee's `R.step` on the callee's states, `prun_transfer`);
      **`funReal_callee`**: the callee's `FunReal` in any linked machine that is `RA.step` on the
      states holding its program, entered at its ABI entry with its CLIF entry state under the
      caller's frames, its runs exclusive-closed (`xClosed_noStx`: no store exclusive with
      release in its code). Witness (`CallThreadWitness.lean`): `compiledE_L`,
      `thread_load_entry`, `noStxL`, **`funReal_load`** (the compiled `atomic_load` as a callee).
    * **A compiled caller calling a compiled callee (done, `CallSeg.lean`, witness
      `CallLoadData.lean`/`CallLoadWitness.lean`)**: `moves_privA` (through moves, per step:
      private events, no store exclusive, the program kept, `linesAt_program`), `prun_privF`
      (a precise run of a linked machine agreeing with `R.step` along such a path is that path,
      its labels the path's events, no `relXW`), `step_bl` (the machine's step at a hooked
      `bl n` line is `R.H.call (some n)`; the decoded `BL` has no events, class `plain`),
      `tstep_plain_nil`, `refines_nilS`. Witness: the CLIF `%f(v0) { v1 = call fn0(v0) }` with
      `fn0 = colocated %ld` compiled (`RC`, its hook `enterL` enters the compiled `atomic_load`:
      its program, pc at its base, x30 the return address); `prefixC` (the caller's path from
      its ABI entry to the `bl`); `RLx s` (the callee's activation entered by the `bl` from `s`,
      the caller's addresses kept: `wfX`, `abiX`, `compiledEX`, `funRealX`); `cstepC` (the
      CLIF `call`, no events); **`funReal_call`** (`link_compose` on the linked machine `MC`:
      every precise run from the caller's ABI entry realizes a prefix that is the whole run or
      ends at the callee's end, `EndC`); **`realizes_call`** (`realizes_linked`).
    * **Exclusive-closed callee runs with LL/SC loops (done, `CallSeg.lean`)**: decided from the
      monitor rather than per loop: **`xClosed_mon`**/`xClosed_mon0` — on a program whose load
      exclusives all acquire with a base other than `sp` (`LdxAcq`) and a machine keeping the
      program and the error (`armStepX_err`), every precise run from the open monitor is
      exclusive-closed (a successful `stlxr` needs the armed monitor, which only an `ldaxr` and
      its `acqXR` event arm). `funReal_callee0`, **`funReal_calleeX`**: the callee contract of a
      compiled callee entered with the open monitor (its `atomic_rmw`/`atomic_cas` loops use
      `ldaxr` on x25), from the word check `WitnessX.ldxAcq_of_words`. Witnesses:
      `WitnessX.xClosed_llsc` (the `ldaxr; add; stlxr; cbnz` loop's run with a successful
      `stlxr`), `WitnessC.funReal_bl_open`.
    * **The callee's return and the caller's whole run, on the witness (done, `CallResume.lean`, `CallLoadFull.lean`, `CallLoadResume.lean`)**:
      generic `oneEv_op1` (one `OneEvForm` step from related states, related states after it),
      `moves_privP`/`linesAt_nonRet` (moves with every state at a line other than `ret`),
      `rets_privP` (the epilogue and `ret` per step: private events, the return address, `sp`,
      memory and program after), `srcStep_of_mstep_eq/_nil`, `tstep_transfer`, `tstep_priv1`,
      `ldar_evs_line`, `ClifCStepTerm.cstep_ret_pop` (the CLIF return into a suspended caller).
      Witness: the linked machine `MC2` switches back to the caller's program at the callee's
      `ret` line; **`funReal_ld`**: the compiled `atomic_load` callee's contract *with its return*
      (every precise run realizes a prefix that is the whole run or ends after the callee's `ret`
      with the caller's Arm state resumable, `PostA`, and its CLIF state ready to `return`), from
      a concrete path through its code (`calleePath`, `calleePost`), the `ldar`'s source step by
      layers 2–4a's progress (`mstep_ldar`), the CLIF load on the read bytes (`cstep_ld`).
    * **The caller resumed (done, `CallLoadResume.lean`)**: generic **`resumeQ`** (`Q` at the item
      after a call from `Q` at the call and the caller's state as the callee returns: the pc after
      the `bl`/`blr`, no error, `sp`, program and the activation's addresses `R.F` as at the call;
      the store the state holds), `realized_privSegS`; witness `prefixCQ` (the path to the `bl`
      with `Q` there), `callerPost` (the caller's moves, restores, epilogue and `ret` after the
      return, every step private), **`funReal_callFull`** (`link_compose` with the callee's return,
      `Ret true = RetL`, the caller's invariant again after it; end condition `Returned`: the
      CLIF thread has returned) and **`realizes_call_full`**: every precise run of `MC2` from the
      caller's ABI entry is realized entirely or up to the CLIF thread's return.
    * **Layer 4b pausing at calls and returns (done, `ArmAllocPause.lean`)**: `refA_runQ`,
      **`refines_of_itemSimQ`** (`refines_of_itemSim` that also gives the Arm run up to where the
      source terminates and the relation of its last state there), `AtCall`, `AtRets`, `Pause`,
      `MemScopeLSC` (`MemScopeLS` with `call` items), `itemSim_lsC` and
      **`arm_alloc_refines_lsC`**: every precise run from a `Q`-related state is realized entirely
      or up to a state related (`RelQ`) to a configuration where the allocated code is done or
      pauses at a `call` or `rets` item. Witness (`ArmAllocPauseWitness.lean`): `scopeRC`,
      `not_scopeLS_RC`, `caller_lsC` (the compiled caller of `atomic_load`).
    * **Compiled LL/SC callees and a caller of one (done)**: `CallLLSCEntry.lean` (`compiledE_R`,
      `compiledE_C`, `funReal_rmw`, `funReal_cas` via `funReal_calleeX`: the compiled
      `atomic_rmw`/`atomic_cas` from their ABI entry); `CallRmwData.lean`, `CallRmwWitness.lean`:
      the caller `%f(v0, v1) { v2 = call fn0(v0, v1) }` of the compiled `atomic_rmw`;
      `CallSeg.prun_privF_mon` — a precise run along a private single-core path without load
      exclusive keeps the open monitor, so the callee is entered with the monitor `none` that
      `funReal_calleeX` needs (`noLdxC` from the caller's words); `WitnessCR.funReal_call`,
      `WitnessCR.realizes_call`.
    * **Layer 4b on a linked machine (done, `ArmAllocLinked.lean`)**: the item lemmas' `…R`
      versions (`noev_opR`, `fence_opR`, `oneEv_opR`, `rmw_opR`, `cas_opR`, `goto_opR`,
      `move_opR`; the old statements are their corollaries) record that a run ending inside an
      item ends at an unhooked instruction line other than `ret` (`AtNonRet`; `OpOutN`;
      `noRet_lines`: no allocated instruction's lines contain a `ret`, only the epilogue's do;
      `nonRet_execLines`); `ItemSimN` (`ItemSim` with that condition), `prun_splitN`,
      **`ItemSimN.transfer`** (`ItemSimN` for `f` gives `ItemSim` for every machine agreeing
      with `f` at those states), `AgreesAt R g` (`g` is `R.step` at `R`'s lines other than `ret`
      on `R`'s program), `itemSim_lsCN`, `itemSim_lsCL` and **`arm_alloc_refines_lsCL`**:
      `arm_alloc_refines_lsC` for every such machine. Witness (`ArmAllocLinkedWitness.lean`):
      `agreesAt_MC2`, `caller_lsCL` (the linked machine `MC2` of the caller of `atomic_load`).
    * **The generic call theorem (done for program callees, AtomicsCalls19,
      `CallSegOkGT.funRealT_link`/`realizes_linked_calls`; see "`SegOkG` and the generic call
      theorem" below)** (every compiled function whose callees are compiled program functions
      realizes its runs up to an `EndT` end; `ExtEvContract` externals are not covered by it:
      `StatOk.envx` excludes environment externs). Needed: (1) layer
      4b's pc invariant on a linked machine — **done** (above); (2) layer 2's return coverage — **done at layer 2**
      (`IselStep.term_retN`: a return's code runs to the VCode return without memory instructions;
      `SimResR`/`SegResR` record that a CLIF thread that returned realizes the whole VCode trace,
      through `pure_segR`, `mem_completeR`, `mem_segR`, `term_segR`, `simResR_of_seg`, `seg_resR`,
      **`IselEntry.isel_refines_entryR`**; the `P` versions are their corollaries; witness
      `IselRefines.Witness.isel_refines_entryR_fA`), and through all layers
      (`ThreadCompose.isel_alloc_refinesR`, `ThreadProgress.arm_isel_refines_fullR`,
      **`RealizeCompiled.thread_full_of_simR`**/`thread_compiledLS_fullR`: where the CLIF thread has
      returned, the realized prefix is the whole run or the Arm run up to its end reaches a state
      related to the allocated code's end; witnesses `ThreadCompose.Witness.isel_alloc_refinesR_fA`,
      `WitnessC1.thread_cas1_fullR`); (3) the layers' state relation at a pause (the CLIF state at its
      `call` with its arguments in the Arm registers, for the callee's `CompiledE`) and after the
      return (layer 2's `Match` after the call from the callee's results and preserved registers),
      which the composition theorems (`ThreadCompose.isel_alloc_refinesP`, `arm_isel_refinesE'`)
      do not export; `resumeQ` gives layer 4b's side of the latter.
      **What (2) and (3) still need (mapped 2026-10-22).** Layer 2 has no call case: the
      multi-threaded check rejects call statements (`IselCheck.threadInstB`, `instOkB`:
      `!isCallB`), `LowerSim.Match` requires `s.callers = []`, and `DriverHyp.ext` excludes calls of
      program functions; the single-threaded call proof (`LowerSim.stmt_step` via
      `CallsRefine`/`XCallsOk`, `IselCtlCallRules.call_sym_lowerInstOk`) covers external calls run
      as one CLIF step. The pieces, in order:
      * **(2a) the pause at layer 2 — done (`IselDriverT.lean`, `IselCall.lean`, witness
        `IselCallWitness.lean`)**: `DriverHypT` (`DriverHyp` without `ext`; `DriverHyp.toT`) and
        `IselCheck.threadCheckBlC`/`threadCheckC` (`threadCheckBl` admitting `callOkB` statements:
        a `call` whose code is exactly one direct `call` — a `bl`, register arguments only, no
        `stackArgumentStores`, no GOT load — its results needing no extra moves;
        `threadCheckBlC_of`); the layer-2 lemmas restated on them (`stmt_matchNT`, `term_matchNT`,
        `term_retNT`, `mem_vregT`, `mem_segRT`, `pure_segRT`, `term_segRT`, `entry_matchNT`,
        `enter_matchT`; the old statements are their corollaries); `SimResC`/`SegResC` (a third
        end: the realized prefix stops at a call statement, `AtCallS`, related by `Match` to a
        VCode configuration from which the rest of the trace runs), `simResC_of_seg`, `seg_resC`
        (a call pauses at once), **`isel_refinesC`** (from a `Match`) and
        **`isel_refines_entryC`** (from the entry); with an `ExtSem` without `call` step
        (`NoCall`) the VCode stops at a matched call (`match_atCall`, `vtrun_atCall`), so
        **`isel_pauseC`**: the trace is realized as before, or entirely with the CLIF state at a
        call related by `Match` to its last configuration. Witness: `driverHypT_of`,
        `isel_pause_fC` (the caller of `atomic_load`, which `threadCheck` rejects). Layers 3/4a
        return their relation at the end (`PrepThread.prep_run`, `AllocThread.alloc_run`); the
        composition with them is part of (3).
      * **(2b) the callee's entry from the pause**: `CompiledE` of the callee from the caller's
        `Match` at the call (the CLIF state after `stepCall`'s push, `ClifLift.pushC`) and layer
        4b's `Q` at the `call` item (the fixed-use operands put the arguments in x0…, `ArgsAtEntry`).
      * **(2c) the resume — done per layer (`IselResume.lean`, `CallResumeQ.lean`,
        `CallResumeLayers.lean`; witnesses `IselCallWitness.isel_resume_fC`,
        `CallResumeWitness.resume_RC`)**. The relations after the return are rebuilt by one step
        of the `call` under the external semantics returning the callee's outputs and the caller's
        state after the return as the world (`IselResume.xcallX`; a VCode/allocated step, no
        thread footprint). Layer 2 (**`isel_resumeC`**): the driver's statement step in the
        **extern view** — the callee as an extern of the environment returning exactly the CLIF
        return values and memory (`envX`), the program without functions (`pNil`), the memory
        relation pinned to the caller's slots (`pinSl`), `DriverHypT` for any environment from the
        lowering's obligations (`driverHypT_mk`, `driverHypT_of`) — gives `Match` after the CLIF
        return from `PrefixHold rvals outs` and the memory relation at the caller's slots after
        the return. Layers 3–4b (**`resume_layers`**): `mstep_call` (the allocated `call` steps
        from `Q` at the `call` item when the callee preserved the caller's live locations outside
        the call's clobbers and the low halves of the clobbered callee-saved registers, `ckeep`;
        the outputs the def locations' values), `alloc_call_vstep` (`op_sound`, the checker's
        `Match` after it), `pmatch_call`/`prep_vstep_next` (`prepare`'s block correspondence),
        **`resumeQW`** (`resumeQ` for any store holding the state's live locations and any world
        agreeing outside `R.F`, the caller's frame/code/kept addresses `R.FK` kept). Remaining for
        (3): the callee contract that supplies these premises — for a compiled callee, from its
        layer 4a `Match` at its `rets` (callee-saved registers, `RegallocSound.Match`'s `.ret`
        case) and the epilogue (`RegLevelFrame.ret_machine`, `CallResume.rets_privP`), the result
        registers (the call's fixed defs), `MemAgree` of its final CLIF memory with the Arm memory
        (for the memory relation at the caller's slots); for an external callee, part of its
        `Ret`.
      * **(3)** `SegOk` for a compiled function in `MemScopeLSC` on the machine of
        `arm_alloc_refines_lsCL`: its segments are the runs between its entry, its calls' resumes
        and its `rets`, each by layers 2–4b from the relation of (2a)/(2c); `link_compose_ext`
        then gives `FunReal` for every activation, `realizes_linked` the program level. **Done so
        far**: layers 2–4a from related configurations (`CallLayers.isel_alloc_refinesC`: the
        relations `Driver.Match`, `PMatch`, the checker's `MatchRun` at a segment's start; a run
        of the allocated code is realized entirely with a step at its end, or up to where the CLIF
        thread stops, or — with `NoCall` — entirely, ending at a call statement related by all
        three relations to the run's last configuration; `prep_run`/`alloc_run` keep the
        relations, `PrepThread.prepFacts_of_check` gives `prepare`'s); witness
        `CallResumeWitness.isel_alloc_fC`. **Done since** (#529 and its follow-up): (i) layer 4b
        composed (`CallLayers.arm_isel_refinesG2`/`G`/`C`) and the entry's relations
        (`CallLayers.prep_init`, `alloc_init`, `isel_alloc_refines_entryC`,
        **`arm_isel_refines_entryC`**; witness `CallEntryWitness.arm_entry_fC` on the linked
        machine `MC2`); (ii) the `rets` end at the layers: layer 2 pauses at a `return` too
        (`IselCallRet.isel_refinesCR`, `isel_refines_entryCR`; `IselRetT.term_stepRT` is
        `term_step` on `DriverHypT`), `CallRets.ret_pause` (a done `return`'s VCode tail is
        event-free and returns values holding the CLIF ones), `CallRets.isel_alloc_refinesCR(G)`,
        `CallRetsAlloc.rets_alloc` (from `Q` and the checker's relation at a `rets` item: the
        epilogue and `ret` reach the return address, `sp` as at entry, memory kept, the `rets`'
        uses in their fixed registers, every callee-saved register equal up to `ckeep` to the
        checker's entry value) and `ret_link` (those uses are the VCode's returned values),
        composed in **`CallRetsEnd.arm_isel_refinesCR`**/**`arm_isel_refines_entryCR`** with the
        return contract `RetEnd` at a `rets` pause (witness `CallRetsWitness.arm_entryCR_fC`).
        **Still open**, in order: (ii') the CLIF return pop in the linked thread
        (`ClifCStepTerm.cstep_ret_pop` under `ClifLift.pushC`; done: `CallRets.ret_pop`, #531),
        turning `RetEnd` into (2c)'s
        premises — layers 3–4b **done** (`CallRetResume.lean`, witness `CallRetResumeWitness.lean`):
        `resume_layers`' `hpres` asks the state after the return to keep every non-clobbered live
        location, including the call's result registers (`info.defs` are not clobbers), so it
        fails for a callee with results (`not_hpres_yX`); `mstep_callR`/**`resume_layersR`** ask it
        only off the late def locations; `frame_congr`, **`hpresR_of_callee`**, `hkeep_of_callee`
        derive it from callee-saved registers up to `ckeep`, `sp` and the `RA.FK` memory (premise
        `hdef`: each def register is a late def operand's location, `checkStatic`'s fixed check);
        **`resume_premises_of_retEnd`**: all of them from the callee's `RetEnd`, given the callee's
        entry values = the caller's at the `bl` (`hr₀`), its entry `sp`, the return address and
        the callee's run keeping `RA.FK` (premises supplied by (2b)/(iv)); witness `resume_RX` (a
        callee returning `42` in `x0`). **Done since (`CallRetPremises.lean`, witness
        `CallRetPremisesWitness.lean`)**: `defOps_eq`/`defPairs_locs` (a call with virtual def
        registers has one fixed late def operand per def, in order; past `checkStatic` its def
        locations are the def registers), **`hdef_of_static`**/**`hdef_of_q`** (`hdef` from the
        static check / from `Q` at the `call` item), **`prefixHold_outs`** (`isel_resumeC`'s
        `PrefixHold` from `RetEnd`'s returned values and `rets` uses, given the ABI agreement of
        the callee's `rets` registers with the caller's def registers), **`relW_after_callee`**
        (the memory relation at the caller's slots after the return from the caller's at the call
        and the callee's `MemRel` at its `rets`, given the memory after the return has only
        allocations live at the call), **`realized_rets`** (the epilogue up to the `ret` as a
        private segment on any machine `AgreesAt` the activation); witnesses `defsC1_q`, `locsC1`,
        `prefixHold_RX`, `relW_id`, `rets_RC`. **The two `rets` ends excluded (done,
        `CallRetsN.lean`, witness `CallRetsNWitness.arm_entryCRN_fC`)**: layer 2 with the VCode
        end off `rets` (`IselStep.VAtRets`, `vstep_of_starNR`: a `rets` steps to a return, from
        which no running configuration is reached; `IselThread.SimResRN`/`SegResRN`,
        `pure_segRTN`, `term_segRTN`, `IselMemSeg.mem_completeRN`, `IselMemMain.mem_segRTN`,
        `IselCallRet.SimResPN`, **`isel_refinesCRN`**, `isel_refines_entryCRN`; the old
        statements are corollaries), through layers 3/4a (`isel_alloc_refinesCRGN`, with
        `pmatch_rets`); layer 4b stopping at its first pause (`ItemSim.avoid`,
        `arm_alloc_refines_lsCLA`: its run never steps a `rets` item, `srun_avoid_ret`); at a done
        `return` the allocated configuration steps (`vstep_or_ret_of_retFrom`, `doneRet_mstep`),
        which `Done` and `AtCall` (`NoCall`) exclude: **`arm_isel_refinesCRN`**/
        **`arm_isel_refines_entryCRN`** end entirely, where the CLIF thread stops, at a call
        with the three relations, or at a done `return` with `RetEnd`;
        (iii) (2b) the callee's entry from the relations at the
        pause (`enterFunc`'s CLIF state under `ClifLift.pushC`, the arguments in x0… from the call's
        fixed uses, the callee's `RL` from the caller's state at the `bl`, its memory relation).
        **Done (`CallEntryPremises.lean`, witness `CallEntryPremisesWitness.entry_premises_L`)**:
        `prologue_fields`, `regVal_calleeSaved_congr`, **`entry_premises`** — for a callee whose ABI
        entry state agrees with the caller's state at the call but in the pc and `x30` (the link),
        `resume_premises_of_retEnd`'s `hr₀` (the checker entry values after the prologue),
        `hsp0` and `hra`. **`hmr` done (`CallCalleeRet.lean`, witness
        `CallCalleeRetWitness.lean`)**, without the planned restatement of layer 4b with a
        private set free of the kept addresses: the register-level relation `Q` carries
        `StRel.gkeep` (the kept addresses `RB.G` hold their entry bytes), which survives
        interference (`stRel_patch`: the patches avoid `RB.F ⊇ RB.G`) and the activation's own
        calls (`resumeQW`), so it holds at the `rets` pause (`gkeep_of_q`); with
        `RB.G ⊇ RA.FK` (`Nested`) that is `hmr`. **`RetC R ra r₀ y`** (the return contract
        relative to the activation's own entry: return address, no error, `sp`, `R.G` as at
        entry, callee-saved registers up to `ckeep` the checker entry values),
        **`retC_of_retEnd`**, **`resume_premises_of_retC`** (every premise of `resume_layersR`
        but the program from `RetC` of a callee entered at the caller's call); witnesses
        `retC_RX`, `resume_premises_RX` (the `atomic_load` callee at `sBF`, a return with `42`).
        **The caller resumed at every layer (done, `CallResumeAll.lean`, witness
        `CallResumeAllWitness.resume_all_fC`)**: `atCall_of_pause` (at the call end of
        `arm_isel_refinesCRN` the allocated configuration is at the `call` item, with
        `pmatch_call_fwd`: `prepare` keeps a `call`), **`resume_all`** (from that end and a
        callee's `RetC`, its returned values in its `rets` registers and its `MemRel` at its
        `rets`: `Match`/`PMatch`/`MatchRun`/`Q`/`AInv` at the item after the call, i.e.
        `arm_isel_refinesCRN`'s premises for the caller's next segment; layer 2 by
        `isel_resumeC`, layers 3–4b by `mstep_callR`/`alloc_call_vstep`/`prep_vstep_next`/
        `resumeQW`, the two VCode steps equal by `vstep_det`). Static premises left to the
        general theorem: the call's defs virtual, the callee's `rets` registers the call's def
        registers, `#defs = #sigRets` (checks on the lowered code). **The linked machine (done,
        `LinkedMachine.lean`, witness `LinkedMachineWitness.lean`)**: `LFn` (an activation's
        static data), `Link` (named functions), `Link.enter`/`Link.H` (a `bl` of a linked
        function enters it as `enterL` does), `Link.act F s0 K G` (the activation), `Link.M`
        (the current function's step; at its `ret` the program of the function containing the
        return address); under `Link.Ok` (laid out, disjoint code ranges): `agreesAt_M`,
        `M_eq_step`, `M_bl`, `M_ret`, `M_ret_prog`, `M_ret_x30`; witness `link2` (the two
        witness functions; `M_blC`, `M_retL`, `agreesAtC`, `agreesAtL`). **The callee's entry
        on the linked machine, Arm level (done, `CallEnterArm.lean`, witness
        `CallEnterArmWitness.lean`)**: `Q.hooks`/`StRel.hooks` (the relation does not depend on
        the hooks), `LFn.Static` (the static part of `RL.Wf`), `Link.act_wf`,
        **`Link.step_call`** (at a direct `call` item the machine steps the `bl` into the
        callee, event-free, plain), **`Link.enter_call`** (the callee's activation at the entered
        state is `Wf`, its entry an `AbiCall` returning after the `bl`, it agrees with the
        caller's state but in the pc and `x30` and has its memory, `Q`/`AInv` after its
        prologue: the start of `arm_isel_refines_entryCRN`); witnesses `step_call_C`,
        `enter_call_L` (the caller's `bl` at `sBF` on `link2`). Open on the CLIF side of the
        entry: the callee's CLIF state (`enterFunc` under `pushC`, `cstepI_call`), its memory
        relation and `ArgsAtEntry` — waiting for the slot-oracle semantics (SEM1 design A,
        UninitZ), which changes `enterSlots`.
        **`CStep` runs as `CStepS` runs (done, `CStepSConv.lean`, witnesses
        `CStepSConvWitness.lean`)**: `cstepS_of_cstep`, `crunS_of_crun` (reads avoiding the
        evolving mask), `stop_encT` (the CStepS realization stops where the CStep one does),
        `cstepS_ret_iff` (a bottom-frame return is a `CStepS` step exactly from the empty mask:
        the top-level contract ends before a return with masked bytes), the start-dirty set
        `Refines.toT_dirty`/`Refines.toT_parts` (private set ∪ mask ∪ addresses that start no
        location of a thread-wide partition `PartDisj`/`OnParts`, the T2i restriction).
        **CLIF side of the callee entry (done, `CallEnterClif.lean`, witness `enter_C`)**:
        `step_call_entry`/`cstepI_call_entry` — a direct call's step is `pushC` of the caller's
        frame over the callee's own entry state with exactly the CLIF facts of
        `arm_isel_refines_entryCRN` (slots/memory from `enterSlots`, entry block, registers from
        the call's argument values), adding the placed slot bytes to the mask. Open: the callee's
        `RelW` and `ArgsAtEntry` from the call's fixed uses (layers 2–4 at the `bl`).
        **`resume_all`'s static premises as checks (done, `CallResumeChecks.lean`, witness
        `defs_fC`)**: `callDefsVirtB_iff` (`hvdef`), `callDefsRetB_iff` + `habi_regs` (the register
        part of `habi`), both sound and complete. **The arity part as a check (done,
        `CallArity.lean`, witness `CallArityWitness.arity_fC`)**: `callArityB`/`callArityBl`/
        `callArityC` (per statement on the driver's lowering: a `call fn _` whose code is one `call`
        defines `(sigRets ext.sig).length` registers, `ext = f.extern? fn`), `match_atCallA`
        (`match_atCall` with the arity), `resume_allP` (`resume_all` with `habi` only at the paused
        instruction; `resume_all` its corollary), **`resume_allA`** (`resume_all` with `habi`
        replaced by `CallDefsRet` + `callArityBl`; `rvals.length ≤ defs` by `returns_le_sigRets`).
        **The call's arguments at the `bl` (done, `CallArgsAt.lean`, `CallArgsL2.lean`, witnesses
        `usesV_fC`, `useOps_iC`, `resLen_fC`)**: layers 3–4b, **`call_uses_q`** (with `Q` and the
        checker's `MatchRun` at a direct `call` item with virtual uses, `CallUsesVirt` checked by
        `callUsesVirtB_iff`: the `j`-th use `(v, p)` has in register `p` the `j`-th VCode use value;
        `useOps_eq`); layer 2, **`isel_argsAt`** (at a matched call statement the VCode is at
        `call (.sym ext.name)` whose use values satisfy `ArgsAt ext.sig vals`), read off the
        driver's call step under a *guarded* external semantics (`xcallG`/`ArgG`: its `call`
        steps only when `ArgsAt` holds, which `XCallsOk` grants; `isel_resumeG`, `argG_of_vstep`),
        with probe results of the right types (`callResLenB`: results as many as the extern's
        returns). **The callee's `ArgsAtEntry` (done, `CallArgsEntry.lean`, witness `useRegs_fC`)**:
        the check `callUseRegsB`/`callUseRegsC` (a direct call's use registers are `locsOf
        ext.sig`'s registers in order, `allRegs?`, all argument registers), `match_atCallU`,
        `argsHold_of_uses`, **`callee_args`** (at the paused call every argument in its register
        of the machine state, no stack arguments: `isel_argsAt` through `pmatch_call_fwd`/
        `atCall_of_pause` with `call_uses_q`), **`callee_argsAtEntry`** (`ArgsAtEntry F ext.sig
        vals` of the callee's body-entry world `bodyOf FB.af (Link.enter FB x)`, any `F`;
        `regVal_bodyOf_enter`), `callee_argsAtEntry_sig` (callee signature `ext.sig`). Left: the
        callee's `RelW` (after #567).
        **From the ABI entry (done, `CallSegAbi.lean`, witness `arm_abiCRN_fC`)**:
        `prun_prologueG` (the prologue on a machine agreeing with the activation),
        **`arm_isel_refines_abiCRN`** (`arm_isel_refines_entryCRN` from `RA.s0`, the prologue's
        private writes composed by `Refines.app`): a callee's first segment.
        **Step (4) design (AtomicsCalls14, 2026-10-23)**, decided without changing code:
        - *Activations*: `G` = the activation's data (`LFn`, `s0`, `K`, `G`, `ra`, the CLIF caller
          frames `ext`), `Ext` empty (every callee compiled); `Inv` is the entry form (the
          premises of `arm_isel_refines_abiCRN`) or the resume form (those of
          `arm_isel_refinesCRN`, from `resume_allA`); `DriverHypT` of every activation from the
          function's static checks (`driverHypT_of`, any `Γ`, `c`).
        - *Run condition*: one `ok` for the thread, `OkPriv` of the thread's bound (its stack and
          code), which implies every activation's `OkPriv` (`PRun.mono`, `PrivA ⊆ Bnd`).
        - *Callee budget*: exact nesting, `KB = KA - frameDrop FB.af` (a proof parameter, no code
          change), so the caller's dead stack is the callee's `Region`.
        - *Dirty sets*: at a segment start `D ⊆ PrivA RA ∪ U ∪ NS`, at its end `¬ Clean`
          (`⊆ D ∪ PrivA RA`); across a call `PrivA RA ⊆ PrivA RB ∪ slotArea RB`, the callee's
          slot bytes in the mask (`cstepI_call`), its padding in `NS` as addresses no CLIF read
          of the segment starts at (CLIF-valid memory avoids the caller's dead stack,
          `MemRel.valid`); across a return `PrivA RB ∪ U ⊆ PrivA RA ∪ U`.
        - *Masks*: the realized prefix stops before the first CLIF step reading a masked byte
          (`Refines.take`, labels of at most one event, `prun_len`); a callee's return keeps its
          unwritten slot bytes masked (`CStepI` allows old masked bytes), the bottom frame's
          return needs the empty mask (`cstepS_ret_iff`). The top-level end condition: the
          whole run, `Stop`, the next CLIF step reads a masked byte, or a return with masked
          bytes.
        - *Exclusive-closed segments (done, AtomicsCalls15)*: the monitor survives calls
          (`monAfter`; a failed CAS leaves it armed), so `xClosed_mon` from the open monitor does
          not give each segment's `XClosed`. The Refines-level argument above has a gap (a lone
          CLIF `scW` may map to `relXW` under `Maps`), so it is done at layer 4b instead: a
          private Arm write is never a `relXW` (`PrivW`, `Img.priv`, `RefA.priv` now say
          `Priv addr ∧ k ≠ relXW`; straight-line code by `stepEvs_noRelXW` from `NoStx`), so
          every `relXW` of a `RefA` target is the image of a source `relXW`, the second event of
          an atomic update whose `acqXR` maps before it (**`RefA.xClosed`**). Carried up:
          `refines_of_itemSimQX`, `arm_alloc_refines_lsCLAX`, `xClosed_take`,
          `arm_isel_refinesG2NX`/`CRGNX`/**`CRNX`**/**`entryCRNX`**, **`arm_isel_refines_abiCRNX`**
          (the old names are corollaries); witness `arm_abiCRNX_fC`. The epilogue/`ret` and the
          `bl` have no `relXW` (`ret_end`, `step_bl`).
        - *Valid memory across a callee (done, `CallValid.lean`)*: `resume_allA`'s `hval` (every
          range valid after the callee's return was valid at the call). The callee's run is the
          thread's CLIF run from the caller's call at depth `n` back to depth `n`:
          `AllocInvD cm n` (every allocation within `cm`'s valid ranges or a slot of a frame above
          depth `n`, `slotBasesAbove`), `allocInvD_self`, **`allocInvD_step`**/`allocInvD_run`
          (`Clif.step_next_cases` of `LinkFree` programs, externs keeping allocations),
          **`valid_of_allocInvD`** (back at depth `n`). In the linking induction every open
          activation's `(cm, n)` pair is carried, so the per-alloc form composes without a
          per-range case split. Witness `CallValidWitness.lean` (`allocW`, `retW`: a callee
          with a placed slot).
        - *Segment pieces on the thread (done, AtomicsCalls15)*: **`CallSegLift.realizedT_lift`**
          (a chain segment `CRun` from the activation's own state, lifted below its callers by
          `crun_pushC`, `Refines.prefixNil`, cut before a masked read by `realizedT_cut`);
          **`CallStepT`**: `cstepS_of_cstepI`, `realizedT_nil`, **`realizedT_call`** (the `bl`
          label realizing the CLIF call at `pushC ext s`, the callee's placed slots added to the
          mask), **`realizedT_priv`** (private Arm labels, no `relXW`, realizing event-free CLIF
          steps), `cstepS_ret_lift`; **`CallRetT.realizedT_ret`** (a callee's `RetEnd` pause on
          the linked machine: no CLIF step before the `ret`, the CLIF return into the caller from
          it on, `RetC` after it). Witnesses `CallSegLiftWitness`, `CallStepTWitness`,
          `CallRetTWitness`.
        - *`SegOkG` pieces (done, AtomicsCalls16/17, `CallSegOkG.lean`, `CallSegGeo.lean`)*:
          `RReach`/**`PartsOk`** (reachable CLIF states, their accesses on a location partition:
          a new premise of the general theorem), `OkB` (the thread's run condition), `EndT`
          (whole run, `Stop`, event-free return, stuck, trap, call at depth ≥ `Dcap`, masked read,
          masked return), **`seg_end`** (a chain segment lifted below its callers is a `RealT`
          prefix ending in `EndT` or at its pause, the end-dirty set by `DirtyEnd`), `Act`,
          `StatOk`, `FnOk`, `ChainP` with **`chainP_entry`**/**`chainP_resume`**, **`ret_seg`**
          (a callee's return pause, `realizedT_ret` below its caller), `call_next`;
          `Nested.privA_sub`, `Nested.privA_callee(_out)` (private sets of nested activations),
          `cstep_reads_valid` (CLIF events at valid memory). Sharper end-dirty sets:
          `DirtyEnd`, `realizedT_segW`/`cutW`/`liftW` (old names corollaries). Witnesses
          `CallSegOkGWitness` (from a trap state, the caller's call), `CallSegOkGActWitness` (the
          caller's `StatOk` in `link2`, its chain property from the ABI entry and resumed; the
          callee's return pause), `CallSegGeoWitness` (`atomic_load` nested in its caller). The
          frame-padding gap (a callee's start-dirty set covering stale bytes in its frame's slot
          padding) is closed by `CallSegLive.seg_live` (AtomicsCalls18, #642).
        - *The call pause and the resume (done, AtomicsCalls17, `CallSegCall.lean`)*:
          **`CodeIn L R`** (every linked function `R`'s own or its words in `R.G` and in memory at
          `R`'s entry; `CodeIn.code` via `gkeep`/`StRel.code`, `CodeIn.callee` for `G = R.FK`),
          **`stackAvail_callee`** (budget `KB` with `frameSize + 16 + KB ≤ K`),
          **`budget_call`** (budget `(Dcap - d) * M` at depth `d`), `nested_callee`,
          **`gfree_callee`** (`Nested.region_not_FK`), **`call_endK`** (`call_end` with
          `hcode`/`hstB`/`hgB` discharged, the callee's `CodeIn` and nesting returned),
          `retEnd_n` (a `RetEnd` at any step count reaching `ra` without error), **`resume_ret`**
          (`resume_allA` with `hB`/`hmemB`/`hus`/`hpreB`/`hy`/`hprog` from the callee's `RetEnd`,
          `hval` from `AllocInvD` via `valid_of_allocInvD`; new static premise `hdr`: the
          callee's `rets` registers are `CallDefsRet` of the caller). Witness
          `CallSegCallWitness` (the caller in `link2` with budget `0x100`, `atomic_load` entered
          with `0x10`; the resume after `atomic_load`).
        - *The callee's entry and the padding gap (done, AtomicsCalls18, #642)*:
          `CallEntryRel.callee_relW`, `CallSegEnt.callee_chainP`, `CallSegRun.SegInv`,
          `CallSegLive.Live`/**`seg_live`**, `CallSegPc.ra_in`/`ra_out`/`ret_tys`.
        - ***`SegOkG` and the generic call theorem (done, AtomicsCalls19, `CallSegOkGT.lean`)***:
          `Inv` (the activation's chain property from its own CLIF state below its callers, and
          `Live`), `Ent`, `Ret` (the bottom activation at its done `return`; a callee after its
          `ret` with the CLIF return into its caller realized, the returned state's `LInv`, the
          open activations' `AllocInvD`, the oracle popped, the dirty set bounded); `LinkOk` (the
          static premises of the link: every program function compiled, `FnOk`, with its oracle
          frame `fr n = (frameDrop, slotOffs)` and `frameSize + 16 ≤ Mx`; `CallsInside`; no
          direct self-call; the callees' `rets` registers `CallDefsRet` of every caller).
          **`segOkG`**: `SegOkG` for every activation. Call pause: `call_next`,
          `step_call_entry`/`cstepI_call`, the `bl` by `tstep_plain_nil` and `realizedT_nil`, the
          callee from `callee_chainP` with budget `K - (frameSize + 16)` (`budget_call`; a call at
          depth ≥ `Dcap` is an `EndT` end), `ext := (frame, results) :: ext`, `opens :=
          (mem, depth) :: opens`, `sps := spB :: sps`, `N := (N ∪ (PrivA g ∖ PrivA h)) ∖ slotZ`
          (its `nv` from the caller's `MemRel.valid`, its `ndead` from the nesting); the callee's
          `Ret` resumes the caller by `resume_ret` + `chainP_resume` (`hval` from the head open
          activation's `AllocInvD`). Return pause: `ret_seg`, `LInv`/`AllocInvD`/oracle across the
          CLIF return (`step_next_linv`, `allocInvD_step`, `step_done_mem`).
          **`funRealT_link`** (`link_composeT` with every activation compiled, no external
          callee) and **`realizes_linked_calls`** (`realizes_linkedT` with each thread a root
          activation). Premises: `PartsOk` (accesses from reachable CLIF states on a location
          partition: no mixed-size accesses), `PartDisj`, `LinkFree`, `EnvKeepsAllocs`,
          `EnvKeepsPlace`, `PlaceOk p fr Mx`, the depth bound `Dcap` of reachable CLIF states,
          `LinkOk`, each thread's `Ent`; trusted: `StackDisjoint` (race freedom on the threads'
          stacks and start-dirty sets). Every callee is a program function (`StatOk.envx`), so no
          `ExtEvContract` premise is needed.
          **External callees (#649, done)**: `CallSegExt` — an external is Arm code of the link
          with a slot-free CLIF specification in the program; its trusted contract
          `ExtEvContractT` (`ExtChain`: the `ChainP` shape — `Refines Maps` with private set the
          external's stack `XPriv K x` up to its return `XRetA`: pc after the `bl`, `sp`,
          callee-saved registers, the caller's `FK` memory, the caller's program, `MemRel` of the
          specification's memory, the returned values in its return registers; entry premises:
          `Entered`, `ArgsInRegs`, `MemRel`, the return address in linked code); `XAct`/`XEnt`/
          `XRet`, **`xfunReal`** (the chain lifted by `seg_endP`, the invariants along the
          specification's run, the CLIF return by `cstepS_ret_pop` at no label). `CallSegOkGT`:
          `AG` (compiled or external activations), `EntX`/`RetX`/`InvX`, `LinkOkX`,
          **`segOkG_ext`** (the call pause into an external: `call_stepX`, `XEnt`; the resume
          from `XRet` by `CallArity.resume_allAX`, the RB-free `CallResumeAll.resume_allX`, and
          `chainP_resume`; `segOkG` is its corollary without externals), **`funRealT_link_ext`**,
          **`realizes_linked_calls_ext`**. Witness `CallSegOkGTExtWitness`: `linkX` (the caller
          `fC` and an external `ld` whose code is one `ret`, specification `v1 = bor v0, v0`),
          `ext_ret` (the contract of a one-`ret` external returning its argument, proven in any
          well-formed link; `extX` on `linkX`), `linkOkX`, `funRealT_link_X`. End to end, every
          premise discharged but the run: `CallSegOkGTExtFull.realizes_call_extT` (`linkX`, as
          `realizes_call_fullT`, reachability by `WitnessFull.CallShape`) and
          `CallSegOkGTMix.realizes_calls_mixT` (one link `[ld, xt, f]`: the compiled caller `fM`,
          `v1 = call ld(v0); v2 = call xt(v1)`, calls the compiled `atomic_load` and then the
          external `xt`; its compiled data, `fnOk_M`/`fnOk_LM`, `linkOkM`, and the two-call
          reachability family `CallShape2`/`Fam2`/`reach_inv2`/`depth2`/`partsOk2`).
        (iv) the thread-wide private set (every activation's `PrivA` and the CLIF events' avoidance
        of it; with CLIF stack slots in callees the private sets of different activations overlap
        other activations' slots); then `SegOk`, `link_compose_ext`, and `realizes_call_full`/the
        rmw-callee witness
        as instances. **Scope measurement (2026-10-23)** for the planned first scope "functions
        without CLIF stack slots" (`f.slots = []`), on the retained `bin-check` CLIF dumps:
        functions using atomics (`atomic_load/store/rmw/cas`, `fence`) without slots — fv-demo
        0/12, survey (4 of 18 executables' dumps on disk) 0/6, deps 1/54; their direct callers
        without slots — fv-demo 7/10, survey 4/4, deps 30/63. Every excluded function has
        `explicit_slot`s (mostly 8/16/1 bytes). So that scope covers essentially no function
        that itself uses atomics. The thread-wide private set therefore has to cover activations
        with stack slots: each activation's slots lie in its own Arm frame, below the caller's.
        **Design (decided 2026-10-23, scope "callees without slots" rejected).** Two gaps of the
        multi-threaded specification block activations with slots: (A) `Refines`/`Realized`/
        `link_compose`/`realizes_linked` use one private set per thread for the whole run, but
        with stack reuse an address that is one callee's spill slot (an unmatched write: private)
        is a later callee's CLIF slot (a CLIF event: shared); an uninitialised read of that slot
        would read the stale spill, which the restricted CLIF execution cannot justify. (B) With
        the slot oracle (`Mem.place`, so that CLIF slot addresses are the Arm frame addresses),
        `enterFunc`'s `Mem.allocAt` sets the slot bytes to `none`, but `ClifThread.CStep` requires
        an event-free step to leave every byte memory unchanged, so `CStep` has no step into a
        callee with a slot. The fix, every piece beside the old definitions (whose theorems stay):
        `CStepI` (the thread state carries a ghost own-initialisation mask: the slot allocation
        clears it instead of touching the shared bytes, a CLIF store sets it, a load of an unset
        byte is stuck as in `Clif.run`; correspondence lemma with `Clif.run`, oracle check on the
        slot corpus); `RefinesT` (a position-dependent private set `PrivAt` and a freshness
        clause: after an unmatched own write at `a`, a CLIF read at `a` follows a matched own
        write at `a`) with `PrivCoh.realizes_of_threads_privT`; the thread-wide `PrivAt` is the
        union of the frames of the activations live at that position; `link_composeT`. The
        cross-thread premise becomes: other threads avoid the union over time of a thread's
        private sets (its stack) — a trusted program premise. **Frame disjointness (done,
        `FrameDisj.lean`)**: `Region` (an activation's frame and callee budget), `Frame`,
        `slotArea` (the CLIF slots `[spB + size, spB + frameSize)`, in the `Frame` and outside
        `frameF`'s stack part: `slotArea_frame`, `slotArea_not_frameF`), `frameF_frame`,
        `Nested A B` (the callee's region inside the caller's dead stack, `B.G = A.FK`),
        **`Nested.gfree`** (the callee's `RL.Wf.gfree` from the caller's), `Chain` (the live
        activations, innermost first), **`Chain.region_dead`**, **`Chain.frame_disj`** (distinct
        live frames are disjoint) and **`Chain.slot_not_F`** (every live activation's CLIF slots
        are outside the innermost activation's `RL.F`: the CLIF events, which avoid the innermost
        `RL.F`, avoid every live frame). Witness (`FrameDisjWitness.lean`): the compiled
        `atomic_load` nested in its caller with a `0x100`-byte callee budget (`nested_LC`,
        `wfRLy`, `chain_LC`, `frames_LC`, `slots_LC`). **`CStepI` (done, `ClifThreadI.lean`)**:
        `TStateI` (a `TState` and its mask `U`), `slotByte` (the bytes of the running and
        suspended frames' slots), `mix U B` (`B` with the masked bytes `none`), `CStepI` (`CStep`
        run on `mix U B`; the bytes after it are `mix U'` of the shared bytes with the write events
        applied; `U'` keeps only unwritten masked bytes or adds slot bytes of the new state),
        `CRunI`, `MaskOk` (masked bytes `none` in the own memory). **`cstepI_empty`**: with empty
        masks `CStepI` is `CStep`; **`cstepI_of_cstep`**: every `CStep` whose reads avoid the mask
        (`agrees_mix`, `applyEvs_mix`); `enterSlots_bytes`, `enterFunc_bytes` (`enterFunc` on any
        bytes: the placed slot bytes `slotZ` cleared, the rest kept), `slotZ_frameSlot`,
        **`cstepI_call`** (the call of a program function adds `slotZ` to the mask);
        **`cstepI_own`**/`cstepI_own_stuck` (single-thread correspondence: from a `MaskOk` state a
        `CStepI` reading the own memory is `Clif.step` of the state, to a `MaskOk` state; where
        `Clif.step` is stuck there is no `CStepI`). Witness (`ClifThreadIWitness.lean`): a call
        into `%g` with an 8-byte slot placed at `0x6F20` (`cstepI_callW`, `maskW`, `ownW`),
        `not_cstepW` (no `CStep` enters `%g`), `emptyW'` (with the bump allocator the old `CStep`).
        **Oracle check (2026-10-23)**: the 44 runtests files with stack slots through `Clif.run`
        (whose single-thread behaviour `CStepI` is, `cstepI_own`) and the Cranelift interpreter
        (`scripts/clif-filetests.sh`): 1148 agree, 7 disagree (the known i128 out-of-bounds
        `stack_store` with an instruction offset, in the baseline), **0 runs stuck on an
        uninitialised read**. cg_clif output (static must-initialised scan of the `bin-check`
        dumps, `stack_addr` + `load`/`store`, escaping slots exempt): potential loads of
        uninitialised slot bytes in fv-demo 288 (2,680 functions), survey 92 (1,702), deps 2,938
        (34,180), mostly enum/`Option` partial initialisation (the tag stored, the payload word
        loaded and returned or copied; e.g. fv-demo `bin-check/400b40aa77e2/fns/184.clif`: `store 2`
        to `ss0[0,4)`, `load.i32 ss0+4` returned) — `Clif.run`, and so `CStepI`, is stuck there.
        **`RefinesT` (done, `PrivCohT.lean`)**: `RefinesC` (the order- and pair-preserving part of
        `Refines`), `Unmatched`, `RefinesT MK Priv0 PrivAt` (`shared`: a source event avoids the
        private set at its image's position; `priv`: an unmatched Arm write is in the private set
        at its position; `fresh0`/`fresh`: a source read of a location private at the start, or
        written by an earlier unmatched Arm write, follows a source write there after that write),
        `Refines.toT` (constant private sets), `realizes_of_threads_fn` (`realizes_of_threads` with
        the runs as functions and the source property as a premise), **`src_of_refinesT`** (every
        Arm `rf` source of a source read is a CLIF initial write or an image: another thread's
        unmatched write by `StackDisjoint`, an own one or a private initial write by freshness and
        SC per location), **`realizes_of_threads_privT`**, **`privCoh_of_stackDisjoint`** (reads of
        a thread's stack read its own `po`-latest write: the run condition's justification).
        **Trusted program premise `StackDisjoint PA (PrivU Priv0 PrivAt)`**: no thread's events
        other than fences touch another thread's private locations at any time (the union over time
        of its private sets: its stack) — like the earlier "no thread writes another thread's
        private set" (above), now for the union over time; documented in
        `docs/decisions/arm-model.md`. Witnesses (`PrivCohTWitness.lean`): `refinesT_reuse` (a spill
        at 100, then a CLIF store and load of a slot at 100), `not_refines_reuse` (no fixed private
        set realizes it), `ret_threadsT` (`realizes_of_threads_privT` on `ProgWitness`).
        **Composition (done, `CallComposeT.lean`)**: `RefinesC.app`, **`RefinesT.app`** (private sets
        concatenate, `catP`; the locations not `Clean` at the end of the first segment are dirty at
        the start of the second), `clean_app`; `maskOf`, `CStepS` (`CStepI` with the mask in the
        thread state's bytes), `CRunS`; `RealizedT env p Bnd ls k c c' D D'` (private sets within
        the thread's bound `Bnd`, dirty sets at start/end), `RealizedT.zero`/`trans`;
        `FunRealG`/`SegOkG`/**`link_composeG`** (the linking induction for any realization with
        `zero`/`le`/`trans`), **`link_composeT`**, **`realizes_linkedT`** (program level, premise
        `StackDisjoint` for the bounds and start-dirty sets). Witnesses `CallComposeTWitness.lean`
        (`realizedT_trans0`, `funRealT_ext`, `linkedT_ret`). `SegOkG` for compiled activations
        and the generic call theorem on `link_composeT`: **done** (`CallSegOkGT.segOkG`,
        `funRealT_link`, `realizes_linked_calls`, above). The load-callee witness re-derived from
        it: **`CallSegOkGT.WitnessFull.realizes_call_fullT`** (the `CStepS` variant of
        `realizes_call_full`: `realizes_linked_calls` with one thread, every premise discharged —
        `PartsOk`/depth bound by the reachable states from the oracle entry state `csO`
        (`reach_inv`), `Env.empty`'s `EnvKeeps*`, the caller's `Ent` with budget `0x200`), and
        the rmw-callee witness: **`CallSegOkGT.WitnessRmw.realizes_call_rmwT`** (the link `linkR`
        of the caller and `atomic_rmw`, its LL/SC pair on the partition `a = 0 ∧ n = 8`, budget
        `0x240`). Open: a `CStepS` version of `program_correct` (multi-threaded `Clif.run` with
        masks).
  * **the prologue, from the ABI entry (done, `ArmAllocEntry.lean`)**: `stp_fplr_evs` (the
    prologue's `stp x29, x30, [sp, #-16]!`: one plain write at `sp - 16`, no exclusive);
    `q_init_lines` (`RegLevelFrame.q_init` with the prologue's lines, `LinesAt`, and its step
    count exposed); `prologue_evs`, `prun_prologue` (a precise run under `OkPriv` through the
    prologue is the single-core run, its one event a private plain write to the fp/lr slot);
    `refines_privW`; **`arm_alloc_refines_entry`**: every precise run under `OkPriv` from the ABI
    entry `R.s0` (`AbiCall`) realizes a run of the allocated code from `MConf.init … w₀` (any
    `BodyEntryW` world), `arm_alloc_refines_ls`'s conclusion (scope `MemScopeLS`), the prologue's
    write private (composed by `CallCompose.Refines.app`). Witness (`ArmAllocEntryWitness.lean`):
    `entry_premises`, `run_load_entry` (the compiled `atomic_load` from its ABI entry through the
    prologue, the saves, `args`, the spill and the `ldar`), `refines_load_entry`.
  * plain loads/stores **done** for the one-line forms (`ArmAllocLS.lean`, #460 + follow-up):
    `MemScopeLS` = `MemScopeB` ∨ `LSForm` (GPR/SIMD&FP load/store at a final mode, or at a stack
    mode whose offset `memFinalize` encodes as an immediate), `lsForm_oneEv` (24 final-mode and 4
    stack-mode `OneEvForm` instances; event equality from the closed forms `*_line_cf`,
    receptiveness from `CtlIndep`), `itemSim_ls`, **`arm_alloc_refines_ls`**; witness
    `ArmAllocLSWitness.ls_premises`. The stack offsets lowered through `x16` **done**
    (`ArmAllocLSX.lean`, #473): `OneEvPreForm` (an event-free `loadConst64` prefix, then one
    access; `oneEvPreForm_of_oneEv`), `oneEvPre_op` (the prefix's event-free steps, a run ending
    inside them has no event; they commute with the patch of the read bytes, `iterN_comm`;
    receptiveness `straightSem_preC` from `preMem`/`straightSem_pre`), the four instances
    `load_stackX_form` … `fpuStore_stackX_form`, `MemScopeLSX` = `MemScopeB` ∨ `LSFormX`,
    `itemSim_lsx`, **`arm_alloc_refines_lsx`**, `lsFormX_covered`; witness
    `ArmAllocLSXWitness.lsx_premises` (`R.Wf`, `MemScopeLSX`, `¬ MemScopeLS`) and `lsx_run`; one
    thread on the whole run `RealizeCompiled.thread_compiledLSX_full`;
  * kinds by `MInst.lines` (`Code.lines_kinds`, `VCodeEvents.cEvs_kinds`);
  * frame, spill and prologue accesses in `F s` (= `Priv`; the stack is per thread), read under
    `PrivCoh`;
  * atomic loops: failed iterations are extra reads, and the successful `ldaxr`/`stlxr` pair is
    the monitor pair `pairT`;
  * the canonical run (`cEvs`) and the allocated instruction's run access the same bytes: the
    per-instruction proofs (`OperandsSound`) give whole-state results only, so this needs either
    event-level versions of them or an argument from `OperandsSound` on every memory.
* **Composition (done, `FV/Concurrency/ThreadCompose.lean`).** Layers 3 and 4a are exported as
  `Thin` traces (`PrepThread.prep_thin`, `prep_thin_csem`, `AllocThread.alloc_thin`); layers 2
  and 4b refine a *prefix* of their target (up to where the source stops), so composing needs
  truncation: `Thin.trans`, `Thin.take` (a prefix of the source is `Thin` to a prefix of the
  target, the whole one for the whole source), `Refines.take` (a prefix of the source refines
  the target cut before the first image of a dropped source event, when target steps have at
  most one event: Arm steps, `prun_len`), `Refines.congr`.
  * **`isel_alloc_refines`** (layers 2, 3, 4a): a run of the allocated code from the entry
    (`MTRun` under `csem`/`cEvs`) is realized up to `Stop` by a `CRun`, `Refines Maps`, no
    private location. Witness (`ThreadComposeWitness.lean`): `isel_alloc_refines_fA` on the atomics
    function as compiled (`prepare`, the spill allocation `spillAlloc`, both accepted).
  * **`arm_isel_refinesE`** (all layers): given layer 4b's run-level refinement of a precise Arm
    run from the allocated code's entry configuration (`refines_of_itemSim`'s form, realized up
    to an end condition `E` that is a parameter; `q_init` gives that configuration,
    `MConf.init`), the Arm run (a prefix of it: up to `E` or the CLIF thread's `Stop`) realizes
    a `CRun`, `Refines Maps (PrivA R) (MonPair …)`; `arm_isel_refines`: `E` the allocated
    code's `Done`; `csemV_none`: without GOT-pinned calls the activation's semantics is `csem`.
* **`Realizes` for compiled code (done for the memory scope, `FV/Concurrency/RealizeCompiled.lean`).**
  `Compiled env p RA cs s`: what the pipeline gives one thread (the activation `RA.Wf`,
  `MemScope`, no GOT calls; layer 2's `DriverHyp` and checks; the CLIF entry state `cs` related
  by `MR` to the entry world; `Q ∧ AInv` at `MConf.init` for the Arm state `s`).
  `thread_compiled`: a precise Arm run under `OkPriv` realizes, on a prefix (all of it, or until
  the CLIF thread stops or the allocated code is done), a CLIF thread run from `cs`, the target's
  atomic pairs its own monitor pairs (`monPair_take`, `Refines.pairT_congr`); `crun_states`.
  **`realizes_compiled`**: for `n` compiled threads, every well-formed execution of these prefixes
  whose `rmw` is the monitor pairs and in which no thread's events touch another's private set
  is `Realizes`d by CLIF threads from the `cs i` (`realizes_of_threads_priv`). `wf_noReads`:
  traces without reads have a well-formed execution (`coW`). Witness (`RealizeWitness.lean`):
  `driverHyp_of` (the driver hypothesis of any checked function), `compiledF` (every premise of
  `Compiled` for the compiled `fence; return`: `Γ` with the activation's private set `RA.F`, empty
  CLIF memory), `realizes_nil` (the contract on the empty run). Forward runs
  (`ArmAllocFwd.lean`): `step_fwd`, `prun_fwd` (precise runs reading the thread's own bytes
  through straight-line lines, `LinesAt`), `move_fwd`/`moves_fwd` (through moves, `Q` after them,
  events private, of the kinds of the moves' lines), `q_head` (the first line of the remaining
  code at the pc). Witness (`RealizeWitnessFence.lean`): **`realizes_fence`**, the precise run of
  the compiled `fence; return` from the state after the prologue through its 18 saves (private
  `plainW` writes) and its `dmb ish` (`dmbEv`) satisfies `realizes_compiled`'s premises; every
  execution of its realized prefix is `Realizes`d by a CLIF thread from `csF` (one exists,
  `wf_noReads`). The realized prefix covers the whole run (T2j, below).
* **Loads, stores, LL/SC loops, plain memory (done, T2l/T2m #446–#470).** `CompiledB`/
  `realizes_compiledB` (loops and branches, `arm_alloc_refines_br`) and `CompiledLS`/
  `thread_compiledLS`/**`realizes_compiledLS`** (also plain loads/stores, `MemScopeLS`,
  `arm_alloc_refines_ls`); `Compiled` and `CompiledB` are corollaries. `Exec.Wf.rmw_imm` ranges
  over events only (`Exec.ev`, §2), so executions with successful Arm LL/SC pairs are well formed.
  Forward runs through the loops with the monitor tracked (`ArmAllocLoopFwd.lean`: `step_fwdS`,
  `prun_quiet`, `rmw_fwd`, `cas_fwd`, `rmw_lines`, `cas_lines`). Witnesses, each on the function
  as `lowerFunction`/`prepare`/`spillAlloc` compile it, every premise of `Compiled`/`CompiledLS`
  discharged: `WitnessL.realizes_load` (`atomic_load.i64`, an `ldar`), `WitnessS.realizes_store`
  (`atomic_store.i64`, an `stlr`), `WitnessMP.realizes_mp`/`mp_reads` (two compiled threads,
  message passing: the `ldar` reads from the `stlr`), `WitnessR.realizes_rmw`
  (`atomic_rmw.i64 add`: `ldaxr; add; stlxr`, the execution's `rmw` the prefix's monitor pairs,
  `rmw_full`: on the whole run it relates the `ldaxr` read to the `stlxr` write) and
  `WitnessC.realizes_cas` (`atomic_cas.i64` with the expected value present: `ldaxr; cmp; b.ne;
  stlxr`); generic `WitnessR.realizes_pair` (one thread, private plain prefix then an exclusive
  pair), `RealizeExec.wf_rmw`. Layer 4b with the stack offsets built in x16:
  `arm_alloc_refines_lsx` (#473). Open: mixed-size accesses (T2i, #317).
* **The realized prefix covers the whole run (done, T2j #473, `FV/Concurrency/ThreadProgress.lean`).**
  Layer 4b could end the realized prefix where the allocated code is `Done` — returned, trapped,
  or *without a step* — while the CLIF thread could still step. Excluded by a progress argument
  through every layer: where layer 2's realized prefix is the whole VCode run, the run's last
  configuration has a `VStep` (`IselThread.SimResP`/`SegResP`, `pure_segP`, `term_segP`,
  `mem_segP`, `mem_completeP`, `isel_refines_entryP`: a run ending inside a segment follows the
  driver's forward run of that segment — on the thread's own bytes for a memory statement,
  `IselStep.vstep_of_starN`/`vstep_of_vtrun` — which steps there); `prepare` keeps it
  (`PrepThread.prep_fwd`, `prep_thinP`), register allocation turns it into a step of the
  allocated code (`AllocThread.alloc_thinP`, `sim_progress_at`), composed in
  `ThreadCompose.isel_alloc_refinesP`; layer 4b ends at a configuration still related to an Arm
  state (`ItemSim.withRel`, `arm_alloc_refinesQ`, `arm_alloc_refines_lsQ`), where a step of
  covered code (`CoveredCode`, `coveredCode_of_ls`) is a thread step with the precise footprint
  (**`srcStep_of_mstep`**: `ifoot_csem` on the error-free aligned world `StRel` gives; the
  footprint's reads come first, `agrees_cEvs`), which `Done` excludes. **`arm_isel_refines_full`**,
  `thread_full_of_sim`/`thread_compiledLS_full`, **`realizes_compiledLS_full`** (and the `B`/plain
  versions): every thread's realized prefix is its whole Arm run, or a CLIF thread run realizing it
  stops there (`Covers`; `Stop`: no step — returned, trapped, undefined behaviour — or an
  `atomic_cas` on read-only data); `realizes_compiledLS` is now its corollary. The witnesses on
  the whole run: `covers_full` (a covering prefix is the whole run when the CLIF thread cannot stop
  at its start and its first step's events cannot sit in a strict prefix), `WitnessL.one_full`,
  `WitnessR.pair_full`; **`WitnessL.realizes_load_full`**, **`WitnessS.realizes_store_full`**,
  **`WitnessMP.realizes_mp_full`** (both prefixes whole, so `mp_reads` applies),
  **`WitnessR.realizes_rmw_full`**; `WitnessC.realizes_cas_cov` (`Covers` only, and `WitnessC1.realizes_cas_full` on the whole run: the same compiled function with the replacement `1`, `pair_full_rd` with the read value `cstep_rd`; the former: that `atomic_cas`
  stores the value it finds, and a CLIF `atomic_cas` leaving the bytes unchanged is a step with the
  read alone, which realizes the run up to the `ldaxr` and returns).
* **Backward from forward.** The layers are forward per-step simulations; `Refines` is
  backward (from the actual Arm trace to a CLIF run). The bridge is determinism of each level
  given its read values (receptiveness): the source run is the one reading the target's values
  (layer 3: `prep_back`; the Arm level: `ArmPrecise.stepEvs_setMem`).
* **Widening** (§3c): extern calls that touch memory, per-thread allocation metadata,
  `tls_value`.

**Layers 1–4 discharge `Realizes` for compiled code (#311, #38 closed by T2m), on realized
prefixes that cover the runs (T2j, #473).** `realizes_compiledLS_full` gives the contract
`program_correct*` assume, for threads running compiled functions in the scope `MemScopeLS`
(atomic loads/stores, `atomic_rmw`/`atomic_cas` LL/SC loops, fences, branches, plain
loads/stores), each thread's realized prefix its whole Arm run or ending where the CLIF thread
stops, with calls through `CallCompose.realizes_linked`; the witnesses above show it on
`atomic_load`, `atomic_store`, message passing and `atomic_rmw` on the whole runs, and on
`atomic_cas`. The stack offsets built in x16 are in layer 4b's scope (`arm_alloc_refines_lsx`; one thread on
the whole run: `thread_compiledLSX_full`). Remaining scope widening tracked separately: mixed-size
accesses (T2i, #317).

**Frame shapes after #479 (Cranelift's frame, for whoever resumes atomics after #567).** The
register-level layer now follows Cranelift's prologue/epilogue: `prologueLines saves size` is
`stp x29, x30, [sp, #-16]!; mov x29, sp`, then the callee-save pushes (int pairs, then float
pairs), then `sub sp`; the epilogue mirrors it and ends `ldp x29, x30, [sp], #16; ret`. What the
`FV/Concurrency` layers see: `q_init_lines` is stated over `prologueLines saves size`;
`StRel` has a new field `fp : R.af.frame = true → xreg 29 s = spv R.s0 - 16` (x29 is part of the
world, so a move keeps it: `xreg29_sw`); `FrameKeep F s s'` has a third conjunct
`Arm.r (.GPR 29#5) s' = Arm.r (.GPR 29#5) s` (`corr_tac`/`atom_tail` prove it); `ret_machine`
takes `QA` (`Q ∧ AInv` or a return tail `RetTail`) and additionally concludes that each saved
register holds its entry value. `ArmAllocItem`/`ArmAllocMove`/`CallEnterArm` were updated for these.

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
| T2h (#311) | Discharge `Realizes`: the per-thread event-level refinement of compiled code (isel/prepare/register-level layers re-proven as footprint-preserving simulations with interference; §3e) | layer 0 **done** (`ThreadRefine`: reduction `realizes_of_threads`, composition `Refines.trans`); layer 1 **done** (precise footprints `ArmInstFoot`, VCode thread semantics `VCodeThread.VTStep`); layer 1b **done** (event kinds `VCodeEvents.cEvs_kinds`); precise Arm labels (`ArmPrecise`) and private coherence (`PrivCoh.privCoh_of_consistent`) **done**; layer 3 **done** (`PrepThread.prep_refines_csem`); layer 4a **done** (`AllocThread.alloc_refines`); layer 4b run level and event-free items **done** (`ArmAllocThread.refines_of_itemSim`, `arm_alloc_refines_noev`); layer 2 steps 2a–2e **done** (`VCodeAddr.cEvs_avoid`, `SegRun.vtrun_patch`, `SegShape.segShapeCheck`, `IselClif.access_in_events`, assembly from a match `IselRefines.isel_refines`); layer 4b's LL/SC loops **done** (`ArmAllocThread.rmw_op`, `cas_op`, `arm_alloc_refines_loop`), block-ending branches **done** (`goto_op`, `arm_alloc_refines_br`), plain loads/stores **done** (`arm_alloc_refines_ls`, the x16 stack offsets `arm_alloc_refines_lsx`); all layers on the whole run **done** (T2j: `RealizeCompiled.realizes_compiledLS_full`); calls: the linking induction **done** (`CallCompose.link_compose`), compiled callers/callees on witnesses **done** (`CallSeg.WitnessC.realizes_call_full`; a caller of the compiled `atomic_rmw`: `CallSeg.WitnessCR.realizes_call`), layer 4b pausing at calls and returns **done** (`ArmAllocThread.arm_alloc_refines_lsC`), the return coverage **done** (layer 2 `IselEntry.isel_refines_entryR`, all layers `RealizeCompiled.thread_full_of_simR`); open: the generic call theorem (layer 4b's pc invariant on linked machines, the layers' relation at a call and after its return) |
| T2f (#304) | Rust/C++20 (RC11 with all orderings) → the Cranelift contract: cg_clif's ordering strengthening as a theorem (§3d), and the program-level chain `program_correct_rust` | **done** |
| T2g (#305) | Widening: LSE atomics (`has_lse`: not emitted in our configuration, covered by the table, `Lse.lse_maps`), the full `aarch64.cat` (`Armv8Full`, monotonicity `consistent_frag`), `i128` atomics (rejected by cg_clif) | **done** |
| T2i (#317) | Mixed-size accesses (a mixed-size model instead of `NoOverlap`) | open |

The existing single-core assumption stays in the trusted base of `E2E.backend_correct_final`, and
#38 is closed by T2h/T2m (§3e: `realizes_compiledLS` discharges the per-thread contract for
compiled code in the scope `MemScopeLS`). T2a–T2c replace "a multi-core memory model is a project of its own" by a proven
mapping at the execution level: every Armv8 execution of Cranelift's atomics code is consistent
for the Cranelift contract, and SC (an interleaving) when the program is race-free.
