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

## 2. The models (decision)

**Executions.** Axiomatic, herd/cat style, in the formulation of the Arm ARM (B2.3) and
Pulte et al., *Simplifying ARM concurrency* (POPL 2018). An execution over an event type `E`:
thread `tid`, direction `R`/`W`/`F`, location `loc`, program order `po`, reads-from `rf`,
coherence `co`, `rmw` (exclusive pair / atomic update); `fr = rf⁻¹;co`; `com = rf ∪ co ∪ fr`.
Well-formedness `Exec.Wf`: `po` a strict order within a thread, total on each thread; `rf` from a
write to a read of the same location, functional and total on reads (initial writes are events);
`co` a strict total order on the writes of each location; `rmw` relates a read to its write, same
thread and location, `po`-adjacent. Locations are abstract (no mixed-size accesses: Rust's atomics
of a type are accessed at that type; a mixed-size model, Flur et al. POPL 2017, is out of scope).

**Arm side: the Armv8 axiomatic model, restricted to the fragment.** Event kinds `plainR`, `plainW`,
`acqR` (`ldar`), `relW` (`stlr`), `acqXR` (`ldaxr`), `relXW` (`stlxr`), `dmb` (`dmb ish`, a full
barrier). `A = acqR ∪ acqXR`, `L = relW ∪ relXW`.

* internal: `acyclic(po-loc ∪ rf ∪ co ∪ fr)`;
* atomic: `rmw ∩ (fre; coe) = ∅`;
* external: `acyclic(ob)`, `ob = obs ∪ aob ∪ bob`, `obs = rfe ∪ coe ∪ fre`, `aob = rmw`,
  `bob = po;[dmb];po ∪ [L];po;[A] ∪ [A];po ∪ po;[L]`.

These are clauses of the official `aarch64.cat`; the omitted ones (`dob` dependencies, the
`rfi;[A|Q]` part of `aob`, `po;[L];coi`, `dmb.ld`/`dmb.st`, `Q`) only *add* order. So the model
here is weaker than Armv8 and allows a superset of its executions: every theorem of the form "every
consistent execution …" proven here holds for real Armv8. The cost: tests that rely on dependencies
(e.g. `MP+dmb+addr`) are allowed here but forbidden by Armv8; the litmus table records them.

**CLIF side (the Cranelift contract).** Kinds `naR`, `naW`, `scR`, `scW`, `fence`; `At = scR ∪ scW`.
`sw = [scW];rf;[scR]`, `hb = (po ∪ sw)⁺`, `eco = com⁺`.

* coherence: `irreflexive(hb; eco?)` (RC11);
* atomicity: `rmw ∩ (fr; co) = ∅`;
* SC atomics: `acyclic((po ∪ com)|At)`.

A *race* is a pair of distinct conflicting events (same location, one a write, not both atomic)
unordered by `hb`. RC11's `acyclic(po ∪ rf)` (no out-of-thin-air) is deliberately not part of the
contract: Armv8 does not provide it for plain accesses, and a load-buffering cycle through plain
accesses is a race, undefined behaviour in Rust.

**Why this composes with the single-thread refinement.** The bridge is DRF-SC: for a race-free
execution every consistent execution is sequentially consistent, and an SC execution is an
interleaving in which every read sees the latest write to its location. Each thread's slice of an
interleaving is a run of that thread against a sequential memory, which is what `Clif.run` and
`E2E.backend_correct_final` already describe (the single-core assumption is exactly "the other
threads' writes happen between my steps").

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
| T2e (#303) | Program level: multi-threaded `Clif.run` (interleavings), DRF-SC for programs (the prefix argument over T2d's traces; `hb` with thread spawn/join edges, so initialising writes are ordered), and the whole-program statement composing theorem 4 with `backend_correct_final` per thread | open, needs T2d |
| T2f (#304) | Rust/C++20 (RC11 with all orderings) → the Cranelift contract: cg_clif's ordering strengthening as a theorem | open |
| T2g (#305) | Widening: LSE atomics (`has_lse`), mixed-size accesses, `i128` atomics, the full `aarch64.cat` (`dob`, `dmb.ld/st`) | open |

The existing single-core assumption stays in the trusted base of `E2E.backend_correct_final` until
T2e is done. T2a–T2c replace "a multi-core memory model is a project of its own" by a proven
mapping at the execution level: every Armv8 execution of Cranelift's atomics code is consistent
for the Cranelift contract, and SC (an interleaving) when the program is race-free.
