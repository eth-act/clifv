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

## 3. Theorem shape

Execution level (FV/Concurrency, no dependency on the existing proofs):

1. `Concurrency.Armv8.atomics_sc` — in an Armv8-consistent execution of the fragment, the acquire
   and release accesses are SC: `acyclic((po ∪ com)|(A ∪ L))`.
2. `Concurrency.Mapping.armv8_to_clif` — **compilation correctness of the mapping** (C11 → Armv8
   style, Lahav et al. PLDI 2017, Podkopaev et al. POPL 2019): if an Arm execution is the image of a
   CLIF execution under the table of §1 (`Compiled`: each CLIF event's kind maps to its Arm kind,
   the extra Arm events are the `ldaxr`s of failed LL/SC iterations, `rmw` pairs are `po`-adjacent)
   and is Armv8-consistent, then the CLIF execution (the Arm execution restricted to the source
   events) is consistent for the Cranelift contract. Per-operation lemmas: `po` between atomics is
   in `bob` (`ldar`/`stlr`/`ldaxr`/`stlxr`), `hb ⊆ po ∪ ob⁺` with release/acquire end points,
   `dmb ish` orders every pair across it (`fence`), the exclusive pair gives atomicity.
3. `Concurrency.Clif.drf_sc` — DRF-SC for an execution: consistent and race-free ⇒
   `acyclic(po ∪ com)`.
4. `Concurrency.Mapping.armv8_drf_sc` — 2 + 3: a race-free CLIF execution compiled to Arm is SC.
5. `Concurrency.Exec.sc_interleaving` — a finite SC execution has a rank (interleaving position)
   increasing along `po ∪ com` in which every read reads the latest same-location write before it,
   and no same-location write falls between the two halves of an `rmw`.

Code level: `Concurrency.Code` classifies `Backend.Insn` by memory-event kind and proves that
`MInst.lines` produces, for each atomic `MInst`, exactly the Arm kinds of the table (and only plain
kinds for the other instructions), so `Compiled` is the table of the code we emit.

Every theorem gets a concrete non-vacuity witness (small litmus executions).

## 4. Testing (the oracle)

qemu is not weak-memory faithful (TCG on an x86 host is close to TSO), so it cannot show that a
relaxed outcome is possible; herd7's `aarch64.cat` verdicts are the oracle.

* `FVTest/Concurrency/Litmus.lean`: the classic tests on the emitted instructions (MP, SB, LB,
  IRIW, 2+2W, R, S, CoRR, CoWR, atomic increment) with herd7's Armv8 verdict for each. Forbidden
  outcomes are proven forbidden in the Lean model (for every consistent execution); allowed outcomes
  are proven allowed by a consistent witness execution. A test where the model and herd7 differ must
  be a dependency test (the model is weaker by construction, §2).
* `scripts/litmus-qemu.sh`: each test as an aarch64 musl binary (`asm!` threads, the exact
  instructions Cranelift emits) run many times under `qemu-aarch64-static`; every observed outcome
  must be allowed by the Lean model (observed ⊆ allowed). This checks the model is not too strong.

## 5. Sub-issues

| Id | Item | State |
| --- | --- | --- |
| T2a (#299) | Execution graphs, the Armv8 fragment, the Cranelift contract, theorems 1–5 (`FV/Concurrency/*`) | this WP |
| T2b (#300) | Code-level classification of `Backend.Insn`/`MInst.lines` (`FV/Concurrency/Code.lean`) | this WP |
| T2c (#301) | Litmus tests in Lean + qemu harness | this WP |
| T2d (#302) | Per-thread event semantics of the Arm model: the run of one thread as a trace of memory events with an exclusive monitor (failing `stlxr`, the `cbnz` retry); the existing single-core model is that semantics against an SC memory with a monitor that never fails | open |
| T2e (#303) | Program level: multi-threaded `Clif.run` (interleavings), DRF-SC for programs (the prefix argument over T2d's traces), and the whole-program statement composing theorem 4 with `backend_correct_final` per thread | open, needs T2d |
| T2f (#304) | Rust/C++20 (RC11 with all orderings) → the Cranelift contract: cg_clif's ordering strengthening as a theorem | open |
| T2g (#305) | Widening: LSE atomics (`has_lse`), mixed-size accesses, `i128` atomics, the full `aarch64.cat` (`dob`, `dmb.ld/st`) | open |

The existing single-core assumption stays in the trusted base until T2e is done; T2a–T2c turn its
"a multi-core memory model is a project of its own" into a proven mapping at the execution level.
