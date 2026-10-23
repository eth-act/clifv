# SEM1: reads of uninitialised stack bytes (#537)

Status: decided (2026-10-23): design A, route (i) of §5.1, in progress (agent UninitZ). The
design-B prototype and its checks in §8 remain a test tool only (`clif-filetest --zero-slots`).

## 1. The gap

`Clif.run` stores memory bytes as `Option (BitVec 8)`. A stack slot is allocated with `none`
bytes: `Mem.alloc` through `bumpSlots`, or `Mem.allocAt` through `placeSlots`, both in
`enterSlots`/`enterFunc`. A `load` of a `none` byte is `stuck` (`Mem.load`/`readBits`), and so
is `memcmp` over one (`Clif.Rust.memcmp`). `memcpy`/`memmove` copy the `none` along. Cranelift
has no such undefined behaviour: the load returns whatever bytes are there. cg_clif's output
relies on this, for example:
- an `Option`/enum built partially, then returned whole (`store 2 -> ss0[0,4)`, then
  `load.i32 ss0+4`);
- the copy of a partially written `sret` slot.

`ArmRefines`/`ExecRefines` map `.stuck` to `True`, `Front.bundle_correct_*` conclude only about
`.returned`/`.trapped`, and the linking lemmas assume a run that is not stuck. So such a run gets
no guarantee, end to end.

### 1.1 Where exactly

- **Per function, nothing is missing.** `E2E.backend_correct_final` takes the CLIF entry state
  `cs` as a premise. `ClifEntry` does not constrain `cs.mem`, and `MemRel` constrains only live
  `some` bytes, which must equal the Arm bytes. An entry memory whose slot bytes are the Arm
  bytes at the body entry (`BodyEntry.mem`: the prologue's memory equals the entry's) is therefore
  already covered.
- **The entered function of an outside call, nothing is missing either.** `ClifRun` and
  `OutsideCall` leave `cs.mem` free (`OutsideCall.bytes`/`valid` again constrain only `some`
  bytes and allow allocations in the entered function's slot area). Choosing slot bytes equal to
  `r`'s memory covers that activation's stale reads under `Link.DeadCleanup.compileExe_correct*`
  today.
- **Program callees are the gap.** A callee entered during the run gets its slots from
  `enterFunc`, so with `none` bytes (`LinkArm.initState_mem`). A stale read in any callee makes
  the whole run stuck.

### 1.2 Measurements

Static: AtomicsCalls8's must-init scan of the cg_clif dumps, deduplicated (the earlier
150/92/1764 counted dump files). Distinct functions with a possible read of unwritten
explicit-slot bytes: fv-demo 75, survey 46, deps 879. Escaped slots are exempt, so the scan
under-counts.

Dynamic: a qemu 10.2.1 TCG plugin with a shadow stack and heap
(`notes-uninit/uninit_plugin.c`, driver `uninit_dyn.py`, branch `agent/uninit-sem`). It runs
`cargo fv test --lean-link --verified` executables, each test alone. Every access by
Lean-compiled code is classified:

| category | meaning | fv-demo runs (of 21) | survey runs (of 53) |
|---|---|---|---|
| `stack_uninit` | load of a slot byte not written since its activation began, the activation being a program callee of the current outside call | 9 (135 loads, 34 fns) | 46 (3,039 loads, 149 fns) |
| `stack_uninit_outer` | the same in the activation entered from outside code (covered today, §1.1) | 0 | 0 |
| `stack_uninit_cp` | a byte copied uninitialised by a `memcpy`/`memmove` from Lean code | 1 (6) | 0 |
| `heap_uninit` | load of a heap byte not written since `malloc` | 0 | 0 |
| `memcmp_uninit` | `memcmp`/`bcmp` from Lean code over an uninitialised byte (up to the first difference) | 0 | 0 |
| `heap_fresh` | any access to a heap block allocated during the current outside call | 5 (138) | 44 (71,564) |

So uninitialised *bytes* matter only on the stack, and only in program callees. `heap_fresh` is a
different gap (§6).

## 2. Requirements

1. Every run in §1.2's `stack_uninit`/`stack_uninit_cp` categories gets the end-to-end guarantee.
2. Old statements, names and meanings stay as they are. New semantics and theorems go under new
   names. Standard axioms only, and a non-vacuity witness for every new top-level theorem.
3. The new statements are precise: the source run reads definite bytes, not a value existentially
   chosen per read.
4. The new semantics is checked against oracles: Cranelift's interpreter (zero-filled stack),
   native runs (`clif-native`), and runs of the compiled code.

## 3. Design A: slot bytes from an oracle, instantiated by the Arm memory

**Semantics.** Add `Place.init : Option SlotInit := none`, with
`SlotInit := { bytes : Nat → Nat → BitVec 8, next : Nat }`. When `init = some ini`, `enterSlots`
places the slots with `Mem.allocAtInit base size (ini.bytes ini.next)`, whose bytes are
`some (ini.bytes ini.next a)`, and increments `next`. With `init = none` nothing changes.
`LinkArm.PlaceAt` pins the whole `Place`, so every existing linked statement keeps its meaning.
`Clif.run` stays deterministic for a given oracle.

**Instantiation.** `O k a` is the Arm memory at `a` when the *k-th* program-function body is
entered in the executable machine's run from `r`. That run is deterministic and `BodyEntry.mem`
holds, so the definition is concrete: a function of `r` and the file. New theorems
`Link.DeadCleanup.compileExe_correct_init{,_peak}` and `Front.bundle_correct_raw_init{,_peak}`
take `cs.mem.place = some {…, init := some ⟨O r, 0⟩}`.

**The obstacle.** At the `k`-th callee entry, the CLIF slot bytes must equal the Arm bytes there
(`MemRel` at the callee's entry). Those bytes hold the residue of every earlier activation:
spills, callee-saved registers, frame records, outgoing stack arguments, and slots that CLIF
already freed. CLIF does not model any of these. The only thing that can supply them is an
oracle about the *future* Arm run, i.e. a prophecy indexed by the activation count.

The linking proofs are built per call: `LinkSys.Cond`/`progX` choose a CLIF memory per call;
`CrunOk.link` composes per-function runs; `DeadCleanupExecBytes.act_sim` is an induction over
activations. Their invariants mention only the current Arm state. To discharge the prophecy, all
of them must carry an *entry count*: the Arm segment of a callee run contains exactly as many body
entries as the CLIF callee run has activations, in the same order. That is a new conjunct in the
induction statements of `LinkArm` (`progX`, `Cond`, the call lemmas), `LinkSys`'s `CrunOk`, and
the executable-level `act_core`/`act_sim` (in @codygunton's `DeadCleanup*` files and their
`Production*`/`Semantic*` copies). Estimate: weeks, mostly re-proving those inductions with the
stronger statement. Without the count, the oracle is ∃-chosen globally, and the proof still needs
the same prophecy argument.

Alternatives inside A:
- **Nondeterministic reads** (a load of an uninitialised byte returns any value): a relational
  `Clif.run`, so every linking proof would be redone over relations. Rejected: more work than the
  count, and less precise.
- **A CLIF-tracked dead stack** (`allocAt` keeps the bytes previously in CLIF memory, instead of
  erasing them): wrong for spill/save residue, which CLIF never sees, so `MemRel` fails at the
  callee's entry. Rejected.

## 4. Design B: the compiler zeroes slots; the source semantics is zero-initialised

The compiled code does not zero slots today, and that was the argument against zero-initialisation
(#537). We control the backend, so we can make it zero them.

**Transformation.** `Z : Program → Program` adds `v = iconst 0; stack_store v, ssN+off` for every
8/4/2/1-byte piece of every explicit slot, at the head of the entry block, before the first
original instruction. The pieces are opcodes of subset E, and the frame layout does not change.
Variant `Z'` zeroes only the slot bytes that a must-init analysis cannot prove written before
read, treating escaped slots conservatively; it then needs a soundness proof of the analysis
(§5).

**Compiler.** `compileExeZ S := compileExe (Z S)`. `lean-link` and `cargo fv --lean-link` call
it. `lean-backend` applies `Z` before the mid-end, so per-function and executable reports agree.

**Theorems.** All of them are instances of the existing ones on `Z S`; no linking proof changes.
- `Link.DeadCleanup.compileExeZ_correct{,_peak}` and `Front.bundle_correct_rawZ{,_peak}`:
  `ExecRefines … (Clif.runLoop B.env (Z P) (M+1) cs)`.
- `Clif.Z_noUninitSlot`: no run of `Z P` reads an uninitialised slot byte. Every slot byte is
  written before the first original instruction runs.
- `Clif.Z_refines`: a run of `P` that returns or traps has a run of `Z P` with the same
  outcome. The returned values are equal. The final memory agrees on every live byte that is
  initialised in `P`'s and has `some 0` where `P`'s has `none`. The added steps only write slot
  bytes that `P` would have read as `none` and been stuck on. So a theorem about `Z P` covers
  every guaranteed run of `P` with the same or a stronger claim.
- Scope: `InScopeP (Z S)`/`InScopeIn (Z S)` from the same predicates on `S`, or decided on `Z S`
  by `lean-link --verified` (it already decides on its input).

Meaning: the executable behaves exactly like the CLIF program with zero-filled slots, which is one
of the behaviours Cranelift allows. That is a deterministic, precise statement. It equals
Cranelift's interpreter, whose stack is zero-filled.

**Costs.**
- Run time: one store per slot piece per activation. cg_clif's `opt_level=none` slots are small,
  e.g. fv-demo's flagged functions have 8–32 bytes of slots. To be measured before merging.
- Stock agreement (#140, @codygunton): every function whose code changes loses byte agreement with
  stock Cranelift. With `Z` that is every function with explicit slots; with `Z'` it is about
  3 % (75 of 2,680 fv-demo functions).

## 5. Decision (2026-10-23)

**A.** User rule: the generated code stays byte-for-byte what stock Cranelift emits, and
Cranelift does not zero slots. So B (`Z`/`Z'`) is out. Its prototype stays a test tool
(`clif-filetest --zero-slots`) and is never used by `lean-link`/`cargo fv`.

**Finding ([#556](https://github.com/eth-act/clifv/issues/556)): §3's plan is not enough.** The
linking evaluates a program call by the *canonical* run (`LinkSys.progX` from `canon g uses w`,
built from the VCode world). It transfers the result to the actual machine by non-interference
over the masked fields and `F` (`CalleeOkG.os`, `XNI`, the `NeedNI` clause of `LinkSys.Thm`).
Under A a callee's result depends on stale bytes in its caller's dead stack (in `F`). Those
bytes include earlier callees' saves of `x19`–`x28`, their spills and frame records. These are
regalloc-chosen values outside the world, which differ between the canonical and the actual run.
Example: `h1` saves the actual `x19`, then `h2` reads it through a half-written slot. So "one
VCode outcome that every machine entry realises" and `CalleeOkG.os` are false for stale-reading
runs, whatever the entry count.

### 5.1 Two code-preserving routes

- **(i) Prophecy-indexed calls.** Slot bytes come from the oracle (`Place.init`, §3). The
  per-function theorem gets a call semantics indexed by the activation's call count. Its results
  are those of the activation's actual run, a prophecy fixed by the machine entry state. This
  replaces the world-only `ExtSem` at the calls: a new `CalleeOkG` variant, required only along
  the actual run, threaded through the VCode → reg-level (regalloc) → Arm simulation. The linking
  is then stated per actual activation, without canonical runs or NI. The entry count of §3 comes
  on top. Per-function semantics outside calls: unchanged. An activation's own slot bytes are in
  its entry memory, which `backend_correct_final` already leaves free.
- **(ii) Nondeterministic/poison reads.** An uninitialised byte reads as any value, and the theorem
  says the compiled run matches *some* source run. A run that reads no uninitialised byte is
  pinned down exactly as today, but a stale read is no longer pinned to the bytes the machine
  reads. It does *not* avoid the canonical-run/NI problem. The source run the machine matches
  must pick, at every stale read, the value the actual run reads. That choice is again a prophecy
  of the actual run, aligned with the calls, and the VCode-level callee semantics becomes
  relational: the same backend-deep change as (i). In addition, the nondeterminism sits in every
  `load` (`Mem.load`/`readBits`), so every load lemma of the instruction-selection proofs
  (`IselMem*`, `IselAtomic*`, `LegalMem`, …) and `Clif.Rust.memcmp` would change. (i) touches
  only `enterSlots`.

**Chosen: (i).** It needs strictly less work than (ii) and gives the more precise statement: the
exact bytes, not any bytes. It is implemented in small PRs, leaf first:
1. semantics: `Clif.SlotInit`, `Place.init` (default `none` = today's semantics, so every
   existing statement keeps its meaning), with a native check that the values the source reads
   are the stale bytes the native run reads;
2. per-function layer: the oracle entry states under `backend_correct_final`, then the
   prophecy-indexed callee contract through the reg-level simulation;
3. linking (`LinkArm`, `CrunOk`) per actual activation, with the entry count;
4. executable (`act_core`/`act_sim` variants beside @codygunton's, #140 note),
   `compileExe_correct_init{,_peak}`, `Front.bundle_correct_raw_init{,_peak}`.

The gap stays open until step 4 lands. That is months of work, not weeks.

### 5.2 Step 1 (semantics), as built

- `Clif.SlotInit` (`bytes : Nat → Nat → BitVec 8`, `next`) and `Place.init : Option SlotInit :=
  none` (`FV/Clif/Mem.lean`). `Clif.enterSlots` places a covered function's slots as before, then
  `Clif.initSlots`: with `init = some ini` and slots, the activation is the `ini.next + 1`-th one
  with slots; its slot bytes become `ini.bytes (ini.next + 1) a` (`Mem.fillAt`) and the oracle
  advances (`Place.advance`). Slotless activations and `init = none` are unchanged. So a
  self-`return_call` of a slotless function still gives back its memory (`selfTail_mem`).
- Every existing statement keeps its meaning. `LinkSys.PlaceAt`, `PlaceInv`, `PlacedInv`,
  `bounded_placed` and the `LinkArmUClif` place lemmas pin `init = none` (`⟨sps, frames, none⟩`).
  Internal lemmas, conclusions kept:
  - `enterSlots_place`, `enterSlots_sps`, `enterFunc_sps`, `initState_place`,
    `ClifThreadI.enterSlots_bytes`, `enterFunc_bytes`, `cstepI_call` and
    `CallEnterClif.cstepI_call_entry` take an `init = none` premise; the general forms (which say
    what happens to `init`) are `enterSlots_place_init`, `enterSlots_sps_init`,
    `enterFunc_sps_init`.
  - `linkEnvR_keepsPlace`, `linkEnvN_keepsPlace`, `linkEnvRX_keepsPlace` and
    `LinkSys.envRX_keepsPlace` concluded `EnvKeepsPlace`/`XEnvKeepsPlace` of the linked
    environment. That is false with the oracle for every premise on the memory (the memory is
    quantified inside the conclusion, and a program callee with slots advances `init`), so those
    names are retired; the forms on memories without the oracle are `linkEnvR_keepsPlace0`,
    `linkEnvN_keepsPlace0`, `linkEnvRX_keepsPlace0`, `LinkSys.envRX_keepsPlace0`
    (`EnvKeepsPlace0`/`XEnvKeepsPlace0`). All their callers pass `init = none`.
- Native check: `clif-native --stale-seed n` fills the stack below the harness's `sp` with
  `(n + 37·(a mod 16)) mod 256`, and `clif-filetest --stale-seed n` runs `Clif.run` with the same
  oracle (slots at `Backend.slotLayout` offsets below a 16-aligned `sp`). On the prototype's 310
  leaf functions × 5 runs = 1,550 runs per seed (seeds 90 and 195): 1,070 agree, 288 are native
  `SIGSEGV`s on wild pointer arguments (`Clif.run` stuck, oracle-error), and 192 disagree, all
  `Clif.run` `stuck` on an out-of-bounds slot access (a load wider than its slot, e.g. `load.i64`
  of a 5-byte `ss0`, 40 functions; natively it reads the neighbouring bytes): no guarantee is
  claimed there. 934 runs give different native results under the two seeds (stale reads); 742
  of them are in functions without a disagreement, and `Clif.run` reproduces every one of them
  under both seeds.

### 5.3 Step 2 design: a call counter in the VCode world

The VCode semantics is generic in its world type (`VState V W`, `ISem V W`), and `csem` fixes
`W = Arm.ArmState`. Plan:
- `W := Arm.ArmState × Nat`, the second component counting the activation's calls.
- `ExtSemI.call : Nat → …`: call `i` gets the actual run's `i`-th callee result.
- `csemI`: `csem` on the first component, a call bumping the counter.
- CLIF ↔ VCode relation `RelW cm w.1 ∧ (counter of cm's slot-byte oracle) = base + entries of
  the first w.2 calls`. Unlike a ghost inside `Arm.ArmState`, this relation is stable under
  `SameWorld` (`MRStable`), because `SameWorld` acts on `w.1` only.
- The call contract (`CalleeOkG`/`CallSoundCtlG`) is required only at the states of the
  activation's own machine run, from its entry `s0`. There the prophecy `ExtSemI` is the
  machine's result by definition.

Non-call instructions lift from `csem` to `csemI` unchanged (`csemI i uses (w, n) = (csem i uses
w).map (·, n)`), so the `Refines`/`MemRefines` obligations transfer generically. The reg-level
simulation (`regLevelCorrect_world`) has to be redone with the counter in `StRel` and the
run-restricted contract.

## 6. Heap (separate gap, SEM2)

`BaseOk.baseKeepsAllocs`/`baseNoAlloc` require base externs to allocate nothing whenever a program
callee has slots (`EnvKeepsAllocs`, `NoAllocEnv`). An access to a heap block that `malloc`
returned during the outside call is then out of bounds in CLIF memory (a `notrap` access is
`stuck`). The only way around this is an entry memory that pre-declares the whole future arena,
plus an environment that simulates the allocator byte-exactly. That is impractical: 44/53 survey
and 5/21 fv-demo test runs do such accesses. Uninitialised heap *bytes* are never read (0 runs),
so a fix needs only allocating externs: the allocation must avoid the stack and the code, which is
what the `valid` clauses of `OutsideCall` already demand of the entry memory. Tracked in
[#547](https://github.com/eth-act/clifv/issues/547).

## 7. Interaction with the atomics layer

`ClifThreadI.CStepI` carries a ghost mask of unwritten own slot bytes and makes a read of a masked
byte stuck, which matches today's `Clif.run`.
- Under B the mask stays as it is, and `Z P` never reads a masked byte, so `cstepI_of_cstep`
  applies to every step of `Z P`.
- Under A a masked byte has a value, so the mask places no constraint on the oracle runs; the
  `CStepI` lemmas stay true for `init = none`.

## 8. Prototype and checks (branch `agent/uninit-sem`, not merged)

`Opt.zeroSlots` (design B's `Z`, `FV/Opt/ZeroSlots.lean`) and `clif-filetest --zero-slots`.
Test input: every leaf function among the static scan's findings with integer
parameters/returns, 310 functions (`notes-uninit/gen_uninit_runtests.py`), each on 5 argument
tuples. Compared with the Cranelift interpreter (`clif-oracle interp`, zero-filled stack):
- without `Z`: 742 runs `stuck (read of uninitialised memory)`;
- with `Z`: 0 such runs, and 1,070 runs agree with the interpreter;
- the remaining 314 disagreements are out-of-bounds accesses through the synthetic pointer
  arguments (the interpreter does not check them), not slot reads.

Run-time cost of `Z` on the test runs: 0.94 (fv-demo) and 1.70 (survey) extra stores per Lean
activation, about 0.4 per load executed by Lean code (`notes-uninit/zcost.txt`).

Design A, statement preservation: with the oracle inside `enterSlots`, several internal lemmas
quantified over every memory become false on oracle states: `ClifThreadI.enterSlots_bytes`
(slot bytes masked to `none`), `LinkArm.initState_mem` (callee slot bytes `none`), and
`enterSlots_place` if the counter lives in `Place`. They would need an `init = none` premise, or
the oracle semantics would have to be a separate copy of the interpreter. Either way that adds to
A's cost.

