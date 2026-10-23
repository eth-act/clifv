# SEM1: reads of uninitialised stack bytes (#537)

Status: design (2026-10-23, agent UninitSem). Implementation has not started; the decision in §5 is
open.

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

## 5. Decision needed

- A: precise to native Cranelift code generation, but a weeks-long prophecy/count proof through
  the linking and executable inductions, including @codygunton's files.
- B: precise and small (a pass, a few instance theorems, a CLIF-level simulation), but it changes
  the generated code. With `Z` it costs stock agreement on all slotted functions. With `Z'` it
  costs about 3 % of agreement plus a must-init soundness proof.

Recommendation: **B with `Z` first**. It closes the gap for every measured run soonest. `Z'`
then recovers stock agreement. A stays possible later, e.g. for an unmodified-code mode.

## 6. Heap (separate gap, SEM2)

`BaseOk.baseKeepsAllocs`/`baseNoAlloc` require base externs to allocate nothing whenever a program
callee has slots (`EnvKeepsAllocs`, `NoAllocEnv`). An access to a heap block that `malloc`
returned during the outside call is then out of bounds in CLIF memory (a `notrap` access is
`stuck`). The only way around this is an entry memory that pre-declares the whole future arena,
plus an environment that simulates the allocator byte-exactly. That is impractical: 44/53 survey
and 5/21 fv-demo test runs do such accesses. Uninitialised heap *bytes* are never read (0 runs),
so a fix needs only allocating externs: the allocation must avoid the stack and the code, which is
what the `valid` clauses of `OutsideCall` already demand of the entry memory. This needs its own
issue and plan.

## 7. Interaction with the atomics layer

`ClifThreadI.CStepI` carries a ghost mask of unwritten own slot bytes and makes a read of a masked
byte stuck, which matches today's `Clif.run`.
- Under B the mask stays as it is, and `Z P` never reads a masked byte, so `cstepI_of_cstep`
  applies to every step of `Z P`.
- Under A a masked byte has a value, so the mask places no constraint on the oracle runs; the
  `CStepI` lemmas stay true for `init = none`.
