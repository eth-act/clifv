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

### 5.4 Step 2, as built so far (leaf PRs)

- #568 `FV/Backend/Proof/VCodeSemI.lean`: `ExtSemI` (`call : Nat → …`), `ExtSemI.at`/`.const`,
  `MInst.isCallI`, `csemI`; `csem_call_congr` (only calls read `ExtSem.call`); world-map
  simulation lemmas for VCode and allocated-code runs (`VStep_mapW`/`_liftW`,
  `MStep_mapW`/`_liftW`, `vstar_*`, `mstar_*`); `vstar_csemI_const{,_lift}` (one `ExtSem` for
  every call: today's runs).
- #570 `VCodeSemISeq.lean`: `seqRun_csemI_noCall`, `LowerInstOk.csemI` (call-free lowerings).
- #573 `VCodeSemICall.lean`: `callsI`, `SeqEnd.liftI`, `seqRun_csemI_le1`,
  `LowerInstOk.csemI_le1` (at most one call: a CLIF call's lowering; the counter invariant
  advances by the calls).
- #575 `VCodeSemIDriver.lean`: `DriverSemG.csemI`, `LowerTermOk.csemI`; witness
  `driverSemG_csemI`. With these the generic `Driver.DriverHyp` fields `dsem`, `insts` and
  `terms` hold for the counted world once the per-index `csem` ones do.
- #643 (step 2f) `FV/E2E/LinkArmProph.lean`: the first worklist item below. `LinkSys.calleeRgn κ M g w`
  is `Cond`'s own callee region `StackBelow (frameDrop (A g).af + κ (M - 1) g) (spv w)` (the plan's
  `StackBelow K (sp w)`, inside `F` and outside the image under `Cond`); `worldP` overlays it by
  the prophecy `Pn` (`StaleRegion.overlay`), and `canonP`/`CondP`/`progXP` are
  `canon`/`Cond`/`progX` of that world (`progXP_eq`, by `rfl`). `XP … P n : ExtSem` is call number
  `n` (`progXP` with `P n`), i.e. the future `ExtSemI.at n`: `ExtSemI` cannot be imported next to
  `LinkArm` yet, because `VCodeSemI*.lean` and `FV/E2E/Pair.lean` both declare `VConf.mapW`,
  `SeqEnd.mapW`, `SeqEnd.mapW_succ` ([#640](https://github.com/eth-act/clifv/issues/640), fixed
  by #644: Pair imports `VCodeSemISeq` and drops its copies). (a) the world's own bytes give today's contract (`worldP_self`,
  `canonP_self`, `progXP_self`, `XP_call_self`); (b) the canonical state depends on the world's
  registers, program and bytes outside the region, and on the prophecy inside it only
  (`worldP_congr`, `canonP_congr`, `condP_congr`, `progXP_congr`); (c) `Cond` depends on registers
  and the memory outside `F` only (`cond_congr`), so `CondP ↔ Cond` (`condP_iff_cond`: the
  prophecy changes the canonical run, not the condition); `canonP_eq_overlay`,
  `sameWorld_canonP`, `mem_canonP_in`/`_out`, `r_canonP`, `program_canonP`. Witnesses
  `LinkArmProphWitness.lean` (on `LinkWitness.L` without an image, `sp = 0x8000`).
- #648 (step 2h) `FV/E2E/LinkArmProphThm.lean` (on #643, #644): `XPI … P : ExtSemI` (`XPI_at`: `.at n`
  is `XP … P n`, by `rfl`). The prophecy of a machine run: `callsBefore Mm fa base s i` counts
  the call states (`CallPc`) before step `i`; `ProphOk K c Mm fa base s P`: at each call state
  with `sp = c`, `P (callsBefore … i)` holds the state's bytes `StackBelow K c`; `prophOf` is one
  (`prophOf_call`, `prophOk_prophOf`). `MachEntryP … P`: `MachEntry` and `ProphOk (κ M g)
  (spv w₀) (mach M g) …` (the callees' budget below the body's `sp`). `ThmP κ M`: `Thm` with the
  outcome chosen after a prophecy `P` and realised by the `MachEntryP … P` activations (also in
  the NI clause, the same `P`): the counted VCode run's calls read `P`, so its outcome depends
  on it. `Thm.thmP` (one outcome for every prophecy) and `thmP` (it holds today at every depth).
  Deviations from the worklist: no `WorldEntryP` (with `PlaceAt`'s `init = none` it would be
  `WorldEntry`; with an oracle the statement also needs the oracle's agreement with the
  machine's slotted activation entries in call order, recursively through nested linked calls,
  which is the CLIF-side `PlaceAt`/`CrunOk` item); the counted machine count (`CallPc` states)
  must equal the VCode `csemI` counter, a proof obligation of the counted simulation (every
  `bl`/`blr` executed by an activation is a `call`/`try_call`'s `callInsn?`). Witnesses
  `LinkArmProphThmWitness.lean`.
- #651 (step 2i) `FV/E2E/RegLevelCorrectI.lean` (on #648): `ISem.counted sem` (step at counter `n` is
  `sem n`'s, the counter bumped by the calls; `csemI_eq_counted`), `csemVI` (`csemV` with
  `X.at n`; `csemVI_sub`), `MStep.counted_proj`/`_lift`, `Realizes.counted` (the machine
  realises the counted semantics under `Q` of the first components when it realises each `sem n`),
  `RL.Q_withX` (`Q` does not read `R.X`); `regLevelCorrect_world_atI`/`regLevelCorrect_worldI`:
  `regLevelCorrect_world` for the `csemVI` run from `(w₀, 0)`, machine `ArmStepX (XI.at 0) H fa`
  (it reads only `XI.sym`), with the callee contracts of **every** index. Not yet: the counter in
  the relation (`= callsBefore` of the machine run) and the contract only at the run's own call
  of that index. That needs, per realised segment of an item, the number of `CallPc` states
  (`1` for `call`/`try_call`, `0` otherwise): the existing `realizes_*` lemmas expose only the
  per-state `RL.GoodX`, which says every `bl`/`blr` state has *some* call's `CallPre`, not that it
  is the current item's; so every `realizes_*` case needs a variant with a per-segment fact (the
  states are at the item's own lines, as the `*W.lean` variants did for `WritesAt`). The static
  fact that only `call`/`try_call` emit `bl`/`blr` exists already (`lines_noCall`,
  `lines_callKeys`, `L_callKeys` in `FV/E2E/RegLevelCallSite.lean`, S10e). Witnesses
  `RegLevelCorrectIWitness.lean`.
- step 2j `FV/E2E/RegLevelCountI.lean` (on #651): the obligation and its lift. `countIn C step s n`
  (the `C` states among the first `n`; `callsBefore_eq_countIn`: the prophecy index is `countIn`
  of the call states), `stepC C step` (the machine paired with that count, `iterN_stepC`),
  `opCalls vc c` (`1` when `c`'s next item is a call), `MStep.counted_ctr` (a counted step adds
  `opCalls`); `RealizesC … C`: `Realizes` whose every segment passes `opCalls vc c` states of
  `C`; `RealizesC.counted`: from `RealizesC` at every index, `stepC C step` realises the counted
  semantics under `Q` of the first components **and counter = count**. Next: `RealizesC` for
  `realizes_all` with `C` the call states (`CallPc fa base` at the pc), i.e. the per-segment
  variants above, then `regLevelCorrect_world_atI` on `stepC` with the contract of index `n` only
  at the states whose count is `n` (`CallSoundCtlG` with that premise beside its `G`-keep one).
  Witnesses `RegLevelCountIWitness.lean`.

### 5.5 Segment locality: call states per realised segment (step 2k)

`FV/E2E/RegLevelNoCall.lean`: `RL.CallSt R u := CallPc R.fa R.base (pc u)` (the pc is a
`bl`/`blr` line of the activation), `RL.NoCallAt := ¬ CallSt`, `RL.GoodXN := GoodX ∧ NoCallAt`.
Every `bl`/`blr` is hooked (`Insn.not_call_of_hooked`), so a state at an unhooked line is no
call state (`RL.noCallAt_of_line`, `noCallAt_of_noCall`; `callSt_of_line` for the call line);
`RL.goodXN_execLinesG`/`goodXN_execLines` are the straight-line builders. This per-state fact
is all the count needs: we do not state "the item's own lines" as a range, because a non-call
item's segment can leave its lines (relaxed branches, veneers, trap sections) and none of
those is a call line either. Variants, new files beside the originals (the `*W.lean` pattern),
same hypotheses as the original:
- non-call items, `realizes_XN` in `RegLevelXN.lean`: `R.GoodX` replaced by `R.GoodXN` in the
  conclusion (`∀ i < n, R.GoodXN (iterN R.step i s)`); zero-length segments need none.
- `call`/`try_call`, `realizes_callN`/`realizes_tryCallN`: the contract restricted to states `P`
  (`CalleeOkGP P`, `CalleeTryOkGP P`: `CallSoundCtlG`'s obligation only at states with `P`;
  `CalleeOkG.p`/`CalleeTryOkG.p` restrict the old ones) and `hP : P s` at the segment's first
  state (the `bl`/`blr` state); conclusion: the original's and
  `∃ i0 < n, R.CallSt (iterN R.step i0 s) ∧ ∀ i < n, i ≠ i0 → R.NoCallAt (iterN R.step i s)`.
- composition `realizes_allC` (`RegLevelCorrectC.lean`): `RealizesCP … R.step (Q ∧ AInv)
  R.GoodX R.CallSt P` (`RealizesC` from the states `P`: per segment `countIn = opCalls`), via
  `countIn_zero_of`/`countIn_one_of` (`RegLevelCountP.lean`).
Files: core `RegLevelNoCall`, `MoveN`, `OpN` (`RunsAsN`), `GotoN` (`reach_*XN`), `NextN`
(`args`/`island`/`rets`/`udf` are zero-length); rest `GoodXN`, `CallN` (`symAddrN`), `TryN`,
`JTN`, `AtomicN`, `TlsN`, `FrameN` (`q_initN`, `ret_machineN`), `TrapN` (`trap_trapIfN`) (#657).
Not built (nothing uses them yet): `*W` call-state variants, the `UTry` raise, `trapT`/`haltTry`
and the `MemTrap` loop wrappers; add them when the linking needs them.

As built: `RegLevelCountP.lean`: `RealizesCP`, `RealizesCP.countedRun` (from `RealizesCP` at
every index `n` with precondition `P n`, where `P n` holds at the states of the run from `s0`
with count `n`: the machine with the count `stepC` realises the counted semantics under `Q`,
*counter = count* and *on the run*), `Realizes.ofStepC`, `OnCall Mm fa base s n u` (`u` is a
state of the run of `Mm` from `s` with `callsBefore … = n`), `onCall_of_run`.
`RegLevelCorrectC.lean`: `regLevelCorrect_world_atC`/`regLevelCorrect_worldC`:
`regLevelCorrect_world_atI`/`_worldI` (same conclusion) with the contracts of index `n`
required only at `OnCall (ArmStepX (XI.at 0) H fa) fa base s n`, i.e. at the activation's own
run where it has made `n` calls (the prophecy index of `ProphOk`). The prologue makes no call
(`q_initN`), so the counted VCode run's counter is the machine's call count. Witnesses
`RegLevelCorrectCWitness.lean` (`countIn` facts, `countedRun_any`, `worldC_const`). Next: the
refined contract below, with `P n` from `ProphOk` at the `OnCall … n` state.

**Refined call contract (next).** `X.call n` should be the *canonical* callee run from the
VCode world `w` with the callee's stack region (the addresses `StackBelow K (sp w)`, inside the
caller's `F`) overwritten by the prophecy `P n`: the actual machine memory there at the
activation's `n`-th call. This is a function of `(uses, w)`, so the CLIF-level contract
(`XCallsOk` at index `n`, for every related `(cm, w)`) comes from the callee's own theorem with
the slot-byte oracle built from `P n`. The machine-level contract (`CallSoundCtlG`) gets one more
premise beside its `G`-keep one: the state's region below `sp` holds `P n` (`n` from the VCode
counter via `StRel`). On the actual run it holds by the definition of `P n`, and the stale bytes
that broke #556 (earlier callees' saves, spills, frame records) are then the same in the
canonical and the actual run. Non-interference over the masked registers within one call is
kept as today.

Linking worklist for that contract (`FV/E2E/LinkArm.lean`, sizes as of `dbd6c21c`): an indexed
`canon` (`canon` overwrites nothing today: the callee's future stack comes from `w`) with the
region from `P n`, and the indexed `Cond`/`progX`/`X` (≈45 lines); `MachEntry`/`WorldEntry`/`Thm`
(≈60); `progCall` (≈390; its NI bridge for the newly exposed outgoing/slot regions may become a
direct realization, since those bytes are now the actual ones); `progResult` (≈100);
`progOsCore` (≈190) and `calleeOk`/`calleeTryOk`; `xni`/`progX_ni`; `thm_of`. On the CLIF side
`PlaceAt` (today `init = none`), `initState_mem` (today: every initialised callee-entry byte lies
outside the new slots) and `progCall`'s `hRel`. The local call index (VCode counter) and the
global activation count of the CLIF oracle differ (nested callees enter several activations);
`CrunOk` has to carry that correspondence.

**Step 2l, as built** (`FV/E2E/RegLevelCorrectP.lean`): `OnCallP Kp c P Mm fa base s n u` is
`OnCall … n u` plus "if `u` is a call state with `sp = c`, its `Kp` bytes below `c` are `P n`";
`onCallP_of_prophOk` (every `OnCall … n` state of a run with the prophecy `P` is `OnCallP`);
`CalleeOkGP.mono`/`CalleeTryOkGP.mono`; `regLevelCorrect_worldP`: `regLevelCorrect_worldC`
(same conclusion) for a prophecy `P` of the machine run (`ProphOk Kp c`), with the contracts of
index `n` needed only at `OnCallP … P n`. With `XI := L.XPI κ M g F P`, `Kp := κ M g`,
`c := spv w₀` this is the per-function input `progCall` needs: call `n`'s contract is
discharged by the callee's `ThmP` at the prophecy `P n`, and the premise is exactly
`MachEntryP.proph`. Witnesses `RegLevelCorrectPWitness.lean` (`onCallP_entry`,
`worldP_const` with `prophOf`).

**Count correspondence (design for `PlaceAt`/`CrunOk`).** The CLIF oracle counts slotted
activations globally (`SlotInit.next`, nested callees included); the VCode counter `n` counts
the activation's own calls. Do not relate them arithmetically inside the backend; instead:
- the oracle is a prophecy of the *whole* machine run: `bytes j` is the machine memory at the
  `j`-th slotted activation entry (the CLIF and the machine run enter activations in the same
  order: both are sequential and the linking simulates call for call), so the stale bytes the
  CLIF slot sees are by definition the bytes the machine slot holds;
- each activation carries its entry index `j0 = ini.next` (the `PlaceAt` field, no longer
  `none`), and a second prophecy `E k` = slotted entries made during the activation's call `k`
  (its callee's whole nested run, read off the machine run like `P k`);
- `RelW`/`CrunOk` invariant at VCode counter `n`: `cm.place.init = some ⟨bytes, j0 + slotted? +
  Σ_{k<n} E k⟩` (`slotted?` = 1 when the activation itself has slots). A call `n` hands the
  callee `j0' = that value`, and the callee's `ThmP` returns `next = j0' + E n`, which is the
  invariant at `n + 1`. `E` lives in `ThmP`'s outcome next to `P`, so the reg-level layer stays
  oracle-free (it never sees CLIF memory), and only the linking (`progCall`, `progResult`)
  touches the sum.


**Count correspondence, CLIF side (step 2m, `FV/E2E/LinkPlaceB.lean`).** Interface agreed with
the Arm side: the byte table `B j` is the machine memory at the `j`-th placed activation with
slots of the whole run (an activation entered with counter `j0` reads `B (j0 + 1)`, `initSlots`);
a callee run advances the counter by its own count `e`, and the caller's call `k` contributes
`E k :=` that `e`. Built: `SlotInit.adv`, `NextAdv m m' e` (oracle kept, counter `+ e`),
`EnvAdv`, `enterSlots_adv` (`+0`/`+1`), `PlaceInvB`/`placeInvB_step`/`runLoop_placeB`/
`initState_placeB` (a returning run advances by some `e`), `linkEnvR_adv`/`linkEnvN_adv` (the
linked environment advances when the base does; `envAdv_of_keepsPlace`: `e = 0`). Witnesses
`LinkPlaceBWitness.lean` (one slotted function: counter `0 → 1`, slot bytes = table entry `1`).


### 5.6 Linking on `ThmP`: the caller-family obstacle (2026-10-28)

Investigation for `thmP_of` (`ThmP κ (M-1) → ThmP κ M` on `XPI`), before reworking `progCall`.
In `LinkArm.lean` the induction hypothesis is used at exactly one place (`progCall`, the
`ih h hh Fh … hWE hm` call); every other item (`progOsCore`, `progOs*`, `calleeOk`,
`calleeTryOk`, `progResult`, `xCallsOk`, `xCallsIndOk`, `progX_ni`, `xni`) only threads it to
`progCall`. And `progXP … Pn uses w = progX … uses (worldP … w Pn)` by `rfl` (`progXP_eq`), so
each item for `XP … P n` is the `X` item at the overlaid world. The real change is `progCall`
with `ih : ThmP κ (M-1)`, and there `ThmP` as built (#648) is too weak:

- `progCall` chooses **one** callee outcome and realises it from **every** caller state `t` with
  `CallerOk F h uses w t` (`SameWorld F t w`: `t` may differ from `w` inside `F`, in particular in
  the callee region `calleeRgn` and the caller's frame). `xCallsOk`/`calleeOk`/`xni` rely on that
  universality: the actual machine state at call `n` is such a `t`, not the canonical state.
- `ThmP` gives one outcome per prophecy `P'` of the *callee's* run (`MachEntryP … P'`). The callee
  runs from two `CallerOk` states have prophecies `prophOf` that nothing relates (the region's
  bytes at the callee's own calls are stale bytes its earlier callees left below the caller's
  `sp`), so the outcome chosen for the canonical state's prophecy says nothing about the run from
  `t`. Same for `ThmP`'s NI clause, which assumes the *same* `P` for the run from `w₀'`.
- With `init = none` this is invisible (`Thm.thmP`: one outcome for all `P`). With `init = some`
  the callee's CLIF outcome reads the stale bytes, so the obligation is real.

What closes it (conservative: #648's statements stay; new names):

1. Restrict the family: the caller state at call `n` is `OnCallP … P n`, i.e. its callee region
   holds `P n`, the overlay of `worldP`. `progCallP` quantifies over `t` with `CallerOk F h uses
   (worldP … w Pn) t` **and** `∀ a, calleeRgn a → t.mem a = Pn a`.
2. **Prophecy determinism (the missing theorem):** two activations of `h` entered from states that
   agree on the registers `CallerOk` fixes, the image, the callee region and the stack arguments,
   and differ only on addresses the callee neither reads nor writes (`D`, as in the NI clause),
   have the same prophecy (`prophOf` equal at every index) and the same final bytes in the callee
   region. Stronger than `ActRet` (results, `MemRel`, memory outside `G` only). It needs a
   lock-step invariant of two machine runs against the same counted VCode run (both `RL.Q`-related
   to the same world at every segment boundary, so equal outside `frameWG`; inside `frameWG`
   equal because both store the same values and their stale bytes come from equal region bytes):
   a new reg-level theorem beside `regLevelCorrect_worldP`, and the callee's determinism
   inductively (`ThmPD`: `ThmP` whose NI clause takes `MachEntry` and *concludes* `ProphOk … P`
   and equal final region bytes).
3. Then `progCallP` takes `ih : ThmPD κ (M-1)`, picks `P' := prophOf` of the canonical callee run
   (`prophOk_prophOf`) and moves it to every `t` of the family by (2); the rest of `progCall` is
   unchanged at the world `worldP … w Pn`.

So the next Arm-side leaf is the two-run reg-level invariant of (2); the `LinkArm` items are
mechanical once `ThmPD` exists. CLIF side (#665): `Clif.NextAdv`, `EnvAdv`, `PlaceAtB`; the
slot-byte table `B j` (memory at the `j`-th slotted body entry, counted from 1: `initSlots` reads
`bytes (next + 1)`) is the canonical runs' bytes, which (2) makes equal to the actual run's.

Step 2n (`FV/E2E/LinkArmPlaceB.lean`, `SrcBoundedB.lean`): `LinkSys.PlaceAtB cm c ini` (`PlaceAt`
with `init = some ini`), `PlaceAtB.adv`; `Clif.runsOf_nextAdv`, `crun_advK`/`crun_adv`/
`crun_nextAdv` (a returning callee run `crun M` advances the counter, from `CrunOk.runs` and the
base keeping the oracle: `CrunOk` itself needs no oracle variant); `initState_memB` (the
`initState_mem` facts with `PlaceAtB`: an initialised entry byte is the caller's outside the new
slots or the table's entry `ini.next + 1` inside them; the entry is `PlaceAtB` at the callee's
`sp` with the counter `+1`, `+0` without slots); `SrcBounded.PlacedInvB`/`bounded_placedB`
(`bounded_placed` under `EnvAdv`). Witnesses `LinkArmPlaceBWitness.lean`: `LinkWitness`'s `f`
entered with the table `0xAB` has `0xAB` in its compiled slot at `slotAddr` (`initState_memB_f`).

Step 2o (`FV/E2E/LinkPlaceBCount.lean`): the invariant at VCode counter `n`. `LinkSys.counter_at`:
`h` entered from `PlaceAtB cm c ini`, memories `m 0 = cs.mem, …, m N` with step `k` advancing by
`E k` (a program call: `crun_nextAdv`) ⇒ `PlaceAtB (m N) (h's sp) (ini.adv (slotted h + sumTo E N))`,
i.e. `next = j0 + slotted? + Σ_{k<N} E k`; `NextAdv.unique` (the advance is determined by the
memories), `nextAdv_chain`. Witness `LinkPlaceBCountWitness.counter_f` (`f`, two calls `+2`, `+3`: `6`).

### 5.7 Prophecy determinism: the masked-register obstacle, and step 2m as built (2026-10-28)

**(2) as stated in §5.6 is false.** The `progCall` family (`CallerOk … w t`: `SameWorld F t w`)
and the canonical state (`canon`, registers of the VCode world `w`) agree on the *unmasked*
fields only; `StRel.world` is `SameWorld R.F s w`, so the machine's masked registers (x0–x28 but
x18, x30, the SIMD file) at a call are unrelated to the world's. Callee-saved registers flow into
the callee region: a callee `g` that does not use `x19` passes the caller's `x19` to its own
callee `h`; `h`'s prologue saves it into `h`'s frame, which lies in `g`'s callee region; at `g`'s
next call those stale bytes are part of `g`'s prophecy. So the prophecies of `g`'s runs from `t`
and from `canon … w` differ whenever `t`'s `x19` differs from `w`'s, and under `init = some` a
later uninitialised slot of a callee of `g` reads them (its CLIF outcome differs). Likewise
`g`'s final frame bytes hold the entry `x30` (the frame record), which differs between `t` and
the canonical state (`canon` sets `x30 := raStar`), so "equal final callee-region bytes" is
false for the caller's region; it can hold only for `g`'s own callee region, or with equal `x30`.

**Correction (decided conservatively, without changing code).** The determinism clause needs, in
addition to §5.6 (2): equal masked registers but `x30`/pc at the body entry, and equal bytes of
the activation's frame and callee region. For `progCallP` this means the canonical callee state
must take the masked registers from the actual call state as well: the prophecy of call `n`
carries the registers (`Pn` bytes *and* the masked register file at the `n`-th call state, read
off the machine run like `P n`), and `worldP` overlays both. The non-deterministic parts that
remain (base externs `L.Hb.call`/`L.Hb.tls` are arbitrary functions of the state; their leftover
bytes below `sp` and scratch registers are unconstrained by `CalleeOk`) need a new base-hook
premise in `Ok` (locality: from states equal outside a set `D` the hooks return states equal
outside `D`), `NeedNI`-guarded like `baseNI`. The reg-level lock-step itself can use the per-state
`RL.GoodX.reads` (D2: unhooked reads avoid `G` but code words) with the instruction footprints
(`FV/Concurrency/ArmInstFoot.lean`).

**Step 2m, as built** (`FV/E2E/LinkArmProphDet.lean`): the transfer half of (2), independent of
how the lock-step is established. `runX_lockstep` (a relation the steps keep relates the runs at
every index); `ProphStep K c fa base u u'` (same pc; at call states same `sp`, and with `sp = c`
the same `K` bytes below `c`); `callsBefore_congr`, `ProphOkUpTo` (`ProphOk` up to step `n`, the
callee's return: past it the two runs return to different addresses), `prophOkUpTo_congr`,
`prophOk_congr`, `prophOkUpTo_prophOf`/`prophOk_prophOf_congr` (**`P' := prophOf` of the
canonical run is a prophecy of every lock-step run**). `ThmPD κ M`: `ThmP` whose NI clause takes
`MachEntry`, plus the determinism clause with the corrected premises (masked registers but
`x30`/pc, frame and callee-region bytes, an activation from `w₀` with prophecy `P`) concluding
`ActRet` and `ProphOkUpTo (κ M g) (spv w₀) … P n`; `ThmPD.thmP`, `Thm.thmPD_of_not_needNI`.
Witnesses `LinkArmProphDetWitness.lean` (`prophOk_u1`: two different states in lock-step;
`thmPD_LU`: `ThmPD` at every depth for a program with a call). Next: the prophecy of registers
(`worldP` overlay of the masked file), the base-hook locality premise, the reg-level lock-step
giving `ProphStep` for two runs of one activation, then `progCallP` on `ThmPD`.

### 5.8 Register prophecy, deterministic base hooks, the two-state step (steps 2n, 2o, 2026-10-28)

**Step 2n** (`FV/E2E/LinkArmProphReg.lean`): `MaskedReg` (`Masked` but the pc; `maskedRegs`,
`mem_maskedRegs`), `regOverlay S w` (`w` with `S`'s masked registers: `r_regOverlay_in`/`_out`,
`regOverlay_self`, `sameWorld_regOverlay`), `prophStOf` (the *state* at call `n` of a run:
`prophStOf_call`, `prophOf_eq_mem`), `ProphRegOk`/`prophRegOk_prophStOf`, and the new contract
family `worldPR κ M g Pn Sn w := regOverlay Sn (worldP κ M g Pn w)`, `canonPR`, `progXPR`
(`progXPR_eq`: `progX` of `worldPR`), `XPR`, `XPRI` (call `n` with `P n` and `R n`);
`worldPR_self`/`progXPR_self`/`XPR_call_self` (with the world's own masked registers it is the
`P` family), `sameWorld_worldPR`. `worldP` and `XP`/`XPI` stay. For `progCallP` the register
prophecy is `R := prophStOf` of the activation's machine run, so at call `n` the actual state
has the masked registers of `R n` (`ProphRegOk`) and the canonical callee state from
`worldPR … (P n) (R n) w` agrees with it on every masked register but `x30` and the pc
(`canon` sets the pc; the callee entry's `bl` sets `x30`) — the determinism premise of `ThmPD`.
Witnesses `LinkArmProphRegWitness.lean`.

**Step 2o** (`FV/E2E/LinkArmBaseDet.lean`, `LinkArmStepDet.lean`): `StEqOut Z s t` (same
registers and program, same memory outside `Z`); `HookDet Hb BD` (from two `StEqOut Z` states with
`Z` strictly below `sp` a base call/TLS hook gives `StEqOut Z` states); `OkD` = `Ok` +
`baseDet : NeedNI → HookDet L.Hb L.BaseDest` (`Ok.okD_of_not_needNI`, `Ok.okD`). **Decision
(conservative):** the premise is about the *dead stack* only (AAPCS64 has no red zone, so an
extern never reads below its entry `sp` before writing it); differences above the hook's `sp`
(non-live caller-frame bytes, the NI set `D`) are not covered by it: those are bytes no CLIF
access reaches (`RelW` to the same CLIF memory), and the lock-step must keep them out of every
hook's and instruction's reads by the `GoodX.reads` argument, not by a hook premise. The
single-step half of the lock-step: `ReadsAvoid Z evs`, `stEqOut_exec_inst` (from
`footprint_exec_inst`/`agrees_instEvs`: an instruction whose read events avoid `Z`),
`stEqOut_stepi` (`stepiEvs`), `stEqOut_armStepX` (unhooked line, `HookedInsn`),
`stEqOut_armStepX_call` (hooks that keep `StEqOut Z`). Witnesses `LinkArmBaseDetWitness.lean`,
`LinkArmStepDetWitness.lean`. Note: `LinkArmStepDet` imports `FV.Concurrency.VCodeThread`
(the instruction footprints), like `FV/ArmFault/Step.lean` already does.

**Design changes found while building 2o (for the reg-level lock-step, item 3):**
1. *`x30` differs between the two runs* (`canon`'s callee entry returns to `raStar`, the actual
   one to the call site). `StEqOut` (all registers equal) therefore holds only from the first
   `bl` of the body on, and the frame record bytes (inside the frame, above the body `sp`, so
   outside the prophecy region) differ for the whole activation. The lock-step relation must be
   `StEqOut` up to the registers `{x30}` until the first call and the frame-record bytes in `Z`,
   which needs a *register* footprint: no instruction of the body but `bl`/`blr`/`ret` and the
   prologue/epilogue frame-record pair reads `x30` (Cranelift never allocates `x30`). The memory
   footprints exist (`ArmInstFoot`); a register footprint per `Insn` does not yet: that is the
   next leaf (per `Insn` constructor: the encoded word's `exec_inst` reads only its operand
   registers; `x30` is no operand of a lowered body `Insn`, checked on the compiled code).
2. *`ThmPD`'s determinism clause is too weak for its own induction (`thmPD_of`).* Inside `g`'s
   two runs, after a nested program call of `h` returns, the lock-step must continue with
   `StEqOut`-related states (the bytes `h` left below `g`'s `sp` are part of `g`'s next
   prophecy). `ThmPD` concludes only `ActRet` + `ProphOkUpTo`. The inductive statement needs, in
   addition: the two runs' states at the return are `StEqOut Z` for the differing set `Z` of the
   entries minus the callee region (registers equal but `x30`/pc). `progCallP` itself needs one
   use of the determinism clause only, of `ThmPDE` (3) (the caller's prophecy is of the *actual* run, so no determinism across the
   caller's calls is needed there): it uses the determinism clause once, from the canonical state
   to the actual call state `t` (`OnCallP` + `ProphRegOk` give the premises). So `progCallP` on
   `ThmPDE` (item 4, see (3)) is independent of item 3, and item 3 proves `ThmPDE` by induction
   (`thmPDE_of`).
3. *`ThmPD`'s determinism premises are on the wrong states (step 2p).* `MachEntry s w₀` relates
   the machine entry `s` to `w₀` only outside `F` and on the unmasked registers (`BodyEntryW`);
   the callee region lies in `F`. So two entries with the *same* `w₀` (take `w₀' := w₀`, `D := ∅`:
   every premise of the clause holds trivially) may hold different stale region bytes and masked
   registers, and their prophecies differ: the clause is false as soon as the callee calls before
   overwriting its region. `FV/E2E/LinkArmProphDetE.lean`: `EntryAgree K s s₀` (masked registers
   but `x30`/pc, the `K` bytes below `sp`, of the *machine entries*), `RetAgree`, and `ThmPDE`:
   `ThmP`'s clauses, `¬ NeedNI →` realisation from every `MachEntry` (the outcome reads no stale
   bytes), and under `NeedNI` `ThmP`'s NI clause (`MachEntryP … P`: `ThmPD`'s NI clause, for
   every `MachEntry` without a prophecy, fails for the same reason) plus the determinism clause between a `MachEntryP … P`
   entry `s₀` and a `MachEntry` entry `s` with `EntryAgree (frameDrop + κ M g) s s₀`, concluding
   `ActRet`, `ProphOkUpTo … s P n` and `RetAgree` of the two runs at step `n` (design change 2).
   `ThmPDE.thmP`, `Thm.thmPDE_of_not_needNI`; witnesses `LinkArmProphDetEWitness.lean`. `ThmPD`
   stays (it is not used by anything); `progCallP` and `thmP_of` use `ThmPDE`. In `progCallP` the
   entries are `enterAt (canonPR … (P n) (R n) w)` (`s₀`) and `enterAt t` (`s`): `EntryAgree`
   holds by `ProphRegOk` (masked registers but the argument registers: `R n`; argument registers:
   `CallerOk.regs`; `x30` is set by `enterAt`) and `OnCallP` (region bytes `P n` on both).

**Steps 2q–2s, as built (the linking items on `ThmPDE`).**
- `FV/E2E/LinkArmProgCallP.lean`: `progCallP` (`progCall` with `ih : ThmPDE κ (M - 1)`; the
  callee outcome is `ThmPDE`'s for `P' := prophOf` of the canonical callee run; its two caller
  families additionally assume agreement with `canon h uses w` on the masked registers but
  `x30`/pc and on the callee's frame and region `StackBelow (frameDrop h + κ (M-1) h) (spv w)`;
  under `NeedNI` the determinism clause from the canonical `MachEntryP` entry, without `NeedNI`
  the prophecy-free clause), `canon_agree` (the canonical state is in the families),
  `progOsCoreP`. Witness `progCallP_Lu`.
- `FV/E2E/RegLevelCorrectPR.lean`: `ProphRegOkM`, `OnCallPR` (`OnCallP` + the masked registers
  of `R n` at a call state with `sp = c`), `onCallPR_of`, `regLevelCorrect_worldPR`. Witness
  `onCallPR_u0`.
- `FV/E2E/LinkArmProgOsP.lean`: `setReg_self`, `placeArgs_self`, `canon_self_r`;
  `progOsCoreXPR` (`progOsCoreP` at `worldPR … (P n) (R n) w` from a call state with the masked
  registers of `R n` and `P n` in the `κ M g` bytes below its `sp`: the arguments `canon` places
  are the state's own, so `canon` keeps every register but the pc); `progOsP`, `progOsRegP`,
  `calleeOkP` (the call contract of `XPR … n` as `CallSoundCtlGP Q`/`CalleeOkGP Q` for every `Q`
  that gives those two facts at call states), `XPR_base`/`_none`/`_ind`/`_ext`. Witnesses
  `progOsP_Lu`, `calleeOkP_Lu`.

**Steps 2t, 2u, as built.** (a) `FV/E2E/RegLevelTryP.lean`: `calleeTryP_at`,
`calleeTryOkGP_of_call` (the `try_call` helpers at restricted states); `calleeTryOkP` in
`LinkArmProgOsP.lean` (witness `calleeTryOkP_Lu`). (b) `FV/E2E/RegLevelCorrectPRS.lean`:
`realizes_allC_sp` (the call states the composition hands the contract are segment starts, where
`StRel.sp : spOf s = R.spB`), `regLevelCorrect_world_atCS`/`_worldCS`/`_worldPRS` (contracts at
`OnCall(PR) … n u ∧ spOf u = spv s - frameDrop af`; same proofs). Witness `worldPRS_const`.

**(4) Register prophecy in the linking statement (steps 2v, 2w, 2026-10-28).** `ThmP`/`ThmPDE`
choose the outcome per byte prophecy `P` only (`MachEntryP`). With the register prophecy the
activation's VCode run uses `XPRI … P R`, whose callee results depend on `R` (the callee runs from
`worldPR … (R n)`), so the outcome is a function of `(P, R)`, and `R := prophStOf` of the machine
run depends on the activation `s`. Decided (conservative): `FV/E2E/LinkArmProphDetR.lean`:
`MachEntryPR` (`MachEntryP` + `ProphRegOkM (spv w₀) … s R`), `ProphRegOkUpTo`, `ThmPR`/`ThmPDER`
(`∀ P R`; the determinism clause also concludes `ProphRegOkUpTo … R n`), `Thm.thmPR`,
`ThmPDER.thmPR`, `Thm.thmPDER_of_not_needNI` (witnesses `LinkArmProphDetRWitness.lean`).
`ThmPR → ThmP` does not follow (activations with one `P` have different `R`); the CLIF side
(#665) needs only the outcome per actual run, so the induction is `thmPR_of : ThmPDER κ (M-1) →
ThmPR κ M` and the top-level statement instantiates `(P, R)` with the actual run's
`(prophOf, prophStOf)`. `FV/E2E/LinkArmProgCallPR.lean`, `LinkArmProgOsPR.lean`: `progCallPR`
(callee prophecies `(prophOf, prophStOf)` of the canonical callee run), `progOsCorePR`,
`progOsCoreXPRR`, `progOsPR`, `progOsRegPR`, `calleeOkPR`, `calleeTryOkPR` (witnesses
`LinkArmProgOsPRWitness.lean`).

**Remaining for `thmPR_of`.** (i) An indexed pipeline: `thm_of` goes through
`backend_correct_world_ni_pipeline` (CLIF → VCode with one `ExtSem` `X`, then
`regLevelCorrect_world`); `thmPR_of` needs it with `XPRI` (`csemVI`, the counted VCode run of step
2j) ending in `regLevelCorrect_worldPRS` with `hC n := calleeOkPR … (Q := OnCallPR … n ∧ sp)` (the
`Q`-facts from `OnCallPR` at `sp = spv w₀`, the region `κ M g` below it). (ii) `xCallsOkP`/
`progResultP` (the CLIF-side call contract of `XPR … n`: `progXPR` defined with the callee's CLIF
results; the slot bytes the callee's CLIF run reads are `P n`'s, the #665 `PlaceAtB`/`B j`
interface with UninitZ6b) and `xniP`/`progX_niP` (from `progCallPR`'s NI family). (iii)
`ThmPDER`'s determinism clause by the lock-step (§5.8 (1), (2)).

### 5.9 The CLIF → counted-VCode half: per-step contracts (UninitZ9, 2026-10-28)

**Finding.** With `init = none` (`WorldEntry`) `ThmPR` already follows from `Thm` (`Thm.thmPR`),
so the indexed pipeline matters only with the oracle (`WorldEntryB`, item (d)). There the
per-index callee contract `XCallsOk env … (RelW …) (XPRI.at n)` — for **every** CLIF memory `cm`,
VCode world `w` and argument list related by `RelW` — is false: the callee's CLIF run reads the
table entries from `cm`'s counter on, and those are the machine's slot bytes only for the actual
call (actual memory, arguments and index; a callee entered with other arguments enters other
nested activations than the ones the table recorded). The driver (`driver_correct`) consumes the
contracts per instruction for arbitrary related states (`LowerInstOk.run`); the rule theorems
fix one memory relation for the states before and after a call (`CallRulesCorrect`: `∀ isem :
Sem`, one `MR`) and `Sem`'s world is `Arm.ArmState`. So an index-dependent relation (counter
`c_n` before call `n`, `c_{n+1}` after it) cannot be threaded through the rule-level contracts,
and the index cannot live in the Arm world (every field `SameWorld` keeps is tied to the machine
by `StRel`, every other one breaks `MRStable`). `LowerInstOk.csemI_le1` (#573) with one `MR` and
a counter invariant `Q` is therefore not enough once the contract depends on `Q`.

**Decision (conservative: no rule-level, driver or semantics change; new files).** Contracts per
step of the actual CLIF run:
1. `Clif.Env.only env A`: `env` whose externs answer only invocations `A name vals cm` (`stuck`
   otherwise; the same names are defined). Every extern invocation of one `Clif.step` from `s`
   is at `s.mem` with the one name and argument list the step determines (`call`,
   `call_indirect` via `callExternAt`, `try_call`, `try_call_indirect`), so restricting to it
   does not change the step.
2. Each step of the simulation instantiates the existing `DriverHyp` with `sem := csem F ctx
   (XI.at n)` (`n` = the counter), `MR := RelW …` and the restricted environment
   (`instCalls_of_rules`, `termCalls_of_rules`, … unchanged), runs the existing one-step lemmas
   (`stmt_run`, `term_step_*`, `entry_step`) and lifts the segment run to `csemI` at counter `n`.
   The induction over the run (`sim_run_abi`'s, ≈100 lines) is redone with the per-step
   hypothesis; nothing in `LowerSim.lean` changes.
3. Call counts. The lift needs the executed part of a segment to contain at most one call, and
   the counter to advance with the CLIF run's extern calls. Non-call statements and non-`try`
   terminators: dynamic — the same `DriverHyp` with an `ExtSem` whose calls fail and an empty
   environment (its contracts are vacuous) still runs the segment, so no executed instruction is
   a call. `call`/`call_indirect`/`try_call(_indirect)`: the lowering emits exactly one
   `MInst.isCallI` instruction; this is a property of the ISLE lowering, stated as premises
   (`InstCallsOne f`, `TryCallsOne f`) until a rule-table certificate proves them.
4. The pipeline premise is per state: for `s` reached from the entry after `n` extern calls
   (`ReachN`), the contract of `XI.at n` for the environment restricted to `s`'s invocation. No
   counter invariant `Q` enters the simulation: the discharge (item (b)) reads it off the actual
   run (`counter_at` along `ReachN`), at the machine's `n`-th call (`OnCallPR`).

**As built (steps 3a–3e, branch `agent/uninit-z9`).**
- `FV/E2E/ClifEnvOnly.lean`: `Clif.Env.only`, `onlyFn` (+`_of`/`_of_not`), `Env.only_extern_eq`,
  `CallInv`, `IndInv`, `Invoked`, `stepCall_only`, `callExternAt_only`, `stepCallIndirect_only`,
  **`step_only`** (`step (env.only A) p s = step env p s` when `A ⊇ Invoked env p s`).
- `FV/E2E/IselSimI.lean`: `ExtSem.noCall`, `csem_noCall_call`, `csem_noCall_proj`, `MRI`,
  `callNum`, `ReachN`, `xCallsOk_none`/`xCallsIndOk_none`, `step_none_of_callNum`,
  `driverHyp_relW` (`iselSim_relW`'s `DriverHyp` for any contracts), `vTrapFrom_mapW`/
  `vRetFrom_mapW`, `callsI_*`, `InstCallsOne`, `segCalls_of`, `stmt_stepI_noCall`,
  `stmt_stepI_call`, `term_stepI`.
- `FV/E2E/IselSimITry.lean`: `TryCallsOne`, `term_step_tryI` (`term_step_tryP`'s proof copied,
  ending in the counted run: its `TermZone` star alone does not fix the number of calls, the
  block can be re-entered), `sim_runI`, **`iselSim_relWI`** (CLIF → `csemI` from counter 0).
- `FV/E2E/PrepareSoundW.lean`: `prep_soundW` (`prep_sound` for any world with `DriverSemG`; the
  original uses only `jump`/`retarget`). `FV/E2E/GotFlowI.lean`: `GotInvI`, `vRetFrom_gotVI`,
  `vTrapFrom_gotVI`.
- `FV/E2E/BackendWorldI.lean`: `ActEntryPR`, **`backend_correct_worldPRI`** (legacy `Compiled`
  path: `iselSim_relWI` → `prep_soundW` → GOT → `regLevelCorrect_worldPRS`).
- Witnesses `FV/E2E/IselSimIWitness.lean`: `step_only_ret`, `a2_callsOne`, `a2_compiled`,
  `a2_xcalls`, `a2_iselSimI`, `a2_worldPRI` (`LinkWitness`'s `a2`).

**Remaining for item (a).** The cleanup path (`CompiledCleanup`, the one `Link.DeadCleanup`
uses): CLIF → counted VCode for `valueSem` (the per-step lemmas above are stated for `csem`;
generalise them over a semantics family with the two facts they use: non-calls do not read
`X.call`, calls of `X.noCall` fail), `prune_correct` and the GOT flow counted, and the counted
value-semantics register level (`regLevelCorrect_world_value` → `…_valuePRS`, the chain of steps
2i–2u for `valueSemV`: the pure items have no call states, the call items are `csem`'s). Then
`backend_correct_world_ni_pipeline`'s NI clause counted, and the `CompiledEither` pipeline.
Step 3f, as built: `FV/E2E/DeadCleanupRealizesC.lean`: `realizes_value_allC`
(`realizes_value_all`'s proof on `realizes_allC`: each value step is matched by an `RL.sem` step
of the same configuration, so the segment's call-state count carries over). Step 3g, as built:
`FV/E2E/DeadCleanupRegLevelPRS.lean`: `valueSemVI` (the counted `valueSemV`),
`realizes_value_allC_sp`, `regLevelCorrect_world_value_atCS`/`_worldCS`/**`_worldPRS`** (copies of
`RegLevelCorrectPRS.lean`'s; `rets`/halt as in `DeadCleanupRegLevel.lean`). Next for the cleanup
path: generalise `IselSimI`/`IselSimITry`'s step lemmas and `sim_runI` from `csem F fctx (XI.at n)`
to a family `sem : Nat → Sem` (hypotheses: non-calls do not depend on the index; a probe `semB`
agreeing on non-calls whose calls fail; `seqRun_csemI_le1` for `ISem.counted sem`), instantiate
with `valueSem`; then `prune_correct` and the GOT flow for `valueSemVI`, and
`backend_correct_world_cleanupPRI`.

of the same configuration, so the segment's call-state count carries over). Next on that chain:
`realizes_value_allC_sp`, `regLevelCorrect_world_value_atCS`/`_worldCS`/`_worldPRS` (copies of
`RegLevelCorrectPRS.lean`'s with `csemVI` → the counted `valueSemV`, `realizes_allC_sp` →
`realizes_value_allC_sp`; the `rets`/halt cases as in `DeadCleanupRegLevel.lean`).

**Steps 3h–3j, as built (UninitZ10, branch `agent/uninit-z10`).** Item (a) is complete for both
compile paths.
- `FV/E2E/CountedFam.lean`: `NoncallIndep sem`, `ProbeOf semB sem` (for `sem : Nat → ISem CV W`,
  any world), `SeqEnd.liftW`, `counted_noncall`/`counted_call`, `counted_probe_proj`,
  `seqRun_counted_le1`; instances `noncallIndep_csem`/`probeOf_csem`,
  `noncallIndep_valueSem`/`probeOf_valueSem`. `IselSimI`/`IselSimITry`: the step lemmas and the run
  induction for any such family and memory relation (`stmt_stepG_noCall`, `stmt_stepG_call`,
  `term_stepG`, `term_step_tryG`, `sim_runG`); the `csem` statements (`stmt_stepI_*`, `term_stepI`,
  `term_step_tryI`, `sim_runI`) are unchanged, now instances.
- `FV/E2E/IselSimICleanup.lean`: `valueSemI`, `driverHyp_relW_cleanup`, **`iselSim_relWI_cleanup`**.
- `FV/E2E/BackendWorldCleanupI.lean`: `prune_correctW` (the cleanup simulation `star_sim` is
  world-generic, so `prune_correct` holds for the counted world; `returns_cleanW`/`traps_cleanW`),
  `pureForm_isCallI`/`cmpForm_isCallI`, `counted_pure`, `cmpOverwrite_counted`,
  `DriverSemG.counted`, `valueSemV_sub`, `gotInvI_step_value`/`_star_value`,
  `vRetFrom_gotV_valueI`/`vTrapFrom_gotV_valueI`, **`backend_correct_world_cleanupPRI`**
  (`backend_correct_worldPRI`'s conclusion for `CompiledCleanup`).
- `FV/E2E/CompiledEitherI.lean`: **`backend_correct_world_pipelinePRI`** (`CompiledEither`).
- `FV/E2E/PairDriverI.lean`: `counted_pair_proj₁`/`₂`, `noncallIndep_pair`, `probeOf_pair`,
  `xNI_none`, **`vcode_niI`**: the pair driver per CLIF step (family `pairSem (csem F ctx (XI.at
  n))`, `MRP`), with `XNI` of call `n` needed, like the callee contracts, only at the CLIF states
  reached after `n` calls and for the environment restricted to their invocation (decision:
  per-state, the same shape as `hX`; the old one-`X` `XNI` premise is the special case).
  `FV/E2E/PairDriverICleanup.lean`: **`vcode_niI_value`**.
- `FV/E2E/BackendWorldNII.lean`: `backend_correct_world_niPRI`, `backend_correct_world_ni_cleanupPRI`,
  **`backend_correct_world_ni_pipelinePRI`** (`backend_correct_world_ni_pipeline`'s two clauses,
  counted: `ActEntryPR` activations, `XTls F (XI.at 0)`; the two outcomes are identified by the
  world-generic `vRetFrom_det`).
- Witnesses `FV/E2E/BackendWorldCleanupIWitness.lean` (`DeadCleanupWitness.source`, the closed
  cleanup compilation that removes an instruction): `source_callsOne`, `source_xcalls`,
  `source_xni`, `cleanupPRI_applies` (through `backend_correct_world_pipelinePRI`),
  `ni_pipelinePRI_applies`.

Item (b) interface, as built: `FV/E2E/ClifEnvOnlyContracts.lean`: `xCallsOk_only_of`,
`xCallsIndOk_only_of`, `xNI_only_of` (the per-state premises from the contract at the admitted
invocations only, the shape to discharge at the machine's `n`-th call), `xCallsOk_only`,
`xCallsIndOk_only`, `xNI_only` (an environment's contract holds for each restriction, so the
one-`ExtSem` premises give the per-state ones for `ExtSemI.const X`); witness `source_only`.
`InstCallsOne`/`TryCallsOne` are theorems in #675 (UninitZ10b: `instCallsOne_all`,
`tryCallsOne_all`); the premise-free `*_PRIC` corollaries of 3i/3j are one-liners once both are on
main.

Next: item (b) proper (`thmPR_of` on `backend_correct_world_ni_pipelinePRI`: discharge `hX`/`hNI`
per state through `xCallsOk_only_of` from `progCallPR`/`calleeOkPR` at the machine's `n`-th call,
`counter_at` along `ReachN`), item (d) (`WorldEntryB`), item (e).

**Design notes for (b)+(d) (UninitZ10, not built).** With the oracle the CLIF outcome of an
activation depends on its byte table, and the table must be the machine's: entry `j` is the memory
at the `j`-th placed activation with slots that the whole machine run enters (§5.5). So the oracle
statement cannot choose the outcome before the machine activation, as `ThmPR` does for `(P, R)`:
the table, `P := prophOf` and `R := prophStOf` are all functions of the machine entry `s`. Proposed
shape: `ThmPRB κ M` = for every `g`, CLIF entry placed with `PlaceAtB cs.mem (spv w₀) ini`
(`WorldEntryB`) and machine entry `s` (`MachEntryPR … (prophOf s) (prophStOf s)`) whose run's
entry-order table agrees with `ini` from `ini.next` on (`TableOf s ini`: for the activation's
`n`-th call, the entries `ini.next + slotted g + sumTo E n …` are the callee run's, `counter_at`),
a returning CLIF run gives one counted outcome realised by `s`. The induction step (`thmPRB_of`)
uses `backend_correct_world_ni_pipelinePRI` with `XI := L.XPRI κ M g F (prophOf s) (prophStOf s)`
and discharges `hX` at the state `s'` reached after `n` CLIF calls with `xCallsOk_only_of`: only
the actual invocation (memory `s'.mem`, placed at the counter `counter_at` gives) and the machine's
`n`-th call (`OnCallPR`) are related, and the callee's CLIF run reads the table entries the callee's
machine run entered, i.e. `ThmPRB (M - 1)` for the callee with `ini.adv (counter)` and the
canonical callee run (`progCallPR`) — its entry-order table is the caller's table from that
counter on because the canonical callee state agrees with the actual call state on the region
(`P n`) and the masked registers (`R n`), the determinism clause (item (c), UninitZ10b's lock-step).

**Finding (UninitZ11, 2026-10-28): the `hX` of the design above cannot be discharged as stated.**
`xCallsOk_only_of` restricts the *CLIF* side to the actual invocation `(vals, cm)`, but its
premise still quantifies over every VCode `(uses, w)` with `ArgsAt ext.sig vals uses w` and
`RelW … cm w`. `ArgsAt` fixes only the low `ty.width` bits of a register argument (`VHolds`), and
`RelW` fixes neither `x29`/`x18`/flags/TPIDR nor the world bytes outside `cm`'s live allocations.
`XPR n`'s canonical callee state is built from `(uses, w)` (`canon` puts the full 64-bit `uses`
in the argument registers), so for two such `(uses, w)` the canonical callee runs can differ in
what they spill: Cranelift spills an integer register as 64 bits whatever its CLIF type. A later
nested callee whose slot overlaps that spill and reads it unwritten then reads different bytes in
the two runs, while the CLIF callee run, with the oracle `ini` fixed, reads one table entry. So
`XCallsOk … (XPRI.at n)` is false in general, and `EntryAgree` (the determinism clause) does not
apply either, since it needs the masked registers, argument registers included, equal.
Decision (to build next, no stage-1/stage-2 proof changes): a new call semantics `XPRB` that is
`XPR n` on the *actual* call and an ε-chosen related result elsewhere. `ActualCall n d uses w`:
`w` agrees with the machine's `n`-th call state `R n` (`prophStOf`) outside `F` (`SameWorld F`)
and the argument values are `R n`'s argument registers, 64 bits. Stage 2 (VCode → Arm,
`CalleeOkGP` at `OnCallPR … n`) only ever asks for the result at such `(uses, w)`:
`OperandsSoundCtlAtI` gives `SameWorld F s w` and `uses = useVals ops regs s` at the machine
state `s`, which is `R n` there, so `calleeOkPR` applies unchanged through `XPRB = XPR` on
`ActualCall`. Stage 1 (`hX`, per CLIF state, `xCallsOk_only_of`): at an actual `(uses, w)` the
canonical callee state agrees with the actual one on every register but `x30`/pc and outside `F`,
and on the region (`P n`), so `EntryAgree` and the determinism clause transfer the table, and
`ThmPRB (M - 1)` gives the related result; at any other `(uses, w)` the result is the ε-choice
of a related one, which exists because the CLIF invocation of call `n` is unique (`ReachN`,
deterministic run) and a world related to `cm'` exists (`w` with `cm'`'s bytes written; the
callee keeps the allocations, `runLoop_allocs`). Only program callees need this (base externs keep
`L.Ok`'s all-world contract), and only with `NeedSlots`. `XNI` is not needed for `ThmPRB`
(statement per actual activation, §5.1 (i)). Alternatives rejected: restricting the stage-1
contract to the counted VCode run's call states (needs `hX` variants through
`iselSim_relWI`/`sim_runG` and the pipelines); a `w`-independent `XI` (the actual callee result
cannot be shown related to `cm` in stage 1 without stage 2's invariant).

As built (UninitZ11, stage 1 of the decision): `FV/E2E/ExtSemGuard.lean`: `ExtSem.guard`,
`guard_of`, `guard_spec`, `CallPost` (the results `XCallsOk`/`XCallsIndOk` accept for a call),
`xCallsOk_guard`, `xCallsIndOk_guard`. `FV/E2E/RelWPatch.lean`: `patchW cm' w` (`w` with `cm'`'s
initialised live bytes), `relW_patchW`. `FV/E2E/CallPostExists.lean`: `valCV`, `outsOf`,
`callPost_only_exists` (one invocation), `invoked_unique`, `callPost_invoked_exists` (the
environment restricted to a state's invocation; premises: the returning invocation keeps the
allocations and symbols, and fixes the ABI return count). Next: `XI.at n` cannot depend on the
state, so the guard's `Q` uses the invocation of the call state with count `n`
(`InvokedN n := ∃ s, ReachN … s n ∧ Invoked … s`, single-valued in a deterministic run: the
invoking state is the last of its count's segment), plus `CallPost` antitone in the restriction
(`env.only A'` for `A ⊆ A'`) and an `xCallsOk_guard` for any `Q` implying `CallPost`; then
`XPRBI` and stage 2 (`guard_of` at `OnCallPR` states).

As built (UninitZ12, `InvokedN` and the stage-1 discharge): `FV/E2E/InvokedN.lean`:
`reachN_uncons`, `reachN_cmp` (the reached states lie on one path), `reachN_call_unique`,
`InvokedN`, **`invokedN_unique`**, `NoRetCall` + `noRetCall_of_linv`, `callNum_of_invoked`,
`invoked_sub_invokedN`, `callPost_invokedN_exists`. **Finding:** a `return_call` to an extern
has `callNum = 0` and its step can continue in the caller (`stepReturnCall` → `returnValues` →
`.next`), so a later call in the same run could have the same count and `InvokedN` would not be
single-valued. **Decision:** scope condition `NoRetCall` (no reached state ends in
`return_call`; cg_clif emits none; `callNum` is not changed), discharged from `Clif.LInv` for
`LinkFree` functions (the existing link scope already demands `linkFreeB`).
`FV/E2E/BackendWorldPRB.lean`: `ExtSemI.guardI XI Q` (call `n` is `(XI.at n).guard (Q n)`),
`CallPostN`, `InvokedRetOk` (the returning invocation keeps allocations and symbols; its
declarations agree on the ABI return count), **`hX_guardI`** (the per-state `hX` of the
counted pipelines for `XI.guardI (CallPostN …)`, any `XI`), **`backend_correct_world_cleanupPRB`**,
**`backend_correct_world_pipelinePRB`** (the `*_PRIC` theorems with `hX` replaced by `NoRetCall`
and `InvokedRetOk`; the NI clause is not carried: §5.1 (i)). Witnesses
`FV/E2E/BackendWorldPRBWitness.lean`: `InvokedNWitness.{invokedN_sCall, noRetCall_sCall,
invokedRetOk_sCall, hX_sCall}` (a state at `call fn0()` to a returning extern),
`DeadCleanupWitness.{prb_applies, prb_pipeline_applies}`. So `XPRBI := (L.XPRI …).guardI
(CallPostN …)`; stage 2 needs `guard_of` at the machine's call states.

**Item (d) statement layer, as built (UninitZ12): `FV/E2E/LinkArmTableB.lean`.** The linked
machine runs a program callee atomically (`pcall` = `linkedCall` of `mach (M - 1) h`), so the
machine side of the byte table is recursive in the depth. Table entry `k` is the memory at the
entry state of the `k`-th placed activation with slots (= the memory at the call, the body-entry
world has the entry memory, `BodyEntry.mem`), restricted to its slot bytes.
- `CallsTo g t h` (the step at `t` calls `h` of `P`: `bl n`, or `blr` to `h`'s address, as
  `callHook`), `SlotByte h c a` (the slot addresses `initState_memB` gives), `RetAt g s t`;
- **`TabUpTo M g s b k N e`**: the first `N` steps of `mach M g` from `s` enter the placed
  activations with slots `k + 1, …, k + e` of `b`; per call `j` (`callsBefore`) a count `E j`:
  `0` at a call outside `P`, else `slotted h` (its slot bytes `= b (k + Σ_{<j} E + 1)`, the memory
  at the call) plus the callee run's own `TabUpTo (M - 1)` up to its first `RetOf`; depth `0`:
  no program call, `e = 0`;
- **`TableOf M g s ini`**: every prefix before `RetAt` has a `TabUpTo … ini.bytes ini.next`;
- **`WorldEntryB`** (`WorldEntry` with `NeedSlots → PlaceAtB cs.mem (spv w₀) ini`),
  `WorldEntryB.toWorldEntry` (without `NeedSlots`);
- **`ThmPRB κ M`**: for `g`, a `WorldEntryB … ini`, a machine entry `s` with
  `MachEntryPR … (prophOf s) (prophStOf s)` and `TableOf M g s ini`, a returning CLIF run under
  `envR M g` gives `us outs wf n e` with `ThmPR`'s facts, `ActRet`/`PostTrace` at `n`,
  `TabUpTo M g s ini.bytes ini.next n e` and `NeedSlots → NextAdv cs.mem cm' e` (the machine's
  count is the CLIF counter's advance: what the caller needs for its later calls);
- **`XPRBI κ M g F P R env cs c`** `:= (L.XPRI …).guardI (CallPostN env L.P.bare cs …)`,
  `XPRBI_of` (stage-2 interface: `guard_of`), `tabUpTo_zero`, `tabUpTo_mono`, `tableOf_of_retAt`.
Witnesses `FV/E2E/LinkArmTableBWitness.lean` (on `Lu`). The determinism clause is not part of
`ThmPRB`: `thmPRB_of` takes it as a stated premise (UninitZ10b's `thmPDER_det_of` interface, with
`TabUpTo` transferred between agreeing entries) until it lands.

**Finding (UninitZ12, 2026-10-28): stage 2 needs the CLIF/machine call correspondence of the
earlier calls.** At the machine's call `n` (`OnCallPR … n`), `guard_of` needs `XPR n`'s result
accepted by `CallPostN n`: for the CLIF invocation `(m_n, vals_n)` of count `n` related to the
call's world, the callee's CLIF run (`ThmPRB (M - 1)`, `WorldEntryB` with `m_n`'s oracle) must
read the table entries the machine callee entered. `m_n`'s counter is `ini.next + Σ_{j<n}
adv_j` (`counter_at`, CLIF advances), the machine's is `ini.next + Σ_{j<n} E j` (`TabUpTo`).
They agree when every earlier CLIF invocation `j` is the one the machine's call `j` simulates
(then `ThmPRB (M - 1)`'s `NextAdv` conclusion gives `adv_j = E j`), but that correspondence is
known only inside the simulation (`sim_runG` + the register level); the contracts `hC n` of
`ActEntryPR` are demanded for all `n` up front, and stage 2 sees only the Arm/VCode side. An
index-dependent memory relation (counter `= C n`) cannot be threaded through the rule-level
contracts (§5.9 first Finding).
**Decision (next, conservative: new files, no existing statement changed): a prefix form of the
counted pipeline.** `backend_correct_world_*PRB_upTo`: from the CLIF entry and an `ActEntryPR`
whose callee contracts are given only for the indices `j < n`, every CLIF state with count `n`
reached from `cs` is matched by a machine state on the run with `callsBefore = n` (an `OnCall …
n` state at a call, `SameWorld F` with a VCode world `RelW`-related to the CLIF memory, the
arguments `ArgsAt`). `thmPRB_of` then proves `hC n` by strong induction on `n`: the prefix
theorem at `n` gives the correspondence of every invocation `j ≤ n`, `ThmPRB (M - 1)` at each
`j < n` gives `adv_j = E j`, so the counters agree at `n`, `TableOf` of the actual callee comes
from the caller's `TabUpTo` prefix, the determinism premise transfers it to the canonical callee
(`progCallPR`), and `ThmPRB (M - 1)` gives `CallPost` for `XPR n`'s result. Ingredients: the run
inductions `sim_runG` (CLIF → counted VCode) and `realizes_allC`/`countedRun` (VCode → Arm) are
already sequential, so the prefix forms are copies stopping at the first count-`n` state.
As built (UninitZ12), the CLIF → counted-VCode half: `FV/E2E/IselSimIPrefix.lean`: `PrefixAt`,
**`sim_prefixG`** (induction on `ReachN` from the root: every reached state is matched by a state
of the counted run with counter `n`, or is the pending `jump` of a matched `try_call` state),
`sim_prefix_call` (calling states are matched), **`iselSim_prefixWI`** (`Compiled` path, the
premises of `iselSim_relWI`: a calling CLIF state with count `n` has its memory `RelW`-related to
a world the counted VCode run from the entry reaches with counter `n`). Witness
`FV/E2E/IselSimIPrefixWitness.lean` (`a2_prefixWI`). Cleanup path:
`FV/E2E/IselSimIPrefixCleanup.lean`: **`iselSim_prefixWI_cleanup`** (`valueSemI`); witness
`DeadCleanupWitness.prefix_cleanup_applies`. Next: the VCode → Arm prefix (contracts `hC j` for
`j < n` only, concluding the `OnCall … n` machine state), then the GOT/prune steps.

**The VCode → Arm prefix and the composed prefix pipeline, as built (UninitZ13, branch
`agent/uninit-z13`).** No existing statement or module changed (new leaf modules only).
- `FV/E2E/RegLevelPrefixC.lean`: `ExtSemI.upTo XI N` (the calls `j < N` of `XI`, failing calls
  from `N` on) with `upTo_at_lt`/`upTo_at_ge`, `csemV_call_congr`, `vctr`, `vstep_counted_ctr`,
  **`vstar_counted_upTo`**/`vstar_upTo` (a counted run to counter `≤ N` uses only the calls
  `j < N`), `calleeOkGP_upTo_ge`/`calleeTryOkGP_upTo_ge` (from `N` on the contracts are vacuous:
  the calls fail; the hook's pc is a separate premise), `tlsOk_upTo`; `isSimulation_match`,
  `match_init` (`checkedAt_sound` with its relation `Match` named), **`match_op_uses`** (at an
  instruction item the machine's operand values are the VCode's), `match_to_op` (past the pending
  moves); `CallSiteAt` (the premises of a call contract at a machine state, without the call's
  result: stack, kept bytes, `CallAt`, `SameWorld F u w`, alignment, `ERR`, `useVals = uses`);
  **`regLevel_prefix_core`** (any counted family the machine realises from the call-`n` states:
  every VCode state with counter `N` at a call is matched by an `OnCall … N` machine state at the
  body `sp` with `CallSiteAt`); **`regLevel_prefixC`** (`regLevelCorrect_world_atCS`'s premises
  with the contracts `n < N` only; the contracts of `XI.upTo N` from `N` on are vacuous, so the
  existing `realizes_allC_sp` applies unchanged), `regLevel_prefixPRS` (from `checkAlloc`, with
  the prophecies, contracts in `OnCallPR` form).
- `FV/E2E/BackendPrefixI.lean`: `callDest`, `callLike_of_isCallI`, `csem_call_some`,
  **`vstar_call_at`** (a counted run past counter `j` passes a successful call at counter `j`),
  `prep_prefixW` (`prepare` on run prefixes, with the instruction the same up to its targets),
  `sameInst_callLike`, `ActEntryPRN` (`ActEntryPR` with the contracts `n < N` only, and the
  hook's pc), `ActEntryPR.toN`, **`backend_prefixPRI`** (`Compiled`): for a CLIF calling state
  reached after `N` calls, every call `j < N` of the counted VCode run is realised by the
  machine's `OnCall … j` state `u` (body `sp`, `CallSiteAt` with the VCode call's `uses`, `w`), and
  `(XI.at j).call (callDest info) uses w = some r`.
- `FV/E2E/DeadCleanupPrefix.lean`: `valueSemV_call_congr`, `vstar_upTo_value`,
  `regLevel_value_prefixC`/`_prefixPRS`, `prune_prefixW` (a kept instruction reached by the VCode
  is reached by the cleaned VCode, same block and world, same operand values),
  `valueSem_callLike`, **`backend_prefix_cleanupPRI`** (`CompiledCleanup`, the path
  `Link.DeadCleanup` uses; the decomposition `vstar_call_at` is done on the CLIF-side VCode, then
  mapped through the cleanup, `prepare` and the GOT).
- Witnesses `FV/E2E/BackendPrefixIWitness.lean`: `LinkWitness.{upTo_const_at, a2_prefixPRI}`,
  `DeadCleanupWitness.prefix_cleanupPRI_applies`.

The correspondence of the earlier calls, as built: `FV/E2E/PrefixRelated.lean`: `ExtSemI.relOnly
XI Q` (call `n` of `XI` where `Q n d uses w`, undefined elsewhere), `relOnly_call_some`/`_of`,
`csemV_of_call_sub`, `CalleeOkGP.ofCallSub`/`CalleeTryOkGP.ofCallSub` (the machine contracts are
antitone in the call results), `ActEntryPRN.relOnly`, `RelatedN` (the call's `CallPostN` is not
vacuous), `xCalls_relOnly` (stage 1 for `XI.relOnly (RelatedN …)` from stage 1 for `XI`: every
query of the extern contracts is related, `callPost_not_vacuous`), **`prefix_related_cleanupPRI`**,
**`prefix_relatedPRI`**: `backend_prefix*PRI`'s conclusion plus `RelatedN … j (callDest info) uses
w` at the machine's call `j < N` (premise `NoRetCall` added). Witness
`FV/E2E/PrefixRelatedWitness.lean` (`relOnly_none`, `relOnly_all`, `prefix_related_applies`).

**Finding (UninitZ13, 2026-10-28): `XPRBI` cannot meet the stage-2 contract when program callees
have slots.** `XPRBI := (L.XPRI …).guardI (CallPostN …)` answers `XPR`'s result where `CallPostN`
accepts it and otherwise an ε-chosen accepted result; the machine contract (`CalleeOkGP`) then
needs the machine's callee result to *be* the answer at every `OnCallPR … n` call state. But
`XPR`'s `progX` is defined only under `Cond`, whose CLIF witness memory is placed with
`PlaceAt cm (spv w)` (oracle `none`); with `NeedSlots` the CLIF memories of the run are placed
with `PlaceAtB … (some ini)`, so at the actual call `Cond` is witnessed only if some `none`-placed
memory makes the callee's CLIF run return — not implied (the callee may read an unwritten slot
byte). Where `XPR` is `none` the guard answers ε and the contract fails. Second, where
`CallPostN` is vacuous (no CLIF invocation of count `n`, or none related to `(uses, w)`), a `none`
of `XPR` also becomes an ε answer, while the unguarded `XPR`'s contracts are vacuous there.
**Decision (conservative, new definitions only):** (1) `CondB`/`progXB`/`XPRB`: `Cond` with
`∃ ini, PlaceAtB cm (spv w) ini` (the result is still the machine's `pcall` from `canon`, so the
generated code and `progX`'s users are unchanged); (2) a guard that keeps `none` where no CLIF
invocation is related (`ExtSem.guardR`: ε only when `CallPost` is not vacuous), so the contracts
outside the simulated calls stay vacuous; (3) `progOsPRB`/`calleeOkPRB` on `ThmPRB (M - 1)` (the
`progOsPR` proofs with `WorldEntryB`/`TableOf` from the table prefix `TabUpTo` at the call and the
counter equality from `prefix_related*PRI` + `NextAdv` of the earlier calls), by strong induction
on `n`. As built (UninitZ13), (1) and (2): `FV/E2E/ExtSemGuardR.lean`: `ExtSem.guardR`,
`guardR_of`, `guardR_spec`, **`guardR_eq_of`** (stage 2: where every non-vacuous contract accepts
`X`'s result, every answer is `X`'s), `callPost_not_vacuous`(`_ind`), **`xCallsOk_guardR_only`**;
`FV/E2E/LinkArmXPB.lean`: `ExtSemI.guardRI`, **`hX_guardRI`** (stage 1 for any `XI`), `CondB`
(`Cond` with, under `NeedSlots`, `PlaceAtB cm (spv w) ini` and `TableOf (M - 1) g (enterAt (canon
…)) ini`: the oracle is the canonical callee run's table, so `ThmPRB (M - 1)` applies to the
canonical callee), `cond_iff_condB` (without `NeedSlots`), `progXB`, `progXPRB`, `XPRB`, `XPBI`,
`XPRB_of_not_needSlots`, **`XPBG`** (`XPBI` guarded by `CallPostN` with `guardR`: the `XI` of the
induction step, replacing `XPRBI`), `XPBG_eq_of`. Witnesses `FV/E2E/LinkArmXPBWitness.lean`
(`guardR_vacuous`, `hX_sCall_R`, `XPRB_Lu`). `ThmPRB`'s statement does not mention `XPRBI`, so it
is unchanged.
Next, (3): `progCallPRB` (copy of `progCallPR`, `LinkArmProgCallPR.lean`, 650 lines) on
`ThmPRB (M - 1)`: `initState_memB` with `PlaceAtB` (LinkPlaceB), the callee's `MachEntryPR` with
`(prophOf, prophStOf)` as there, `TableOf` from `CondB`; the transfer from the canonical callee
state to the actual call state (`progCallPR`'s `∀ t, CallerOk … → agreement → …` clause) needs the
determinism clause, here a stated premise `DetPRB κ (M - 1)` (ThmPDER's determinism clause for
`ThmPRB`'s outcome, plus `TabUpTo` carried to the agreeing run) until `thmPDER_det_of` (UninitZ11b,
blocked on `ReadsIn`, UninitZ12b's #682) gives it. Then `progOsPRB`/`calleeOkPRB` (copies of
`LinkArmProgOsPR.lean`), and the stage-2 obligation of `XPBG_eq_of` at `OnCallPR … n` call states
where `RelatedN … n` holds: `CondB` at the actual call with `ini := ini.adv (counter)` (the counter
equality from `prefix_related_cleanupPRI` at every `j < n` and `ThmPRB (M - 1)`'s `NextAdv`), by
strong induction on `n`; then `thmPRB_of`, `thmPRB`, item (e).

**(3), as built (UninitZ14, 2026-10-28).** Finding: `CondB` is too weak for `ThmPRB (M - 1)`: the
callee's CLIF entry is placed with `calleeIni h ini` (`ini.adv 1` when `h` has slots,
`initState_memB`), so the canonical callee run's table must be `calleeIni h ini`'s, also without
`NeedSlots` (`TableOf` at depth `0` excludes program calls), and the new slot bytes
`ini.bytes (ini.next + 1)` must be the call world's memory (else `RelW` fails on them). Decision
(new names, `CondB` kept): `FV/E2E/LinkArmXPBT.lean`: **`CondBT`** (both added), `progXBT`,
`progXPRBT`, `XPRBT`, `XPBTI`, **`XPBTG`** (the `XI` of the induction step), `XPBTG_eq_of`,
`XPRBT_{prog,none,ind,base,ext}`. `FV/E2E/LinkArmProgCallPRB.lean`: **`DetPRB κ M`** (`ThmPDER`'s
determinism clause for any outcome of a `ThmPRB` entry `s₀` with its own prophecies and table,
plus `TabUpTo` with the same count on the agreeing run), `calleeIni`, **`progCallPRB`** (premises
`ThmPRB (M - 1)`, `DetPRB (M - 1)`, `PlaceAtB`, slot bytes, callee table; conclusion: one outcome,
`NextAdv` of the callee's CLIF run, and for every compatible caller state the linked call's
`ActRet` and `TabUpTo` with that count; the non-interference clause of `progCallPR` is not
restated, `DetPRB` covers both cases). `FV/E2E/LinkArmProgOsPRB.lean`: `progOsCorePRB`,
`progOsCoreXPRRB`, `progOsPRB`, `progOsRegPRB`, **`calleeOkPRB`**, **`calleeTryOkPRB`** (for
`XPRBT … n`). `FV/E2E/BackendWorldPRG.lean`: **`backend_correct_world_{cleanup,pipeline}PRG`**
(`guardRI`, stage 1 by `hX_guardRI`); witnesses `FV/E2E/BackendWorldPRGWitness.lean`.
Item (e): `Link.DeadCleanup.compileExe` compiles every function by the untyped cleanup path
(`compiledCleanup_of`, `FV/E2E/DeadCleanupExecMemTrap.lean`: `CompiledCleanup`), so the prefix
files already cover it; the typed `CompiledCleanupT/TC` are `compileExeT{,3}`'s only.
Open for stage 2: `CondBT` at `worldPR (P n) (R n) w` needs the canonical callee run's table,
while the caller's `TableOf` gives the actual call's; a transfer `TableOf s → TableOf s₀` for
`EntryAgree`-related entries (a second determinism fact, `DetTabPRB`, stated premise like
`DetPRB`) is needed, then `XPBTG_eq_of` by strong induction on `n`, `thmPRB_of`, `thmPRB`.

**Stage 2 groundwork, as built (UninitZ15, 2026-10-28, PR #688).** Decisions (new names, old
statements kept):
- `DetTabPRB κ M` (`FV/E2E/LinkArmDetTabPRB.lean`): the second determinism fact, stated
  call-shaped with `progCallPRB`'s premises: a call state `t` with `CallerOk`, the canonical
  state's masked registers but `x30`/pc and its bytes in `StackBelow (frameDrop + κ (M - 1))`
  moves `TableOf (M - 1) h (enterAt t) (calleeIni h ini)` to `enterAt (canon h uses w)`;
  `progCallPRB_at`. A premise beside `DetPRB`, both for `thmPDER(X)_det_of`.
- Finding [#687](https://github.com/eth-act/clifv/issues/687): `ThmPRB` is unsatisfiable at
  entries with `ra = base` (`RetAt g s s`, so `TableOf` holds for every oracle,
  `tableOf_of_retAt`, while the conclusion's table pins the first slotted callee's bytes).
  `ThmPRBR` adds `RaOk (L.A g) (ra - 4)` (every linked call has it; a top-level entry has `ra`
  outside the code), `ThmPRB.toR`; R-variants `progCallPRBR(_at)`, `progOsCorePRBR`,
  `progOsCoreXPRRBR`, `progOsPRBR`, `progOsRegPRBR`, `calleeOkPRBR`, `calleeTryOkPRBR`.
  `noRetAt_of` (under `RaOk` no `RetAt` precedes the return: `retStuck` / `PostTrace`) and
  **`thmPRBR_of_thm`** (`¬ NeedSlots`: `Thm κ M → ThmPRBR κ M`), so `ThmPRBR` holds at every depth
  for systems without slotted callees (witness `thmPRBR_LU`).
- `tabUpTo_count` (`FV/E2E/LinkArmTabCount.lean`): the count of a table prefix is unique
  (independent of table and offset), which ties `progCallPRB`'s per-call count (`NextAdv`) to the
  caller's `E j`.
- Finding [#690](https://github.com/eth-act/clifv/issues/690): `ActEntryPR` for `XPBG`/`XPBTG`
  is unprovable: `CalleeOkGP.ext` asks the guarded answers to keep the program, `guardR`'s ε
  answers are only `CallPost`-accepted, and `CallPost` never constrains the program.
  `FV/E2E/ExtSemGuardRX.lean`: `CallPostX := CallPost ∧ ExtOkR`, `CallPostNX`, `fixW`,
  `callPostNX_exists`, `xCallsOk_guardRX_only`, **`guardR_ext`**, **`hX_guardRXI`**;
  `FV/E2E/BackendWorldPRGX.lean`: **`backend_correct_world_{cleanup,pipeline}PRGX`**;
  `FV/E2E/LinkArmXPBTX.lean`: `XPBTGX` (the `XI` of the induction step), `XPBTGX_ext`,
  `XPBTGX_eq_of`.
- `FV/E2E/LinkArmEnvOfB.lean`: `PlacedB`, `envOfB` (program callees guarded by "placed with some
  oracle"), `ActInvB`, `actInvB_step`, `step_envOfB`, **`runLoop_envOfB`** (the activation's
  environment for `backend_correct_world_*PRGX` in `thmPRBR_of`, as `envOf` in `thm_of`).

Next (`thmPRBR_of`, in order): (a) the CLIF counter along `ReachN` under `ActInvB`: the state
after `k` calls is placed with `ini.adv (sumTo A k)`, `A j` the advance of invocation `j`
(`InvokedN`; `placeInvB_step`, `NextAdv.unique`); (b) stage 2 at call `n` (strong induction on
`n`): at an `OnCallPR … n` state `t` whose call is `RelatedN … n`, `CondBT` at `worldPR (P n)
(R n) w` with `ini := ini0.adv (sumTo A n)` (= the caller table's offset by (a), `tabUpTo_count`
and `progCallPRBR`'s per-call count for `j < n`), the slot bytes from `TabUpTo`'s call clause,
the canonical table by `DetTabPRB`, and `CallPostNX` of `XPRBT`'s answer (`progCallPRBR`'s
outcome, `XPRBT_ext`); then `CalleeOkGP` for `XPBTGX … n` at the `OnCallPR` states from
`calleeOkPRBR` (a `P`-restricted `ofCallSub` with `XPBTGX_eq_of`, `ext` by `XPBTGX_ext`); (c)
`thmPRBR_of` from `backend_correct_world_pipelinePRGX` with `XI := XPBTI`, `env := envOfB`
(`runLoop_envOfB`), the table to the return by `noRetAt_of`, `NextAdv` by (a) at the return;
(d) `thmPRBR` by induction on `M`; (e) `compileExe_correct_init`.

**Stage 2 and `thmPRBR_of`, as built (UninitZ16, 2026-10-28).**
- (a) `FV/E2E/LinkPlaceBReach.lean`: `advAt env p cs j` (the counter advance of the step of the
  calling state of count `j`; unique: `advAt_eq`), **`nextAdv_reachN`** (a bare activation reached
  after `k` calls has `cs`'s oracle advanced by `sumTo (advAt …) k`; non-call steps keep the
  oracle, `step_bare_noCall_place`), **`LinkSys.counter_reachN`** (`PlaceAtB s.mem c
  (ini.adv (sumTo (advAt …) k))` from `WorldEntryB.place`), `envAdv_envOfB`, `initState_linv_only`.
- Finding [#692](https://github.com/eth-act/clifv/issues/692): `CallPostNX` (#690) is never
  vacuous at a world without error, so `guardR` answers ε-junk where `XPRBT` has none, also at
  calls unrelated to the CLIF run (e.g. a later activation at the same `sp`, which `OnCallPR`
  admits); `CalleeOkGP.os` of `XPBTGX` is unprovable there. Fix (new names):
  `CallPostXR := CallPost ∧ ((¬ ∀ r', CallPost r') → ExtOkR w r)` (vacuous exactly where
  `CallPost` is), `CallPostNXR`, `guardR_extV`, `hX_guardRXRI`, `guardRXRI_ext`, `guardRXR_sub`
  (`FV/E2E/ExtSemGuardRY.lean`); **`backend_correct_world_{cleanup,pipeline}PRGY`**.
- (b) interface, `FV/E2E/LinkArmStage2Y.lean`: `CalleeOkGP.ofCallSubW` /
  `CalleeTryOkGP.ofCallSubW` (antitone in the call results only at the worlds of the states `P`),
  `XPBTGY`, `XPBTGY_ext`, **`Stage2Y`** (at the states `Q`, where `CallPost` of the invocation of
  count `n` is not vacuous, `XPRBT … n` answers a `CallPost`-result), `XPBTGY_sub`,
  **`calleeOkXPBTGY`**, **`calleeTryOkXPBTGY`**.
- Finding [#694](https://github.com/eth-act/clifv/issues/694): `ThmPRB`/`ThmPRBR` end with
  `NeedSlots → NextAdv cs.mem cm' e`, from the entry memory (the activation's `sp` on top) to the
  returned one, which the return popped (`Mem.leave`): false for every returning run under
  `NeedSlots` (witness `not_nextAdv_entry`), so the PRB induction hypothesis is unsatisfiable on
  systems with slotted callees (all earlier witnesses are on `¬ NeedSlots`). Fix (new names):
  **`ThmPRBRL`** with `NextAdv cs.mem.leave cm' e` (`nextAdv_leave_entry`), and the copies
  `progCallPRBRL(_at)` (`FV/E2E/LinkArmProgCallPRBRL.lean`), `progOsCorePRBRL`,
  `progOsCoreXPRRBRL`, `progOsPRBRL`, `progOsRegPRBRL`, `calleeOkPRBRL`, `calleeTryOkPRBRL`
  (`FV/E2E/LinkArmProgOsPRBRL.lean`; same proofs, the conjunct is only passed through).
- (c) `FV/E2E/LinkArmThmPRBROf.lean`: **`thmPRBRL_of`**: `ThmPRBRL κ M` from `ThmPRBRL κ (M - 1)`,
  `DetPRB κ (M - 1)` and three per-activation premises: `RetOkPRB` (`InvokedRetOk` of the run
  under `envOfB`), `Stage2PRB` (`Stage2Y` at `CallStPRB`, the activation's call-`n` states),
  `CountPRB` (the CLIF advance from the popped entry is the machine table's count to the
  return). The `ActEntryPR` is `MachEntryPR`'s fields with `calleeOkXPBTGY` (`callStPRB_q`), the
  table by `noRetAt_of`. `thmPRBRL_of_thm` (`¬ NeedSlots`). Witnesses on `Lu` (`thmPRBRL_LU`,
  `thmPRBRL_of_Lu`, `countPRB_Lu`, `stage2Y_noExt`, …).

Next: `Stage2PRB` is stated at every `CallStPRB … n` state, which includes call-`n` states after
the activation returned (same code and `sp`, another activation); there the related CLIF call `n`
fixes the answer from the prophecies `P n`, `R n` of the activation's own call `n`, whose existence
(before the return, calling the same callee with compatible arguments) needs the simulation up to
call `n` (`backend_prefixPRI` extended to the state *at* call `N`, contracts `j < N` by strong
induction). Base externs are the easy half (`baseX`/`baseXI`, `symInj`); at depth `0` every
returning invocation is a base one (`CrunOk.zero`), so `Stage2PRB κ 0` should follow from that
half alone. `CountPRB` (from (a), `tabUpTo_count`, `progCallPRBRL`'s `TabUpTo … e`/`NextAdv … e`
per call, `prefix_relatedPRI`), `RetOkPRB` (a scope fact of `Ok` + `NeedSlots`: callee runs free
what they allocate, `baseKeepsAllocs`; return-count agreement of the declarations), then
`thmPRBRL` and `compileExe_correct_init`.

**Slotted witness system, depth 0, `RetOkPRB`, `Stage2PRBR`, as built (UninitZ17, 2026-10-28).**
No existing statement changed; new leaf modules only; no generated-code change.
- Witness system `FV/E2E/LinkSlotSysWitness.lean` (`Lsl`, the witness system for the slot-byte
  statements from now on): `f n = r (h n)` compiled by the pipeline, `h` writes then reads its
  slot, `r` reads its unwritten slot (the bytes `h` left there), `NeedSlots`, no base externs.
  `#guard` checks on a computable mirror of the linked machine (`machC`): the machine returns
  `82 = 41 + 41`, calling `h` then `r` at `f`'s body `sp`; `iniT` is the machine's byte table.
  Theorems: `Lsl_ok`, `needSlots`, `run_f` (the CLIF run with `iniT` returns `82`; with the zero
  table `41`, `run_f_zero`), `nextAdv_leave_f` (`NextAdv cs0.mem.leave cm' 2`: `ThmPRBRL`'s
  conjunct, `CountPRB`'s count = the machine's two slotted activations), `not_nextAdv_f` (#694 on
  a real program). No further false statement found.
- `FV/E2E/LinkPlaceBLeave.lean`: `initState_place`, **`initState_leave_nextAdv`** (`NextAdv cm
  cs.mem.leave (slotted h)`), `NextAdv.cancel`.
- Depth `0`: `FV/E2E/LinkArmStage2Zero.lean` (`envOfB_zero_ret`, `callPost_xb_zero`,
  **`stage2Y_zero`**, **`stage2PRB_zero`**), `FV/E2E/LinkArmCountZero.lean` (`reachN_cons`,
  `reaches_reachN`, `step_done_mem_q`, **`returned_nextAdv_leave`** (a returning bare
  activation advances the popped entry by `Σ_{j<k} advAt … j`), `place_reachN_keeps`,
  `returned_keeps_leave`, `envR_zero_keeps`, **`countPRB_zero`**, `thmPRBRL_zero` (from
  `RetOkPRB κ 0`)).
- `RetOkPRB` is not a consequence of `Ok` (no field keeps symbols when every function is
  `IndFree`; declarations of one extern outside `P`, or indirect call signatures, may differ in
  their return registers). Scope conditions (`FV/E2E/LinkArmRetOkZero.lean`): `BaseRetOk` (base
  externs keep valid addresses and symbols) and `RetCount g` (per extern name outside `P`: its
  declarations and `g`'s indirect call signatures with equal return counts have equal `sigRets`
  counts; decidable `retCountB`; fv-demo: 551/551 functions, the cross-name form fails on 3).
  **`retOkPRB_zero`**, `thmPRBRL_zero_of`; `FV/E2E/LinkArmRetOkPRB.lean`: `sigRets_length_eq`,
  `sigRets_length_of_abiMatch`, **`retOkPRB_of`** (every depth, under `NeedSlots`; without it
  `thmPRBRL_of_thm` applies).
- `Stage2PRB` reconsidered (`FV/E2E/LinkArmStage2R.lean`): its discharge at `M > 0` needs the
  call correspondence up to call `n` (`prefix_relatedPRI`), whose premises include `TrapsExplicit`
  of the CLIF run, available only for returning runs (`thmPRBRL_of` uses stage 2 only there);
  post-return `CallStPRB` states carry counts `≥` the machine's return count, and at counts
  without a CLIF invocation stage 2 is vacuous (**`stage2Y_of_not_invoked`**). New: **`Stage2PRBR`**
  (with the returning-run premise, as `CountPRB`), `Stage2PRB.toR`, `stage2PRBR_zero`,
  **`thmPRBRL_ofR`**. Witnesses `FV/E2E/LinkArmThmPRBRZeroWitness.lean`,
  `FV/E2E/LinkArmStage2RWitness.lean` (`thmPRBRL_zero_Lsl`, `thmPRBRL_ofR_Lsl`, `retOkPRB_Lsl`,
  `keeps_leave_h`, `stage2Y_sZ`).

Next (general `M`, one strong induction on the call index `j` of a returning activation, giving
both `Stage2PRBR` and `CountPRB`): (P1) `backend_prefixPRI` extended to the call itself (from
`iselSim_prefixWI`'s matched VCode state at the statement start, run the call statement's segment
to the VCode call instruction, then `regLevel_prefix_core` at counter `j`), with `RelatedN j`;
(P2) at the machine's call `j` (pre-return), `CondBT`'s facts: `counter_reachN`, the slot bytes
from `TabUpTo`'s call clause, `Σ_{i<j} advAt = Σ_{i<j} E i` (induction), the canonical callee's
table by `DetTabPRB`; (P3) `progCallPRBRL` gives `advAt j = E j` (`initState_leave_nextAdv`,
`tabUpTo_count`); (P4) `Stage2Y` at `j` (the answer `pcall … canon …` is `CallPost`-accepted);
`CountPRB` then from `returned_nextAdv_leave`; then `thmPRBRL`, `compileExe_correct_init`.

**Per-call pieces, as built (UninitZ18, 2026-10-28).** New leaf modules; no statement changed.
- (P1) `FV/E2E/RegLevelPrefixG.lean` (`OnCallG`: the call state with the `Good` trace,
  `regLevel_prefix_coreG/CG/PRSG`), `FV/E2E/BackendPrefixAt.lean`: `step_ne_done_of_callNum`,
  `runLoop_returned_reachN`, `next_of_returned`, `iselSim_prefixWI_next`,
  **`backend_prefixPRI_at`**, **`prefix_relatedPRI_at`** (calls `j ≤ N` of a returning run,
  contracts `n < N` only).
- Finding [#697](https://github.com/eth-act/clifv/issues/697): `Stage2Y`/`Stage2PRB(R)` ask for
  an answer at **every** `uses` the CLIF invocation accepts; `VHolds` leaves the upper bits of a
  narrow argument free, so `XPRBT`'s canonical callee state may differ from the actual one in
  them and its slot table need not be the oracle's (spill-then-overlap). The machine contracts
  only call the semantics at the call state's own operands `useVals ops regs u`. Fix (new names,
  `FV/E2E/LinkArmStage2Z.lean`): `csemV_of_call_subAt`, `CalleeOkGP/CalleeTryOkGP.ofCallSubU`,
  **`Stage2Z`** (stage 2 at the call's own operands), `Stage2Y.toZ`, `XPBTGY_subZ`,
  `calleeOk(Try)XPBTGZ`, **`Stage2PRBZ`**, `Stage2PRBR.toZ`, `stage2PRBZ_zero`,
  **`thmPRBRL_ofZ`**; base calls: `FV/E2E/LinkArmStage2Base.lean` (`stage2Y_base`,
  `stage2Z_base`).
- (P2/P4) `FV/E2E/LinkArmProgResultBT.lean` (**`progResultBT`**: a program call's result under
  the oracle facts), `FV/E2E/LinkArmStage2Prog.lean` (`callPost_of_answers`, `envOfB_only_some`,
  `OracleAt`, **`stage2_answer`**), `FV/E2E/LinkArmCallTab.lean` (`retAt_enterAt_iff`,
  **`noRetAt_upTo`**, **`tabUpTo_call_at`**, `tableOf_callee`), `FV/E2E/LinkArmOracleAt.lean`
  (**`callerFacts`**, **`oracleAt_of_call`**: `OracleAt` at a pre-return call from the caller
  table's count and the invocation's placement, with `DetTabPRB`).
- (P3) `FV/E2E/LinkArmProgCallPRBRLT.lean` (`progCallPRBRLT`: `progCallPRBRL` with the callee
  run's trace), `FV/E2E/LinkArmCallCount.lean` (**`callCount`**: the caller table's count grows
  over a program call by the CLIF advance `d` of the invocation, `NextAdv cm cm' d`).

**The glue, as built (UninitZ19, 2026-10-28).** New leaf modules; no existing statement changed;
no generated-code change.
- Finding (refines #697): `Stage2Z` still quantifies over every call instruction assigning to the
  machine call at the pc; only at a call site of the compiled code (`VCode.CallSite`) does the
  scope fix the argument registers (`Ok.callRegs`, `Ok.blrRegs`, the latter only under the GOT
  guard `gotGuard`), and the machine contracts are only applied there, under the guard (`csemV`).
  New (`FV/E2E/LinkArmStage2ZS.lean`): `csemV_of_call_subAtG`, `CalleeOkGP/CalleeTryOkGP.ofCallSubS`,
  **`Stage2ZS`**, `Stage2Z.toZS`, `XPBTGY_subZS`, `calleeOk(Try)XPBTGZS`, **`Stage2PRBZS`**,
  `stage2PRBZS_zero`, **`thmPRBRL_ofZS`**.
- Prefix at call `N` for the artifact of `Ok.compiled` (`FV/E2E/BackendPrefixAtCleanup.lean`):
  `regLevel_value_prefixCG/PRSG`, `iselSim_prefixWI_next_cleanup`, `backend_prefix_cleanupPRI_at`,
  `prefix_related_cleanupPRI_at`, `backend_prefixPRI_atS`, `prefix_relatedPRI_atS`,
  **`prefix_relatedPRI_atE`** (`CompiledEither`), also giving the VCode call site and its GOT
  guard (`gotGuard_of_inv`, `csemV_guard`).
- `stage2_answerF` (`stage2_answer` whose oracle premise receives the invocation's facts: the
  callee memory and arguments at the world with the prophecies, the callee's run, `IndTo` and the
  target of an indirect call, the body `sp`; `stage2_answer` is its corollary).
- (1) `FV/E2E/LinkArmCallDecode.lean`: `call_of_callLike`, **`callDecode`** (at a call site under
  the guard, a program call's arguments are in the callee's parameter registers, the machine calls
  it (`CallsTo`), `RaOk`).
- (2) `FV/E2E/LinkArmInvokedStep.lean` (**`invoked_step`**: the step of an invoking state gets its
  memory from the invoked extern; `reachN_call_at`; `callIdx_unique`), `FV/E2E/LinkArmProgInst.lean`
  (`ProgInst`, **`nv_cases`**: the invocation behind a related call is a program call with
  `stage2_answerF`'s facts or a base call), `FV/E2E/LinkArmCountStep.lean`
  (`tabUpTo_succ_noCall`, `tabUpTo_succ_base`, `callDecodeBase`, `adv_base`, `adv_prog`),
  `FV/E2E/LinkArmStage2Count.lean` (**`oracleAt_at`**, **`countStep_prog`**,
  **`countStep_base`**: the count invariant `TabUpTo … i e → e = Σ_{k < callsBefore i} advAt k`
  passes one machine step).
- (3) `FV/E2E/LinkArmStage2PRBZSOf.lean`: **`stage2PRBZS_of`**: under `NeedSlots`,
  `Stage2PRBZS κ (M' + 1)` from `ThmPRBRL κ M'`, `DetPRB κ M'`, `DetTabPRB κ (M' + 1)`,
  `RetOkPRB κ (M' + 1)` (strong induction on the call count; the call state of stage 2 is the
  machine's call-`n` state by `callIdx_unique`; the count invariant by an inner induction over the
  machine steps; `oracleAt_at` then `stage2_answerF`).
- (4) `FV/E2E/LinkArmThmPRBRLAll.lean`: **`thmPRBRL_succS`**, **`thmPRBRL_all`** (`ThmPRBRL` at
  every depth from `BaseRetOk`, `RetCount`, and `DetPRB`, `DetTabPRB`, `CountPRB` at every depth).
- Witnesses on `Lsl`: `FV/E2E/LinkArmStage2ZWitness.lean` (UninitZ18's modules: `thmPRBRL_ofZ_zero_Lsl`,
  `prefix_relatedPRI_atE_f`, instances), `FV/E2E/LinkArmStage2GlueWitness.lean`
  (`thmPRBRL_ofZS_zero_Lsl`, `stage2PRBZS_one_Lsl`, `thmPRBRL_every_Lsl`, concrete
  `reachN_call_at_sP`, `invoked_step_sP`, `callIdx_unique_u0`).

Next: `CountPRB` needs the machine's call count at the return to be the CLIF run's call count
`k` (`callsBefore n = k`; the count invariant then gives `e = Σ_{j<k} advAt j`, and
`returned_nextAdv_leave` the CLIF side). The counted register-level theorem relates the VCode
counter to the machine's calls at every realised state (`RealizesCP.countedRun`) but
`regLevelCorrect_world_atC` does not export it at the return; extend it (and the pipeline copies)
with `callsBefore n = nc` for the VCode return `(w, nc)`, and `iselSim` with `nc = k`. Then
`compileExe_correct_init` (CompiledCleanup, `BaseRetOk`/`RetCount`) and the fv-demo witness.
`DetPRB`/`DetTabPRB` stay premises until `thmPDERX_det_of` lands (UninitZ17b).

**`CountPRB` and the top-level statement, as built (UninitZ20, 2026-10-28).** New leaf modules;
no existing statement changed; no generated-code change.
- (a) machine side, `FV/E2E/RegLevelCorrectPRSN.lean`: `forward_lastC` (`forward`/`forward_last`
  on the counted machine `stepC`, read back on the plain one, with *count = counter*);
  `regLevelCorrect_world_atCSN`, `_worldCSN`, **`_worldPRSN`** and the value-semantics copies
  `_world_value_atCSN`, `_value_worldCSN`, **`_value_worldPRSN`**: the return index `n` also has
  `callsBefore (ArmStepX (XI.at 0) H fa) fa base s n = nc`, `nc` the VCode return's counter (the
  epilogue makes no call, `ret_machineN`).
- (b) CLIF side, `FV/E2E/IselSimIN.lean`: `RunOkAbiN` (`RunOkAbi` whose return has a state `u` of
  the CLIF run reached after `w.2` calls whose step returns), `sim_runGN`, **`iselSim_relWIN`**,
  **`iselSim_relWI_cleanupN`**.
- Pipeline, `FV/E2E/BackendWorldPRGYN.lean`: `backend_correct_worldPRIN`, `_cleanupPRIN`,
  `_pipelinePRIN`, `_{cleanup,pipeline}PRICN`, **`_{cleanup,pipeline}PRGYN`**: the return also has
  `∃ u, ReachN env p cs u (callsBefore … n) ∧ Clif.step env p u = .done vals cm`.
- `FV/E2E/LinkArmCountPRBSucc.lean`: `nextAdv_leave_of_done` (`returned_nextAdv_leave` from a
  given returning state), `retAt_of_actRet`, `actRet_unique` (two returns with the trace are one
  step, `noRetAt_of` both ways), **`countPRB_succ`** (`CountPRB κ (M' + 1)` from the premises of
  `stage2PRBZS_of`: the pipeline at the return with stage 2 by `stage2PRBZS_of`, the count
  invariant of `stage2PRBZS_of` up to the return, each machine call before it realised by the
  prefix theorem at the last CLIF call), **`thmPRBRL_allC`** (`thmPRBRL_all` without `CountPRB`).
- Finding [#700](https://github.com/eth-act/clifv/issues/700): `TableOf M g s ini` presupposes
  that every program callee the machine calls before its return returns (`TabUpTo`'s call clause
  `∃ N', RetOf …` at every pre-return prefix; a non-returning callee is `junkAt`, so `TableOf` is
  false for every `ini`). Inside the induction that is harmless (`tableOf_callee`); at a top-level
  entry it cannot be discharged without the theorem itself. Proposed fix (new names): a
  prefix-closed `TabUpToE`, `TableOfE` over the error-free prefixes, `ThmPRBRLE`, the machine's own
  table `iniOf`.
- `FV/E2E/LinkArmProgramInit.lean`: **`backend_correct_program_core_init`**,
  **`backend_correct_program_init`**: the linked program under the slot-byte oracle at a top-level
  entry (`PlaceAtB … ini`, `TableOf M f s ini`): a returning (whole-program) CLIF run is realised
  by the linked machine (`ArmRefines`), from `thmPRBRL_allC` with the entry's own prophecies and
  `RaOk` from `raOutside`; premises `BaseRetOk`, `RetCount`, `DetPRB`, `DetTabPRB`, `TableOf`.
- Witnesses `FV/E2E/CountPRBNWitness.lean`: `worldPRSN_const`, `a2_iselSimIN`, `a2_worldPRIN`,
  `prgyN_applies`, `prgyN_pipeline_applies`, `countPRB_one_Lsl`, `countPRB_succ_Lsl`,
  `thmPRBRL_allC_Lsl`, `actRet_unique_Lsl`, `backend_correct_program_core_init_Lsl`,
  `backend_correct_program_init_L0`.

**#700, steps 1–2, as built (UninitZ20, branch `agent/uninit-z20b`).**
- `FV/E2E/LinkArmTableE.lean`: **`TabUpToE`** (at each call of the prefix: the callee's slot
  bytes, `slotted h ≤ E j`, the callee's table for every callee prefix before its first return
  without an error, and, only if it returns, its full `TabUpTo` with count `E j - slotted h`),
  **`TableOfE`** (every pre-return prefix whose states have no error), `tabUpToE_zero/mono`,
  `firstRet_unique`, **`tabUpToE_of`**, **`tableOfE_of`** (`TableOf → TableOfE`),
  `tableOfE_of_retAt`, `tableOfE_of_err`.
- `FV/E2E/LinkArmTableECall.lean`: `mach_callsTo`, **`callsTo_ret`** (a program call whose next
  state has no error returns: `junkAt` is an error), **`tabUpToE_count`**, **`tabUpToE_call_at`**
  (the callee's `TableOfE` without its return). Witnesses `FV/E2E/LinkArmTableEWitness.lean`.
- Found: the machine's states before its return are not known to be error-free (`ArmStepX` does
  not keep an error through the arbitrary base hooks), so `TableOfE` at the return needs the
  pipeline to export the `GoodX` trace (`err`, `prog`) up to the return, as `RegLevelCorrectPRSN`
  exports the call count: `realizes_allC` already realises `GoodX`, the `*_atCS` proofs weaken it
  to `Good` (`mono_T`). Same for the prefix theorems (`OnCallG`'s trace).
- Next for #700: export `GoodX` at the return and at the prefix calls; `DetTabPRBE` (premise);
  E-copies of `oracleAt_of_call`/`OracleAt`, `progResultBT`, `stage2_answerF`, `callCount`,
  `countStep_*`, `stage2PRBZS_of`, `countPRB_succ`, `thmPRBRL_ofZS`; `ThmPRBRLE` (implies
  `ThmPRBRL`); the machine's table `iniOf` with `TableOfE` at a top-level entry.

Next: (1) #700's fix, then `TableOfE M f s (iniOf …)` at the top-level entry; (2) the executable
level: `exec_of_model` needs the model run's `RunOk`, which `binary_correct_exec_proven` gets from
the `Good`-trace chain of the `init = none` statement (`binary_correct_of_checksX`); the oracle
version needs that chain (or `RunOk` from `thmPRBRL`'s trace) under `PlaceAtB`, then
`ClifRunB`/`premisesB`, `binary_correct_init`, `compileExe_correct_init`, the fv-demo witness.

**Step 3h, as built (UninitZ10b): the call-count premises are theorems.** `InstCallsOne f` and
`TryCallsOne f` hold for every `f` (`E2E.instCallsOne_all`, `E2E.tryCallsOne_all`,
`FV/E2E/IselCallsOneAll.lean`), from `FV/Backend/Proof/IselCallsOne.lean`:
- the rule-table certificate `Cov.lower_call_fmts` (one `decide +kernel` over the exported rules
  of `lower`, `callFmtOk`): every root rule is a call root (1031–1033), outside the closure
  (`excludedUnmatchable`), or names a root `InstructionData` format whose variant is neither
  `Call` nor `CallIndirect` (`ruleFmt_match`: it cannot match a call, whose data has that format,
  `instData_call_fmt`); `lower_branch` needs none (`tryUnmatchable`, `tryIndUnmatchable`);
- the call roots' runs, copies of the shape inversions (`IselShpCall.run_*`, `IselShpTry.shpTry_*`)
  concluding the count `CallsSince 1` (stack-argument stores, a GOT load, one call):
  `callRun_2508`/`_2518`/`_2529`, `tryRun_2542`/`_2551`/`_2561`;
- `Cov.lower_callsOne`, `Cov.tryCall_callsOne`, `Cov.tryCallInd_callsOne` (the driver's calls).
`iselSim_relWIC`, `backend_correct_worldPRIC`: the pipeline theorems without the two premises
(the originals stay). Witnesses `FV/E2E/IselCallsOneWitness.lean`: `f_hasCall`, `f_segCalls`
(every call statement of `LinkWitness`'s entry `f` has a one-call segment in its compiled code),
`a2_iselSimIC`. The premises are stated for the integer subset (`Compile.functionE`, the
`Compiled` pipeline); they are universal, so every function of the typed scope has them, and a
typed pipeline (`CtxInvT`) would take the same proof over `IselShpTCall`'s typed runs.

**Steps 3h–3j, as built (UninitZ10, branch `agent/uninit-z10`).** Item (a) is complete for both
compile paths.
- `FV/E2E/CountedFam.lean`: `NoncallIndep sem`, `ProbeOf semB sem` (for `sem : Nat → ISem CV W`,
  any world), `SeqEnd.liftW`, `counted_noncall`/`counted_call`, `counted_probe_proj`,
  `seqRun_counted_le1`; instances `noncallIndep_csem`/`probeOf_csem`,
  `noncallIndep_valueSem`/`probeOf_valueSem`. `IselSimI`/`IselSimITry`: the step lemmas and the run
  induction for any such family and memory relation (`stmt_stepG_noCall`, `stmt_stepG_call`,
  `term_stepG`, `term_step_tryG`, `sim_runG`); the `csem` statements (`stmt_stepI_*`, `term_stepI`,
  `term_step_tryI`, `sim_runI`) are unchanged, now instances.
- `FV/E2E/IselSimICleanup.lean`: `valueSemI`, `driverHyp_relW_cleanup`, **`iselSim_relWI_cleanup`**.
- `FV/E2E/BackendWorldCleanupI.lean`: `prune_correctW` (the cleanup simulation `star_sim` is
  world-generic, so `prune_correct` holds for the counted world; `returns_cleanW`/`traps_cleanW`),
  `pureForm_isCallI`/`cmpForm_isCallI`, `counted_pure`, `cmpOverwrite_counted`,
  `DriverSemG.counted`, `valueSemV_sub`, `gotInvI_step_value`/`_star_value`,
  `vRetFrom_gotV_valueI`/`vTrapFrom_gotV_valueI`, **`backend_correct_world_cleanupPRI`**
  (`backend_correct_worldPRI`'s conclusion for `CompiledCleanup`).
- `FV/E2E/CompiledEitherI.lean`: **`backend_correct_world_pipelinePRI`** (`CompiledEither`).
- `FV/E2E/PairDriverI.lean`: `counted_pair_proj₁`/`₂`, `noncallIndep_pair`, `probeOf_pair`,
  `xNI_none`, **`vcode_niI`**: the pair driver per CLIF step (family `pairSem (csem F ctx (XI.at
  n))`, `MRP`), with `XNI` of call `n` needed, like the callee contracts, only at the CLIF states
  reached after `n` calls and for the environment restricted to their invocation (decision:
  per-state, the same shape as `hX`; the old one-`X` `XNI` premise is the special case).
  `FV/E2E/PairDriverICleanup.lean`: **`vcode_niI_value`**.
- `FV/E2E/BackendWorldNII.lean`: `backend_correct_world_niPRI`, `backend_correct_world_ni_cleanupPRI`,
  **`backend_correct_world_ni_pipelinePRI`** (`backend_correct_world_ni_pipeline`'s two clauses,
  counted: `ActEntryPR` activations, `XTls F (XI.at 0)`; the two outcomes are identified by the
  world-generic `vRetFrom_det`).
- Witnesses `FV/E2E/BackendWorldCleanupIWitness.lean` (`DeadCleanupWitness.source`, the closed
  cleanup compilation that removes an instruction): `source_callsOne`, `source_xcalls`,
  `source_xni`, `cleanupPRI_applies` (through `backend_correct_world_pipelinePRI`),
  `ni_pipelinePRI_applies`.

Item (b) interface, as built: `FV/E2E/ClifEnvOnlyContracts.lean`: `xCallsOk_only_of`,
`xCallsIndOk_only_of`, `xNI_only_of` (the per-state premises from the contract at the admitted
invocations only, the shape to discharge at the machine's `n`-th call), `xCallsOk_only`,
`xCallsIndOk_only`, `xNI_only` (an environment's contract holds for each restriction, so the
one-`ExtSem` premises give the per-state ones for `ExtSemI.const X`); witness `source_only`.
`InstCallsOne`/`TryCallsOne` are theorems in #675 (UninitZ10b: `instCallsOne_all`,
`tryCallsOne_all`); the premise-free `*_PRIC` corollaries of 3i/3j are one-liners once both are on
main.

Next: item (b) proper (`thmPR_of` on `backend_correct_world_ni_pipelinePRI`: discharge `hX`/`hNI`
per state through `xCallsOk_only_of` from `progCallPR`/`calleeOkPR` at the machine's `n`-th call,
`counter_at` along `ReachN`), item (d) (`WorldEntryB`), item (e).

**Design notes for (b)+(d) (UninitZ10, not built).** With the oracle the CLIF outcome of an
activation depends on its byte table, and the table must be the machine's: entry `j` is the memory
at the `j`-th placed activation with slots that the whole machine run enters (§5.5). So the oracle
statement cannot choose the outcome before the machine activation, as `ThmPR` does for `(P, R)`:
the table, `P := prophOf` and `R := prophStOf` are all functions of the machine entry `s`. Proposed
shape: `ThmPRB κ M` = for every `g`, CLIF entry placed with `PlaceAtB cs.mem (spv w₀) ini`
(`WorldEntryB`) and machine entry `s` (`MachEntryPR … (prophOf s) (prophStOf s)`) whose run's
entry-order table agrees with `ini` from `ini.next` on (`TableOf s ini`: for the activation's
`n`-th call, the entries `ini.next + slotted g + sumTo E n …` are the callee run's, `counter_at`),
a returning CLIF run gives one counted outcome realised by `s`. The induction step (`thmPRB_of`)
uses `backend_correct_world_ni_pipelinePRI` with `XI := L.XPRI κ M g F (prophOf s) (prophStOf s)`
and discharges `hX` at the state `s'` reached after `n` CLIF calls with `xCallsOk_only_of`: only
the actual invocation (memory `s'.mem`, placed at the counter `counter_at` gives) and the machine's
`n`-th call (`OnCallPR`) are related, and the callee's CLIF run reads the table entries the callee's
machine run entered, i.e. `ThmPRB (M - 1)` for the callee with `ini.adv (counter)` and the
canonical callee run (`progCallPR`) — its entry-order table is the caller's table from that
counter on because the canonical callee state agrees with the actual call state on the region
(`P n`) and the masked registers (`R n`), the determinism clause (item (c), UninitZ10b's lock-step).

**Finding (UninitZ11, 2026-10-28): the `hX` of the design above cannot be discharged as stated.**
`xCallsOk_only_of` restricts the *CLIF* side to the actual invocation `(vals, cm)`, but its
premise still quantifies over every VCode `(uses, w)` with `ArgsAt ext.sig vals uses w` and
`RelW … cm w`. `ArgsAt` fixes only the low `ty.width` bits of a register argument (`VHolds`), and
`RelW` fixes neither `x29`/`x18`/flags/TPIDR nor the world bytes outside `cm`'s live allocations.
`XPR n`'s canonical callee state is built from `(uses, w)` (`canon` puts the full 64-bit `uses`
in the argument registers), so for two such `(uses, w)` the canonical callee runs can differ in
what they spill: Cranelift spills an integer register as 64 bits whatever its CLIF type. A later
nested callee whose slot overlaps that spill and reads it unwritten then reads different bytes in
the two runs, while the CLIF callee run, with the oracle `ini` fixed, reads one table entry. So
`XCallsOk … (XPRI.at n)` is false in general, and `EntryAgree` (the determinism clause) does not
apply either, since it needs the masked registers, argument registers included, equal.
Decision (to build next, no stage-1/stage-2 proof changes): a new call semantics `XPRB` that is
`XPR n` on the *actual* call and an ε-chosen related result elsewhere. `ActualCall n d uses w`:
`w` agrees with the machine's `n`-th call state `R n` (`prophStOf`) outside `F` (`SameWorld F`)
and the argument values are `R n`'s argument registers, 64 bits. Stage 2 (VCode → Arm,
`CalleeOkGP` at `OnCallPR … n`) only ever asks for the result at such `(uses, w)`:
`OperandsSoundCtlAtI` gives `SameWorld F s w` and `uses = useVals ops regs s` at the machine
state `s`, which is `R n` there, so `calleeOkPR` applies unchanged through `XPRB = XPR` on
`ActualCall`. Stage 1 (`hX`, per CLIF state, `xCallsOk_only_of`): at an actual `(uses, w)` the
canonical callee state agrees with the actual one on every register but `x30`/pc and outside `F`,
and on the region (`P n`), so `EntryAgree` and the determinism clause transfer the table, and
`ThmPRB (M - 1)` gives the related result; at any other `(uses, w)` the result is the ε-choice
of a related one, which exists because the CLIF invocation of call `n` is unique (`ReachN`,
deterministic run) and a world related to `cm'` exists (`w` with `cm'`'s bytes written; the
callee keeps the allocations, `runLoop_allocs`). Only program callees need this (base externs keep
`L.Ok`'s all-world contract), and only with `NeedSlots`. `XNI` is not needed for `ThmPRB`
(statement per actual activation, §5.1 (i)). Alternatives rejected: restricting the stage-1
contract to the counted VCode run's call states (needs `hX` variants through
`iselSim_relWI`/`sim_runG` and the pipelines); a `w`-independent `XI` (the actual callee result
cannot be shown related to `cm` in stage 1 without stage 2's invariant).

As built (UninitZ11, stage 1 of the decision): `FV/E2E/ExtSemGuard.lean`: `ExtSem.guard`,
`guard_of`, `guard_spec`, `CallPost` (the results `XCallsOk`/`XCallsIndOk` accept for a call),
`xCallsOk_guard`, `xCallsIndOk_guard`. `FV/E2E/RelWPatch.lean`: `patchW cm' w` (`w` with `cm'`'s
initialised live bytes), `relW_patchW`. `FV/E2E/CallPostExists.lean`: `valCV`, `outsOf`,
`callPost_only_exists` (one invocation), `invoked_unique`, `callPost_invoked_exists` (the
environment restricted to a state's invocation; premises: the returning invocation keeps the
allocations and symbols, and fixes the ABI return count). Next: `XI.at n` cannot depend on the
state, so the guard's `Q` uses the invocation of the call state with count `n`
(`InvokedN n := ∃ s, ReachN … s n ∧ Invoked … s`, single-valued in a deterministic run: the
invoking state is the last of its count's segment), plus `CallPost` antitone in the restriction
(`env.only A'` for `A ⊆ A'`) and an `xCallsOk_guard` for any `Q` implying `CallPost`; then
`XPRBI` and stage 2 (`guard_of` at `OnCallPR` states).

As built (UninitZ12, `InvokedN` and the stage-1 discharge): `FV/E2E/InvokedN.lean`:
`reachN_uncons`, `reachN_cmp` (the reached states lie on one path), `reachN_call_unique`,
`InvokedN`, **`invokedN_unique`**, `NoRetCall` + `noRetCall_of_linv`, `callNum_of_invoked`,
`invoked_sub_invokedN`, `callPost_invokedN_exists`. **Finding:** a `return_call` to an extern
has `callNum = 0` and its step can continue in the caller (`stepReturnCall` → `returnValues` →
`.next`), so a later call in the same run could have the same count and `InvokedN` would not be
single-valued. **Decision:** scope condition `NoRetCall` (no reached state ends in
`return_call`; cg_clif emits none; `callNum` is not changed), discharged from `Clif.LInv` for
`LinkFree` functions (the existing link scope already demands `linkFreeB`).
`FV/E2E/BackendWorldPRB.lean`: `ExtSemI.guardI XI Q` (call `n` is `(XI.at n).guard (Q n)`),
`CallPostN`, `InvokedRetOk` (the returning invocation keeps allocations and symbols; its
declarations agree on the ABI return count), **`hX_guardI`** (the per-state `hX` of the
counted pipelines for `XI.guardI (CallPostN …)`, any `XI`), **`backend_correct_world_cleanupPRB`**,
**`backend_correct_world_pipelinePRB`** (the `*_PRIC` theorems with `hX` replaced by `NoRetCall`
and `InvokedRetOk`; the NI clause is not carried: §5.1 (i)). Witnesses
`FV/E2E/BackendWorldPRBWitness.lean`: `InvokedNWitness.{invokedN_sCall, noRetCall_sCall,
invokedRetOk_sCall, hX_sCall}` (a state at `call fn0()` to a returning extern),
`DeadCleanupWitness.{prb_applies, prb_pipeline_applies}`. So `XPRBI := (L.XPRI …).guardI
(CallPostN …)`; stage 2 needs `guard_of` at the machine's call states.

**Item (d) statement layer, as built (UninitZ12): `FV/E2E/LinkArmTableB.lean`.** The linked
machine runs a program callee atomically (`pcall` = `linkedCall` of `mach (M - 1) h`), so the
machine side of the byte table is recursive in the depth. Table entry `k` is the memory at the
entry state of the `k`-th placed activation with slots (= the memory at the call, the body-entry
world has the entry memory, `BodyEntry.mem`), restricted to its slot bytes.
- `CallsTo g t h` (the step at `t` calls `h` of `P`: `bl n`, or `blr` to `h`'s address, as
  `callHook`), `SlotByte h c a` (the slot addresses `initState_memB` gives), `RetAt g s t`;
- **`TabUpTo M g s b k N e`**: the first `N` steps of `mach M g` from `s` enter the placed
  activations with slots `k + 1, …, k + e` of `b`; per call `j` (`callsBefore`) a count `E j`:
  `0` at a call outside `P`, else `slotted h` (its slot bytes `= b (k + Σ_{<j} E + 1)`, the memory
  at the call) plus the callee run's own `TabUpTo (M - 1)` up to its first `RetOf`; depth `0`:
  no program call, `e = 0`;
- **`TableOf M g s ini`**: every prefix before `RetAt` has a `TabUpTo … ini.bytes ini.next`;
- **`WorldEntryB`** (`WorldEntry` with `NeedSlots → PlaceAtB cs.mem (spv w₀) ini`),
  `WorldEntryB.toWorldEntry` (without `NeedSlots`);
- **`ThmPRB κ M`**: for `g`, a `WorldEntryB … ini`, a machine entry `s` with
  `MachEntryPR … (prophOf s) (prophStOf s)` and `TableOf M g s ini`, a returning CLIF run under
  `envR M g` gives `us outs wf n e` with `ThmPR`'s facts, `ActRet`/`PostTrace` at `n`,
  `TabUpTo M g s ini.bytes ini.next n e` and `NeedSlots → NextAdv cs.mem cm' e` (the machine's
  count is the CLIF counter's advance: what the caller needs for its later calls);
- **`XPRBI κ M g F P R env cs c`** `:= (L.XPRI …).guardI (CallPostN env L.P.bare cs …)`,
  `XPRBI_of` (stage-2 interface: `guard_of`), `tabUpTo_zero`, `tabUpTo_mono`, `tableOf_of_retAt`.
Witnesses `FV/E2E/LinkArmTableBWitness.lean` (on `Lu`). The determinism clause is not part of
`ThmPRB`: `thmPRB_of` takes it as a stated premise (UninitZ10b's `thmPDER_det_of` interface, with
`TabUpTo` transferred between agreeing entries) until it lands.

**Finding (UninitZ12, 2026-10-28): stage 2 needs the CLIF/machine call correspondence of the
earlier calls.** At the machine's call `n` (`OnCallPR … n`), `guard_of` needs `XPR n`'s result
accepted by `CallPostN n`: for the CLIF invocation `(m_n, vals_n)` of count `n` related to the
call's world, the callee's CLIF run (`ThmPRB (M - 1)`, `WorldEntryB` with `m_n`'s oracle) must
read the table entries the machine callee entered. `m_n`'s counter is `ini.next + Σ_{j<n}
adv_j` (`counter_at`, CLIF advances), the machine's is `ini.next + Σ_{j<n} E j` (`TabUpTo`).
They agree when every earlier CLIF invocation `j` is the one the machine's call `j` simulates
(then `ThmPRB (M - 1)`'s `NextAdv` conclusion gives `adv_j = E j`), but that correspondence is
known only inside the simulation (`sim_runG` + the register level); the contracts `hC n` of
`ActEntryPR` are demanded for all `n` up front, and stage 2 sees only the Arm/VCode side. An
index-dependent memory relation (counter `= C n`) cannot be threaded through the rule-level
contracts (§5.9 first Finding).
**Decision (next, conservative: new files, no existing statement changed): a prefix form of the
counted pipeline.** `backend_correct_world_*PRB_upTo`: from the CLIF entry and an `ActEntryPR`
whose callee contracts are given only for the indices `j < n`, every CLIF state with count `n`
reached from `cs` is matched by a machine state on the run with `callsBefore = n` (an `OnCall …
n` state at a call, `SameWorld F` with a VCode world `RelW`-related to the CLIF memory, the
arguments `ArgsAt`). `thmPRB_of` then proves `hC n` by strong induction on `n`: the prefix
theorem at `n` gives the correspondence of every invocation `j ≤ n`, `ThmPRB (M - 1)` at each
`j < n` gives `adv_j = E j`, so the counters agree at `n`, `TableOf` of the actual callee comes
from the caller's `TabUpTo` prefix, the determinism premise transfers it to the canonical callee
(`progCallPR`), and `ThmPRB (M - 1)` gives `CallPost` for `XPR n`'s result. Ingredients: the run
inductions `sim_runG` (CLIF → counted VCode) and `realizes_allC`/`countedRun` (VCode → Arm) are
already sequential, so the prefix forms are copies stopping at the first count-`n` state.
As built (UninitZ12), the CLIF → counted-VCode half: `FV/E2E/IselSimIPrefix.lean`: `PrefixAt`,
**`sim_prefixG`** (induction on `ReachN` from the root: every reached state is matched by a state
of the counted run with counter `n`, or is the pending `jump` of a matched `try_call` state),
`sim_prefix_call` (calling states are matched), **`iselSim_prefixWI`** (`Compiled` path, the
premises of `iselSim_relWI`: a calling CLIF state with count `n` has its memory `RelW`-related to
a world the counted VCode run from the entry reaches with counter `n`). Witness
`FV/E2E/IselSimIPrefixWitness.lean` (`a2_prefixWI`). Cleanup path:
`FV/E2E/IselSimIPrefixCleanup.lean`: **`iselSim_prefixWI_cleanup`** (`valueSemI`); witness
`DeadCleanupWitness.prefix_cleanup_applies`. Next: the VCode → Arm prefix (contracts `hC j` for
`j < n` only, concluding the `OnCall … n` machine state), then the GOT/prune steps.

**The VCode → Arm prefix and the composed prefix pipeline, as built (UninitZ13, branch
`agent/uninit-z13`).** No existing statement or module changed (new leaf modules only).
- `FV/E2E/RegLevelPrefixC.lean`: `ExtSemI.upTo XI N` (the calls `j < N` of `XI`, failing calls
  from `N` on) with `upTo_at_lt`/`upTo_at_ge`, `csemV_call_congr`, `vctr`, `vstep_counted_ctr`,
  **`vstar_counted_upTo`**/`vstar_upTo` (a counted run to counter `≤ N` uses only the calls
  `j < N`), `calleeOkGP_upTo_ge`/`calleeTryOkGP_upTo_ge` (from `N` on the contracts are vacuous:
  the calls fail; the hook's pc is a separate premise), `tlsOk_upTo`; `isSimulation_match`,
  `match_init` (`checkedAt_sound` with its relation `Match` named), **`match_op_uses`** (at an
  instruction item the machine's operand values are the VCode's), `match_to_op` (past the pending
  moves); `CallSiteAt` (the premises of a call contract at a machine state, without the call's
  result: stack, kept bytes, `CallAt`, `SameWorld F u w`, alignment, `ERR`, `useVals = uses`);
  **`regLevel_prefix_core`** (any counted family the machine realises from the call-`n` states:
  every VCode state with counter `N` at a call is matched by an `OnCall … N` machine state at the
  body `sp` with `CallSiteAt`); **`regLevel_prefixC`** (`regLevelCorrect_world_atCS`'s premises
  with the contracts `n < N` only; the contracts of `XI.upTo N` from `N` on are vacuous, so the
  existing `realizes_allC_sp` applies unchanged), `regLevel_prefixPRS` (from `checkAlloc`, with
  the prophecies, contracts in `OnCallPR` form).
- `FV/E2E/BackendPrefixI.lean`: `callDest`, `callLike_of_isCallI`, `csem_call_some`,
  **`vstar_call_at`** (a counted run past counter `j` passes a successful call at counter `j`),
  `prep_prefixW` (`prepare` on run prefixes, with the instruction the same up to its targets),
  `sameInst_callLike`, `ActEntryPRN` (`ActEntryPR` with the contracts `n < N` only, and the
  hook's pc), `ActEntryPR.toN`, **`backend_prefixPRI`** (`Compiled`): for a CLIF calling state
  reached after `N` calls, every call `j < N` of the counted VCode run is realised by the
  machine's `OnCall … j` state `u` (body `sp`, `CallSiteAt` with the VCode call's `uses`, `w`), and
  `(XI.at j).call (callDest info) uses w = some r`.
- `FV/E2E/DeadCleanupPrefix.lean`: `valueSemV_call_congr`, `vstar_upTo_value`,
  `regLevel_value_prefixC`/`_prefixPRS`, `prune_prefixW` (a kept instruction reached by the VCode
  is reached by the cleaned VCode, same block and world, same operand values),
  `valueSem_callLike`, **`backend_prefix_cleanupPRI`** (`CompiledCleanup`, the path
  `Link.DeadCleanup` uses; the decomposition `vstar_call_at` is done on the CLIF-side VCode, then
  mapped through the cleanup, `prepare` and the GOT).
- Witnesses `FV/E2E/BackendPrefixIWitness.lean`: `LinkWitness.{upTo_const_at, a2_prefixPRI}`,
  `DeadCleanupWitness.prefix_cleanupPRI_applies`.

The correspondence of the earlier calls, as built: `FV/E2E/PrefixRelated.lean`: `ExtSemI.relOnly
XI Q` (call `n` of `XI` where `Q n d uses w`, undefined elsewhere), `relOnly_call_some`/`_of`,
`csemV_of_call_sub`, `CalleeOkGP.ofCallSub`/`CalleeTryOkGP.ofCallSub` (the machine contracts are
antitone in the call results), `ActEntryPRN.relOnly`, `RelatedN` (the call's `CallPostN` is not
vacuous), `xCalls_relOnly` (stage 1 for `XI.relOnly (RelatedN …)` from stage 1 for `XI`: every
query of the extern contracts is related, `callPost_not_vacuous`), **`prefix_related_cleanupPRI`**,
**`prefix_relatedPRI`**: `backend_prefix*PRI`'s conclusion plus `RelatedN … j (callDest info) uses
w` at the machine's call `j < N` (premise `NoRetCall` added). Witness
`FV/E2E/PrefixRelatedWitness.lean` (`relOnly_none`, `relOnly_all`, `prefix_related_applies`).

**Finding (UninitZ13, 2026-10-28): `XPRBI` cannot meet the stage-2 contract when program callees
have slots.** `XPRBI := (L.XPRI …).guardI (CallPostN …)` answers `XPR`'s result where `CallPostN`
accepts it and otherwise an ε-chosen accepted result; the machine contract (`CalleeOkGP`) then
needs the machine's callee result to *be* the answer at every `OnCallPR … n` call state. But
`XPR`'s `progX` is defined only under `Cond`, whose CLIF witness memory is placed with
`PlaceAt cm (spv w)` (oracle `none`); with `NeedSlots` the CLIF memories of the run are placed
with `PlaceAtB … (some ini)`, so at the actual call `Cond` is witnessed only if some `none`-placed
memory makes the callee's CLIF run return — not implied (the callee may read an unwritten slot
byte). Where `XPR` is `none` the guard answers ε and the contract fails. Second, where
`CallPostN` is vacuous (no CLIF invocation of count `n`, or none related to `(uses, w)`), a `none`
of `XPR` also becomes an ε answer, while the unguarded `XPR`'s contracts are vacuous there.
**Decision (conservative, new definitions only):** (1) `CondB`/`progXB`/`XPRB`: `Cond` with
`∃ ini, PlaceAtB cm (spv w) ini` (the result is still the machine's `pcall` from `canon`, so the
generated code and `progX`'s users are unchanged); (2) a guard that keeps `none` where no CLIF
invocation is related (`ExtSem.guardR`: ε only when `CallPost` is not vacuous), so the contracts
outside the simulated calls stay vacuous; (3) `progOsPRB`/`calleeOkPRB` on `ThmPRB (M - 1)` (the
`progOsPR` proofs with `WorldEntryB`/`TableOf` from the table prefix `TabUpTo` at the call and the
counter equality from `prefix_related*PRI` + `NextAdv` of the earlier calls), by strong induction
on `n`. As built (UninitZ13), (1) and (2): `FV/E2E/ExtSemGuardR.lean`: `ExtSem.guardR`,
`guardR_of`, `guardR_spec`, **`guardR_eq_of`** (stage 2: where every non-vacuous contract accepts
`X`'s result, every answer is `X`'s), `callPost_not_vacuous`(`_ind`), **`xCallsOk_guardR_only`**;
`FV/E2E/LinkArmXPB.lean`: `ExtSemI.guardRI`, **`hX_guardRI`** (stage 1 for any `XI`), `CondB`
(`Cond` with, under `NeedSlots`, `PlaceAtB cm (spv w) ini` and `TableOf (M - 1) g (enterAt (canon
…)) ini`: the oracle is the canonical callee run's table, so `ThmPRB (M - 1)` applies to the
canonical callee), `cond_iff_condB` (without `NeedSlots`), `progXB`, `progXPRB`, `XPRB`, `XPBI`,
`XPRB_of_not_needSlots`, **`XPBG`** (`XPBI` guarded by `CallPostN` with `guardR`: the `XI` of the
induction step, replacing `XPRBI`), `XPBG_eq_of`. Witnesses `FV/E2E/LinkArmXPBWitness.lean`
(`guardR_vacuous`, `hX_sCall_R`, `XPRB_Lu`). `ThmPRB`'s statement does not mention `XPRBI`, so it
is unchanged.
Next, (3): `progCallPRB` (copy of `progCallPR`, `LinkArmProgCallPR.lean`, 650 lines) on
`ThmPRB (M - 1)`: `initState_memB` with `PlaceAtB` (LinkPlaceB), the callee's `MachEntryPR` with
`(prophOf, prophStOf)` as there, `TableOf` from `CondB`; the transfer from the canonical callee
state to the actual call state (`progCallPR`'s `∀ t, CallerOk … → agreement → …` clause) needs the
determinism clause, here a stated premise `DetPRB κ (M - 1)` (ThmPDER's determinism clause for
`ThmPRB`'s outcome, plus `TabUpTo` carried to the agreeing run) until `thmPDER_det_of` (UninitZ11b,
blocked on `ReadsIn`, UninitZ12b's #682) gives it. Then `progOsPRB`/`calleeOkPRB` (copies of
`LinkArmProgOsPR.lean`), and the stage-2 obligation of `XPBG_eq_of` at `OnCallPR … n` call states
where `RelatedN … n` holds: `CondB` at the actual call with `ini := ini.adv (counter)` (the counter
equality from `prefix_related_cleanupPRI` at every `j < n` and `ThmPRB (M - 1)`'s `NextAdv`), by
strong induction on `n`; then `thmPRB_of`, `thmPRB`, item (e).

**Step 3k, as built (UninitZ10b): the call-count premises are theorems.** `InstCallsOne f` and

**(3), as built (UninitZ14, 2026-10-28).** Finding: `CondB` is too weak for `ThmPRB (M - 1)`: the
callee's CLIF entry is placed with `calleeIni h ini` (`ini.adv 1` when `h` has slots,
`initState_memB`), so the canonical callee run's table must be `calleeIni h ini`'s, also without
`NeedSlots` (`TableOf` at depth `0` excludes program calls), and the new slot bytes
`ini.bytes (ini.next + 1)` must be the call world's memory (else `RelW` fails on them). Decision
(new names, `CondB` kept): `FV/E2E/LinkArmXPBT.lean`: **`CondBT`** (both added), `progXBT`,
`progXPRBT`, `XPRBT`, `XPBTI`, **`XPBTG`** (the `XI` of the induction step), `XPBTG_eq_of`,
`XPRBT_{prog,none,ind,base,ext}`. `FV/E2E/LinkArmProgCallPRB.lean`: **`DetPRB κ M`** (`ThmPDER`'s
determinism clause for any outcome of a `ThmPRB` entry `s₀` with its own prophecies and table,
plus `TabUpTo` with the same count on the agreeing run), `calleeIni`, **`progCallPRB`** (premises
`ThmPRB (M - 1)`, `DetPRB (M - 1)`, `PlaceAtB`, slot bytes, callee table; conclusion: one outcome,
`NextAdv` of the callee's CLIF run, and for every compatible caller state the linked call's
`ActRet` and `TabUpTo` with that count; the non-interference clause of `progCallPR` is not
restated, `DetPRB` covers both cases). `FV/E2E/LinkArmProgOsPRB.lean`: `progOsCorePRB`,
`progOsCoreXPRRB`, `progOsPRB`, `progOsRegPRB`, **`calleeOkPRB`**, **`calleeTryOkPRB`** (for
`XPRBT … n`). `FV/E2E/BackendWorldPRG.lean`: **`backend_correct_world_{cleanup,pipeline}PRG`**
(`guardRI`, stage 1 by `hX_guardRI`); witnesses `FV/E2E/BackendWorldPRGWitness.lean`.
Item (e): `Link.DeadCleanup.compileExe` compiles every function by the untyped cleanup path
(`compiledCleanup_of`, `FV/E2E/DeadCleanupExecMemTrap.lean`: `CompiledCleanup`), so the prefix
files already cover it; the typed `CompiledCleanupT/TC` are `compileExeT{,3}`'s only.
Open for stage 2: `CondBT` at `worldPR (P n) (R n) w` needs the canonical callee run's table,
while the caller's `TableOf` gives the actual call's; a transfer `TableOf s → TableOf s₀` for
`EntryAgree`-related entries (a second determinism fact, `DetTabPRB`, stated premise like
`DetPRB`) is needed, then `XPBTG_eq_of` by strong induction on `n`, `thmPRB_of`, `thmPRB`.

**Stage 2 groundwork, as built (UninitZ15, 2026-10-28, PR #688).** Decisions (new names, old
statements kept):
- `DetTabPRB κ M` (`FV/E2E/LinkArmDetTabPRB.lean`): the second determinism fact, stated
  call-shaped with `progCallPRB`'s premises: a call state `t` with `CallerOk`, the canonical
  state's masked registers but `x30`/pc and its bytes in `StackBelow (frameDrop + κ (M - 1))`
  moves `TableOf (M - 1) h (enterAt t) (calleeIni h ini)` to `enterAt (canon h uses w)`;
  `progCallPRB_at`. A premise beside `DetPRB`, both for `thmPDER(X)_det_of`.
- Finding [#687](https://github.com/eth-act/clifv/issues/687): `ThmPRB` is unsatisfiable at
  entries with `ra = base` (`RetAt g s s`, so `TableOf` holds for every oracle,
  `tableOf_of_retAt`, while the conclusion's table pins the first slotted callee's bytes).
  `ThmPRBR` adds `RaOk (L.A g) (ra - 4)` (every linked call has it; a top-level entry has `ra`
  outside the code), `ThmPRB.toR`; R-variants `progCallPRBR(_at)`, `progOsCorePRBR`,
  `progOsCoreXPRRBR`, `progOsPRBR`, `progOsRegPRBR`, `calleeOkPRBR`, `calleeTryOkPRBR`.
  `noRetAt_of` (under `RaOk` no `RetAt` precedes the return: `retStuck` / `PostTrace`) and
  **`thmPRBR_of_thm`** (`¬ NeedSlots`: `Thm κ M → ThmPRBR κ M`), so `ThmPRBR` holds at every depth
  for systems without slotted callees (witness `thmPRBR_LU`).
- `tabUpTo_count` (`FV/E2E/LinkArmTabCount.lean`): the count of a table prefix is unique
  (independent of table and offset), which ties `progCallPRB`'s per-call count (`NextAdv`) to the
  caller's `E j`.
- Finding [#690](https://github.com/eth-act/clifv/issues/690): `ActEntryPR` for `XPBG`/`XPBTG`
  is unprovable: `CalleeOkGP.ext` asks the guarded answers to keep the program, `guardR`'s ε
  answers are only `CallPost`-accepted, and `CallPost` never constrains the program.
  `FV/E2E/ExtSemGuardRX.lean`: `CallPostX := CallPost ∧ ExtOkR`, `CallPostNX`, `fixW`,
  `callPostNX_exists`, `xCallsOk_guardRX_only`, **`guardR_ext`**, **`hX_guardRXI`**;
  `FV/E2E/BackendWorldPRGX.lean`: **`backend_correct_world_{cleanup,pipeline}PRGX`**;
  `FV/E2E/LinkArmXPBTX.lean`: `XPBTGX` (the `XI` of the induction step), `XPBTGX_ext`,
  `XPBTGX_eq_of`.
- `FV/E2E/LinkArmEnvOfB.lean`: `PlacedB`, `envOfB` (program callees guarded by "placed with some
  oracle"), `ActInvB`, `actInvB_step`, `step_envOfB`, **`runLoop_envOfB`** (the activation's
  environment for `backend_correct_world_*PRGX` in `thmPRBR_of`, as `envOf` in `thm_of`).

Next (`thmPRBR_of`, in order): (a) the CLIF counter along `ReachN` under `ActInvB`: the state
after `k` calls is placed with `ini.adv (sumTo A k)`, `A j` the advance of invocation `j`
(`InvokedN`; `placeInvB_step`, `NextAdv.unique`); (b) stage 2 at call `n` (strong induction on
`n`): at an `OnCallPR … n` state `t` whose call is `RelatedN … n`, `CondBT` at `worldPR (P n)
(R n) w` with `ini := ini0.adv (sumTo A n)` (= the caller table's offset by (a), `tabUpTo_count`
and `progCallPRBR`'s per-call count for `j < n`), the slot bytes from `TabUpTo`'s call clause,
the canonical table by `DetTabPRB`, and `CallPostNX` of `XPRBT`'s answer (`progCallPRBR`'s
outcome, `XPRBT_ext`); then `CalleeOkGP` for `XPBTGX … n` at the `OnCallPR` states from
`calleeOkPRBR` (a `P`-restricted `ofCallSub` with `XPBTGX_eq_of`, `ext` by `XPBTGX_ext`); (c)
`thmPRBR_of` from `backend_correct_world_pipelinePRGX` with `XI := XPBTI`, `env := envOfB`
(`runLoop_envOfB`), the table to the return by `noRetAt_of`, `NextAdv` by (a) at the return;
(d) `thmPRBR` by induction on `M`; (e) `compileExe_correct_init`.

**Stage 2 and `thmPRBR_of`, as built (UninitZ16, 2026-10-28).**
- (a) `FV/E2E/LinkPlaceBReach.lean`: `advAt env p cs j` (the counter advance of the step of the
  calling state of count `j`; unique: `advAt_eq`), **`nextAdv_reachN`** (a bare activation reached
  after `k` calls has `cs`'s oracle advanced by `sumTo (advAt …) k`; non-call steps keep the
  oracle, `step_bare_noCall_place`), **`LinkSys.counter_reachN`** (`PlaceAtB s.mem c
  (ini.adv (sumTo (advAt …) k))` from `WorldEntryB.place`), `envAdv_envOfB`, `initState_linv_only`.
- Finding [#692](https://github.com/eth-act/clifv/issues/692): `CallPostNX` (#690) is never
  vacuous at a world without error, so `guardR` answers ε-junk where `XPRBT` has none, also at
  calls unrelated to the CLIF run (e.g. a later activation at the same `sp`, which `OnCallPR`
  admits); `CalleeOkGP.os` of `XPBTGX` is unprovable there. Fix (new names):
  `CallPostXR := CallPost ∧ ((¬ ∀ r', CallPost r') → ExtOkR w r)` (vacuous exactly where
  `CallPost` is), `CallPostNXR`, `guardR_extV`, `hX_guardRXRI`, `guardRXRI_ext`, `guardRXR_sub`
  (`FV/E2E/ExtSemGuardRY.lean`); **`backend_correct_world_{cleanup,pipeline}PRGY`**.
- (b) interface, `FV/E2E/LinkArmStage2Y.lean`: `CalleeOkGP.ofCallSubW` /
  `CalleeTryOkGP.ofCallSubW` (antitone in the call results only at the worlds of the states `P`),
  `XPBTGY`, `XPBTGY_ext`, **`Stage2Y`** (at the states `Q`, where `CallPost` of the invocation of
  count `n` is not vacuous, `XPRBT … n` answers a `CallPost`-result), `XPBTGY_sub`,
  **`calleeOkXPBTGY`**, **`calleeTryOkXPBTGY`**.
- Finding [#694](https://github.com/eth-act/clifv/issues/694): `ThmPRB`/`ThmPRBR` end with
  `NeedSlots → NextAdv cs.mem cm' e`, from the entry memory (the activation's `sp` on top) to the
  returned one, which the return popped (`Mem.leave`): false for every returning run under
  `NeedSlots` (witness `not_nextAdv_entry`), so the PRB induction hypothesis is unsatisfiable on
  systems with slotted callees (all earlier witnesses are on `¬ NeedSlots`). Fix (new names):
  **`ThmPRBRL`** with `NextAdv cs.mem.leave cm' e` (`nextAdv_leave_entry`), and the copies
  `progCallPRBRL(_at)` (`FV/E2E/LinkArmProgCallPRBRL.lean`), `progOsCorePRBRL`,
  `progOsCoreXPRRBRL`, `progOsPRBRL`, `progOsRegPRBRL`, `calleeOkPRBRL`, `calleeTryOkPRBRL`
  (`FV/E2E/LinkArmProgOsPRBRL.lean`; same proofs, the conjunct is only passed through).
- (c) `FV/E2E/LinkArmThmPRBROf.lean`: **`thmPRBRL_of`**: `ThmPRBRL κ M` from `ThmPRBRL κ (M - 1)`,
  `DetPRB κ (M - 1)` and three per-activation premises: `RetOkPRB` (`InvokedRetOk` of the run
  under `envOfB`), `Stage2PRB` (`Stage2Y` at `CallStPRB`, the activation's call-`n` states),
  `CountPRB` (the CLIF advance from the popped entry is the machine table's count to the
  return). The `ActEntryPR` is `MachEntryPR`'s fields with `calleeOkXPBTGY` (`callStPRB_q`), the
  table by `noRetAt_of`. `thmPRBRL_of_thm` (`¬ NeedSlots`). Witnesses on `Lu` (`thmPRBRL_LU`,
  `thmPRBRL_of_Lu`, `countPRB_Lu`, `stage2Y_noExt`, …).

Next: `Stage2PRB` is stated at every `CallStPRB … n` state, which includes call-`n` states after
the activation returned (same code and `sp`, another activation); there the related CLIF call `n`
fixes the answer from the prophecies `P n`, `R n` of the activation's own call `n`, whose existence
(before the return, calling the same callee with compatible arguments) needs the simulation up to
call `n` (`backend_prefixPRI` extended to the state *at* call `N`, contracts `j < N` by strong
induction). Base externs are the easy half (`baseX`/`baseXI`, `symInj`); at depth `0` every
returning invocation is a base one (`CrunOk.zero`), so `Stage2PRB κ 0` should follow from that
half alone. `CountPRB` (from (a), `tabUpTo_count`, `progCallPRBRL`'s `TabUpTo … e`/`NextAdv … e`
per call, `prefix_relatedPRI`), `RetOkPRB` (a scope fact of `Ok` + `NeedSlots`: callee runs free
what they allocate, `baseKeepsAllocs`; return-count agreement of the declarations), then
`thmPRBRL` and `compileExe_correct_init`.

**Step 3h, as built (UninitZ10b): the call-count premises are theorems.** `InstCallsOne f` and
`TryCallsOne f` hold for every `f` (`E2E.instCallsOne_all`, `E2E.tryCallsOne_all`,
`FV/E2E/IselCallsOneAll.lean`), from `FV/Backend/Proof/IselCallsOne.lean`:
- the rule-table certificate `Cov.lower_call_fmts` (one `decide +kernel` over the exported rules
  of `lower`, `callFmtOk`): every root rule is a call root (1031–1033), outside the closure
  (`excludedUnmatchable`), or names a root `InstructionData` format whose variant is neither
  `Call` nor `CallIndirect` (`ruleFmt_match`: it cannot match a call, whose data has that format,
  `instData_call_fmt`); `lower_branch` needs none (`tryUnmatchable`, `tryIndUnmatchable`);
- the call roots' runs, copies of the shape inversions (`IselShpCall.run_*`, `IselShpTry.shpTry_*`)
  concluding the count `CallsSince 1` (stack-argument stores, a GOT load, one call):
  `callRun_2508`/`_2518`/`_2529`, `tryRun_2542`/`_2551`/`_2561`;
- `Cov.lower_callsOne`, `Cov.tryCall_callsOne`, `Cov.tryCallInd_callsOne` (the driver's calls).
`iselSim_relWIC`, `backend_correct_worldPRIC`: the pipeline theorems without the two premises
(the originals stay). Witnesses `FV/E2E/IselCallsOneWitness.lean`: `f_hasCall`, `f_segCalls`
(every call statement of `LinkWitness`'s entry `f` has a one-call segment in its compiled code),
`a2_iselSimIC`. The premises are stated for the integer subset (`Compile.functionE`, the
`Compiled` pipeline); they are universal, so every function of the typed scope has them, and a
typed pipeline (`CtxInvT`) would take the same proof over `IselShpTCall`'s typed runs.

**Step 3l, as built (UninitZ10b, branch `agent/uninit-z10b-x30`): the `x30` footprint and the
single steps of the lock-step (§5.8 (1)).**
- `FV/E2E/ArmGprFoot.lean`: `GprFoot.setGpr`, `GprFree k f` (`f` commutes with setting `x_k`),
  one lemma per instruction class of the Arm model (load/store via `reg_imm_common`,
  `reg_pair_common`), `ArmInst.gprs` (the GPR fields a class names; SIMD&FP data registers
  excluded, `x30` added for `bl`/`blr`), **`gprFree_exec_inst`** (`k ∉ ai.gprs → k ≠ 31 →
  GprFree k (exec_inst ai)`): every instruction reads and writes only the GPRs it names.
- `FV/E2E/LinkArmStepX30.lean`: `StEqOutX Z` (all registers but `x30`, program, memory outside
  `Z`), `stEqOut_setGpr30`, `stEqOutX_exec_inst`, `stEqOutX_stepi` (`DecX30Free`: the decoded
  instruction names no `x30`), **`stEqOutX_armStepX`** (unhooked line), `stEqOutX_armStepX_call`.
- `FV/E2E/LinkArmStepFrameRec.lean`: the lines that name `x30`: `stEqOutX_stpFR` (the prologue's
  `stp x29, x30, [sp, #-16]!` adds the record's high 8 bytes `HiBytes A 8 16` to `Z`),
  `stEqOutX_ldpFR` (the epilogue's `ldp` keeps `StEqOutX Z` when the saved `x29` is outside `Z`),
  `stEqOutX_ret` (registers but `x30`/pc: `RetAgree`'s register part).
- Witnesses `ArmGprFootWitness.lean` (`add_x30Free`, `str_d30_x30Free`, `add_writes_x0`, …),
  `LinkArmStepX30Witness.lean` (`add_lockstep`, `stp_lockstep`, `ldp_lockstep`, `ret_lockstep_x0`,
  and `prologue_stp`/`epilogue_ldp`/`ret_insn`: the backend's own frame-record and `ret` encode
  to exactly these instructions).

**Finding (base hooks, decided conservatively).** `HookDet` (step 2o) assumes all registers equal
and differences only strictly below `sp`. In the lock-step the two runs differ in `x30` at a
call until the `bl` overwrites it, and in the caller's saved LR bytes (above the callee's `sp`)
for the whole activation. Program callees are covered by the induction (`EntryAgree` excludes
`x30`; they read above their `sp` only stack arguments). A base extern, an arbitrary function,
could read the caller's frame record (an unwinder taking a backtrace does). Decision: the
multi-step lock-step takes a new base-hook premise `HookDetX` beside `OkD.baseDet` (from
`StEqOutX Z` states, with `Z` below `sp` or within the frame records' LR bytes, a base call or TLS
hook gives `StEqOutX Z` states: the extern does not observe return addresses), `NeedNI`-guarded
like `baseNI`; nothing in the existing statements changes.

**Remaining for `ThmPDER`'s determinism clause (item 3).** (i) A compiled-code check `DecX30Free`
on every body line but `bl`/`blr`/`ret`/the frame-record pair (decidable on `fb`, Cranelift never
allocates `x30`) with its soundness lemma; (ii) `ReadsAvoid Z (stepiEvs u₀)` along the canonical
run from `RL.GoodX.reads` (`Z` = the NI set `D` and the activation's LR bytes; no body line but the
epilogue `ldp` reads the record); (iii) the run induction `lockstep_runX` (`StEqOutX` at every
index up to the return, nested program calls by `ih : ThmPDER κ (M-1)`, base hooks by
`HookDetX`), then `ProphStep` ⇒ `prophOk_congr` (step 2m) and `RetAgree` from `stEqOutX_ret`;
(iv) `LinkSys.thmPDER_det_of`.

**Steps 3m–3o, as built (UninitZ11b, branch `agent/uninit-z11b`).**
- `FV/E2E/LinkArmX30Check.lean` (item (i)): `Insn.x30Exempt` (`bl`, `blr`, `blrTlsDesc`, `ret`, the
  frame-record pair), `Insn.x30Ok`, **`FnAsm.x30Free fa lm`** (decidable: every instruction line is
  exempt or its `toArmInst` at the line's encoder environment names no `x30`),
  **`decX30Free_of_check`** (`RL`) / `decX30Free_of_line` (laid-out function): at a non-exempt
  line of a function passing the check, `DecX30Free`. Measured (throwaway runner over
  `compileFile`, 2026-10-28): corpus + Cranelift runtests 1105 functions / 54572 instruction
  lines (3836 exempt); fv-demo split CLIF 2122 functions / 108285 lines (10812 exempt); survey
  1329 functions / 60030 lines (6054 exempt): 0 failing lines. Witness `x30Free_all` (every
  function of `LinkWitness`'s program).
- `FV/E2E/LinkArmBaseDetX.lean` (the base-hook finding above): `fpChain`, `LRByte` (a saved-LR
  byte of the frame-record chain), **`HookDetX Hb BD`** (from `StEqOutX Z` states with `Z` below
  `sp` or saved-LR bytes, base calls and TLS hooks give `StEqOutX Z` states), `LinkSys.OkDX`
  (`OkD` + `baseDetX : NeedNI → HookDetX L.Hb L.BaseDest`), `Ok.okDX_of_not_needNI`, `Ok.okDX`.
  Trusted (outside code), `docs/contracts/e2e.md`. Witnesses `LinkArmBaseDetXWitness.lean`.
- `FV/E2E/LinkArmStepLine.lean`: `OnLine` (the canonical state at an instruction line of the
  laid-out function), the lock-step per line kind on `ArmStepX`: `stEqOutX_line_free` (checked
  lines; reads avoid `Z`), `stEqOutX_line_call`, `stEqOutX_line_stpFR` (the record's LR bytes join
  `Z`), `stEqOutX_line_ldpFR`, `retAgree_line_ret`, combined **`stEqOutX_line`** (any line but
  `ret`/the TLS tail, to `zNext Z x t`; obligations: a checked line reads nothing in `Z`, the
  `ldp` reloads `fp` from outside `Z`, hooks keep `StEqOutX Z`); **`lockstep_runX`** (the run induction from
  per-index steps). Witnesses `LinkArmStepLineWitness.lean` (a laid-out
  `stp; add; ldp; ret`, each line stepped from two states differing in `x30`).

**Finding (item (ii), decided conservatively: not from `GoodX.reads` alone).** `RL.GoodX.reads`
bounds the reads of the run only away from the kept addresses `G`; it does not keep them out of
the NI set `D` or the frame record. The differing set of the two entries is (outside the
`EntryAgree` region) `D` and the callers' frames in `F`, plus the record's LR bytes after the
`stp`. A body read is a frame-slot read (move code, `moveInsts_reads`), the epilogue's `ldp`
(`memReads_ldp_fplr`), a jump-table word, or a covered form's access (`formOk_reads`: outside
`F`, a CLIF-mapped byte). CLIF-mapped bytes at entry are equal in both runs (`RelW` to the same
`cs.mem`); bytes mapped later are this activation's slots (in the `EntryAgree` region) or
allocations by externs. So `ReadsAvoid Z (stepiEvs u₀)` needs a new per-state fact
(`RL.ReadsIn`: every read is a frame slot, a jump-table byte, the record's `fp` word, or a byte
CLIF-mapped at the state), proven next to `GoodX.reads` in each `realizes_*` case, plus the
CLIF-side fact that a byte mapped at a state was mapped at entry or allocated in the run.

**Step 3p, as built (UninitZ12b, branch `agent/uninit-z12b`): the located reads (item (ii), Arm
side).**
- `FV/E2E/RegLevelReadsIn.lean`: `Insn.ldpFR` (the epilogue's `ldp x29, x30, [sp], #16`),
  `RL.FrameRd lr a` (`spB + o`, `o < frameDrop`, not the record's saved-LR word unless `lr`),
  **`RL.ReadIn lr a`** (a jump-table byte, a `FrameRd` byte, or a byte outside `F`),
  **`RL.ReadsIn u`** (the reads of the unhooked instruction `x` at the pc are `ReadIn x.ldpFR`:
  only the epilogue's `ldp` reads the saved LR word), `RL.GoodXNR` (`GoodXN ∧ ReadsIn`),
  `RL.readIn_ok`/`RL.ReadsIn.readsAt` (it refines D2), builders as for D2
  (`readsIn_of_line/_noLoad/_hooked/_noLine`, `readsIn_execLinesP`, `goodXNR_execLines(G,GP)`);
  `RegLevelGoodXNR.lean` (`goodXNR_ofIns`, `goodXNR_line`).
- The `realizes_*N` cases with `GoodXNR`: `RegLevel{Move,Op,Next,Call,Try,JT,Atomic,Tls,Frame,
  Goto,Trap}NR.lean` (copies of the `*N` files: moves read slots `frameRd_slot`, covered forms
  outside `F` (`formOk_reads`), the jump table its words, atomics outside `F`, the epilogue's
  `ldp` the record (`ReadIn true`); `realizes_callNR`/`realizes_tryCallNR` state
  `GoodX ∧ ReadsIn`).
- Up the counted chain: `realizes_allCR`, `regLevelCorrect_world_atCR`/`_worldCR`/`_worldPRR`
  (`RegLevelCorrectCR/PRR.lean`), `realizes_allC_spR`, `regLevelCorrect_world_atCSR`/`_worldCSR`/
  `_worldPRSR` (`RegLevelCorrectPRSR.lean`), **`backend_correct_worldPRIR`**
  (`BackendWorldIR.lean`): the `*` theorems (same proofs) that also give `actReadsIn` (= `RL.ReadsIn`
  of the activation) at every state of the run before the return. Existing statements unchanged.
- Witnesses `RegLevelReadsInWitness.lean` (`worldPRSR_const`, `a2_worldPRIR`). Axioms standard.

**Finding (item (ii), CLIF side; design for the next step).** For the lock-step the `¬ F`
disjunct must become "a byte equal in both runs". `D` may contain world bytes outside `F`, so
`¬ F` alone is not enough; the bytes the two runs agree on outside `F` are those CLIF holds
(valid and initialised) at the matching CLIF state: both machine runs realise the *same* CLIF run
from `cs` (`iselSim_relWI` applies to `w₀` and to `w₀'`, `RelW` to the same `cs.mem`), and a CLIF
load of an uninitialised byte is stuck (`Mem.load`). Plan: (a) refine the third disjunct of
`ReadIn` per segment to the bytes the realised VCode instruction's `csem` accesses at the
segment's world (`AccessOk`, from `reads_of_accR`/`formOk_reads`, which already have them before
weakening to `¬ F`); (b) from the counted simulation, every such access is a CLIF access of an
initialised valid byte of the matching CLIF state, related to both worlds by `MemRel F`; (c) take
the lock-step sets as the exact difference sets of the two runs (`Zs i a := (runX f i s).mem a ≠
(runX f i s₀).mem a`, plus the record's LR bytes), so a write of equal values shrinks them;
then `lockstep_runX` with `stEqOutX_line` per index gives the determinism clause of
`LinkSys.thmPDER_det_of` (nested program calls through `ih : ThmPDER κ (M-1)`, base calls through
`HookDetX`).

**Item (2), as built (UninitZ13b, branch `agent/uninit-z13b`): guarded world reads, Arm side.**
The guard set is a per-step fact of the VCode run, so it enters as a guard on the VCode
semantics, and `ReadIn`'s third case becomes "outside `F` and outside the step's guard set".
- `RegLevelReadsIn.lean`: `RL.ReadInY Y lr a` (third case `¬ F a ∧ ¬ Y a`), `RL.ReadsInY Y`,
  `RL.GoodXNY Y`; `ReadIn`/`ReadsIn`/`GoodXNR` are the instances at `Y := F` (same meaning). The
  builders and every `realizes_*NR` theorem of a case that reads no world byte are generic in `Y`
  (implicit; the old uses elaborate at `Y := F`).
- The cases that read world bytes take the step's `csem` at `Y` (`formOk_reads`, `loopSem_inv`
  are generic in the frame set): **`realizes_op_nextNY`** (`hsemY`, `Y ⊇ F`),
  **`realizes_rmwLoopNY`**, **`realizes_casLoopNY`**; `realizes_rmwLoopNR`/`_casLoopNR` keep
  their statements (now the `Y := F` instances).
- `RegLevelCorrectCY.lean`: `MInst.wReads` (straight-line forms and atomic loops), **`WGuard F ctx
  X Ok i us w`** (`∃ Y ⊇ F, Ok w Y ∧ (i.wReads → csem Y ctx X i us w ≠ none)`), the guarded
  semantics `csemVG`/`csemVIG` (`csemV`/`csemVI` where `WGuard` holds; `csemVIG_eqF`: at
  `Ok := (· = F)` it is `csemVI`), `RL.WReadsIn Ok u` (`ReadsInY Y u` for a `Y ⊇ F` that is
  everything or admitted by `Ok`), `MStep.guardLift`, **`realizes_allCY`**, `realizes_allC_spY`.
- `RegLevelCorrectPRSY.lean`: `actWReadsIn`, `regLevelCorrect_world_atCSY`/`_worldCSY`/
  `_worldPRSY` (the `*SR` proofs on the guarded semantics); `BackendWorldIY.lean`:
  **`backend_correct_worldPRIY`** = `backend_correct_worldPRIR` with `Ok` and the premise `hGd`
  (the compiled `csemVI` run of `vcp` is a `csemVIG … Ok` run), giving `actWReadsIn … Ok` at every
  state before the return. Witness `BackendWorldIYWitness.lean` (`a2_worldPRIY`, `Ok := (· = F)`).
- Open: `hGd` for the pair (`Ok w Y := Y = Zof F D cm` at a `cm` the pair relates `w` to). It
  needs a per-step refinement of the counted pair run (`vcode_niI`): the rules on `csemG` with
  `Rd := ¬ Zof F D cm` give `GuardR`, hence `csem (F ∪ ¬ Rd)` (loads, atomics); and the transport
  across `prep` (`DriverSemG` of the guarded family). Not started.

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

