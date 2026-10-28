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

