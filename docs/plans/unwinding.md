# S10 (#34): unwinding under the theorems

Plan of 2026-10-16, base main f29d0c06. Branch prefix `agent/unwinding`. Sub-issues of #34:
S10b #229, S10c #230, S10d #231, S10e #232, S10f #233 (one PR each, merged in order; later
slices build on earlier ones; S10a is this plan).

## Status

| Slice | State |
| --- | --- |
| S10a | merged (this plan) |
| S10b | done: `FV/Clif/Unwind.lean` (`Clif.runX`; `runLoopX_of_returned`, `runLoopX_of_trapped`, `runLoopX_toX`; witnesses `Clif.UnwindWitness.caught`/`uncaught`/`old_stuck`), native oracle `scripts/clif-unwind-native.sh` (`rust/crates/clif-throw-native`): 17/17 runs, agree 17, disagree 0 (`docs/contracts/clif.md`) |
| S10c–S10f | open |

## Where we are

* `try_call`/`try_call_indirect` are inside `E2E.backend_correct_final` and every theorem built
  on it **for their normal returns only** (`docs/contracts/e2e.md`, "`try_call` (the normal
  return)"). `Clif.run` has no unwinding: `Clif.stepTryCall` is the call followed by the jump to
  the normal-return successor. `cargo fv` labels such functions
  `verified (normal returns; unwinding trusted)` (`rust/crates/cargo-fv/src/report.rs`
  `NORMAL_RETURNS`, from `lean-backend`'s `compiled, verified for normal returns` line,
  `FVTest/Backend/Main.lean`); last counts: fv-demo 253–254, survey 498 (`docs/USAGE.md`).
* Trusted and outside every theorem today: the landing pads (the handler edge blocks of a
  `tryCall`, `FV/Backend/Isel.lean` `lowerFunction`), the exception payload on the handler edges
  (`gen_try_call_rets`: x0/x1), the call-site table (`Backend.callSites`,
  `FV/Backend/Unwind.lean`) and its LSDA bytes (`Backend.lsdaBytes`, `.gcc_except_table`), the
  CFI rows (`Backend.unwindRows`) and their `.eh_frame` bytes (`Backend.ehFrame`,
  `FV/Backend/Obj.lean`), the personality routine and the unwinder.
* The Arm side models a call as one hooked step (`Backend.Proof.ArmStepX`: `bl`/`blr` run
  `H.call`), and the callee contracts (`CalleeOk.pc`, `CalleeOkG.pc`) require the hook to return
  to `pc + 4`. `ExtSem.call` and `csem`'s `tryCall` produce only the normal-return successor
  (`.goto ti.handlers.length`); `LowerSim.term_step_try` follows only that edge;
  `E2E.ArmRefines` has no exceptional outcome.

## Target

Every function `cargo fv` reports as `verified (normal returns; unwinding trusted)` becomes
`verified`: a theorem covers both edges of each `try_call`, and a function the unwinder passes
through (a call without a landing pad that unwinds) restores its caller's frame as the ABI
requires. What stays trusted, by design and like std: the Itanium personality routine and the
DWARF unwinder of libgcc/libunwind, stated as an outside-code contract that reads the emitted
tables (S10d). Nothing else about unwinding is trusted.

## Design

### 1. CLIF exceptional semantics (S10b)

Cranelift's `try_call` (`cranelift/codegen/meta/src/shared/instructions.rs`): "On exceptional
return, look up the thrown exception tag in the provided exception table; if the tag matches
one of the targets, branch to the matching target with the exception payload values available
as `exnN` block arguments. If no tag matches, then propagate the exception up the stack. It is
the Cranelift embedder's responsibility to define the meaning of tags."

Additive, in a new module `FV/Clif/Unwind.lean` (no change to `Clif.run`, its `Outcome`, `Env`
or any existing statement):

* `Clif.Exn`: an exception in flight: `catches : Nat → Bool` (the embedder's tag matching: does
  a handler with tag `n` catch it; `default` handlers catch every exception) and
  `payload : List Val` (the `exnN` values: on aarch64 SystemV x0, x1).
* `Clif.XOutcome`: `returned vals mem | unwound (e : Exn) (mem : Mem) | trapped | stuck |
  outOfFuel`; `unwound` = the run's bottom frame was left by an exception (its stack slots
  freed, as on a return).
* `Clif.XEnv`: externs `String → Option (List Val → Mem → XOutcome)` (plus `names`, `sigOf` as
  `Env`); `XEnv.toEnv` maps `unwound` to `stuck` (the old semantics: no unwinding).
* `Clif.XState`: `State` plus the pending exception tables of the suspended callers
  (`tries : List (Option ExnTable)`, aligned with `callers`: `some et` for a caller suspended at
  a `try_call` of a program function), so that whole-program runs propagate through program
  frames (needed by the linking theorems, S10f).
* `Clif.stepX`: if the current statement/terminator calls an extern (direct, indirect,
  `return_call`, `try_call[_indirect]`) whose semantics `unwound e m`, the exception is raised
  at that point: at a `try_call` whose table has a handler catching `e` (first `tag n` with
  `e.catches n`, or `default`; `context` items skipped), the payload is bound to fresh values
  `freshValue + i` and the frame continues with the pending `jump` to the handler (`exnN ↦
  freshValue + N`; two steps, the normal edge's shape); otherwise the frame is left (slots
  freed, `Mem.leave`) and the exception propagates into the caller (its pending table, if any,
  is consulted the same way), or the run ends `unwound e mem`. Every other step is `step
  env.toEnv` (callers pushed/popped with `tries`).
* `Clif.runLoopX`, `runWithX`, `runX`.
* Theorems: the old semantics is the restriction to non-unwinding runs —
  `runLoopX_of_returned`/`_of_trapped` (a `returned`/`trapped` run of `runLoop env.toEnv` is
  the same outcome of `runLoopX env`), `runLoopX_noUnwind` (an environment whose externs never
  unwind: `runLoopX` = `runLoop` lifted). Non-vacuity: a concrete program whose `runLoopX`
  catches at a `tag` handler, propagates through a plain call into a catching caller, and ends
  `unwound` (by `decide`/`rfl`).
* **Oracle** (the semantics is a specification, `docs/ARCHITECTURE.md`): the Cranelift
  interpreter has no exceptions (`interpreter/src/step.rs`: `TryCall => unimplemented!`), so the
  oracle is native: Cranelift's own filetest runner (`clif-util test`, `cranelift-filetests`
  `function_runner.rs`) runs `test run` files whose throws go through `__cranelift_throw` (tag +
  two payload words; Cranelift's exception tables, `wasmtime_unwinder`), on the x86_64 host.
  New fixtures `FVTest/Clif/fixtures/unwind/*.clif` (catch by tag, `default`, no match ⇒
  propagate through plain calls and non-matching `try_call`s into a catching caller, payload
  arithmetic, stack slots of exited frames, nested `try_call`s), run natively (expectations
  checked by `clif-util test`) and by `clif-filetest --unwind` (the Lean `runX`, the thrower
  modelled as the extern `Exn { catches := (· == tag), payload := [p1, p2] }`);
  `scripts/clif-unwind-native.sh` reports both, 0 disagreements required.

### 2. The outside contract: personality + unwinder (S10d)

Trusted by design, as std is: a Lean model, **generic over the tables it reads** (not over our
compiler), of what the Itanium C++ ABI (§1.6 "Exception Handling", two-phase
`_Unwind_RaiseException`) and libgcc/libunwind's DWARF unwinder do to one frame during phase 2:

* `Unw.Cfa`, `Unw.RegRule`, `Unw.Row`: the CFA rule and register rules of a DWARF CFI row;
  `Unw.decodeCfi : ByteArray → Option (List (Nat × Cfi))` and `Unw.rowAt (cie fde) (pc)`:
  DWARF 5 §6.4 (the CIE's initial instructions, then the FDE's advanced to `pc`), for the subset
  of CFA instructions the backend emits (`def_cfa`, `def_cfa_offset`, `def_cfa_register`,
  `offset[_extended[_sf]]`, `advance_loc*`, `nop`); any other opcode ⇒ `none` (the model is
  undefined there, not wrong).
* `Unw.restore (row) (s : ArmState) : Option ArmState`: CFA := rule(s); every register with an
  `offset(n)` rule := `mem[CFA + n]`; `sp := CFA`; `pc := x30` restored (return-address column
  30); other registers unchanged (libgcc's "same value" default for callee-saved registers,
  undefined for caller-saved ones: the contract havocs x0–x18).
* `Unw.Lsda`, `Unw.decodeLsda : ByteArray → Option Lsda` (header `0xff` lpStart, `udata4`
  type table, `uleb128` call-site table, action table), `Unw.lookup (lsda) (pcOff) : Option
  (Nat × Nat)` (the first call-site entry with `start ≤ pcOff < start + len`; landing pad,
  action).
* `Personality`: `decide : Lsda-entry → (exception object) → Option (pad, x1)` — install the
  landing pad (Rust's `rust_eh_personality`: any non-zero action or cleanup with `pad ≠ 0`
  installs it, `x0 := exception object`, `x1 := 0`), or continue unwinding.
* The machine with unwinding `ArmStepU X H U fa`: `ArmStepX`, except that a call whose hook
  raises (`U.raise d s = some (obj, t)`: the callee and the frames below it were unwound, `t` is
  the state at our call site as the unwinder restored it — sp, x19–x29, d8–d15 as at the call
  by the callee's own CFI, caller-saved registers arbitrary, memory the world's) continues at
  the landing pad `fnStart + pad` with `x0 := obj, x1 := sel` when the personality installs
  one for `lookup lsda (pc + 4 - 1 - fnStart)`, and otherwise at `Unw.restore (rowAt eh (pc +
  4 - 1)) t` (our frame unwound; control at our caller's return address with the in-flight
  object kept in x0, a model convention: x0 is caller-saved, the unwinder carries the object
  in its context).
* Contract on `U` (`CalleeUnwOk`, the analogue of `CalleeOk`): from an aligned, error-free
  state at a call site, a raising callee keeps sp, the callee-saved registers, the frame outside
  its dead stack and the program; its world is `X.raise`'s (a new `ExtSem` field: the
  extern's exceptional result `(obj, world)`); `X.raise` agrees with the CLIF extern's
  `unwound e mem` through the memory relation and `ExnRel e obj` (`e.payload = [obj, sel]`
  with the personality's `sel`; `e.catches` = the personality's decision for cg_clif's tags 0
  = cleanup and 1 = catch-all).

### 3. What is proven about the emitted code (S10c, S10e)

**Tables by construction (S10c, `FV/Backend/Proof/UnwindTables.lean`).** Decidable relations
between the allocated function, its final code and the tables, proven for every output of the
emitters (no per-program certificate):

* `CallSitesOk af fa sites`: `callSites af fa = .ok (some sites)` lists, in code order, one
  entry `[ret - 1, ret)` per `bl`/`blr` of `fa` (`ret` = the call's byte offset + 4); for a
  `tryCall info ti` whose handler `tag 0 l`/`tag 1 l` is the first, `pad` = byte offset of label
  `block l` in `fa` and `action` = tag; for a plain call `pad = 0, action = 0`. Theorem
  `callSites_ok`.
* `decodeLsda (lsdaBytes sites) = some ⟨sites, …⟩` and `Unw.lookup` on it at `ret - 1` of the
  `k`-th call returns that call's entry (`lsdaBytes_decode`, `lookup_callSites`; requires the
  call sites' disjointness, which holds since offsets strictly increase).
* `FrameRowsOk af fa rows`: for every code offset `o` after the prologue and the callee-save
  stores (every call is there: `ctlCheck` puts the saves first in block 0), `rowAt rows o` is
  `CFA = x29 + 16`, `x29 ↦ CFA - 16`, `x30 ↦ CFA - 8`, and `r ↦ CFA + o_r - 16 - frameSize` for
  each callee-saved `r` saved at `[sp, #o_r]`; `decodeCfi (cfiProgram rows) = some rows`
  (`cfiProgram_decode`) and the `.eh_frame` FDE of `fa` decodes to these rows with `pc_begin` =
  the function's start (`ehFrame_decode`).
* `restore_frame`: from any Arm state `t` with the frame invariant `FrameAt af s0 t` (x29 = entry
  sp − 16, `mem[x29] = ` entry x29, `mem[x29 + 8] = ` entry x30 (= the return address),
  `mem[CFA + o] = ` entry value of each saved callee-saved register), `Unw.restore (rowAt rows
  o) t` has sp = entry sp, pc = return address, callee-saved registers = entry values: the ABI
  return condition `ArmRet`'s register part. The frame invariant holds at every call site of a
  run of the compiled code (S10e: from `StRel`'s `fplr` and the spill invariant's
  `inState_save`, plus x29 never written by allocated code — x29 is not allocatable).

**The exceptional edge in the per-function theorem (S10e).** Additive variants, normal-return
theorems unchanged:

* `ExtSem.raise`; `csemU`: `csem` plus, for a `tryCall info ti`, the outcome `.goto j` of the
  first handler `j` that catches (payload defs = the payload), and for a plain call a new
  control outcome `.unwind` (frame exit); `HavocOuts` keeps the payload defs on handler edges
  (already the case: only the normal edge havocs them, `havocFrom`).
* `LowerTryOk`'s handler clause: the edge block of handler `j` is the landing pad, its code
  copies the `exnN` arguments from the payload registers and jumps to the handler successor
  (the lowering already builds it: `lowerFunction`'s `et.dests.zipIdx`; proof as the normal
  edge's `succOk`).
* `term_step_try_exn` (LowerSim): the CLIF `try_call` caught by handler `j` (two steps) is
  simulated by the VCode `tryCall` with outcome `.goto j`, the landing-pad edge block and its
  `jump`; `stmt_step_unwind`: a plain call that unwinds ends the CLIF frame `unwound` and the
  VCode run `.unwind`.
* M6/Arm: at a raising call, `ArmStepU` reaches the landing pad (LSDA, S10c) with x0/x1 =
  payload, sp/callee-saved as at the call (`CalleeUnwOk`), so `StRel` holds at the edge block's
  entry with the payload registers holding their defs (the in-state of a `try_call` successor);
  at a propagating call, `restore_frame` gives the frame exit.
* `E2E.ArmRefinesU` = `ArmRefines` plus `| .unwound e cm => ∃ n, UnwRet ra s (runX astep n s)
  ∧ ExnRel e (xreg 0 (runX astep n s)) ∧ MemAgree cm (runX astep n s)` (`UnwRet`: pc = ra, sp
  = entry sp, callee-saved = entry values); **`E2E.backend_correct_final_unwind`**: the
  premises of `backend_correct_final` plus `CalleeUnwOk` and `XRaiseOk` (the externs'
  exceptional results), conclusion `ArmRefinesU … (ArmStepU X H U fa) s (Clif.runLoopX env p
  fuel cs)`. `backend_correct_final` stays as is (it is the `runLoopX_of_returned`/`_trapped`
  specialisation).

### 4. Linking and executables (S10f)

`Clif.runLoopX_link` (whole-program `runLoopX` with program callees = per-function runs under
`linkEnvX`, the exception propagating through suspended program frames by their `tries`),
`backend_correct_linked_unwind`, `backend_correct_program_unwind`,
`Link.compileExe_correct_unwind*` (the Lean linker, `FV/Link`, writes no `.eh_frame` today:
the binary-level theorem's configuration is `--panic-abort`; S10f makes it place the objects'
`.eh_frame`/`.gcc_except_table` with an `.eh_frame_hdr`, and the theorem reads the placed bytes
through `Unw.decode*`), `Front.bundle_correct_raw_unwind`. Then the `lean-backend` line becomes
`compiled, verified` for `try_call` functions, `cargo fv` drops `NORMAL_RETURNS`, and USAGE's
counts move from "normal returns" to verified.

## Sub-issues

| | Slice | Files (new unless noted) | Shared files touched |
| --- | --- | --- | --- |
| S10a | this plan | `docs/plans/unwinding.md` | — |
| S10b (#229) | CLIF exceptional semantics + native oracle | `FV/Clif/Unwind.lean`, `FVTest/Clif/Unwind*.lean`, `FVTest/Clif/fixtures/unwind/`, `scripts/clif-unwind-native.sh` | `FV.lean`/`lakefile` imports only |
| S10c (#230) | unwind tables correct by construction | `FV/Backend/Proof/UnwindTables.lean`, `FV/Unw/*.lean` (decoders) | none (reads `FV/Backend/Unwind.lean`, `Obj.lean`) |
| S10d (#231) | personality/unwinder contract, `ArmStepU`, `restore_frame` | `FV/Unw/Model.lean`, `FV/E2E/RegLevelUnwind.lean` | none |
| S10e (#232) | per-function exceptional edge | `FV/Backend/Proof/*Unw*.lean`, `FV/E2E/FinalUnwind.lean` | `RegallocCSem.lean` (`ExtSem.raise`: coordinate), `IselContract.lean` |
| S10f (#233) | linking, executables, report | `FV/E2E/LinkUnwind.lean`, `FV/Link/ExeUnwind.lean`, `FVTest/Backend/Main.lean`, `rust/crates/cargo-fv/src/report.rs` | `FV/E2E/Statement.lean`, `FV/Link/*`, cargo-fv (coordinate) |

Order: S10b and S10c are independent; S10d needs S10c's decoders; S10e needs S10b–S10d; S10f
needs S10e. Each PR keeps every existing theorem statement; new top-level theorems get
concrete non-vacuity witnesses; axioms stay `[propext, Classical.choice, Quot.sound]`.

## Risks

* `ExtSem` is a structure used throughout M6; adding `raise` with a default keeps existing
  terms well-typed but changes the `ExtSem` mk arity seen by anonymous constructors (check
  `⟨…⟩` uses; else a separate `ExtSemU := ExtSem × raise`).
* The frame invariant at call sites needs x29 fixed across the body; the allocated code never
  names x29 (not in the allocatable set), but the TLSDESC hook and the call hooks must keep it
  (they do: x29 is callee-saved in `CalleeOk`/`TlsOk`).
* cg_clif may emit a `try_call` with both a cleanup and a catch handler; `callSites` then emits
  two entries for the same range and the personality takes the first (cleanup), which matches
  `Clif.stepX`'s "first catching handler" only if `catches 0` holds for every exception — true
  for Rust's personality (cleanups run for every exception). Stated in `ExnRel`.
* Foreign exceptions and `_Unwind_ForcedUnwind` (thread cancellation) are outside: the model's
  personality is Rust's for Rust panics.
