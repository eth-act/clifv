# S10 (#34): unwinding under the theorems

Plan of 2026-10-16, base main f29d0c06. Branch prefix `agent/unwinding`. Sub-issues of #34:
S10b #229, S10c #230, S10d #231, S10e #232, S10f #233 (one PR each, merged in order; later
slices build on earlier ones; S10a is this plan).

## Status

| Slice | State |
| --- | --- |
| S10a | merged (this plan) |
| S10b | done: `FV/Clif/Unwind.lean` (`Clif.runX`; `runLoopX_of_returned`, `runLoopX_of_trapped`, `runLoopX_toX`; witnesses `Clif.UnwindWitness.caught`/`uncaught`/`old_stuck`), native oracle `scripts/clif-unwind-native.sh` (`rust/crates/clif-throw-native`): 17/17 runs, agree 17, disagree 0 (`docs/contracts/clif.md`) |
| S10c | done: emitters total/structural (`uleb`/`sleb` well-founded, `cfiProgramFrom`, `saveRows`, `scanLines`/`handlerEntry`/`siteEntries`; objects byte-identical on 753 fv-demo/deps `try_call` files), `FV/Unw/Dwarf.lean` (decoder model), `FV/Backend/Proof/UnwindTables.lean`: `uleb?_uleb`, `sleb?_sleb`, `decodeCfa?_cfiProgram`, `decodeLsda?_lsdaBytes`, `callSites_ok` (decidable `CallSitesOk`), `unwindRows_frame` (the row at every call's return offset − 1 is `frameRow frameSize saved`; the rows now define the CFA from sp after the prologue, `frameRows`, so no x29 invariant is needed), `unwindRows_leaf`; witness `Witness.call_row`. The `.eh_frame` section as a whole (CIE/FDE framing, `pc_begin`) is read in S10f, where the linker places it |
| S10d | done: `FV/Unw/Model.lean` (the outside contract: `restore`, `personality` (Rust's, cleanup phase), `FnTables`, `unwindAt`, `UnwHooks`, the machine `ArmStepU`; `armStepU_none` (no raising callee: `ArmStepX`), `armStepU_raise`, `armStepU_noRaise`, `unwindAt_install`, `unwindAt_continue`, `restore_spec`, `FrameAt`, **`restore_frame`** (a frame satisfying the invariant unwinds to `ArmRet`), the register part of the raising callees' contract `CalleeUnwRegs`); `FV/E2E/RegLevelUnwind.lean` (`frameAt_frameRow`, **`unwind_call_restores`** (S10c's emitted rows at every call restore the ABI return from a frame with `FrameSaved`), `personality_callSite`/`personality_plain` (S10c's emitted LSDA); witness `Unw.Witness.restores`). The world part of `CalleeUnwOk` comes with `ExtSem.raise` (S10e) |
| S10e | done: the per-function theorem with the exceptional edge. CLIF→VCode: `FV/Backend/Proof/LowerSimURaise.lean` (`stmt_raise`, `try_raise`: M4's proven rules run on a proof-only probe semantics), `LowerSimUCheck.lean` (validator `unwCheck`/`lowerCheckU`, soundness `loweringU_of_check`), `LowerSimU.lean` (`stmt_step_raise`, `term_step_try_exn`, `sim_runX`, `driver_correctU`, generic in the semantics), `FV/E2E/IselSimU.lean` (`iselSimU_of_driver`). VCode→Arm: `FV/E2E/RegLevelU.lean` (`csemVU`, `GoodXU`, `realizes_allU`), `RegLevelUTry.lean` (`realizes_tryCall_raiseU`: the personality installs the landing pad of the emitted LSDA, `siteAt_of_check`, `padsNonzeroB`), `RegLevelCallSite.lean` (`q_callSite(_last)`, `lastCallsOk`), `RegLevelFrameSaved.lean` (`savedCheck`, `frameSaved_of_q`), `RegLevelCorrectU.lean` (`regLevelCorrect_coreU`, `regLevelCorrect_backend(_ex)U`: a propagating call unwinds the frame to `ArmRet` with the object in x0). Statements/composition: `FV/E2E/UnwindSem.lean` (`csemU`, `tryUOk`), `UnwindStatement.lean` (`ArmRefinesU`, `backend_correct_of_layersU`), `UnwindPrepare.lean`. Final: **`E2E.backend_correct_final_unwind{,_ex}`** (`FV/E2E/FinalUnwind.lean`) and, for the shipped dead-cleanup pipeline, **`E2E.backend_correct_final_cleanup_unwind{,_ex}`** (`FV/E2E/DeadCleanupUnwind*.lean`, `UnwindValueSem.lean`); `backend_correct_final_of_unwind` (the old shape for callees that do not raise). The tables the unwinder reads are premises (`T.cie = cieInsns`, `T.fde = insnsFrom 0 rows`, `T.lsda` = the emitted call sites), the checks `unwCheck`, `savedCheck`, `lastCallsOk`, `padsNonzeroB` run in `lean-backend`, which labels a passing `try_call` function `compiled, verified`: fv-demo 254 → 0 and survey 498 → 5 normal-returns-only (the 5: i128-legalised functions, no unwinding theorem composes the legalisation) |
| S10f | done except the items under "Left". Linking: `FV/Clif/LinkClifX.lean`, `LinkClifXN.lean` (`Clif.runLoopX_link`, `runLoopX_linkR/N/D`: the whole-program run with unwinding is the per-function run under `linkEnvX`/`linkEnvRX`/`linkEnvNX`/`linkEnvDX`, the exception propagating through program frames; witnesses `UnwindLinkWitness.link_caught`, `linkN_caught`, `linkD_caught`), `E2E.backend_correct_linked_unwind` (`FV/E2E/LinkUnwind.lean`), the per-function world theorems with unwinding `backend_correct_world_pipelineU`/`_cleanupU`/`backend_correct_worldU` (`FV/E2E/WorldUnwind*.lean`; `ActUnw`, `UnwExit`, `PostTrace`) and with non-interference `backend_correct_world_ni_pipelineU` (`FV/E2E/WorldUnwindNI.lean`: the driver generic in the world type `sim_runXW`, raising calls on world pairs `PairRaise.lean`, the pair driver `vcode_niU`; witness `WorldUnwindNIWitness.world_ni_applies`); the Arm-level linked program `LinkSysU` (`FV/E2E/LinkArmU*.lean`: `thmU`/`thmUN`, **`E2E.backend_correct_program_budgetU'`/`peakU'`** (and `budgetU`/`peakU` with `¬ NeedNI`); witnesses `LinkArmUProgWitness.budgetU_applies` (a raise through a program frame), `LinkArmUProgNIWitness.budgetU'_applies` (a program with `NeedNI`)). Executables: the `.eh_frame`/`.gcc_except_table` decoding model `Unw.tablesAt` (`FV/Unw/EhFrame.lean`) with `Backend.Proof.EhFrameDecode.tablesAt_ehFrame` and `E2E.backend_correct_final_cleanup_unwind_eh`; libunwind's lookup `FV/Unw/EhFrameHdr.lean` (trusted) and the decidable check of the linked file `Link.EhCheck.ehOkR` (`ehOkR_sound`) with the per-function checks `unwFnsB`; `Link.DeadCleanup.compileExeU`, **`Link.DeadCleanup.compileExe_correct_unwind`/`_peak`** (`FV/Link/ExeUnwind.lean`), lean-link's `coverage:` line names them when `unwOkB` holds; **`Front.bundle_correct_raw_unwind`**, `bundle_correct_raw_unwind_ren` (i128-free, `Clif.runLoopX_ren`); witnesses `Link.EhCheck.Witness.unw_call`, `Link.DeadCleanup.UnwindWitness.unwind_applies`, crate-proofs `Crates.FrontendBundleUnwindWitness`. `i128` legalisation with unwinding: `E2E.backend_correct_legal_unwind` (`FV/E2E/LegalUnwind.lean`, from `Opt.Legal.X.check_refinesX` + the handler-edge check `Opt.Legal.exnOk`; witnesses `Clif.Rust.LegalXWitness.refines`, `E2E.LegalUnwindWitness.legal_unwind_applies`), lean-backend labels such functions verified: survey `verified (normal returns; unwinding trusted)` 5 → 0; program-level legalisation with unwinding `E2E.LegalProgram.legalProg_refinesX` (`check_refinesX2`, `Clif.unlinkX_run`) and the raw program's exceptional edges for `i128` programs, **`Front.bundle_correct_raw_unwind_src`** (`FV/Front/RawExeUnwindSrc.lean`). The mid-end with unwinding: `Opt.runLoopX_refinesU` (`FV/Opt/Proof/SemSimU.lean`: `HCont`, `TryOkU`, `FunSimU`, states related by `SRU` with the callers' pending tables), the stages `removeUnreachable_simU`/`simpOk_simU`/`editOk_simU`, `Opt.optimizeExe_simU`/`optimizeProgramExe_refinesU` (`PipelineU.lean`), `E2E.optExe_entryX`, **`E2E.backend_correct_opt_exe_cleanup_unwind`**/`backend_correct_opt_exe_unwind` (`FV/E2E/OptUnwind.lean`), `E2E.backend_correct_legal_opt_unwind` (`FV/E2E/LegalOptUnwind.lean`); witnesses `OptUnwindWitness.refines`, `opt_unwind_applies(_legacy)`, `LegalOptUnwindWitness.legal_opt_unwind_applies`; with `--opt-proven-only` normal-returns-only fv-demo 246 → 0, survey 456 → 0. Left: the `--opt` executable (`compileExeOpt`) with unwinding, an executable-bytes machine with unwinding, the witnesses' entry-state premises |

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
  `CFA = sp + frameSize + 16` (the rows switch to sp after the prologue: the body keeps sp), `x29 ↦ CFA - 16`, `x30 ↦ CFA - 8`, and `r ↦ CFA + o_r - 16 - frameSize` for
  each callee-saved `r` saved at `[sp, #o_r]`; `decodeCfi (cfiProgram rows) = some rows`
  (`cfiProgram_decode`) and the `.eh_frame` FDE of `fa` decodes to these rows with `pc_begin` =
  the function's start (`ehFrame_decode`).
* `restore_frame`: from any Arm state `t` with the frame invariant `FrameAt row s0 t` (CFA =
  the body sp + frameSize + 16 = entry sp, `mem[CFA − 16] = ` entry x29, `mem[CFA − 8] = `
  entry x30 (= the return address), `mem[CFA + o] = ` entry value of each saved callee-saved
  register), `Unw.restore (rowAt rows o) t` has sp = entry sp, pc = return address,
  callee-saved registers = entry values: the ABI return condition `ArmRet`'s register part.
  The frame invariant holds at every call site of a run of the compiled code (S10e: from
  `StRel`'s `sp` and `fplr` and the spill invariant's `inState_save`; no x29 invariant).

**The exceptional edge in the per-function theorem (S10e).** Additive variants, normal-return
theorems unchanged:

* `ExtSem.raise`; `csemU`: `csem` plus, for a `tryCall info ti`, the outcome `.goto j` of the
  first handler `j` that catches (payload defs = the payload), and for a plain call a new
  control outcome `.unwind` (frame exit); the handler edges must forget the non-payload defs
  (today they keep every def, see the findings below).
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

**Findings for S10e (from the S10c/S10d work; precise starting points).**

* The proof chain to extend (normal edge today): `Clif.stepTryCall` (`FV/Clif/Run.lean`) →
  `LowerTryOk.run` (`FV/Backend/Proof/IselContract.lean`, pinned `LowerTryOkP` in
  `IselContractP.lean`, proofs `IselCtlTry.lean`/`IselCtlTryInd.lean`) → `term_step_try`,
  `sim_run`, `driver_correct` (`LowerSim.lean`) → `IselSim` (`E2E/Main.lean`
  `iselSim_of_driver`) → `PrepareCorrect` → `checkAlloc_sound` (`RegallocSound.lean`, generic
  in the `ISem`: its `goto` case takes any successor `j`) → `realizes_tryCall`
  (`E2E/RegLevelTry.lean`, forces `j = ti.handlers.length` from `csem`) / `realizes_all`
  (`RegLevelCorrect.lean`) → `RegLevelCorrect` → `backend_correct_final`.
* Handler edges keep **every** def of the `tryCall` (`havocFrom … (.goto j) = none` for
  `j < handlers.length`; the checker's `CheckCtx.edgeForget` forgets defs only on the normal
  edge). After unwinding, the machine's caller-saved registers other than x0/x1 are
  arbitrary, so `csemU` cannot give the return-only defs (x2…) values the machine agrees with.
  Needed: forget the non-payload defs on handler edges too (an additive `havocFromU` and the
  checker's `edgeForget` extended to handler successors — a compiler change: rerun the
  lean-backend gates; the lowering never reads those vregs on a handler edge, `tryRegsOf`).
* `Ctl` (`VCodeSem.lean`) has no frame-exit outcome; a propagating call (plain `call`, or a
  `tryCall` without a catching handler) needs one (`.unwind`, with `VUnwinds`/`MUnwinds`
  observables next to `VReturns`/`VTraps`). Adding a constructor touches every match on `Ctl`
  (~100 files mention it); alternatively an `ISemU` with its own control type and a lifting
  of the generic simulations.
* The frame invariant at calls (`FrameSaved`, `FV/E2E/RegLevelUnwind.lean`) from M6's state
  relation: `StRel.fplr` gives the entry x29/x30 (a 16-byte read, split into the two 8-byte
  reads `frameAt_frameRow` takes) and `StRel.sp` the body sp (the CFA); still needed: the
  callee-save slots holding the entry values at each call —
  the checker's abstract state has `Sym.entry r` there (`SpillCheckAlloc*.lean`), and the M5
  relation (`RegallocSound.lean` `MatchRun`: `Inv keep a ms.m vs.ρ r₀` for the abstract state
  `a` before each item) turns `Sym.entry r ∈ a.get l` into `keep r (m l) = keep r (r₀ r)`. So a
  decidable check at every call — `Sym.entry r ∈ a.get (.save r)` for `r ∈ rf.saved`,
  `Sym.entry r ∈ a.get (.reg r)` for the other callee-saved `r` — gives the frame's save slots
  (`locVal` of `.save r` = the slot at body sp + `saveOff r` = CFA + `o − 16 − frameSize`,
  S10c's `saveRow`) and unsaved registers, i.e. `FrameSaved`'s hypotheses.
  The CFA needs no x29 invariant: the rows define it from sp after the prologue
  (`frameRows`: `def_cfa_register sp`, `def_cfa_offset frameSize + 16`), and the body keeps
  sp = `spB` (`StRel.sp`); a raising callee keeps our sp (`CalleeUnwRegs`).
* LSDA ↔ layout: done in S10d (`scanLines_labelOffsets`: the landing-pad offsets are
  `labelOffsets`'; `scanLines_rets_eq`: the `k`-th return offset is the `k`-th call line's
  `lineOffset` + 4, `callIdx`). Left: the `k`-th call line is the code of `af`'s `k`-th call
  (`AFunc.calls`), from the emitter's block layout (`Q`'s `R.L.drop j = …`).
* Build cost: `FV/Backend/Unwind.lean` is imported (via `FV.Backend` → `IselData` →
  `IselCmp*`) by `FV.Opt.Proof.*`; every change to it rebuilds those (§7's scheduler).

### 4. Linking and executables (S10f)

`Clif.runLoopX_link` (whole-program `runLoopX` with program callees = per-function runs under
`linkEnvX`, the exception propagating through suspended program frames by their `tries`),
`backend_correct_linked_unwind`, the linked Arm program `backend_correct_program_budgetU'`/
`peakU'`, `Link.DeadCleanup.compileExe_correct_unwind*`, `Front.bundle_correct_raw_unwind`.
As built: the Lean linker still patches only the region's bytes; the region object cargo-fv
gives rust-lld carries lean-backend's `.eh_frame`/`.gcc_except_table`, rust-lld lays them out
and builds `.eh_frame_hdr`, and `lean-link` checks the resulting file (`unwOkB`: libunwind's
lookup, `FV/Unw/EhFrameHdr.lean`, finds for every pc of every Lean function an FDE and LSDA
decoding to the theorem's tables), so the theorem reads the placed bytes without the Lean
linker writing them. `lean-backend` labels `try_call` functions `compiled, verified` when the
per-function checks pass, and USAGE's counts moved from "normal returns" to verified.

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
* The frame invariant at call sites needs no x29 invariant (the rows define the CFA from sp
  after the prologue, `frameRows`); this deviates from Cranelift's x29-based rows, which are
  equivalent while the frame pointer is kept (checked natively by the panic=unwind tests).
* cg_clif may emit a `try_call` with both a cleanup and a catch handler; `callSites` then emits
  two entries for the same range and the personality takes the first (cleanup), which matches
  `Clif.stepX`'s "first catching handler" only if `catches 0` holds for every exception — true
  for Rust's personality (cleanups run for every exception). Stated in `ExnRel`.
* Foreign exceptions and `_Unwind_ForcedUnwind` (thread cancellation) are outside: the model's
  personality is Rust's for Rust panics.
