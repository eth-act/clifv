# Contract: per-function translation validator (`FV/Validate`, M3)

## Status

**Stopped at the owner's request: M3 is optional and the compiler goes all-Lean.** The design is
settled, and the kernel-checked library it needs builds without `sorry`. The generator is only
partly written. No function has been validated end to end, there is no `lean_exe validate`,
and `lakefile.toml` is unchanged.

### What exists (all builds: `lake build FV.Validate.Tactics FV.Validate.Gen.Explore`, no `sorry`/`axiom`)

| File | Content | Proven? |
| --- | --- | --- |
| `FV/Validate/Basic.lean` | Simulation statement: `World`, `Act`, `CSGpr`/`VSaved`/`CSaved`, `RegsHold`/`StackHold`/`ArgsAt`/`ResultsAt`, `MemRel`, `AllocsOK`/`AllocsRet`, `Pres`, `GotOK`, `Common`, `RetOK`, `TrapOK`, `StackOut`, `Matches`, `GoodF`, `CodeAt`, `TrapsAt`. Rules `Reach.*`, `GoodF.arm/stepEq/stepIte/stepPc/clif/clifDec/done/trapped/stuck/stackOut/mono/zero`, fuel induction `GoodF.induct`. | all proven |
| `FV/Validate/StepThms.lean` | `#vstep pfx addr word`: step theorem over an *abstract* linked program (`s.program = P`, `P.find? addr = some word`), adapted from LNSym `#genStepEqTheorems`. | kernel-checked per use |
| `FV/Validate/ClifDef.lean` | `#clif_def F "<clif text>"`: runs `Clif.parse` at elaboration time and adds the literals `F`, `F.b<k>`, and the lemmas `F.block_<k>`, `F.params_<k>`, `F.param_tys`, `F.ret_tys`. `ToExpr` instances for the CLIF syntax. | `rfl` lemmas |
| `FV/Validate/Rules.lean` | CLIF-side rules for the single top frame (`cst`, `noFuncs`: every call is an `Env` extern): `ResK` (+ simp lemmas, `ResK_ite`, `ofExcept_ite`), `StepGood`, `GoodF.ofStep/ofStepDec/stmt/jump/brif/brTable/ret/trapTerm`. | all proven |
| `FV/Validate/Frame.lean` | Frame lemmas (`MemRel_w`, `Pres_w`, `GotOK_w`, `VSaved_w_*`, `RegsHold_cons`, `Ty.width_*`, `as?_i*`, `MemRel_free`, `AllocsRet_free`, `retOK_of`, `trapOK_of`). | all proven |
| `FV/Validate/Attr.lean`, `Tactics.lean` | Simp sets `vsimp`, `vsem`; tactics `vside [..]` (step side conditions), `vclif [..]` (evaluate the next CLIF step), `vfact [..]` (close relation facts: simp, then `bv_decide`); lemmas `bool8_eq_cond`, `ite_true_eq_cond`, `sub_udiv_mul` (the `urem` → `udiv`+`msub` identity). | all proven |
| `FV/Validate/Gen/Sym.lean` | Untrusted value numbering: a node arena where every node carries its value in 48 random samples (biased toward edge values). Used for `agree`, `constDiff`, printing. | untrusted |
| `FV/Validate/Gen/Arm.lean` | Untrusted AArch64 decoder and symbolic stepper for the Cranelift integer subset (add/sub imm/shift/ext, adc/sbc, logical, movz/n/k, bitfield, extr, dp1/2/3, csel, ccmp, branches, udf, single and pair loads/stores, register offset). `adr/adrp` and SIMD (popcnt) are not handled. | untrusted; **not yet cross-checked against the LNSym model** |
| `FV/Validate/Gen/Explore.lean` | Untrusted co-execution (partial): the `Desc`/`CutInv`/`FnInfo`/`Path` data types, sample evaluation of CLIF statements through the real `Clif.evalInst` (`clifEval`), `execStmt`, lazy CLIF `advance` (pure statements, `jump`, determined `brif`), which emits the tactic lines, and cut-point relation inference (`describe`, `mkInv`, `intersect`). | untrusted |

A hand-written prototype (divMod, since deleted: it had `sorry` placeholders) established the
proof-script patterns below. Every step pattern was checked to elaborate: straight-line
steps, `cbz`/`b.cond` splits, `brif`, `jump`, `udiv`/`urem` with trap guards, returns
through `retOK_of`, trap sites through `trapOK_of`, and contradiction closing (`bvContra`).

### Design (settled)

- **Statement.** It is per function and modular. For a `World W` (the linked program `P ⊇`
  the function's code at a fixed `base`; global trap table; stack region `[lim, top)`; GOT
  entries; `Clif.Env` for callees) and an activation `A` (Arm entry state `a0`, CLIF entry
  memory `m0`, own slot allocations), `GoodF A noFuncs n c a` says: every CLIF run of at most
  `n` steps from `c` is matched by the Arm run from `a`, per `Matches`:
  - `returned vals m`: the Arm run reaches `RetOK`. That is: PC is the entry `x30`; x19–x29,
    SP and d8–d15 are restored; the results are in `x0..`; `MemRel m`; the allocation
    discipline holds; the callers' frames and the GOT are unchanged.
  - `trapped c`: the Arm run reaches a trap site with code `c`.
  - Either outcome may instead end in `StackOut` (SP below `lim`).
  - `stuck` and `outOfFuel` constrain nothing.
- **CLIF semantics used.** It is `Clif.runLoop` on the empty program (`noFuncs`), so every
  `call` is an `Env` extern. The top frame's stack slots are placed at the Arm frame
  addresses. CLIF leaves slot addresses unspecified, and `Clif.run`'s bump allocator is one
  choice among many. This is documented as the M2/M7 composition obligation:
  address-independence of the emitted code. For functions without slots or calls, it
  coincides with `Clif.runWith` (lemma still to write).
- **Proof shape.**
  - Cut points are the function entry and the Arm join points. Each has an invariant `I_q`:
    ∃ atoms, `c = cst F regs slots (F.b<k>.body) F.b<k>.term mem`, CLIF facts
    `regs v = some ⟨ty, x_v⟩` or a constant, `Common A mem a`, `r PC a = addr`, and register
    facts (`setWidth w (r (GPR i) a) = x_v`, entry values, `A.sp0 + c`, constants).
  - One segment theorem per cut: `I_q A c a → GoodF A noFuncs (n+1) c a`, given
    `IH : ∀ c a, Cut A c a → GoodF … n c a`. Segments are composed by `GoodF.induct`.
  - Within a segment, Arm steps use `GoodF.stepEq/stepPc/stepIte` with `#vstep` theorems and
    `hcode i (by decide)`. CLIF steps run lazily at events (memory access sync, call, return,
    trap, cut arrival, determined `brif`).
  - Inconsistent branch or trap combinations are closed by `bvContra`. Facts are closed by
    `vfact`.
- **Inference is untrusted.** It uses value numbering over random samples, and path-live
  samples decide CLIF branch directions. A wrong guess only makes a proof fail.

### Remaining steps (in order)

1. Finish `Gen/Explore.lean`:
   - `walk`: Arm step emission, splits, cut arrival (`apply IH; apply Cut.c<j>; refine ⟨…⟩;
     all_goals vfact [..]`), return (`GoodF.ret` → `Reach.stepEq` → `retOK_of`), `udf`
     (`trapOK_of`).
   - Fixpoint of cut invariants: phase 1 analyses, phase 2 emits.
2. `Gen/Emit.lean`: the per-function file.
   - Contents in order: `#clif_def`, `code`, `traps`, `#vstep`s (with an SP flag for SP-based
     memory ops; make `#vstep` take the flag explicitly), `I_q` defs, `Cut`, segment
     theorems, `good` by `GoodF.induct`.
   - Entry theorem: add `FV/Validate/Spec.lean` with `entryState`/`runF`/`EntryOK`/
     `FnContract`, then prove `EntryOK → I_entry` by `rcases` on the arguments list.
   - Stack-exhaustion case split at entry.
3. `FV/Validate/Main.lean` + `lean_exe validate` (append to `lakefile.toml`) +
   `scripts/validate.sh`: run clif2obj, parse the dumps (`Lean.Json` for relocs/traps), patch
   relocated words (bl / GOT adrp+ldr at fixed addresses), write
   `build/validate/<file>/<fn>.lean`, check it with `lake env lean`, and print
   VALID/INVALID/UNSUPPORTED with timings.
4. Memory (stage c):
   - Lemmas: `MemRel`/`Pres`/`GotOK`/spill-fact preservation for frame writes (range in
     `[lim, sp0)` outside own slots), CLIF load/store versus `read/write_mem_bytes`
     (`MemRel` + `valid`), read-over-write for disjoint SP offsets (LNSym
     `Memory.read_bytes_write_bytes_eq_read_bytes_of_mem_separate'`).
   - Stack-slot facts in the invariants.
   - Frame layout: slots at `sp_body + outgoing_args + Cranelift offset` (see `abi.rs` lines
     1252–1310).
5. Calls (stage d):
   - A call rule taking the callee's `FnContract` for `Env.extern g`.
   - GOT relocations patched to fixed GOT slots; `W.got` holds the callee address.
6. `br_table` (`adr` + `ldrsw` + `br`), `popcnt` (SIMD), `sdiv`/`srem` identities (`msub`
   after `sdiv`).
7. Negative tests (mutated `.bin` words), corpus and runtest runs, results tables.
8. Cross-check `Gen/Arm.lean` against the LNSym model on random states.
9. The PLAN.md M3 PCC item was skipped: not started.
