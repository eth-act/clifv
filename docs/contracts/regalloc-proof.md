# Register allocation: soundness proof of the checker (M6)

Modules (all under `FV/Backend/Proof/`, namespace `Backend.Proof`):

| File | Content |
| --- | --- |
| `VCodeSem.lean` | abstract semantics: `ISem`, `Ctl`, VCode (`VStep`), allocated code (`MStep`), `Clobbered`, `Star` |
| `RegallocState.lean` | lemmas on the checker's abstract state (`AState.get/put/define/meet/parCopy/le`), the invariant `Inv`, its preservation lemmas |
| `RegallocLemmas.lean` | what an accepting run of each checker function establishes (`stepOp_ok`, `runItems_*`, `edge_ok`, `verify_ok`, `checkAlloc_ok`, `checkStatic_ok`), operand-list correspondence, per-instruction soundness `op_sound` |
| `RegallocSound.lean` | simulation relation `Match`, `sim_step`, `sim_progress`, **`checkAlloc_sound`** and corollaries |
| `RegallocOperands.lean` | the operand-view obligation `OperandsSound` against the Arm model (incl. `FrameKeep`: `sp` and the frame bytes untouched), the bridge `operandsSound_step` |
| `RegallocCSem.lean` | the concrete semantics `csem F ctx X` (defined by the Arm model under a canonical allocation), `AllocOk` (what `checkStatic` gives), `Corr` and the reduction `os_of_corr` |
| `RegallocTac.lean` | `csimp_rules` (unfolding set of emitted-code runs), `sw_tac`, `veq_tac`, `corr_tac` |
| `RegallocInstsInt.lean`, `RegallocInstsZR.lean` | `Corr` for every integer and zero-register straight-line form |
| `RegallocOS.lean` | `OperandsSound` for those forms (`os_*`) |
| `RegallocFrame.lean` | frame/move lowering: `locVal`, `FrameOk`, int register move, int spill, int reload |

The checker itself is `FV/Backend/RegallocCheck.lean` (see `regalloc.md`).

## Status (2026-09-27)

- [x] abstract semantics of VCode and allocated code, parametric in the instruction semantics
- [x] `checkAlloc_sound`, sorry-free, for **every** instruction semantics `sem` and every
      callee-preserved-part function `keep` (no hypothesis on `sem` is needed at this level)
- [x] corollaries: returns, halts (traps), stuck states, divergence
- [x] `csem` redefined (2026-09-28): a straight-line instruction means the Arm model's run of its
      `MInst.lines` under the canonical allocation (operand k → `x k`/`v k`, fixed → its
      register, reuse → the reused operand's), uses placed in the world, defs read back; `none`
      if a memory access touches `F` (`AccessOk`) or the run sets the model's `ERR`. Branches
      (`goto j`), traps (`halt`), `Rets`, `Args` (reads the argument registers of the world),
      calls and symbol addresses (`ExtSem`) have explicit clauses. No per-instruction formula is
      hand-written.
- [x] `OperandsSound (execMInst ctx env) (csem F ctx X)` proven, all ops × both widths × all
      immediates, for: `aluRRR`, `aluRRRR`, `aluRRImm12`, `aluRRImmLogic`, `aluRRImmShift`,
      `aluRRRShift`, `aluRRRExtend`, `bitRR`, `mov`, `movWide`, `movK` (reuse constraint),
      `extend`, `bitfieldMove`, `cset`, `csel`, `ccmp`, `ccmpImm`; zero-register forms
      (`rn = xzr`: neg/mvn; `rd = xzr`: cmp/cmn/tst incl. imm12/logic/shifted/extended;
      `ra = xzr`: mul). Forms the Arm model does not implement
      (umaddl/smaddl: `Unimplemented`) have `csem = none`, so they are vacuous.
- [ ] `OperandsSound` still open: float/vector `movToFpu`, `movFromVec`, `vecMisc cnt`,
      `vecLanes`, `vecRRR addp` (the `Corr` proofs pass under `lake env lean` but not under
      `lake build` — `split at hex` renames hypotheses there; not committed), loads/stores (all amodes; the address lemmas relating the
      model's address arithmetic to `AMode.addr` are the missing piece), `loadAddr`, calls of any
      arity and `blr` (the one-argument proof was removed with the old `csem`; the general one is
      an induction over `info.uses`/`info.defs` under `CalleeSound`), `loadExtNameGot/Near`
      (linker hook), branches/traps/`jtSequence` (control; see "Remaining")
- [x] frame/move lowering proven for int register moves, int spills and int reloads
      (unsigned-offset encoding)
- [ ] remaining obligations: listed under "Proven vs assumed" below
- checker behaviour unchanged: `lake exe lean-backend-regalloc-test` accepts 932/932
  (`aarch64Env` and `--small`), every mutant rejected (swap 2681/2681, drop-reload 10/10,
  drop-restore 253/253, call-clobber 166/166; `--small`: 2655, 173, 158, 88, all rejected)

## Checker changes made for the proof (behaviour-preserving)

- `runBlock` is a structural recursion (`runItems`) instead of a `for` loop; the checks are
  `ensure b msg` / `List.forM` (no `do` join points); the transfer of an instruction is the pure
  `transferOp` (early defs, clobbers, late defs), its return check `retCheck`.
- **Certificate check.** The fixpoint iteration (`fixpoint`, `round`) is now untrusted: it only
  proposes in-states. `CheckCtx.verify` checks them — the entry block's in-state is included in
  `entryState`, and every block (`verifyBlock`) is reached, its items check from its in-state,
  and each successor's in-state is included (`AState.le`) in the state the edge produces. The
  proof uses only `verify`. It accepts whenever the old last round (no change) did.
- `edge` rejects block parameters that are not pairwise distinct (the parallel copy would be
  ambiguous; VCode from `Isel` never has duplicates).
- `Loc`, `Sym`, `RItem`, `OpKind`, `OpPos`, `Constraint`, `Operand` use the `BEq` of their
  `DecidableEq` (lawful) instead of a derived one.

## Abstract semantics (`VCodeSem.lean`)

Parameters: values `V`, world `W`, `sem : ISem V W := MInst → List V → W → Option (List V × W × Ctl)`
(use values in operand order ↦ def values in operand order, new world, control `next | goto j |
ret | halt`). Observables — memory effects, calls with their arguments, traps, branch decisions
— are whatever `sem` records in `W`; both semantics thread `W` through the same `sem`.

- **VCode** `VStep vc sem`: state `⟨b, k, ρ, w⟩` (block, instruction index, vreg file
  `ρ : Nat → V`, world). Instruction `k` reads `ρ` at its use operands, writes its def
  operands (early defs, then late defs, operand order); `goto j` is allowed only at the last
  instruction and performs the block's branch arguments as a parallel copy into the parameters
  of successor `j` (`edgeEnv`); `ret` only for `Rets` (returns the use values); `halt` anywhere.
- **Allocated code** `MStep vc sem keep rf`: state `⟨b, items, m, w⟩` with location store
  `m : Loc → V` (registers, spill slots, callee-save slots). `move src dst` is
  `m[dst ↦ m src]`; `op k allocs` reads its uses from `allocs`, writes early defs, havocs its
  clobbers (`Clobbered keep`: any value, a callee-saved register keeps its `keep`-part), writes
  late defs; the defs past `havocFrom i ctl` take any value (`HavocOuts`: a branch's defs, the
  LL/SC loops' scratch registers, a `try_call`'s exception payload defs when it returns normally).
  No copy on edges (the allocator's moves do it). A return yields the use values and the final
  store.

## Theorem (`RegallocSound.lean`)

```lean
structure IsSimulation (R : MConf V W → VConf V W → Prop) : Prop where
  step : R c v → MStep vc sem keep rf c c' →
    (R c' v ∧ c'.measure < c.measure) ∨ ∃ v', VStep vc sem v v' ∧ R c' v'
  progress : R c v → VStep vc sem v v' → ∃ c', MStep vc sem keep rf c c'
  ret : R (.ret vals m w) v → v = .ret vals w
  halt : R (.halt w) v → v = .halt w
  run : R (.run s) v → ∃ s', v = .run s'

theorem checkAlloc_sound (h : checkAlloc vc rf = .ok ()) (m₀ : Loc → V) (ρ₀ : Nat → V) (w₀ : W) :
    ∃ R, IsSimulation vc rf sem keep R ∧ R (MConf.init rf m₀ w₀) (VConf.init ρ₀ w₀) ∧
      ∀ {vals m w v}, R (.ret vals m w) v →
        ∀ r ∈ calleeSaved, keep r (m (.reg r)) = keep r (m₀ (.reg r))

theorem checkAlloc_ret (h) (ρ₀) (hs : Star (MStep vc sem keep rf) (MConf.init rf m₀ w₀) (.ret vals m w)) :
    Star (VStep vc sem) (VConf.init ρ₀ w₀) (.ret vals w) ∧
      ∀ r ∈ calleeSaved, keep r (m (.reg r)) = keep r (m₀ (.reg r))
theorem checkAlloc_halt (h) (ρ₀) (hs : Star MStep init (.halt w)) : Star VStep vinit (.halt w)
theorem checkAlloc_stuck (h) (ρ₀) (hs : Star MStep init (.run s)) (hstuck : ∀ c', ¬ MStep (.run s) c') :
    ∃ vs, Star VStep vinit (.run vs) ∧ ∀ v', ¬ VStep (.run vs) v'
theorem checkAlloc_diverges (h) (ρ₀) (f : Nat → MConf V W) (h0 : f 0 = MConf.init rf m₀ w₀)
    (hf : ∀ n, MStep (f n) (f (n + 1))) : ∀ N, ∃ v, StepsN (VStep vc sem) N (VConf.init ρ₀ w₀) v
```

The entry register file is `r₀ r := m₀ (.reg r)`. Refinements of the intended statement in
`regalloc.md`: (1) the theorem is between two abstract semantics sharing `sem`, so it holds for
every `sem`; the connection to the Arm model is the separate obligation `OperandsSound`; (2)
"same observables" is "same world", plus equal returned values; (3) `Args` is an ordinary
instruction whose defs come from `sem` (the lowering drops it: see below); (4) a branch must be
the last instruction of its block, a return must be a `Rets` (VCode with a mid-block branch is
stuck in both semantics); (5) the callee-saved statement is up to `keep` (for Arm: all of
x19–x28, the low 64 bits of v8–v15).

Proof. `Inv keep a m ρ r₀ := ∀ ℓ s, s ∈ a.get ℓ → Holds s (m ℓ)` with `Holds (vreg v) x :=
x = ρ v`, `Holds (entry r) x := r ∈ calleeSaved ∧ keep r x = keep r (r₀ r)`. `Match` relates run
states when the machine's remaining items check (`runItems`) from an abstract state satisfying
`Inv` and the block's out-state feeds the verified successors (`EdgesOk`). Moves: `Inv_move`.
Instructions: `op_sound` — early uses by the use check, late uses by the use check after the
early defs plus "an early def is disjoint from every use" (static check), then
`Inv_defineAll` / `Inv_clobberAll` / `Inv_defineAll`; the return check gives the callee-saved
conclusion; the havocked defs are forgotten (`transferOp`'s `keptDefs`, and `tryForget` for a
`try_call`'s payload defs on its normal return). Branches: `edgeForget_inv` (the terminator's
dead defs forgotten on the edge, `CheckCtx.edgeForget`), `edge_ok` (`Inv_parCopy`, distinct
parameters) and `Inv_mono` against the verified in-state. Entry: `Inv_entryState`.

## Operand-view obligation (`RegallocOperands.lean`)

Concrete instance: `V = CV = BitVec 128` (an X register zero-extended, `regVal`), `keep = ckeep`,
`W = Arm.ArmState` compared by `SameWorld F` (equal outside the allocatable registers, x16/x17,
the link register x30, the pc and the frame addresses `F`), emitted code run by `execMInst`
(`MInst.lines` → `Insn.toArmInst` → `Arm.exec_inst`; with M5's `Insn.stepi_eq_sem` this is what
`Arm.stepi` does on the encoded word).

x30 is in `Masked` since agent/stack-tls-proof (the TLSDESC `blr` of `tls_value` overwrites it
inside the body). For functions without `tls_value` the end-to-end statement does not get
weaker: x30 is not allocatable and no body instruction reads it; the prologue stores the entry
x30 in the fp/lr slot (an `F` address: `frameF`), the epilogue reloads it from there
(`ret_machine`: the return address comes from the slot, `AbiEntry.lr`), and every function has
a frame (`lowerRFunc_frame`); `ArmRet` never mentioned x30. In the statement `Masked` occurs in
`BodyEntry.other`, a premise on the body-entry world `w₀`: masking x30 drops the requirement
that `w₀` and `s` agree on x30 (a weaker premise). In the callee contract `CalleeOk.os`
(`OperandsSound` of the call hook) the callee no longer has to return with x30 equal to the
world's (a `bl`/`blr` sets x30 to the return address, so the old clause was only satisfiable
when `X.call` put that address in the world), and in exchange it is quantified over caller
states whose x30 differs from the world's: a real callee's effect on everything but the pc
(`CalleeOk.pc`) does not depend on its return address.

```lean
def OperandsSound (F) (exec : MInst → ArmState → Option ArmState) (sem : ISem CV ArmState) (i : MInst) : Prop :=
  ∀ c wh ops regs i' s w outs w',
    i.operands = .ok ops → c.checkStatic wh ops (regs.map .reg) i.clobbers = .ok () →
    i.assign regs = .ok i' → SameWorld F s w →
    sem i (useVals ops regs s) w = some (outs, w', .next) →
    ∃ s', exec i' s = some s' ∧ SameWorld F s' w' ∧
      (∀ p ∈ defRegs ops regs outs, regVal s' p.1.2 = p.2) ∧
      (∀ r, r.allocatable → (∀ p ∈ (ops.zip regs).toList, p.1.isDef → p.2 ≠ r) → r ∉ i.clobbers →
        regVal s' r = regVal s r) ∧
      (∀ r ∈ i.clobbers, r ∈ calleeSaved → ckeep r (regVal s' r) = ckeep r (regVal s r))
```

`operandsSound_step`: from `OperandsSound`, the static checks and a store `m` agreeing with `s`
on allocatable registers, the concrete instruction yields `s'` and a havoc `m2` with
`Clobbered ckeep` such that the store `MStep.op` computes agrees with `s'` on allocatable
registers (and frame locations are untouched). This is where the static checks enter
(allocatable registers, fixed constraints, distinct defs, defs disjoint from clobbers).

`csem F` (value-level semantics built from the Arm model's operations) and the proven
instances:

| Theorem | Instruction (vreg operands of class int) | Side conditions |
| --- | --- | --- |
| `operandsSound_mov` | `mov .size64 rd rm` | — |
| `operandsSound_add` | `aluRRR .add .size64 rd rn rm` | — |
| `operandsSound_addImm` | `aluRRImm12 .add .size64 rd rn imm` | `imm.bits < 4096` |
| `operandsSound_csel` | `csel rd rn rm c` | — |
| `operandsSound_cset` | `cset rd c` | `c ∉ {al, nv}` |
| `operandsSound_load` | `load .uload64 rd (unsignedOffset rn off)` | `8 ∣ off`, `off/8 < 4096`; access avoids `F` |
| `operandsSound_store` | `store .store64 rd (unsignedOffset rn off)` | same |
| `operandsSound_call` | `call ⟨sym, [(v, x0)], [(x0, v')]⟩` | `CalleeSound F callee callSem` |

`CalleeSound` is the AAPCS64 contract of the external callee (results from the argument values
and the world; allocatable registers outside `DEFAULT_AAPCS_CLOBBERS` preserved; low 64 bits of
v8–v15 preserved). It is an assumption about code outside the function, not a model gap.
Memory accesses of the program must avoid the frame addresses `F` (source-level memory
safety: the program never addresses the allocator's slots); `csem` is undefined otherwise.

**Path to all instructions.** Each proof is the same recipe (operand array by `rfl`, register
shape from `checkStatic_facts`/`locOk_int`, `MInst.assign` by `rfl`, `Insn.toArmInst` and
`exec_inst` by `simp`, then `gpr_write_sound` for one-X-register results). Remaining:
other ALU ops/widths and flag-setting forms (world gains the new NZCV), 32-bit forms (upper
half zero), float/vector instructions (`SFP`), other addressing modes (`memFinalize` may use
x16, which is masked), calls of any arity (induction over `info.uses`/`info.defs`) and `blr`,
branches and traps (`Ctl.goto`/`halt`: `OperandsSound` currently covers `next` only; a branch
needs the pc/label correspondence of `emitFunc`), `Args` (the lowering drops it: sound when
its fixed registers still hold the incoming arguments, i.e. no item before it writes an
argument register), `Rets` (becomes the epilogue).

## Frame and move lowering (`RegallocFrame.lean`)

`locVal fr s` reads registers by `regVal` and frame slots at `sp + RAFrame.offset` (8 bytes
zero-extended for int spill / x save slots, 16 for float). `FrameOk fr sp0 F`: distinct frame
locations have separate slots (`Arm.mem_separate'`), all inside `F`.

- `lower_move_reg_int`: `fr.moveInsts (reg xa) (reg xb) = [mov xb, xa]`, and executing it
  gives `locVal = (locVal s)[reg xb ↦ locVal s (reg xa)]` on every maintained location
  (`ValidLoc`: allocatable registers and frame slots), same world, same `sp`;
- `lower_spill_int`: `str xa, [sp, #off]` (unsigned-offset form, `256 ≤ off`, `8 ∣ off`,
  `off < 32768`, `sp` 16-aligned) gives `locVal[stack k int ↦ locVal (reg xa)]`, same world
  (the written bytes are in `F`), same `sp`;
- `lower_reload_int`: `ldr xb, [sp, #off]` likewise;
- `move_agree`: these are exactly `MStep.move`'s store update.

Remaining (trusted until proven): the `stur`/`ldur` encoding for offsets below 256 and the
x16 sequence for large offsets, float moves (through `fmoveTmp`, which lies in `F`),
callee-save slots (same shape as spills), `FrameOk` for `RAFrame.compute` (a layout fact:
int slots, float slots, save slots and `fmoveTmp` are laid out in disjoint ranges above the
CLIF slots and the outgoing area), `sp` alignment maintained, prologue/epilogue (save x29/x30,
restore `sp`).

## How it plugs into M7

1. M4 proves CLIF ≈ VCode semantics `VStep vc (csem F)` (isel) — `csem` is the value-level
   MInst semantics both sides share.
2. `checkAlloc_sound` gives VCode ≈ allocated code `MStep vc (csem F) ckeep rf`.
3. The concrete Arm execution of `lowerRFunc vc rf` refines `MStep` item by item, under the
   relation "`m` agrees with `locVal fr s` on `ValidLoc`, `SameWorld F s w`, `sp = sp0`, pc at the
   item's code": `operandsSound_step` for original instructions, `lower_*` + `move_agree` for
   moves; with M5's `Insn.stepi_eq_sem`/`FnAsm.stepi_eq_sem` each lowered instruction is one
   `Arm.stepi`. Branch lowering, prologue/epilogue and the remaining `OperandsSound`/frame
   cases above are the open pieces of this step.

## Status update (M6Rest2, 2026-09-27)

Done (sorry-free, committed on `agent/m6-rest2`):

- **Float/vector `OperandsSound`** (`RegallocInstsFP.lean`, wrappers in `RegallocOS.lean`):
  `movToFpu` (all sizes), `movFromVec` (every size, every lane index: `umov`'s `match_bv`
  decoding needs the index concrete, the valid ones are enumerated), `vecMisc cnt`,
  `vecLanes addv/uaddlv`, `vecRRR addp`, all arrangements. `corr_tac` fixed: the operand
  pattern now matches the operand count (a trailing float operand was destructured as `Nat.le`).
- **`rm = xzr` forms** (M4Cmp's `subs rd, rn, xzr`): `os_aluRRR_rmZ`, `os_aluRRR_rdZ_rmZ`.
- **umaddl/smaddl**: the Arm model does implement `UMADDL`/`SMADDL`
  (`Data_processing_three_source.lean`); `corr_aluRRRR` covers them. Non-issue.
- **`csem`**: explicit clauses for `emitIsland` (`next`) and `jtSequence` (agreed with M4Ctl:
  `goto 0` on `hs`, else `goto (i+1)` for the index's low 32 bits `< targets.length`, temporaries
  `[0, 0]`). `execLines` now also checks that each instruction advances the pc by 4 (needed to
  run straight-line code on the machine; all `Corr` proofs unchanged).
- **Statement** (with M7Driver): `BodyEntry` (body-entry world after the prologue),
  `sem : ArmState → Sem` per activation, `BodyEntry.argsV` (v0–v7).
- **`IsSimulation`** gains `move` (a move keeps the relation) and `at_op` (at an instruction
  item the VCode is at that instruction).
- **Forward simulation** (`RegallocFwd.lean`): `VStep_det`; `forward` (a machine that
  `Realizes` the allocated code realises every VCode run, through `checkAlloc_sound`'s
  relation); `forward_op` (advance past pending moves to the instruction item).
- **Emission structure** (`FV/E2E/RegLevelEmit.lean`): `fallthrough_eq` (the imperative loop is
  the structural `ftList`), `ftList_label_split` (never looks past a label),
  `ftList_snoc_label`, `ftList_plain_append` (plain lines pass through), `emitFunc_ok`
  (`emitFunc` = `blocksLinesE` + `fallthrough` + trap section), `lowerRFunc_ok` (block code =
  prologue + `itemsCode`), `blocksLinesE_block`, trap-table prefix monotonicity, `emit_block`
  (block `b` in the final lines: its label, then `ftList (lines ++ next label)`).
- **Machine** (`FV/E2E/RegLevelMachine.lean`): `ArmStepX X H fa` = `stepi` except `bl`/`blr`
  (callee hook `H.call`) and the relocated `adrp`/`ldr got`/`add lo12` pairs (`X.sym`); base
  from the program (`progBase`); `insnAt_line`, `armStepX_ins` (one step at a non-hooked line =
  the encoder's instruction at that offset, from M5's `FnAsm.stepi_eq_sem`),
  `iterN_execLines` (straight-line code = `execLines` at the layout's offsets).
- **Relation** (`FV/E2E/RegLevelSim.lean`): `frameF` (frame addresses `[sp_body + intBase,
  sp_entry)`), `RL` (activation data), `StRel` (store = `locVal`, same world, no error,
  program, sp, alignment, fp/lr), `Q` (code position via `emit_block`/`ftList` + `StRel`).

## Remaining (precise, for the next agent)

1. `Realizes (R.sem) ckeep R.step (Q R)` by cases on the item:
   * moves: `lower_*` for every move kind (unsigned-offset int spill/reload/reg move done;
     missing: `stur`/`ldur` (offset < 256), x16 sequence, float moves via `fmoveTmp`, float
     spills, save/restore slots) and `FrameOk (RAFrame.compute …) spB F`;
     plumbing: `codeLinesE_append`, `itemsCode_cons`, `execLines_pc`,
     `lineOffset_drop_ins`, `ftList_plain_append` (+ "body lines have no trap label") are ready;
   * straight-line ops: `operandsSound_step` + `iterN_execLines`; needs
     `MInst.lines c m ps = (lines c m {}).1, ps` for non-`trapIf`/`jtSequence` and a coverage
     statement that every instruction of `vcp` has an `os_*` instance (missing forms:
     loads/stores — address lemmas to `AMode.addr`; `loadAddr`; `aluRRImmLogic` with
     `rn = xzr`, M4AluB2's batch);
   * `Args`: 0 lines; needs a checker check "Args is instruction 0 of block 0, no earlier item
     writes x0–x7/v0–v7, no edge into block 0" (behaviour-preserving on the corpus; not added);
   * calls: `OperandsSound F (hook exec) csem (.call _)` is exactly the AAPCS callee contract
     (state it as the hypothesis `CalleeOk`, plus `H.call` returns to pc+4 with no error and the
     same program); `loadExtNameGot/Near`: two hooked lines;
   * control: `jump`/`condBr`/`testBitAndBranch` via `FnAsm.layout_branch` and
     `emit_block` of the target (label = block index via `VCode.cfg`); the `fallthrough`
     variants of the terminator (`ftStep`); `trapIf` not taken; `jtSequence` needs readable
     code bytes (the table is loaded from memory; propose `AbiEntry.code` + code in `F`) and
     the checker/`MStep` havoc of branch defs.
2. Prologue (from `AbiEntry` to `Q` at block 0 after `prologueLines`, `StRel` incl. `fplr`),
   epilogue (`rets`: `ArmRet`, values, memory, callee-saved from `checkAlloc_sound`'s `keep`
   conclusion), traps (`trapIf` taken / `udf` → `TrapAt` via `layout_traps`/`layout_trap_word`;
   `forward_op` then the halting item).
3. Assemble `RegLevelCorrect (fun s => csem (frameF intBase af s) ctx X) (frameF …)
   (ArmStepX X H fa) vcp af fb` with `forward`/`forward_op`.
4. csem obligations of `backend_correct`: `Refines`, `DriverSem` (incl. `retarget`),
   `CallsRefine` (M4Ctl's contract #5; discharge from an `ExtSem` contract hypothesis).

## Status update (M6Rest3, 2026-09-27)

Done (sorry-free):

- **Frame layout** (`RegallocLayout.lean`): `FrameOk` is now over the live locations `Live rf`
  (int slots `< spillSlots`, float slots only when the code uses float slots — `RFunc.floatStack`,
  every save slot) and carries the `fmoveTmp` facts (`T` = `RFunc.floatMove`);
  `frameOk_compute`: `RAFrame.compute` satisfies it for any non-wrapping `sp0` and `F ⊇ [sp0 +
  intBase, sp0 + size)`; `live_align` (slots aligned to their size, below `size`).
  `RAFrame.compute` names its two flags (`RFunc.floatStack`, `RFunc.floatMove`; same values).
- **Frame-size check** (compiler change, conservative): `lowerRFunc` rejects frames of 32 KiB or
  more. Reason: the model has no SIMD&FP register-offset load/store, so a float slot beyond the
  scaled-immediate range could not be proven; below 32 KiB every slot access is `stur`/`ldur`
  (offset ≤ 255) or the scaled `str`/`ldr`, so the x16 sequence never occurs for slots.
  `lean-e2e-check` unchanged (913 accepted).
- **Slot accesses** (`RegallocSlots.lean`): `exec_store_int`, `exec_load_int`,
  `exec_store_float`, `exec_load_float` for every aligned offset below 32 KiB (both encodings);
  their effect on `locVal` (`store_effect`, `store_dst8/16`, `loadInt_effect`, `loadFloat_effect`).
- **Every checked move** (`RegallocMoves.lean`): `lower_move` — for `checkMove`-accepted moves
  between live locations, `moveInsts` is a list of `MoveInst`s that runs (`ExecAll`, each step
  keeping the error flag and the program) and gives `MoveOk`: world, `sp`, the store
  `upd (locVal s) dst (locVal s src)`, memory outside `[sp, sp + size)` unchanged. Covers int
  register moves, int/float spills, reloads, callee-save saves/restores and float register
  moves through `fmoveTmp`. The old `lower_spill_int`/`lower_reload_int` are superseded (removed);
  `move_agree` is over `ValidLoc ∧ L`.
- **Moves on the machine** (`FV/E2E/RegLevelMove.lean`): `RL.Wf` (pipeline and ABI facts of an
  activation), `RL.frameOk`, `lines_ps` (non-`trapIf`/`jtSequence` expansions are
  emitter-state independent), `codeLinesE_noTrap` (body lines are never trap labels),
  `run_oneLines`, `move_facts`, and **`realizes_move`**: from `Q` at a move item the machine
  reaches `Q` at the next item with `MStep.move`'s store (the `Realizes` move case).
  `StRel.store` is now over `ValidLoc ∧ Live`.

- **Straight-line items** (`FV/E2E/RegLevelOp.lean`): `realizes_op_next` — the `op`/`next`
  case of `Realizes`, given `OperandsSound` of the instruction and `LinesOk` of its allocated
  form (plain unhooked lines; `linesOk_of_oneLine` for one-line forms); `csem_next_world`
  (non-call `next` steps keep the program, error-free world). `straightSem` now also requires
  the canonical run to keep the program (needed for `StRel.prog`; `os_of_corr` unchanged).

Remaining (in the order of the plan above): per-form `LinesOk`/coverage for the `op` of `Realizes` (straight-line via
`operandsSound_step` + an `InterOk` fact for multi-line expansions — `execLines` does not
check the error flag of intermediate states, so each multi-line form, i.e. the x16 address
sequence, needs it — and the coverage of every `vcp` form), `Args`, calls, control flow,
prologue/epilogue, traps, final assembly, and the csem obligations `Refines` (per `ispec`
form), `DriverSem`, `CallsRefine`, and (new, M4Mem's contract #7) `MemRefines`.

## `#print axioms`

New (2026-09-27): `os_movFromVec`, `os_vecRRR`, `os_aluRRR_rmZ`, `checkAlloc_sound`, `forward`,
`emitFunc_ok`, `fallthrough_eq`, `lowerRFunc_ok`, `emit_block`:
`[propext, Classical.choice, Quot.sound]`; `forward_op`: `[propext]`; `ftList_label_split`,
`ftList_plain_append`: `[propext, Quot.sound]`; `iterN_execLines`: those plus M5's
`decode_armBits_*._native.bv_decide` axioms (inherited from `FnAsm.stepi_eq_sem`).

Earlier:

```
checkAlloc_sound, checkAlloc_ret, checkAlloc_halt, checkAlloc_stuck, checkAlloc_diverges,
operandsSound_step, operandsSound_{mov,add,addImm,csel,cset,load,store,call},
lower_move_reg_int, lower_reload_int:
  [propext, Classical.choice, Quot.sound]
lower_spill_int:
  [propext, Classical.choice, Quot.sound, Arm.Memory.read_write_bytes_different._native.bv_decide.ax_1_9]
  (the bv_decide axiom of the Arm model's memory library lemma)
move_agree: [propext, Quot.sound]
```

## Status update (M6Rest4, 2026-09-28)

- **Regression fix (compiler change)**: the allocator's slots now sit right above the outgoing
  area and *below* the explicit CLIF slots. `RAFrame.size` = end of the allocator area (bounded
  `< 32 KiB` by `lowerRFunc`), `RAFrame.total` = whole frame (`AFunc.frameSize`), CLIF slots at
  `slotBase = size`. 64 KiB CLIF slots compile again (corpus 114/114, extrt 22/22, runtests
  3085/0/0, encode-check 971 identical, lean-e2e-check 913/0, regalloc-test 932/932 + all
  mutants rejected). `frameF lo hi` is now `[sp_body+intBase, sp_body+size) ∪ [sp_body+frameSize,
  sp_entry)` (the CLIF slots belong to the world); `frameOk_compute`, `RL.frameOk`,
  `fplr_outside`, `fplr_inF`, `lowerRFunc_ok` updated (`compute_size_le_total`).
- **Interface**: `OperandsSound` and `Corr` assume an aligned `sp` (`Arm.CheckSPAlignment s`;
  slot accesses through `sp` fault otherwise; `StRel.align` provides it). `corr_tac` updated.
- **Loads/stores** (`RegallocMem.lean`): `ldst_load`/`ldst_store` (the model's GPR load/store
  operation), `exec_load_line`/`exec_store_line` for every final addressing mode (`FinalAM`:
  unsigned/unscaled immediate, register, scaled, (scaled-)extended), `steps_loadConst64` (the
  `movz`/`movk` constant load), `StepsOk` (error-free straight-line runs: gives `execLines` and
  the intermediate-state facts `InterOk` needs), `execMInst_load`/`execMInst_store` for every
  `MemMode` (register forms and stack-slot offsets incl. the x16 sequence), `load_core` (the
  operand-independent part of `Corr` for a load) and `corr_load_uoff` (first instance).

Remaining, in order: `Corr` instances for the other load forms and all store forms (a
`store_core` like `load_core`; `SameWorld.write_mem_bytes'`), `loadAddr` (slot offsets incl.
x16 + `add ..., sxtx`), `LinesOk` for the multi-line forms (from `StepsOk`), a decidable
form-coverage predicate over `vcp` (proposed as a premise decided by `lean-e2e-check`, not a
compile-time check: out-of-scope forms such as `fpOffset`/`spOffset` stack-argument accesses
must keep compiling), then `Args`, calls, control flow, `jtSequence`, prologue/epilogue, traps,
the assembly of `RegLevelCorrect`, and the csem obligations (`Refines`, `DriverSem`,
`CallsRefine`, `MemRefines` — `execMInst_load`/`_store` are the canonical-run characterizations
`MemRefines` needs). M4AluB4 announced new `ispec` arms (9bb4e3a: `aluRRRShift` rn=xzr,
`bitfieldMove`, popcnt vector forms) that `Refines` will have to cover.

`#print axioms` (new): `corr_load_uoff`, `execMInst_load`, `execMInst_store`,
`steps_loadConst64`, `RL.frameOk`: `[propext, Classical.choice, Quot.sound]`;
`realizes_op_next`: those plus M5's `decode_armBits_*._native.bv_decide` axioms.

## Status update (M6Ctl, 2026-09-28)

Compiler change (behaviour-preserving; corpus + extrt + runtests compile with no `ctlCheck`
rejection): `lowerRFunc` runs `ctlCheck` (`Regalloc.lean`, `ctlInstOk`): `Args` only as
instruction 0 of block 0 with (int vreg, x0–x7/v0–v7) pairs; before it block 0 has only moves
into memory; no edge enters block 0; `cbz`/`cbnz`/`tbz` tested registers and
`loadExtNameGot/Near` destinations are int vregs. `lowerRFunc_ok` returns `ctlCheck = true`;
`RL.Wf` gains `psF` (the emitter's final state).

Done (sorry-free, `FV/E2E/`):
- `RegLevelArgs`: `AInv` (argument registers while `op 0` of block 0 is pending), `aInv_step`
  (kept by every `MStep` from `Q`), `realizes_args` (no code, store unchanged).
- `RegLevelDriverSem`: `driverSem_csem` (args, jump, rename — `visit_mapRegs`,
  `assign_mapRegs`, `straightSem_mapRegs` —, retarget); `callsRefine_csem` from the external
  contract `XCallsOk env MR X`.
- `RegLevelBranch`: `exec_brInsn`, `brCond_{bcond,cbz,tbz}`, `step_branch` (M5 label
  resolution), `StRel.pc`, `itemsChecked_block`, `q_entry` (machine at a block label ⇒ `Q` at
  the block's items).
- `RegLevelGoto`: `cfg_block` (successor labels), `ft_b`/`ft_cb` (fallthrough rewrites),
  `reach_b`/`reach_cb`, `KindRel`/`kind_alloc`/`kind_brCond(_inv)`, **`realizes_goto`**
  (jump/condBr/testBitAndBranch incl. fallthrough-rewritten variants).
- `RegLevelNext`: `q_op`/`q_next`, `realizes_island`, `realizes_trapIf_next`.

Interface with M6Insts (agreed; their commit 18796fb, `RegallocCover.lean`): `MInst.isCtl`,
`csem_of_not_isCtl`, `FormsCovered`, `formOk_sound` = exactly `realizes_op_next`'s premises.

Remaining (in order): calls (`CalleeOk` hook contract: `OperandsSound` for a `callExec H`, pc+4,
program, error-free `X.call`; proof mirrors `realizes_op_next` with one hooked step),
`loadExtNameGot/Near` (two hooked steps; `gpr_write_sound`), `jtSequence` (open issue: `csem`'s
temporaries `[0, 0]` differ from the machine's, so `Q.store` fails after it — needs a havoc of
branch defs in `MStep`/checker or a weaker store relation; plus `AbiEntry.code` for the table),
`Realizes (Q ∧ AInv)` by cases (all pieces above), prologue/epilogue (stp/ldp/mov sp exec
lemmas), traps (`layout_traps`), and the assembly of `RegLevelCorrect`.

`#print axioms`: `realizes_args`, `driverSem_csem`, `callsRefine_csem`:
`[propext, Classical.choice, Quot.sound]`; `realizes_goto`, `realizes_trapIf_next`: those plus
M5's `decode_armBits_*._native.bv_decide` axioms.

## Status update (M6Insts, 2026-09-28)

- **Interface with M6Ctl** (`RegallocCover.lean`, `RegallocCSem.lean`): `MInst.isCtl`, `FormOk ctx i`
  (decidable covered-form test), `FormsCovered ctx vc` (+ `formsCoveredB`, `Decidable`), 
  `formOk_sound : FormOk ctx i = true → (∀ env, OperandsSound …) ∧ (∀ regs i', assign → LinesOk ∧ ≠args ∧ ≠rets)`.
  Proposed as a premise decided by `lean-e2e-check`.
- **Loads/stores**: `store_core`, generic `corr_load{0,1,2}`/`corr_store{0,1,2}`, `os_load_*`/`os_store_*`
  for every `amodeAddr` mode (slot offsets incl. x16). **loadAddr** of slot offsets:
  `execMInst_loadAddr_slot` (mov/add/sub/x16+`add sxtx`), `os_loadAddr_slot`, `linesOk_loadAddr_slot`.
  `LinesOk` for multi-line forms via `linesOk_gen`/`interOk_prefix` (from `StepsOk`).
- **Design change (decision)**: `Refines F (csem …)` is false with the old csem (ispec ignores operand
  shape: rn = xzr with one use, allocatable rd, wrong use count, erroneous world). csem's straight-line
  clause is now `if csemWF ctx i uses ∧ ERR w = None then straightSem else ispec`; `OperandsSound`
  (and `operandsSound_step`) assume `Arm.r .ERR s = .None` (`realizes_op_next` passes `hst.err`);
  `csem_next_world` via `ispec_world`.
- **Refines**: `RefinesInsts.lean`: `RefAt`, `ref_tac`, `ref_aluRRR` (all ops/sizes) proven.
- **Open**: (1) `RegLevelDriverSem.driverSem_csem.rename` (from main) must handle the new ispec branch:
  needs `ispec (i.mapRegs g) = ispec i` for `VRenaming g` (and `csemWF` invariance). Experiment: 
  `unfold ispec; split <;> split <;> simp_all [ren_xzr, defOut_ren]` leaves only a few goals per
  constructor (~100 s for aluRRR). (2) `ref_*` for the remaining FormOk forms and the final
  `refines_csem : Refines F (csem F ctx X)`. (3) `MemRefines` (use `execMInst_load/_store`,
  `execMInst_loadAddr_slot`; GOT clause is ctl, needs `X.sym n 0 = ofNat b`).
## Status update (M6Ctl2, 2026-09-28)

Done (sorry-free, branch `agent/m6-ctl2`):

- **Calls** (`FV/E2E/RegLevelCall.lean`): `realizes_op_core` (the `op`/`next` case for any
  execution function the machine realises, `RunsAs`; `realizes_op_next` is now an instance),
  `callExec`, **`CalleeOk F X H`** (`OperandsSound` of every call against the hooked callee,
  return to pc+4, `X.call` keeps the program and is error-free), `realizes_call` (one hooked
  step), `symExec`/`os_symAddr`/`realizes_symAddr` (`loadExtNameGot/Near`, two hooked steps).
- **Jump tables** (decision of the integrator; `RegLevelJT.lean`): `MStep.op` has a new premise
  `HavocOuts i outs outs'` (a branch's def values are havocked), the checker's `transferOp`
  forgets a branch's def vregs (`forgetDefs`); `op_sound`/`sim_step`/`sim_progress` adapted.
  Regalloc test unchanged: 932/932 accepted, every mutant rejected (both environments).
  Statement change: `AbiEntry.code` (the code words are readable as data), `CodeAddr`,
  `frameF` includes the code addresses, `StackAvail` keeps the frame off the code, `StRel.code`
  (maintained by ops, moves, branches). `ctlCheck` also requires `jtSequence`'s index and
  temporaries to be int vregs. `jt_machine`, `realizes_jt`.
- **Traps** (`RegLevelTrap.lean`): `trap_udf`, `trap_trapIf` (`TrapAt` via `layout_traps` and the
  trap section `trapLines`).
- **Codegen changes (behaviour-preserving, conservative for the proof)**: the epilogue frees the
  frame by adjusting `sp` (`epilogueLines size`), not `mov sp, fp` (the per-instruction contract
  keeps `sp`, not `fp`); every function keeps a frame (`lowerRFunc_frame`): leaf functions then
  restore lr from the stack, so no per-instruction fact "the body keeps x30" is needed (M6Insts
  could not add it). Corpus/runtests: encode-check 932 identical, native filetests 3085 pass /
  0 fail (runtests).
- `emit_block` gives block 0 at line 0.

Remaining (not done in this run): prologue/epilogue exec lemmas (normal forms established:
`stp` pre-index = write fp/lr at `sp-16`, `sp -= 16`; `mov x29, sp`; `sub/add sp` imm or via
x16 `uxtx`; `ldp` post-index; `ret`), `ArmRet` from `checkAlloc_sound`'s keep conclusion,
`Realizes (Q ∧ AInv)` by cases (all cases now exist: moves, `realizes_op_next` via
`formOk_sound`, args, calls, symbol addresses, islands, `trapIf` not taken, goto, jump tables;
halts/rets are trivial for `Realizes` since `Q` is `True` there), and the assembly of
`RegLevelCorrect` (prologue → `Q` at `MConf.init`, `forward`/`forward_op`, then
`trap_udf`/`trap_trapIf` or the epilogue). Merging main needs M6Insts' note (driverSem_csem
`rename` case for the `ispec` branch).

`#print axioms realizes_jt / realizes_call / realizes_symAddr`: `propext, Classical.choice,
Quot.sound` plus M5's `decode_armBits_*._native.bv_decide` axioms.

## Status update (M6Ctl3, 2026-09-28)

Done (sorry-free, branch `agent/m6-ctl3`, merged with `agent/m6-insts` f216ee3):

- **Prologue/epilogue on the machine** (`FV/E2E/RegLevelFrame.lean`): exec lemmas
  `exec_stp_fplr`, `exec_mov_fp_sp`, `exec_{sub,add}_sp_imm`, `exec_{sub,add}_sp_x16uxtx`,
  `exec_ldp_fplr`, `exec_ret`; `spAdj_ok` (the `sp` adjustment, `Imm12` or `x16` + `uxtx`),
  `prologue_ok`, `epilogue_ok` (as `StepsOk` runs); `iterN_steps` (straight-line lines on the
  machine); `entry_block` (block 0: label at line 0, prologue, items); **`q_init`**: after the
  prologue the machine satisfies `Q R s_body (MConf.init rf (locVal fr s_body) w₀)` and `AInv`
  for every `BodyEntry` world `w₀`, and every field but pc/x16/x29/sp is as at entry;
  **`ret_machine`**: from `Q` at a `Rets` item, the epilogue and `ret` reach `ra` with `sp` and
  x29 as at entry, the allocatable registers and memory as at the item, and the `j`-th
  returned value in the `j`-th fixed register (callee-saved restores are the `restores` moves
  before the item, realised by `realizes_move`).
- **`Realizes (Q ∧ AInv)` by cases** (`realizes_all`, `FV/E2E/RegLevelCorrect.lean`): moves,
  covered straight-line forms via `formOk_sound` under `FormsCovered` (control outcome `next` by
  `csem_ctl`: `ispec_ctl`, `mspec_ctl`), `Args`, calls, symbol addresses, islands, `trapIf`,
  branches, jump tables; `Rets`/`udf` end the run.
- `forward_last` (generic): the machine reaches the allocated configuration whose `MStep`
  successor is related to the VCode's successor (used for `rets` and halts instead of
  `forward_op`, so the halting item's condition is read off the allocated step).
- `csem_halt` (only `udf` and a taken `trapIf` halt), `udf_ops`, `trapIf_nodefs`.
- **`regLevelCorrect_backend`**: `RegLevelCorrect (fun s => csem (frameF lo hi af s) ⟨fa.k,
  af.slotBase⟩ X) (frameF lo hi af) (ArmStepX X H fa) vcp af fb` (`lo`/`hi` = `intBase`/`size`
  of `RAFrame.compute vcp rf`) from `checkAlloc`, `lowerRFunc`, `emitFunc`, `layout`,
  `FormsCovered ⟨fa.k, af.slotBase⟩ vcp` and `∀ s, CalleeOk (frameF lo hi af s) X H`.
  `ArmRet`: lr and x29 from the fp/lr slot (`StRel.fplr`), x19–x28 and the low 64 bits of
  v8–v15 from `checkAlloc_sound`'s `keep` conclusion (`ckeep`) through the store relation,
  `sp` from `spB + size + 16`; values from the fixed uses; memory from `SameWorld`.
- **`E2E.backend_correct_final`** (`FV/E2E/Final.lean`): `backend_correct_m4` with `hM6`
  instantiated; final hypothesis list in `e2e.md` ("Final hypotheses").
- **Compiler change (behaviour-preserving)**: `ctlCheck` requires the values of a `Rets` to be
  int vregs (a real register there would shift the returned-values/operands correspondence);
  `lean-backend` over corpus, extrt and runtests (445 files): no function rejected.
- Build fixes after the merge: `RegLevelOp.csem_next_world` removed (superseded by
  `csem_next_world'`, `RegallocCSemWorld`); `os_oneDef` takes the new `ERR` premise of
  `OperandsSound`; `exec_{add,sub}_sp_x16` renamed `…x16uxtx` (clash with `RegallocMemAddr`).

Remaining: `Refines`/`MemRefines` of `csem` (M6Insts), deciding `FormsCovered`
(`formsCoveredB`) in `lean-e2e-check`, the callee contract `CalleeOk` and `XCallsOk`
(environment).

`#print axioms regLevelCorrect_backend`: `propext, Classical.choice, Quot.sound`, M5's
`decode_armBits_*`/`decode_raw_inst_of_*` `_native.bv_decide` axioms and
`Arm.Memory.read_write_bytes_different._native.bv_decide.ax_1_9`.

## Status update (M6Insts2, 2026-09-28)

- **Build fix**: `CSemRename.lean` proves `ispec_mapRegs`, `formOk_mapRegs`, `csemWF_mapRegs`,
  `amodeAddr_mapRegs`, `mspec_mapRegs` for a `VRenaming` (registers split into renamed vreg /
  concrete real register, uses by length, enumerations; then `rfl`). `driverSem_csem.rename`
  uses them via `csem_straight`.
- **csem change (decision)**: the straight-line clause is now
  `if csemWF ∧ ERR w = None ∧ CheckSPAlignment w then straightSem else mspec ctx.slotBase`.
  `mspec` = `ispec` extended by the memory forms exactly as `MemRefines` states them, so
  `MemRefines` holds on error/misaligned worlds, where the canonical run can't be used.
  `csem_of_wf`/`csem_useVals` take the alignment (from `OperandsSound`'s `SameWorld` + aligned `s`).
- **FormOk must be narrowed (NOT applied: the edit broke `RegallocOS`'s `fo_tac` proofs)**: `false` for logical immediates, immediate shifts,
  `bitfieldMove`, FP/vector forms; `movWide` only `movz`; `xzr` destinations of imm/extended
  `add`/`sub` only for `adds`/`subs` (Arm writes `sp` otherwise — with the current FormOk `Refines`
  for csem is FALSE on those forms). Re-enabling needs Arm-level lemmas: bitmask round-trip of `bitmaskEnc?`,
  `DecodeBitMasks` with symbolic immr/imms (or enumeration), `movn` values, `cnt/addp/addv/umov/fmov`.
- **Refines**: `RefinesInsts.lean`: `ref_tac`/`ref_tac_fl` and `RefAt` lemmas for aluRRR (all 5
  register shapes), aluRRRR (+xzr), aluRRImm12 (+xzr adds/subs), aluRRRShift, aluRRRExtend
  (+xzr adds/subs), bitRR, movWide(movz), movK, cset, csel, ccmpImm.
- **Open**: `ref_extend` (3 cases), the dispatcher `refAt_of_wf` and the final
  `Refines F (csem F ctx X)`; `MemRefines` (needs premises `ctx.slotBase = slotOff` and
  `syms n = some b → X.sym n 0 = ofNat b`, since csem is parametric in both).

## Status update (M6MemRef, 2026-09-28)

- **`MemRefines` proven**: `memRefines_csem (hsb : ctx.slotBase = sb)
  (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b) : MemRefines F sb syms (csem F ctx X)`
  (`FV/Backend/Proof/MemRefines.lean`; axioms `propext`, `Classical.choice`, `Quot.sound`).
  Off error-free aligned worlds (or with an ill-formed use list) `csem` is `mspec`, which is
  `MemRefines`' result verbatim. Otherwise `straightSem`: `ss_load`/`ss_store` (from
  `execMInst_load`/`execMInst_store` on the canonical load/store of `x0`, address operands in
  `x1`/`x2`) per `amodeAddr` arm (`straight_load`/`straight_store`; the extended index modes via
  `ext_uxtw`/`ext_sxtw`), and `straight_loadAddr` (from `execMInst_loadAddr_slot'`). GOT loads
  are `X.sym n 0` (premise `hsym`).
- **`E2E.backend_correct_final`**: `hmem` replaced by `hsym` and `hslot : af.slotBase = slotOff`
  (neither `Compiled` nor the statement fixes `slotOff`; callers instantiate
  `slotOff := af.slotBase`).

## Status update (M6Refines, 2026-09-28)

- **`Refines` proven**: `refines_csem (F ctx X) : Refines F (csem F ctx X)`
  (`FV/Backend/Proof/RefinesCSem.lean`); `E2E.refines_final` is `hRef` at the backend's choices
  and `E2E.backend_correct_final` no longer takes `hRef`. Proof: control forms by `csem`'s own
  arms (`holds_eq`); off error-free aligned worlds or ill-formed uses `csem` is `mspec`, which is
  `ispec` wherever `ispec` is defined (`mspec_of_ispec`); otherwise `refAt_of_wf` dispatches on
  the `FormOk` arm and the use count to the per-form `RefAt` lemmas.
- **`FormOk` narrowed (soundness)**: register 31 as destination of `add`/`sub` immediate and
  extended-register, and of the logical-immediate forms, is `sp` unless the instruction sets the
  flags: those `xzr`-destination arms now require `adds`/`subs` resp. `ands` (`Refines` was false
  otherwise). The `os_*_rdZ` lemmas take the op premise.
- **Logical immediates**: `FormOk` also requires `logicImmOk op sz imm` — a per-instruction check
  that the emitter's `bitmaskEnc?` encoding of the (possibly inverted, 32-bit-truncated)
  immediate exists and Arm's `DecodeBitMasks` decodes it to the operand `ispec` states (with
  `N = 0` at 32 bits). Decision: translation validation instead of a general round-trip proof of
  `bitmaskEnc?`. New covered form: `orr rd, xzr, #imm` (`aluRRImmLogic` with `rn = xzr`, the
  bitmask `mov`; `corr_aluRRImmLogic_rnZ`, `os_aluRRImmLogic_rnZ`, `ref_aluRRImmLogic_xn`).
- **`RefinesInsts2.lean`**: bitfield moves with symbolic `immr`/`imms` — `dbm_len` (generic
  `DecodeBitMasks` equation given `len`), `dbm64`/`dbm32` (non-immediate masks), `bfm_core` (the
  bitwise identity of Arm's masked result with `bfmVal`), `exec_bfm64`/`exec_bfm32` (used by the
  canonical runs before `exec_bitfield` unfolds); `bfm_lsl`/`bfm_lsr`/`bfm_asr`/`bfm_sxt`/`bfm_uxt`;
  `extract_dup_ror` (`ror` immediate); `pi_movw` (`movn`); `cnt_aux_8`/`addv_aux_8`/`addp_aux_8`/
  `elem_get_sw64` (vector forms). `RefAt` for `bitfieldMove`, `aluRRImmShift`, `extend`, `movn`,
  `fmov`/`umov`/`cnt`/`addv`/`addp`, shifted-register `xzr` forms, logical immediates.
- **Coverage**: `lean-e2e-check` now decides `formsCoveredB` on every prepared VCode and prints
  the uncovered instructions; corpus + extrt + runtests: 913 of 913 checked functions covered
  (before the `rn = xzr` logical-immediate form: 907, the 6 others used `orr rd, xzr, #imm`).
- `#print axioms E2E.backend_correct_final`: `propext`, `Classical.choice`, `Quot.sound` and
  `_native.bv_decide` axioms only (no `sorryAx`).

## Status update (agent/callee-fix, 2026-10-02)

The callee contract changed (`docs/contracts/e2e.md`, "Callee contract with a dead stack"):
`CalleeOk F K X H S` (`os : ∀ ctx info, S info → CallSoundCtl F K (callExec H) (csem F ctx X)
(.call info) .next`), `TlsOk F K X H`, `CalleeTryOk F X H S` (since agent/trycall-contract over the `try_call` sites
`VCode.TrySite` and for the results only: the exception payload defs are havocked on the
normal return, `havocFrom`, and the checker forgets them on that edge, `CheckCtx.edgeForget`); `RL` has the callees' stack budget
`K`, `RL.F = frameW K …` (the world excludes the frame and the dead stack below `spB`),
`RL.FK = frameF …` (the frame `FrameKeep` keeps), `RL.Wf.stack : StackAvail R.K R.af R.s0`.
`realizes_op_core` takes `OperandsSoundCtlAt R.F R.FK` at the state (`OperandsSoundCtl.at` for
straight-line instructions, `RL.callAt` for calls, the call of a `try_call` and the TLSDESC hook);
`operandsSound_step` is stated at one state (`OperandsSoundCtlAt F FK`, in `RegallocOperands`),
with the kept frame `FK`.
`regLevelCorrect_backend` takes `K`, `hC : ∀ s, CalleeOk (frameW K lo hi af s) K X H
vcp.CallSite` and gives `RegLevelCorrect (fun s => csem (frameW K lo hi af s) …) (frameW K lo hi
af) K (ArmStepX X H fa) vcp af fb`.
