# Arm model contract (`FV.Arm`, LNSym port)

Producer: M3-model. Model choice: `docs/decisions/arm-model.md`. Attribution:
`third_party/NOTICE-lnsym.md`.

## Status (work log for successors)

- DONE: `FV/Arm.lean` imports all 70 non-test modules, and `lake build FV.Arm` is clean.
- DONE: required-instruction list (below). It was derived by compiling CLIF with Cranelift 0.136.1
  (`opt_level=none`, `is_pic=true`, `enable_verifier`, `regalloc_checker`, aarch64) and
  disassembling the output with `llvm-mc`, then cross-read against `lower.isle`, `inst.isle`,
  `inst/emit.rs` and `abi.rs`. Every one of the 772 distinct instruction words from that corpus
  decodes and executes in the model without an `Unimplemented`/`Illegal` error.
- DONE: co-simulation (`lake exe arm-cosim`, `scripts/arm-cosim.sh`). 161 forms, 32 200
  vectors, 0 failures.
- DONE: symbolic-simulation demo (`FVTest/Arm/Sym/Demo.lean`); see "Tactic API" below.
- DONE: `third_party/NOTICE-lnsym.md`.
- Nothing remains for M3-model. `Arm.encode` is M5.

## Public API (namespace `Arm`)

Names follow LNSym. `docs/ARCHITECTURE.md` uses generic names; they map as follows:
`Arm.State` = `ArmState`, `Arm.Inst` = `ArmInst`, `Arm.decode` = `decode_raw_inst`,
`Arm.exec` = `exec_inst`, `Arm.run` = `run`.

| What | API | Module |
| --- | --- | --- |
| State | `ArmState` with fields GPR x0–x30, SP (`GPR 31`), v0–v31 (`SFP`, 128-bit), `PC`, `PState` (N Z C V), `mem : Memory` (`BitVec 64 → BitVec 8`, little-endian), `program : Program`, and an error field. `ArmState.default` is all zeros, with an empty program and no error. | `FV.Arm.State` |
| Generic read/write | `r (fld : StateField) s`, `w fld v s`, where `StateField := GPR i \| SFP i \| PC \| FLAG f \| ERR`. There are simp lemmas `r_of_w_same`, `r_of_w_different`, `w_of_w_shadow`, … | `FV.Arm.State` |
| GPRs | `read_gpr n i s` / `write_gpr n i v s` treat register 31 as SP. `read_gpr_zr` / `write_gpr_zr` treat it as XZR (ASL `X[]`). Reads take the low `n` bits; writes zero-extend to 64 bits. | `FV.Arm.State` |
| SIMD&FP | `read_sfp n i s`, `write_sfp n i v s` (the write zero-extends to 128 bits) | `FV.Arm.State` |
| PC | `read_pc s`, `write_pc v s` | `FV.Arm.State` |
| Flags | `read_flag f s` / `write_flag f v s` with `f : PFlag := N \| Z \| C \| V`; `read_pstate`, `write_pstate`, `make_pstate`; `ConditionHolds cond s` (ASL) | `FV.Arm.State`, `FV.Arm.Insts.Common` |
| Memory | `read_mem_bytes n addr s : BitVec (n*8)`, `write_mem_bytes n addr v s` (little-endian, wraps mod 2^64); `Memory.read_bytes`/`write_bytes`; separation theory in `FV.Arm.Memory.{Separate,SeparateProofs,MemoryProofs}` (`mem_separate'`, `mem_subset'`, …) | `FV.Arm.State`, `FV.Arm.Memory.*` |
| Program | `Program := Map (BitVec 64) (BitVec 32)` (an association list); `def_program`, `set_program s p`; `fetch_inst addr s : Option (BitVec 32)` (`@[irreducible]`). Code is disjoint from data memory: `mem` never holds instructions. | `FV.Arm.Map`, `FV.Arm.State` |
| Decode | `decode_raw_inst : BitVec 32 → Option ArmInst`. `ArmInst := DPI \| BR \| DPR \| DPSFP \| LDST \| RES` (per-class structures in `FV.Arm.Decode.*`). `none` = not decoded, i.e. unallocated or outside the modelled classes. | `FV.Arm.Decode` |
| Execute | `exec_inst : ArmInst → ArmState → ArmState` | `FV.Arm.Exec` |
| Step | `stepi s`: if the error field is `None`, fetch at `PC`, decode, execute; otherwise `s` is unchanged | `FV.Arm.Exec` |
| Run | `run (n : Nat) s` (fuel = number of `stepi`s); `run_plus`, `run_onestep`, `run_opener_*`, `stepi_eq_of_fetch_inst_of_decode_raw_inst` | `FV.Arm.Exec` |

### Outcomes (`read_err s : StateError`)

| Outcome | Meaning |
| --- | --- |
| `.None` | Normal. |
| `.Trap imm16` | `UDF #imm16` executed. The state is otherwise unchanged (PC still at the `udf`), and `stepi` makes no further progress. Architecturally this is the Undefined Instruction exception, which Linux delivers as `SIGILL` at that PC. Cranelift's trap is `udf #0xc11f`. The trap code lives only in Cranelift's side table, not in `imm16`. |
| `.NotFound msg` | No instruction at `PC` in `program`. |
| `.Unimplemented msg` | The word does not decode, or it decodes to a form the model does not implement (e.g. PRFM, PAC hints). |
| `.Illegal msg` | UNDEFINED / CONSTRAINED UNPREDICTABLE encodings that the model refuses, e.g. load with writeback where `Rn = Rt`. |
| `.Fault msg` | SP-based access with SP not 16-byte aligned (`CheckSPAlignment`). |
| `.Other msg` | Internal. |

Once the error field is non-`None`, `stepi`/`run` leave the state unchanged.

Model assumptions: EL0 and AArch64 only; no exceptions other than the `udf` trap; no
top-byte-ignore, pointer authentication, BTI-guarded pages or speculation (`csdb`, `bti` are
NOPs); memory is flat, total and little-endian, with no alignment faults except the SP check.

## Module mapping (LNSym `Arm/`, `Tactics/` → `FV/Arm/`)

| LNSym @ 5c05220 | FV | Notes |
| --- | --- | --- |
| `Arm/{Attr,BitVec,Decode,Exec,FromMathlib,Map,MinTheory,State}.lean` | `FV/Arm/…` | ported to v4.34.1 |
| `Arm/Decode/{BR,DPI,DPR,DPSFP,LDST}.lean` | `FV/Arm/Decode/…` | new classes added (below) |
| `Arm/Insts/**` (scalar + subset of SIMD) | `FV/Arm/Insts/**` | fixes and additions (below) |
| `Arm/Memory/{Attr,MemoryProofs,Separate,SeparateProofs}.lean` | `FV/Arm/Memory/…` | ported |
| `Tactics/{Attr,BvOmegaBench,Common,FetchAndDecode,IntroHyp,Simp,StepThms,Sym}.lean`, `Tactics/Sym/*` | `FV/Arm/Tactics/…` | ported: `sym_n` and `#genStepEqTheorems` |
| — | `FV/Arm/Decode/Reserved.lean`, `FV/Arm/Insts/Reserved/Udf.lean`, `Insts/BR/Test_branch.lean`, `Insts/DPI/Extract.lean`, `Insts/DPR/{Add_sub_ext_reg,Conditional_compare}.lean`, `Insts/DPSFP/Advanced_simd_across_lanes.lean` | FV additions |

Ported files keep the Amazon copyright header. Modified files say so in a "Modified by
fv-compiler-rust (2026)" comment. New files are marked "FV addition".

Dropped (not ported):

- The SIMD/crypto instruction files `Arm/Insts/DPSFP/{Advanced_simd_extract, _modified_immediate,
  _permute, _scalar_copy, _scalar_shift_by_immediate, _shift_by_immediate, _table_lookup,
  _three_different}`, `Crypto_*`, and `Arm/Insts/LDST/Advanced_simd_multiple_struct`. Cranelift
  does not emit them for the integer-only `clif-subset-v1`, and they account for most of LNSym's
  proof and elaboration cost.
- `Arm/Cosim.lean` and `Arm/Insts/CosimM.lean` (LNSym's own co-simulation, which needs native Arm
  hardware), and the per-instruction `.rand` generators that depend on them. Their replacement is
  `FVTest/Arm/Cosim` (QEMU).
- `Arm/Cfg`, `Arm/Syntax`, `Arm/Util`.
- `Arm/Memory/{AddressNormalization,Common,MemOmega,SeparateAutomation}` (`mem_omega`, `simp_mem`).
- `Tactics/{Aggregate,CSE,ChangeHyps,ClearNamed,Name,PruneUpdates*,Rename,SkipProof,SymBlock}`.

None of the dropped modules is on the dependency path of the model or of `sym_n`. Port them from
upstream if memory-separation automation is needed later. Also not ported: LNSym's `Proofs/`, `Specs/`, `Tests/`, `Benchmarks/`, `Correctness/`: out of scope.

Fixes to upstream semantics, all found against the ASL or by co-simulation (each is noted in its
file): register 31 is XZR, not SP, in CBZ/CBNZ, BR/BLR/RET, MOVZ/MOVN/MOVK, LDP/LDPSW, FMOV
(general), DUP/INS (general) and SMOV/UMOV. The CBZ/CBNZ offset is
`SignExtend(imm19:'00')` (upstream lost `imm19<18:17>`). The GPR single-register load/store
decode follows the ASL for every `size`/`opc`.

## Required instructions (Cranelift 0.136.1, `opt_level=none`, `clif-subset-v1` at i8–i64)

Status: **port** = in upstream LNSym; **port+fix** = in upstream, semantics fixed; **added** = FV
addition, transcribed from the Arm ARM ASL (cited in the file header); **extra** = not emitted,
modelled and co-simulated anyway. "Seen" = observed in the Cranelift probe output (see Status),
with the CLIF source. The cosim column is vectors / failures for `scripts/arm-cosim.sh` (default
seed `0x5eed`, 200 per form). A second run, `--seed 12345 --n 1000`, gave 161 000 vectors and 0
failures.

| Form (encoding class) | Status | Seen / emitted for | Cosim |
| --- | --- | --- | --- |
| `add` (imm, incl. `mov xd, sp`, `add sp, sp, #n`) | port | iadd, frames | 200/0 |
| `adds` (imm; `cmn`) | port | icmp with negative imm | 200/0 |
| `sub` (imm; `sub sp, sp, #n`) | port | isub, frames | 200/0 |
| `subs` (imm; `cmp`) | port | icmp, br_table bound | 200/0 |
| `and` (imm) | port | band, masks | 200/0 |
| `orr` (imm; `mov` bitmask) | port | bor, iconst | 200/0 |
| `eor` (imm) | port | bxor | 200/0 |
| `ands` (imm; `tst`) | port | brif of band | 200/0 |
| `movn` / `movz` / `movk` | port+fix | iconst, large frames | 200/0 each |
| `sbfm` (`asr #`, `sxtb/h/w`) / `ubfm` (`lsl/lsr #`, `uxtb/h`) | port | shifts by const, extends | 200/0 each |
| `bfm` | port (extra) | — | 200/0 |
| `extr` (`ror #`) | added | rotl/rotr by const | 200/0 |
| `adr` / `adrp` | port | br_table, GOT calls | 200/0 each |
| `add`/`sub` (shifted reg; `neg`) | port | iadd/isub/ineg | 200/0 each |
| `adds` (shifted reg) | port (extra) | — | 200/0 |
| `subs` (shifted reg; `cmp`) | port | icmp | 200/0 |
| `add`/`sub` (extended reg; `add/sub sp, sp, x16, uxtx`) | added | large frames | 200/0 each |
| `subs` (extended reg; `cmp w, w, uxtb/sxth`) | added | icmp i8/i16 | 200/0 |
| `adds` (extended reg) | added (extra) | — | 200/0 |
| `and`/`orr` (`mov`)/`eor`/`orn` (`mvn`) (shifted reg) | port | band/bor/bxor/bnot, moves | 200/0 each |
| `bic`/`eon`/`ands`/`bics` (shifted reg) | port (extra) | — | 200/0 each |
| `udiv` / `sdiv` | added | udiv/urem/sdiv/srem | 200/0 each |
| `lslv` / `lsrv` / `asrv` / `rorv` | port | ishl/ushr/sshr/rotl/rotr | 200/0 each |
| `madd` (`mul`) | port | imul | 200/0 |
| `msub` | added | urem/srem | 200/0 |
| `smulh` / `umulh` | added | smulhi/umulhi | 200/0 each |
| `clz` / `rbit` | added | clz, ctz | 200/0 each |
| `cls` | added (extra) | — | 200/0 |
| `csel` | port | br_table index clamp | 200/0 |
| `csinc` (`cset`) | added | icmp | 200/0 |
| `csinv` / `csneg` | added (extra) | — | 200/0 each |
| `ccmp` (imm) | added | sdiv/srem overflow guard | 200/0 |
| `ccmn` (imm), `ccmp`/`ccmn` (reg) | added (extra) | — | 200/0 each |
| `adc`/`adcs`/`sbc`/`sbcs` | port (extra) | — | 200/0 each |
| `b.cond` (all 16 conds) | port | brif, trap guards | 200/0 |
| `cbz` / `cbnz` | port+fix | brif, div-by-zero guard | 200/0 each |
| `tbz` / `tbnz` | added | brif of band with a single-bit const | 200/0 each |
| `b` / `bl` | port | jump / colocated call | 200/0 each |
| `br` / `blr` | added | br_table / GOT call | 200/0 each |
| `ret` (x30) / `ret xn` | port+fix | return | 200/0 each |
| `nop`, `csdb` (and `bti`) | port / added | `csdb` only with `use_csdb` | 200/0 each |
| `udf #imm16` | added | trap | 200/0 |
| `ldr`/`str` x and w, `ldrb`/`strb`, `ldrh`/`strh`, `ldrsb` (x/w), `ldrsh` (x/w), `ldrsw` — unsigned imm | port (str/ldr/strb/ldrb) + added | load/store/uload*/sload*/istore*, GOT | 13 × 200/0 |
| same 13 — unscaled (`ldur*`/`stur*`) | added (GPR) | negative/unaligned offsets, spills | 13 × 200/0 |
| same 13 — register offset (`[xn, xm{, lsl/uxtw/sxtw/sxtx #s}]`) | added | large offsets, br_table `ldrsw [x, w, uxtw #2]` | 13 × 200/0 |
| same 13 — pre-index `[xn, #s]!` | added | odd callee-save count (`abi.rs`) | 13 × 200/0 |
| same 13 — post-index `[xn], #s` | port (str/ldr/strb/ldrb) + added | odd callee-save restore | 13 × 200/0 |
| `stp`/`ldp` (x, w), `ldpsw` — signed offset, pre-index, post-index | port+fix | frames, callee saves | 15 × 200/0 |
| `fmov s/d ← w/x`, `fmov w/x ← s/d` | port+fix | popcnt | 4 × 200/0 |
| `cnt` (8b/16b) | added | popcnt | 200/0 |
| `addv` (b/h/s) | added | popcnt i32/i64 | 200/0 |
| `addp` (vector) | added | popcnt i16 | 200/0 |
| `uaddlv` | added (extra) | — | 200/0 |
| `umov` (b/h/s/d lanes) | port+fix | popcnt | 200/0 |

Sequences, all built from rows above:

- Prologue: `stp x29, x30, [sp, #-16]!; mov x29, sp; stp x19..x28 pairs [sp, #-16]!` (or
  `str x, [sp, #-16]!` for an odd count); `sub sp, sp, #n`, or for large frames
  `movz/movk w16; sub sp, sp, x16, uxtx`. The epilogue mirrors it with `add`, `ldp …, [sp], #16`,
  `ret`.
- Calls: `bl` for colocated callees. Otherwise, under `is_pic`,
  `adrp x, :got:f; ldr x, [x, :got_lo12:f]; blr x`. Stack arguments use `stur`/`str`.
- `br_table` (`JTSequence`, `emit.rs`): `cmp w, #n; b.hs default; csel x, xzr, x, hs;
  [csdb when use_csdb]; adr x8, table; ldrsw x9, [x8, w9, uxtw #2]; add x8, x8, x9; br x8;`
  followed by the 32-bit offset table words (data, not executed).
- popcnt (`lower.isle`): `fmov s/d, w/x; cnt v.8b, v.8b;` then nothing (i8), `addp` (i16), or
  `addv b` (i32/i64); then `umov w, v.b[0]`.
- Traps (`trap`, the zero-divisor guard, and signed div/rem overflow via `ccmp` + `b.vs`) are
  `udf #0xc11f`.

Not modelled, because Cranelift does not emit them for the subset: `ldr` (literal), PRFM, SIMD&FP
register-offset loads and stores, exclusives/atomics, system instructions other than hints.

## Co-simulation (`FVTest/Arm/Cosim/*`, `lake exe arm-cosim`)

`scripts/arm-cosim.sh [--n N] [--seed S] [--only SUBSTR] [--show K]` builds and runs it.
Environment: `ARM_COSIM_CLANG` (default `clang`), `ARM_COSIM_LLD` (default: `rust-lld` from the
active rustc sysroot), `ARM_COSIM_QEMU` (default `qemu-aarch64-static`). Exit 0 means every
vector matched. Output has one `form<TAB>vectors<TAB>failures` line per form, then a total line.

Per vector: a random valid encoding of the form, with all register fields random, including
31 (SP or ZR according to the form). The initial state is random: x0–x30 (biased towards edge
values), SP, NZCV, v0–v30 and a 64-byte data buffer. Batches of vectors (one batch per
instruction class) become one freestanding static aarch64 program (`Harness.lean`), assembled
by clang, linked by rust-lld, and run under qemu-aarch64-static with raw `write`/`exit`
syscalls. The program echoes the initial state, runs each instruction, and reports x0–x30, SP,
NZCV, PC, v0–v30 and the buffer afterwards. Lean rebuilds the initial state from the echo, runs
`stepi`, and compares every field. It also checks the error outcome: `.None`, or `.Trap imm16`
for `udf`, where the QEMU side is a `SIGILL` handler reading the signal frame.

- Memory forms: the base register (or SP, kept 16-byte aligned) is set so that the effective
  address falls inside the buffer, for random immediates and register offsets.
  Writeback/unpredictable register overlaps are avoided.
- Branch forms: targets are limited to ±32 instructions, where landing pads record the reached
  PC. The immediate fields therefore span only small magnitudes, in both signs. `br`/`blr`/`ret`
  targets are landing-pad addresses.

## Tactic API (symbolic simulation)

From `FV.Arm.Tactics.Sym` and `FV.Arm.Tactics.StepThms`. The worked examples are in
`FVTest/Arm/Sym/Demo.lean` and `FVTest/Arm/Sym/Simple.lean`.

1. Define the program: `def prog : Program := def_program [(addr, word), …]`.
2. `#genStepEqTheorems prog` generates, per instruction, `prog.stepi_eq_0x…`, which rewrites
   `stepi s` into `exec_inst` of the decoded instruction, given the fetch hypotheses.
3. State the theorem over `s0 sf : ArmState`. `sym_n` finds its hypotheses by type (up to
   defeq), not by name: `s0.program = prog` (where `prog` must be a global constant),
   `read_pc s0 = addr` (a literal), `sf = run n s0` (a literal `n` ≥ the number of steps
   taken), `read_err s0 = .None` and `CheckSPAlignment s0`. If either of the last two is
   missing, `sym_n` adds it as a new goal.
4. Proof: run `simp_all only [state_simp_rules, -h_run]` (the prelude), then `sym_n n`.
   `sym_n` steps through `n` instructions. For each intermediate state `s{k}` it introduces
   hypotheses `h_s{k}_pc`, `h_s{k}_err`, `h_s{k}_x{i}` (written registers), `h_s{k}_non_effects`
   (every other field unchanged), `h_s{k}_memory_effects`, `h_s{k}_program` and
   `h_s{k}_sp_aligned`. It then simplifies the goal with them. If a goal remains, it is a pure
   `BitVec` statement over the initial state's registers and memory reads, such as
   `Memory.read_bytes 8 (r (GPR 0) s0) s0.mem`. Close it with `bv_decide`, `omega` or
   `simp [bitvec_rules]`. `sym_n n at s` starts from a named state.
   `sym_n (while := tac) n` replaces the tactic that discharges the step-count side goal
   `steps = (steps - 1) + 1` (the default is `omega`). This matters when the step count is
   symbolic.

Worked examples: `add_ret_sym` (`add x0, x0, x1; ret`; `sym_n 2` closes the goal) and
`load_scale_sym` (`ldr x2, [x0]; add; lsl; sub; ret`, i.e. `x0 := 7 * (mem64[x0] + x1)`; closed
by `sym_n 5` and then `bv_decide`). Both build in about a second.

`#print axioms` for the demos shows only `propext`, `Classical.choice`, `Quot.sound` (plus
`*._native.bv_decide.ax_*` where `bv_decide` is used).
