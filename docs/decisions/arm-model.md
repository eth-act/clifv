# Decision: AArch64 model = LNSym (ported), not Sail Arm

Status: decided at the start of M3 (PLAN.md §4 M3 says "decide by M3"). Supersedes the
open question in PLAN.md §6, "Arm model size".

## Choice

Use LNSym's `Arm/` library (github.com/leanprover/LNSym, commit
`5c05220ff970e3bdd7813ad0c9ef3741522c8b92`, Apache-2.0) as the base of `FV/Arm`. Port it from
its toolchain (`nightly-2024-10-07`) to the pinned `v4.34.1`, and extend it with any
instructions Cranelift emits that it lacks.

## Why

- LNSym is an Arm semantics in Lean whose instruction definitions are transcribed from the
  Arm ARM/ASL pseudocode. It is already co-simulated against hardware (`Arm/Insts/Cosim`).
  It has a decoder, `stepi`/`run`, and byte memory.
- It is about 14k lines for `Arm/`, and it is scalar-first; the crypto and SIMD parts are
  dropped from the port. Sail Arm is several hundred thousand lines, and its Lean
  backend path needs a Sail/OCaml toolchain that is not installed. The project owner has
  also reported trouble with sail-arm before.
- The owner's standing instruction is not to rewrite the Arm ISA from scratch unless there
  is no other option. Porting LNSym and adding missing instructions in LNSym's style
  (ASL-transcribed, co-simulated) complies with it.

## Checkability (PLAN.md §0: models must be checkable)

- Every instruction the backends emit must be covered by co-simulation vectors, run as
  native aarch64 executables under `qemu-aarch64-static` and compared with `Arm.run` on
  random register states.
- Instructions added beyond upstream LNSym cite the Arm ARM section and ASL function they
  transcribe. Where VeriISLE's ASL-derived spec (`cranelift/codegen/src/isa/aarch64/spec/*.isle`)
  covers the same instruction, they are also cross-checked against that spec.

## Revisit if

Sail's Lean backend becomes usable for the Arm model at the pin (rems-project/sail-tiny-arm-lean
exists, but it covers only a tiny subset), or LNSym's coverage gaps make porting costlier than
extraction.

## Results (M3-model, 2026-09-27)

- The port builds: 70 modules under `FV/Arm`, all imported by `FV/Arm.lean`, and
  `lake build FV.Arm` is clean. There is no `sorry` and no hand-written `axiom`. `native_decide`
  appears only in upstream `example`s, which is allowed by the v4.34.1 axiom policy.
- Coverage: the required list comes from compiling `clif-subset-v1` CLIF at i8–i64 with
  Cranelift 0.136.1 (`opt_level=none`, `is_pic`) and disassembling the output. All 772 distinct
  words in that corpus decode and execute. The table, with upstream/added status, is in
  `docs/contracts/arm.md`.
- Checkability: `scripts/arm-cosim.sh` (`lake exe arm-cosim`) co-simulates 161 instruction
  forms against `qemu-aarch64-static`, 200 random vectors per form by default: 32 200 vectors,
  0 failures. A run with `--seed 12345 --n 1000` gave 161 000 vectors and 0 failures.
  Co-simulation also found upstream LNSym bugs, now fixed: register 31 was read as SP instead of
  XZR in FMOV (general), DUP/INS (general) and UMOV/SMOV. The earlier ASL audit had already fixed
  the same bug in CBZ/CBNZ, BR/BLR/RET, MOV wide and LDP, plus the CBZ/CBNZ offset truncation.
- Symbolic simulation: the ported `sym_n` proves register effects of straight-line programs,
  including one with a load (`FVTest/Arm/Sym/Demo.lean`). That meets the M3 validator's need.
- Nothing so far suggests revisiting this decision.
