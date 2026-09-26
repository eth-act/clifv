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
