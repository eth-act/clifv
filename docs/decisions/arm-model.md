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

## Atomics: trusted single-threaded assumption (agent/atomics-proof, 2026-10-01)

`E2E.backend_correct_final` covers `atomic_load`, `atomic_store` and `fence`. Once the LL/SC
loops are proven, it will also cover `atomic_rmw`/`atomic_cas`. These rest on a **trusted**
property of the Arm model, which is single-core and has no other agents:

- `LDAR`/`LDAXR` (`Arm.LDST.exec_reg_exclusive`, `L = 1`) are plain zero-extending loads.
- `STLR`/`STLXR` are plain stores. An exclusive store **always succeeds** and writes status 0
  to `Rs` (for `STLR`, `Rs` is `XZR`, so nothing is written). There is **no exclusive
  monitor**.
- `DMB ISH` (`Arm.BR.exec_barrier`) only advances the pc.

This is sound for the CLIF semantics `Clif.run`, which is single-threaded. It does **not**
model concurrent agents: a theorem about a multi-threaded execution would need a memory
model and a monitor, and Cranelift's LL/SC retry loops would then be needed. The co-simulation
(`scripts/arm-cosim.sh`) does not exercise exclusives against another agent.

## Thread-local storage: trusted TLSDESC hook (agent/stack-tls-proof, 2026-10-01)

`E2E.backend_correct_final` covers `tls_value` (`elf_gd`, cg_clif's setting). Its code is
Cranelift's TLSDESC sequence (`ElfTlsGetAddr`, `emit.rs`):

```
adrp x0, :tlsdesc:v ; ldr tmp, [x0, :tlsdesc_lo12:v] ; add x0, x0, :tlsdesc_lo12:v
blr tmp ; mrs tmp, tpidr_el0 ; add x0, x0, tmp
```

The model cannot run it: it has no system registers (`mrs tpidr_el0` stops with an error), and
the resolver `tmp` calls is code of the dynamic linker, outside the function. The machine of the
theorem (`ArmStepX X H fa`, `FV/E2E/RegLevelMachine.lean`) therefore hooks the sequence, as it
hooks calls: the `adrp` only advances the pc, and at the `ldr` the rest of the sequence runs as
one step `H.tls v tmp`. The hook's contract `TlsOk F X H` (`FV/E2E/RegLevelTls.lean`, premise
`hTls` of `backend_correct_final`, only for a function with a `tls_value`) is the **trusted**
part:

- `pc`: the hooked step ends at the instruction after the sequence;
- `seq`: x0 holds the variable's address `X.sym v 0`, `tmp` holds the thread pointer `X.tp`;
  every other register except x30 (the `blr` writes it), the condition flags, the memory and
  the program are unchanged;
- `flags`: the flags are `X.tlsFlags v w`, a function of the world (the resolver may change
  them).

`Clif.run` has one thread, whose instance of a thread-local variable `v` is the memory's symbol
`v` (`Clif.Mem.symbols`, `docs/contracts/clif.md`); `tls_value` gives its address, as
`symbol_value` does. The theorem is about that one thread: the caller's `syms` (with `hsym`,
`X.sym v 0` is `syms v`) gives the address of the running thread's instance of `v`, and
`TlsOk.seq` says the sequence computes it (`TPIDR_EL0` plus the resolver's offset). That
the dynamic linker's resolver and the thread pointer produce this address is trusted, like
the GOT contents of `symbol_value`.

The register clause is Cranelift's TLSDESC convention (`ElfTlsGetAddr` in
`inst/mod.rs`: the resolver "is required to preserve all registers except x0 and x30"; the
register allocator keeps values live in every other register across the sequence). `TlsOk` is
that convention, plus the flags: it lets the resolver change NZCV, so the proof does not rely on
the flags surviving the sequence.
