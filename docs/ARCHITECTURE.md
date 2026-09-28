# Repository architecture and cross-component contracts

`docs/PLAN.md` is the design plan and `docs/PINS.md` lists the pinned versions. This file
records who owns what, and the interfaces between components. Change an interface here
first, then update its producer and its consumers together.

## Layout

| Path | Component | Milestone |
| --- | --- | --- |
| `FV/Clif/` | CLIF syntax, printer, parser, `Clif.run`, filetest runner | M0 |
| `FV/DSL/` | `flat def` frontend: deep AST, `denote`, checker, elaborator | M1 |
| `FV/Compile/` | DSL → CLIF emitter (`compile`) and its proof `compile_correct` | M1, M2 |
| `FV/Arm/` | AArch64 semantics (ASL-derived), decoder, and later the encoder | M3, M5 |
| `FV/Validate/` | per-function translation validator: Cranelift AArch64 output against CLIF | M3 |
| `FV/Isle/` | Lean ISLE syntax, generated rule data (aarch64 lowering; mid-end `opt` in `Generated/Opt`, `Isle.Opt`), rule interpreter (incl. multi terms), `Isle.Opt.simplify` | M4, M7 |
| `FV/Backend/` | isel, stack-slot allocator, regalloc checker, asm/bytes emission | M4–M6 |
| `FV/E2E/` | `backend_correct` | M7 |
| `FVTest/` | Lean-side tests and corpora drivers (`lean_exe` targets) | all |
| `rust/crates/clif2obj` | Cranelift driver (PLAN.md Appendix A), with relocation dumps | M1, M3 |
| `rust/crates/clif-oracle` | `clif-oracle interp <file.clif>`: runs the Cranelift interpreter on `; run:` lines, output JSON | M0 |
| `rust/crates/clif-native` | `clif-native <file.clif>`: compiles with Cranelift for aarch64, runs `; run:` lines natively under qemu, output JSON (same schema as clif-oracle) | M1 |
| `rust/crates/isle2lean` | exports ISLE rules and VeriISLE specs to Lean data | M4 |
| `rust/crates/flat-runtime` | runtime externs (collections), built for aarch64 | M1 |
| `corpus/` | DSL programs and generated `.clif` for differential testing | M1+ |
| `third_party/wasmtime` | pinned Cranelift sources (fetched by `scripts/fetch-third-party.sh`, not committed) | — |

## Ground rules (from PLAN.md §0, binding on every component)

- No `sorry` in any merged Lean file. No new `axiom` declarations. Each claimed theorem's
  `#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound`, plus the
  compiled-evaluation trust axioms Lean v4.34.1 auto-generates: `<thm>._native.bv_decide.ax_*`
  (from `bv_decide` when it needs them) and `<thm>._native.native_decide.ax_*` (from `native_decide`).
  These replace `Lean.ofReduceBool` from older toolchains, with the same trust base. Prefer
  `omega`/`decide`/`simp` in library lemmas; keep `bv_decide` for real bit-blasting goals.
- Lean: core and `Std` only, no Mathlib (keeps the toolchain pin to `v4.34.1` alone).
- Lean namespaces follow the directories: `Clif`, `DSL`, `Compile`, `Arm`, `Validate`, `Isle`, `Backend`, `E2E`.
- Anything executable that is meant as a model must be *checkable* against an external
  oracle: Cranelift's interpreter, native execution under `qemu-aarch64-static`, or `llvm-mc`.

## Building

- Lean: `lake build` (all of `FV`), or `lake build FV.Clif.Run` for a single module.
  Components are separate module trees, so concurrent builds of different trees are fine.
- Rust: `cargo build --manifest-path rust/Cargo.toml -p <crate>`.
- aarch64 executables: `aarch64-unknown-linux-musl` std target or freestanding objects,
  linked with `rust-lld`, run with `qemu-aarch64-static`. No aarch64 gcc or glibc sysroot is
  installed. `clang --target=aarch64-linux-gnu -ffreestanding -nostdlib -c` works for C shims.

## Workflow: one git worktree per agent

- The main checkout belongs to the integrator. Every agent works in its own worktree,
  created by `scripts/agent-worktree.sh <name>`, at `../clifv-wt/<name>` on branch
  `agent/<name>`. The script copies warm `.lake`/`rust/target` caches and symlinks the pinned
  `third_party` sources.
- Agents commit on their own branch after every meaningful step. They never push, merge,
  rebase, or touch other branches or worktrees.
- The integrator pushes agent branches to `origin` at each check-in, verifies finished work,
  merges it into `main` (`--no-ff`), pushes `main`, then removes the worktree.
- Scripts must not hardcode an absolute checkout path. Derive the repo root from the script's
  own location.
- The agent file tools (read/edit/write/grep) resolve relative paths against the integrator's
  checkout, not the agent's worktree. Every tool path an agent uses must therefore be absolute,
  under `/home/kev/work/clifv-wt/<name>/`. In bash, `cd` into the worktree in the same command.
- Every Lean/lake, cargo, or test command an agent runs must go through `scripts/memcap.sh`
  (a per-command cgroup memory cap, `FV_MEMCAP`, default 16G), e.g.
  `cd <worktree> && scripts/memcap.sh lake build FV.Backend`. A runaway `lean` process then
  dies alone. Without the cap, `lean` processes reaching 37–58 GB triggered global OOM kills
  on this 62 GB machine; those aborted the agent harness and killed every running agent.
- Never reduce the exported ISLE programs (`Isle.Aarch64.program`, `Isle.Opt.program`, the generated rule data)
  wholesale with the kernel or `decide`/`rfl`/`native_decide`. Reason about individual rules
  or per-opcode slices, and keep `maxHeartbeats` and `maxRecDepth` at their defaults, unless
  a local, justified increase is needed.
- Never use `git stash` in a worktree: the stash is shared by every worktree of the repository,
  so one agent can pop or drop another's entry. To set work aside, commit it on your own branch.
- Temporary files go under private names (`/tmp/<agent>_*`), because `/tmp` is shared.

## Contract: CLIF in Lean (`FV/Clif`, producer M0)

The authoritative API is documented in `docs/contracts/clif.md` (written by M0). Required shape:

- `Clif.Ty`: integer types `i8 i16 i32 i64 i128` only. Floats and vectors are outside the subset.
- `Clif.Val`: a width-indexed `BitVec`, e.g. `⟨ty, BitVec ty.width⟩`.
- `Clif.Function`, `Clif.Program` (a list of functions and extern declarations), SSA values,
  blocks with parameters, and the opcode subset listed in `docs/contracts/clif-subset.md`
  (named, versioned; version `clif-subset-v2`).
- `Clif.print : Program → String` and `Clif.parse : String → Except String Program`, with
  output accepted by `cranelift-reader` 0.136.1.
- `Clif.run`: executable and fuel-bounded:
  `Clif.run (env : Clif.Env) (p : Program) (f : String) (args : List Val) (fuel : Nat) : Clif.Outcome`,
  where `Outcome := returned (List Val) (Mem) | trapped TrapCode | stuck String | outOfFuel`.
  `stuck` means a precondition was violated: an ill-typed or ill-formed program, or a
  `notrap`/`aligned` flag that is false at run time. Flags are preconditions, not behaviour.
  `Env` gives the semantics of extern callees as Lean functions on `(args, Mem)`.
- Memory: byte-addressed and little-endian, with explicit allocations (stack slots are
  allocations). An access outside every allocation traps with `heap_oob` if the access may
  trap, and is `stuck` if it is `notrap`.

## Contract: DSL (`FV/DSL`, producer M1-frontend)

Documented in `docs/contracts/dsl.md`. Required: `DSL.Ty`, an intrinsically typed deep AST
`DSL.Stmt Γ τ`, `DSL.FlatFn σ τ`, `DSL.denote`, `DSL.FlatFn.checked`, `DSL.Err`, and the `flat def`
command, which generates the deep AST constant `<name>.ast`, the shallow `<name>`, and
`<name>.denote_eq`. `M := Except DSL.Err`.

## Contract: error-tag ABI (PLAN.md §3.2)

A compiled `flat def f : σ → M τ` becomes a CLIF function returning `(i8 tag, payload...)`:
`tag = 0` is `ok` with payload `τ`, and `tag = k > 0` is `throw (Err.ofTag k)`, with the payload
zero-filled. Traps are never used to signal `throw`. The error enum's tag assignment is
fixed by `DSL.Err.tag`.

## Contract: Arm model (`FV/Arm`, producer M3-model)

Documented in `docs/contracts/arm.md`, with the model choice in `docs/decisions/arm-model.md`.
Required: `Arm.State` (X0–X30, SP, PC, NZCV, byte memory), `Arm.decode : BitVec 32 → Option Arm.Inst`,
`Arm.exec : Arm.Inst → Arm.State → Arm.State` (or an error), `Arm.run` with fuel, and later
`Arm.encode`. It must be validated against `qemu-aarch64-static` on test vectors.
