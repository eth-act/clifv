# Why Lean's output differs from stock Cranelift

This explains the stock comparison's numbers (`docs/STOCK-COMPILER-COMPARISON.md`):
why outputs differ or are rejected, and where a fix would go. The counts come from
the `main` push run 37250037579 (`5863d3a`): of 4,455 stock outputs, 425 match, 983
differ, 1,176 are rejected for a setting and 1,871 for an operation. Pull requests
#47 (settings) and #50 (repeated function names) change these counts. To see the
current numbers, run the breakdown on a comparison output, either local or from a
CI artifact (`stock-comparison-artifacts-N`, directory `target/ci-comparison`):

```sh
python3 scripts/stock-comparison-breakdown.py target/ci-comparison
```

## Different outputs (983)

| Shape | Outputs |
| --- | --- |
| Neither side sets up a frame; Lean's code is longer | 606 |
| Neither side sets up a frame; same length | 207 |
| Both set up a frame; Lean's code is longer | 162 |
| Both set up a frame; same length | 6 |
| Neither side sets up a frame; Lean's code is shorter | 2 |

Three causes explain the samples we read. They overlap, and the counts are by
shape, not by proven cause.

### 1. Lean lowers every instruction; stock skips dead ones

Cranelift lowers each block bottom-up (`machinst/lower.rs:864`, at the pinned
commit). It skips a pure instruction when none of its results has a lowered use
(`is_any_inst_result_needed`, `machinst/lower.rs:724`). So a value that is used only
inside a pattern its user already matched never reaches a register. Examples: an
`icmp` folded into a `select`, an `iconst 0` that became `xzr`, a `stack_addr` folded
into a load's address. Cranelift also sinks a load into its single use. Lean
lowers top-down and lowers every instruction, dead or not
(`FV/Backend/Isel.lean:20-26`).

`egraph/issue-11578-semantics.clif` `%eq_k1`: `v4 = icmp eq v3, 0` is used only by
`select v4, 6, 7`.

```text
stock                          Lean
mov  x8, #2                    mov  x3, #2
movk x8, #0xfffe, lsl #48      movk x3, #0xfffe, lsl #48
and  x8, x0, x8                and  x6, x0, x3
mov  x9, #6                    mov  x8, #0          ; dead: iconst 0
mov  x10, #7                   cmp  x6, #0          ; dead: the icmp itself
cmp  x8, xzr                   cset x11, eq         ; dead
csel x9, x9, x10, eq           mov  x13, #6
cmp  x9, #6                    mov  x15, #7
cset x0, eq                    cmp  x6, xzr
ret                            csel x0, x13, x15, eq
                               cmp  x0, #6
                               cset x0, eq
                               ret
```

`isa/aarch64/stack.clif` `%stack_load_small`: Lean adds a dead `mov x1, sp` (the
`stack_addr` that the load already folded in), and is otherwise identical.

The extra instructions also change the instruction positions and virtual
registers that regalloc2 sees, so register choices diverge after them. Most of the
768 longer outputs probably have this cause; only samples were checked.

### 2. Callee-saved registers: stock pushes them, Lean stores them in the frame

In 139 of the 168 outputs where both sides set up a frame, the third instruction
differs: stock pushes a callee-saved register there, and Lean allocates the frame.
Stock pushes callee-saved registers in pairs with pre-indexed stores, then
allocates the rest of the frame (`gen_clobber_save`, `isa/aarch64/abi.rs:774`). Lean allocates one frame and stores the registers into
save slots inside it. The saves and restores are allocator moves (`RAFrame.compute`,
`FV/Backend/Regalloc.lean:230-239`), and `ctlCheck` and the register-level proof
rely on that shape.

134 of these 139 are in the atomics tests, whose LL/SC loops use the fixed
registers x24–x28.
Their bodies are identical, for example `isa/aarch64/atomic-rmw.clif`
`%atomic_rmw_add_i64`:

```text
stock                              Lean
stp x29, x30, [sp, #-16]!          stp x29, x30, [sp, #-16]!
mov x29, sp                        mov x29, sp
str x28, [sp, #-16]!               sub sp, sp, #0x30
stp x26, x27, [sp, #-16]!          stur x24, [sp]
stp x24, x25, [sp, #-16]!          ... (x25-x28 at sp+8..sp+32)
<identical loop>                   <identical loop>
ldp x24, x25, [sp], #16            ldur x24, [sp]
ldp x26, x27, [sp], #16            ... (x25-x28)
ldr x28, [sp], #16                 add sp, sp, #0x30
ldp x29, x30, [sp], #16            ldp x29, x30, [sp], #16
ret                                ret
```

Matching stock also means matching its frame layout. Upward from `sp`, stock has
the outgoing-argument area, CLIF stack slots, spill slots, then the pushed
registers (`machinst/abi.rs:64-92`). Lean has spill slots, save slots, then CLIF
stack slots.

### 3. Same length, different registers (207)

Typically a single temporary register differs, as in `isa/aarch64/amodes.clif`
`%f14`, where stock has `sxtw x3, w0` and Lean has `sxtw x2, w0`. regalloc2
starts its register search at an offset computed from the instruction position
and the bundle number (regalloc2 0.15.2, `src/ion/process.rs:1075`). So its choice
depends on the instruction positions and virtual registers it is given. The likely cause, not yet checked, is that Lean numbers temporaries in a
different order than Cranelift, which allocates them while lowering bottom-up.
Fixing cause 1 changes these too.

### Where fixes would go

All three causes are in the verified backend, not in the stock adapter.
`FVTest/Backend/StockConfig.lean` only implements settings, and its output is
already outside `backend_correct`.

- Causes 1 and 3 need Cranelift's bottom-up lowering in `lowerFunction`, with
  sinking and skipping of dead instructions, plus proofs. Its completeness was just
  proved (V1, #4), and V3 (#5, form coverage) works on the same code.
- Cause 2 changes the frame layout in `RAFrame`/`lowerRFunc` and the frame proofs,
  which overlaps V5 (#7).

Coordinate with those work packages before starting (`AGENTS.md`).

## Rejected for a setting (1,176)

The adapter rejects a request with a setting Lean does not implement. The receipt
names only the first such setting, so a test may need several. On `main` the
largest are `enable_llvm_abi_extensions` (299), `enable_multi_ret_implicit_sret`
(298), `opt_level=speed`/`speed_and_size` (243) and `has_lse` (136). #47 accepts
settings that cannot change a function, which leaves 477. Most of the rest are
`opt_level=speed`, which needs Cranelift's e-graph mid-end, and functions with LSE
atomics, `use_csdb`, or `is_pic=false` far symbols.

## Rejected for an operation (1,871)

Grouped by Lean's first error for the function. Lean reports the first
unsupported thing it meets, so a vector function can appear under a scalar type.

| Outputs | First error | Work package |
| --- | --- | --- |
| 957 | integer vector type (`iNxN`) | S12 SIMD (#36) |
| 486 | scalar float type (`f32`/`f64`) | S11 floats (#35) |
| 232 | float vector type | S11, S12 |
| 37 | `const` declarations | |
| 33 | `tail` calling convention | S8 (#32) |
| 17 | user function names `uN:N` | |
| 14 | `is_pic=false` far symbols (a setting; #47 reports it as one) | |
| 95 | other: missing operations (`uadd_overflow_trap`, overflow multiplies, `iabs`, `bitselect`, `trapz`/`trapnz`, `return_call_indirect`, `get_stack_pointer`, ...) | |
