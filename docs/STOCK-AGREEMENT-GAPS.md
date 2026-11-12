# Why Lean's output differs from stock Cranelift

This explains the stock comparison's numbers (`docs/STOCK-COMPILER-COMPARISON.md`):
why outputs differ or are rejected, and where a fix would go. The counts come from
the `main` push run 37250037579 (`5863d3a`): of 4,455 stock outputs, 425 match, 983
differ, 1,176 are rejected for a setting and 1,871 for an operation. #50 (repeated
function names) and #47 (settings) have since changed these counts: 465 match,
1,145 differ, 432 are rejected for a setting and 2,413 for an operation. The
section "Different outputs" uses the earlier run.

The two "Rejected" sections use a newer run: the `main` push run 42181236069
(`60188b47`, 2026-11-06). Of 4,455 stock outputs, 1,882 match, 115 differ, 563
are rejected for a setting and 1,895 for an operation. To see the current
numbers, run the breakdown on a comparison output, either local or from a CI
artifact (`stock-comparison-artifacts-N`, directory `target/ci-comparison`):

```sh
python3 scripts/stock-comparison-breakdown.py --top 100 target/ci-comparison
```

## Different outputs (983)

On 2026-11-06, 115 outputs differ. A comment on #557 assigns each of them to
an issue.

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
registers x24–x28. Without the frame setup and the saves, 40 of the 134 bodies
are identical, for example `isa/aarch64/atomic-rmw.clif` `%atomic_rmw_add_i64`
below. Changing how callee saves are stored is not enough for the rest:

- In 92, the CLIF stack slot is at a different address (stock: `sp`; Lean:
  above its save slots; see the frame layout below). In 48 of these, a
  temporary register also differs (cause 3).
- The other 2 are in `runtests/atomic-cas.clif`. Both have dead `stack_addr`
  results in Lean (cause 1). In `%atomic_cas_i32` the comparison also differs,
  on purpose: stock compares all 64 bits (`cmp x27, x26`), Lean only the low 32
  (`cmp x27, w26, uxtw`). Cranelift 0.136.1 fails the compare-and-swap when the
  upper bits of the register holding the expected value are nonzero; Lean fixes
  this upstream bug (commit `482ed62`). This output cannot match without the bug.

`isa/aarch64/atomic-rmw.clif` `%atomic_rmw_add_i64`:

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

## Rejected for a setting (563)

The adapter rejects a request with a setting Lean does not implement. The receipt
names only the first such setting, so a test may need several. #47 accepts
settings that cannot change a function. Four settings are rejected only for the
functions that they change: `has_lse`, `use_csdb`, `sign_return_address` and
`is_pic=false` far symbols. The other settings reject the whole request.

| Outputs | Setting | What Lean needs |
| --- | --- | --- |
| 243 | `opt_level=speed` (238), `speed_and_size` (5) | Cranelift's e-graph mid-end |
| 171 | `is_pic=false` with a far symbol | the non-PIC far-symbol lowering |
| 114 | `has_lse=true` with `atomic_rmw`/`atomic_cas` | LSE atomics |
| 11 | `use_bti=true` | BTI landing pads |
| 8 | `probestack_strategy=inline` (5), `probestack_size_log2` other than 12 (3) | inline stack probes (#581) |
| 6 | `use_csdb=true` with `select_spectre_guard`/`br_table` | `csdb` |
| 3 | `bb_padding_log2_minus_one` other than 0 | block padding |
| 2 | `sign_return_address=true` in a function that is signed | pointer authentication |
| 5 | other: `tls_model` (2), `enable_compact_unwind_abi`, `enable_pinned_reg`, `enable_table_access_spectre_mitigation=false` | |

## Rejected for an operation (1,895)

Grouped by Lean's first error for the function. Lean reports the first
unsupported thing it meets, so a vector function can appear under a scalar type.

| Outputs | First errors | Work package |
| --- | --- | --- |
| 1,257 | vector types: integer (`iNxN`) 990, float (`fNxN`) 267 | S12 SIMD (#36) |
| 216 | scalar floats: the `f32`/`f64` type 66, `fcvt_to_uint`/`fcvt_to_sint` 40, the saturating converts 31, `bxor`/`bnot`/`band`/`bor` on float values 30, `fma` 21, `fcmp one`/`ueq` 20, `fcopysign` 5, `call_indirect` with float parameters or returns 3 | S11 floats (#35) |
| 157 | tail calls: the `tail` calling convention 122, `return_call_indirect` 26, `try_call` to a `tail` callee 9 | S8b (#380) |
| 152 | integer operations: `select_spectre_guard` 60, the overflow operations (`{s,u}{add,sub,mul}_overflow`, `uadd_overflow_trap`) 49, `trapz`/`trapnz` 20, `iabs` 9, `cls` 8, `bitselect` 6 | |
| 71 | declarations and names: `const` declarations 38, user function names `uN:N` 20, `stack_limit` 5, `dss` 3, patchable function references 3, `dyn_scale_target_const` 2 | |
| 20 | special registers: `get_stack_pointer` 11, `get_frame_pointer` 4, `get_exception_handler_address` 3, `get_return_address` 2 | |
| 14 | other calling conventions: `apple_aarch64` 6, `windows_fastcall` 6, `preserve_all` 2 | |
| 8 | ABI limits: too many return values of one register class 5, an `i128` parameter of `atomic_cas` 3 | |
