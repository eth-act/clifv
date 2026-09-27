# Cross-read: `Clif.Sem` vs VeriISLE CLIF specs

Pinned: `third_party/wasmtime/cranelift/codegen/src/spec/inst_specs.isle` (wasmtime v49.0.1,
Cranelift 0.136.1). For every opcode of the emitter subset E (`docs/contracts/clif-subset.md`)
this file quotes the spec, states whether our definition agrees, and names the Lean theorems
in `FVTest/Clif/SpecCrossread.lean` (namespace `Clif.SpecCrossread`) that check it. The theorems
compare our definition with a Lean transcription of the spec (`Spec.*`), not with itself.

Build: `lake build FVTest.Clif.SpecCrossread` (no `sorry`; `#print axioms` shows only
`propext`, `Classical.choice`, `Quot.sound` and `*._native.bv_decide.ax_*`).

## How the spec language is transcribed

| VeriISLE / SMT-LIB | Lean transcription |
| --- | --- |
| `bvadd bvsub bvneg bvmul bvand bvor bvxor bvnot` | `+ - - * &&& \|\|\| ^^^ ~~~` on `BitVec w` |
| `bvudiv x y` (SMT-LIB: `~0` if `y = 0`) | `bvudiv` (explicit `y = 0` case) |
| `bvurem x y` (SMT-LIB: `x` if `y = 0`) | `bvurem` |
| `bvsdiv`, `bvsrem` | `bvsdiv`, `bvsrem`: the SMT-LIB definitions by cases on the sign bits, via `bvudiv`/`bvurem` of absolute values |
| `bvslt bvsle bvsgt bvsge` / `bvult ...` | comparisons of `toInt` / `toNat` |
| `bvshl bvlshr bvashr` (bit-vector amount) | `<<< >>> sshiftRight'` with a `BitVec` amount |
| `rotl`/`rotr` (`encode_rotate` in `veri/src/solver.rs`) | `rotl`/`rotr`: `(x << a') \| (x >> (w - a'))`, `a' = a urem w` |
| `clz` (`veri/src/encoded/clz.rs`) | `clzRounds`: binary search over shifts `w/2 … 1` plus the final round |
| `rev` (`encoded/rev.rs`) | `rev8/16/32/64`: swap halves, then masked swaps with the literal masks of the encoding |
| `popcnt` (`encoded/popcnt.rs`) | `popcnt k`: sum of the `w` bits in `k = log2 w + 1` bits, zero-extended |
| `zero_ext n x` / `sign_ext n x` | `0#(n-w) ++ x` / `(sign copies) ++ x` |
| `conv_to n x`, `n < w` | `x.extractLsb' 0 n` (only narrowing `conv_to` occurs in the E specs we compare) |
| `(modifies clif_trap)` | `SpecOut.trap` / `SpecOut.val r`; our `Except TrapCode` result is mapped by `toSpec`, which forgets the trap code (VeriISLE has none) |

Widths: every E spec is instantiated at i8/i16/i32/i64 (`bv_*_8_to_64` forms). Each theorem
below exists per width (`*_i8 … *_i64`); for shifts and rotates the amount width `v` is
universally quantified (`v ≤ 64`), which covers both `bv_shift_8_to_64` and the `slow`
`bv_shift_8_to_64_extra` instantiations. Generic lemmas (`*_eq`) hold for all widths where
the transcription is width-independent.

## Per opcode

### `iconst`
```
(spec (iconst ty arg) (provide (= arg (zero_ext 64 result)) (= (:bits ty) (widthof result))))
```
Agrees. `Inst.iconst ty imm` carries the result bits `imm : BitVec ty.width` directly; the
reader's `Imm64` is their zero-extension (`parse` builds `BitVec.ofInt w i`, the reader
masks to `uN`). `iconst_i8 … iconst_i64`: the spec relation determines the result uniquely
(`zero_ext 64` is injective below 64 bits). `iconst.i128` is not valid CLIF (the parser
rejects it).

### `iadd`, `isub`, `ineg`, `imul`
```
(spec (iadd ty x y) (provide (= result (bvadd x y)) ...))   ; also i128
(spec (isub ty x y) (provide (= result (bvsub x y)) ...))
(spec (ineg ty x)   (provide (= result (bvneg x)) ...))
(spec (imul ty x y) (provide (= result (bvmul x y)) ...))
```
Agree (wrapping). `iadd_eq isub_eq ineg_eq imul_eq`; `iadd_i8 … iadd_i128`, `isub_i*`,
`ineg_i*`, `imul_i*`.

### `umulhi`, `smulhi`
```
(spec (umulhi ty x y) (provide (= (:bits ty) (widthof result))
  (let ((double (concat x x)) (double_width (widthof double))
        (xwide (zero_ext double_width x)) (ywide (zero_ext double_width y)))
    (with (low) (= (concat result low) (bvmul xwide ywide))))))
```
(`smulhi`: `sign_ext`.) Agrees: ours is the high half of the double-width product,
`(x.zeroExtend (w+w) * y.zeroExtend (w+w)).extractLsb' w w`. `umulhi_spec`/`smulhi_spec`: our
result satisfies the relation (with `low` = the low half); `umulhi_unique`/`smulhi_unique`:
the relation determines the result. Per width: `umulhi_i*`, `smulhi_i*`.

### `udiv`, `urem`
```
(spec (udiv ty x y) (modifies clif_trap)
  (provide (= result (bvudiv x y)) (= clif_trap (bv_is_zero! y)) ...))
(spec (urem ty x y) (modifies clif_trap)
  (provide ... (if (bv_is_zero! y) clif_trap (and (not clif_trap) (= result (bvurem x y))))))
```
Agree: trap iff `y = 0` (our trap code `int_divz`), otherwise the unsigned quotient /
remainder. For `udiv` the spec also constrains `result` when trapping (SMT `bvudiv x 0 = ~0`);
a trapping instruction has no result, so `SpecOut` ignores it. `udiv_eq urem_eq`,
`udiv_i* urem_i*`.

### `sdiv`
```
(spec (sdiv ty x y) (modifies clif_trap)
  (provide (= (widthof result) (:bits ty))
    (if (bv_is_zero! y) clif_trap
    (if (and (= x (bv_top_bit_set! (widthof x))) (bv_is_zero! (bvnot y))) clif_trap
      (and (not clif_trap) (= result (bvsdiv x y)))))))
```
Agrees: traps on `y = 0` (ours: `int_divz`) and on `MIN / -1` (ours: `int_ovf`), otherwise
truncating signed division. `sdiv_i8 … sdiv_i64` (the division is bit-blasted per width).

### `srem`
```
(spec (srem ty x y) (modifies clif_trap)
  (provide ... (if (bv_is_zero! y) clif_trap (and (not clif_trap) (= result (bvsrem x y))))))
```
Agrees: traps only on `y = 0`; `srem MIN, -1 = 0`. `srem_i8 … srem_i64`.
(The Cranelift interpreter traps `int_ovf` on `srem MIN, -1`; the CLIF docs, this spec, the
native backends and `runtests/div-checks.clif` say 0. See `docs/contracts/clif.md`.)

### `band`, `bor`, `bxor`, `bnot`
```
(spec (band ty x y) (provide (= result (bvand x y)) ...))   ; bor: bvor, bxor: bvxor
(spec (bnot ty x) (provide (= result (bvnot x)) ...))
```
Agree. `band_eq bor_eq bxor_eq bnot_eq`, per width `band_i* bor_i* bxor_i* bnot_i*`.

### `ishl`, `ushr`, `sshr`
```
(macro (shift_amount x y) (conv_to (widthof x)
  (bvand (zero_ext 64 y) (bvsub (int2bv 64 (widthof x)) #x0000000000000001))))
(spec (ishl ty x y) (provide ... (= result (bvshl x (shift_amount! x y)))))
(spec (ushr ty x y) (provide ... (= result (bvlshr x (shift_amount! x y)))))
(spec (sshr ty x y) (provide ... (= result (bvashr x (shift_amount! x y)))))
```
Agree: ours shifts by `y.toNat % w`. `shiftAmount_toNat`: for `w = 2^k ≤ 64` and amount
widths `v ≤ 64`, the spec's masked amount is `y mod w`. `ishl_eq ushr_eq sshr_eq` (all
`k ≤ 6`), per width `ishl_i* ushr_i* sshr_i*` (all amount widths). For i128 operands the spec
is not instantiated; our definition is the same `mod w` rule.

### `rotl`, `rotr`
```
(spec (rotl ty x y) (provide (= result (rotl x (shift_amount! x y))) ...))
(spec (rotr ty x y) (provide (= result (rotr x (shift_amount! x y))) ...))
```
Agree: `rotl_encode`/`rotr_encode` relate `BitVec.rotateLeft/Right` to the solver's
shift-or encoding; `rotl_eq rotr_eq`, per width `rotl_i* rotr_i*`.

### `clz`, `ctz`, `popcnt`
```
(spec (clz ty x) (provide (= result (clz x)) ...))
(spec (ctz ty x) (provide (= result (clz (rev x))) ...))
(spec (popcnt ty x) (provide (= result (popcnt x)) ...))
```
Agree (`clz 0 = ctz 0 = w`). Per width, bit-blasted against the encodings: `clz_i*`,
`ctz_i*` (with `rev8/16/32/64`), `popcnt_i*`.

### `icmp` (all 10 `IntCC`)
```
(spec (icmp ty cc x y) (provide (= result (if (match cc ((Equal) (= x y)) ... 
  ((UnsignedLessThanOrEqual) (bvule x y))) #x01 #x00))))
```
Agrees: `i8` 1/0. `icmp_eq` (all `cc`, all widths, against integer comparisons),
`icmp_i8 … icmp_i64`.

### `uextend`, `sextend`, `ireduce`
```
(spec (uextend ty x) (provide (= result (zero_ext (widthof result) x)) ...))
(spec (sextend ty x) (provide (= result (sign_ext (widthof result) x)) ...))
(spec (ireduce ty x) (provide (= result (conv_to (widthof result) x)) ...))
```
Agree for every instantiation of the `extend` form (8→16/32/64, 16→32/64, 32→64) and of
`ireduce` (the reverse pairs): `uextend_8_16 … uextend_32_64`, `sextend_8_16 … sextend_32_64`,
`ireduce_16_8 … ireduce_64_32`. Our `evalInst` additionally requires a strict width change
(same-width extends are rejected by the CLIF verifier) and is `stuck` otherwise.

### `load`, `uload8/16/32`, `sload8/16/32`
```
(macro (effective_address p offset) (bvadd p (sign_ext 64 offset)))
(spec (load ty flags p offset) (modifies clif_load) (modifies loaded_value)
  (provide ... (clif_load_activate! clif_load (widthof result) p offset)
               (= result (conv_to (widthof result) loaded_value))))
(macro (uloadN ...) (and (clif_load_activate! clif_load size_bits p offset)
  (= result (zero_ext (widthof result) (conv_to size_bits loaded_value)))))   ; sloadN: sign_ext
```
Agree on what the spec fixes: the effective address, the access size, and the extension.
`effAddr_eq`: our `effAddr p offset` (p + offset mod 2^64) is the spec's
`bvadd p (sign_ext 64 offset)` for `i64` pointers and `Offset32` offsets. Access sizes are
`LoadOp.size` (1/2/4 bytes or `ty.bytes`), and the result is `zeroExtend`/`signExtend` of the
bytes read. **Differences (refinements, not contradictions):** the spec abstracts memory into
one `loaded_value` and says nothing about traps or flags; ours reads little-endian bytes
from explicit allocations (big-endian with the `big` flag), traps with the flags' trap code
(default `heap_oob`) outside every allocation, and is `stuck` for `notrap` out-of-bounds,
misaligned `aligned` accesses and uninitialised bytes. Pointers of type `i32` are
zero-extended (not in the spec's instantiations, which use a 64-bit `Value`).

### `store`, `istore8/16/32`
```
(macro (clif_store_activate clif_store value p offset) (and (:active clif_store)
  (= (:size_bits clif_store) (widthof value)) (= (:addr clif_store) (effective_address! p offset))
  (= (conv_to (widthof value) (:value clif_store)) value)))
(spec (istore8 flags value p offset) ... (store! clif_store flags (extract 7 0 value) p offset result))
```
Agree: same effective address (`effAddr_eq`), size = width of the stored (truncated) value.
`store_load_1/2/4/8`: a load of the same size and address returns exactly the stored bits
(the spec's `loaded_value`/`:value` correspondence); `istore8_bits istore16_bits
istore32_bits`: `istoreN` stores `extract (N-1) 0 value`. Trap/flag differences as for loads.

### `trap`
```
(spec (trap trap_code) (modifies clif_trap) (provide clif_trap))
```
Agrees: `trap_eq` (`stepTerm _ _ _ (.trap c) = .trapped c`).

### `smin`, `smax`, `umin`, `umax` (E since `clif-subset-v2`)
```
(spec (smin ty x y) (provide (= result (if (bvsle x y) x y)) ...))   ; bv_binary_8_to_64
(spec (umin ty x y) (provide (= result (if (bvule x y) x y)) ...))
(spec (smax ty x y) (provide (= result (if (bvsge x y) x y)) ...))
(spec (umax ty x y) (provide (= result (if (bvuge x y) x y)) ...))
```
Agree: `smin_eq smax_eq umin_eq umax_eq` (all widths) and `smin_i8 … umax_i64`. Note that
`smax`/`umax` return `x` on equality, as `Sem.smax`/`Sem.umax` do (`if y ≤ x then x else y`);
the values are equal then, so the choice is unobservable.

### `bswap` (E since `clif-subset-v2`, i16/i32/i64)
```
(macro (bswap16 x) (concat (extract  7  0 x) (extract 15  8 x)))
(macro (bswap32 x) (concat (bswap16! x) (concat (extract 23 16 x) (extract 31 24 x))))
(macro (bswap64 x) (concat (bswap32! x) (concat (extract 39 32 x) ... (extract 63 56 x))))
(spec (bswap ty x) (provide (= (:bits ty) (widthof result))
  (let ((w (conv_to 64 x))) (= result (conv_to (widthof result)
    (switch (widthof x) (16 (conv_to 64 (bswap16! w))) (32 (conv_to 64 (bswap32! w)))
                        (64 (bswap64! w))))))))
(instantiate bswap ((args (named Type) (bv 16)) (ret (bv 16))) ... 32 ... 64)
```
Agrees: `bswap_i16 bswap_i32 bswap_i64` (`Spec.bswapI16/32/64` transcribe the macros with
`concat a b = a ++ b`, `extract h l = extractLsb' l (h-l+1)`, widening `conv_to 64 x` =
zero-extension; proved by `bv_decide`). `bswap.i8` is not valid CLIF (`iSwappable` =
i16..i128); `bswap.i128` has no spec instantiation and is outside E.

### Added to E without a VeriISLE spec (`clif-subset-v2`)
Checked against `inst_specs.isle` at the pin: there is **no** `(spec ...)` for `select`
(only the `(attr select_spectre_guard (tag spectre))`/`wasm_category_stack` tags), `bitrev`,
`nop` or `symbol_value`. Their semantics is defined only in `FV/Clif/Sem.lean`/`Run.lean`:

- `select c, x, y` = `if c ≠ 0 then x else y` (`Sem.select`; interpreter `step.rs`:
  `choose(arg(0).into_bool()?, arg(1), arg(2))`, `into_bool` = non-zero);
- `bitrev x` = `x.reverse` (`Sem.bitrev`; interpreter `DataValueExt::reverse_bits`);
- `nop`: no effect (interpreter `ControlFlow::Continue`);
- `symbol_value.i64 gvN` with `gvN = symbol [colocated] %s[+k]` = the link-time address of
  `%s` plus `k` (`Mem.symbols`, `Clif.Image`; the interpreter does not implement data symbols:
  `GlobalValueData::Symbol => unimplemented!()`, so this is checked against native code only).

All four are checked by the `FVTest/Clif/fixtures/e-v2-*.clif` runs (interpreter and native).

### No VeriISLE spec (not cross-read)
`stack_addr`, `jump`, `brif`, `br_table`, `return`, `call`. Their semantics is defined only
in `FV/Clif/Run.lean` (see `docs/contracts/clif.md`) and checked against the Cranelift
interpreter by the filetests.

## S opcodes with a spec (bonus)

| Opcode | Theorems | Result |
| --- | --- | --- |
| `iabs` (`if (bvsge x 0) x (bvneg x)`) | `iabs_eq`, `iabs_i*` | agrees (`iabs MIN = MIN`) |
| `bitselect` (`bvor (bvand c x) (bvand (bvnot c) y)`) | `bitselect_eq` | agrees |
| `uadd_overflow_trap` (32/64: carry bit of the 65-bit sum) | `uaddOverflowTrap_i32/_i64` | agrees (trap code is the instruction's) |
| `trapz` (`clif_trap = bv_is_zero! val`) | — | agrees by definition (`evalInst`: trap iff the value is 0) |
| `cls`, `umul_overflow`, `smul_overflow` | — | not cross-read (not in E); covered by the filetests |
