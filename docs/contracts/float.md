# Contract: IEEE 754 core (`FV/Float`, `namespace IEEE`)

Producer: S11c (#236). Consumers: the CLIF float semantics (`Clif.run`, S11b/S11c) and the Arm
FP instructions (S11d). Plan and semantics decisions: `docs/plans/floats.md` §2.

## Model

binary32 and binary64 encodings as raw bits, operated on exactly with `Nat`/`Int` and rounded
once. Lean's `Float` is not used (opaque to the kernel, `f64` only). Everything is computable
and kernel-reducible: closed-form arithmetic (`Nat.log2` reduces in the kernel) and structural
recursion on fuel (`IEEE.isqrt`), no well-founded recursion, no `partial`. Concrete cases are
checked with `decide +kernel`.

The functions transcribe the Arm ARM pseudocode (`shared/functions/float/*`) with

- **FPCR fixed to the Linux process default**: `AHP = 0`, `DN = 0` (NaN payloads propagate),
  `FZ = 0`, `FZ16 = 0` (subnormals kept, gradual underflow), `AH = 0` (`FPNeg`/`FPAbs` flip or
  clear the sign of NaNs too; `FPMax`/`FPMin` with `altfp = FALSE`);
- **the rounding mode an explicit argument** `RMode` (`rne rpi rmi rz` = `FPCR.RMode`
  `RN RP RM RZ`; `rna` = `FPRounding_TIEAWAY` for `FRINTA`/`FCVTA*`);
- **no exception flags**: `FPProcessException` (FPSR cumulative bits, trapped exceptions) is
  dropped; the results are the untrapped ones.

Types:

```lean
structure Fmt where E : Nat; F : Nat          -- width 1 + E + F
abbrev Fmt.b32 : Fmt := ⟨8, 23⟩;  abbrev Fmt.b64 : Fmt := ⟨11, 52⟩
abbrev Bits (f : Fmt) := BitVec (1 + f.E + f.F) -- defeq to BitVec 32 / BitVec 64
inductive RMode | rne | rpi | rmi | rz | rna
inductive FPType | zero | denormal | nonzero | infinity | qnan | snan
inductive Cmp | lt | eq | gt | un
```

| Lean (`IEEE.`) | ASL function (Arm ARM, `shared/functions/float/…`) | notes |
| --- | --- | --- |
| `unpack f x : FPType × Bool × Nat × Int` | `FPUnpack` / `FPUnpackBase` | `(type, sign, mant, exp)`, magnitude `mant * 2^exp`; `mant = exp = 0` for ∞/NaN |
| `zero f s`, `infinity f s`, `maxNormal f s`, `defaultNaN f` | `FPZero`, `FPInfinity`, `FPMaxNormal`, `FPDefaultNaN` | default NaN `0x7FC00000` / `0x7FF8000000000000` |
| `round f rm sign mant exp (sticky := false)` | `FPRound` / `FPRoundBase` | overflow → ∞ or max normal per mode; gradual underflow; `sticky`: value strictly between `mant` and `mant+1` units |
| `processNaN f t op`, `processNaNs f t1 t2 a b : Option`, `processNaNs3` | `FPProcessNaN`, `FPProcessNaNs`, `FPProcessNaNs3` | sNaN quietened (top fraction bit); sNaNs first, then qNaNs, operand order |
| `add`, `sub`, `mul`, `div f rm a b` | `FPAdd`, `FPSub`, `FPMul`, `FPDiv` | exact zero sum is `-0` iff `rm = rmi` |
| `sqrt f rm a` | `FPSqrt` | `sqrt(-0) = -0`, negative → default NaN |
| `mulAdd f rm addend op1 op2` | `FPMulAdd` | `addend + op1*op2`, one rounding; a qNaN addend with `0 * ∞` gives the default NaN |
| `neg f a`, `abs f a` | `FPNeg`, `FPAbs` | sign bit only |
| `max f rm a b`, `min f rm a b` | `FPMax`, `FPMin` | NaN-propagating, `max(-0,+0) = +0`, `min(-0,+0) = -0` |
| `compare f a b : Cmp` | `FPCompare` | `un` iff a NaN operand; `-0 = +0` |
| `roundInt f rm a` | `FPRoundInt` (`exact = FALSE`) | zero results keep the operand's sign |
| `convert src dst rm a` | `FPConvert`, `FPConvertNaN` | NaN: sign and top payload bits kept (truncated when narrowing), quiet bit set |
| `toFixed f a unsigned M rm : BitVec M` | `FPToFixed` (`fbits = 0`) | `SatQ` saturation; NaN → 0, ±∞ saturate |
| `fromFixed f M x unsigned rm` | `FixedToFP` (`fbits = 0`) | `0` → `+0` |
| `truncInt? f a : Option Int` | — | exact truncation toward zero; `none` for NaN/∞ (CLIF's trapping `fcvt_to_{u,s}int` range checks) |

Helpers: `isNaN isSNaN isQNaN isInf isZero typeOf signOf expOf fracOf pack`, `roundToInt rm v
exp` (the `RoundDown` + increment step of `FPRoundInt`/`FPToFixed`), `satQ`, `isqrt`.

Arm instructions map to these with the operand order of the ASL (`FMADD d = a + n*m` is
`mulAdd a n m`; `FMSUB`/`FNMADD`/`FNMSUB` negate operands with `neg` first). CLIF operations
use `rm = .rne` (`docs/plans/floats.md` §2).

## Trust: FloatLib as the spec of record

FV/Float stays core-only (the Arm ARM transcription above, kernel-reducible). The leaf package
`float-spec/` (library `FVFloatSpec`, built and audited by `scripts/float-spec.sh`, part of the
main gate) proves it equal to [FloatLib](https://github.com/lean-dojo/FloatLib) (@1f5771b)'s IEEE 754 model: 84 theorems,
for every input and every FPCR rounding mode, generic over formats with `E ≥ 2`, `F ≥ 1` with
b32/b64 corollaries; `#print axioms` (`float-spec/audit.lean`) shows only `propext`,
`Classical.choice`, `Quot.sound`.

- Exactly FloatLib's operation, NaNs included: `add_eq`, `mul_eq`, `div_eq`, `sqrt_eq`,
  `max_eq`, `min_eq`, `compare_eq`, `neg_eq`, `abs_eq`.
- FloatLib's operation plus an Arm NaN wrapper (`FPProcessNaNs`, `FPCR.DN = 0`), with
  `*_of_not_nan` corollaries for exact equality on non-NaN operands: `sub_eq` (FloatLib flips the
  sign of the second operand's NaN), `mulAdd_eq` (Arm's NaN operand order and the qNaN addend
  with `0·∞` rule), `convert_eq` (payloads differ by design; `convert_isNaN`).
- Conversions and rounding: `roundInt_eq` (FloatLib `roundToIntegral`, needs `F ≤ bias`),
  `fromFixed_eq`, `toFixed_eq` (FloatLib integer rounding, Arm `SatQ` saturation),
  `truncInt?_eq`, `roundToInt_eq`, `round_eq` (`FPRound` = `roundDyadicWithRounding`),
  `round_sticky`.

Exceptions (Arm-pseudocode-only, not tied to FloatLib): the ties-away mode `rna` (`FRINTA`,
`FCVTA*`; FloatLib has no ties-away operation); `convert` between formats with equal exponent
width (unused). FloatLib proves real-valued correctness only for round-to-nearest-even (in
directed modes the bridge still holds, against FloatLib's executable operations;
`roundToIntegral` has full theorems in every mode).

## Validation

- **Kernel witnesses** `FVTest/Float/Witness.lean` (`decide +kernel`): `1+2 = 3` (b32, b64),
  `0.1+0.2 = 0x3FD3333333333334`, signed zero sums under `rne`/`rmi`, `∞-∞` = default NaN, sNaN
  quietening and NaN operand priority, invalid `0*∞`, `0/0`, `sqrt(-1)`, overflow per mode,
  subnormal results and ties, `1/3`, `sqrt 2`, fused vs unfused multiply-add, `FPMulAdd`'s qNaN
  addend rule, min/max of signed zeros, compare, `roundInt` ties under all modes, `f64↔f32`
  rounding and NaN payloads, `toFixed` saturation/NaN, `fromFixed (2^64-1)`.
- **Differential test** `scripts/float-difftest.sh [--aarch64] [--count N] [--seed S]`:
  `float-difftest` (`FVTest/Float/DiffTest.lean`) generates edge-biased cases (±0, smallest and
  largest subnormals/normals, ±∞, qNaN/sNaN with payloads, values near 1, integers and
  half-integers, values near 2^31/2^32/2^63/2^64, cancelling operands and sum ties, binary64
  values on binary32 rounding boundaries, fma addends cancelling the product) and
  `rust/crates/float-oracle` recomputes them with Rust `f32`/`f64` (`+ - * /`, `sqrt`,
  `mul_add`, `partial_cmp`, `round_ties_even`/`ceil`/`floor`/`trunc`/`round`, saturating
  `as` casts). Arithmetic, `sqrt`, `fma` and `f64↔f32` cycle through `rne rpi rmi rz` (set in
  MXCSR / FPCR around the operation), `rint` and `tofix` through all five modes, `fromfix`
  is `rne`. 34 classes: `{add,sub,mul,div,sqrt,fma,cmp,rint}.{32,64}`, `cvt.64.32`,
  `cvt.32.64`, `tofix.{32,64}.{i32,u32,i64,u64}`, `fromfix.{i32,u32,i64,u64}.{32,64}`.
  Results are compared bit-for-bit; on x86-64 two NaN results agree regardless of payload
  (x86 NaN rules differ). `--aarch64` cross-compiles the oracle for
  `aarch64-unknown-linux-musl` (linked with `rust-lld`) and runs it under
  `qemu-aarch64-static`, comparing NaNs bit-for-bit as well.

Results (2026-10-16, 100000 cases per class, 3.4M cases per run):

| run | mismatches |
| --- | --- |
| x86-64 host, seed 1 and seed 7 | 0 / 3400000 each |
| aarch64 qemu `--exact-nan`, seed 1 and seed 7 | 0 / 3400000 each (NaN payloads bit-exact) |

Not covered by the differential test: `max`/`min` (Rust's `f32::max` is not `FPMax`;
witnesses only; the Arm co-simulation of `FMAX`/`FMIN` checks them), `rna` for arithmetic
(no FPCR encoding), `toFixed`/`fromFixed` with `fbits ≠ 0` (not modelled).
