/-
Copyright (c) 2026 fv-compiler-rust contributors.
Released under Apache 2.0 license.

Co-simulation harness: the `FV.Arm` model against `qemu-aarch64-static`.

A test case is one instruction word plus an initial machine state (x0–x30, SP, NZCV, v0–v30,
TPIDR_EL0 and a 64-byte data buffer). FPCR is 0 (Linux's initial value, checked at `_start` and
rewritten before every test): the model fixes FPCR = 0. A batch of test cases becomes one
freestanding aarch64 program:

* The data section holds one *init record* per test (layout below). Register values are
  assembler expressions, so a base register can point into the test's own buffer
  (`buf_i + delta`) and a branch-target register can hold a landing-pad address.
* `_start` installs a `SIGILL` handler (for `udf`), writes all init records to stdout, then runs
  each test: load v0–v30, NZCV, TPIDR_EL0, SP, x0–x30 from the record, execute the instruction at
  `ins_i`. Control then reaches a landing pad `pad_i_j = ins_i + 4j` (fall-through is `j = 1`;
  branch tests get pads on both sides), whose handler stashes x0 in the low half of v31 and the
  pad address in its upper half and jumps to `dump`, which stores x0–x30, SP, NZCV, PC(= pad
  address), TPIDR_EL0 and v0–v30 into the test's *result record*. A `udf` test reaches the
  `SIGILL` handler instead, which copies the same fields from the signal frame's `ucontext`
  (TPIDR_EL0, which signal delivery keeps, from the register).
* Finally the program writes all result records, then the init records again (whose buffers now
  hold the memory after each test), and exits.

The harness itself uses only v31 as scratch, so test instructions may use any of x0–x30, SP,
NZCV, TPIDR_EL0 and v0–v30.

Lean then rebuilds each initial state from the echoed init record (so label-valued registers are
the linked addresses), runs `Arm.stepi` once, and compares every field.
-/
module

public import FV.Arm.Exec

@[expose] public section

namespace Arm.Cosim

open Arm

/-! ## Random numbers (xorshift64*) -/

structure Rng where
  s : UInt64

abbrev GenM := StateM Rng

def next64 : GenM UInt64 := modifyGet fun (g : Rng) =>
  let x : UInt64 := g.s
  let x : UInt64 := x ^^^ (x >>> 12)
  let x : UInt64 := x ^^^ (x <<< 25)
  let x : UInt64 := x ^^^ (x >>> 27)
  ((x * 0x2545F4914F6CDD1D : UInt64), (⟨x⟩ : Rng))

/-- Uniform in `[0, n)` (`n > 0`). -/
def below (n : Nat) : GenM Nat := do return (← next64).toNat % n

/-- Uniform `n`-bit value. -/
def bits (n : Nat) : GenM Nat := do return (← next64).toNat % (2 ^ n)

def coin : GenM Bool := do return (← below 2) == 1

def pick {α} [Inhabited α] (xs : Array α) : GenM α := do return xs[← below xs.size]!

def interesting : Array UInt64 :=
  #[0, 1, 2, 0xFFFFFFFFFFFFFFFF, 0x7FFFFFFFFFFFFFFF, 0x8000000000000000, 0x7FFFFFFF,
    0x80000000, 0xFFFFFFFF, 0xFF, 0x80, 0x7F, 0xFFFF, 0x8000, 0x100000000, 0xFFFFFFFF80000000,
    0xFFFFFFFE, 0xFFFFFFFFFFFFFF80, 0xFFFFFFFFFFFF8000, 0x3F, 0x40, 0x1F, 0x20]

/-- A 64-bit value biased towards edge cases. -/
def randVal : GenM UInt64 := do
  match ← below 8 with
  | 0 | 1 => pick interesting
  | 2 => return (← bits 8).toUInt64
  | 3 => return 0 - (← bits 8).toUInt64
  | 4 => return (← bits 32).toUInt64
  | 5 => let v := (← bits 32).toUInt64
         return if v >= 0x80000000 then v ||| 0xFFFFFFFF00000000 else v
  | _ => next64

/-! ## IEEE 754 edge values (binary32 `E = 8, F = 23`; binary64 `E = 11, F = 52`) -/

/-- binary32 edge values: ±0, ±min/max subnormal, ±min normal, ±1, ±max finite, ±∞, quiet and
signalling NaNs with payloads, powers of two at the integer-conversion bounds, and values whose
sums/products/roundings are ties. -/
def fp32Edge : Array Nat :=
  #[0x00000000, 0x80000000, 0x00000001, 0x80000001, 0x007FFFFF, 0x807FFFFF, 0x00800000,
    0x80800000, 0x00400000, 0x3F800000, 0xBF800000, 0x7F7FFFFF, 0xFF7FFFFF, 0x7F800000,
    0xFF800000, 0x7FC00000, 0xFFC00000, 0x7FC00001, 0x7FFFFFFF, 0xFFD23456, 0x7F800001,
    0xFF800001, 0x7FA00000, 0x7FBFFFFF, 0xFF9ABCDE, 0x3F000000, 0xBF000000, 0x3FC00000,
    0x40200000, 0xC0200000, 0x40000000, 0x40400000, 0x4B000000, 0x4B000001, 0x4B800000,
    0x4B7FFFFF, 0x34000000, 0x33800000, 0x33000000, 0x4EFFFFFF, 0x4F000000, 0x4F800000,
    0xCF000000, 0xCF000001, 0x5EFFFFFF, 0x5F000000, 0x5F800000, 0xDF000000, 0x3EFFFFFF,
    0x3F7FFFFF, 0xBF7FFFFF, 0x3EAAAAAB, 0x40490FDB, 0x7F000000, 0x1F800000, 0x5F7FFFFF,
    0x3F800001, 0x3FFFFFFF, 0x4F7FFFFF, 0xBF800001]

/-- binary64 edge values (as `fp32Edge`). -/
def fp64Edge : Array Nat :=
  #[0x0000000000000000, 0x8000000000000000, 0x0000000000000001, 0x8000000000000001,
    0x000FFFFFFFFFFFFF, 0x800FFFFFFFFFFFFF, 0x0010000000000000, 0x8010000000000000,
    0x0008000000000000, 0x3FF0000000000000, 0xBFF0000000000000, 0x7FEFFFFFFFFFFFFF,
    0xFFEFFFFFFFFFFFFF, 0x7FF0000000000000, 0xFFF0000000000000, 0x7FF8000000000000,
    0xFFF8000000000000, 0x7FF8000000000001, 0x7FFFFFFFFFFFFFFF, 0xFFFA5A5A5A5A5A5A,
    0x7FF0000000000001, 0xFFF0000000000001, 0x7FF4000000000000, 0x7FF7FFFFFFFFFFFF,
    0xFFF123456789ABCD, 0x3FE0000000000000, 0xBFE0000000000000, 0x3FF8000000000000,
    0x4004000000000000, 0xC004000000000000, 0x4000000000000000, 0x4008000000000000,
    0x4330000000000000, 0x4330000000000001, 0x4340000000000000, 0x433FFFFFFFFFFFFF,
    0x3CB0000000000000, 0x3CA0000000000000, 0x41DFFFFFFFC00000, 0x41DFFFFFFFFFFFFF,
    0x41E0000000000000, 0x41EFFFFFFFFFFFFF, 0x41F0000000000000, 0xC1E0000000000000,
    0xC1E0000000200000, 0x43DFFFFFFFFFFFFF, 0x43E0000000000000, 0x43F0000000000000,
    0xC3E0000000000000, 0x3FDFFFFFFFFFFFFF, 0x3FEFFFFFFFFFFFFF, 0x3FD5555555555555,
    0x400921FB54442D18, 0x7FE0000000000000, 0x1FF0000000000000, 0x47EFFFFFE0000000,
    0x47EFFFFFF0000000, 0x36A0000000000000, 0x3690000000000000, 0x3FF0000000000001,
    0x381FFFFFE0000000, 0x3810000000000000, 0xBFF0000000000001]

/-- An `(E, F)` float with sign `s`, biased exponent `e` and fraction `f`. -/
def fpBits (E F s e f : Nat) : Nat := (s <<< (E + F)) ||| ((e % 2 ^ E) <<< F) ||| (f % 2 ^ F)

/-- A random `(E, F)` float (as bits), biased towards IEEE edge cases: edge values, random bits,
exact small integers, values near 1 (whose sums and products round, often to ties), short
fractions (exact ties after one operation), subnormals, and exponents near the overflow and
underflow thresholds. -/
def randFp (E F : Nat) : GenM Nat := do
  let bias := 2 ^ (E - 1) - 1
  let s ← bits 1
  match ← below 10 with
  | 0 | 1 | 2 => pick (if E == 8 then fp32Edge else fp64Edge)
  | 3 => bits (1 + E + F)
  | 4 =>
    -- an exact integer `k < 2^(F+1)` (or a few bits above), as the float `±k`
    let k ← bits (← below (F + 4))
    if k == 0 then return fpBits E F s 0 0
    let e := Nat.log2 k
    if e ≤ F then return fpBits E F s (bias + e) ((k - 2 ^ e) <<< (F - e))
    else return fpBits E F s (bias + e) ((k - 2 ^ e) >>> (e - F))
  | 5 => return fpBits E F s (bias - 8 + (← below 17)) (← bits F)
  | 6 =>
    -- a short fraction: a few significant bits, the rest zero
    let nb ← below 6
    return fpBits E F s (bias - 30 + (← below 61)) ((← bits nb) <<< (F - nb))
  | 7 => return fpBits E F s 0 (← bits (← below (F + 1)))
  | 8 => return fpBits E F s (2 ^ E - 2 - (← below 4)) (← bits F)
  | _ => return fpBits E F s (1 + (← below 4)) (← bits F)

/-! ## Test cases -/

inductive Kind where
  /-- Execution falls through to the next instruction. -/
  | normal
  /-- May branch: landing pads cover `ins_i + 4j` for `-padK ≤ j ≤ padK`, `j ≠ 0`. -/
  | branch
  /-- Raises `SIGILL` (`udf`). -/
  | udf
deriving BEq, Repr

/-- Number of landing pads on each side of a branch test's instruction. -/
def padK : Nat := 32

structure TestCase where
  /-- Mnemonic/form counted in the report (e.g. `"adds (imm)"`). -/
  name : String
  inst : UInt32
  kind : Kind := .normal
  /-- TPIDR_EL0 (the thread pointer). -/
  tpidr : UInt64 := 0
  /-- Assembler expressions for x0..x30 (31 entries). -/
  regs : Array String
  sp : String
  /-- NZCV as a 4-bit value `N:Z:C:V`. -/
  nzcv : Nat
  /-- v0..v30 as `(lo, hi)` 64-bit halves (31 entries). -/
  simd : Array (UInt64 × UInt64)
  /-- Initial contents of the 64-byte buffer `buf_i`. -/
  buf : Array UInt8
  /-- Literal pools (for `ldr (literal)`): `buf`'s bytes are also placed in the code, at
  `ins_i - 64` (before the instruction) and at `ins_i + 8` (after its landing pad). -/
  pool : Bool := false
  /-- Instructions run (by qemu and by the model) right before `inst`, e.g. the `ldaxr` that
  opens the exclusive monitor a `stlxr` needs. Only for `.normal` cases without `pool`. -/
  pre : Array UInt32 := #[]

def hex (n : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

def lit (v : UInt64) : String := hex v.toNat

/-- Label names for test `i`. -/
def bufLabel (i : Nat) : String := s!"buf_{i}"
def insLabel (i : Nat) : String := s!"ins_{i}"
def padLabel (i : Nat) (j : Int) : String :=
  if j < 0 then s!"pad_{i}_m{j.natAbs}" else s!"pad_{i}_{j.toNat}"

/-- `buf_i + delta` (delta a signed byte offset). -/
def bufPlus (i : Nat) (delta : Int) : String :=
  if delta < 0 then s!"({bufLabel i} - {delta.natAbs})" else s!"({bufLabel i} + {delta.toNat})"

/-- A test case with random registers, flags, SIMD registers and buffer. -/
def randomCase (name : String) (inst : UInt32) : GenM TestCase := do
  let mut regs := #[]
  for _ in [0:31] do regs := regs.push (lit (← randVal))
  let sp := lit (← randVal)
  let tpidr ← randVal
  let nzcv ← bits 4
  let mut simd := #[]
  for _ in [0:31] do simd := simd.push ((← randVal), (← randVal))
  let mut buf := #[]
  for _ in [0:64] do buf := buf.push (← bits 8).toUInt8
  return { name, inst, regs, sp, nzcv, simd, buf, tpidr }

/-- A random float of `dbl ? binary64 : binary32` in the low bits of a 128-bit register value
(the other bits random). -/
def randFpReg (dbl : Bool) : GenM (UInt64 × UInt64) := do
  let lo ← if dbl then do pure (← randFp 11 52).toUInt64
    else do pure (((← next64) &&& 0xFFFFFFFF00000000) ||| (← randFp 8 23).toUInt64)
  return (lo, ← next64)

/-- `randomCase` with IEEE floats (binary64 if `dbl`, else binary32) in v0–v30. -/
def randomFpCase (name : String) (dbl : Bool) (inst : UInt32) : GenM TestCase := do
  let tc ← randomCase name inst
  let mut simd := #[]
  for _ in [0:31] do simd := simd.push (← randFpReg dbl)
  return { tc with simd }

def TestCase.setReg (tc : TestCase) (r : Nat) (e : String) : TestCase :=
  if r < 31 then { tc with regs := tc.regs.set! r e } else { tc with sp := e }

/-! ## Record layout (bytes) -/

def offSP : Nat := 248
def offNZCV : Nat := 256
def offPC : Nat := 264
def offV : Nat := 272
def offBufAddr : Nat := 768
def offTPIDR : Nat := 776
def offBuf : Nat := 784
def recSize : Nat := 848

/-! ## Assembly generation -/

def emitInit (i : Nat) (tc : TestCase) : String := Id.run do
  let mut s := s!"  .balign 16\nrin_{i}:\n"
  for e in tc.regs do s := s ++ s!"  .quad {e}\n"
  let start := if tc.pre.isEmpty then insLabel i else s!"pre_{i}"
  s := s ++ s!"  .quad {tc.sp}\n  .quad {hex (tc.nzcv <<< 28)}\n  .quad {start}\n"
  for (lo, hi) in tc.simd do s := s ++ s!"  .quad {lit lo}, {lit hi}\n"
  s := s ++ s!"  .quad {bufLabel i}\n  .quad {lit tc.tpidr}\n{bufLabel i}:\n"
  s := s ++ "  .byte " ++ ", ".intercalate (tc.buf.toList.map (fun b => toString b.toNat)) ++ "\n"
  return s

def adrl (reg lbl : String) : String :=
  s!"  adrp {reg}, {lbl}\n  add {reg}, {reg}, :lo12:{lbl}\n"

def emitCode (i : Nat) (tc : TestCase) (next : String) : String := Id.run do
  let mut s := s!"tst_{i}:\n"
  -- cur = { result record, continuation }
  s := s ++ adrl "x0" "cur" ++ adrl "x1" s!"rout_{i}" ++ "  str x1, [x0]\n" ++ adrl "x1" next ++
    "  str x1, [x0, #8]\n"
  s := s ++ "  msr fpcr, xzr\n"
  s := s ++ adrl "x30" s!"rin_{i}"
  for k in [0:15] do
    s := s ++ s!"  ldp q{2*k}, q{2*k+1}, [x30, #{offV + 32*k}]\n"
  s := s ++ s!"  ldr q30, [x30, #{offV + 16*30}]\n"
  s := s ++ s!"  ldr x0, [x30, #{offNZCV}]\n  msr nzcv, x0\n  ldr x0, [x30, #{offTPIDR}]\n" ++
    s!"  msr tpidr_el0, x0\n  ldr x0, [x30, #{offSP}]\n  mov sp, x0\n"
  for k in [0:15] do
    s := s ++ s!"  ldp x{2*k}, x{2*k+1}, [x30, #{16*k}]\n"
  s := s ++ "  ldr x30, [x30, #240]\n"
  let (back, fwd) := match tc.kind with
    | .branch => (padK, padK)
    | .normal => (0, 1)
    | .udf => (0, 0)
  if back > 0 then
    s := s ++ s!"  b {insLabel i}\n"
    for m in [0:back] do
      let j : Int := (m : Int) - back
      s := s ++ s!"{padLabel i j}:\n  b hnd_{padLabel i j}\n"
  let poolBytes := "  .byte " ++ ", ".intercalate (tc.buf.toList.map (fun b => toString b.toNat)) ++ "\n"
  if tc.pool then s := s ++ s!"  b {insLabel i}\n" ++ poolBytes
  if !tc.pre.isEmpty then
    s := s ++ s!"pre_{i}:\n"
    for p in tc.pre do s := s ++ s!"  .inst {hex p.toNat}\n"
  s := s ++ s!"{insLabel i}:\n  .inst {hex tc.inst.toNat}\n"
  for m in [0:fwd] do
    let j : Int := m + 1
    s := s ++ s!"{padLabel i j}:\n  b hnd_{padLabel i j}\n"
  if tc.pool then s := s ++ poolBytes
  let pads : List Int :=
    (List.range back).map (fun (m : Nat) => (m : Int) - (back : Int)) ++
      (List.range fwd).map (fun (m : Nat) => (m : Int) + 1)
  for j in pads do
    s := s ++ s!"hnd_{padLabel i j}:\n  fmov d31, x0\n" ++ adrl "x0" (padLabel i j) ++
      "  mov v31.d[1], x0\n  b dump\n"
  return s

/-- Fixed program text: entry, dump routine, SIGILL handler, write loop. -/
def prelude : String := Id.run do
  let mut s := "  .text\n  .globl _start\n_start:\n"
  -- FPCR must be 0 (the model's fixed FPCR): exit 3 otherwise
  s := s ++ "  mrs x0, fpcr\n  cbnz x0, fail\n"
  -- sigaltstack(&ss, 0)
  s := s ++ adrl "x0" "ss" ++ "  mov x1, #0\n  mov x8, #132\n  svc #0\n"
  -- rt_sigaction(SIGILL, &act, 0, 8)
  s := s ++ "  mov x0, #4\n" ++ adrl "x1" "act" ++ "  mov x2, #0\n  mov x3, #8\n  mov x8, #134\n  svc #0\n"
  s := s ++ adrl "x1" "initbeg" ++ adrl "x2" "initend" ++ "  sub x2, x2, x1\n  bl writeall\n"
  s := s ++ "  b tst_0\n"
  s := s ++ "finish:\n" ++ adrl "x1" "resbeg" ++ adrl "x2" "resend" ++ "  sub x2, x2, x1\n  bl writeall\n"
  s := s ++ adrl "x1" "initbeg" ++ adrl "x2" "initend" ++ "  sub x2, x2, x1\n  bl writeall\n"
  s := s ++ "  mov x0, #0\n  mov x8, #93\n  svc #0\n"
  s := s ++ "fail:\n  mov x0, #3\n  mov x8, #93\n  svc #0\n"
  -- writeall(x1 = buf, x2 = len)
  s := s ++ "writeall:\n  cbz x2, 2f\n1:\n  mov x0, #1\n  mov x8, #64\n  svc #0\n  cmp x0, #0\n" ++
    "  b.le fail\n  add x1, x1, x0\n  subs x2, x2, x0\n  b.ne 1b\n2:\n  ret\n"
  -- dump: x0 in v31.d[0], pad address in v31.d[1]
  s := s ++ "dump:\n  adrp x0, cur\n  ldr x0, [x0, :lo12:cur]\n  str x1, [x0, #8]\n"
  for k in [1:15] do
    s := s ++ s!"  stp x{2*k}, x{2*k+1}, [x0, #{16*k}]\n"
  s := s ++ "  str x30, [x0, #240]\n  fmov x1, d31\n  str x1, [x0]\n"
  s := s ++ s!"  mov x1, sp\n  str x1, [x0, #{offSP}]\n  mrs x1, nzcv\n  str x1, [x0, #{offNZCV}]\n"
  s := s ++ s!"  mov x1, v31.d[1]\n  str x1, [x0, #{offPC}]\n"
  s := s ++ s!"  mrs x1, tpidr_el0\n  str x1, [x0, #{offTPIDR}]\n"
  for k in [0:15] do
    s := s ++ s!"  stp q{2*k}, q{2*k+1}, [x0, #{offV + 32*k}]\n"
  s := s ++ s!"  str q30, [x0, #{offV + 16*30}]\n"
  s := s ++ "  adrp x1, cur\n  add x1, x1, :lo12:cur\n  ldr x1, [x1, #8]\n  br x1\n"
  -- SIGILL handler: x2 = ucontext. mcontext at +176: fault_address, regs[31] (+184), sp (+432),
  -- pc (+440), pstate (+448); fpsimd_context at +464 with vregs at +480.
  s := s ++ "sigill:\n  adrp x0, cur\n  ldr x0, [x0, :lo12:cur]\n"
  for k in [0:31] do
    s := s ++ s!"  ldr x3, [x2, #{184 + 8*k}]\n  str x3, [x0, #{8*k}]\n"
  s := s ++ s!"  ldr x3, [x2, #432]\n  str x3, [x0, #{offSP}]\n"
  s := s ++ s!"  ldr x3, [x2, #448]\n  and x3, x3, #0xf0000000\n  str x3, [x0, #{offNZCV}]\n"
  s := s ++ s!"  ldr x3, [x2, #440]\n  str x3, [x0, #{offPC}]\n"
  s := s ++ s!"  mrs x3, tpidr_el0\n  str x3, [x0, #{offTPIDR}]\n"
  for k in [0:31] do
    s := s ++ s!"  ldr q3, [x2, #{480 + 16*k}]\n  str q3, [x0, #{offV + 16*k}]\n"
  s := s ++ "  adrp x1, cur\n  add x1, x1, :lo12:cur\n  ldr x1, [x1, #8]\n  br x1\n"
  return s

def dataPrelude : String :=
  "  .data\n  .balign 16\ncur:\n  .quad 0, 0\nact:\n  .quad sigill\n  .quad 0x48000004\n" ++
  "  .quad 0\n  .quad 0\nss:\n  .quad altstack\n  .word 0, 0\n  .quad 65536\n"

def program (tcs : Array TestCase) : String := Id.run do
  let mut s := prelude
  for h : i in [0:tcs.size] do
    let next := if i + 1 < tcs.size then s!"tst_{i+1}" else "finish"
    s := s ++ emitCode i tcs[i] next
  s := s ++ dataPrelude ++ "  .balign 16\ninitbeg:\n"
  for h : i in [0:tcs.size] do
    s := s ++ emitInit i tcs[i]
  s := s ++ "  .balign 16\ninitend:\n  .bss\n  .balign 16\naltstack:\n  .zero 65536\n  .balign 16\nresbeg:\n"
  for i in [0:tcs.size] do
    s := s ++ s!"rout_{i}:\n  .zero {recSize}\n"
  s := s ++ "resend:\n"
  return s

/-! ## Model side -/

def u64At (b : ByteArray) (o : Nat) : Nat := Id.run do
  let mut v := 0
  for k in [0:8] do v := v + (b.get! (o + k)).toNat <<< (8 * k)
  return v

def bv64At (b : ByteArray) (o : Nat) : BitVec 64 := BitVec.ofNat 64 (u64At b o)

def bv128At (b : ByteArray) (o : Nat) : BitVec 128 := bv64At b (o + 8) ++ bv64At b o

/-- The initial model state for the record at offset `o` of `b`, and the buffer's address: the
program is `insts` from the recorded PC on. -/
def initState (b : ByteArray) (o : Nat) (insts : Array UInt32) : ArmState × BitVec 64 := Id.run do
  let pc := bv64At b (o + offPC)
  let mut s := set_program ArmState.default <| insts.toList.zipIdx.map fun (ins, k) =>
    (pc + BitVec.ofNat 64 (4 * k), BitVec.ofNat 32 ins.toNat)
  for k in [0:31] do
    s := w (.GPR (BitVec.ofNat 5 k)) (bv64At b (o + 8 * k)) s
  s := w (.GPR 31#5) (bv64At b (o + offSP)) s
  let nzcv := u64At b (o + offNZCV)
  s := w (.FLAG .N) (BitVec.ofNat 1 (nzcv >>> 31)) s
  s := w (.FLAG .Z) (BitVec.ofNat 1 (nzcv >>> 30)) s
  s := w (.FLAG .C) (BitVec.ofNat 1 (nzcv >>> 29)) s
  s := w (.FLAG .V) (BitVec.ofNat 1 (nzcv >>> 28)) s
  for k in [0:31] do
    s := w (.SFP (BitVec.ofNat 5 k)) (bv128At b (o + offV + 16 * k)) s
  s := w .PC pc s
  s := w .TPIDR (bv64At b (o + offTPIDR)) s
  let buf := bv64At b (o + offBufAddr)
  for k in [0:64] do
    s := write_mem (buf + BitVec.ofNat 64 k) (BitVec.ofNat 8 (b.get! (o + offBuf + k)).toNat) s
  return (s, buf)

/-- Compare the model's final state with the observed result record; returns mismatches. -/
def compare (tc : TestCase) (s : ArmState) (bufAddr : BitVec 64)
    (res : ByteArray) (ro : Nat) (fin : ByteArray) (fo : Nat) : Array String := Id.run do
  let mut errs := #[]
  let expErr : StateError :=
    if tc.kind == .udf then .Trap (BitVec.ofNat 16 (tc.inst.toNat % 65536)) else .None
  if r .ERR s != expErr then
    errs := errs.push s!"model error {repr (r .ERR s)}"
    return errs
  for k in [0:31] do
    let m := r (.GPR (BitVec.ofNat 5 k)) s
    let q := bv64At res (ro + 8 * k)
    if m != q then errs := errs.push s!"x{k}: model {m.toHex} qemu {q.toHex}"
  let msp := r (.GPR 31#5) s
  let qsp := bv64At res (ro + offSP)
  if msp != qsp then errs := errs.push s!"sp: model {msp.toHex} qemu {qsp.toHex}"
  let mn := ((r (.FLAG .N) s).toNat <<< 3) ||| ((r (.FLAG .Z) s).toNat <<< 2) |||
    ((r (.FLAG .C) s).toNat <<< 1) ||| (r (.FLAG .V) s).toNat
  let qn := u64At res (ro + offNZCV) >>> 28
  if mn != qn then errs := errs.push s!"nzcv: model {mn} qemu {qn}"
  let mpc := r .PC s
  let qpc := bv64At res (ro + offPC)
  if mpc != qpc then errs := errs.push s!"pc: model {mpc.toHex} qemu {qpc.toHex}"
  let mtp := r .TPIDR s
  let qtp := bv64At res (ro + offTPIDR)
  if mtp != qtp then errs := errs.push s!"tpidr_el0: model {mtp.toHex} qemu {qtp.toHex}"
  for k in [0:31] do
    let m := r (.SFP (BitVec.ofNat 5 k)) s
    let q := bv128At res (ro + offV + 16 * k)
    if m != q then errs := errs.push s!"v{k}: model {m.toHex} qemu {q.toHex}"
  for k in [0:64] do
    let m := read_mem (bufAddr + BitVec.ofNat 64 k) s
    let q := BitVec.ofNat 8 (fin.get! (fo + offBuf + k)).toNat
    if m != q then errs := errs.push s!"buf[{k}]: model {m.toHex} qemu {q.toHex}"
  return errs

/-! ## Running a batch -/

structure Tools where
  clang : String
  lld : String
  qemu : String
  workDir : String

def runCmd (cmd : String) (args : Array String) : IO Unit := do
  let out ← IO.Process.output { cmd, args }
  if out.exitCode != 0 then
    throw <| IO.userError s!"{cmd} {args}: exit {out.exitCode}\n{out.stderr}"

/-- Assemble, link and run a batch under qemu; returns the raw stdout. -/
def runBatch (t : Tools) (tag : String) (tcs : Array TestCase) : IO ByteArray := do
  let base := s!"{t.workDir}/{tag}"
  IO.FS.writeFile s!"{base}.s" (program tcs)
  runCmd t.clang #["--target=aarch64-linux-gnu", "-c", s!"{base}.s", "-o", s!"{base}.o"]
  runCmd t.lld #["-flavor", "gnu", "-static", "-e", "_start", s!"{base}.o", "-o", base]
  let child ← IO.Process.spawn
    { cmd := t.qemu, args := #[base], stdout := .piped, stderr := .piped, stdin := .null }
  let out ← child.stdout.readBinToEnd
  let err ← child.stderr.readToEnd
  let code ← child.wait
  if code != 0 then
    throw <| IO.userError s!"qemu {base}: exit {code}\n{err}"
  let expected := 3 * tcs.size * recSize
  if out.size != expected then
    throw <| IO.userError s!"qemu {base}: {out.size} bytes of output, expected {expected}"
  return out

/-- Per-test outcome: the list of mismatches (empty = pass). -/
def checkBatch (tcs : Array TestCase) (out : ByteArray) : Array (TestCase × Array String) :=
  Id.run do
    let n := tcs.size
    let mut rs := #[]
    for h : i in [0:n] do
      let tc := tcs[i]
      let o := i * recSize
      let (s0, buf) := initState out o (tc.pre.push tc.inst)
      -- the literal pools (`TestCase.pool`) are code bytes: at `pc - 64` and `pc + 8`
      let s0 := if !tc.pool then s0 else Id.run do
        let pc := r .PC s0
        let mut s := s0
        for k in [0:64] do
          let b := BitVec.ofNat 8 (tc.buf[k]!).toNat
          s := write_mem (pc - 64#64 + BitVec.ofNat 64 k) b s
          s := write_mem (pc + 8#64 + BitVec.ofNat 64 k) b s
        return s
      let s1 := (List.range (tc.pre.size + 1)).foldl (fun s _ => stepi s) s0
      rs := rs.push (tc, compare tc s1 buf out (n * recSize + o) out (2 * n * recSize + o))
    return rs

end Arm.Cosim
