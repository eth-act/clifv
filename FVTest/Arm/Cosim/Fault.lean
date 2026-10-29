/-
Copyright (c) 2026 fv-compiler-rust contributors.
Released under Apache 2.0 license.

Co-simulation of memory faults (A3, #412, F1; `docs/plans/memfault.md`): the fault-aware step
`ArmFault.stepF` against `qemu-aarch64-static`.

The test program is the harness's (`Harness.lean`, one instruction per test) with two regions of
the data section whose pages the entry code `_fstart` protects with `mprotect`:

* the load region `flr`: pages `[ro | none | ro]`, filled with the byte pattern `faultPat`;
* the store region `fsr`: pages `[rw | none | ro | rw]`.

Every load/store form of `Specs.lean` (single register, all addressing modes, GPR and SIMD&FP,
pairs, `ldar`/`stlr`/`ldaxr`) and `stlxr` (after an `ldaxr xzr` that opens the monitor) is
generated as for the normal co-simulation, then its 64-byte buffer is moved onto a page boundary
of the region (loads: `flr`, stores: `fsr`), so that the access lies before, across or after the
boundary. A `SIGSEGV`/`SIGBUS` handler stores the signal number and `si_addr` into the result
record (offsets 768/784, unused there) and dumps the registers from the signal context (the
harness's `SIGILL` path). `_fstart` first writes a 16-byte header (the two region addresses).

The model runs `stepF (faultMap flr fsr)` from the echoed initial state, its memory holding the
pattern in the load region. A test passes when the model faults exactly when qemu signals, on a
fault `si_addr` is a forbidden byte of an event of the faulting step, and every compared field
(registers, SP, NZCV, PC, TPIDR_EL0, SIMD&FP registers, the test's buffer) agrees: on a fault the
state before the faulting instruction, else the state after it.
-/
module

public import FVTest.Arm.Cosim.Specs
public import FV.ArmFault.Step

@[expose] public section

namespace Arm.Cosim.Fault

open Arm Arm.Cosim ArmFault Concurrency Concurrency.ArmFoot Concurrency.ArmInstFoot

def pageSize : Nat := 4096

/-- The byte at offset `k` of the load region. -/
def faultPat (k : Nat) : Nat := (k * 7 + 3) % 256

/-- The model's memory map: the load region `[ro | none | ro]` at `L`, the store region
`[rw | none | ro | rw]` at `S`, everything else read-write. -/
def faultMap (L S : Nat) : MemMap := fun a =>
  let x := a.toNat
  if L ≤ x ∧ x < L + pageSize then .ro
  else if L + pageSize ≤ x ∧ x < L + 2 * pageSize then .none
  else if L + 2 * pageSize ≤ x ∧ x < L + 3 * pageSize then .ro
  else if S + pageSize ≤ x ∧ x < S + 2 * pageSize then .none
  else if S + 2 * pageSize ≤ x ∧ x < S + 3 * pageSize then .ro
  else .rw

/-- Is the form a store (its buffer goes to the store region)? -/
def isStore (name : String) : Bool := name.startsWith "st"

/-- `stlxr ws, xt, [xn]` (sizes 1, 2, 4, 8) after `ldaxr xzr, [xn]` (the monitor open), the
address aligned. -/
def stlxrSpec : Spec := ⟨"stlxr", "fault-excl", fun i => do
  let size ← bits 2
  let bytes := 2 ^ size
  let rn ← below 31
  let mut rt ← reg
  let mut rs ← below 31
  for _ in [0:1000] do
    if rs == rt || rs == rn then
      rt ← reg
      rs ← below 31
  let inst := enc [(size, 2), (0b001000, 6), (0, 1), (0, 1), (0, 1), (rs, 5), (1, 1), (31, 5),
    (rn, 5), (rt, 5)]
  let pre := enc [(size, 2), (0b001000, 6), (0, 1), (1, 1), (0, 1), (31, 5), (1, 1), (31, 5),
    (rn, 5), (31, 5)]
  let e ← below (64 - bytes + 1)
  let tc ← randomCase "stlxr" inst
  return { (tc.setReg rn (bufPlus i (e - e % bytes : Nat))) with pre := #[pre] }⟩

/-- The load/store forms of `Specs.lean` (no literal loads: they read the code) and `stlxr`. -/
def faultSpecs : List Spec :=
  (allSpecs.filter fun sp => sp.batch.startsWith "ldst-" && sp.batch != "ldst-literal") ++
    [stlxrSpec]

/-- Replace every occurrence of `pat` in `s` by `rep`. -/
def replaceAll (s pat rep : String) : String := rep.intercalate (s.splitOn pat)

/-- Move test `i`'s base register from its buffer to `X = region + boundary - t` (`t` a multiple of
16, so alignment is kept): its access `[X + e, X + e + bytes)` with `e < 64` lies before, across or
after the boundary. -/
def relocate (i : Nat) (tc : TestCase) : GenM TestCase := do
  let region := if isStore tc.name then "fsr" else "flr"
  let boundary ← pick #[pageSize, pageSize + 2048, 2 * pageSize, 3 * pageSize]
  let boundary := if region == "flr" && boundary == 3 * pageSize then pageSize else boundary
  let t := 16 * (← below 6)
  let x := s!"({region} + {boundary - t})"
  let old := bufLabel i
  return { tc with regs := tc.regs.map (replaceAll · old x), sp := replaceAll tc.sp old x }

/-- The program text: the harness's, the regions, the fault handler and `_fstart`. -/
def faultProgram (tcs : Array TestCase) : String := Id.run do
  let mut s := program tcs
  s := s ++ "  .data\n  .balign 4096\nflr:\n"
  for k in [0:3 * pageSize / 16] do
    s := s ++ "  .byte " ++ ", ".intercalate ((List.range 16).map fun j => toString (faultPat (16 * k + j))) ++ "\n"
  s := s ++ "  .balign 4096\nfsr:\n  .zero 16384\n  .balign 16\nfhdr:\n  .quad flr, fsr\n"
  s := s ++ "actsegv:\n  .quad sigsegv\n  .quad 0x48000004\n  .quad 0\n  .quad 0\n"
  s := s ++ "  .text\n  .globl _fstart\n_fstart:\n"
  -- mprotect(addr, len, prot)
  for (lbl, off, prot) in [("flr", 0, 1), ("flr", pageSize, 0), ("flr", 2 * pageSize, 1),
      ("fsr", pageSize, 0), ("fsr", 2 * pageSize, 1)] do
    s := s ++ adrl "x0" lbl ++ s!"  add x0, x0, #{off}\n  mov x1, #{pageSize}\n  mov x2, #{prot}\n" ++
      "  mov x8, #226\n  svc #0\n  cbnz x0, fail\n"
  -- rt_sigaction(SIGSEGV / SIGBUS, &actsegv, 0, 8)
  for sig in [11, 7] do
    s := s ++ s!"  mov x0, #{sig}\n" ++ adrl "x1" "actsegv" ++
      "  mov x2, #0\n  mov x3, #8\n  mov x8, #134\n  svc #0\n"
  s := s ++ adrl "x1" "fhdr" ++ "  mov x2, #16\n  bl writeall\n  b _start\n"
  -- the fault handler: x0 = signal, x1 = siginfo (si_addr at +16), x2 = ucontext
  s := s ++ "sigsegv:\n  adrp x3, cur\n  ldr x3, [x3, :lo12:cur]\n  str x0, [x3, #768]\n" ++
    "  ldr x4, [x1, #16]\n  str x4, [x3, #784]\n  b sigill\n"
  return s

def hdrSize : Nat := 16

/-- Assemble, link and run under qemu; returns the raw stdout. -/
def runFaultBatch (t : Tools) (tag : String) (tcs : Array TestCase) : IO ByteArray := do
  let base := s!"{t.workDir}/{tag}"
  IO.FS.writeFile s!"{base}.s" (faultProgram tcs)
  runCmd t.clang #["--target=aarch64-linux-gnu", "-c", s!"{base}.s", "-o", s!"{base}.o"]
  runCmd t.lld #["-flavor", "gnu", "-static", "-e", "_fstart", s!"{base}.o", "-o", base]
  let child ← IO.Process.spawn
    { cmd := t.qemu, args := #[base], stdout := .piped, stderr := .piped, stdin := .null }
  let out ← child.stdout.readBinToEnd
  let err ← child.stderr.readToEnd
  let code ← child.wait
  if code != 0 then
    throw <| IO.userError s!"qemu {base}: exit {code}\n{err}"
  let expected := hdrSize + 3 * tcs.size * recSize
  if out.size != expected then
    throw <| IO.userError s!"qemu {base}: {out.size} bytes of output, expected {expected}"
  return out

/-- The model's run: `stepF` over the instructions; the state before a faulting step, if any,
and the final state. -/
def runModel (mp : MemMap) (n : Nat) (s0 : ArmState) : Option ArmState × ArmState := Id.run do
  let mut s := s0
  let mut flt : Option ArmState := none
  for _ in [0:n] do
    if flt.isNone && r .ERR s == .None && !evsOk mp (stepEvs s) then flt := some s
    s := stepF mp s
  return (flt, s)

/-- A load that faults leaves its destination registers UNKNOWN (Arm ARM: qemu, e.g., has written
the first register of a SIMD&FP `ldp` crossing into an unmapped page); the model keeps them. The
fault check compares the model's fault state with these registers taken from qemu's: `Rt` (and
`Rt2` of a pair) of the faulting load `word`, GPR or SIMD&FP by its `V` bit. -/
def unknownDests (word : Nat) (pair : Bool) (res : ByteArray) (ro : Nat) (s : ArmState) :
    ArmState := Id.run do
  let simd := (word >>> 26) % 2 == 1
  let dests := if pair then [word % 32, (word >>> 10) % 32] else [word % 32]
  let mut s := s
  for k in dests do
    if simd then s := w (.SFP (BitVec.ofNat 5 k)) (bv128At res (ro + offV + 16 * k)) s
    else if k < 31 then s := w (.GPR (BitVec.ofNat 5 k)) (bv64At res (ro + 8 * k)) s
  return s

/-- Per test: the mismatches (empty = pass) and whether the model faulted. -/
def checkFaultBatch (tcs : Array TestCase) (out : ByteArray) :
    Array (TestCase × Array String × Bool) := Id.run do
  let n := tcs.size
  let L := u64At out 0
  let S := u64At out 8
  let mp := faultMap L S
  let mut rs := #[]
  for h : i in [0:n] do
    let tc := tcs[i]
    let o := hdrSize + i * recSize
    let ro := hdrSize + n * recSize + i * recSize
    let fo := hdrSize + 2 * n * recSize + i * recSize
    let (s0, buf) := initState out o (tc.pre.push tc.inst)
    let m0 := s0.mem
    let s0 := setMem (fun a =>
      let x := a.toNat
      if L ≤ x ∧ x < L + 3 * pageSize then BitVec.ofNat 8 (faultPat (x - L)) else m0 a) s0
    let (flt, s1) := runModel mp (tc.pre.size + 1) s0
    let signo := u64At out (ro + 768)
    let siAddr := u64At out (ro + 784)
    let mut errs := #[]
    match flt with
    | some t =>
      if signo == 0 then errs := errs.push "model faults, qemu does not"
      else
        let hit := (stepEvs t).any fun e =>
          (List.range e.n).any fun k =>
            (e.addr + BitVec.ofNat 64 k).toNat == siAddr &&
              !(mp (e.addr + BitVec.ofNat 64 k)).allows e.k.dir
        if !hit then errs := errs.push s!"si_addr {hex siAddr} not a forbidden byte of the access"
        -- a faulting load of the test instruction (the `pre` `ldaxr xzr` of `stlxr` loads nothing)
        let isLoad := tc.pre.isEmpty && (stepEvs t).any (·.k.dir == .R)
        let s1' := if isLoad then
            unknownDests tc.inst.toNat ((tc.name.splitOn "ldp").length > 1) out ro (write_err .None s1)
          else write_err .None s1
        errs := errs ++ compare tc s1' buf out ro out fo
    | none =>
      if signo != 0 then errs := errs.push s!"qemu signal {signo} at {hex siAddr}, model no fault"
      else errs := errs ++ compare tc s1 buf out ro out fo
    rs := rs.push (tc, errs, flt.isSome)
  return rs

end Arm.Cosim.Fault
