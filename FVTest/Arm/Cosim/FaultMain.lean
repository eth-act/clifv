/-
Copyright (c) 2026 fv-compiler-rust contributors.
Released under Apache 2.0 license.

`lake exe arm-fault-cosim [--n N] [--seed S] [--only SUBSTR] [--workdir DIR] [--show K]`: the
fault co-simulation of `Fault.lean` (`ArmFault.stepF` against `qemu-aarch64-static`). Tools as
for `arm-cosim` (`ARM_COSIM_CLANG`, `ARM_COSIM_LLD`, `ARM_COSIM_QEMU`;
`scripts/arm-fault-cosim.sh` sets them up). Prints one line per form (vectors, faults, failures)
and the total; exits 1 if any vector fails.
-/
module

public import FVTest.Arm.Cosim.Fault

@[expose] public section

open Arm.Cosim Arm.Cosim.Fault

structure Opts where
  n : Nat := 100
  seed : Nat := 0xfa17
  only : Option String := none
  workDir : String := ".lake/arm-fault-cosim"
  verbose : Nat := 5

partial def parseArgs (o : Opts) : List String → Except String Opts
  | [] => .ok o
  | "--n" :: v :: rest => parseArgs { o with n := v.toNat! } rest
  | "--seed" :: v :: rest => parseArgs { o with seed := v.toNat! } rest
  | "--only" :: v :: rest => parseArgs { o with only := some v } rest
  | "--workdir" :: v :: rest => parseArgs { o with workDir := v } rest
  | "--show" :: v :: rest => parseArgs { o with verbose := v.toNat! } rest
  | a :: _ => .error s!"unknown argument {a}"

def envOr (k d : String) : IO String := return (← IO.getEnv k).getD d

def main (args : List String) : IO UInt32 := do
  let o ← match parseArgs {} args with
    | .ok o => pure o
    | .error e => IO.eprintln e; return 2
  IO.FS.createDirAll o.workDir
  let tools : Tools :=
    { clang := ← envOr "ARM_COSIM_CLANG" "clang", lld := ← envOr "ARM_COSIM_LLD" "rust-lld",
      qemu := ← envOr "ARM_COSIM_QEMU" "qemu-aarch64-static", workDir := o.workDir }
  let specs := faultSpecs.filter fun sp => match o.only with
    | some sub => (sp.name.splitOn sub).length > 1
    | none => true
  let mut rng : Rng := ⟨o.seed.toUInt64 ||| 1⟩
  -- one qemu program per chunk of at most 4000 cases (case indices are chunk-relative)
  let mut chunks : Array (Array TestCase) := #[]
  let mut tcs : Array TestCase := #[]
  for sp in specs do
    for _ in [0:o.n] do
      if tcs.size ≥ 4000 then
        chunks := chunks.push tcs
        tcs := #[]
      let i := tcs.size
      let (tc, rng') := ((do relocate i (← sp.gen i)) : GenM TestCase).run rng
      rng := rng'
      tcs := tcs.push tc
  chunks := chunks.push tcs
  let mut results := #[]
  for h : c in [0:chunks.size] do
    let out ← runFaultBatch tools s!"faults_{c}" chunks[c]
    results := results ++ checkFaultBatch chunks[c] out
  let mut shown := 0
  let mut totalFail := 0
  let mut totalFault := 0
  for sp in specs do
    let mine := results.filter (·.1.name == sp.name)
    let fails := mine.filter (·.2.1.size > 0)
    let faults := mine.filter (·.2.2)
    totalFail := totalFail + fails.size
    totalFault := totalFault + faults.size
    IO.println s!"{sp.name}\t{mine.size}\t{faults.size}\t{fails.size}"
    for (tc, errs, _) in fails do
      if shown < o.verbose then
        shown := shown + 1
        IO.println s!"FAIL {sp.name} inst {hex tc.inst.toNat}: {errs.toList.take 6}"
  IO.println s!"TOTAL forms {specs.length} vectors {results.size} faults {totalFault} failures {totalFail}"
  return if totalFail == 0 then 0 else 1
