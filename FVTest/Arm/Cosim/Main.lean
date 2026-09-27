/-
Copyright (c) 2026 fv-compiler-rust contributors.
Released under Apache 2.0 license.

`lake exe arm-cosim [--n N] [--seed S] [--only SUBSTR] [--workdir DIR]`: differential test of the
`FV.Arm` model against `qemu-aarch64-static` (see `Harness.lean`). Tool paths come from the
environment: `ARM_COSIM_CLANG` (default `clang`), `ARM_COSIM_LLD` (default `rust-lld`),
`ARM_COSIM_QEMU` (default `qemu-aarch64-static`). Prints one line per instruction form with its
vector and failure counts; exits 1 if any vector fails. `scripts/arm-cosim.sh` sets the tools up.
-/
import FVTest.Arm.Cosim.Specs

open Arm.Cosim

structure Opts where
  n : Nat := 200
  seed : Nat := 0x5eed
  only : Option String := none
  workDir : String := ".lake/arm-cosim"
  verbose : Nat := 3

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
  let specs := allSpecs.filter fun sp => match o.only with
    | some sub => (sp.name.splitOn sub).length > 1 || (sp.batch.splitOn sub).length > 1
    | none => true
  -- Group specs into batches, preserving order.
  let mut batches : Array (String × Array Spec) := #[]
  for sp in specs do
    match batches.findIdx? (·.1 == sp.batch) with
    | some k => batches := batches.modify k fun (b, xs) => (b, xs.push sp)
    | none => batches := batches.push (sp.batch, #[sp])
  let mut rng : Rng := ⟨o.seed.toUInt64 ||| 1⟩
  let mut totalFail := 0
  let mut totalVec := 0
  let mut rows : Array (String × Nat × Nat) := #[]
  for (bname, bspecs) in batches do
    let mut tcs : Array TestCase := #[]
    for sp in bspecs do
      for _ in [0:o.n] do
        let (tc, rng') := (sp.gen tcs.size).run rng
        rng := rng'
        tcs := tcs.push tc
    let tag := String.map (fun c => if c.isAlphanum then c else '_') bname
    let out ← runBatch tools tag tcs
    let results := checkBatch tcs out
    let mut shown := 0
    for sp in bspecs do
      let mine := results.filter (·.1.name == sp.name)
      let fails := mine.filter (·.2.size > 0)
      rows := rows.push (sp.name, mine.size, fails.size)
      totalVec := totalVec + mine.size
      totalFail := totalFail + fails.size
      for (tc, errs) in fails do
        if shown < o.verbose then
          shown := shown + 1
          IO.println s!"FAIL {sp.name} inst {hex tc.inst.toNat}: {errs.toList.take 6}"
  for (nm, v, f) in rows do
    IO.println s!"{nm}\t{v}\t{f}"
  IO.println s!"TOTAL forms {rows.size} vectors {totalVec} failures {totalFail}"
  return if totalFail == 0 then 0 else 1
