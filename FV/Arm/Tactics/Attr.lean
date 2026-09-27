/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Siddharth Bhat, Alex Keizer
-/
-- Modified by fv-compiler-rust (2026): ported to Lean v4.34.1, module prefix FV.Arm, wrapped in namespace Arm, dropped the CSE/prune_updates trace classes and options (those tactics are not ported), `bv_omega_bench` file logging is off by default.
import Lean

namespace Arm

open Lean
initialize
  -- enable tracing for `sym_n` tactic and related components
  registerTraceClass `Tactic.sym
  -- enable verbose tracing
  registerTraceClass `Tactic.sym.info

  -- enable tracing for heartbeat usage of `sym_n`
  registerTraceClass `Tactic.sym.heartbeats

  -- enable extra checks for debugging `sym_n`,
  -- see `AxEffects.validate` for more detail on what is being type-checked
  registerOption `Tactic.sym.debug {
    name := `Tactic.sym.debug
    defValue := true
    descr := "enable/disable type-checking of internal state during execution \
      of the `sym_n` tactic, throwing an error if mal-formed expressions were \
      created, indicating a bug in the implementation of `sym_n`.

      This is an internal option for debugging purposes, end users should \
      generally not set this option, unless they are reporting a bug with \
      `sym_n`"
  }

register_option Tactic.bv_omega_bench.filePath : String := {
  defValue := "/tmp/omega-bench.txt"
  descr := "File path that `omega-bench` writes its results to."
}

register_option Tactic.bv_omega_bench.enabled : Bool := {
  defValue := false,
  descr := "Enable `bv_omega_bench`'s logging, which writes benchmarking data to \
    `Tactic.bv_omega_bench.filePath`."
}

register_option Tactic.bv_omega_bench.minMs : Nat := {
  defValue := 1000,
  descr := "Log into `Tactic.bv_omega_bench.filePath` if the time spent in milliseconds is \
    greater than or equal to `Tactic.bv_omega_bench.minMs`."
}

def getBvOmegaBenchFilePath [Monad m] [MonadOptions m] : m String := do
  return Tactic.bv_omega_bench.filePath.get (← getOptions)

def getBvOmegaBenchIsEnabled [Monad m] [MonadOptions m] : m Bool := do
  return Tactic.bv_omega_bench.enabled.get (← getOptions)

def getBvOmegaBenchMinMs [Monad m] [MonadOptions m] : m Nat := do
  return Tactic.bv_omega_bench.minMs.get (← getOptions)

end Arm
