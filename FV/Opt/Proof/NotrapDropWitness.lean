import FV.Opt.Proof.NotrapDropKeep
import FV.Opt.Proof.NotrapDropSimU

/-!
# Non-vacuity of the drop of unused `notrap` loads (option D, #1017)

The functions of Cranelift's filetest `isa/aarch64/dead-notrap-load.clif` (wasmtime v49.0.1) and
one more:

* `chain` (`%dead_notrap_load_chain`): both loads go (`chain_run`), so `run_simU` relates two
  different functions (`chain_run_simU`);
* `liveAddr` (`%dead_notrap_load_live_address`): the load goes, the address `iadd` (returned) and
  its `iconst` stay (`liveAddr_run`);
* negative: `trapping` (`%dead_trapping_load`, flags without `notrap`: a trap code) is unchanged
  (`trapping_run`; in general `run_keeps_trapping`), and `used` (a `notrap` load whose value is
  returned) is unchanged (`used_run`; in general `run_keeps_used`).

The pass's `Std.HashSet`s do not reduce in the kernel, so the evaluations use `native_decide`.
-/

namespace Opt.NotrapDrop.Witness

open Clif

/-- `notrap aligned` -/
def nt : MemFlags := { trapCode := none, aligned := true }

def sigI64 : Signature := { params := [{ ty := .i64 }], returns := [] }

/-- `%dead_notrap_load_chain`: `v1 = load.i64 notrap aligned readonly v0+176`,
`v2 = load.i32 notrap aligned v1`, `return`. -/
def chain : Function where
  name := "dead_notrap_load_chain"
  sig := sigI64
  blocks := [{ id := 0, params := [(0, .i64)], body := [
    { results := [1], inst := .load .load .i64 { nt with readonly := true } 0 176 },
    { results := [2], inst := .load .load .i32 nt 1 0 }], term := .ret [] }]

def chain' : Function :=
  { chain with blocks := [{ id := 0, params := [(0, .i64)], body := [], term := .ret [] }] }

theorem chain_run : run chain = chain' := by native_decide -- witness: native_decide

theorem chain_changed : chain' ≠ chain := by decide +kernel

/-- **`run_simU` relates two different functions** (both dead loads dropped). -/
theorem chain_run_simU : FunSimU chain chain' := chain_run ▸ run_simU chain

/-- `%dead_notrap_load_live_address`: `v1 = iconst.i64 8`, `v2 = iadd v0, v1`,
`v3 = load.i64 notrap aligned v2`, `return v2`. -/
def liveAddr : Function where
  name := "dead_notrap_load_live_address"
  sig := { params := [{ ty := .i64 }], returns := [{ ty := .i64 }] }
  blocks := [{ id := 0, params := [(0, .i64)], body := [
    { results := [1], inst := .iconst .i64 8 },
    { results := [2], inst := .binary .iadd .i64 0 1 },
    { results := [3], inst := .load .load .i64 nt 2 0 }], term := .ret [2] }]

def liveAddr' : Function :=
  { liveAddr with blocks := [{ id := 0, params := [(0, .i64)], body := [
    { results := [1], inst := .iconst .i64 8 },
    { results := [2], inst := .binary .iadd .i64 0 1 }], term := .ret [2] }] }

theorem liveAddr_run : run liveAddr = liveAddr' := by native_decide -- witness: native_decide

theorem liveAddr_simX : FunSimX liveAddr liveAddr' := liveAddr_run ▸ run_simX liveAddr

/-- `%dead_trapping_load`: `v1 = load.i64 aligned v0` (a trap code: `heap_oob`), `return`. -/
def trapping : Function where
  name := "dead_trapping_load"
  sig := sigI64
  blocks := [{ id := 0, params := [(0, .i64)], body := [
    { results := [1], inst := .load .load .i64 { aligned := true } 0 0 }], term := .ret [] }]

/-- **Negative: a load with a trap code is not dropped.** -/
theorem trapping_run : run trapping = trapping := by native_decide -- witness: native_decide

/-- A `notrap` load whose value is returned. -/
def used : Function where
  name := "used_notrap_load"
  sig := { params := [{ ty := .i64 }], returns := [{ ty := .i64 }] }
  blocks := [{ id := 0, params := [(0, .i64)], body := [
    { results := [1], inst := .load .load .i64 nt 0 0 }], term := .ret [1] }]

/-- **Negative: a `notrap` load whose value is used is not dropped.** -/
theorem used_run : run used = used := by native_decide -- witness: native_decide

end Opt.NotrapDrop.Witness
