import FV.Concurrency.IselClif
import FV.Concurrency.VCodeFrameWitness

/-!
# Non-vacuity of layer 2d (T2h, #311): `IselFoot`, `IselClif`

* `runOut_ldar`: the `ldar` of `VCodeThread.Witness` (8 bytes at `0x8000`, under `csem` with the
  frame `F8` of `VCodeAddr.Witness`, on which it steps: `csem_ldar8`) keeps the byte `0x9000`
  outside its events, so it is `Untouched` (`untouched_ldar`, by `untouched_of_runOut`);
* `atomicLoad_facts0`, `store_facts0`: an `atomic_load.i64` and a `store.i64` through `v1 = 0x8000`
  on a memory with the 8 bytes `[0x8000, 0x8008)` allocated and initialised succeed, their access
  is `(0x8000, 8)`, and their `LoadFacts`/`StoreFacts` (the premises of `load_touched`/
  `store_touched`) hold.
-/

namespace Concurrency.IselClif.Witness

open Arm ArmFoot ArmThread Backend Backend.Proof VCodeThread VCodeThread.Witness
  VCodeAddr.Witness IselFoot

/-- The `ldar`'s run keeps `0x9000` outside its events. -/
theorem runOut_ldar : RunOut (csem F8 ctx0 X0) 0x9000#64 [iLdar] ρ0 w0 := by
  intro ops hops
  rw [ops0_eq] at hops
  cases hops
  refine ⟨cEvs F8 ctx0 iLdar [ofX 0x8000#64] w0, ?_, ?_, fun _ _ _ => trivial⟩
  · rw [show vuses ops0 ρ0 = [ofX 0x8000#64] from uses0]
    exact ifoot_csem X0_tls (by decide +kernel) (fun _ h => nomatch h) (fun _ _ h => nomatch h)
      (fun _ => ⟨by decide +kernel, by unfold Arm.CheckSPAlignment; decide +kernel⟩)
  · unfold Out
    decide +kernel

/-- **Non-vacuity of `untouched_of_runOut`**: the byte `0x9000` is untouched by the `ldar`. -/
theorem untouched_ldar : IselVary.Untouched (csem F8 ctx0 X0) [iLdar] ρ0 w0 0x9000#64 :=
  untouched_of_runOut runOut_ldar

/-- `v1 = 0x8000`, `v2 = 7`. -/
def fr0 : Clif.Frame where
  func := default
  regs := fun v => if v = 1 then some ⟨.i64, 0x8000#64⟩ else if v = 2 then some ⟨.i64, 7#64⟩
    else none
  slots := []
  body := []
  term := default

/-- The 8 bytes at `0x8000`, allocated and zero. -/
def cm0 : Clif.Mem where
  allocs := [{ base := 0x8000, size := 8 }]
  bytes := fun a => if 0x8000 ≤ a ∧ a < 0x8008 then some 0#8 else none

def env0 : Clif.Env := {}

def p0 : Clif.Program := { funcs := [] }

theorem atomicLoad_ok0 :
    instOutcome env0 p0 fr0 cm0 (.atomicLoad .i64 {} 1) = .ok ([⟨.i64, 0#64⟩], cm0) := by
  rfl

theorem atomicLoad_access0 : access fr0 (.atomicLoad .i64 {} 1) = some (0x8000, 8) := by
  decide

/-- **Non-vacuity of `atomicLoad_facts`**. -/
theorem atomicLoad_facts0 : LoadFacts env0 p0 fr0 cm0 (.atomicLoad .i64 {} 1) 0x8000 8 :=
  atomicLoad_facts (pv := ⟨.i64, 0x8000#64⟩) rfl atomicLoad_ok0 rfl

theorem store_ok0 : instOutcome env0 p0 fr0 cm0 (.store .store .i64 {} 2 1 0) =
    .ok ([], cm0.writeBits false 0x8000 8 (7#64)) := by
  rfl

theorem store_access0 : access fr0 (.store .store .i64 {} 2 1 0) = some (0x8000, 8) := by
  decide

/-- **Non-vacuity of `store_facts`**. -/
theorem store_facts0 : StoreFacts env0 p0 fr0 cm0 (.store .store .i64 {} 2 1 0) 0x8000 8 :=
  store_facts (pv := ⟨.i64, 0x8000#64⟩) store_ok0 rfl

end Concurrency.IselClif.Witness
