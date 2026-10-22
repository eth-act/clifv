import FV.Concurrency.ClifCStep
import FV.Concurrency.IselClifWitness

/-!
# Non-vacuity of the CLIF thread steps of the memory statements (T2h, #311)

On the frame of `IselClif.Witness` (`v1 = 0x8000`, `v2 = 7`, `v3 = 0`) and the memory with the
8 zero bytes at `0x8000`:

* `cstep_atomicLoad0`: `v4 = atomic_load.i64 v1` is a `CStep` with the `scR` read of the 8 zero
  bytes at `0x8000`;
* `cstep_store0`: `store.i64 v2, v1` is a `CStep` with the `naW` write of `7`'s bytes there;
* `cstep_atomicCas0`: `v4 = atomic_cas.i64 v1, v3, v2` (expected `0`, found `0`) is a `CStep`
  with the read and the write of `7`.
-/

namespace Concurrency.ClifCStep.Witness

open Prog ClifThread IselClif IselClif.Witness

/-- `fr0` with `v3 = 0`. -/
def frC : Clif.Frame := { fr0 with
  regs := fun v => if v = 3 then some ⟨.i64, 0#64⟩ else fr0.regs v }

/-- The state about to run `stm`. -/
def st (stm : Clif.Stmt) : Clif.State :=
  { frame := { frC with body := [stm] }, callers := [], mem := cm0 }

def sLoad : Clif.Stmt := { results := [4], inst := .atomicLoad .i64 {} 1 }
def sStore : Clif.Stmt := { inst := .store .store .i64 {} 2 1 0 }
def sCas : Clif.Stmt := { results := [4], inst := .atomicCas .i64 {} 1 3 2 }

theorem zeros : getB cm0.bytes 0x8000 8 = List.replicate 8 (some 0#8) := by decide

/-- **Non-vacuity of `cstep_atomicLoad`.** -/
theorem cstep_atomicLoad0 : ∃ s', CStep env0 p0 (.run (st sLoad))
    [⟨.scR, .R, 0x8000, 8, List.replicate 8 (some 0#8)⟩] (.run s') := by
  obtain ⟨s', hs⟩ : ∃ s', Clif.step env0 p0 (st sLoad) = .next s' := ⟨_, rfl⟩
  refine ⟨s', ?_⟩
  rw [← zeros]
  exact cstep_atomicLoad (s := st sLoad) (pv := ⟨.i64, 0x8000#64⟩) rfl rfl rfl hs

/-- **Non-vacuity of `cstep_store`.** -/
theorem cstep_store0 : ∃ s', CStep env0 p0 (.run (st sStore))
    [⟨.naW, .W, 0x8000, 8, valB false 8 (7#64)⟩] (.run s') :=
  ⟨_, cstep_store (s := st sStore) (pv := ⟨.i64, 0x8000#64⟩) rfl rfl rfl rfl rfl⟩

/-- **Non-vacuity of `cstep_atomicCas`** (the comparison succeeds). -/
theorem cstep_atomicCas0 : ∃ s', CStep env0 p0 (.run (st sCas))
    [⟨.scR, .R, 0x8000, 8, List.replicate 8 (some 0#8)⟩,
      ⟨.scW, .W, 0x8000, 8, valB false 8 (7#64)⟩] (.run s') := by
  obtain ⟨s', hs⟩ : ∃ s', Clif.step env0 p0 (st sCas) = .next s' := ⟨_, rfl⟩
  refine ⟨s', ?_⟩
  have h := cstep_atomicCas (s := st sCas) (pv := ⟨.i64, 0x8000#64⟩) (ev := 0#64) (v := 7#64)
    (old := 0#64) rfl rfl rfl rfl rfl rfl hs
  rw [← zeros]
  exact h

end Concurrency.ClifCStep.Witness
