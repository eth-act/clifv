module

public import FV.Concurrency.ArmThread

@[expose] public section

/-!
# Non-vacuity of the per-thread Arm semantics (T2d, #302)

Cranelift's `atomic_rmw add` loop (`FV/Backend/Asm.lean` `rmwLoopLines`, registers as emitted),
loaded at `0x1000`, with the atomic's address `0x8000` in x25:

```
0x1000  ldaxr x27, [x25]        c85fff3b
0x1004  add   x28, x27, x26     8b1a037c
0x1008  stlxr w24, x28, [x25]   c818ff3c
0x100c  cbnz  w24, 0x1000       35ffffb8
```

`retry_run`: under the Arm monitor policy the thread reads `5` at `0x8000` (an `acqXR` event,
the monitor armed), adds, its `stlxr` **fails** (no event, `w24 := 1`) and `cbnz` branches back
to the `ldaxr`: the retry of the loop. `retry_succ`: with the monitor armed the `stlxr` may also
succeed, a `relXW` write event of the sum (`evWrite_eq`). `no_xfail_sc` (general): the single-core monitor never
fails, so the failing run is not a single-core run.
-/

namespace Concurrency.ArmThread.Witness

open Arm ArmFoot

/-- The loop's words. -/
def prog : Program :=
  [(0x1000#64, 0xc85fff3b#32), (0x1004#64, 0x8b1a037c#32), (0x1008#64, 0xc818ff3c#32),
   (0x100c#64, 0x35ffffb8#32)]

/-- The state at `pc` with x24 = `x24`, x25 = `0x8000`, x26 = `1`, the memory zero. -/
def st (pc x24 : BitVec 64) : ArmState :=
  w .PC pc (w (.GPR 24#5) x24 (w (.GPR 26#5) 1#64 (w (.GPR 25#5) 0x8000#64
    (set_program ArmState.default prog))))

/-- `ldaxr x27, [x25]` -/
def iLdaxr : Reg_exclusive_cls := { size := 3, ord := 0, L := 1, Rs := 31, o0 := 1, Rn := 25, Rt := 27 }

/-- `stlxr w24, x28, [x25]` -/
def iStlxr : Reg_exclusive_cls := { size := 3, ord := 0, L := 0, Rs := 24, o0 := 1, Rn := 25, Rt := 28 }

theorem decode_ldaxr : decodeAt (st 0x1000#64 0#64) = some (.LDST (.Reg_exclusive iLdaxr)) := by
  decide +kernel

/-- The read event of the `ldaxr`: `5` at `0x8000`. -/
def evRead : Ev := ⟨.acqXR, 0x8000#64, 8, 5#64⟩

/-- The state after the `ldaxr` read `5`. -/
def s1 : ArmState := stepi (setMem (applyR [evRead] (st 0x1000#64 0#64).mem) (st 0x1000#64 0#64))

theorem step_ldaxr :
    TStep Policy.arm stepi (st 0x1000#64 0#64, none) ⟨[evRead], false⟩ (s1, some (0x8000#64, 8)) := by
  have hfp := footprint_load_excl (s := st 0x1000#64 0#64) .acqXR rfl (by decide +kernel)
    decode_ldaxr rfl (by decide +kernel) (5#64 : BitVec 64)
  have hcls : cls (st 0x1000#64 0#64) = .ldx true 25#5 3#2 := by
    unfold cls; rw [decode_ldaxr]; decide
  have haddr : read_gpr 64 iLdaxr.Rn (st 0x1000#64 0#64) = 0x8000#64 := by decide +kernel
  rw [haddr] at hfp
  have hmon : monAfter (cls (st 0x1000#64 0#64)) (st 0x1000#64 0#64) none = some (0x8000#64, 8) := by
    rw [hcls]; simp only [monAfter]; rw [show read_gpr 64 25#5 (st 0x1000#64 0#64) = 0x8000#64 from haddr]
    rfl
  rw [← hmon]
  refine TStep.exec ⟨?_, ?_⟩ ?_ hfp ?_
  · intro e he; simp only [List.mem_singleton] at he; subst he; rw [hcls]; rfl
  · rw [hcls]; intro h; cases h
  · intro e he hr; simp only [List.mem_singleton] at he; subst he
    simp only [applyR, evRead, AKind.dir, ite_true]
    exact readM_writeM _ _ _ _ (by decide)
  · intro _ _ _ h; rw [hcls] at h; cases h

theorem s1_pc : r .PC s1 = 0x1004#64 := by decide +kernel

theorem decode_s1 : decodeAt s1 = some (.DPR (.Add_sub_shifted_reg
    { sf := 1, op := 0, S := 0, shift := 0, Rm := 26, imm6 := 0, Rn := 27, Rd := 28 })) := by
  decide +kernel

/-- The state after the `add`. -/
def s2 : ArmState := stepi s1

theorem step_add : TStep Policy.arm stepi (s1, some (0x8000#64, 8)) ⟨[], false⟩
    (s2, some (0x8000#64, 8)) := by
  have hcls : cls s1 = .plain := by unfold cls; rw [decode_s1]
  have e : s2 = stepi (setMem (applyR [] s1.mem) s1) := rfl
  have hm : some (0x8000#64, 8) = monAfter (cls s1) s1 (some (0x8000#64, 8)) := by
    rw [hcls]; rfl
  have h := TStep.exec (P := Policy.arm) (f := stepi) (s := s1) (mon := some (0x8000#64, 8)) (evs := [])
    ⟨fun _ h => absurd h List.not_mem_nil, by rw [hcls]; intro h; cases h⟩
    (fun _ h => absurd h List.not_mem_nil)
    (footprint_nonldst (fun ai h => by rw [decode_s1] at h; cases h; rfl))
    (fun _ _ _ h => by rw [hcls] at h; cases h)
  rw [← hm, ← e] at h
  exact h

theorem decode_s2 : decodeAt s2 = some (.LDST (.Reg_exclusive iStlxr)) := by decide +kernel

theorem cls_s2 : cls s2 = .stx true 24#5 25#5 := by unfold cls; rw [decode_s2]; decide

/-- The state after the failing `stlxr`. -/
def s3 : ArmState := failState 24#5 s2

/-- **The `stlxr` fails** under the Arm policy (monitor armed or not). -/
theorem step_xfail : TStep Policy.arm stepi (s2, some (0x8000#64, 8)) ⟨[], true⟩ (s3, none) :=
  TStep.xfail cls_s2 trivial (by decide +kernel) (by decide +kernel)

theorem s3_w24 : r (.GPR 24#5) s3 = 1#64 := by decide +kernel

theorem decode_s3 : decodeAt s3 = some (.BR (.Compare_branch
    { sf := 0, op := 1, imm19 := 0x7fffd, Rt := 24 })) := by decide +kernel

/-- The state after `cbnz`. -/
def s4 : ArmState := stepi s3

theorem step_cbnz : TStep Policy.arm stepi (s3, none) ⟨[], false⟩ (s4, none) := by
  have hcls : cls s3 = .plain := by unfold cls; rw [decode_s3]
  have e : s4 = stepi (setMem (applyR [] s3.mem) s3) := rfl
  have hm : (none : Mon) = monAfter (cls s3) s3 none := by rw [hcls]; rfl
  have h := TStep.exec (P := Policy.arm) (f := stepi) (s := s3) (mon := none) (evs := [])
    ⟨fun _ h => absurd h List.not_mem_nil, by rw [hcls]; intro h; cases h⟩
    (fun _ h => absurd h List.not_mem_nil)
    (footprint_nonldst (fun ai h => by rw [decode_s3] at h; cases h; rfl))
    (fun _ _ _ h => by rw [hcls] at h; cases h)
  rw [← hm, ← e] at h
  exact h

/-- **The retry**: `cbnz` branches back to the `ldaxr`. -/
theorem s4_pc : r .PC s4 = 0x1000#64 := by decide +kernel

/-- **Non-vacuity of the failing store exclusive**: a run of the loop under the Arm policy in which
the `ldaxr` reads `5`, the `stlxr` fails and the loop retries from the `ldaxr`. -/
theorem retry_run :
    TRun Policy.arm stepi (st 0x1000#64 0#64, none)
      [⟨[evRead], false⟩, ⟨[], false⟩, ⟨[], true⟩, ⟨[], false⟩] (s4, none) ∧
      r .PC s4 = 0x1000#64 ∧ decodeAt s4 = decodeAt (st 0x1000#64 0#64) :=
  ⟨.cons step_ldaxr (.cons step_add (.cons step_xfail (.cons step_cbnz .nil))), s4_pc,
    by rw [decode_ldaxr]; decide +kernel⟩

/-- The write event of the successful `stlxr`. -/
def evWrite : Ev := ⟨.relXW, read_gpr 64 iStlxr.Rn s2, exclBytes iStlxr.size,
  BitVec.cast (exclBytes_mul iStlxr.size).symm (ldst_read false (8 <<< iStlxr.size.toNat) iStlxr.Rt s2)⟩

/-- It writes the sum `6` (8 bytes) at `0x8000`. -/
theorem evWrite_eq : evWrite.addr = 0x8000#64 ∧ evWrite.n = 8 ∧ evWrite.val.toNat = 6 := by
  decide +kernel

/-- **The successful `stlxr`**: with the monitor armed it writes the sum (`evWrite`, a `relXW`
event) and disarms the monitor. -/
theorem retry_succ :
    TStep Policy.arm stepi (s2, some (0x8000#64, 8)) ⟨[evWrite], false⟩ (stepi s2, none) := by
  have hfp : Footprint stepi s2 [evWrite] :=
    footprint_store_excl (s := s2) .relXW rfl (by decide +kernel) decode_s2 rfl (by decide +kernel)
  have e : stepi s2 = stepi (setMem (applyR [evWrite] s2.mem) s2) := by
    simp only [applyR, evWrite, AKind.dir, show (Dir.W = Dir.R) = False from by simp, ite_false,
      setMem_self]
  have hm : (none : Mon) = monAfter (cls s2) s2 (some (0x8000#64, 8)) := by rw [cls_s2]; rfl
  rw [e, hm]
  refine TStep.exec ⟨?_, ?_⟩ ?_ hfp ?_
  · intro e he; simp only [List.mem_singleton] at he; subst he; rw [cls_s2]; rfl
  · rw [cls_s2]; intro h; cases h
  · intro e he hr; simp only [List.mem_singleton] at he; subst he; cases hr
  · intro _ _ _ _; exact rfl

end Concurrency.ArmThread.Witness
