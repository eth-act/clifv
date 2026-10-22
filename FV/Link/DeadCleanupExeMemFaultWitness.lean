import FV.Link.DeadCleanupExeMemTrapWitness
import FV.Link.DeadCleanupExeMemFault

/-!
# Witness: the fault-aware executable theorem applies to a compiled executable (A3, #412, F8)

`DeadCleanupExeMemTrapWitness`'s `f(a, e, x) = atomic_cas.i64 a, e, x` compiled by the shipped
compiler into `file`, its run on `(0, 1, 2)` trapping `heap_oob` at the null page, the memory map
`nullMap` (nothing mapped below 4096, everything else read-write):

* `img_ge`: the program's code lies above the null page (`chkImg`, `native_decide`);
* `mapRelRW`: the memory map premise `MapRelRW nullMap` of an outside call of `f` on `(0, 1, 2)`
  whose reserved stack lies above the null page (the entry's CLIF memory is empty, the arguments
  are in registers);
* `exec_trapsF`: `Link.DeadCleanup.compileExe_correct_memtrapF_rw` with every premise discharged
  but the entry contract (`Image.Intact`, `OutsideCall`, `ClifRun`) and the stack above the null
  page: the fault-aware executable machine `stepF nullMap` runs from `r`, with no faulting step,
  to a trap site of `f` with `heap_oob` whose instruction errs or faults, and errs there
  (`ExecTrapF`).
-/

namespace Link.DeadCleanup.MemTrapWitness

open E2E E2E.LinkCheck E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes Backend Backend.Proof
  Backend.Proof.Driver

/-- Every word of the compiled program lies above the null page, without wrapping. -/
def chkImg : Bool :=
  (tabOf spec.inputCleanup.resultsCleanup).all fun e =>
    (e.2.fb.program e.2.base).all fun p => decide (4096 ≤ p.1.toNat ∧ p.1.toNat + 4 ≤ 2 ^ 64)

set_option maxRecDepth 100000 in
theorem chkImg_true : chkImg = true := by native_decide

/-- **The program's code lies above the null page.** -/
theorem img_ge {a : BitVec 64} (h : img spec.inputCleanup a) : 4096 ≤ a.toNat := by
  obtain ⟨e, he, p, hp, hd⟩ := h
  have h12 := List.all_eq_true.1 (List.all_eq_true.1 chkImg_true e he) p hp
  simp only [decide_eq_true_eq] at h12
  obtain ⟨h1, h2⟩ := h12
  have ha : a = p.1 + (a - p.1) := by rw [BitVec.add_comm, BitVec.sub_add_cancel]
  rw [ha, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  omega

/-- **The memory map premise `MapRelRW nullMap`** of an outside call of `f` on `(0, 1, 2)` whose
reserved stack `N` lies above the null page. -/
theorem mapRelRW {N : Nat} {r : Arm.ArmState} (hsp : 4096 + N ≤ (spv r).toNat) :
    MapRelRW nullMap spec.inputCleanup fF N r [vA, vE, vX] cs0.mem where
  nw := {
    stack := fun a ha hb => by
      simp only [nullMap] at ha
      split at ha
      · rename_i hlt
        obtain ⟨-, h2⟩ := hb
        omega
      · simp [ArmFault.Perm.allows] at ha
    args := fun off v hm => by
      have hall : (locsOf fF.sig).all (fun l => match l with | .stack _ => false | _ => true) =
          true := by decide
      have := List.all_eq_true.1 hall _ (List.of_mem_zip hm).1
      simp at this
    valid := fun a n hv => by
      simp [cs0, Clif.Mem.valid] at hv }
  code := fun a ha => by
    have := img_ge ha
    simp only [nullMap, show ¬ a.toNat < 4096 by omega, ite_false]
    rfl

/-- **The fault-aware executable reaches the `atomic_cas`'s memory trap without an earlier
fault**: for every machine state `r` meeting the entry contract of an outside call of `f` on
`(0, 1, 2)` (`Image.Intact`, `OutsideCall`, `ClifRun`) whose reserved stack lies above the null
page, the run of `stepF nullMap` on the written executable `file` from `r` reaches, with no
faulting step, a trap site of `f` with `heap_oob` whose instruction errs or faults under
`nullMap`, and errs there (`Link.DeadCleanup.compileExe_correct_memtrapF_rw`, every other premise
discharged). -/
theorem exec_trapsF {r : Arm.ArmState} (hX : (imageOf file).Intact r)
    (ho : OutsideCall spec.inputCleanup (BinCheck.roByte spec.inputCleanup spec.data) fF
      (DeadCleanupStackBound.stackFn spec.inputCleanup fF) r [vA, vE, vX] cs0.mem)
    (hr : ClifRun spec.inputCleanup closedBase fF r [vA, vE, vX] cs0)
    (hsp : 4096 + DeadCleanupStackBound.stackFn spec.inputCleanup fF ≤ (spv r).toNat) :
    ExecTrapF nullMap spec.inputCleanup closedBase file fF .heapOob r :=
  compileExe_correct_memtrapF_rw compile_eq closedBase baseOk (hooksSim_closed _) hf hc 0 hX ho hr
    cs0_trapsExplicitM cs0_mapFaults (mapRelRW hsp) _ run_traps

end Link.DeadCleanup.MemTrapWitness
