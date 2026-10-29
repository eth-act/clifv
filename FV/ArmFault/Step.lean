module

public import FV.Concurrency.ArmInstFoot

@[expose] public section

/-!
# Memory faults of the Arm machine (A3, #412, slice F1; `docs/plans/memfault.md`)

`Arm.stepi` has no memory faults: every address can be read and written. A process has a
**memory map**: an access to a byte its map does not allow (unmapped, or written while
read-only) raises a synchronous Data Abort, which Linux delivers as `SIGSEGV` at the faulting
instruction. This file adds that fault to the model **without changing `FV/Arm`**: the access of
an instruction is its precise footprint (`Concurrency.ArmInstFoot.instEvs`, `stepEvs`: address,
size and direction of each memory event, `footprint_exec_inst`/`footprint_stepi`), and

* `MemMap := BitVec 64 → Perm` (`none`, `ro`, `rw`); `Perm.allows`: a read needs `ro` or `rw`, a
  write `rw`, a barrier event nothing;
* `evsOk mp evs`: every byte of every event is allowed; `InstFaults mp ai s`/`Faults mp s`: not
  `evsOk` of `instEvs ai s`/`stepEvs s`;
* `execF mp ai s`, `stepF mp s`, `runF mp n s`: `exec_inst`, `stepi`, `Arm.run`, except that a
  faulting instruction sets the error `memFault` and changes nothing else. A Data Abort is precise:
  pc, registers and memory are those before the instruction (a page-crossing store's partial
  write is CONSTRAINED UNPREDICTABLE in the Arm ARM; no theorem observes memory after a trap).

Results: `stepF_of_ok`/`execF_of_ok` (no fault: the old step), `stepF_fault`/`execF_fault` and the
field lemmas (`r_stepF_fault`, `mem_stepF_fault`, `program_stepF_fault`), `stepF_err` (an error
state stays), `stepF_eq_execF` (at a decoded instruction), `runF_eq_run` (a run in which no
step faults is `Arm.run`), `runF_fault` (the run up to the first fault, then the fault for ever),
`faults_of_byte` (a forbidden byte of an event faults), `evsOk_mono` (a map allowing more faults
less). The co-simulation `arm-fault-cosim` (`FVTest/Arm/Cosim/Fault.lean`) checks `stepF` against
qemu on accesses around a `PROT_NONE` and a read-only page. Witnesses: `FV/ArmFault/Witness.lean`.

Not modelled: alignment faults of mapped exclusives, instruction-fetch faults (the program is
separate from memory), changes of the map during a run.
-/

namespace ArmFault

open Arm Concurrency Concurrency.ArmFoot Concurrency.ArmThread Concurrency.ArmInstFoot

/-! ## Memory maps -/

/-- The permission of a byte in the process's memory map. -/
inductive Perm where
  | none | ro | rw
  deriving DecidableEq, Repr, Inhabited

/-- Does a byte with this permission allow an access in direction `d`? A barrier event (`F`)
accesses no byte. -/
def Perm.allows : Perm → Dir → Bool
  | _, .F => true
  | .rw, _ => true
  | .ro, .R => true
  | _, _ => false

/-- **A memory map**: the permission of every byte. -/
abbrev MemMap := BitVec 64 → Perm

/-- `mp'` allows every access `mp` allows. -/
def MemMap.Le (mp mp' : MemMap) : Prop := ∀ a d, (mp a).allows d = true → (mp' a).allows d = true

/-- The map allowing everything (the fault-free machine). -/
def MemMap.all : MemMap := fun _ => .rw

/-! ## Faulting accesses -/

/-- Every byte of the event is allowed in the event's direction. -/
def evOk (mp : MemMap) (e : Ev) : Bool :=
  (List.range e.n).all fun i => (mp (e.addr + BitVec.ofNat 64 i)).allows e.k.dir

/-- Every event's bytes are allowed. -/
def evsOk (mp : MemMap) (evs : List Ev) : Bool := evs.all (evOk mp)

/-- **The instruction `ai` faults at `s`**: a byte of its access is not allowed. -/
def InstFaults (mp : MemMap) (ai : ArmInst) (s : ArmState) : Prop :=
  evsOk mp (instEvs ai s) = false

/-- **The step of `stepi` from `s` faults.** -/
def Faults (mp : MemMap) (s : ArmState) : Prop := evsOk mp (stepEvs s) = false

instance (mp : MemMap) (ai : ArmInst) (s : ArmState) : Decidable (InstFaults mp ai s) := by
  unfold InstFaults; infer_instance

instance (mp : MemMap) (s : ArmState) : Decidable (Faults mp s) := by
  unfold Faults; infer_instance

/-- The error of a memory fault. -/
def memFault : StateError := .Fault "memory fault"

theorem memFault_ne_none : memFault ≠ .None := by simp [memFault]

/-! ## The machine with faults -/

/-- **`exec_inst` with faults.** -/
def execF (mp : MemMap) (ai : ArmInst) (s : ArmState) : ArmState :=
  if evsOk mp (instEvs ai s) then exec_inst ai s else write_err memFault s

/-- **`stepi` with faults.** -/
def stepF (mp : MemMap) (s : ArmState) : ArmState :=
  if evsOk mp (stepEvs s) then stepi s else write_err memFault s

/-- **`Arm.run` with faults.** -/
def runF (mp : MemMap) : Nat → ArmState → ArmState
  | 0, s => s
  | n + 1, s => runF mp n (stepF mp s)

theorem runF_succ' (mp : MemMap) (n : Nat) (s : ArmState) :
    runF mp (n + 1) s = stepF mp (runF mp n s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp only [runF] at ih ⊢; exact ih _

theorem runF_add (mp : MemMap) (m n : Nat) (s : ArmState) :
    runF mp (m + n) s = runF mp n (runF mp m s) := by
  induction m generalizing s with
  | zero => simp [runF]
  | succ m ih => rw [Nat.add_right_comm]; simp only [runF]; exact ih _

/-! ## No fault: the old step -/

theorem execF_of_ok {mp : MemMap} {ai : ArmInst} {s : ArmState}
    (h : evsOk mp (instEvs ai s) = true) : execF mp ai s = exec_inst ai s := by
  simp [execF, h]

theorem stepF_of_ok {mp : MemMap} {s : ArmState} (h : evsOk mp (stepEvs s) = true) :
    stepF mp s = stepi s := by
  simp [stepF, h]

theorem execF_of_not {mp : MemMap} {ai : ArmInst} {s : ArmState} (h : ¬ InstFaults mp ai s) :
    execF mp ai s = exec_inst ai s :=
  execF_of_ok (by simpa [InstFaults] using h)

theorem stepF_of_not {mp : MemMap} {s : ArmState} (h : ¬ Faults mp s) : stepF mp s = stepi s :=
  stepF_of_ok (by simpa [Faults] using h)

/-- The map allowing everything never faults. -/
theorem evsOk_all (evs : List Ev) : evsOk MemMap.all evs = true := by
  simp only [evsOk, evOk, List.all_eq_true, List.mem_range]
  intro e _ i _
  cases e.k.dir <;> rfl

theorem stepF_all (s : ArmState) : stepF MemMap.all s = stepi s := stepF_of_ok (evsOk_all _)

theorem execF_all (ai : ArmInst) (s : ArmState) : execF MemMap.all ai s = exec_inst ai s :=
  execF_of_ok (evsOk_all _)

/-! ## A fault -/

theorem execF_fault {mp : MemMap} {ai : ArmInst} {s : ArmState} (h : InstFaults mp ai s) :
    execF mp ai s = write_err memFault s := by
  simp only [InstFaults] at h; simp [execF, h]

theorem stepF_fault {mp : MemMap} {s : ArmState} (h : Faults mp s) :
    stepF mp s = write_err memFault s := by
  simp only [Faults] at h; simp [stepF, h]

/-- At a fault the error is `memFault`. -/
theorem err_stepF_fault {mp : MemMap} {s : ArmState} (h : Faults mp s) :
    r .ERR (stepF mp s) = memFault := by
  rw [stepF_fault h]; simp only [write_err, r_of_w_same]

/-- At a fault every other field (pc, registers, flags, thread pointer) is unchanged. -/
theorem r_stepF_fault {mp : MemMap} {s : ArmState} (h : Faults mp s) {fld : StateField}
    (hf : fld ≠ .ERR) : r fld (stepF mp s) = r fld s := by
  rw [stepF_fault h]; simp only [write_err]; exact r_of_w_different hf

theorem mem_stepF_fault {mp : MemMap} {s : ArmState} (h : Faults mp s) :
    (stepF mp s).mem = s.mem := by
  rw [stepF_fault h]; exact w_mem _ _ _

theorem program_stepF_fault {mp : MemMap} {s : ArmState} (h : Faults mp s) :
    (stepF mp s).program = s.program := by
  rw [stepF_fault h]; exact w_program

/-- **A forbidden byte of an event of the step faults.** -/
theorem faults_of_byte {mp : MemMap} {s : ArmState} {e : Ev} (he : e ∈ stepEvs s) {i : Nat}
    (hi : i < e.n) (hb : (mp (e.addr + BitVec.ofNat 64 i)).allows e.k.dir = false) :
    Faults mp s := by
  simp only [Faults, evsOk, evOk, List.all_eq_false, List.all_eq_true, List.mem_range]
  exact ⟨e, he, fun h => by rw [h i hi] at hb; cases hb⟩

/-- The same for an instruction. -/
theorem instFaults_of_byte {mp : MemMap} {ai : ArmInst} {s : ArmState} {e : Ev}
    (he : e ∈ instEvs ai s) {i : Nat} (hi : i < e.n)
    (hb : (mp (e.addr + BitVec.ofNat 64 i)).allows e.k.dir = false) : InstFaults mp ai s := by
  simp only [InstFaults, evsOk, evOk, List.all_eq_false, List.all_eq_true, List.mem_range]
  exact ⟨e, he, fun h => by rw [h i hi] at hb; cases hb⟩

/-- Conversely, a fault has a forbidden byte. -/
theorem byte_of_faults {mp : MemMap} {s : ArmState} (h : Faults mp s) :
    ∃ e ∈ stepEvs s, ∃ i < e.n, (mp (e.addr + BitVec.ofNat 64 i)).allows e.k.dir = false := by
  simp only [Faults, evsOk, evOk, List.all_eq_false, List.all_eq_true, List.mem_range] at h
  obtain ⟨e, he, hne⟩ := h
  refine ⟨e, he, ?_⟩
  refine Classical.byContradiction fun hn => hne fun i hi => ?_
  cases hx : (mp (e.addr + BitVec.ofNat 64 i)).allows e.k.dir
  · exact absurd ⟨i, hi, hx⟩ hn
  · rfl

/-- **A map allowing more faults less.** -/
theorem evsOk_mono {mp mp' : MemMap} (hle : mp.Le mp') {evs : List Ev}
    (h : evsOk mp evs = true) : evsOk mp' evs = true := by
  simp only [evsOk, evOk, List.all_eq_true, List.mem_range] at h ⊢
  exact fun e he i hi => hle _ _ (h e he i hi)

theorem not_faults_mono {mp mp' : MemMap} (hle : mp.Le mp') {s : ArmState}
    (h : ¬ Faults mp s) : ¬ Faults mp' s := by
  simp only [Faults, Bool.not_eq_false] at h ⊢; exact evsOk_mono hle h

/-! ## Error states and decoded instructions -/

/-- The events of a step at an error state are barrier events, which access no byte. -/
theorem evsOk_errEvs (mp : MemMap) (ai : ArmInst) : evsOk mp (errEvs ai) = true := by
  unfold errEvs
  split
  · split <;> rfl
  · rfl

/-- **An error state stays** (as under `stepi`). -/
theorem stepF_err {mp : MemMap} {s : ArmState} (h : read_err s ≠ .None) : stepF mp s = s := by
  have hok : evsOk mp (stepEvs s) = true := by
    unfold stepEvs
    split
    · simp only [h, ite_false]; exact evsOk_errEvs mp _
    · rfl
  rw [stepF_of_ok hok, stepi_err h]

theorem runF_err {mp : MemMap} {s : ArmState} (h : read_err s ≠ .None) : ∀ n, runF mp n s = s
  | 0 => rfl
  | n + 1 => by simp only [runF, stepF_err h]; exact runF_err h n

/-- **At a decoded instruction of an error-free state, `stepF` is `execF`.** -/
theorem stepF_eq_execF {mp : MemMap} {s : ArmState} {ai : ArmInst} (herr : read_err s = .None)
    (hd : decodeAt s = some ai) : stepF mp s = execF mp ai s := by
  have hev : stepEvs s = instEvs ai s := by simp only [stepEvs, hd, herr, ite_true]
  simp only [stepF, execF, hev, stepi_of_decodeAt herr hd]

theorem faults_iff {mp : MemMap} {s : ArmState} {ai : ArmInst} (herr : read_err s = .None)
    (hd : decodeAt s = some ai) : Faults mp s ↔ InstFaults mp ai s := by
  have hev : stepEvs s = instEvs ai s := by simp only [stepEvs, hd, herr, ite_true]
  simp only [Faults, InstFaults, hev]

/-! ## Runs -/

/-- **A run in which no step faults is the run of `stepi`.** -/
theorem runF_eq_run {mp : MemMap} {n : Nat} {s : ArmState}
    (h : ∀ j < n, ¬ Faults mp (run j s)) : runF mp n s = run n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    have h0 : ¬ Faults mp s := h 0 (Nat.succ_pos n)
    simp only [runF, run, stepF_of_not h0]
    exact ih fun j hj => by
      have := h (j + 1) (Nat.succ_lt_succ hj)
      simpa [run] using this

/-- **The first fault**: if the first `n` steps of `stepi` do not fault and the next one does,
the run with faults is the run of `stepi` up to `n`, then the fault state for ever. -/
theorem runF_fault {mp : MemMap} {n : Nat} {s : ArmState}
    (h : ∀ j < n, ¬ Faults mp (run j s)) (hf : Faults mp (run n s)) (k : Nat) :
    runF mp (n + 1 + k) s = write_err memFault (run n s) := by
  rw [runF_add, runF_succ', runF_eq_run h, stepF_fault hf]
  refine runF_err ?_ k
  simp only [read_err, write_err, r_of_w_same]
  exact memFault_ne_none

end ArmFault
