import FV.E2E.LinkArmBaseDet
import FV.E2E.LinkArmProph
import FV.Concurrency.VCodeThread

/-!
# One machine step from two states equal but for unread memory (SEM1 step 2o, §5.7)

The single-step half of the two-run lock-step of prophecy determinism: two states equal but for
memory in a set `Z` (`StEqOut Z`) take equal steps, but for `Z`, when the step reads nothing in
`Z`. The instruction footprints (`FV/Concurrency/ArmInstFoot.lean`: `footprint_exec_inst`,
`instEvs`, `agrees_instEvs`) give the instruction case.

* `ReadsAvoid Z evs`: no read event of `evs` touches `Z`;
* `applyW_congr_out`: writing the same events into two memories equal outside `Z` keeps them so;
* `stEqOut_exec_inst`, `stEqOut_stepi`: an instruction, and `Arm.stepi`;
* `stEqOut_w`: a register write;
* `stEqOut_armStepX`: a step of `ArmStepX` at an unhooked line (no `bl`/`blr`, no TLS descriptor
  call), with the hooks' and the extern semantics' parts excluded;
* `stEqOut_armStepX_call`: at a `bl`/`blr`/TLS line, a hook that keeps `StEqOut Z` (a base hook
  under `HookDet` with `Z` below `sp`, a program call by the callee's determinism) does.
-/

namespace E2E

open Arm Backend Backend.Proof Concurrency.ArmFoot Concurrency.ArmThread Concurrency.ArmInstFoot
  Concurrency.VCodeThread

/-- No read event of `evs` touches an address of `Z`. -/
def ReadsAvoid (Z : BitVec 64 → Prop) (evs : List Ev) : Prop :=
  ∀ e ∈ evs, e.k.dir = .R → ∀ k < e.n, ¬ Z (e.addr + BitVec.ofNat 64 k)

theorem write_store_congr_out {Z : BitVec 64 → Prop} {m m' : Memory}
    (h : ∀ x, ¬ Z x → m x = m' x) (a : BitVec 64) (b : BitVec 8) :
    ∀ x, ¬ Z x → write_store a b m x = write_store a b m' x := by
  intro x hx
  simp only [write_store]
  split
  · rfl
  · exact h x hx

theorem writeM_congr_out {Z : BitVec 64 → Prop} :
    ∀ (n : Nat) (a : BitVec 64) (v : BitVec (n * 8)) {m m' : Memory},
      (∀ x, ¬ Z x → m x = m' x) → ∀ x, ¬ Z x → Concurrency.ArmFoot.writeM n a v m x = Concurrency.ArmFoot.writeM n a v m' x
  | 0, _, _, _, _, h => h
  | n + 1, a, v, _, _, h => by
    simp only [Concurrency.ArmFoot.writeM]
    exact writeM_congr_out n _ _ (write_store_congr_out h a _)

theorem applyW_congr_out {Z : BitVec 64 → Prop} :
    ∀ (evs : List Ev) {m m' : Memory},
      (∀ x, ¬ Z x → m x = m' x) → ∀ x, ¬ Z x → applyW evs m x = applyW evs m' x
  | [], _, _, h => h
  | e :: es, m, m', h => by
    simp only [applyW]
    apply applyW_congr_out es
    split
    · exact writeM_congr_out _ _ _ h
    · exact h

/-- Read events avoiding `Z` hold in a memory equal to `s`'s outside `Z`. -/
theorem agrees_of_avoid {Z : BitVec 64 → Prop} {evs : List Ev} {m m' : Memory}
    (hA : Agrees evs m) (hZ : ReadsAvoid Z evs) (h : ∀ x, ¬ Z x → m x = m' x) : Agrees evs m' := by
  intro e he hr
  rw [← hA e he hr]
  exact (readM_congr e.n e.addr m m' fun k hk => h _ (hZ e he hr k hk)).symm

/-- `t` is `s` with `t`'s memory when they have the same registers and program. -/
theorem eq_setMem_of {s t : ArmState} (hr : ∀ f, r f s = r f t) (hp : s.program = t.program) :
    t = Concurrency.ArmFoot.setMem t.mem s :=
  state_eq_of (fun f => (hr f).symm.trans (by cases f <;> unfold Arm.r <;> rfl)) hp.symm (fun _ => rfl)

/-- **An instruction from two states equal but for memory in `Z` it does not read gives states
equal but for `Z`.** -/
theorem stEqOut_exec_inst {Z : BitVec 64 → Prop} {s t : ArmState} (ai : ArmInst)
    (h : StEqOut Z s t) (hZ : ReadsAvoid Z (instEvs ai s)) :
    StEqOut Z (exec_inst ai s) (exec_inst ai t) := by
  have hfp := footprint_exec_inst ai s
  have hA := agrees_instEvs ai s
  have hA' := agrees_of_avoid hA hZ h.2.2
  have e1 := hfp s.mem hA
  have e2 := hfp t.mem hA'
  rw [setMem_self] at e1
  rw [← eq_setMem_of h.1 h.2.1] at e2
  rw [e1, e2]
  refine ⟨fun f => ?_, rfl, fun x hx => ?_⟩
  · cases f <;> unfold Arm.r <;> rfl
  · exact applyW_congr_out _ h.2.2 x hx

/-- The read events of `Arm.stepi`'s instruction at `s` (none when it does not execute one). -/
def stepiEvs (s : ArmState) : List Ev :=
  match read_err s with
  | StateError.None =>
    (match fetch_inst (read_pc s) s with
      | none => []
      | some i => (match decode_raw_inst i with
        | none => []
        | some ai => instEvs ai s))
  | _ => []

theorem stEqOut_write_err {Z : BitVec 64 → Prop} {s t : ArmState} (h : StEqOut Z s t)
    (e : StateError) : StEqOut Z (write_err e s) (write_err e t) := by
  refine ⟨r_w_congr h.1 .ERR e, ?_, fun x hx => ?_⟩
  · simp only [write_err]; rw [Arm.w_program, Arm.w_program]; exact h.2.1
  · simp only [write_err]
    rw [Arm.mem_w_of_mem_eq rfl, Arm.mem_w_of_mem_eq rfl]; exact h.2.2 x hx

/-- **`Arm.stepi` from two states equal but for memory in `Z` it does not read.** -/
theorem stEqOut_stepi {Z : BitVec 64 → Prop} {s t : ArmState} (h : StEqOut Z s t)
    (hZ : ReadsAvoid Z (stepiEvs s)) : StEqOut Z (stepi s) (stepi t) := by
  have herr : read_err s = read_err t := h.1 .ERR
  have hpc : read_pc s = read_pc t := h.1 .PC
  have hf : ∀ a, fetch_inst a s = fetch_inst a t := fun a => by
    simp only [fetch_inst, h.2.1]
  simp only [stepi, ← herr, ← hpc, ← hf]
  unfold stepiEvs at hZ
  cases he : read_err s with
  | None =>
    rw [he] at hZ
    simp only
    cases hfe : fetch_inst (read_pc s) s with
    | none => exact stEqOut_write_err h _
    | some i =>
      rw [hfe] at hZ
      simp only
      cases hd : decode_raw_inst i with
      | none => exact stEqOut_write_err h _
      | some ai =>
        simp only [hd] at hZ
        exact stEqOut_exec_inst ai h hZ
  | _ => exact h

theorem stEqOut_w {Z : BitVec 64 → Prop} {s t : ArmState} (h : StEqOut Z s t)
    (g : StateField) (v : state_value g) : StEqOut Z (Arm.w g v s) (Arm.w g v t) := by
  refine ⟨r_w_congr h.1 g v, ?_, fun x hx => ?_⟩
  · rw [Arm.w_program, Arm.w_program]; exact h.2.1
  · rw [Arm.mem_w_of_mem_eq rfl, Arm.mem_w_of_mem_eq rfl]; exact h.2.2 x hx

/-- The line kinds `ArmStepX` hands to a hook. -/
def HookedInsn : Option Insn → Prop
  | some (.bl _) => True
  | some (.blr _) => True
  | some (.ldrTlsDescLo12 _ _ _) => True
  | _ => False

/-- **A step of `ArmStepX` at an unhooked line from two states equal but for memory in `Z` it
does not read.** -/
theorem stEqOut_armStepX {X : ExtSem} {H : ArmHooks} {fa : FnAsm} {Z : BitVec 64 → Prop}
    {s t : ArmState} (h : StEqOut Z s t)
    (hn : ¬ HookedInsn (insnAt fa (progBase s) (r .PC s)))
    (hZ : ReadsAvoid Z (stepiEvs s)) :
    StEqOut Z (ArmStepX X H fa s) (ArmStepX X H fa t) := by
  have hpb : progBase s = progBase t := by simp only [progBase, h.2.1]
  have hpc : r .PC s = r .PC t := h.1 .PC
  simp only [ArmStepX, ← hpb, ← hpc]
  split
  all_goals first
    | (exfalso; apply hn; rename_i hh; rw [hh]; exact trivial)
    | exact stEqOut_w (stEqOut_w h _ _) _ _
    | exact stEqOut_w h _ _
    | exact stEqOut_stepi h hZ

/-- **A step of `ArmStepX` keeps `StEqOut Z` when the hooks do** (and the instruction does not
read `Z`). -/
theorem stEqOut_armStepX_call {X : ExtSem} {H : ArmHooks} {fa : FnAsm} {Z : BitVec 64 → Prop}
    {s t : ArmState} (h : StEqOut Z s t)
    (hc : ∀ d, StEqOut Z (H.call d s) (H.call d t))
    (ht : ∀ n r, StEqOut Z (H.tls n r s) (H.tls n r t)) (hZ : ReadsAvoid Z (stepiEvs s)) :
    StEqOut Z (ArmStepX X H fa s) (ArmStepX X H fa t) := by
  have hpb : progBase s = progBase t := by simp only [progBase, h.2.1]
  have hpc : r .PC s = r .PC t := h.1 .PC
  simp only [ArmStepX, ← hpb, ← hpc]
  split
  all_goals first
    | exact hc _
    | exact ht _ _
    | exact stEqOut_w (stEqOut_w h _ _) _ _
    | exact stEqOut_w h _ _
    | exact stEqOut_stepi h hZ

end E2E
