import FV.E2E.LinkArmTwinCLock
import FV.E2E.BackendTwoRunLWLslWitness
import FV.E2E.LinkArmTwinCLslWitness

/-!
# Witnesses for the lock-to-twin lemmas on `Lsl` (SEM1 #537), on pairs of distinct states

* `not_callsTo_of_noHook`: code without `bl`/`blr` lines calls no program function;
* `twinState_Lsl`: `twinState_of_lock` for `r` on the image state and the same state with a
  different `x30` (locked at the empty set; distinct states);
* `twinBaseC_Lsl`: `twinBaseC_of_lock` for `r` at return index `0` on two returned entries that
  differ in `x1`.
-/

namespace E2E.LinkSlotSysWitness

open Backend Backend.Proof

/-- **Code without `bl`/`blr` lines calls no program function.** -/
theorem _root_.E2E.LinkSys.not_callsTo_of_noHook (L : LinkSys) {g : Clif.Function}
    (hn : noHookLinesB (L.A g).fa = true) (u : Arm.ArmState) (h : Clif.Function) :
    ¬ L.CallsTo g u h := by
  rintro (⟨n, hi, -⟩ | ⟨⟨x, hi⟩, -⟩)
  · obtain ⟨j, t, hj, -⟩ := insnAt_line_of hi
    exact (noHook_line hn hj).1 n rfl
  · obtain ⟨j, t, hj, -⟩ := insnAt_line_of hi
    exact (noHook_line hn hj).2.1 x rfl

/-- The image state of `Lsl`. -/
noncomputable def uImg : Arm.ArmState := Lsl.withImg Arm.ArmState.default

theorem uImg_x30_ne :
    uImg ≠ Arm.w (.GPR 30#5) (Arm.r (.GPR 30#5) uImg + 1) uImg := by
  intro e
  have := congrArg (Arm.r (.GPR 30#5)) e
  simp only [Arm.r_of_w_same] at this
  exact absurd this (by bv_omega)

/-- **`twinState_of_lock` on two distinct states** (they differ in `x30`). -/
theorem twinState_Lsl :
    let u' := Arm.w (.GPR 30#5) (Arm.r (.GPR 30#5) uImg + 1) uImg
    Arm.r .PC uImg = Arm.r .PC u' ∧ spv uImg = spv u' ∧
      (∀ h, Lsl.CallsTo fR uImg h ↔ Lsl.CallsTo fR u' h) ∧
      ∀ h, Lsl.CallsTo fR uImg h → ∀ a, Lsl.SlotByte h (spv uImg) a →
        uImg.mem (BitVec.ofNat 64 a) = u'.mem (BitVec.ofNat 64 a) := by
  intro u'
  have hmem : ∀ a, uImg.mem a = u'.mem a := fun _ => by
    simp only [u', Arm.ArmState.mem_w_eq_mem]
  have hlk : StEqOutX (fun _ => False) uImg u' :=
    ⟨fun f hf => (Arm.r_of_w_different hf).symm, Arm.w_program.symm, fun a _ => hmem a⟩
  have himg : ∀ a, Lsl.Img a → uImg.mem a = Lsl.imgMem a := fun a ha => by
    rw [uImg, mem_withImg]; simp [ha]
  have hD : Lsl.D < 2 ^ 64 := by native_decide
  exact Lsl.twinState_of_lock Lsl_ok fR_mem
    (List.all_eq_true.mp lsl_blrLow fR fR_mem) (K := Lsl.D) (c := BitVec.ofNat 64 Lsl.D)
    (by simp [Nat.mod_eq_of_lt hD])
    (fun h hc => Lsl_ok.depth h (Lsl.callee_mem hc)) hlk (fun _ _ h => h) himg
    (fun a ha => (hmem a).symm.trans (himg a ha))
    (fun h hc => absurd hc (Lsl.not_callsTo_of_noHook fR_noHookLines _ h))
    (fun h hc => absurd hc (Lsl.not_callsTo_of_noHook fR_noHookLines _ h))

/-- A returned entry of `r`: pc at `x30`, no error, `r`'s code. -/
noncomputable def sRet : Arm.ArmState :=
  let b := Arm.w .ERR .None (Arm.set_program uImg ((Lsl.A fR).fb.program (Lsl.A fR).base))
  Arm.w .PC (Arm.r (.GPR 30#5) b) b

/-- `sRet` with a different `x1`. -/
noncomputable def sRet₁ : Arm.ArmState :=
  Arm.w (.GPR 1#5) (Arm.r (.GPR 1#5) sRet + 1) sRet

theorem sRet_ne : sRet ≠ sRet₁ := by
  intro e
  have := congrArg (Arm.r (.GPR 1#5)) e
  simp only [sRet₁, Arm.r_of_w_same] at this
  exact absurd this (by bv_omega)

theorem retAt_sRet : Lsl.RetAt fR sRet sRet := by
  refine ⟨?_, ?_, ?_, rfl⟩ <;>
    simp [sRet, xreg, Arm.r_of_w_same, Arm.r_of_w_different, Arm.w_program]

theorem retAt_sRet₁ : Lsl.RetAt fR sRet₁ sRet₁ := by
  refine ⟨?_, ?_, ?_, rfl⟩ <;>
    simp [sRet₁, sRet, xreg, Arm.r_of_w_same, Arm.r_of_w_different, Arm.w_program]

theorem lsl_D_lt : Lsl.D < 2 ^ 64 := by native_decide

/-- **`twinBaseC_of_lock` on two distinct entries** (they differ in `x1`; both have returned, the
shared return index is `0`). -/
theorem twinBaseC_Lsl (M : Nat) : Lsl.TwinBaseC M fR sRet sRet₁ :=
  Lsl.twinBaseC_of_lock Lsl_ok fR_mem (List.all_eq_true.mp lsl_blrLow fR fR_mem) (K := Lsl.D)
    (c := BitVec.ofNat 64 Lsl.D) (by simp [Nat.mod_eq_of_lt lsl_D_lt])
    (fun h hc => Lsl_ok.depth h (Lsl.callee_mem hc)) (T := 0)
    (fun _ h => absurd h (Nat.not_lt_zero _)) (fun _ h => absurd h (Nat.not_lt_zero _))
    (fun _ h => absurd h (Nat.not_lt_zero _)) (fun _ h => absurd h (Nat.not_lt_zero _))
    (fun _ h => absurd h (Nat.not_lt_zero _)) (fun _ h => absurd h (Nat.not_lt_zero _))
    ⟨retAt_sRet, retAt_sRet₁⟩

end E2E.LinkSlotSysWitness
