import FV.E2E.LinkArmU

/-!
# Linking at the Arm level with unwinding: where a linked call returns or raises (S10f, #233)

`LinkArm.linkedCall_eq` for the machine with unwinding (`Unw.ArmStepU`): a return (`RetOf`) of the
callee's machine at step `n` that the per-function theorem gives (with `PostTrace`, the return
address `RaOk`) is the callee's first return, so the linked call's hooks (`returnedCall`,
`raisedCall`) are decided by the step into it: not leaving the frame by unwinding (the per-function
theorem's returned case, `¬ UnwExit`) the call returns there; leaving it (its unwound case,
`UnwExit`) the call raises there, the exception object in x0.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- Outside the code of `fa` the machine with unwinding is `ArmStepX` (no call to raise). -/
theorem armStepU_of_insn_none {X : ExtSem} {H : ArmHooks} {U : Unw.UnwHooks} {T : Unw.FnTables}
    {fa : FnAsm} {u : Arm.ArmState} (h : insnAt fa (progBase u) (Arm.r .PC u) = none) :
    Unw.ArmStepU X H U T fa u = ArmStepX X H fa u := by
  simp only [Unw.ArmStepU, h]

/-- **Past the return address the callee's machine with unwinding stops with an error**
(`retStuck`). -/
theorem retStuckU {X : ExtSem} {H : ArmHooks} {U : Unw.UnwHooks} {T : Unw.FnTables} {a : Art}
    {lm : Std.HashMap Lbl Nat}
    (hl : a.fa.layout = .ok a.fb) (hm : labelOffsets a.fa.lines = .ok lm)
    {t : Arm.ArmState} (hprog : t.program = a.fb.program a.base)
    (hra : ∀ k < a.fb.words.size, Arm.r .PC t ≠ a.base + BitVec.ofNat 64 (4 * k)) :
    ∀ n, Arm.r .ERR (runX (Unw.ArmStepU X H U T a.fa) (n + 1) t) ≠ .None := by
  have hins : ∀ u : Arm.ArmState, u.program = a.fb.program a.base → Arm.r .PC u = Arm.r .PC t →
      Unw.ArmStepU X H U T a.fa u = Arm.stepi u := by
    intro u hu hpc
    have hnone : insnAt a.fa (progBase u) (Arm.r .PC u) = none := by
      by_cases hw : a.fb.words.toList = []
      · unfold insnAt
        split
        · rename_i h
          obtain ⟨j, i, t', hj, -⟩ := h
          obtain ⟨-, w, -, hw'⟩ := FnAsm.layout_word hl hm hj rfl
          have := (Array.getElem?_eq_some_iff.mp hw').1
          simp only [Array.toList_eq_nil_iff] at hw
          simp [hw] at this
        · rfl
      · rw [progBase_eq (by rw [hu]; rfl) hw, hpc]
        exact insnAt_none hl hm hra
    rw [armStepU_of_insn_none hnone]
    simp only [ArmStepX, hnone]
  have h1 : ∀ u : Arm.ArmState, u.program = a.fb.program a.base → Arm.r .PC u = Arm.r .PC t →
      Arm.r .ERR (Unw.ArmStepU X H U T a.fa u) ≠ .None := by
    intro u hu hpc
    rw [hins u hu hpc]
    by_cases he : Arm.r .ERR u = .None
    · unfold Arm.stepi
      simp only [Arm.read_err] at he ⊢
      rw [he]
      simp only
      have hf : Arm.fetch_inst (Arm.read_pc u) u = none := by
        unfold Arm.fetch_inst
        rw [hu]
        simp only [Arm.read_pc] at *
        rw [hpc]
        exact program_find_none hra
      rw [hf]
      simp [Arm.r, Arm.write_err, Arm.read_base_error, Arm.write_base_error]
    · rw [stepi_err he]; exact he
  have hfix : ∀ u : Arm.ArmState, u.program = a.fb.program a.base → Arm.r .PC u = Arm.r .PC t →
      Arm.r .ERR u ≠ .None → Unw.ArmStepU X H U T a.fa u = u := fun u hu hpc he => by
    rw [hins u hu hpc, stepi_err he]
  have hstep1 : (Unw.ArmStepU X H U T a.fa t).program = a.fb.program a.base ∧
      Arm.r .PC (Unw.ArmStepU X H U T a.fa t) = Arm.r .PC t := by
    rw [hins t hprog rfl]
    by_cases he : Arm.r .ERR t = .None
    · unfold Arm.stepi
      simp only [Arm.read_err] at he ⊢
      rw [he]
      simp only
      have hf : Arm.fetch_inst (Arm.read_pc t) t = none := by
        unfold Arm.fetch_inst
        rw [hprog]
        exact program_find_none hra
      rw [hf]
      simp only [Arm.write_err]
      exact ⟨by rw [Arm.w_program]; exact hprog, Arm.r_of_w_different (by simp)⟩
    · rw [stepi_err he]; exact ⟨hprog, rfl⟩
  have hP : ∀ m, (runX (Unw.ArmStepU X H U T a.fa) (m + 1) t).program = a.fb.program a.base ∧
      Arm.r .PC (runX (Unw.ArmStepU X H U T a.fa) (m + 1) t) = Arm.r .PC t ∧
      Arm.r .ERR (runX (Unw.ArmStepU X H U T a.fa) (m + 1) t) ≠ .None := by
    intro m
    induction m with
    | zero => exact ⟨hstep1.1, hstep1.2, h1 t hprog rfl⟩
    | succ m ih =>
      have e : runX (Unw.ArmStepU X H U T a.fa) (m + 1 + 1) t =
          Unw.ArmStepU X H U T a.fa (runX (Unw.ArmStepU X H U T a.fa) (m + 1) t) := by
        rw [runX_add _ (m + 1) 1]; rfl
      rw [e, hfix _ ih.1 ih.2.1 ih.2.2]
      exact ih
  exact fun n => (hP n).2.2

/-- **No earlier return**: a return of the callee's machine with unwinding at step `n` with
`PostTrace` (and the return address `RaOk`) is its first. -/
theorem noEarlierRetU {X : ExtSem} {H : ArmHooks} {U : Unw.UnwHooks} {T : Unw.FnTables} {a : Art}
    {lm : Std.HashMap Lbl Nat} (hl : a.fa.layout = .ok a.fb) (hm : labelOffsets a.fa.lines = .ok lm)
    {s : Arm.ArmState} (hra : RaOk a (Arm.r .PC s)) (hfd : 0 < frameDrop a.af)
    (hfd' : frameDrop a.af < 2 ^ 64) {n : Nat}
    (htr : PostTrace a.fa a.af a.base (Unw.ArmStepU X H U T a.fa) (enterAt a s) n)
    (hret : RetOf a s (runX (Unw.ArmStepU X H U T a.fa) n (enterAt a s))) :
    ∀ i < n, ¬ RetOf a s (runX (Unw.ArmStepU X H U T a.fa) i (enterAt a s)) := by
  intro i hi hri
  rcases hra with hra | ⟨hcp, hne⟩
  · have := retStuckU (X := X) (H := H) (U := U) (T := T) hl hm hri.2.2.1 (by rw [hri.1]; exact hra)
      (n - i - 1)
    rw [← runX_add, show i + (n - i - 1 + 1) = n by omega] at this
    exact this hret.2.1
  · rcases Nat.eq_zero_or_pos i with rfl | hi0
    · apply hne
      rw [← hri.1]
      simp [runX, enterAt, Arm.r_of_w_same]
    · have hsp := htr i hi0 hi ⟨_, hcp, hri.1⟩
      have hse : spv (enterAt a s) = spv s := by
        simp only [spv, enterAt]
        rw [Arm.r_of_w_different (by simp), Arm.r_of_w_different (by simp), r_set_program]
      rw [hri.2.2.2, hse] at hsp
      have e := congrArg BitVec.toNat hsp
      have hlt := (spv s).isLt
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfd'] at e
      omega

/-- The first return of the callee's machine is the given one. -/
theorem firstNat_ret {M : Arm.ArmState → Arm.ArmState} {a : Art} {s : Arm.ArmState} {n : Nat}
    (hret : RetOf a s (runX M n (enterAt a s)))
    (hfirst : ∀ i < n, ¬ RetOf a s (runX M i (enterAt a s)))
    (h : ∃ n, RetOf a s (runX M n (enterAt a s))) : firstNat _ h = n := by
  obtain ⟨hp, hmin⟩ := firstNat_spec _ h
  rcases Nat.lt_trichotomy (firstNat _ h) n with e | e | e
  · exact absurd hp (hfirst _ e)
  · exact e
  · exact absurd hret (hmin n e)

/-- **Where a linked call with unwinding returns**: at a return of the callee's machine at step
`n` (with `PostTrace`, `RaOk`) whose step is not an unwinding one (`¬ UnwExit`), the call does not
raise and returns there. -/
theorem returnedCall_eq {X : ExtSem} {H : ArmHooks} {U : Unw.UnwHooks} {T : Unw.FnTables} {a : Art}
    {lm : Std.HashMap Lbl Nat} (hl : a.fa.layout = .ok a.fb) (hm : labelOffsets a.fa.lines = .ok lm)
    {s : Arm.ArmState} (hra : RaOk a (Arm.r .PC s)) (hfd : 0 < frameDrop a.af)
    (hfd' : frameDrop a.af < 2 ^ 64) {n : Nat}
    (htr : PostTrace a.fa a.af a.base (Unw.ArmStepU X H U T a.fa) (enterAt a s) n)
    (hret : RetOf a s (runX (Unw.ArmStepU X H U T a.fa) n (enterAt a s)))
    (hnu : ¬ UnwExit U T a.fa (runX (Unw.ArmStepU X H U T a.fa) (n - 1) (enterAt a s))) :
    ¬ ExitU (Unw.ArmStepU X H U T a.fa) U T a s ∧
      returnedCall (Unw.ArmStepU X H U T a.fa) U T a s =
        Arm.set_program (runX (Unw.ArmStepU X H U T a.fa) n (enterAt a s)) s.program ∧
      raisedCall (Unw.ArmStepU X H U T a.fa) U T a s = none := by
  have hfirst := noEarlierRetU hl hm hra hfd hfd' htr hret
  have hx : ¬ ExitU (Unw.ArmStepU X H U T a.fa) U T a s := by
    rintro ⟨h, -, hu⟩
    rw [firstNat_ret hret hfirst h] at hu
    exact hnu hu
  refine ⟨hx, ?_, by simp only [raisedCall, hx, ↓reduceIte]⟩
  simp only [returnedCall, hx, ↓reduceIte]
  exact linkedCall_first hret hfirst

/-- **Where a linked call with unwinding raises**: at a return of the callee's machine at step
`n > 0` (with `PostTrace`, `RaOk`) whose step leaves the callee's frame by unwinding (`UnwExit`),
the call raises there, the exception object in x0. -/
theorem raisedCall_eq {X : ExtSem} {H : ArmHooks} {U : Unw.UnwHooks} {T : Unw.FnTables} {a : Art}
    {lm : Std.HashMap Lbl Nat} (hl : a.fa.layout = .ok a.fb) (hm : labelOffsets a.fa.lines = .ok lm)
    {s : Arm.ArmState} (hra : RaOk a (Arm.r .PC s)) (hfd : 0 < frameDrop a.af)
    (hfd' : frameDrop a.af < 2 ^ 64) {n : Nat}
    (htr : PostTrace a.fa a.af a.base (Unw.ArmStepU X H U T a.fa) (enterAt a s) n)
    (hret : RetOf a s (runX (Unw.ArmStepU X H U T a.fa) n (enterAt a s))) (hn0 : 0 < n)
    (hu : UnwExit U T a.fa (runX (Unw.ArmStepU X H U T a.fa) (n - 1) (enterAt a s))) :
    ExitU (Unw.ArmStepU X H U T a.fa) U T a s ∧
      raisedCall (Unw.ArmStepU X H U T a.fa) U T a s =
        some (xreg 0 (runX (Unw.ArmStepU X H U T a.fa) n (enterAt a s)),
          Arm.set_program (runX (Unw.ArmStepU X H U T a.fa) n (enterAt a s)) s.program) := by
  have hfirst := noEarlierRetU hl hm hra hfd hfd' htr hret
  have hex : ∃ n, RetOf a s (runX (Unw.ArmStepU X H U T a.fa) n (enterAt a s)) := ⟨n, hret⟩
  have hx : ExitU (Unw.ArmStepU X H U T a.fa) U T a s :=
    ⟨hex, by rw [firstNat_ret hret hfirst hex]; exact hn0,
      by rw [firstNat_ret hret hfirst hex]; exact hu⟩
  refine ⟨hx, ?_⟩
  simp only [raisedCall, hx, ↓reduceIte, linkedCall_first hret hfirst]
  congr 2
  simp only [xreg]
  rw [r_set_program]

end E2E
