import FV.E2E.LinkArmProphThm
import FV.E2E.LinkArmProphWitness

/-!
# Witnesses for the linking statement with prophecies (`FV/E2E/LinkArmProphThm.lean`)

* the prophecy of a run: a one-line function `bl f` at `0x1000` and a machine that stays at its
  call (every state a call state): the calls before step `i` are `i`, call number `3`'s memory is
  the state's, and `prophOf` is a prophecy of the run (`ProphOk`) while a wrong one is not;
* `XPI`'s call number `3` is `XP … 3` (on `LinkArmProphWitness.L0`);
* `ThmP` at every depth for `LinkWitness.L`'s default callee runs (`LinkSys.std`, the budget
  `K`): its `Ok` (`L_ok`, `native_decide` checks), `crunOk_std`, `budget_K`.
-/

namespace E2E.LinkArmProphThmWitness

open Backend Backend.Proof LinkWitness LinkArmProphWitness

/-- A function whose only instruction is `bl f`. -/
def faC : FnAsm := { name := "c", k := 0, lines := #[.ins (.bl "f")], size := 4, traps := [] }

/-- A state at that call (base `0x1000`) with `sp = 0x8000`. -/
def u0 : Arm.ArmState := Arm.w .PC 0x1000#64 (Arm.w (.GPR 31#5) 0x8000#64 Arm.ArmState.default)

theorem runX_id : ∀ (i : Nat) (s : Arm.ArmState), runX id i s = s
  | 0, _ => rfl
  | i + 1, s => runX_id i s

theorem callPc_u0 (i : Nat) : CallPc faC 0x1000#64 (Arm.r .PC (runX id i u0)) := by
  rw [runX_id, u0, Arm.r_of_w_same]
  exact ⟨0, .bl "f", none, rfl, .inl ⟨_, rfl⟩, by simp [lineOffset]⟩

theorem callsBefore_u0 : ∀ i, callsBefore id faC 0x1000#64 u0 i = i
  | 0 => rfl
  | i + 1 => by simp only [callsBefore, callsBefore_u0 i, callPc_u0 i, ↓reduceIte]

theorem callsBefore_mono_u0 : callsBefore id faC 0x1000#64 u0 2 ≤ callsBefore id faC 0x1000#64 u0 5 :=
  callsBefore_mono id faC 0x1000#64 u0 (by omega)

theorem callsBefore_lt_u0 : callsBefore id faC 0x1000#64 u0 1 < callsBefore id faC 0x1000#64 u0 4 :=
  callsBefore_lt (callPc_u0 1) (by omega)

theorem prophOf_u0 : prophOf id faC 0x1000#64 u0 3 = u0.mem := by
  have h := prophOf_call (callPc_u0 3)
  rwa [callsBefore_u0, runX_id] at h

theorem spv_u0 : spv u0 = 0x8000#64 := by
  simp only [u0, spv]
  rw [Arm.r_of_w_different (by simp), Arm.r_of_w_same]

theorem prophOk_u0 : ProphOk 16 0x8000#64 id faC 0x1000#64 u0 (prophOf id faC 0x1000#64 u0) :=
  prophOk_prophOf 16 0x8000#64 id faC 0x1000#64 u0

/-- A prophecy other than the run's bytes below `sp` is not one. -/
theorem not_prophOk_u0 :
    ¬ ProphOk 16 0x8000#64 id faC 0x1000#64 u0 (fun _ a => u0.mem a + 1#8) := by
  intro h
  have h1 := h 0 (callPc_u0 0) (by rw [runX_id, spv_u0]) 0x7FFF#64 (by
    unfold StackBelow
    have h1 : (0x7FFF#64).toNat = 32767 := rfl
    have h2 : (0x8000#64).toNat = 32768 := rfl
    rw [h1, h2]; omega)
  rw [runX_id] at h1
  simp only at h1
  bv_omega

theorem XPI_at_L0 (F : BitVec 64 → Prop) :
    (L0.XPI κ16 1 fF F (fun _ => PAB)).at 3 = L0.XP κ16 1 fF F (fun _ => PAB) 3 :=
  L0.XPI_at 1 fF F _ 3

/-- `LinkWitness.L`'s default callee runs. -/
def Ls : LinkSys := (L (Img P A)).std

theorem Ls_ok : Ls.Ok := (L_ok (Img P A) fun _ h => h).withCrun _

instance : Ls.CrunOk := (L (Img P A)).crunOk_std (L_ok (Img P A) fun _ h => h)

/-- **`ThmP` holds at every depth for the witness program.** -/
theorem thmP_Ls (M : Nat) : Ls.ThmP (fun M _ => Ls.K M) M :=
  Ls.thmP Ls_ok (Ls.budget_K Ls_ok) M

/-- Today's statement at depth `2` gives the one with prophecies. -/
theorem thm_thmP_Ls : Ls.ThmP (fun M _ => Ls.K M) 2 :=
  LinkSys.Thm.thmP Ls (Ls.thm Ls_ok (Ls.budget_K Ls_ok) 2)

end E2E.LinkArmProphThmWitness
