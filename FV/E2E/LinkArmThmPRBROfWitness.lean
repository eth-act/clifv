import FV.E2E.LinkArmThmPRBROf
import FV.E2E.LinkArmThmPRBRWitness

/-!
# Witnesses for `LinkArmStage2Y.lean` and `LinkArmThmPRBROf.lean`

On `LinkArmProphDetWitness.Lu` (a program with a call `f → h`, no slots):
* `countPRB_Lu`: `CountPRB` holds (no slotted callee);
* `stage2Y_noExt`: stage 2 holds where the CLIF environment has no externs (every `CallPost` is
  vacuous); `calleeOkXPBTGY_Lu`, `calleeTryOkXPBTGY_Lu`, `XPBTGY_sub_Lu` on it (through
  `CalleeOkGP.ofCallSubW`, `CalleeTryOkGP.ofCallSubW`, `csemV_of_call_subW`, `guardRXR_sub`);
* `callStPRB_q_Lu`: the activation's call states see the prophecies;
* `thmPRBR_of_Lu`: `thmPRBR_of` applies at every depth `M + 1` (the induction hypothesis by
  `thmPRBR_LU`, `CountPRB` by `countPRB_Lu`; `DetPRB`, `RetOkPRB`, `Stage2PRB` remain premises).
-/

namespace E2E.LinkArmThmPRBRWitness

open Backend Backend.Proof LinkArmProphDetWitness

/-- **`CountPRB` on `Lu`** (no program callee has slots). -/
theorem countPRB_Lu (M : Nat) : Lu.CountPRB (fun M _ => Lu.K M) M := by
  unfold LinkSys.CountPRB
  intros
  exact absurd ‹Lu.NeedSlots› noSlots_Lu

/-- **Stage 2 without CLIF externs**: every `CallPost` is vacuous. -/
theorem stage2Y_noExt {L : LinkSys} {κ : Nat → Clif.Function → Nat} {M : Nat} {g : Clif.Function}
    {F : BitVec 64 → Prop} {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState}
    {env : Clif.Env} (h0 : ∀ n, env.extern n = none) {cs : Clif.State} {c : BitVec 64}
    {Q : Arm.ArmState → Prop} {n : Nat} : L.Stage2Y κ M g F P R env cs c Q n := by
  intro u w _ _ d uses hn
  refine absurd (fun r => ⟨fun ext _ G sl cm args vals rvals cm' hg _ _ _ _ _ => ?_,
    fun sig _ nm G sl cm u' args vals rvals cm' _ _ hg _ _ _ _ _ _ _ _ => ?_⟩) hn
  · obtain ⟨g0, hg0, -⟩ := Clif.Env.only_extern_eq hg
    rw [h0] at hg0; cases hg0
  · obtain ⟨g0, hg0, -⟩ := Clif.Env.only_extern_eq hg
    rw [h0] at hg0; cases hg0

/-- **`calleeOkXPBTGY` on `Lu`** at depth `M + 1`, at any call states seeing the prophecies,
for the CLIF environment without externs. -/
theorem calleeOkXPBTGY_Lu (M : Nat) (hdet : Lu.DetPRB (fun M _ => Lu.K M) M) {g : Clif.Function}
    (hg : g ∈ Lu.P.funcs) {F G : BitVec 64 → Prop} {ra : BitVec 64} {s w₀ : Arm.ArmState}
    (he : Lu.MachEntry (fun M _ => Lu.K M) (M + 1) g F G ra s w₀)
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {n : Nat}
    {Q : Arm.ArmState → Prop}
    (hQ : ∀ t, Q t → CallPc (Lu.A g).fa (Lu.A g).base (Arm.r .PC t) →
      (∀ f, MaskedReg f → Arm.r f t = Arm.r f (R n)) ∧
        ∀ a, StackBelow (Lu.K (M + 1)) (spv t) a → t.mem a = P n a)
    (cs : Clif.State) (c : BitVec 64) :
    CalleeOkGP Q F (Lu.K (M + 1)) G s (CallAt (Lu.A g).fa (Lu.A g).base)
      ((Lu.XPBTGY (fun M _ => Lu.K M) (M + 1) g F P R Clif.Env.empty cs c).at n) (Lu.hooks (M + 1))
      (Lu.A g).vcp.CallSite (GotV (Lu.A g).vcp) :=
  Lu.calleeOkXPBTGY (M := M + 1) Lu_ok (Lu.budget_K Lu_ok) (fun _ => thmPRBR_LU M) (fun _ => hdet)
    hg he hQ
    (stage2Y_noExt fun _ => rfl)

theorem calleeTryOkXPBTGY_Lu (M : Nat) (hdet : Lu.DetPRB (fun M _ => Lu.K M) M)
    {g : Clif.Function} (hg : g ∈ Lu.P.funcs) {F G : BitVec 64 → Prop} {ra : BitVec 64}
    {s w₀ : Arm.ArmState} (he : Lu.MachEntry (fun M _ => Lu.K M) (M + 1) g F G ra s w₀)
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {n : Nat}
    {Q : Arm.ArmState → Prop}
    (hQ : ∀ t, Q t → CallPc (Lu.A g).fa (Lu.A g).base (Arm.r .PC t) →
      (∀ f, MaskedReg f → Arm.r f t = Arm.r f (R n)) ∧
        ∀ a, StackBelow (Lu.K (M + 1)) (spv t) a → t.mem a = P n a)
    (cs : Clif.State) (c : BitVec 64) :
    CalleeTryOkGP Q F (Lu.K (M + 1)) G s (CallAt (Lu.A g).fa (Lu.A g).base)
      ((Lu.XPBTGY (fun M _ => Lu.K M) (M + 1) g F P R Clif.Env.empty cs c).at n)
      (Lu.hooks (M + 1)) (Lu.A g).vcp.TrySite (GotV (Lu.A g).vcp) :=
  Lu.calleeTryOkXPBTGY (M := M + 1) Lu_ok (Lu.budget_K Lu_ok) (fun _ => thmPRBR_LU M)
    (fun _ => hdet) hg he hQ
    (stage2Y_noExt fun _ => rfl)

/-- `XPBTGY_sub` on `Lu`: without CLIF externs the guarded answers are `XPRBT`'s. -/
theorem XPBTGY_sub_Lu (M : Nat) (g : Clif.Function) (F : BitVec 64 → Prop)
    (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState) (cs : Clif.State) (c : BitVec 64)
    (n : Nat) {u w : Arm.ArmState} (hsw : SameWorld F u w) (d : Option String) (uses : List CV)
    (r : List CV × Arm.ArmState)
    (hr : ((Lu.XPBTGY (fun M _ => Lu.K M) M g F P R Clif.Env.empty cs c).at n).call d uses w =
      some r) :
    (Lu.XPRBT (fun M _ => Lu.K M) M g F P R n).call d uses w = some r :=
  Lu.XPBTGY_sub Lu_ok (Q := fun _ => True) (stage2Y_noExt fun _ => rfl) trivial hsw hr

/-- `callStPRB_q` on `Lu`. -/
theorem callStPRB_q_Lu (M : Nat) (g : Clif.Function) {s w₀ : Arm.ArmState}
    (hsp : spv w₀ = spv s - BitVec.ofNat 64 (frameDrop (Lu.A g).af)) (n : Nat) :
    ∀ t, Lu.CallStPRB (fun M _ => Lu.K M) M g s w₀ n t →
      CallPc (Lu.A g).fa (Lu.A g).base (Arm.r .PC t) →
      (∀ f, MaskedReg f → Arm.r f t = Arm.r f (Lu.RP M g s n)) ∧
        ∀ a, StackBelow (Lu.K M) (spv t) a → t.mem a = Lu.BP M g s n a :=
  Lu.callStPRB_q hsp n

/-- **`thmPRBR_of` applies on `Lu`** at every depth `M + 1`. -/
theorem thmPRBR_of_Lu (M : Nat) (hdet : Lu.DetPRB (fun M _ => Lu.K M) M)
    (hret : Lu.RetOkPRB (fun M _ => Lu.K M) (M + 1))
    (h2 : Lu.Stage2PRB (fun M _ => Lu.K M) (M + 1)) :
    Lu.ThmPRBR (fun M _ => Lu.K M) (M + 1) :=
  Lu.thmPRBR_of (M := M + 1) Lu_ok (Lu.budget_K Lu_ok) (fun _ => thmPRBR_LU M) (fun _ => hdet)
    hret h2
    (countPRB_Lu (M + 1))

end E2E.LinkArmThmPRBRWitness
