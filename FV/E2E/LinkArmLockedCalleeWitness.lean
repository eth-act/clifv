import FV.E2E.LinkArmLockedCallee
import FV.E2E.LinkSlotSysWitness
import FV.E2E.BackendTwoRunNIUWitness

/-!
# Witnesses: the `DetPRBR` form of the `x30`-exempt call contracts and the second activation's
contracts at its locked call states (SEM1 #537, #713, #719; `LinkArmProgOsPRBRL30.lean`,
`LinkArmLockedCallee.lean`)

On the slotted system `Lsl` (`Ok`, budget discharged):

* `useVals_eq_x30`: the operand values of a checked instruction on two distinct states that
  differ in `x30` (`useVals_eq_of_x30`);
* `calleeOkPRBRL30R_Lsl`, `calleeTryOkPRBRL30R_Lsl`, `calleeOkXPBTGZS30R_Lsl`,
  `calleeTryOkXPBTGZS30R_Lsl`: the `DetPRBR`-form `x30`-exempt contracts;
* `lockedCall_Lsl`: `LinkSys.lockedCall` with the second run locked to the first by
  `lockedUpTo_self` (no hypothesis on the lock);
* `calleeOkLockedR_Lsl`, `calleeTryOkLockedR_Lsl`: the second activation's contracts at its
  locked call states (`ThmPRBRL`/`DetPRBR` below `M`, the canonical stage 2 remain).
-/

namespace E2E.LinkSlotSysWitness

open Backend Backend.Proof Backend.Proof.Driver

/-- **`useVals_eq_of_x30` on two distinct states** (they differ in `x30`). -/
theorem useVals_eq_x30 {c : CheckCtx} {wh : String} {ops : Array Operand} {regs : Array Reg}
    {clob : List Reg} (hst : c.checkStatic wh ops (regs.map .reg) clob = .ok ())
    (u : Arm.ArmState) (v : BitVec 64) :
    useVals ops regs u = useVals ops regs (Arm.w (.GPR 30#5) v u) :=
  useVals_eq_of_x30 hst fun f hf => (Arm.r_of_w_different hf).symm

theorem calleeOkPRBRL30R_Lsl {M : Nat}
    (ih : 0 < M → Lsl.ThmPRBRL (fun M _ => Lsl.K M) (M - 1))
    (hdet : 0 < M → Lsl.DetPRBR (fun M _ => Lsl.K M) (M - 1)) {g : Clif.Function}
    (hg : g ∈ Lsl.P.funcs) {F G : BitVec 64 → Prop} {ra : BitVec 64} {s w₀ : Arm.ArmState}
    (he : Lsl.MachEntry (fun M _ => Lsl.K M) M g F G ra s w₀)
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {n : Nat}
    {Q : Arm.ArmState → Prop}
    (hQ : ∀ t, Q t → CallPc (Lsl.A g).fa (Lsl.A g).base (Arm.r .PC t) →
      (∀ f, MaskedReg f → f ≠ .GPR 30#5 → Arm.r f t = Arm.r f (R n)) ∧
        ∀ a, StackBelow ((fun M _ => Lsl.K M) M g) (spv t) a → t.mem a = P n a) :
    CalleeOkGP Q F ((fun M _ => Lsl.K M) M g) G s (CallAt (Lsl.A g).fa (Lsl.A g).base)
      (Lsl.XPRBT (fun M _ => Lsl.K M) M g F P R n) (Lsl.hooks M)
      (Lsl.A g).vcp.CallSite (GotV (Lsl.A g).vcp) :=
  Lsl.calleeOkPRBRL30R Lsl_ok (Lsl.budget_K Lsl_ok) ih hdet hg he hQ

theorem calleeTryOkPRBRL30R_Lsl {M : Nat}
    (ih : 0 < M → Lsl.ThmPRBRL (fun M _ => Lsl.K M) (M - 1))
    (hdet : 0 < M → Lsl.DetPRBR (fun M _ => Lsl.K M) (M - 1)) {g : Clif.Function}
    (hg : g ∈ Lsl.P.funcs) {F G : BitVec 64 → Prop} {ra : BitVec 64} {s w₀ : Arm.ArmState}
    (he : Lsl.MachEntry (fun M _ => Lsl.K M) M g F G ra s w₀)
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {n : Nat}
    {Q : Arm.ArmState → Prop}
    (hQ : ∀ t, Q t → CallPc (Lsl.A g).fa (Lsl.A g).base (Arm.r .PC t) →
      (∀ f, MaskedReg f → f ≠ .GPR 30#5 → Arm.r f t = Arm.r f (R n)) ∧
        ∀ a, StackBelow ((fun M _ => Lsl.K M) M g) (spv t) a → t.mem a = P n a) :
    CalleeTryOkGP Q F ((fun M _ => Lsl.K M) M g) G s (CallAt (Lsl.A g).fa (Lsl.A g).base)
      (Lsl.XPRBT (fun M _ => Lsl.K M) M g F P R n) (Lsl.hooks M)
      (Lsl.A g).vcp.TrySite (GotV (Lsl.A g).vcp) :=
  Lsl.calleeTryOkPRBRL30R Lsl_ok (Lsl.budget_K Lsl_ok) ih hdet hg he hQ

theorem calleeOkXPBTGZS30R_Lsl {M : Nat}
    (ih : 0 < M → Lsl.ThmPRBRL (fun M _ => Lsl.K M) (M - 1))
    (hdet : 0 < M → Lsl.DetPRBR (fun M _ => Lsl.K M) (M - 1)) {g : Clif.Function}
    (hg : g ∈ Lsl.P.funcs) {F G : BitVec 64 → Prop} {ra : BitVec 64} {s w₀ : Arm.ArmState}
    (he : Lsl.MachEntry (fun M _ => Lsl.K M) M g F G ra s w₀)
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {n : Nat}
    {Q : Arm.ArmState → Prop}
    (hQ : ∀ t, Q t → CallPc (Lsl.A g).fa (Lsl.A g).base (Arm.r .PC t) →
      (∀ f, MaskedReg f → f ≠ .GPR 30#5 → Arm.r f t = Arm.r f (R n)) ∧
        ∀ a, StackBelow ((fun M _ => Lsl.K M) M g) (spv t) a → t.mem a = P n a)
    {env : Clif.Env} {cs : Clif.State} {c : BitVec 64}
    (h2 : Lsl.Stage2ZS (fun M _ => Lsl.K M) M g F P R env cs c Q n) :
    CalleeOkGP Q F ((fun M _ => Lsl.K M) M g) G s (CallAt (Lsl.A g).fa (Lsl.A g).base)
      ((Lsl.XPBTGY (fun M _ => Lsl.K M) M g F P R env cs c).at n) (Lsl.hooks M)
      (Lsl.A g).vcp.CallSite (GotV (Lsl.A g).vcp) :=
  Lsl.calleeOkXPBTGZS30R Lsl_ok (Lsl.budget_K Lsl_ok) ih hdet hg he hQ h2

theorem calleeTryOkXPBTGZS30R_Lsl {M : Nat}
    (ih : 0 < M → Lsl.ThmPRBRL (fun M _ => Lsl.K M) (M - 1))
    (hdet : 0 < M → Lsl.DetPRBR (fun M _ => Lsl.K M) (M - 1)) {g : Clif.Function}
    (hg : g ∈ Lsl.P.funcs) {F G : BitVec 64 → Prop} {ra : BitVec 64} {s w₀ : Arm.ArmState}
    (he : Lsl.MachEntry (fun M _ => Lsl.K M) M g F G ra s w₀)
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {n : Nat}
    {Q : Arm.ArmState → Prop}
    (hQ : ∀ t, Q t → CallPc (Lsl.A g).fa (Lsl.A g).base (Arm.r .PC t) →
      (∀ f, MaskedReg f → f ≠ .GPR 30#5 → Arm.r f t = Arm.r f (R n)) ∧
        ∀ a, StackBelow ((fun M _ => Lsl.K M) M g) (spv t) a → t.mem a = P n a)
    {env : Clif.Env} {cs : Clif.State} {c : BitVec 64}
    (h2 : Lsl.Stage2ZS (fun M _ => Lsl.K M) M g F P R env cs c Q n) :
    CalleeTryOkGP Q F ((fun M _ => Lsl.K M) M g) G s (CallAt (Lsl.A g).fa (Lsl.A g).base)
      ((Lsl.XPBTGY (fun M _ => Lsl.K M) M g F P R env cs c).at n) (Lsl.hooks M)
      (Lsl.A g).vcp.TrySite (GotV (Lsl.A g).vcp) :=
  Lsl.calleeTryOkXPBTGZS30R Lsl_ok (Lsl.budget_K Lsl_ok) ih hdet hg he hQ h2

/-- **`lockedCall` with the run locked to itself** (`lockedUpTo_self`): a call state of the
canonical run is the canonical call-`n` state. -/
theorem lockedCall_Lsl {M : Nat} {g : Clif.Function} {F G : BitVec 64 → Prop} {ra : BitVec 64}
    {s w₀ : Arm.ArmState} {D : BitVec 64 → Prop}
    (hME : Lsl.MachEntryPR (fun M _ => Lsl.K M) M g F G ra s w₀ (Lsl.BP M g s) (Lsl.RP M g s))
    (hD : ∀ a, D a → F a) (i : Nat)
    (hsp : spOf (runX (ArmStepX Lsl.Xb (Lsl.hooks M) (Lsl.A g).fa) i s) =
      spv s - BitVec.ofNat 64 (frameDrop (Lsl.A g).af)) :
    ∃ u₀, Lsl.CallStPRB (fun M _ => Lsl.K M) M g s w₀
        (callsBefore (ArmStepX Lsl.Xb (Lsl.hooks M) (Lsl.A g).fa) (Lsl.A g).fa (Lsl.A g).base s i)
        u₀ ∧
      (∀ f, f ≠ .GPR 30#5 → Arm.r f (runX (ArmStepX Lsl.Xb (Lsl.hooks M) (Lsl.A g).fa) i s) =
        Arm.r f u₀) ∧
      (runX (ArmStepX Lsl.Xb (Lsl.hooks M) (Lsl.A g).fa) i s).program = u₀.program ∧
      (∀ a, StackBelow ((fun M _ => Lsl.K M) M g)
        (spv (runX (ArmStepX Lsl.Xb (Lsl.hooks M) (Lsl.A g).fa) i s)) a →
        (runX (ArmStepX Lsl.Xb (Lsl.hooks M) (Lsl.A g).fa) i s).mem a = u₀.mem a) ∧
      ∀ a, ¬ F a → (runX (ArmStepX Lsl.Xb (Lsl.hooks M) (Lsl.A g).fa) i s).mem a = u₀.mem a :=
  Lsl.lockedCall rfl hME rfl hD hsp (lockedUpTo_self _ _ _ _ _ F D s i)

theorem calleeOkLockedR_Lsl {M : Nat}
    (ih : 0 < M → Lsl.ThmPRBRL (fun M _ => Lsl.K M) (M - 1))
    (hdet : 0 < M → Lsl.DetPRBR (fun M _ => Lsl.K M) (M - 1))
    {g : Clif.Function} (hg : g ∈ Lsl.P.funcs) {F G G' : BitVec 64 → Prop} {ra ra' : BitVec 64}
    {s w₀ t0 w₀' : Arm.ArmState} {D : BitVec 64 → Prop}
    (hME : Lsl.MachEntryPR (fun M _ => Lsl.K M) M g F G ra s w₀ (Lsl.BP M g s) (Lsl.RP M g s))
    (he' : Lsl.MachEntry (fun M _ => Lsl.K M) M g F G' ra' t0 w₀') (hspt : spv t0 = spv s)
    (hD : ∀ a, D a → F a) {env : Clif.Env} {cs : Clif.State} {n : Nat}
    (h2 : Lsl.Stage2ZS (fun M _ => Lsl.K M) M g F (Lsl.BP M g s) (Lsl.RP M g s) env cs (spv w₀)
      (Lsl.CallStPRB (fun M _ => Lsl.K M) M g s w₀ n) n)
    {Q : Arm.ArmState → Prop}
    (hQsp : ∀ u, Q u → spOf u = spv t0 - BitVec.ofNat 64 (frameDrop (Lsl.A g).af))
    (hQ : ∀ u, Q u → CallPc (Lsl.A g).fa (Lsl.A g).base (Arm.r .PC u) →
      LockedUpTo (ArmStepX ((Lsl.XPBTGY (fun M _ => Lsl.K M) M g F (Lsl.BP M g s) (Lsl.RP M g s)
        env cs (spv w₀)).at 0) (Lsl.hooks M) (Lsl.A g).fa) (Lsl.A g).fa (Lsl.A g).base
        ((fun M _ => Lsl.K M) M g) (spv s - BitVec.ofNat 64 (frameDrop (Lsl.A g).af)) F D s t0 n
        u) :
    CalleeOkGP Q F ((fun M _ => Lsl.K M) M g) G' t0 (CallAt (Lsl.A g).fa (Lsl.A g).base)
      ((Lsl.XPBTGY (fun M _ => Lsl.K M) M g F (Lsl.BP M g s) (Lsl.RP M g s) env cs (spv w₀)).at
        n) (Lsl.hooks M) (Lsl.A g).vcp.CallSite (GotV (Lsl.A g).vcp) :=
  Lsl.calleeOkLockedR Lsl_ok (Lsl.budget_K Lsl_ok) ih hdet hg hME he' hspt hD h2 hQsp hQ

theorem calleeTryOkLockedR_Lsl {M : Nat}
    (ih : 0 < M → Lsl.ThmPRBRL (fun M _ => Lsl.K M) (M - 1))
    (hdet : 0 < M → Lsl.DetPRBR (fun M _ => Lsl.K M) (M - 1))
    {g : Clif.Function} (hg : g ∈ Lsl.P.funcs) {F G G' : BitVec 64 → Prop} {ra ra' : BitVec 64}
    {s w₀ t0 w₀' : Arm.ArmState} {D : BitVec 64 → Prop}
    (hME : Lsl.MachEntryPR (fun M _ => Lsl.K M) M g F G ra s w₀ (Lsl.BP M g s) (Lsl.RP M g s))
    (he' : Lsl.MachEntry (fun M _ => Lsl.K M) M g F G' ra' t0 w₀') (hspt : spv t0 = spv s)
    (hD : ∀ a, D a → F a) {env : Clif.Env} {cs : Clif.State} {n : Nat}
    (h2 : Lsl.Stage2ZS (fun M _ => Lsl.K M) M g F (Lsl.BP M g s) (Lsl.RP M g s) env cs (spv w₀)
      (Lsl.CallStPRB (fun M _ => Lsl.K M) M g s w₀ n) n)
    {Q : Arm.ArmState → Prop}
    (hQsp : ∀ u, Q u → spOf u = spv t0 - BitVec.ofNat 64 (frameDrop (Lsl.A g).af))
    (hQ : ∀ u, Q u → CallPc (Lsl.A g).fa (Lsl.A g).base (Arm.r .PC u) →
      LockedUpTo (ArmStepX ((Lsl.XPBTGY (fun M _ => Lsl.K M) M g F (Lsl.BP M g s) (Lsl.RP M g s)
        env cs (spv w₀)).at 0) (Lsl.hooks M) (Lsl.A g).fa) (Lsl.A g).fa (Lsl.A g).base
        ((fun M _ => Lsl.K M) M g) (spv s - BitVec.ofNat 64 (frameDrop (Lsl.A g).af)) F D s t0 n
        u) :
    CalleeTryOkGP Q F ((fun M _ => Lsl.K M) M g) G' t0 (CallAt (Lsl.A g).fa (Lsl.A g).base)
      ((Lsl.XPBTGY (fun M _ => Lsl.K M) M g F (Lsl.BP M g s) (Lsl.RP M g s) env cs (spv w₀)).at
        n) (Lsl.hooks M) (Lsl.A g).vcp.TrySite (GotV (Lsl.A g).vcp) :=
  Lsl.calleeTryOkLockedR Lsl_ok (Lsl.budget_K Lsl_ok) ih hdet hg hME he' hspt hD h2 hQsp hQ

end E2E.LinkSlotSysWitness
