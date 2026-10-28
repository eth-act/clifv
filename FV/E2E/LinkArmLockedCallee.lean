import FV.E2E.LinkArmProgOsPRBRL30
import FV.E2E.BackendTwoRunNIU
import FV.E2E.LinkArmBlrCheck

/-!
# The second activation's call contracts at its locked call states (SEM1 #537, #713)

`backend_twoRunLERWZIU` asks the contracts of the first activation's `XI` (the link's `XPBTGY`
with the first run's prophecies) for the second activation only at its call states locked with
the first run up to there (`LockedUpTo`), with the two memories equal outside `F ∪ D` there.
With `D ⊆ F` (`DetPRBR`'s premise) such a state `u` and the first run's state `u₀` of the same
index are the same but for `x30` and bytes in `F` and outside the callees' dead stack: `u₀` is
the first run's call-`n` state (`LockedUpTo.callsBefore_eq`), so

* the prophecies of call `n` hold at `u` but for `x30` (the dead stack is `u₀`'s), which the
  `x30`-exempt contracts accept (`calleeOkXPBTGZS30R`);
* stage 2 at `u` is the first run's at `u₀`: a world of `u` (`SameWorld F u w`) is one of `u₀`,
  and the call's operand values are `u₀`'s (`useVals_eq_of_x30`: the allocated operand registers
  are allocatable, never `x30`).

* `useVals_eq_of_x30`, `LinkSys.lockedCall`;
* **`LinkSys.calleeOkLockedR`**, **`LinkSys.calleeTryOkLockedR`**.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- **The operand values of a checked instruction do not read `x30`.** -/
theorem useVals_eq_of_x30 {c : CheckCtx} {wh : String} {ops : Array Operand} {regs : Array Reg}
    {clob : List Reg} (hst : c.checkStatic wh ops (regs.map .reg) clob = .ok ())
    {u u' : Arm.ArmState} (h : ∀ f, f ≠ .GPR 30#5 → Arm.r f u = Arm.r f u') :
    useVals ops regs u = useVals ops regs u' := by
  obtain ⟨hsz, hloc, -, -⟩ := checkStatic_facts hst
  unfold useVals
  refine List.map_congr_left fun p hp => ?_
  have hp' := (List.mem_filter.mp hp).1
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hp'
  have hq : (p.1, Loc.reg p.2) ∈ (ops.zip (regs.map .reg)).toList := by
    apply List.mem_iff_getElem?.mpr
    refine ⟨j, ?_⟩
    simp only [Array.toList_zip, Array.toList_map, List.getElem?_zip_eq_some,
      List.getElem?_map] at hj ⊢
    obtain ⟨h1, h2⟩ := hj
    exact ⟨h1, by rw [h2]; rfl⟩
  have hok := (hloc _ hq).1
  simp only [CheckCtx.locOk, Loc.cls?, Bool.and_eq_true] at hok
  rcases allocatable_cases hok.2 with ⟨n, hr, hn, -⟩ | ⟨n, hr, -⟩
  · rw [hr]
    have hne : Arm.StateField.GPR (rnum n) ≠ .GPR 30#5 := by
      intro e
      have := congrArg BitVec.toNat (Arm.StateField.GPR.inj e)
      rw [rnum_toNat (by omega)] at this
      simp at this
      omega
    simp only [regVal]
    rw [h _ hne]
  · rw [hr]
    simp only [regVal]
    exact h _ (by simp)

namespace LinkSys

variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

/-- **A locked call state of the second run is the first run's call-`n` state** up to `x30`, the
bytes of `F` and bytes outside the callees' dead stack (module doc). -/
theorem lockedCall {M : Nat} {g : Clif.Function} {F G : BitVec 64 → Prop} {ra : BitVec 64}
    {s w₀ t0 : Arm.ArmState} {D : BitVec 64 → Prop} {X : ExtSem} (hX : X.sym = L.Xb.sym)
    (hME : L.MachEntryPR κ M g F G ra s w₀ (L.BP M g s) (L.RP M g s))
    (hspt : spv t0 = spv s) (hD : ∀ a, D a → F a) {n : Nat} {u : Arm.ArmState}
    (hsp : spOf u = spv t0 - BitVec.ofNat 64 (frameDrop (L.A g).af))
    (hlk : LockedUpTo (ArmStepX X (L.hooks M) (L.A g).fa) (L.A g).fa (L.A g).base (κ M g)
      (spv s - BitVec.ofNat 64 (frameDrop (L.A g).af)) F D s t0 n u) :
    ∃ u₀, L.CallStPRB κ M g s w₀ n u₀ ∧ (∀ f, f ≠ .GPR 30#5 → Arm.r f u = Arm.r f u₀) ∧
      u.program = u₀.program ∧ (∀ a, StackBelow (κ M g) (spv u) a → u.mem a = u₀.mem a) ∧
      ∀ a, ¬ F a → u.mem a = u₀.mem a := by
  rw [armStepX_congr_sym hX] at hlk
  obtain ⟨i, Z, hu, hcb, hz, hZ, hm⟩ := hlk.callsBefore_eq
  have h31 : spv u = spv (runX (L.mach M g) i s) := hz.1 _ (by simp)
  have hsp' : spv u = spv s - BitVec.ofNat 64 (frameDrop (L.A g).af) := by
    rw [← hspt]; exact hsp
  refine ⟨runX (L.mach M g) i s,
    ⟨onCallPR_of hME.entryP.proph hME.reg ⟨i, rfl, hcb⟩, by
      show spv _ = _; rw [← h31]; exact hsp'⟩,
    hz.1, hz.2.1, fun a ha => hz.2.2 a (hZ a (by rw [hsp'] at ha; exact ha)),
    fun a ha => hm a ha (fun hd => ha (hD a hd))⟩

/-- **The second activation's call contract at its locked call states** (module doc). -/
theorem calleeOkLockedR (hL : L.Ok) [L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1)) (hdet : 0 < M → L.DetPRBR κ (M - 1))
    {g : Clif.Function} (hg : g ∈ L.P.funcs) {F G G' : BitVec 64 → Prop} {ra ra' : BitVec 64}
    {s w₀ t0 w₀' : Arm.ArmState} {D : BitVec 64 → Prop}
    (hME : L.MachEntryPR κ M g F G ra s w₀ (L.BP M g s) (L.RP M g s))
    (he' : L.MachEntry κ M g F G' ra' t0 w₀') (hspt : spv t0 = spv s) (hD : ∀ a, D a → F a)
    {env : Clif.Env} {cs : Clif.State} {n : Nat}
    (h2 : L.Stage2ZS κ M g F (L.BP M g s) (L.RP M g s) env cs (spv w₀)
      (L.CallStPRB κ M g s w₀ n) n)
    {Q : Arm.ArmState → Prop}
    (hQsp : ∀ u, Q u → spOf u = spv t0 - BitVec.ofNat 64 (frameDrop (L.A g).af))
    (hQ : ∀ u, Q u → CallPc (L.A g).fa (L.A g).base (Arm.r .PC u) →
      LockedUpTo (ArmStepX ((L.XPBTGY κ M g F (L.BP M g s) (L.RP M g s) env cs (spv w₀)).at 0)
        (L.hooks M) (L.A g).fa) (L.A g).fa (L.A g).base (κ M g)
        (spv s - BitVec.ofNat 64 (frameDrop (L.A g).af)) F D s t0 n u) :
    CalleeOkGP Q F (κ M g) G' t0 (CallAt (L.A g).fa (L.A g).base)
      ((L.XPBTGY κ M g F (L.BP M g s) (L.RP M g s) env cs (spv w₀)).at n) (L.hooks M)
      (L.A g).vcp.CallSite (GotV (L.A g).vcp) := by
  have hlc : ∀ u, Q u → CallPc (L.A g).fa (L.A g).base (Arm.r .PC u) → ∃ u₀,
      L.CallStPRB κ M g s w₀ n u₀ ∧ (∀ f, f ≠ .GPR 30#5 → Arm.r f u = Arm.r f u₀) ∧
      u.program = u₀.program ∧ (∀ a, StackBelow (κ M g) (spv u) a → u.mem a = u₀.mem a) ∧
      ∀ a, ¬ F a → u.mem a = u₀.mem a := fun u hu hpc =>
    L.lockedCall rfl hME hspt hD (hQsp u hu) (hQ u hu hpc)
  have hq := L.callStPRB_q (κ := κ) (M := M) hME.entryP.entry.body.sp n
  refine L.calleeOkXPBTGZS30R hL hκ ih hdet hg he' (fun t ht hpc => ?_) (fun u w hu hsw i info
    hi hS ops regs i' hops cc wh hst hasg hpi hal herr hgd hnv => ?_)
  · obtain ⟨u₀, hcs, hr, -, hd, -⟩ := hlc t ht hpc
    have hpc₀ : CallPc (L.A g).fa (L.A g).base (Arm.r .PC u₀) := by
      rw [← hr .PC (by simp)]; exact hpc
    obtain ⟨hq1, hq2⟩ := hq u₀ hcs hpc₀
    refine ⟨fun f hf h30 => (hr f h30).trans (hq1 f hf), fun a ha => ?_⟩
    rw [hd a ha]
    have e31 : spv t = spv u₀ := hr (.GPR 31#5) (by simp)
    exact hq2 a (by rw [← e31]; exact ha)
  · obtain ⟨u₀, hcs, hr, hp, -, hmF⟩ := hlc u hu hpi.callPc
    have hU : useVals ops regs u = useVals ops regs u₀ := useVals_eq_of_x30 hst hr
    rw [hU] at hgd hnv ⊢
    have h31 := hr (.GPR 31#5) (by simp)
    refine h2 u₀ w hcs ⟨fun f hf => (hr f (fun e => hf (e ▸ by simp [Masked]))).symm.trans
        (hsw.1 f hf), fun a ha => (hmF a ha).symm.trans (hsw.2.1 a ha), hp.symm.trans hsw.2.2⟩
      i info hi hS ops regs i' hops cc wh hst hasg (by rw [← hr .PC (by simp)]; exact hpi)
      (by simp only [Arm.CheckSPAlignment, Arm.read_gpr] at hal ⊢; rw [← h31]; exact hal)
      (by rw [← hr .ERR (by simp)]; exact herr) hgd hnv

/-- **The second activation's try-call contract at its locked call states.** -/
theorem calleeTryOkLockedR (hL : L.Ok) [L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1)) (hdet : 0 < M → L.DetPRBR κ (M - 1))
    {g : Clif.Function} (hg : g ∈ L.P.funcs) {F G G' : BitVec 64 → Prop} {ra ra' : BitVec 64}
    {s w₀ t0 w₀' : Arm.ArmState} {D : BitVec 64 → Prop}
    (hME : L.MachEntryPR κ M g F G ra s w₀ (L.BP M g s) (L.RP M g s))
    (he' : L.MachEntry κ M g F G' ra' t0 w₀') (hspt : spv t0 = spv s) (hD : ∀ a, D a → F a)
    {env : Clif.Env} {cs : Clif.State} {n : Nat}
    (h2 : L.Stage2ZS κ M g F (L.BP M g s) (L.RP M g s) env cs (spv w₀)
      (L.CallStPRB κ M g s w₀ n) n)
    {Q : Arm.ArmState → Prop}
    (hQsp : ∀ u, Q u → spOf u = spv t0 - BitVec.ofNat 64 (frameDrop (L.A g).af))
    (hQ : ∀ u, Q u → CallPc (L.A g).fa (L.A g).base (Arm.r .PC u) →
      LockedUpTo (ArmStepX ((L.XPBTGY κ M g F (L.BP M g s) (L.RP M g s) env cs (spv w₀)).at 0)
        (L.hooks M) (L.A g).fa) (L.A g).fa (L.A g).base (κ M g)
        (spv s - BitVec.ofNat 64 (frameDrop (L.A g).af)) F D s t0 n u) :
    CalleeTryOkGP Q F (κ M g) G' t0 (CallAt (L.A g).fa (L.A g).base)
      ((L.XPBTGY κ M g F (L.BP M g s) (L.RP M g s) env cs (spv w₀)).at n) (L.hooks M)
      (L.A g).vcp.TrySite (GotV (L.A g).vcp) := by
  have hlc : ∀ u, Q u → CallPc (L.A g).fa (L.A g).base (Arm.r .PC u) → ∃ u₀,
      L.CallStPRB κ M g s w₀ n u₀ ∧ (∀ f, f ≠ .GPR 30#5 → Arm.r f u = Arm.r f u₀) ∧
      u.program = u₀.program ∧ (∀ a, StackBelow (κ M g) (spv u) a → u.mem a = u₀.mem a) ∧
      ∀ a, ¬ F a → u.mem a = u₀.mem a := fun u hu hpc =>
    L.lockedCall rfl hME hspt hD (hQsp u hu) (hQ u hu hpc)
  have hq := L.callStPRB_q (κ := κ) (M := M) hME.entryP.entry.body.sp n
  refine L.calleeTryOkXPBTGZS30R hL hκ ih hdet hg he' (fun t ht hpc => ?_) (fun u w hu hsw i info
    hi hS ops regs i' hops cc wh hst hasg hpi hal herr hgd hnv => ?_)
  · obtain ⟨u₀, hcs, hr, -, hd, -⟩ := hlc t ht hpc
    have hpc₀ : CallPc (L.A g).fa (L.A g).base (Arm.r .PC u₀) := by
      rw [← hr .PC (by simp)]; exact hpc
    obtain ⟨hq1, hq2⟩ := hq u₀ hcs hpc₀
    refine ⟨fun f hf h30 => (hr f h30).trans (hq1 f hf), fun a ha => ?_⟩
    rw [hd a ha]
    have e31 : spv t = spv u₀ := hr (.GPR 31#5) (by simp)
    exact hq2 a (by rw [← e31]; exact ha)
  · obtain ⟨u₀, hcs, hr, hp, -, hmF⟩ := hlc u hu hpi.callPc
    have hU : useVals ops regs u = useVals ops regs u₀ := useVals_eq_of_x30 hst hr
    rw [hU] at hgd hnv ⊢
    have h31 := hr (.GPR 31#5) (by simp)
    refine h2 u₀ w hcs ⟨fun f hf => (hr f (fun e => hf (e ▸ by simp [Masked]))).symm.trans
        (hsw.1 f hf), fun a ha => (hmF a ha).symm.trans (hsw.2.1 a ha), hp.symm.trans hsw.2.2⟩
      i info hi hS ops regs i' hops cc wh hst hasg (by rw [← hr .PC (by simp)]; exact hpi)
      (by simp only [Arm.CheckSPAlignment, Arm.read_gpr] at hal ⊢; rw [← h31]; exact hal)
      (by rw [← hr .ERR (by simp)]; exact herr) hgd hnv

end LinkSys

end E2E
