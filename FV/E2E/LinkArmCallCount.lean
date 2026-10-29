import FV.E2E.LinkArmOracleAt
import FV.E2E.LinkArmProgCallPRBRLT
import FV.E2E.LinkPlaceBLeave

/-!
# The count of a program call (SEM1 #537, #680 (3), stage 2 (P3))

At a pre-return call of a function `h` of `P` by the activation (state `t`, step `i`) with the
oracle facts of its CLIF invocation (`OracleAt`, memory `cm`, callee run returning `cm'`), the
caller table's count advances over the call by the CLIF counter's advance of the call: the call
clause's callee count (the callee run up to its first return) is `progCallPRBRLT`'s count, whose
run returns first at the same step (`noRetOf_before`, the callee run's `PostTrace`), and the CLIF
advance is `slotted h` (the callee's own entry, `initState_leave_nextAdv`) plus that count.

* `noRetOf_before`: under `RaOk` and `PostTrace` a return of a linked call is its first;
* `retOf_of_actRet`;
* **`callCount`**: `∃ d, NextAdv cm cm' d ∧` the count of every table of the prefix past the call
  is the count before it plus `d`.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- **A return of a linked call with the callee run's trace is its first** (`linkedCall_eq`'s
argument). -/
theorem noRetOf_before {X : ExtSem} {H : ArmHooks} {a : Art} {lm : Std.HashMap Lbl Nat}
    (hl : a.fa.layout = .ok a.fb) (hm : labelOffsets a.fa.lines = .ok lm) {s : Arm.ArmState}
    (hra : RaOk a (Arm.r .PC s)) (hfd : 0 < frameDrop a.af) (hfd' : frameDrop a.af < 2 ^ 64)
    {n : Nat} (htr : PostTrace a.fa a.af a.base (ArmStepX X H a.fa) (enterAt a s) n)
    (hret : RetOf a s (runX (ArmStepX X H a.fa) n (enterAt a s))) :
    ∀ i < n, ¬ RetOf a s (runX (ArmStepX X H a.fa) i (enterAt a s)) := by
  intro i hi hri
  rcases hra with hra | ⟨hcp, hne⟩
  · have := retStuck (X := X) (H := H) hl hm hri.2.2.1 (by rw [hri.1]; exact hra) (n - i - 1)
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

/-- **A return of a linked call** from `ActRet` at the call's return address. -/
theorem retOf_of_actRet {a : Art} {t x : Arm.ArmState} {F G : BitVec 64 → Prop}
    {us : List (Reg × Reg)} {outs : List CV} {w : Arm.ArmState}
    (h : ActRet (Arm.r .PC t + 4) F G us outs w (enterAt a t) x) : RetOf a t x := by
  refine ⟨h.ret.pc, h.ret.err, ?_, ?_⟩
  · rw [h.prog]; simp only [enterAt, Arm.w_program, program_set_program]
  · rw [h.ret.sp]; exact r_enterAt _ _ (by decide) (by decide)

namespace LinkSys

variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

/-- **The count of a program call** (module doc). -/
theorem callCount (hL : L.Ok) [hR : L.CrunOk] (hκ : L.Budget κ) {M' : Nat}
    (ih : L.ThmPRBRL κ M') (hdet : L.DetPRB κ M')
    {g : Clif.Function} (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {ra : BitVec 64}
    {s w₀ : Arm.ArmState} (hME : L.MachEntry κ (M' + 1) g F G ra s w₀)
    (hra : RaOk (L.A g) (ra - 4)) {ini : Clif.SlotInit} (htab : L.TableOf (M' + 1) g s ini)
    (himgF : ∀ a, L.Img a → F a) {c : BitVec 64}
    (hroom : κ (M' + 1) g ≤ c.toNat)
    (hdead : ∀ a, StackBelow (κ (M' + 1) g) c a → F a ∧ ¬ L.Img a) (halign : c.toNat % 16 = 0)
    {i : Nat}
    (htr : ∀ j < i, ¬ PostCall (L.A g).fa (L.A g).base (Arm.r .PC (runX (L.mach (M' + 1) g) j s)) ∨
      spOf (runX (L.mach (M' + 1) g) j s) = spv s - BitVec.ofNat 64 (frameDrop (L.A g).af))
    (hsp : spOf (runX (L.mach (M' + 1) g) i s) = spv s - BitVec.ofNat 64 (frameDrop (L.A g).af))
    (herr : Arm.r .ERR (runX (L.mach (M' + 1) g) i s) = .None)
    (hcp : CallPc (L.A g).fa (L.A g).base (Arm.r .PC (runX (L.mach (M' + 1) g) i s)))
    {h : Clif.Function} (hpf : L.P.func? h.name = some h) (hcal : L.Callee g h)
    (hct : L.CallsTo g (runX (L.mach (M' + 1) g) i s) h)
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState}
    (hmskQ : ∀ f, MaskedReg f → Arm.r f (runX (L.mach (M' + 1) g) i s) =
      Arm.r f (R (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i)))
    (hrgnQ : ∀ a, StackBelow (κ (M' + 1) g) (spv (runX (L.mach (M' + 1) g) i s)) a →
      (runX (L.mach (M' + 1) g) i s).mem a =
        P (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i) a)
    {Lu : List (Nat × Reg)} (hLu : Lu.map (·.2) = regLocs h.sig) {w : Arm.ArmState}
    (hsw : SameWorld F (runX (L.mach (M' + 1) g) i s) w) (hspw : spv w = c)
    (himgT : ∀ a, L.Img a → (runX (L.mach (M' + 1) g) i s).mem a = L.imgMem a)
    (hrah : RaOk (L.A h) (Arm.r .PC (runX (L.mach (M' + 1) g) i s)))
    {vals : List Clif.Val} {cm : Clif.Mem} {cs : Clif.State} {rvals : List Clif.Val}
    {cm' : Clif.Mem}
    (hmrW : MemRel F L.syms cm (L.worldPR κ (M' + 1) h
      (P (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i))
      (R (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i)) w))
    (hargsW : ArgsAt h.sig vals (Lu.map (fun q => regVal (runX (L.mach (M' + 1) g) i s) q.2))
      (L.worldPR κ (M' + 1) h (P (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i))
        (R (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i)) w))
    (hsavW : StackArgsAvoid F h.sig vals
      (L.worldPR κ (M' + 1) h (P (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i))
        (R (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i)) w))
    (hor : L.OracleAt κ (M' + 1) h c cm (Lu.map (fun q => regVal (runX (L.mach (M' + 1) g) i s) q.2))
      (L.worldPR κ (M' + 1) h (P (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i))
        (R (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i)) w))
    (hinit : Clif.initState L.P h.name vals cm = .ok cs)
    (hrun : L.crun (M' + 1) cs = .returned rvals cm') :
    ∃ d, (L.NeedSlots → Clif.NextAdv cm cm' d) ∧
      ∀ e e', L.TabUpTo (M' + 1) g s ini.bytes ini.next i e →
        L.TabUpTo (M' + 1) g s ini.bytes ini.next (i + 1) e' → e' = e + d := by
  have hM : 0 < M' + 1 := Nat.succ_pos M'
  have hh : h ∈ L.P.funcs := L.callee_mem hcal
  have hbud := L.budget_step hκ hM hg hcal
  have hnr := L.noRetAt_upTo hL hg hME hra htr hsp herr
  have hspW : spv (L.worldPR κ (M' + 1) h
      (P (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i))
      (R (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i)) w) = c :=
    (L.r_worldPR_out (κ := κ) (M := M' + 1) h _ _ w (f := .GPR 31#5)
      (fun hm => by simp [MaskedReg, Masked] at hm)).trans hspw
  have hdeadW : ∀ a, StackBelow (frameDrop (L.A h).af + κ (M' + 1 - 1) h) (spv w) a →
      F a ∧ ¬ L.Img a := fun a ha => hdead a (by rw [← hspw]; exact stackBelow_mono ha hbud)
  obtain ⟨hcOk, hmsk, hrgn, -⟩ := L.callerFacts hL hκ hM hg hh hcal himgF hLu hsw himgT hrah
    hmskQ hrgnQ hdeadW
  obtain ⟨inj, hpl, hslot, htabC⟩ := hor
  -- the callee's linking statement, with the trace of the actual callee run
  obtain ⟨us0, outs0, wf0, ec, -, -, -, -, -, hadv, hcall⟩ :=
    L.progCallPRBRLT hL hM ih hdet hpf ⟨g, hg, hcal⟩ himgF
      (by rw [show Arm.r .ERR _ = Arm.r .ERR w from
            L.r_worldPR_out h _ _ w (fun hm => by simp [MaskedReg, Masked] at hm),
          ← hsw.1 .ERR (by simp [Masked])]; exact herr)
      (by rw [hspW]; exact halign) (by rw [hspW]; have := hbud; omega)
      (fun a ha => hdead a (by rw [hspW] at ha; exact stackBelow_mono ha hbud))
      (hκ.2 _ h hh)
      hmrW hargsW hsavW (fun hN => by rw [hspW]; exact hpl hN)
      (fun hN => by rw [hspW]; exact hslot hN) htabC hinit hrun
  obtain ⟨k', -, hret', htabk, htrk⟩ := hcall _ hcOk hmsk hrgn
  -- the caller's table over the call
  obtain ⟨e1, E, -, hall⟩ := htab (i + 1) hnr
  obtain ⟨-, -, N', hretN, hfirst, htabN⟩ := (hall i (by omega) hcp).2 h hct
  have hc := hL.compiled h hh
  obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hc.layout
  have hfd := L.frameDrop_eq hL hh
  have hfdlt : frameDrop (L.A h).af < 2 ^ 64 := by
    have := (spv w).isLt
    have := hdeadW
    have hr : frameDrop (L.A h).af + κ (M' + 1 - 1) h ≤ (spv w).toNat := by rw [hspw]; omega
    omega
  have hk : k' = N' := by
    have hro := retOf_of_actRet hret'
    rcases Nat.lt_trichotomy k' N' with hlt | heq | hgt
    · exact absurd hro (hfirst k' hlt)
    · exact heq
    · exact absurd hretN (noRetOf_before (X := L.Xb) (H := L.hooks M') hc.layout hlm hrah
        (by omega) hfdlt htrk hro N' hgt)
  subst hk
  have hec : ec = E (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i) - slotted h :=
    L.tabUpTo_count _ _ _ _ _ _ _ _ _ _ htabk htabN
  obtain ⟨-, hle, -⟩ := (hall i (by omega) hcp).2 h hct
  refine ⟨slotted h + ec, fun hN => ?_, fun e e' he he' => ?_⟩
  · have h1 := L.initState_leave_nextAdv hpf hinit (hpl hN)
    have h2 := hadv hN
    have : (if h.slots.isEmpty then 0 else 1) = slotted h := rfl
    rw [this] at h1
    exact h1.trans h2
  · have hpre : L.TabUpTo (M' + 1) g s ini.bytes ini.next i
        (Clif.sumTo E (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i)) :=
      ⟨E, rfl, fun i' hi' => hall i' (by omega)⟩
    have hpost : L.TabUpTo (M' + 1) g s ini.bytes ini.next (i + 1)
        (Clif.sumTo E (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s (i + 1))) :=
      ⟨E, rfl, hall⟩
    rw [L.tabUpTo_count _ _ _ _ _ _ _ _ _ _ he hpre, L.tabUpTo_count _ _ _ _ _ _ _ _ _ _ he' hpost]
    simp only [callsBefore, hcp, ↓reduceIte, Clif.sumTo]
    omega

end LinkSys

end E2E
