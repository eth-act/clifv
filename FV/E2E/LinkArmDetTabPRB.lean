import FV.E2E.LinkArmProgCallPRB

/-!
# The second determinism fact: the callee table carries over (SEM1 #537, #680 (3) stage 2)

`progCallPRB` needs the table of the **canonical** callee run (`TableOf … (enterAt (canon h uses w))`),
but at a call of the linked machine the caller's table (`TabUpTo`'s call clause) gives the table
of the **actual** call's callee run (`enterAt t`). `DetTabPRB κ M` states the transfer for calls
at depth `M` (callee at depth `M - 1`): with `progCallPRB`'s premises, a call state `t` compatible
with `w` (`CallerOk`) that agrees with the canonical state on the masked registers but `x30`/pc
and on the callee's frame and region below `sp` has the canonical run's table if its own run has
it. It is a premise beside `DetPRB` (both to be discharged by the determinism of the linked
machine, `thmPDER_det_of`).

`progCallPRB_at`: `progCallPRB` with the table premise at an actual call state `t₁`.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

namespace LinkSys

variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

/-- **The callee table carries over to the canonical call** (calls at depth `M`, callee at depth
`M - 1`): under `progCallPRB`'s premises, a call state `t` agreeing with the canonical state
`canon h uses w` (`CallerOk`, masked registers but `x30`/pc, the region below `sp`) whose callee
run's table is `ini'`'s gives the canonical callee run the same table. -/
def DetTabPRB (κ : Nat → Clif.Function → Nat) (M : Nat) : Prop :=
  ∀ (n : String) (h : Clif.Function), L.P.func? n = some h → (∃ g ∈ L.P.funcs, L.Callee g h) →
    ∀ (F : BitVec 64 → Prop), (∀ a, L.Img a → F a) →
    ∀ (uses : List CV) (w : Arm.ArmState), Arm.r .ERR w = .None → (spv w).toNat % 16 = 0 →
    frameDrop (L.A h).af + κ (M - 1) h ≤ (spv w).toNat →
    (∀ a, StackBelow (frameDrop (L.A h).af + κ (M - 1) h) (spv w) a → F a ∧ ¬ L.Img a) →
    ∀ (vals : List Clif.Val) (cm : Clif.Mem) (cs : Clif.State) (rvals : List Clif.Val)
      (cm' : Clif.Mem) (ini : Clif.SlotInit),
    MemRel F L.syms cm w → ArgsAt h.sig vals uses w → StackArgsAvoid F h.sig vals w →
    (L.NeedSlots → L.PlaceAtB cm (spv w) ini) →
    (L.NeedSlots → ∀ a, L.SlotByte h (spv w) a →
      ini.bytes (ini.next + 1) a = probeMem (L.A h).af w (BitVec.ofNat 64 a)) →
    Clif.initState L.P n vals cm = .ok cs → L.crun M cs = .returned rvals cm' →
    ∀ t, L.CallerOk F h uses w t →
      (∀ f, Masked f → f ≠ .PC → f ≠ .GPR 30#5 → Arm.r f t = Arm.r f (L.canon h uses w)) →
      (∀ a, StackBelow (frameDrop (L.A h).af + κ (M - 1) h) (spv w) a →
        t.mem a = (L.canon h uses w).mem a) →
      L.TableOf (M - 1) h (enterAt (L.A h) t) (calleeIni h ini) →
      L.TableOf (M - 1) h (enterAt (L.A h) (L.canon h uses w)) (calleeIni h ini)

/-- **`progCallPRB` at an actual call state**: the canonical table premise from the table of the
callee run of a call state `t₁` compatible with the canonical one (`DetTabPRB`; with `hpb`, #581,
as `progCall`). -/
theorem progCallPRB_at (hL : L.Ok) [hR : L.CrunOk] {M : Nat} (hM : 0 < M)
    (ih : L.ThmPRB κ (M - 1)) (hdet : L.DetPRB κ (M - 1)) (hdt : L.DetTabPRB κ M) {n : String}
    {h : Clif.Function} (hpf : L.P.func? n = some h) (hcal : ∃ g ∈ L.P.funcs, L.Callee g h)
    {F : BitVec 64 → Prop} (himgF : ∀ a, L.Img a → F a)
    {uses : List CV} {w : Arm.ArmState} (herr : Arm.r .ERR w = .None)
    (hal : (spv w).toNat % 16 = 0)
    (hroom : frameDrop (L.A h).af + κ (M - 1) h ≤ (spv w).toNat)
    (hdead : ∀ a, StackBelow (frameDrop (L.A h).af + κ (M - 1) h) (spv w) a → F a ∧ ¬ L.Img a)
    (hpb : probeBelow (L.A h).af ≤ κ (M - 1) h)
    {vals : List Clif.Val} {cm : Clif.Mem} {cs : Clif.State} {rvals : List Clif.Val}
    {cm' : Clif.Mem} {ini : Clif.SlotInit} (hmr : MemRel F L.syms cm w)
    (hargs : ArgsAt h.sig vals uses w)
    (hsav : StackArgsAvoid F h.sig vals w) (hpl : L.NeedSlots → L.PlaceAtB cm (spv w) ini)
    (hslotb : L.NeedSlots → ∀ a, L.SlotByte h (spv w) a →
      ini.bytes (ini.next + 1) a = probeMem (L.A h).af w (BitVec.ofNat 64 a))
    (hinit : Clif.initState L.P n vals cm = .ok cs)
    (hrun : L.crun M cs = .returned rvals cm')
    {t₁ : Arm.ArmState} (ht₁ : L.CallerOk F h uses w t₁)
    (hmsk₁ : ∀ f, Masked f → f ≠ .PC → f ≠ .GPR 30#5 → Arm.r f t₁ = Arm.r f (L.canon h uses w))
    (hrgn₁ : ∀ a, StackBelow (frameDrop (L.A h).af + κ (M - 1) h) (spv w) a →
      t₁.mem a = (L.canon h uses w).mem a)
    (htab₁ : L.TableOf (M - 1) h (enterAt (L.A h) t₁) (calleeIni h ini)) :
    ∃ (us : List (Reg × Reg)) (outs : List CV) (wf : Arm.ArmState) (e : Nat),
      us.map (·.2) = (List.range us.length).map Reg.x ∧ us.length = outs.length ∧
      PrefixHold rvals outs ∧ MemRel F L.syms cm' wf ∧ (L.A h).vc.RetsSite us ∧
      (L.NeedSlots → Clif.NextAdv cs.mem cm' e) ∧
      (∀ t, L.CallerOk F h uses w t →
        (∀ f, Masked f → f ≠ .PC → f ≠ .GPR 30#5 → Arm.r f t = Arm.r f (L.canon h uses w)) →
        (∀ a, StackBelow (frameDrop (L.A h).af + κ (M - 1) h) (spv w) a →
          t.mem a = (L.canon h uses w).mem a) → ∃ k,
        L.pcall M h t =
          Arm.set_program (runX (L.mach (M - 1) h) k (enterAt (L.A h) t)) t.program ∧
        ActRet (Arm.r .PC t + 4) F
          (fun a => F a ∧ ¬ StackBelow (frameDrop (L.A h).af + κ (M - 1) h) (spv w) a)
          us outs wf (enterAt (L.A h) t) (runX (L.mach (M - 1) h) k (enterAt (L.A h) t)) ∧
        L.TabUpTo (M - 1) h (enterAt (L.A h) t) (calleeIni h ini).bytes (calleeIni h ini).next k
          e) :=
  L.progCallPRB hL hM ih hdet hpf hcal himgF herr hal hroom hdead hpb hmr hargs hsav hpl hslotb
    (hdt n h hpf hcal F himgF uses w herr hal hroom hdead vals cm cs rvals cm' ini hmr hargs hsav
      hpl hslotb hinit hrun t₁ ht₁ hmsk₁ hrgn₁ htab₁) hinit hrun

end LinkSys

end E2E
