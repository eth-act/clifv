import FV.E2E.LinkArmProgOsP
import FV.E2E.LinkArmStage2Prog
import FV.E2E.LinkArmCallTab

/-!
# The oracle facts of a program call before the return (SEM1 #537, #680 (3), stage 2 (P2))

At a call of a function `h` of `P` by the activation (state `t`, step `i`, before the return), with
the prophecies of the call (`t`'s masked registers `R n`, its bytes below `sp` `P n`), the oracle
facts `OracleAt` of the CLIF invocation (memory `cm` placed at the body `sp` with `ini.adv x`)
hold when `x` is the caller table's count before the call: the slot bytes are the table entry the
call clause fixes (the memory at the call, which the world with the prophecies holds), and the
canonical callee run's table is the actual callee run's (`tableOf_callee`) carried over by
`DetTabPRB`.

* `slotByte_below`, `calleeIni_bytes`, `calleeIni_next`;
* **`callerFacts`**: `DetTabPRB`'s premises at the call state for the world with the prophecies;
* **`oracleAt_of_call`**.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

namespace LinkSys

variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

/-- **A slot byte of an activation of `h` at `sp = c` is below `c`**, within `h`'s frame. -/
theorem slotByte_below (hL : L.Ok) {g h : Clif.Function} (hg : g ∈ L.P.funcs) (hcal : L.Callee g h)
    {c : BitVec 64} (hroom : frameDrop (L.A h).af ≤ c.toNat) {a : Nat} (ha : L.SlotByte h c a) :
    StackBelow (frameDrop (L.A h).af) c (BitVec.ofNat 64 a) ∧ (BitVec.ofNat 64 a).toNat = a := by
  obtain ⟨p, hp, hlo, hhi⟩ := ha
  obtain ⟨off, hoff, hle⟩ := hL.slotFits g hg h hcal p hp
  simp only [hoff, Option.getD_some] at hlo hhi
  have hfd := L.frameDrop_eq hL (L.callee_mem hcal)
  have hlt := c.isLt
  have hsub : (c - BitVec.ofNat 64 (frameDrop (L.A h).af)).toNat = c.toNat - frameDrop (L.A h).af :=
    (off_toNat 0 c (frameDrop (L.A h).af) hroom).2.2
  rw [hsub] at hlo hhi
  have e : (BitVec.ofNat 64 a).toNat = a := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  exact ⟨⟨by rw [e]; omega, by rw [e]; omega⟩, e⟩

theorem calleeIni_bytes (h : Clif.Function) (ini : Clif.SlotInit) :
    (calleeIni h ini).bytes = ini.bytes := by
  unfold calleeIni; split <;> rfl

theorem calleeIni_next (h : Clif.Function) (ini : Clif.SlotInit) :
    (calleeIni h ini).next = ini.next + slotted h := by
  unfold calleeIni slotted; split <;> simp [Clif.SlotInit.adv]

/-- **`DetTabPRB`'s premises at a call state**: a caller state `t` with the masked registers of
`R n` and `P n` below its `sp`, whose arguments (`Lu`) are in `h`'s parameter registers, is
compatible with the canonical callee state of the world with the prophecies. -/
theorem callerFacts (hL : L.Ok) (hκ : L.Budget κ) {M : Nat} (hM : 0 < M) {g h : Clif.Function}
    (hg : g ∈ L.P.funcs) (hh : h ∈ L.P.funcs) (hcal : L.Callee g h) {F : BitVec 64 → Prop}
    (himgF : ∀ a, L.Img a → F a)
    {Lu : List (Nat × Reg)} (hLu : Lu.map (·.2) = regLocs h.sig)
    {t w : Arm.ArmState} (hsw : SameWorld F t w)
    (himgT : ∀ a, L.Img a → t.mem a = L.imgMem a)
    (hra : RaOk (L.A h) (Arm.r .PC t))
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {n : Nat}
    (hmskQ : ∀ f, MaskedReg f → Arm.r f t = Arm.r f (R n))
    (hrgnQ : ∀ a, StackBelow (κ M g) (spv t) a → t.mem a = P n a)
    (hdeadW : ∀ a, StackBelow (frameDrop (L.A h).af + κ (M - 1) h) (spv w) a → F a ∧ ¬ L.Img a) :
    L.CallerOk F h (Lu.map (fun q => regVal t q.2)) (L.worldPR κ M h (P n) (R n) w) t ∧
    (∀ f, Masked f → f ≠ .PC → f ≠ .GPR 30#5 →
      Arm.r f t = Arm.r f (L.canon h (Lu.map (fun q => regVal t q.2)) (L.worldPR κ M h (P n) (R n) w))) ∧
    (∀ a, StackBelow (frameDrop (L.A h).af + κ (M - 1) h) (spv (L.worldPR κ M h (P n) (R n) w)) a →
      t.mem a = (L.canon h (Lu.map (fun q => regVal t q.2)) (L.worldPR κ M h (P n) (R n) w)).mem a) ∧
    SameWorld F t (L.worldPR κ M h (P n) (R n) w) := by
  let W := L.worldPR κ M h (P n) (R n) w
  obtain ⟨hnd, harg, -⟩ := hL.argRegs h hh
  have hspW : spv W = spv w :=
    L.r_worldPR_out (κ := κ) (M := M) h (P n) (R n) w (f := .GPR 31#5)
      (fun hm => by simp [MaskedReg, Masked] at hm)
  have hst : spv t = spv w := hsw.1 _ (by simp [Masked])
  have hmaskedF : ∀ (r : Reg) (f : Arm.StateField), r.isArgReg = true → r.field = some f → MaskedReg f := by
    intro r f hr hf
    refine ⟨?_, (argReg_ne29 hr hf).2.2.2⟩
    cases r with
    | x k =>
      simp only [Reg.isArgReg, decide_eq_true_eq] at hr
      simp only [Reg.field, Option.some.injEq] at hf
      subst hf
      simp only [Masked, rnum_toNat (show k < 32 by omega)]
      omega
    | v k =>
      simp only [Reg.field, Option.some.injEq] at hf
      subst hf
      trivial
    | _ => simp [Reg.isArgReg] at hr
  have hargW : ∀ r ∈ regLocs h.sig, regVal t r = regVal W r := fun r hr =>
    regVal_eq_of_field (harg r hr) fun f hf => by
      have hm := hmaskedF r f (harg r hr) hf
      rw [hmskQ f hm, L.r_worldPR_in h (P n) w hm]
  have huses : Lu.map (fun q => regVal t q.2) = (regLocs h.sig).map (regVal W) := by
    rw [← hLu, List.map_map]
    exact List.map_congr_left fun q hq => hargW q.2 (by rw [← hLu]; exact List.mem_map_of_mem hq)
  have hmsk : ∀ f, Masked f → f ≠ .PC → f ≠ .GPR 30#5 →
      Arm.r f t = Arm.r f (L.canon h (Lu.map (fun q => regVal t q.2)) W) := by
    intro f hf hpc _
    rw [huses, L.canon_self_r h W hpc, L.r_worldPR_in h (P n) w ⟨hf, hpc⟩, hmskQ f ⟨hf, hpc⟩]
  have hrgn : ∀ a, StackBelow (frameDrop (L.A h).af + κ (M - 1) h) (spv W) a →
      t.mem a = (L.canon h (Lu.map (fun q => regVal t q.2)) W).mem a := by
    intro a ha
    rw [hspW] at ha
    have hFI := hdeadW a ha
    rw [L.mem_canon, mem_withImg, if_neg hFI.2, L.mem_worldPR, worldP,
      mem_overlay_in (show L.calleeRgn κ M h w a from ha)]
    exact hrgnQ a (stackBelow_mono (by rw [hst]; exact ha) (L.budget_step hκ hM hg hcal))
  have hsw' : SameWorld F t W :=
    ⟨fun f hf => (hsw.1 f hf).trans (L.r_worldPR_out h _ _ w (fun hm => hf hm.1)).symm,
      fun a ha => (hsw.2.1 a ha).trans (by
        rw [L.mem_worldPR, worldP, mem_overlay_out (R := L.calleeRgn κ M h w)
          (fun hr => ha (hdeadW a hr).1)]),
      hsw.2.2.trans (L.program_worldPR h _ _ w).symm⟩
  have hcOk : L.CallerOk F h (Lu.map (fun q => regVal t q.2)) W t := by
    refine ⟨hsw', himgT, fun r hr => ?_, hra⟩
    rw [← hLu] at hr
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hr
    have hrA : r.isArgReg = true := harg r (by rw [← hLu]; exact List.mem_of_getElem? hj)
    have hu : (Lu.map (fun q => regVal t q.2))[j]? = some (regVal t r) := by
      simp only [List.getElem?_map, Option.map_eq_some_iff] at hj
      obtain ⟨q, hq, rfl⟩ := hj
      simp [hq]
    rw [L.regVal_canon _ _ _ hrA, placeArgs_regVal _ _ _ hnd harg (by rw [← hLu]; exact hj) hu,
      setVal_regVal]
  exact ⟨hcOk, hmsk, hrgn, hsw'⟩

/-- **The oracle facts of a program call before the return** (module doc): at the activation's
call state `t` (step `i`, `Good` trace, body `sp` `c`, calling `h`), with the prophecies of the
call, for an invocation memory `cm` placed with `ini.adv x` where `x` is the caller table's count
before the call. -/
theorem oracleAt_of_call (hL : L.Ok) (hκ : L.Budget κ) {M' : Nat} (hdt : L.DetTabPRB κ (M' + 1))
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
    {x : Nat} (hpl : L.NeedSlots → L.PlaceAtB cm c (ini.adv x))
    (hcnt : ∀ e, L.TabUpTo (M' + 1) g s ini.bytes ini.next i e → e = x)
    (hinit : Clif.initState L.P h.name vals cm = .ok cs)
    (hrun : L.crun (M' + 1) cs = .returned rvals cm') :
    L.OracleAt κ (M' + 1) h c cm (Lu.map (fun q => regVal (runX (L.mach (M' + 1) g) i s) q.2))
      (L.worldPR κ (M' + 1) h (P (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i))
        (R (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i)) w) := by
  have hM : 0 < M' + 1 := Nat.succ_pos M'
  have hh : h ∈ L.P.funcs := L.callee_mem hcal
  have hbud := L.budget_step hκ hM hg hcal
  have hnr := L.noRetAt_upTo hL hg hME hra htr hsp herr
  obtain ⟨E, hE, hsb, -, N', hret, -, htabC⟩ := L.tabUpTo_call_at htab hnr hcp hct
  obtain ⟨e0, he0⟩ := htab i (fun j hj => hnr j (by omega))
  have hx : x = Clif.sumTo E (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i) :=
    (hcnt e0 he0).symm.trans (hE e0 he0)
  have hst : spv (runX (L.mach (M' + 1) g) i s) = c := (hsw.1 _ (by simp [Masked])).trans hspw
  have hspW : spv (L.worldPR κ (M' + 1) h
      (P (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i))
      (R (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i)) w) = c :=
    (L.r_worldPR_out (κ := κ) (M := M' + 1) h _ _ w (f := .GPR 31#5)
      (fun hm => by simp [MaskedReg, Masked] at hm)).trans hspw
  have hdeadW : ∀ a, StackBelow (frameDrop (L.A h).af + κ (M' + 1 - 1) h) (spv w) a →
      F a ∧ ¬ L.Img a := fun a ha => hdead a (by rw [← hspw]; exact stackBelow_mono ha hbud)
  obtain ⟨hcOk, hmsk, hrgn, hswW⟩ := L.callerFacts hL hκ hM hg hh hcal himgF hLu hsw himgT hrah
    hmskQ hrgnQ hdeadW
  -- the slot bytes
  have hslot : L.NeedSlots → ∀ a, L.SlotByte h c a →
      (ini.adv x).bytes ((ini.adv x).next + 1) a =
        (L.worldPR κ (M' + 1) h (P (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i))
          (R (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i)) w).mem
          (BitVec.ofNat 64 a) := by
    intro _ a ha
    have h1 : slotted h = 1 := by
      obtain ⟨p, hp, -⟩ := ha
      unfold slotted
      cases hs : h.slots with
      | nil => rw [hs] at hp; cases hp
      | cons _ _ => rfl
    obtain ⟨hbel, -⟩ := L.slotByte_below hL hg hcal (c := c) (by omega) ha
    have hrg : StackBelow (frameDrop (L.A h).af + κ (M' + 1 - 1) h) c (BitVec.ofNat 64 a) :=
      stackBelow_mono hbel (by omega)
    have e1 := hsb h1 a (by rw [hst]; exact ha)
    simp only [Clif.SlotInit.adv]
    rw [hx, e1, hrgnQ _ (by rw [hst]; exact stackBelow_mono hrg hbud), L.mem_worldPR, worldP,
      mem_overlay_in (show L.calleeRgn κ (M' + 1) h w (BitVec.ofNat 64 a) by
        unfold calleeRgn; rw [hspw]; exact hrg)]
  -- the actual callee run's table
  have htabT : L.TableOf M' h (enterAt (L.A h) (runX (L.mach (M' + 1) g) i s))
      (calleeIni h (ini.adv x)) := by
    refine L.tableOf_callee (e := E (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i) -
      slotted h) hret ?_
    rw [calleeIni_bytes, calleeIni_next]
    simp only [Clif.SlotInit.adv]
    rw [hx]
    exact htabC
  refine ⟨ini.adv x, hpl, hslot, ?_⟩
  exact hdt h.name h hpf ⟨g, hg, hcal⟩ F himgF _ _
    (by rw [show Arm.r .ERR _ = Arm.r .ERR w from
          L.r_worldPR_out h _ _ w (fun hm => by simp [MaskedReg, Masked] at hm),
        ← hsw.1 .ERR (by simp [Masked])]; exact herr)
    (by rw [hspW]; exact halign) (by rw [hspW]; have := hbud; omega)
    (fun a ha => hdead a (by rw [hspW] at ha; exact stackBelow_mono ha hbud))
    vals cm cs rvals cm' (ini.adv x) hmrW hargsW hsavW (fun hN => by rw [hspW]; exact hpl hN)
    (fun hN => by rw [hspW]; exact hslot hN) hinit hrun _ hcOk hmsk hrgn htabT

end LinkSys

end E2E
