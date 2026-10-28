import FV.E2E.LinkArmLockRet
import FV.E2E.BackendTwoRunLE
import FV.E2E.LinkArmProgOsPRBRL

/-!
# The call hook from two locked call states (SEM1 #537, #713, step 3)

`backend_twoRunLERWZIUPF_either`'s `hcall` asks the machine's call hook to keep the lock
(`StEqOutX Z`) of two call states. For a call of a function `h` of `P` the hook is `pcall`, the
callee's run one level down. `CallLock` (`LinkArmLockRet.lean`) locks each of the two callee runs
with the canonical callee run (both call states agree with the canonical one: `CallerOk`, masked
registers but `x30`/pc, the callee region), at the canonical return index; composing the two
gives two returns equal but for `Z`: registers by `RetAgreeX` (the pc: both return addresses),
the callee region by `RetAgreeX` and the saved frame record (both entries' `x30` is the call's
`pc + 4`, `x29` the caller's), memory outside `F` the canonical return's, the rest of `F` kept
from the call states.

* `mem_eq_of_saved`;
* **`pcall_lock`**.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- **Two states with the same saved frame record below `c` agree on its top 8 bytes.** -/
theorem mem_eq_of_saved {c : BitVec 64} {s t : Arm.ArmState} (h16 : 16 ≤ c.toNat)
    (h : Arm.read_mem_bytes 16 (c - 16#64) s = Arm.read_mem_bytes 16 (c - 16#64) t)
    {a : BitVec 64} (ha : StackBelow 8 c a) : s.mem a = t.mem a := by
  obtain ⟨h1, h2⟩ := ha
  have hc : (c - 16#64).toNat = c.toNat - 16 := by
    rw [BitVec.toNat_sub]; simp; omega
  have hlt := c.isLt
  have e : a = (c - 16#64) + BitVec.ofNat 64 (a.toNat - (c.toNat - 16)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, hc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : a.toNat - (c.toNat - 16) < 2 ^ 64)]
    omega
  rw [e]
  exact mem_eq_of_read_mem_bytes h (by decide) (by omega)

namespace LinkSys

variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

/-- **The program call hook keeps a lock** of two call states that both agree with the canonical
call state (module doc). -/
theorem pcall_lock (hL : L.Ok) {M : Nat} (hcl : L.CallLock κ M) {nm : String} {h : Clif.Function}
    (hpf : L.P.func? nm = some h) (hcal : ∃ g ∈ L.P.funcs, L.Callee g h)
    {F : BitVec 64 → Prop} (himgF : ∀ a, L.Img a → F a)
    {uses : List CV} {w : Arm.ArmState} (herr : Arm.r .ERR w = .None)
    (hal : (spv w).toNat % 16 = 0)
    (hroom : frameDrop (L.A h).af + κ (M - 1) h ≤ (spv w).toNat)
    (hdead : ∀ a, StackBelow (frameDrop (L.A h).af + κ (M - 1) h) (spv w) a → F a ∧ ¬ L.Img a)
    {vals : List Clif.Val} {cm : Clif.Mem} {cs : Clif.State} {rvals : List Clif.Val}
    {cm' : Clif.Mem} {ini : Clif.SlotInit} (hmr : MemRel F L.syms cm w)
    (hargs : ArgsAt h.sig vals uses w)
    (hsav : StackArgsAvoid F h.sig vals w) (hpl : L.NeedSlots → L.PlaceAtB cm (spv w) ini)
    (hslotb : L.NeedSlots → ∀ a, L.SlotByte h (spv w) a →
      ini.bytes (ini.next + 1) a = w.mem (BitVec.ofNat 64 a))
    (htab : L.TableOf (M - 1) h (enterAt (L.A h) (L.canon h uses w)) (calleeIni h ini))
    (hinit : Clif.initState L.P nm vals cm = .ok cs)
    (hrun : L.crun M cs = .returned rvals cm')
    {u u' : Arm.ArmState} (hu : L.CallerOk F h uses w u)
    (hmu : ∀ f, Masked f → f ≠ .PC → f ≠ .GPR 30#5 → Arm.r f u = Arm.r f (L.canon h uses w))
    (hdu : ∀ a, StackBelow (frameDrop (L.A h).af + κ (M - 1) h) (spv w) a →
      u.mem a = (L.canon h uses w).mem a)
    (hu' : L.CallerOk F h uses w u')
    (hmu' : ∀ f, Masked f → f ≠ .PC → f ≠ .GPR 30#5 → Arm.r f u' = Arm.r f (L.canon h uses w))
    (hdu' : ∀ a, StackBelow (frameDrop (L.A h).af + κ (M - 1) h) (spv w) a →
      u'.mem a = (L.canon h uses w).mem a)
    {Z : BitVec 64 → Prop} (hZ : StEqOutX Z u u') :
    StEqOutX Z (L.pcall M h u) (L.pcall M h u') := by
  have hh := (Clif.Program.func?_some hpf).1
  have h16 : 16 ≤ (spv w).toNat := by
    have := lowerRFunc_frame (hL.compiled h hh).alloc
    simp only [frameDrop, this, ↓reduceIte] at hroom
    omega
  obtain ⟨k, hk⟩ := hcl nm h hpf hcal F himgF uses w herr hal hroom hdead vals cm cs rvals cm' ini
    hmr hargs hsav hpl hslotb htab hinit hrun
  obtain ⟨e1, -, ra1, mo1, sv1, ar1, kp1⟩ := hk u hu hmu hdu
  obtain ⟨e2, -, ra2, mo2, sv2, ar2, kp2⟩ := hk u' hu' hmu' hdu'
  have hpc : Arm.r .PC u = Arm.r .PC u' := hZ.1 _ (by decide)
  rw [e1, e2]
  refine ⟨fun f hf => ?_, by simp only [program_set_program]; exact hZ.2.1, fun a ha => ?_⟩
  · rw [r_set_program, r_set_program]
    by_cases hfp : f = .PC
    · subst hfp; rw [ar1.pc, ar2.pc, hpc]
    · rw [ra1.1 f hfp hf, ra2.1 f hfp hf]
  · rw [mem_set_program, mem_set_program]
    by_cases hr : StackBelow (frameDrop (L.A h).af + κ (M - 1) h) (spv w) a
    · by_cases h8 : StackBelow 8 (spv w) a
      · have h29 : xreg 29 (enterAt (L.A h) u) = xreg 29 (enterAt (L.A h) u') := by
          simp only [xreg]
          rw [r_enterAt _ _ (by decide) (by decide), r_enterAt _ _ (by decide) (by decide)]
          exact hZ.1 _ (by decide)
        refine mem_eq_of_saved h16 ?_ h8
        rw [sv1, sv2, x30_enterAt, x30_enterAt, hpc, h29]
      · rw [ra1.2 a hr h8, ra2.2 a hr h8]
    · by_cases hF : F a
      · rw [kp1 a hF hr, kp2 a hF hr]; exact hZ.2.2 a ha
      · rw [mo1 a hF, mo2 a hF]

set_option maxHeartbeats 1000000 in
/-- **The program call hook keeps a lock at the first run's call state** (`progOsCoreXPRRBRLR`'s
premises: the call state `t` with the masked registers of `R n`, the prophecy `P n` below its
`sp`, and `progXPRBT`'s answer at its world): from a second state `t'` locked with `t` by a set
inside `F` avoiding the callees' dead stack, holding the code image, the two hook results are
locked by the same set (`pcall_lock` on the canonical callee state of `worldPR … (P n) (R n) w`). -/
theorem pcall_lockXPR (hL : L.Ok) (hκ : L.Budget κ) {M : Nat} (hcl : L.CallLock κ M)
    {g h : Clif.Function} (hg : g ∈ L.P.funcs) (hh : h ∈ L.P.funcs) (hcal : L.Callee g h)
    {F G : BitVec 64 → Prop} {s0 : Arm.ArmState} (himgF : ∀ a, L.Img a → F a)
    (himgG : ∀ a, L.Img a → G a) (himgS : ∀ a, L.Img a → s0.mem a = L.imgMem a)
    {Lu : List (Nat × Reg)} (hLu : Lu.map (·.2) = regLocs h.sig)
    {t t' w w' : Arm.ArmState} {outs : List CV}
    (hG : ∀ a, G a → t.mem a = s0.mem a) (hra : RaOk (L.A h) (Arm.r .PC t))
    (hsw : SameWorld F t w)
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {n : Nat}
    (hmskQ : ∀ f, MaskedReg f → Arm.r f t = Arm.r f (R n))
    (hrgnQ : ∀ a, StackBelow (κ M g) (spv t) a → t.mem a = P n a)
    (hx : L.progXPRBT κ M F h (Lu.map (fun q => regVal t q.2)) (P n) (R n) w = some (outs, w'))
    {Z : BitVec 64 → Prop} (hZ : StEqOutX Z t t') (hZF : ∀ a, Z a → F a)
    (hZd : ∀ a, StackBelow (κ M g) (spv t) a → ¬ Z a)
    (himgt' : ∀ a, L.Img a → t'.mem a = L.imgMem a) :
    StEqOutX Z (L.pcall M h t) (L.pcall M h t') := by
  have hpf := func?_of_mem hL.names hh
  obtain ⟨hnd, harg, -⟩ := hL.argRegs h hh
  let W := L.worldPR κ M h (P n) (R n) w
  replace hx : L.progXBT κ M F h (Lu.map (fun q => regVal t q.2)) W = some (outs, w') := hx
  have hcondW : L.CondBT κ M F h (Lu.map (fun q => regVal t q.2)) W := by
    have hx' := hx
    unfold progXBT at hx'
    exact Classical.byContradiction fun hc => by rw [if_neg (fun h' => hc h'.1)] at hx'; cases hx'
  obtain ⟨hM, herrw, halw, hroom, hdeadW, vals, cm, cs, rvals, cm', ini, hmr, hargs, hsav, hpl,
    htab, hinit, hrun⟩ := hcondW
  have hspW : spv W = spv w :=
    L.r_worldPR_out (κ := κ) (M := M) h (P n) (R n) w (f := .GPR 31#5)
      (fun hm => by simp [MaskedReg, Masked] at hm)
  have hst : spv t = spv w := hsw.1 _ (by simp [Masked])
  -- `t`'s arguments are `W`'s
  have hmaskedF : ∀ (r : Reg) (f : Arm.StateField), r.isArgReg = true → r.field = some f →
      MaskedReg f := by
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
  have hreg : ∀ a, StackBelow (frameDrop (L.A h).af + κ (M - 1) h) (spv W) a →
      StackBelow (κ M g) (spv t) a := fun a ha => by
    rw [hspW] at ha
    exact stackBelow_mono (by rw [hst]; exact ha) (L.budget_step hκ hM hg hcal)
  have hrgn : ∀ a, StackBelow (frameDrop (L.A h).af + κ (M - 1) h) (spv W) a →
      t.mem a = (L.canon h (Lu.map (fun q => regVal t q.2)) W).mem a := by
    intro a ha
    have hFI := hdeadW a ha
    rw [hspW] at ha
    rw [L.mem_canon, mem_withImg, if_neg hFI.2, L.mem_worldPR, worldP,
      mem_overlay_in (show L.calleeRgn κ M h w a from ha)]
    exact hrgnQ a (stackBelow_mono (by rw [hst]; exact ha) (L.budget_step hκ hM hg hcal))
  have hsw' : SameWorld F t W :=
    ⟨fun f hf => (hsw.1 f hf).trans (L.r_worldPR_out h _ _ w (fun hm => hf hm.1)).symm,
      fun a ha => (hsw.2.1 a ha).trans (by
        rw [L.mem_worldPR, worldP, mem_overlay_out (R := L.calleeRgn κ M h w)
          (fun hr => ha (hdeadW a (by rw [hspW]; exact hr)).1)]),
      hsw.2.2.trans (L.program_worldPR h _ _ w).symm⟩
  -- the first call state is a caller of the canonical state
  have hcOk : L.CallerOk F h (Lu.map (fun q => regVal t q.2)) W t := by
    refine ⟨hsw', fun a ha => (hG a (himgG a ha)).trans (himgS a ha), fun r hr => ?_, hra⟩
    rw [← hLu] at hr
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hr
    have hrA : r.isArgReg = true := harg r (by rw [← hLu]; exact List.mem_of_getElem? hj)
    have hu : (Lu.map (fun q => regVal t q.2))[j]? = some (regVal t r) := by
      simp only [List.getElem?_map, Option.map_eq_some_iff] at hj
      obtain ⟨q, hq, rfl⟩ := hj
      simp [hq]
    rw [L.regVal_canon _ _ _ hrA, placeArgs_regVal _ _ _ hnd harg (by rw [← hLu]; exact hj) hu,
      setVal_regVal]
  -- the second call state too
  have h30n : ∀ f, ¬ Masked f → f ≠ .GPR 30#5 := fun f hf e => hf (by subst e; simp [Masked])
  have hcOk' : L.CallerOk F h (Lu.map (fun q => regVal t q.2)) W t' := by
    refine ⟨⟨fun f hf => (hZ.1 f (h30n f hf)).symm.trans (hsw'.1 f hf),
      fun a ha => (hZ.2.2 a (fun hz => ha (hZF a hz))).symm.trans (hsw'.2.1 a ha),
      hZ.2.1.symm.trans hsw'.2.2⟩, himgt', fun r hr => ?_, ?_⟩
    · rw [← hcOk.regs r hr]
      exact regVal_eq_of_field (harg r hr) fun f hf =>
        (hZ.1 f (argReg_ne29 (harg r hr) hf).2.2.1).symm
    · rw [← hZ.1 .PC (by decide)]; exact hra
  have hmsk' : ∀ f, Masked f → f ≠ .PC → f ≠ .GPR 30#5 →
      Arm.r f t' = Arm.r f (L.canon h (Lu.map (fun q => regVal t q.2)) W) :=
    fun f hf hpc h30 => (hZ.1 f h30).symm.trans (hmsk f hf hpc h30)
  have hrgn' : ∀ a, StackBelow (frameDrop (L.A h).af + κ (M - 1) h) (spv W) a →
      t'.mem a = (L.canon h (Lu.map (fun q => regVal t q.2)) W).mem a :=
    fun a ha => (hZ.2.2 a (hZd a (hreg a ha))).symm.trans (hrgn a ha)
  exact L.pcall_lock hL hcl hpf ⟨g, hg, hcal⟩ himgF herrw halw hroom hdeadW hmr hargs hsav
    (fun hN => (hpl hN).1) (fun hN => (hpl hN).2) htab hinit hrun hcOk hmsk hrgn hcOk' hmsk' hrgn' hZ

end LinkSys

end E2E
