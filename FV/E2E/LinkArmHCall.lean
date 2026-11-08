import FV.E2E.LinkArmLockRet
import FV.E2E.BackendTwoRunLE
import FV.E2E.LinkArmProgOsPRBRL
import FV.E2E.LinkArmBaseNIX

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
from the call states. At the first run's call state of count `n` the canonical callee state is the
one of `progXPRBT`'s answer (`worldPR … (P n) (R n) w`), which the second run's locked state also
agrees with (`pcall_lockXPR`). Base calls and TLS: the trusted `HookNIX` (`OkDNX.baseNIX`).

* `mem_eq_of_saved`;
* **`pcall_lock`**, **`pcall_lockXPR`**;
* `hooks_lock_base`, `hooks_lock_tls`.
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
      ini.bytes (ini.next + 1) a = probeMem (L.A h).af w (BitVec.ofNat 64 a))
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
    hmr hargs hsav hpl hslotb (L.tableOfE_of htab) hinit hrun
  obtain ⟨e1, -, ra1, mo1, sv1, ar1, kp1, -⟩ := hk u hu hmu hdu
  obtain ⟨e2, -, ra2, mo2, sv2, ar2, kp2, -⟩ := hk u' hu' hmu' hdu'
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

/-- **A base call of the linked machine keeps a lock inside `F`** (`HookNIX`, the trusted base-hook
premise `OkDNX.baseNIX` under `NeedNI`): a call of a destination outside `P` (for a `blr`, no
function of `P` at the target in either state). -/
theorem hooks_lock_base {F : BitVec 64 → Prop} (hN : HookNIX L.Hb L.BaseDest F) {M : Nat}
    {d : Option String} (hb : L.BaseDest d) {u u' : Arm.ArmState}
    (hn : d = none → (blrTarget u).bind (symCallee L.Xb L.P) = none)
    (hn' : d = none → (blrTarget u').bind (symCallee L.Xb L.P) = none)
    {Z : BitVec 64 → Prop} (hZ : StEqOutX Z u u') (hZF : ∀ a, Z a → F a) :
    StEqOutX Z ((L.hooks M).call d u) ((L.hooks M).call d u') := by
  rw [L.hooks_base hb u hn, L.hooks_base hb u' hn']
  exact hN.1 d hb Z u u' hZ hZF

/-- **The TLS hook of the linked machine keeps a lock inside `F`** (`HookNIX`). -/
theorem hooks_lock_tls {F : BitVec 64 → Prop} (hN : HookNIX L.Hb L.BaseDest F) (M : Nat)
    (m : String) (r : Reg) {u u' : Arm.ArmState} {Z : BitVec 64 → Prop} (hZ : StEqOutX Z u u')
    (hZF : ∀ a, Z a → F a) : StEqOutX Z ((L.hooks M).tls m r u) ((L.hooks M).tls m r u') := by
  rw [L.hooks_tls]
  exact hN.2 m r Z u u' hZ hZF

set_option maxHeartbeats 2000000 in
/-- **`hookLock_call` for any clobber list of the static check** (the call of a `try_call`
is checked with the `try_call`'s clobbers; only the operands' locations are used). -/
theorem hookLock_callS (hL : L.Ok) (hκ : L.Budget κ) {M : Nat} (hcl : L.CallLock κ M)
    {F : BitVec 64 → Prop} (hN : HookNIX L.Hb L.BaseDest F)
    {g : Clif.Function} (hg : g ∈ L.P.funcs) {G : BitVec 64 → Prop} {s0 : Arm.ArmState}
    (himgF : ∀ a, L.Img a → F a) (himgG : ∀ a, L.Img a → G a)
    (himgS : ∀ a, L.Img a → s0.mem a = L.imgMem a)
    {info : CallInfo} (hsite : (L.A g).vcp.CallSite info) (ctx : FnCtx)
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {n : Nat}
    {t t' : Arm.ArmState}
    (hmskQ : ∀ f, MaskedReg f → Arm.r f t = Arm.r f (R n))
    (hrgnQ : ∀ a, StackBelow (κ M g) (spv t) a → t.mem a = P n a)
    {c : CheckCtx} {wh : String} {ops : Array Operand} {regs : Array Reg} {i' : MInst}
    {w : Arm.ArmState} {outs : List CV} {w' : Arm.ArmState}
    (hops : (MInst.call info).operands = .ok ops)
    (hst : ∃ clob, c.checkStatic wh ops (regs.map .reg) clob = .ok ())
    (hasg : (MInst.call info).assign regs = .ok i')
    (hP : CallAt (L.A g).fa (L.A g).base (Arm.r .PC t) i') (hsw : SameWorld F t w)
    (hG : ∀ a, G a → t.mem a = s0.mem a)
    (hsem : csemV (GotV (L.A g).vcp) F ctx (L.XPRBT κ M g F P R n) (.call info)
      (useVals ops regs t) w = some (outs, w', .next))
    {Z : BitVec 64 → Prop} (hZ : StEqOutX Z t t') (hZF : ∀ a, Z a → F a)
    (hZd : ∀ a, StackBelow (κ M g) (spv t) a → ¬ Z a)
    (himgt' : ∀ a, L.Img a → t'.mem a = L.imgMem a) :
    StEqOutX Z ((L.hooks M).call (callDest info) t) ((L.hooks M).call (callDest info) t') := by
  obtain ⟨clob, hst⟩ := hst
  cases hd : info.dest with
  | sym nm =>
    have hcd : callDest info = some nm := by simp [callDest, hd]
    rw [hcd]
    cases hpf : L.P.func? nm with
    | none =>
      exact L.hooks_lock_base hN (.inr ⟨nm, rfl, hpf⟩) (fun h => by cases h) (fun h => by cases h)
        hZ hZF
    | some h =>
      have hsite' : L.ProgSite g info h := ⟨hsite, nm, hd, hpf⟩
      obtain ⟨hh, hname⟩ := Clif.Program.func?_some hpf
      subst hname
      obtain ⟨n', Lu, Ld, hinfo, hLu, -⟩ := hL.callRegs g hg info h hsite'
      subst hinfo
      cases hd
      replace hsem := csemV_sub hsem
      rw [operands_call_sym] at hops
      cases hops
      obtain ⟨hsz', hloc, -, -⟩ := checkStatic_facts hst
      have hregs := callRegs_eq (regs := regs) (by simpa using hsz')
        (fun p hp r hr => (hloc p hp).2 r hr)
      rw [call_useVals hregs] at hsem
      have hx : L.progXPRBT κ M F h (Lu.map (fun q => regVal t q.2)) (P n) (R n) w =
          some (outs, w') := by
        simp only [csem, Option.map_eq_some_iff, Prod.mk.injEq] at hsem
        obtain ⟨⟨o, w2⟩, hx, rfl, rfl, -⟩ := hsem
        rw [L.XPRBT_prog hpf] at hx
        exact hx
      rw [L.hooks_some hpf, L.hooks_some hpf]
      exact L.pcall_lockXPR hL hκ hcl hg hh (.inl ⟨_, hsite'⟩) himgF himgG himgS hLu hG
        (hL.raCall g hg _ h hsite' _ hP.callPc) hsw hmskQ hrgnQ hx hZ hZF hZd himgt'
  | reg r =>
    have hcd : callDest info = none := by simp [callDest, hd]
    rw [hcd]
    obtain ⟨tv, Lu, Ld, hinfo, hregs⟩ := hL.blrRegs g hg info hsite (fun n => by rw [hd]; simp)
    subst hinfo
    have hguard := csemV_guard hsem
    replace hsem := csemV_sub hsem
    rw [operands_call_reg] at hops
    cases hops
    obtain ⟨hsz', hloc, -, -⟩ := checkStatic_facts hst
    obtain ⟨r0, hregs0⟩ := callRegs_eq_reg (regs := regs) (by simpa using hsz')
      (fun p hp r hr => (hloc p hp).2 r hr)
    obtain ⟨n0, rfl, hn0, -⟩ : ∃ n, r0 = .x n ∧ n < 29 ∧ n ≠ 16 := by
      have hmem : (tgtOp tv, Loc.reg r0) ∈
          (((tgtOp tv :: (retOps Lu ++ callDefOps Ld)).toArray).zip (regs.map Loc.reg)).toList := by
        simp [Array.toList_zip, Array.toList_map, hregs0]
      obtain ⟨n, hn, h29, h16, -⟩ := locOk_int (hloc _ hmem).1
      exact ⟨n, hn, h29, h16⟩
    rw [call_useVals_reg hregs0] at hsem
    obtain ⟨r1, us', ds', hr1, rfl⟩ := assign_call_reg hasg
    have h0 : regs[0]? = some (.x n0) := by
      rw [← Array.getElem?_toList, hregs0]; rfl
    rw [h0] at hr1
    cases hr1
    -- the targets the machine reads, in both states
    have hc := hL.compiled g hg
    obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hc.layout
    have hcp := hP.callPc
    obtain ⟨j, x, tt, hj, hx, hpc⟩ := hP
    simp only [MInst.callInsn?, Option.some.injEq] at hx
    subst hx
    have htgt : blrTarget t = some (lo64 (regVal t (.x n0))) := by
      rw [lo64_regVal_x]
      exact blrTarget_of hc.layout hlm hj hn0 hpc
        (fun k wd hk => hL.imgCode g hg t (fun a ha => (hG a (himgG a ha)).trans (himgS a ha)) k wd hk)
    have hne : Arm.StateField.GPR (rnum n0) ≠ .GPR 30#5 := by
      intro e
      have := congrArg (fun f => match f with | Arm.StateField.GPR i => i.toNat | _ => 0) e
      simp [rnum_toNat (show n0 < 32 by omega)] at this; omega
    have hx0 : regVal t' (.x n0) = regVal t (.x n0) := by
      simp only [regVal]; rw [hZ.1 _ hne]
    have htgt' : blrTarget t' = some (lo64 (regVal t (.x n0))) := by
      rw [← hx0, lo64_regVal_x]
      exact blrTarget_of hc.layout hlm hj hn0 (by rw [← hZ.1 .PC (by decide)]; exact hpc)
        (fun k wd hk => hL.imgCode g hg t' himgt' k wd hk)
    have hx : (L.XPRBT κ M g F P R n).call none
        (regVal t (.x n0) :: Lu.map (fun q => regVal t q.2)) w = some (outs, w') := by
      simp only [csem, Option.map_eq_some_iff, Prod.mk.injEq] at hsem
      obtain ⟨⟨o, w2⟩, hx, rfl, rfl, -⟩ := hsem
      exact hx
    cases hs : symCallee L.Xb L.P (lo64 (regVal t (.x n0))) with
    | none =>
      exact L.hooks_lock_base hN (.inl rfl) (fun _ => by rw [htgt]; exact hs)
        (fun _ => by rw [htgt']; exact hs) hZ hZF
    | some h =>
      rw [L.XPRBT_ind hs] at hx
      split at hx
      · rename_i hdecl
        have hh : h ∈ L.P.funcs := List.mem_of_find?_eq_some hs
        have hgot : ∀ n, GotV (L.A g).vcp tv n → n = h.name := by
          intro n hn
          have e := hguard tv n _ rfl hn (operands_call_reg tv Lu Ld) (by simp [tgtOp, Operand.isUse])
          rw [call_useVals_reg hregs0] at e
          simp only [List.head?_cons, Option.map_some, Option.some.injEq] at e
          exact L.got_target hL hs e
        obtain ⟨hLu, -⟩ := hregs h hh ⟨hdecl.1, hgot⟩ (by rw [← hdecl.2, List.length_map])
        rw [L.hooks_none (by rw [htgt]; exact hs), L.hooks_none (by rw [htgt']; exact hs)]
        exact L.pcall_lockXPR hL hκ hcl hg hh (.inr (.inr ⟨hh, hdecl.1.1⟩)) himgF himgG himgS hLu
          hG (hL.raBlr g hg _ hsite (fun n => by simp) h hh hdecl.1.1 _ hcp)
          hsw hmskQ hrgnQ hx hZ hZF hZd himgt'
      · cases hx

/-- **The call hook keeps a lock at a `call` of the first run's call-`n` state** (the dispatch of
`progOsPRBRLR`/`progOsRegPRBRLR`): from `XPRBT … n`'s answer at the call's world, a call of a
function of `P` (`bl`, or `blr` of its address) by `pcall_lockXPR`, a base call by
`hooks_lock_base` (the second state's `blr` target is the first's: the target register is not
`x30`). -/
theorem hookLock_call (hL : L.Ok) (hκ : L.Budget κ) {M : Nat} (hcl : L.CallLock κ M)
    {F : BitVec 64 → Prop} (hN : HookNIX L.Hb L.BaseDest F)
    {g : Clif.Function} (hg : g ∈ L.P.funcs) {G : BitVec 64 → Prop} {s0 : Arm.ArmState}
    (himgF : ∀ a, L.Img a → F a) (himgG : ∀ a, L.Img a → G a)
    (himgS : ∀ a, L.Img a → s0.mem a = L.imgMem a)
    {info : CallInfo} (hsite : (L.A g).vcp.CallSite info) (ctx : FnCtx)
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {n : Nat}
    {t t' : Arm.ArmState}
    (hmskQ : ∀ f, MaskedReg f → Arm.r f t = Arm.r f (R n))
    (hrgnQ : ∀ a, StackBelow (κ M g) (spv t) a → t.mem a = P n a)
    {c : CheckCtx} {wh : String} {ops : Array Operand} {regs : Array Reg} {i' : MInst}
    {w : Arm.ArmState} {outs : List CV} {w' : Arm.ArmState}
    (hops : (MInst.call info).operands = .ok ops)
    (hst : c.checkStatic wh ops (regs.map .reg) (MInst.call info).clobbers = .ok ())
    (hasg : (MInst.call info).assign regs = .ok i')
    (hP : CallAt (L.A g).fa (L.A g).base (Arm.r .PC t) i') (hsw : SameWorld F t w)
    (hG : ∀ a, G a → t.mem a = s0.mem a)
    (hsem : csemV (GotV (L.A g).vcp) F ctx (L.XPRBT κ M g F P R n) (.call info)
      (useVals ops regs t) w = some (outs, w', .next))
    {Z : BitVec 64 → Prop} (hZ : StEqOutX Z t t') (hZF : ∀ a, Z a → F a)
    (hZd : ∀ a, StackBelow (κ M g) (spv t) a → ¬ Z a)
    (himgt' : ∀ a, L.Img a → t'.mem a = L.imgMem a) :
    StEqOutX Z ((L.hooks M).call (callDest info) t) ((L.hooks M).call (callDest info) t') :=
  L.hookLock_callS hL hκ hcl hN hg himgF himgG himgS hsite ctx hmskQ hrgnQ hops ⟨_, hst⟩ hasg hP
    hsw hG hsem hZ hZF hZd himgt'

end LinkSys

end E2E
