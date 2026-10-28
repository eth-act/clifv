import FV.E2E.LinkArmLockRet
import FV.E2E.BackendTwoRunLE

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

end LinkSys

end E2E
