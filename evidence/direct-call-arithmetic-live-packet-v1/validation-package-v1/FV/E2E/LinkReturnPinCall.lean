import FV.E2E.LinkReturnPinContract
import FV.E2E.WorldReturnPinBoundary

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver Clif Opt
set_option autoImplicit false
set_option Elab.async false
namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat} {modes : Clif.Function → ReturnPinMode}

theorem callerOk_canon_return_pins (hL : L.OkReturnPins modes) {g : Clif.Function} (hg : g ∈ L.P.funcs) {F : BitVec 64 → Prop}
    (himgF : ∀ a, L.Img a → F a) (uses : List CV)
    (w : Arm.ArmState) : L.CallerOk F g uses w (L.canon g uses w) := by
  have harg := (hL.argRegs g hg).2.1
  refine ⟨⟨fun f hf => L.r_canon harg uses w hf, fun a ha => ?_, L.program_canon g uses w⟩,
    fun a ha => ?_, fun _ _ => rfl, .inl fun k hk => ?_⟩
  · rw [L.mem_canon, mem_withImg, if_neg (fun hi => ha (himgF a hi))]
  · rw [L.mem_canon, mem_withImg, if_pos ha]
  · simp only [canon, Arm.r_of_w_same, BitVec.sub_add_cancel]
    exact hL.raStar g hg k hk
end LinkSys

namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat} {modes : Clif.Function → ReturnPinMode}

theorem bodyEntryW_compat_return_pins (hL : L.OkReturnPins modes) {h : Clif.Function} (hh : h ∈ L.P.funcs) {F : BitVec 64 → Prop}
    (himgF : ∀ a, L.Img a → F a) {uses : List CV}
    {w t : Arm.ArmState} (ht : L.CallerOk F h uses w t) :
    BodyEntryW F (L.A h).vcp.EntryArg (L.A h).af (enterAt (L.A h) t)
      (bodyOf (L.A h).af (enterAt (L.A h) (L.canon h uses w))) := by
  have harg := (hL.argRegs h hh).2.1
  have hc := L.callerOk_canon_return_pins hL hh himgF uses w
  have hsp : spv (enterAt (L.A h) (L.canon h uses w)) = spv (enterAt (L.A h) t) := by
    rw [spv_enterAt, spv_enterAt]; simp only [spv]
    rw [hc.world.1 _ (by simp [Masked]), ht.world.1 _ (by simp [Masked])]
  have h29 : xreg 29 (enterAt (L.A h) (L.canon h uses w)) = xreg 29 (enterAt (L.A h) t) := by
    simp only [xreg]
    rw [r_enterAt _ _ (by simp) (by simp), r_enterAt _ _ (by simp) (by simp),
      hc.world.1 _ (by simp [Masked]), ht.world.1 _ (by simp [Masked])]
  refine ⟨by rw [spv_bodyOf, hsp], by rw [x29_bodyOf, hsp, h29], fun r hr => ?_, fun f hf h29' h31 => ?_,
    fun a ha => ?_, by simp⟩
  · have hra := harg r (hL.entryRegs h hh r hr)
    rw [regVal_bodyOf _ _ hra, regVal_enterAt _ _ hra, regVal_enterAt _ _ hra,
      ht.regs r (hL.entryRegs h hh r hr)]
  · have hpc : f ≠ .PC := by rintro rfl; exact hf trivial
    have h30 : f ≠ .GPR 30#5 := by rintro rfl; exact hf (by simp [Masked])
    rw [r_bodyOf _ _ h29' h31, r_enterAt _ _ hpc h30, r_enterAt _ _ hpc h30,
      hc.world.1 f hf, ht.world.1 f hf]
  · rw [mem_bodyOf, mem_enterAt, mem_enterAt, hc.world.2.1 a ha, ht.world.2.1 a ha]
end LinkSys

namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat} {modes : Clif.Function → ReturnPinMode}

theorem frameSize_mod_return_pins (hL : L.OkReturnPins modes) {h : Clif.Function} (hh : h ∈ L.P.funcs) :
    (L.A h).af.frameSize % 16 = 0 := by
  rw [(lowerRFunc_ok (hL.compiled h hh).alloc).1.1]
  have h1 := compute_saveBase (L.A h).vcp (L.A h).rf
  have h2 := clobberBytes_mod (L.A h).rf.saved
  omega
end LinkSys

namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat} {modes : Clif.Function → ReturnPinMode}

theorem frameDrop_eq_return_pins (hL : L.OkReturnPins modes) {h : Clif.Function} (hh : h ∈ L.P.funcs) :
    frameDrop (L.A h).af = (L.A h).af.frameSize + 16 := by
  simp [frameDrop, lowerRFunc_frame (hL.compiled h hh).alloc]
end LinkSys

namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat} {modes : Clif.Function → ReturnPinMode}

theorem progCall_return_pins (hL : L.OkReturnPins modes) [hR : L.CrunOk] {M : Nat} (hM : 0 < M) (ih : L.ThmReturnPins modes κ (M - 1)) {n : String}
    {h : Clif.Function} (hpf : L.P.func? n = some h) (hcal : ∃ g ∈ L.P.funcs, L.Callee g h)
    (hib : ((RAFrame.compute (L.A h).vcp (L.A h).rf).intBase = 0 ∧
      (RAFrame.compute (L.A h).vcp (L.A h).rf).size = (L.A h).af.frameSize - clobberBytes (L.A h).af.saves) ∨ L.NeedNI)
    {F : BitVec 64 → Prop} (himgF : ∀ a, L.Img a → F a)
    {uses : List CV} {w : Arm.ArmState} (herr : Arm.r .ERR w = .None)
    (hal : (spv w).toNat % 16 = 0)
    (hroom : frameDrop (L.A h).af + κ (M - 1) h ≤ (spv w).toNat)
    (hdead : ∀ a, StackBelow (frameDrop (L.A h).af + κ (M - 1) h) (spv w) a → F a ∧ ¬ L.Img a)
    {vals : List Clif.Val} {cm : Clif.Mem} {cs : Clif.State} {rvals : List Clif.Val}
    {cm' : Clif.Mem} (hmr : MemRel F L.syms cm w) (hargs : ArgsAt h.sig vals uses w)
    (hsav : StackArgsAvoid F h.sig vals w) (hpl : L.NeedSlots → L.PlaceAt cm (spv w))
    (hinit : Clif.initState L.P n vals cm = .ok cs)
    (hrun : L.crun M cs = .returned rvals cm') :
    ∃ (us : List (Reg × Reg)) (outs : List CV) (wf : Arm.ArmState),
      ReturnPinMode.Valid (modes h) h us ∧ us.length = outs.length ∧
      PrefixHold rvals outs ∧ MemRel F L.syms cm' wf ∧ (L.A h).vc.RetsSite us ∧
      (∀ t, L.CallerOk F h uses w t → ∃ k,
        L.pcall M h t =
          Arm.set_program (runX (L.mach (M - 1) h) k (enterAt (L.A h) t)) t.program ∧
        ActRet (Arm.r .PC t + 4) F
          (fun a => F a ∧ ¬ StackBelow (frameDrop (L.A h).af + κ (M - 1) h) (spv w) a)
          us outs wf (enterAt (L.A h) t) (runX (L.mach (M - 1) h) k (enterAt (L.A h) t))) ∧
      (L.NeedNI → ∀ (Z : BitVec 64 → Prop) (t : Arm.ArmState), (∀ a, F a → Z a) →
        SameWorld Z t w → (∀ a, L.Img a → t.mem a = L.imgMem a) →
        (∀ r ∈ regLocs h.sig, regVal t r = regVal (L.canon h uses w) r) →
        RaOk (L.A h) (Arm.r .PC t) →
        MemRel F L.syms cm t →
        (∀ off v, (ArgLoc.stack off, v) ∈ (locsOf h.sig).zip vals → ∀ k < v.ty.bytes,
          t.mem (spv w + BitVec.ofNat 64 off + BitVec.ofNat 64 k) =
            w.mem (spv w + BitVec.ofNat 64 off + BitVec.ofNat 64 k)) → ∃ k,
        L.pcall M h t =
          Arm.set_program (runX (L.mach (M - 1) h) k (enterAt (L.A h) t)) t.program ∧
        ActRet (Arm.r .PC t + 4) Z
          (fun a => F a ∧ ¬ StackBelow (frameDrop (L.A h).af + κ (M - 1) h) (spv w) a)
          us outs wf (enterAt (L.A h) t) (runX (L.mach (M - 1) h) k (enterAt (L.A h) t))) := by
  obtain ⟨hh, hname⟩ := Clif.Program.func?_some hpf
  subst hname
  have hc := hL.compiled h hh
  have hfr := lowerRFunc_frame hc.alloc
  have hdrop := L.frameDrop_eq_return_pins hL hh
  have hfs := L.frameSize_mod_return_pins hL hh
  obtain ⟨hnd, harg, hwid⟩ := hL.argRegs h hh
  have hsl0 : ¬ L.NeedSlots → h.slots = [] := fun hn => Classical.byContradiction fun hne => by
    obtain ⟨g, hg, hcg⟩ := hcal
    exact hn ⟨g, hg, h, hcg, hne⟩
  have hcase : h.slots = [] ∨ L.PlaceAt cm (spv w) := by
    by_cases hN : L.NeedSlots
    · exact .inr (hpl hN)
    · exact .inl (hsl0 hN)
  obtain ⟨hsl', hsym', hal', hby', hpl'⟩ := L.initState_mem hpf hinit hcase
  have hslotB : (L.A h).af.slotBase = (RAFrame.compute (L.A h).vcp (L.A h).rf).size :=
    (lowerRFunc_ok hc.alloc).1.2.1
  have hsz_le := size_le_frameSize hc.alloc
  have hfits : ∀ p ∈ h.slots, ∃ off, (slotLayout h.slots).1.lookup p.1 = some off ∧
      (L.A h).af.slotBase + off + p.2.size ≤ (L.A h).af.frameSize - clobberBytes (L.A h).af.saves := by
    obtain ⟨g, hg, hcg⟩ := hcal
    exact hL.slotFits g hg h hcg
  have hce : ClifEntry h vals cs := clifEntry_initState hpf hinit
  -- the run of the program without functions (program callees: the callee runs one level down)
  obtain ⟨m, hm⟩ := hR.link M hM h hh cs (runInv_entry hh hce)
    (runInv_entry (by simp [Clif.Program.only]) hce) (fun _ => hsym'.trans hmr.symbols)
    (L.envR (M - 1) h) rfl rfl (fun _ hn => L.envR_of (.inl hn)) (L.envR_link hL.names)
    (by rw [hrun]; intro _ e; cases e) (by rw [hrun]; intro e; cases e)
  rw [hrun] at hm
  obtain ⟨Nr, hrunN⟩ := hR.runs M cs _ hrun (.inl ⟨_, _, rfl⟩)
  -- the canonical state and the shared body-entry world
  let cn := L.canon h uses w
  let w₀ := bodyOf (L.A h).af (enterAt (L.A h) cn)
  have hcOk := L.callerOk_canon_return_pins hL hh himgF uses w
  have hsp0 : spv cn = spv w := hcOk.world.1 _ (by simp [Masked])
  have hspw₀ : spv w₀ = spv w - BitVec.ofNat 64 (frameDrop (L.A h).af) := by
    rw [spv_bodyOf, spv_enterAt, hsp0]
  obtain ⟨-, -, hB⟩ := off_toNat 0 (spv w) (frameDrop (L.A h).af) (by omega)
  -- the callee's outgoing area (in the caller's dead stack) is outside the callee's `F`
  let ib := (RAFrame.compute (L.A h).vcp (L.A h).rf).intBase
  let spb := spv w - BitVec.ofNat 64 (frameDrop (L.A h).af)
  let sz := (RAFrame.compute (L.A h).vcp (L.A h).rf).size
  let Fh : BitVec 64 → Prop := fun a =>
    F a ∧ ¬ OutAt ib spb a ∧ ¬ SlotAt sz ((L.A h).af.frameSize - clobberBytes (L.A h).af.saves) spb a
  have hib_le : ib ≤ sz := intBase_le_size _ _
  have hspb : spb.toNat = (spv w).toNat - frameDrop (L.A h).af := hB
  have hlt := (spv w).isLt
  have hout_reg : ∀ a, OutAt ib spb a →
      StackBelow (frameDrop (L.A h).af + κ (M - 1) h) (spv w) a := by
    intro a ⟨h1, h2⟩
    rw [hspb] at h1 h2
    exact ⟨by omega, by omega⟩
  have hout_F : ∀ a, OutAt ib spb a → F a ∧ ¬ L.Img a := fun a ha => hdead a (hout_reg a ha)
  -- the callee's slot region (in the caller's dead stack) is outside the callee's `F`
  have hslot_reg : ∀ a, SlotAt sz ((L.A h).af.frameSize - clobberBytes (L.A h).af.saves) spb a →
      StackBelow (frameDrop (L.A h).af + κ (M - 1) h) (spv w) a := by
    intro a ⟨h1, h2⟩
    rw [hspb] at h1 h2
    exact ⟨by omega, by omega⟩
  have hslot_F : ∀ a, SlotAt sz ((L.A h).af.frameSize - clobberBytes (L.A h).af.saves) spb a → F a ∧ ¬ L.Img a :=
    fun a ha => hdead a (hslot_reg a ha)
  have hspb_add : ∀ j < ib, OutAt ib spb (spb + BitVec.ofNat 64 j) := by
    intro j hj
    have e : (spb + BitVec.ofNat 64 j).toNat = spb.toNat + j := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : j < 2 ^ 64), hspb]
      exact Nat.mod_eq_of_lt (by omega)
    exact ⟨by omega, by omega⟩
  have hOut : ∀ (u : Arm.ArmState), spv u = spb →
      (∀ a n, cs.mem.valid a n = true → ∀ k < n, ¬ OutAt ib spb (BitVec.ofNat 64 (a + k))) →
      OutRel Fh ib cs.mem u := by
    intro u hu hv
    refine ⟨by omega, fun j hj hfh => hfh.2.1 (hu ▸ hspb_add j hj), fun a n hva k hk j hj e => ?_⟩
    rw [hu] at e
    exact hv a n hva k hk (e ▸ hspb_add j hj)
  -- the live allocations of the callee's entry: the caller's, and its slots in its slot region
  have hcsv : ∀ a n, cs.mem.valid a n = true → a + n ≤ 2 ^ 64 ∧ ∀ k < n,
      ¬ Fh (BitVec.ofNat 64 (a + k)) ∧ ¬ OutAt ib spb (BitVec.ofNat 64 (a + k)) := by
    intro a n hv
    simp only [Clif.Mem.valid, List.any_eq_true] at hv
    obtain ⟨x, hx, hcx⟩ := hv
    rcases hal' x hx with hx' | ⟨p, hp, rfl⟩
    · have hv' : cm.valid a n = true := List.any_eq_true.mpr ⟨x, hx', hcx⟩
      obtain ⟨h1, h2⟩ := hmr.valid a n hv'
      exact ⟨h1, fun k hk => ⟨fun hf => h2 k hk hf.1, fun ho => h2 k hk (hout_F _ ho).1⟩⟩
    · obtain ⟨off, hoff, hle⟩ := hfits p hp
      simp only [Clif.Alloc.contains, Bool.and_eq_true, decide_eq_true_eq, hoff,
        Option.getD_some] at hcx
      refine ⟨by omega, fun k hk => ?_⟩
      have e : (BitVec.ofNat 64 (a + k)).toNat = a + k := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
      refine ⟨fun hf => hf.2.2 ⟨by rw [e]; omega, by rw [e]; omega⟩,
        fun ⟨o1, o2⟩ => by rw [e] at o1 o2; omega⟩
  -- the callee's entry memory is related to a body-entry world agreeing with the caller's
  have hRel : ∀ u, spv u = spb → Arm.r .ERR u = .None →
      (∀ a b, cm.valid a 1 = true → cm.bytes a = some b → Arm.read_mem (BitVec.ofNat 64 a) u = b) →
      RelW ⟨Fh, L.syms, (L.A h).af.slotBase, ib⟩ h (spv w₀) cs.frame.slots cs.mem u := by
    intro u hu herru hbu
    refine ⟨⟨⟨fun a b hv hb => ?_, fun a n hv => ⟨(hcsv a n hv).1,
      fun k hk => ((hcsv a n hv).2 k hk).1⟩, hsym'.trans hmr.symbols⟩, fun id b hl => ?_,
      hOut u hu (fun a n hv k hk => ((hcsv a n hv).2 k hk).2)⟩, by rw [hu, hspw₀], herru⟩
    · obtain ⟨hb', hnot⟩ := hby' a b hb
      refine hbu a b ?_ hb'
      simp only [Clif.Mem.valid, List.any_eq_true] at hv ⊢
      obtain ⟨x, hx, hcx⟩ := hv
      rcases hal' x hx with hx' | ⟨p, hp, rfl⟩
      · exact ⟨x, hx', hcx⟩
      · simp only [Clif.Alloc.contains, Bool.and_eq_true, decide_eq_true_eq] at hcx
        exact absurd ⟨hcx.1, by omega⟩ (hnot p hp)
    · rw [hsl'] at hl
      obtain ⟨p, hp, rfl, rfl⟩ := lookup_map_some hl
      obtain ⟨off, hoff, -⟩ := hfits p hp
      refine ⟨off, hoff, ?_⟩
      simp only [Rel.slotReg, hoff, Option.getD_some, hu]
      omega
  have hWE : L.WorldEntry κ (M - 1) h Fh vals cs w₀ := by
    refine ⟨hce, ?_, ?_, ?_, ?_, ?_, fun a ha => ⟨himgF a ha, fun ho => (hout_F a ho).2 ha,
      fun hs => (hslot_F a hs).2 ha⟩, fun hN => by rw [hspw₀]; exact hpl' (hpl hN)⟩
    · refine hRel w₀ hspw₀ ?_ fun a b hv hb => ?_
      · simp only [w₀]
        rw [r_bodyOf _ _ (by simp) (by simp), r_enterAt _ _ (by simp) (by simp),
          hcOk.world.1 _ (by simp [Masked])]
        exact herr
      · rw [← hmr.bytes a b hv hb]
        simp only [Arm.read_mem, Arm.read_store, w₀, mem_bodyOf, mem_enterAt]
        rw [L.mem_canon, mem_withImg, if_neg]
        intro hi
        exact (hmr.valid a 1 hv).2 0 (by omega) (by simpa using himgF _ hi)
    · intro loc v hmem
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hmem
      cases loc with
      | stack off =>
        simp only
        have hx29 : Arm.r (.GPR 29#5) w₀ = spv w - 16#64 := by
          have := x29_bodyOf (L.A h).af (enterAt (L.A h) cn)
          rw [if_pos hfr, spv_enterAt, hsp0] at this
          exact this
        rw [hx29, fp_off_eq]
        refine ⟨fun k hk hf => hsav off v hmem k hk hf.1, ?_⟩
        rw [show Arm.read_mem_bytes v.ty.bytes (spv w + BitVec.ofNat 64 off) w₀ =
            Arm.read_mem_bytes v.ty.bytes (spv w + BitVec.ofNat 64 off) w from
          read_mem_bytes_congr _ _ (fun k hk => by
            simp only [w₀, mem_bodyOf, mem_enterAt]
            rw [L.mem_canon, mem_withImg, if_neg (fun hi => hsav off v hmem k hk (himgF _ hi))])]
        exact hargs.2.2 off v hmem
      | reg r =>
        obtain ⟨i, hr, hv⟩ := reg_zip _ _ hi
        have hlen := hargs.2.1.1
        obtain ⟨u, hu⟩ : ∃ u, uses[i]? = some u := by
          have hi' : i < uses.length := by
            rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hv).1
          exact ⟨uses[i]'hi', List.getElem?_eq_getElem _⟩
        have hvh := hargs.2.1.2 i v u hv hu
        have hrA : r.isArgReg = true := harg r (List.mem_of_getElem? hr)
        simp only
        rw [show regVal w₀ r = regVal (placeArgs (regLocs h.sig) uses (L.withImg w)) r by
          simp only [w₀]; rw [regVal_bodyOf _ _ hrA, regVal_enterAt _ _ hrA, L.regVal_canon _ _ _ hrA],
          placeArgs_regVal _ _ _ hnd harg hr hu]
        refine vHolds_setVal ?_ hvh
        have hty := hce.sig
        have hvmem : v ∈ vals := List.of_mem_zip hmem |>.2
        obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hvmem
        have e := congrArg (·[j]?) hty
        simp only [List.getElem?_map, hj, Option.map_some] at e
        cases hp : h.sig.params[j]? with
        | none => rw [hp] at e; cases e
        | some p =>
          rw [hp] at e
          simp only [Option.map_some, Option.some.injEq] at e
          rw [e]; exact hwid p (List.mem_of_getElem? hp)
    · rw [hspw₀, hB]; omega
    · intro a ha
      rw [hspw₀] at ha
      obtain ⟨h1, h2⟩ := ha
      rw [hB] at h1 h2
      have hd := hdead a ⟨by omega, by omega⟩
      exact ⟨⟨hd.1, fun ⟨o1, o2⟩ => by rw [hspb] at o1; omega,
        fun ⟨o1, o2⟩ => by rw [hspb] at o1; omega⟩, hd.2⟩
    · rw [hspw₀, hB, hdrop]; omega
  obtain ⟨us, outs, wf, hus, hlen, hhold, hmemR, hrs, hall, hni⟩ :=
    ih h hh Fh vals cs w₀ m rvals cm' hWE hm
  -- the callee's live allocations after the call are outside the caller's `F`
  have hmemF : MemRel F L.syms cm' wf := by
    refine ⟨hmemR.bytes, fun a n hv => ?_, hmemR.symbols⟩
    by_cases hN : L.NeedSlots
    · exact hmr.valid a n (Clif.runLoop_allocs hL.free (hL.baseKeepsAllocs hN) Nr cs rvals cm'
        (runInv_entry hh hce) (Clif.initState_allocInv hinit) hrunN a n hv)
    have hsl1 := hsl0 hN
    have hsz1 : sz = (L.A h).af.frameSize - clobberBytes (L.A h).af.saves := by
      obtain ⟨g, hg, hcg⟩ := hcal
      exact hL.calleeFrame g hg h hcg hsl1
    by_cases hib0 : ib = 0
    · obtain ⟨h1, h2⟩ := hmemR.valid a n hv
      exact ⟨h1, fun k hk hf => h2 k hk ⟨hf, fun ⟨o1, o2⟩ => by omega,
        fun ⟨o1, o2⟩ => by omega⟩⟩
    · obtain ⟨-, pl, hcm⟩ := initState_noSlots hpf hsl1 hinit
      have hv0 := runLoop_valid hL.free (hL.baseNoAlloc ⟨h, hh, hib0⟩) (L.slotFree hN) Nr
        cs rvals cm' (runInv_entry hh hce)
        (fun hkk => by
          have ⟨k0, hk0, hnk⟩ := hkk
          refine ⟨(hL.indScope k0 hk0 hnk).keep, fun h' hh' hs' =>
            hL.addrSlots hN ⟨h, hh, hib0⟩ hkk h' hh' ?_⟩
          rw [hcm] at hs'; rwa [← hmr.symbols]) hrunN a n hv
      rw [hcm] at hv0
      exact hmr.valid a n hv0
  -- the callee's activation from a caller state `t`
  let G : BitVec 64 → Prop :=
    fun a => F a ∧ ¬ StackBelow (frameDrop (L.A h).af + κ (M - 1) h) (spv w) a
  have hcode : ∀ t, ∀ a, CodeAddr (enterAt (L.A h) t) a → L.Img a := fun t a ha =>
    hL.imgAddr h hh a (by simpa [CodeAddr] using ha)
  have hME : ∀ t w₀', spv t = spv w → Arm.r .ERR t = .None →
      (∀ a, L.Img a → t.mem a = L.imgMem a) →
      BodyEntryW Fh (L.A h).vcp.EntryArg (L.A h).af (enterAt (L.A h) t) w₀' →
      L.MachEntry κ (M - 1) h Fh G (Arm.r .PC t + 4) (enterAt (L.A h) t) w₀' := by
    intro t w₀' hst herrt himgt hbw
    have hspt : spv (enterAt (L.A h) t) = spv w := by rw [spv_enterAt]; exact hst
    have hFrame : frameWG (κ (M - 1) h) ib (RAFrame.compute (L.A h).vcp (L.A h).rf).size
        (L.A h).af G (enterAt (L.A h) t) = Fh := by
      funext a
      apply propext
      rw [frameWG_out hfr (by rw [hspt, ← hdrop]; exact hroom) hib_le (size_le_frameBody hc.alloc), ← hdrop, hspt]
      constructor
      · rintro (⟨hb, hno, hns⟩ | hc | hg)
        · exact ⟨(hdead a hb).1, hno, hns⟩
        · exact ⟨himgF a (hcode t a hc), fun ho => (hout_F a ho).2 (hcode t a hc),
            fun hs => (hslot_F a hs).2 (hcode t a hc)⟩
        · exact ⟨hg.1, fun ho => hg.2 (hout_reg a ho), fun hs => hg.2 (hslot_reg a hs)⟩
      · intro ⟨hF, hno, hns⟩
        by_cases hb : StackBelow (frameDrop (L.A h).af + κ (M - 1) h) (spv w) a
        · exact .inl ⟨hb, hno, hns⟩
        · exact .inr (.inr ⟨hF, hb⟩)
    refine ⟨⟨by simp, fun k wd hk => hL.imgCode h hh _ (fun a ha => by
        rw [mem_enterAt]; exact himgt a ha) k wd hk, by simp, ?_, x30_enterAt _ _, ?_,
        hL.fits h hh⟩, ?_, fun a ha => ?_, hFrame,
      fun a ha => ⟨himgF a ha, fun hb => (hdead a hb).2 ha⟩,
      fun a ha => by rw [mem_enterAt]; exact himgt a ha, hbw⟩
    · rw [r_enterAt _ _ (by simp) (by simp)]; exact herrt
    · rw [hspt]; exact hal
    · refine stackRoom_of (by rw [hspt, ← hdrop]; exact hroom) fun a ha hb => ?_
      rw [hspt, ← hdrop] at hb
      exact (hdead a hb).2 (hcode t a ha)
    · rw [hspt]; exact ha.2
  have hpcall : ∀ t k, RaOk (L.A h) (Arm.r .PC t) →
      PostTrace (L.A h).fa (L.A h).af (L.A h).base (L.mach (M - 1) h) (enterAt (L.A h) t) k →
      ArmRet (Arm.r .PC t + 4) (enterAt (L.A h) t)
        (runX (L.mach (M - 1) h) k (enterAt (L.A h) t)) →
      (runX (L.mach (M - 1) h) k (enterAt (L.A h) t)).program = (enterAt (L.A h) t).program →
      L.pcall M h t =
        Arm.set_program (runX (L.mach (M - 1) h) k (enterAt (L.A h) t)) t.program := by
    intro t k hra htrk hret hprog
    obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
    obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hc.layout
    show linkedCall _ _ _ = _
    exact linkedCall_eq hc.layout hlm hra (by rw [hdrop]; omega) (by omega) htrk
      ⟨hret.pc, hret.err, hprog.trans (program_enterAt _ _), hret.sp.trans (spv_enterAt _ _)⟩
  have hx29 : Arm.r (.GPR 29#5) w₀ = spv w - 16#64 := by
    have := x29_bodyOf (L.A h).af (enterAt (L.A h) cn)
    rw [if_pos hfr, spv_enterAt, hsp0] at this
    exact this
  -- non-interference: a caller state `t` agreeing with `w` outside `Z ⊇ F`, entered with its
  -- own body-entry world
  have key2 : L.NeedNI → ∀ (Z : BitVec 64 → Prop) (t : Arm.ArmState), (∀ a, F a → Z a) →
      SameWorld Z t w → (∀ a, L.Img a → t.mem a = L.imgMem a) →
      (∀ r ∈ regLocs h.sig, regVal t r = regVal (L.canon h uses w) r) →
      RaOk (L.A h) (Arm.r .PC t) →
      MemRel F L.syms cm t →
      (∀ off v, (ArgLoc.stack off, v) ∈ (locsOf h.sig).zip vals → ∀ k < v.ty.bytes,
        t.mem (spv w + BitVec.ofNat 64 off + BitVec.ofNat 64 k) =
          w.mem (spv w + BitVec.ofNat 64 off + BitVec.ofNat 64 k)) → ∃ k,
      L.pcall M h t =
        Arm.set_program (runX (L.mach (M - 1) h) k (enterAt (L.A h) t)) t.program ∧
      ActRet (Arm.r .PC t + 4) Z G us outs wf (enterAt (L.A h) t)
        (runX (L.mach (M - 1) h) k (enterAt (L.A h) t)) := by
    intro hN Z t hFZ hZ himgt hregt hrat hmt hstkt
    have hst : spv t = spv w := hZ.1 _ (by simp [Masked])
    have herrt : Arm.r .ERR t = .None := by rw [hZ.1 _ (by simp [Masked])]; exact herr
    let w₀' := bodyOf (L.A h).af (enterAt (L.A h) t)
    let D : BitVec 64 → Prop := fun a => Z a ∧ ¬ Fh a
    have hspw₀' : spv w₀' = spb := by
      simp only [w₀']; rw [spv_bodyOf, spv_enterAt, hst]
    have hbw : BodyEntryW Fh (L.A h).vcp.EntryArg (L.A h).af (enterAt (L.A h) t) w₀' :=
      ⟨spv_bodyOf _ _, x29_bodyOf _ _, fun r hr => regVal_bodyOf _ _
        (harg r (hL.entryRegs h hh r hr)), fun f hf h29 h31 => r_bodyOf _ _ h29 h31,
        fun a _ => by simp [w₀'], by simp [w₀']⟩
    have hrel' : RelW ⟨Fh, L.syms, (L.A h).af.slotBase, ib⟩ h (spv w₀) cs.frame.slots cs.mem w₀' := by
      refine hRel w₀' hspw₀' ?_ fun a b hv hb => ?_
      · simp only [w₀']
        rw [r_bodyOf _ _ (by simp) (by simp), r_enterAt _ _ (by simp) (by simp)]
        exact herrt
      · have := hmt.bytes a b hv hb
        simp only [Arm.read_mem, Arm.read_store, w₀', mem_bodyOf, mem_enterAt] at this ⊢
        exact this
    have hsw : SameWorld (fun a => Fh a ∨ D a) w₀ w₀' := by
      refine ⟨fun f hf => ?_, fun a ha => ?_, by simp [w₀, w₀']⟩
      · by_cases h29 : f = .GPR 29#5
        · subst h29
          have e1 := x29_bodyOf (L.A h).af (enterAt (L.A h) cn)
          have e2 := x29_bodyOf (L.A h).af (enterAt (L.A h) t)
          simp only [xreg] at e1 e2
          rw [e1, e2, spv_enterAt, spv_enterAt, hsp0, hst, if_pos hfr, if_pos hfr]
        by_cases h31 : f = .GPR 31#5
        · subst h31
          show spv w₀ = spv w₀'
          rw [hspw₀, hspw₀']
        have hpc : f ≠ .PC := by rintro rfl; exact hf trivial
        have h30 : f ≠ .GPR 30#5 := by rintro rfl; exact hf (by simp [Masked])
        rw [r_bodyOf _ _ h29 h31, r_bodyOf _ _ h29 h31, r_enterAt _ _ hpc h30, r_enterAt _ _ hpc h30,
          hcOk.world.1 f hf, hZ.1 f hf]
      · have hnZ : ¬ Z a := fun hz => by
          by_cases hf : Fh a
          · exact ha (.inl hf)
          · exact ha (.inr ⟨hz, hf⟩)
        simp only [w₀, w₀', mem_bodyOf, mem_enterAt]
        rw [hcOk.world.2.1 a (fun hf => hnZ (hFZ a hf)), hZ.2.1 a hnZ]
    have hreg : ∀ r v, (ArgLoc.reg r, v) ∈ (locsOf h.sig).zip vals →
        regVal w₀' r = regVal w₀ r := by
      intro r v hm
      have hrl : r ∈ regLocs h.sig :=
        List.mem_filterMap.mpr ⟨.reg r, (List.of_mem_zip hm).1, rfl⟩
      have hrA := harg r hrl
      simp only [w₀, w₀']
      rw [regVal_bodyOf _ _ hrA, regVal_bodyOf _ _ hrA, regVal_enterAt _ _ hrA,
        regVal_enterAt _ _ hrA, hregt r hrl]
    have hstk : ∀ off v, (ArgLoc.stack off, v) ∈ (locsOf h.sig).zip vals → ∀ k < v.ty.bytes,
        w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
          w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) := by
      intro off v hm k hk
      rw [hx29, fp_off_eq]
      have hnF := hsav off v hm k hk
      simp only [w₀, w₀', mem_bodyOf, mem_enterAt]
      rw [hstkt off v hm k hk, hcOk.world.2.1 _ hnF]
    obtain ⟨k, hret, htrk⟩ := hni hN D w₀' hrel' hsw hreg hstk G (Arm.r .PC t + 4)
      (enterAt (L.A h) t) (hME t w₀' hst herrt himgt hbw)
    refine ⟨k, hpcall t k hrat htrk hret.ret hret.prog, ⟨hret.ret, hret.regs, fun a ha => hret.mem a
      (fun h' => ha (h'.elim (fun h1 => hFZ a h1.1) (fun h2 => h2.1))), hret.fields, hret.gkeep,
      hret.prog⟩⟩
  refine ⟨us, outs, wf, hus, hlen, hhold, hmemF, hrs, fun t ht => ?_, key2⟩
  by_cases hN : L.NeedNI
  · refine key2 hN F t (fun _ h => h) ht.world ht.img ht.regs ht.ra ⟨fun a b hv hb => ?_,
      hmr.valid, hmr.symbols⟩ fun off v hm k hk => ht.world.2.1 _ (hsav off v hm k hk)
    rw [← hmr.bytes a b hv hb]
    simp only [Arm.read_mem, Arm.read_store]
    exact ht.world.2.1 _ (by simpa using (hmr.valid a 1 hv).2 0 (by omega))
  · -- no outgoing area: the canonical body-entry world is the actual activation's
    obtain ⟨hib0, hsz0⟩ := hib.resolve_right hN
    have hFh : Fh = F := funext fun a => propext ⟨fun h => h.1, fun h => ⟨h, fun ⟨o1, o2⟩ => by
      omega, fun ⟨o1, o2⟩ => by omega⟩⟩
    have hbw : BodyEntryW Fh (L.A h).vcp.EntryArg (L.A h).af (enterAt (L.A h) t) w₀ := by
      rw [hFh]; exact L.bodyEntryW_compat_return_pins hL hh himgF ht
    have hst : spv t = spv w := ht.world.1 _ (by simp [Masked])
    have herrt : Arm.r .ERR t = .None := by rw [ht.world.1 _ (by simp [Masked])]; exact herr
    obtain ⟨k, hret, htrk⟩ := hall G (Arm.r .PC t + 4) (enterAt (L.A h) t)
      (hME t w₀ hst herrt ht.img hbw)
    exact ⟨k, hpcall t k ht.ra htrk hret.ret hret.prog, ⟨hret.ret, hret.regs, fun a ha => hret.mem a
      (fun h' => ha h'.1), hret.fields, hret.gkeep, hret.prog⟩⟩
end LinkSys

namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat} {modes : Clif.Function → ReturnPinMode}


end LinkSys
end E2E
