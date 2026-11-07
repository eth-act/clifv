import FV.E2E.LinkArmUAct
import FV.E2E.LinkArmUEnvCall

/-!
# A call of a program function on the linked machine with unwinding (S10f, #233)

`LinkSys.progCall` (`FV/E2E/LinkArm.lean`) for the linked machine with unwinding, without
non-interference (`¬ NeedNI`: no program callee has an outgoing-argument area or a slot region, so
the canonical body-entry world is every compatible caller's): from the linking statement with
unwinding one level down (`ThmU`), a call of a function `h` of `P` whose callee run with unwinding
returns is one VCode outcome the linked machine's call realises from every compatible caller state
(`pcallU`, the callee not leaving its frame by unwinding: `praiseU = none`, by `returnedCall_eq`);
one whose callee run ends `unwound` is an exception object and world the linked machine's raise
realises from every compatible caller state (`praiseU`, by `raisedCall_eq`).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

namespace LinkSysU

variable (L : LinkSysU)
variable {κ : Nat → Clif.Function → Nat}

/-- Without non-interference a callee has no outgoing-argument area and no slot region. -/
theorem noNI_frame {hN : ¬ L.NeedNI} {g h : Clif.Function} (hg : g ∈ L.P.funcs)
    (hc : L.Callee g h) :
    (RAFrame.compute (L.A h).vcp (L.A h).rf).intBase = 0 ∧
      (RAFrame.compute (L.A h).vcp (L.A h).rf).size = (L.A h).af.frameSize - clobberBytes (L.A h).af.saves := by
  by_cases h0 : (RAFrame.compute (L.A h).vcp (L.A h).rf).intBase = 0
  · by_cases h1 : (RAFrame.compute (L.A h).vcp (L.A h).rf).size = (L.A h).af.frameSize - clobberBytes (L.A h).af.saves
    · exact ⟨h0, h1⟩
    · exact absurd ⟨g, hg, h, hc, .inr h1⟩ hN
  · exact absurd ⟨g, hg, h, hc, .inl h0⟩ hN

/-- The memory after a callee run (returning or unwinding) from the caller's memory `cm`: valid
only where `cm` is, when the base externs create no allocation (`OkU.baseKeepsAllocsU`). -/
theorem crunX_allocs (hL : L.Ok) (hU : L.OkU) [hR : L.CrunOkX] (hA : L.NeedSlots ∨
    ∃ g ∈ L.P.funcs, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase ≠ 0) {M : Nat}
    {n : String} {vals : List Clif.Val}
    {cm : Clif.Mem} {cs : Clif.State} (hinit : Clif.initState L.P n vals cm = .ok cs)
    {o : Clif.XOutcome} (ho : L.crunX M cs = o) {cm' : Clif.Mem}
    (hc : (∃ v, o = .returned v cm') ∨ ∃ e, o = .unwound e cm') :
    ∀ a k, cm'.valid a k = true → cm.valid a k = true := by
  obtain ⟨N, hN'⟩ := hR.runs M cs o ho (by
    rcases hc with ⟨v, rfl⟩ | ⟨e, rfl⟩
    · exact .inl ⟨v, cm', rfl⟩
    · exact .inr (.inr ⟨e, cm', rfl⟩))
  have := Clif.runLoopX_allocs hL.free (L.envX_keepsAllocs hU hA) N cs.toX
    (Clif.initState_xinv hinit) (Clif.initState_allocInv hinit)
  rcases hc with ⟨v, rfl⟩ | ⟨e, rfl⟩
  · exact this.1 v cm' hN'
  · exact this.2 e cm' hN'

/-- **A call of a function `h` of `P` at depth `M + 1` on the linked machine with unwinding**
(without non-interference): from a world `w` with room for the callee's stack and related to CLIF
arguments and memory, when the callee run with unwinding (`crunX (M + 1)`) returns, one VCode
outcome of `h` that the linked machine's call returns with (not raising) from every caller state
compatible with `w` (`CallerOk`); when it ends `unwound`, an exception object related to the CLIF
exception and a world related to the CLIF memory that the linked machine's call raises with from
every compatible caller state, leaving the callee's frame as the ABI return (`ActUnw`). -/
theorem progCallU (hL : L.Ok) (hU : L.OkU) [hR : L.CrunOkX] (hN : ¬ L.NeedNI) {M : Nat}
    (ih : L.ThmU κ M) {n : String} {h : Clif.Function} (hpf : L.P.func? n = some h)
    (hcal : ∃ g ∈ L.P.funcs, L.Callee g h)
    {F : BitVec 64 → Prop} (himgF : ∀ a, L.Img a → F a)
    {uses : List CV} {w : Arm.ArmState} (herr : Arm.r .ERR w = .None)
    (hal : (spv w).toNat % 16 = 0)
    (hroom : frameDrop (L.A h).af + κ M h ≤ (spv w).toNat)
    (hdead : ∀ a, StackBelow (frameDrop (L.A h).af + κ M h) (spv w) a → F a ∧ ¬ L.Img a)
    {vals : List Clif.Val} {cm : Clif.Mem} {cs : Clif.State}
    (hmr : MemRel F L.syms cm w) (hargs : ArgsAt h.sig vals uses w)
    (hsav : StackArgsAvoid F h.sig vals w) (hpl : L.NeedSlots → L.PlaceAt cm (spv w))
    (hinit : Clif.initState L.P n vals cm = .ok cs) :
    (∀ rvals cm', L.crunX (M + 1) cs = .returned rvals cm' →
      ∃ (us : List (Reg × Reg)) (outs : List CV) (wf : Arm.ArmState),
        RetPins rvals us ∧ us.length = outs.length ∧
        PrefixHold rvals outs ∧ MemRel F L.syms cm' wf ∧ (L.A h).vc.RetsSite us ∧
        ∀ t, L.CallerOk F h uses w t → ∃ k,
          L.pcallU (M + 1) h t =
            Arm.set_program (runX (L.machU M h) k (enterAt (L.A h) t)) t.program ∧
          L.praiseU (M + 1) h t = none ∧
          ActRet (Arm.r .PC t + 4) F
            (fun a => F a ∧ ¬ StackBelow (frameDrop (L.A h).af + κ M h) (spv w) a)
            us outs wf (enterAt (L.A h) t) (runX (L.machU M h) k (enterAt (L.A h) t))) ∧
    (∀ e cm', L.crunX (M + 1) cs = .unwound e cm' →
      ∃ (obj : BitVec 64) (wf : Arm.ArmState), ExnRel e obj ∧ MemRel F L.syms cm' wf ∧
        ∀ t, L.CallerOk F h uses w t → ∃ k,
          L.praiseU (M + 1) h t =
            some (xreg 0 (runX (L.machU M h) k (enterAt (L.A h) t)),
              Arm.set_program (runX (L.machU M h) k (enterAt (L.A h) t)) t.program) ∧
          ActUnw (Arm.r .PC t + 4) F
            (fun a => F a ∧ ¬ StackBelow (frameDrop (L.A h).af + κ M h) (spv w) a)
            obj wf (enterAt (L.A h) t) (runX (L.machU M h) k (enterAt (L.A h) t))) := by
  obtain ⟨hh, hname⟩ := Clif.Program.func?_some hpf
  subst hname
  obtain ⟨hib0, hsz0⟩ := L.noNI_frame (hN := hN) hcal.choose_spec.1 hcal.choose_spec.2
  have hc := hL.compiled h hh
  have hfr := lowerRFunc_frame hc.alloc
  have hdrop := L.frameDrop_eq hL hh
  have hfs := L.frameSize_mod hL hh
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
  have hlink : ∀ o, L.crunX (M + 1) cs = o → ((∃ v m, o = .returned v m) ∨ ∃ e m, o = .unwound e m) →
      ∃ m, Clif.runLoopX (L.envRX M h) L.P.bare m cs.toX = o := by
    intro o ho hc'
    have := L.envRX_crun hL.names M hh (runInv_entry hh hce)
      (runInv_entry (by simp [Clif.Program.only]) hce) (fun _ => hsym'.trans hmr.symbols)
      (by rw [ho]; rcases hc' with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> intro _ e <;> cases e)
      (by rw [ho]; rcases hc' with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> intro e <;> cases e)
    rw [ho] at this
    exact this
  -- the canonical state and the shared body-entry world
  let cn := L.canon h uses w
  let w₀ := bodyOf (L.A h).af (enterAt (L.A h) cn)
  have hcOk := L.callerOk_canon hL hh himgF uses w
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
      StackBelow (frameDrop (L.A h).af + κ M h) (spv w) a := by
    intro a ⟨h1, h2⟩
    rw [hspb] at h1 h2
    exact ⟨by omega, by omega⟩
  have hout_F : ∀ a, OutAt ib spb a → F a ∧ ¬ L.Img a := fun a ha => hdead a (hout_reg a ha)
  have hslot_reg : ∀ a, SlotAt sz ((L.A h).af.frameSize - clobberBytes (L.A h).af.saves) spb a →
      StackBelow (frameDrop (L.A h).af + κ M h) (spv w) a := by
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
      obtain ⟨p, hp, rfl, rfl⟩ := LinkSys.lookup_map_some hl
      obtain ⟨off, hoff, -⟩ := hfits p hp
      refine ⟨off, hoff, ?_⟩
      simp only [Rel.slotReg, hoff, Option.getD_some, hu]
      omega
  have hWE : L.WorldEntry κ M h Fh vals cs w₀ := by
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
  -- without non-interference the callee's `F` is the caller's
  have hFh : Fh = F := funext fun a => propext ⟨fun h => h.1, fun h => ⟨h, fun ⟨o1, o2⟩ => by
    simp only [ib] at o1 o2; omega, fun ⟨o1, o2⟩ => by simp only [sz] at o1 o2; omega⟩⟩
  -- the callee's live allocations after the call are outside the caller's `F`
  have hmemF : ∀ cm' (wf : Arm.ArmState) o, L.crunX (M + 1) cs = o →
      ((∃ v, o = .returned v cm') ∨ ∃ e, o = .unwound e cm') → MemRel Fh L.syms cm' wf →
      MemRel F L.syms cm' wf := by
    intro cm' wf o ho hc' hmemR
    refine ⟨hmemR.bytes, fun a n hv => ?_, hmemR.symbols⟩
    by_cases hNS : L.NeedSlots
    · exact hmr.valid a n (L.crunX_allocs hL hU (.inl hNS) hinit ho hc' a n hv)
    · obtain ⟨h1, h2⟩ := hmemR.valid a n hv
      exact ⟨h1, fun k hk hf => h2 k hk (by rw [hFh]; exact hf)⟩
  -- the callee's activation from a caller state `t`
  let G : BitVec 64 → Prop :=
    fun a => F a ∧ ¬ StackBelow (frameDrop (L.A h).af + κ M h) (spv w) a
  have hcode : ∀ t, ∀ a, CodeAddr (enterAt (L.A h) t) a → L.Img a := fun t a ha =>
    hL.imgAddr h hh a (by simpa [CodeAddr] using ha)
  have hME : ∀ t w₀', spv t = spv w → Arm.r .ERR t = .None →
      (∀ a, L.Img a → t.mem a = L.imgMem a) →
      BodyEntryW Fh (L.A h).vcp.EntryArg (L.A h).af (enterAt (L.A h) t) w₀' →
      L.MachEntry κ M h Fh G (Arm.r .PC t + 4) (enterAt (L.A h) t) w₀' := by
    intro t w₀' hst herrt himgt hbw
    have hspt : spv (enterAt (L.A h) t) = spv w := by rw [spv_enterAt]; exact hst
    have hFrame : frameWG (κ M h) ib (RAFrame.compute (L.A h).vcp (L.A h).rf).size
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
        by_cases hb : StackBelow (frameDrop (L.A h).af + κ M h) (spv w) a
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
  obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hc.layout
  have hfd : 0 < frameDrop (L.A h).af := by rw [hdrop]; omega
  have hfd' : frameDrop (L.A h).af < 2 ^ 64 := by omega
  -- a compatible caller state's activation
  have hact : ∀ t, L.CallerOk F h uses w t →
      L.MachEntry κ M h Fh G (Arm.r .PC t + 4) (enterAt (L.A h) t) w₀ := by
    intro t ht
    have hbw : BodyEntryW Fh (L.A h).vcp.EntryArg (L.A h).af (enterAt (L.A h) t) w₀ := by
      rw [hFh]; exact L.bodyEntryW_compat hL hh himgF ht
    have hst : spv t = spv w := ht.world.1 _ (by simp [Masked])
    have herrt : Arm.r .ERR t = .None := by rw [ht.world.1 _ (by simp [Masked])]; exact herr
    exact hME t w₀ hst herrt ht.img hbw
  refine ⟨fun rvals cm' hrun => ?_, fun e cm' hrun => ?_⟩
  · obtain ⟨m, hm⟩ := hlink _ hrun (.inl ⟨_, _, rfl⟩)
    obtain ⟨us, outs, wf, hus, hlen, hhold, hmemR, hrs, hall, -⟩ :=
      (ih h hh Fh vals cs w₀ m hWE).1 rvals cm' hm
    refine ⟨us, outs, wf, hus, hlen, hhold, hmemF cm' wf _ hrun (.inl ⟨_, rfl⟩) hmemR, hrs,
      fun t ht => ?_⟩
    obtain ⟨k, hret, htrk, hnu⟩ := hall G (Arm.r .PC t + 4) (enterAt (L.A h) t) (hact t ht)
    obtain ⟨-, e1, e2⟩ := returnedCall_eq hc.layout hlm ht.ra hfd hfd' htrk
      ⟨hret.ret.pc, hret.ret.err, hret.prog.trans (program_enterAt _ _),
        hret.ret.sp.trans (spv_enterAt _ _)⟩ hnu
    refine ⟨k, e1, e2, ?_⟩
    rw [hFh] at hret
    exact hret
  · obtain ⟨m, hm⟩ := hlink _ hrun (.inr ⟨_, _, rfl⟩)
    obtain ⟨obj, wf, hex, hmemR, hall, -⟩ := (ih h hh Fh vals cs w₀ m hWE).2.2 e cm' hm
    refine ⟨obj, wf, hex, hmemF cm' wf _ hrun (.inr ⟨_, rfl⟩) hmemR, fun t ht => ?_⟩
    obtain ⟨k, hu, htrk, hk0, hx⟩ := hall G (Arm.r .PC t + 4) (enterAt (L.A h) t) (hact t ht)
    obtain ⟨-, e1⟩ := raisedCall_eq hc.layout hlm ht.ra hfd hfd' htrk
      ⟨hu.ret.pc, hu.ret.err, hu.prog.trans (program_enterAt _ _),
        hu.ret.sp.trans (spv_enterAt _ _)⟩ hk0 hx
    refine ⟨k, e1, ?_⟩
    rw [hFh] at hu
    exact hu

end LinkSysU

end E2E
