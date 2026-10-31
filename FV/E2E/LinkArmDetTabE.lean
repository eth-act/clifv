import FV.E2E.LinkArmLockRetOf

/-!
# The prefix-closed table of the canonical callee from the actual one (SEM1 #537, #713, #716)

`DetTabPRBE κ M` (`LinkArmThmPRBRLE.lean`): at a program call, a caller state `t` compatible with
the canonical one whose callee run has the prefix-closed table `TableOfE` gives the canonical
callee run the same table. `CallLock` (the lock to the return at a call) runs the canonical callee
first and needs its table; here the roles are reversed (#713): the actual callee entry `t` is the
first activation (its `WorldEntryB` with its own body-entry world `bodyOf (enterAt t)`, its
prophecies, its table and returning run, `ThmPRBRLE` one level down), the canonical one the second.
`LockRet` one level down then gives the twin runs `TwinCE` (canonical, actual), and the table
carries over (`tableOfE_twinCE`).

* `argsAtEntry_transfer` (the entry arguments of a body-entry world equal on the parameter
  registers and the stack-passed argument bytes);
* **`detTabPRBE_of`**: `DetTabPRBE κ M` from `ThmPRBRLE κ (M - 1)` and `LockRet κ (M - 1)`;
  `detTabPRBE_zero` (no callee run returns at depth `0`).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- **The entry arguments carry over** between body-entry worlds equal on the frame pointer, the
parameter registers and the stack-passed argument bytes. -/
theorem argsAtEntry_transfer {F : BitVec 64 → Prop} {sig : Clif.Signature} {args : List Clif.Val}
    {w w' : Arm.ArmState} (h : ArgsAtEntry F sig args w)
    (hx29 : Arm.r (.GPR 29#5) w' = Arm.r (.GPR 29#5) w)
    (hreg : ∀ r v, (ArgLoc.reg r, v) ∈ (locsOf sig).zip args → regVal w' r = regVal w r)
    (hstk : ∀ off v, (ArgLoc.stack off, v) ∈ (locsOf sig).zip args → ∀ k < v.ty.bytes,
      w'.mem (Arm.r (.GPR 29#5) w + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
        w.mem (Arm.r (.GPR 29#5) w + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k)) :
    ArgsAtEntry F sig args w' := by
  intro loc v hm
  cases loc with
  | reg r =>
    simp only
    rw [hreg r v hm]
    exact h _ _ hm
  | stack off =>
    simp only
    rw [hx29]
    obtain ⟨h1, h2⟩ := h _ _ hm
    refine ⟨h1, ?_⟩
    rw [← h2, read_mem_bytes_congr _ _ (fun k hk => hstk off v hm k hk)]

namespace LinkSys

variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

/-- **`DetTabPRBE` at depth `0`**: no callee run returns. -/
theorem detTabPRBE_zero [hR : L.CrunOk] : L.DetTabPRBE κ 0 :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ cs rvals cm' _ _ _ _ _ _ _ hrun =>
    absurd hrun (hR.zero cs rvals cm')

set_option maxHeartbeats 4000000 in
/-- **The canonical callee's prefix-closed table from the actual one** (module doc). The budget
`hκ` is new (#581): the callee's entry `StackAvail` holds its stack probes (`Budget`'s second
conjunct); without it the callee's `MachEntry` is not available. -/
theorem detTabPRBE_of (hL : L.Ok) (hκ : L.Budget κ) [hR : L.CrunOk] {M : Nat} (hM : 0 < M)
    (ih : L.ThmPRBRLE κ (M - 1)) (hlock : L.LockRet κ (M - 1)) : L.DetTabPRBE κ M := by
  intro n h hpf hcal F himgF uses w herr hal hroom hdead vals cm cs rvals cm' ini hmr hargs hsav
    hpl hslotb hinit hrun t ht hmsk hrgn htabT
  obtain ⟨hh, hname⟩ := Clif.Program.func?_some hpf
  subst hname
  have hc := hL.compiled h hh
  have hpb : probeBelow (L.A h).af ≤ κ (M - 1) h := hκ.2 (M - 1) h hh
  have hfr := lowerRFunc_frame hc.alloc
  have hdrop := L.frameDrop_eq hL hh
  have hfs := L.frameSize_mod hL hh
  obtain ⟨hnd, harg, hwid⟩ := hL.argRegs h hh
  have hsl0 : ¬ L.NeedSlots → h.slots = [] := fun hn => Classical.byContradiction fun hne => by
    obtain ⟨g, hg, hcg⟩ := hcal
    exact hn ⟨g, hg, h, hcg, hne⟩
  -- the callee's entry (`initState_memB` with program callees with slots, else no slots)
  have hentry : cs.frame.slots = h.slots.map (fun p => (p.1,
        (spv w - BitVec.ofNat 64 (frameDrop (L.A h).af)).toNat +
          ((L.A h).af.slotBase + ((slotLayout h.slots).1.lookup p.1).getD 0))) ∧
      cs.mem.symbols = cm.symbols ∧
      (∀ x ∈ cs.mem.allocs, x ∈ cm.allocs ∨ ∃ p ∈ h.slots,
        x = ⟨(spv w - BitVec.ofNat 64 (frameDrop (L.A h).af)).toNat +
          ((L.A h).af.slotBase + ((slotLayout h.slots).1.lookup p.1).getD 0), p.2.size, false⟩) ∧
      (∀ a b, cs.mem.bytes a = some b →
        (cm.bytes a = some b ∧ ∀ p ∈ h.slots,
          ¬ ((spv w - BitVec.ofNat 64 (frameDrop (L.A h).af)).toNat +
              ((L.A h).af.slotBase + ((slotLayout h.slots).1.lookup p.1).getD 0) ≤ a ∧
            a < (spv w - BitVec.ofNat 64 (frameDrop (L.A h).af)).toNat +
              ((L.A h).af.slotBase + ((slotLayout h.slots).1.lookup p.1).getD 0) + p.2.size)) ∨
        (L.NeedSlots ∧ L.SlotByte h (spv w) a ∧ b = ini.bytes (ini.next + 1) a)) ∧
      (L.NeedSlots → L.PlaceAtB cs.mem (spv w - BitVec.ofNat 64 (frameDrop (L.A h).af))
        (calleeIni h ini)) := by
    by_cases hN : L.NeedSlots
    · obtain ⟨h1, h2, h3, h4, h5⟩ := L.initState_memB hpf hinit (hpl hN)
      refine ⟨h1, h2, h3, fun a b hb => ?_, fun _ => h5⟩
      rcases h4 a b hb with h4 | ⟨p, hp, hlo, hhi, rfl⟩
      · exact .inl h4
      · exact .inr ⟨hN, ⟨p, hp, hlo, hhi⟩, rfl⟩
    · obtain ⟨h1, h2, h3, h4, -⟩ := L.initState_mem hpf hinit (c := spv w) (.inl (hsl0 hN))
      exact ⟨h1, h2, h3, fun a b hb => .inl (h4 a b hb), fun h' => absurd h' hN⟩
  obtain ⟨hsl', hsym', hal', hby', hpl'⟩ := hentry
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
  -- the canonical state and the shared body-entry world
  let cn := L.canon h uses w
  let w₀ := bodyOf (L.A h).af (enterAt (L.A h) cn)
  have hcOk := L.callerOk_canon hL hh himgF uses w
  have hsp0 : spv cn = spv w := hcOk.world.1 _ (by simp [Masked])
  have hspw₀ : spv w₀ = spv w - BitVec.ofNat 64 (frameDrop (L.A h).af) := by
    rw [spv_bodyOf, spv_enterAt, hsp0]
  -- the callee's stack probes zero only bytes of its frame and of its budget, inside `F` (#581)
  have hnpw : ∀ u : Arm.ArmState, spv u = spv w → ∀ a, ¬ F a →
      probeHit (L.A h).af (spv (enterAt (L.A h) u)) a = false := fun u hu a ha => by
    rw [spv_enterAt, hu]; exact probeHit_of_notF hpb hroom (fun a hb => (hdead a hb).1) ha
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
  have hslot_F : ∀ a, SlotAt sz ((L.A h).af.frameSize - clobberBytes (L.A h).af.saves) spb a →
      F a ∧ ¬ L.Img a :=
    fun a ha => hdead a (hslot_reg a ha)
  -- a slot byte of the callee is in its slot region
  have hslot_at : ∀ a, L.SlotByte h (spv w) a →
      SlotAt sz ((L.A h).af.frameSize - clobberBytes (L.A h).af.saves) spb (BitVec.ofNat 64 a) := by
    intro a ⟨p, hp, hlo, hhi⟩
    obtain ⟨off, hoff, hle⟩ := hfits p hp
    simp only [hoff, Option.getD_some] at hlo hhi
    have e : (BitVec.ofNat 64 a).toNat = a := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    exact ⟨by rw [e]; omega, by rw [e]; omega⟩
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
  -- the callee's entry memory is related to a body-entry world agreeing with the caller's and
  -- holding the table's slot bytes
  have hRel : ∀ u, spv u = spb → Arm.r .ERR u = .None →
      (∀ a b, cm.valid a 1 = true → cm.bytes a = some b → Arm.read_mem (BitVec.ofNat 64 a) u = b) →
      (L.NeedSlots → ∀ a, L.SlotByte h (spv w) a →
        Arm.read_mem (BitVec.ofNat 64 a) u = ini.bytes (ini.next + 1) a) →
      RelW ⟨Fh, L.syms, (L.A h).af.slotBase, ib⟩ h (spv w₀) cs.frame.slots cs.mem u := by
    intro u hu herru hbu hsu
    refine ⟨⟨⟨fun a b hv hb => ?_, fun a n hv => ⟨(hcsv a n hv).1,
      fun k hk => ((hcsv a n hv).2 k hk).1⟩, hsym'.trans hmr.symbols⟩, fun id b hl => ?_,
      hOut u hu (fun a n hv k hk => ((hcsv a n hv).2 k hk).2)⟩, by rw [hu, hspw₀], herru⟩
    · rcases hby' a b hb with ⟨hb', hnot⟩ | ⟨hN, hsb, rfl⟩
      · refine hbu a b ?_ hb'
        simp only [Clif.Mem.valid, List.any_eq_true] at hv ⊢
        obtain ⟨x, hx, hcx⟩ := hv
        rcases hal' x hx with hx' | ⟨p, hp, rfl⟩
        · exact ⟨x, hx', hcx⟩
        · simp only [Clif.Alloc.contains, Bool.and_eq_true, decide_eq_true_eq] at hcx
          exact absurd ⟨hcx.1, by omega⟩ (hnot p hp)
      · exact hsu hN a hsb
    · rw [hsl'] at hl
      obtain ⟨p, hp, rfl, rfl⟩ := lookup_map_some hl
      obtain ⟨off, hoff, -⟩ := hfits p hp
      refine ⟨off, hoff, ?_⟩
      simp only [Rel.slotReg, hoff, Option.getD_some, hu]
      omega
  have hWE : L.WorldEntryB κ (M - 1) h Fh vals cs w₀ (calleeIni h ini) := by
    refine ⟨hce, ?_, ?_, ?_, ?_, ?_, fun a ha => ⟨himgF a ha, fun ho => (hout_F a ho).2 ha,
      fun hs => (hslot_F a hs).2 ha⟩, fun hN => by rw [hspw₀]; exact hpl' hN⟩
    · refine hRel w₀ hspw₀ ?_ (fun a b hv hb => ?_) (fun hN a hsb => ?_)
      · simp only [w₀]
        rw [r_bodyOf _ _ (by simp) (by simp), r_enterAt _ _ (by simp) (by simp),
          hcOk.world.1 _ (by simp [Masked])]
        exact herr
      · rw [← hmr.bytes a b hv hb]
        have hnF : ¬ F (BitVec.ofNat 64 a) := fun hf =>
          (hmr.valid a 1 hv).2 0 (by omega) (by simpa using hf)
        simp only [Arm.read_mem, Arm.read_store, w₀, mem_bodyOf]
        rw [probeMem_of_not (hnpw cn hsp0 _ hnF), mem_enterAt, L.mem_canon, mem_withImg, if_neg]
        intro hi
        exact hnF (himgF _ hi)
      · rw [hslotb hN a hsb]
        simp only [Arm.read_mem, Arm.read_store, w₀, mem_bodyOf]
        refine probeMem_congr (by rw [spv_enterAt, hsp0]) ?_
        rw [mem_enterAt, L.mem_canon, mem_withImg,
          if_neg (fun hi => (hslot_F _ (hslot_at a hsb)).2 hi)]
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
            simp only [w₀, mem_bodyOf]
            rw [probeMem_of_not (hnpw cn hsp0 _ (hsav off v hmem k hk)), mem_enterAt, L.mem_canon,
              mem_withImg, if_neg (fun hi => hsav off v hmem k hk (himgF _ hi))])]
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
      rw [frameWG_out hfr (by rw [hspt, ← hdrop]; exact hroom) hib_le (size_le_frameBody hc.alloc),
        ← hdrop, hspt]
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
    · refine ⟨stackRoom_of (by rw [hspt, ← hdrop]; exact hroom) fun a ha hb => ?_, hpb⟩
      rw [hspt, ← hdrop] at hb
      exact (hdead a hb).2 (hcode t a ha)
    · rw [hspt]; exact ha.2
  have hx29 : Arm.r (.GPR 29#5) w₀ = spv w - 16#64 := by
    have := x29_bodyOf (L.A h).af (enterAt (L.A h) cn)
    rw [if_pos hfr, spv_enterAt, hsp0] at this
    exact this
  -- the canonical entry (the second activation)
  have herrc : Arm.r .ERR cn = .None := by rw [hcOk.world.1 _ (by simp [Masked])]; exact herr
  have hbw0 : BodyEntryW Fh (L.A h).vcp.EntryArg (L.A h).af (enterAt (L.A h) cn) w₀ :=
    ⟨spv_bodyOf _ _, x29_bodyOf _ _, fun r hr => regVal_bodyOf _ _
      (harg r (hL.entryRegs h hh r hr)), fun f hf h29 h31 => r_bodyOf _ _ h29 h31,
      fun a _ => by simp [w₀], by simp [w₀]⟩
  -- the actual call: `t` agrees with `w` on `F`, entered with its own body-entry world
  have hFZ : ∀ a, F a → F a := fun _ h => h
  have hZ : SameWorld F t w := ht.world
  have hst : spv t = spv w := hZ.1 _ (by simp [Masked])
  have herrt : Arm.r .ERR t = .None := by rw [hZ.1 _ (by simp [Masked])]; exact herr
  let w₀' := bodyOf (L.A h).af (enterAt (L.A h) t)
  let D : BitVec 64 → Prop := fun _ => False
  have hspw₀' : spv w₀' = spb := by
    simp only [w₀']; rw [spv_bodyOf, spv_enterAt, hst]
  have hbw : BodyEntryW Fh (L.A h).vcp.EntryArg (L.A h).af (enterAt (L.A h) t) w₀' :=
    ⟨spv_bodyOf _ _, x29_bodyOf _ _, fun r hr => regVal_bodyOf _ _
      (harg r (hL.entryRegs h hh r hr)), fun f hf h29 h31 => r_bodyOf _ _ h29 h31,
      fun a _ => by simp [w₀'], by simp [w₀']⟩
  have hrel' : RelW ⟨Fh, L.syms, (L.A h).af.slotBase, ib⟩ h (spv w₀) cs.frame.slots cs.mem w₀' := by
    refine hRel w₀' hspw₀' ?_ (fun a b hv hb => ?_) (fun hN a hsb => ?_)
    · simp only [w₀']
      rw [r_bodyOf _ _ (by simp) (by simp), r_enterAt _ _ (by simp) (by simp)]
      exact herrt
    · rw [← hmr.bytes a b hv hb]
      have hnF : ¬ F (BitVec.ofNat 64 a) := fun hf =>
        (hmr.valid a 1 hv).2 0 (by omega) (by simpa using hf)
      simp only [Arm.read_mem, Arm.read_store, w₀', mem_bodyOf]
      rw [probeMem_of_not (hnpw t hst _ hnF), mem_enterAt]
      exact hZ.2.1 _ hnF
    · rw [hslotb hN a hsb]
      simp only [Arm.read_mem, Arm.read_store, w₀', mem_bodyOf]
      refine probeMem_congr (by rw [spv_enterAt, hst]) ?_
      rw [mem_enterAt, hrgn _ (hslot_reg _ (hslot_at a hsb)), L.mem_canon, mem_withImg,
        if_neg (fun hi => (hslot_F _ (hslot_at a hsb)).2 hi)]
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
    · by_cases hFa : F a
      · -- a byte of the exterior outside `Fh`: the callee's outgoing area or slot region, in the
        -- caller's dead stack, where `t` holds the canonical state's bytes
        have hFh : ¬ Fh a := fun hf => ha (.inl hf)
        have hrg : StackBelow (frameDrop (L.A h).af + κ (M - 1) h) (spv w) a := by
          by_cases ho : OutAt ib spb a
          · exact hout_reg a ho
          · by_cases hs : SlotAt sz ((L.A h).af.frameSize - clobberBytes (L.A h).af.saves) spb a
            · exact hslot_reg a hs
            · exact (hFh ⟨hFa, ho, hs⟩).elim
        simp only [w₀, w₀', mem_bodyOf]
        exact probeMem_congr (by rw [spv_enterAt, spv_enterAt, hsp0, hst])
          (by rw [mem_enterAt, mem_enterAt]; exact (hrgn a hrg).symm)
      · simp only [w₀, w₀', mem_bodyOf]
        exact probeMem_congr (by rw [spv_enterAt, spv_enterAt, hsp0, hst])
          (by rw [mem_enterAt, mem_enterAt, hcOk.world.2.1 a (fun hf => hFa (hFZ a hf)),
            hZ.2.1 a hFa])
  have hreg : ∀ r v, (ArgLoc.reg r, v) ∈ (locsOf h.sig).zip vals →
      regVal w₀' r = regVal w₀ r := by
    intro r v hm
    have hrl : r ∈ regLocs h.sig :=
      List.mem_filterMap.mpr ⟨.reg r, (List.of_mem_zip hm).1, rfl⟩
    have hrA := harg r hrl
    simp only [w₀, w₀']
    rw [regVal_bodyOf _ _ hrA, regVal_bodyOf _ _ hrA, regVal_enterAt _ _ hrA,
      regVal_enterAt _ _ hrA, ht.regs r hrl]
  have hstk : ∀ off v, (ArgLoc.stack off, v) ∈ (locsOf h.sig).zip vals → ∀ k < v.ty.bytes,
      w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
        w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) := by
    intro off v hm k hk
    rw [hx29, fp_off_eq]
    have hnF := hsav off v hm k hk
    simp only [w₀, w₀', mem_bodyOf]
    exact probeMem_congr (by rw [spv_enterAt, spv_enterAt, hst, hsp0])
      (by rw [mem_enterAt, mem_enterAt, hZ.2.1 _ hnF, hcOk.world.2.1 _ hnF])
  have hagree : EntryAgree (frameDrop (L.A h).af + κ (M - 1) h) (enterAt (L.A h) t)
      (enterAt (L.A h) cn) := by
    refine ⟨fun f hf hpc h30 => ?_, fun a ha => ?_⟩
    · rw [r_enterAt _ _ hpc h30, r_enterAt _ _ hpc h30]; exact hmsk f hf hpc h30
    · rw [spv_enterAt, hst] at ha
      rw [mem_enterAt, mem_enterAt]; exact hrgn a ha
  have hx29t : Arm.r (.GPR 29#5) (enterAt (L.A h) t) = Arm.r (.GPR 29#5) (enterAt (L.A h) cn) := by
    rw [r_enterAt _ _ (by simp) (by simp), r_enterAt _ _ (by simp) (by simp),
      hZ.1 _ (by simp [Masked]), hcOk.world.1 _ (by simp [Masked])]
  -- the actual entry first: its body-entry world, its own prophecies, its returning run
  have hspw₀w : spv w₀' = spv w₀ := by rw [hspw₀', hspw₀]
  have hx29' : Arm.r (.GPR 29#5) w₀' = spv w - 16#64 := by
    have := x29_bodyOf (L.A h).af (enterAt (L.A h) t)
    rw [if_pos hfr, spv_enterAt, hst] at this
    exact this
  have hWEt : L.WorldEntryB κ (M - 1) h Fh vals cs w₀' (calleeIni h ini) :=
    ⟨hce, by rw [hspw₀w]; exact hrel',
      argsAtEntry_transfer hWE.args (hx29'.trans hx29.symm) hreg hstk,
      by rw [hspw₀w]; exact hWE.room, fun a ha => hWE.dead a (by rw [← hspw₀w]; exact ha),
      by rw [hspw₀w]; exact hWE.align, hWE.img, fun hN => by rw [hspw₀w]; exact hWE.place hN⟩
  have hME0t : L.MachEntryPR κ (M - 1) h Fh G (Arm.r .PC t + 4) (enterAt (L.A h) t) w₀'
      (prophOf (L.mach (M - 1) h) (L.A h).fa (L.A h).base (enterAt (L.A h) t))
      (prophStOf (L.mach (M - 1) h) (L.A h).fa (L.A h).base (enterAt (L.A h) t)) :=
    ⟨⟨hME t w₀' hst herrt ht.img hbw, prophOk_prophOf _ _ _ _ _ _⟩,
      fun _ hc _ _ _ _ => by rw [prophStOf_call hc]⟩
  have hraT : RaOk (L.A h) (Arm.r .PC t + 4 - 4) := by rw [BitVec.add_sub_cancel]; exact ht.ra
  obtain ⟨us, outs, wf, n₀, -, -, -, -, -, hrs, hret0, htr0, -, -⟩ :=
    ih h hh Fh vals cs w₀' m rvals cm' (calleeIni h ini) G (Arm.r .PC t + 4) (enterAt (L.A h) t)
      hWEt hME0t hraT htabT hm
  -- the canonical entry second
  have hagreeC : EntryAgree (frameDrop (L.A h).af + κ (M - 1) h) (enterAt (L.A h) cn)
      (enterAt (L.A h) t) :=
    hagree.symm_of_sp (by rw [spv_enterAt, spv_enterAt, hst, hsp0])
  have hstkC : ∀ off v, (ArgLoc.stack off, v) ∈ (locsOf h.sig).zip vals → ∀ k < v.ty.bytes,
      w₀.mem (Arm.r (.GPR 29#5) w₀' + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
        w₀'.mem (Arm.r (.GPR 29#5) w₀' + BitVec.ofInt 64 (16 + (off : Int)) +
          BitVec.ofNat 64 k) := by
    intro off v hm k hk
    rw [hx29'.trans hx29.symm]
    exact (hstk off v hm k hk).symm
  obtain ⟨-, -, -, -, -, -, htwc⟩ := hlock h hh Fh vals cs w₀' (calleeIni h ini) G
    (Arm.r .PC t + 4) (enterAt (L.A h) t) us outs wf n₀ m rvals cm' hWEt hME0t htabT hret0 hrs htr0
    hm hraT D w₀ (fun _ h => (h : False).elim)
    (by rw [hspw₀w]; exact hWE.rel) hsw.symm (fun r v hm => (hreg r v hm).symm) hstkC G
    (Arm.r .PC cn + 4) (enterAt (L.A h) cn) (hME cn w₀ hsp0 herrc hcOk.img hbw0) hagreeC
    (by rw [BitVec.add_sub_cancel]; exact hcOk.ra) hx29t.symm
  exact L.tableOfE_twinCE (TwinCE.symm L htwc) htabT

end LinkSys

end E2E
