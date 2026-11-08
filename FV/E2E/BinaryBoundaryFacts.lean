import FV.E2E.BinaryBoundaryDefs
import FV.E2E.LinkReturnPinContract

namespace E2E.BinaryBoundaryFacts
open Backend Backend.Proof E2E.LinkCheck E2E.SemanticBinary
set_option autoImplicit false
set_option Elab.async false

/-- Only allocation and image facts enter the machine boundary proof. -/
structure Facts (I : SemanticStackBound.CompilerInput) : Prop where
  alloc : ∀ f ∈ (prog I).funcs,lowerRFunc (art I f).vcp (art I f).rf = .ok (art I f).af
  fits : ∀ f ∈ (prog I).funcs,(art I f).base.toNat + 4 * (art I f).fb.words.size ≤ 2 ^ 64
  imgAddr : ∀ f ∈ (prog I).funcs,∀ a,CodeAddr (Arm.set_program Arm.ArmState.default
    ((art I f).fb.program (art I f).base)) a → img I a
  imgCode : ∀ f ∈ (prog I).funcs,∀ t : Arm.ArmState,(∀ a,img I a → t.mem a = imgMem I a) →
    ∀ k w,(art I f).fb.words[k]? = some w →
      Arm.read_mem_bytes 4 ((art I f).base + BitVec.ofNat 64 (4*k)) t = w

theorem of_semantic {I : SemanticStackBound.CompilerInput} {B : BaseEnv} {F : BitVec 64 → Prop}
    (checked : (SemanticStackBound.ofInput I B F).OkSemanticNI) : Facts I :=
  ⟨fun f member => (checked.compiled f member).alloc,checked.fits,checked.imgAddr,checked.imgCode⟩

theorem of_returnPins {I : SemanticStackBound.CompilerInput} {B : BaseEnv} {F : BitVec 64 → Prop}
    {modes : Clif.Function → ReturnPinMode}
    (checked : (SemanticStackBound.ofInput I B F).OkReturnPins modes) : Facts I :=
  ⟨fun f member => (checked.compiled f member).alloc,checked.fits,checked.imgAddr,checked.imgCode⟩

/-- The model state's code addresses are the program's. -/
theorem img_of_codeAddr {I : SemanticStackBound.CompilerInput} 
    (hL : Facts I) {f : Clif.Function} (hf : f ∈ (prog I).funcs)
    {r : Arm.ArmState} {a : BitVec 64} (h : CodeAddr (modelOf I f r) a) : img I a := by
  obtain ⟨p, hp, hpa⟩ := h
  rw [program_modelOf] at hp
  exact hL.imgAddr f hf a ⟨p, hp, hpa⟩

/-- The frame facts of a compiled function. -/
theorem frame_facts {I : SemanticStackBound.CompilerInput} 
    (hL : Facts I) {f : Clif.Function} (hf : f ∈ (prog I).funcs) :
    frameDrop (art I f).af = (art I f).af.frameSize + 16 ∧
    (art I f).af.slotBase = (RAFrame.compute (art I f).vcp (art I f).rf).size ∧
    (RAFrame.compute (art I f).vcp (art I f).rf).intBase ≤
      (RAFrame.compute (art I f).vcp (art I f).rf).size ∧
    (RAFrame.compute (art I f).vcp (art I f).rf).size ≤
      (art I f).af.frameSize - clobberBytes (art I f).af.saves := by
  have allocation := hL.alloc f hf
  have hfr : (art I f).af.frame = true := lowerRFunc_frame allocation
  exact ⟨by simp [frameDrop, hfr], (lowerRFunc_ok allocation).1.2.1, intBase_le_size _ _,
    size_le_frameBody allocation⟩

/-- A byte of the free stack outside the slot region, or of the code, is outside the world; a
byte that is neither is not. -/
theorem not_worldF {I : SemanticStackBound.CompilerInput} 
    (hL : Facts I) {f : Clif.Function} (hf : f ∈ (prog I).funcs)
    {K : Nat} {r : Arm.ArmState} (hN : frameDrop (art I f).af + K ≤ (spv r).toNat)
    {x : BitVec 64} (hx : ¬ img I x)
    (hs : StackBelow (frameDrop (art I f).af + K) (spv r) x → SemanticBinary.SlotArea (art I f).af r x) :
    ¬ worldF I f K r x := by
  obtain ⟨hd, hsb, hib, hsz⟩ := frame_facts hL hf
  have hsp := (spv r).isLt
  have hxl := x.isLt
  have hoff := off_toNat x (spv r) (frameDrop (art I f).af) (by omega)
  simp only [worldF, frameWG, frameW, frameF, spv_modelOf]
  rintro (((⟨h1, h2⟩ | ⟨h1, h2⟩ | hc) | ⟨h1, h2⟩) | hi)
  · obtain ⟨hs1, -⟩ := hs ⟨(hoff.1.1 (by omega)).1, by have := (hoff.1.1 (by omega)).2; omega⟩
    simp only [spBody] at hs1
    omega
  · have := hoff.1.1 (by omega)
    obtain ⟨-, hs2⟩ := hs ⟨this.1, by omega⟩
    simp only [spBody] at hs2
    omega
  · exact hx (img_of_codeAddr hL hf hc)
  · rw [hoff.2.2] at h1 h2
    obtain ⟨-, hs2⟩ := hs ⟨by omega, by omega⟩
    simp only [spBody, BitVec.toNat_sub, hoff.2.2] at hs2
    rw [Nat.mod_eq_of_lt (by omega)] at hs2
    omega
  · exact hx hi

/-- A byte of the outgoing-argument area `[sp_body, sp_body + intBase)` that is not code is in
the world. -/
theorem not_worldF_out {I : SemanticStackBound.CompilerInput} 
    (hL : Facts I) {f : Clif.Function} (hf : f ∈ (prog I).funcs)
    {K : Nat} {r : Arm.ArmState} (hN : frameDrop (art I f).af + K ≤ (spv r).toNat)
    {j : Nat} (hj : j < (RAFrame.compute (art I f).vcp (art I f).rf).intBase)
    (hx : ¬ img I (spBody (art I f).af r + BitVec.ofNat 64 j)) :
    ¬ worldF I f K r (spBody (art I f).af r + BitVec.ofNat 64 j) := by
  obtain ⟨hd, hsb, hib, hsz⟩ := frame_facts hL hf
  have hsp := (spv r).isLt
  have hspbN : (spBody (art I f).af r).toNat = (spv r).toNat - frameDrop (art I f).af :=
    (off_toNat 0 (spv r) _ (by omega)).2.2
  have hxN : (spBody (art I f).af r + BitVec.ofNat 64 j).toNat = (spBody (art I f).af r).toNat + j := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : j < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
  have ho : (spBody (art I f).af r + BitVec.ofNat 64 j - (spv (modelOf I f r) -
      BitVec.ofNat 64 (frameDrop (art I f).af))).toNat = j := by
    rw [spv_modelOf, show spv r - BitVec.ofNat 64 (frameDrop (art I f).af) = spBody (art I f).af r from rfl,
      BitVec.add_comm, BitVec.add_sub_cancel]
    simp; omega
  simp only [worldF, frameWG, frameW, frameF]
  rw [ho]
  rintro (((⟨h1, h2⟩ | ⟨h1, h2⟩ | hc) | ⟨h1, h2⟩) | hi)
  · omega
  · omega
  · exact hx (img_of_codeAddr hL hf hc)
  · rw [spv_modelOf, show spv r - BitVec.ofNat 64 (frameDrop (art I f).af) = spBody (art I f).af r
      from rfl, hxN] at h1
    omega
  · exact hx hi

/-- **The per-run premises of `backend_correct_program` from the boundary contract**, for the
model state `s = modelOf I f r`, the body-entry world `bodyOf af s`, the callees' budget `K` and
the addresses outside the world `worldF I f K r`. The stack premise is the room `StackRoom` only
(#581: `StackAvail` also asks `probeBelow ≤ K`, a fact of the budget, not of the contract). -/
theorem premises {I : SemanticStackBound.CompilerInput} {B : BaseEnv} {f : Clif.Function} {K : Nat} {r : Arm.ArmState}
    {args : List Clif.Val} {cs : Clif.State}
    (hL : Facts I) (hf : f ∈ (prog I).funcs)
    {roB : BitVec 64 → Option (BitVec 8)} (hro : ∀ a b, roB a = some b → r.mem a = b)
    (ho : OutsideCall I roB f (frameDrop (art I f).af + K) r args cs.mem)
    (hr : ClifRun I B f r args cs) :
    AbiEntry (art I f).fb (art I f).base (xreg 30 r) (modelOf I f r) ∧
    StackRoom ((art I f).af.frameSize + 16 + K) (modelOf I f r) ∧
    (∀ a, img I a → ¬ StackBelow (frameDrop (art I f).af + K) (spv (modelOf I f r)) a) ∧
    (∀ a, img I a → (modelOf I f r).mem a = imgMem I a) ∧
    BodyEntry (art I f).af (modelOf I f r) (bodyOf (art I f).af (modelOf I f r)) ∧
    ArgsIn f.sig args (modelOf I f r) ∧ StackArgsAvoid (img I) f.sig args (modelOf I f r) ∧
    Rel.holds ⟨worldF I f K r, fun n => I.syms.lookup n, (art I f).af.slotBase,
      (RAFrame.compute (art I f).vcp (art I f).rf).intBase⟩ f cs.frame.slots cs.mem
      (bodyOf (art I f).af (modelOf I f r)) ∧
    ((sys I B).NeedSlots → (sys I B).PlaceAt cs.mem (spv (bodyOf (art I f).af (modelOf I f r)))) := by
  obtain ⟨hd, hsb, hib, hsz⟩ := frame_facts hL hf
  have hsp := (spv r).isLt
  have hN := ho.stack
  have himg : ∀ a, img I a → (modelOf I f r).mem a = imgMem I a := fun a h => mem_modelOf_img h
  have hspb : spv (bodyOf (art I f).af (modelOf I f r)) = spBody (art I f).af r := by
    rw [spv_bodyOf, spv_modelOf]; rfl
  have hspbN : (spBody (art I f).af r).toNat = (spv r).toNat - frameDrop (art I f).af :=
    (off_toNat 0 (spv r) _ (by omega)).2.2
  -- a byte at `sp_body + j` with `j` below the frame drop is in the free stack
  have hbelow : ∀ j < frameDrop (art I f).af,
      StackBelow (frameDrop (art I f).af + K) (spv r) (spBody (art I f).af r + BitVec.ofNat 64 j) ∧
      (spBody (art I f).af r + BitVec.ofNat 64 j - spBody (art I f).af r).toNat = j := by
    intro j hj
    refine ⟨?_, by rw [BitVec.add_comm, BitVec.add_sub_cancel]; simp; omega⟩
    simp only [StackBelow, BitVec.toNat_add, BitVec.toNat_ofNat, hspbN]
    rw [Nat.mod_eq_of_lt (by omega : j < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
    omega
  refine ⟨⟨by simp, hL.imgCode f hf _ himg, by rw [r_modelOf]; exact ho.pc,
    by rw [r_modelOf]; exact ho.err, by simp only [xreg]; rw [r_modelOf], fun k hk e => ?_,
    by rw [spv_modelOf]; exact ho.spAligned, hL.fits f hf⟩, ?_, ?_, himg,
    bodyEntry_bodyOf _ _, ?_, ?_, ⟨⟨fun a b hv hb => ?_, fun a n hv => ?_, ho.symbols⟩, ?_, ?_⟩, ?_⟩
  · -- the return address is outside `f`'s code
    obtain ⟨w, hw⟩ : ∃ w, (art I f).fb.words[k]? = some w := ⟨_, Array.getElem?_eq_getElem hk⟩
    apply ho.ra
    rw [e]
    have := codeAddr_word (s := modelOf I f r) (base := (art I f).base) (by simp) hw (i := 0) (by omega)
    rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at this
    exact img_of_codeAddr hL hf this
  · -- the stack
    refine stackRoom_of (by rw [spv_modelOf, ← hd]; exact hN) fun a hc hb => ?_
    rw [spv_modelOf, ← hd] at hb
    exact ho.stackFree a (img_of_codeAddr hL hf hc) hb
  · intro a ha
    rw [spv_modelOf]
    exact ho.stackFree a ha
  · -- the arguments
    intro loc v hm
    have h := ho.args loc v hm
    cases loc with
    | reg x => simp only at h ⊢; rw [regVal_modelOf]; exact h
    | stack off =>
      obtain ⟨hfit, hav, hby⟩ := h
      have hbytes : ∀ k < v.ty.bytes, (modelOf I f r).mem (spv r + BitVec.ofNat 64 off + BitVec.ofNat 64 k) =
          r.mem (spv r + BitVec.ofNat 64 off + BitVec.ofNat 64 k) := fun k hk => mem_modelOf_not (hav k hk)
      refine ⟨by rw [spv_modelOf]; exact hfit, fun k hk hc => hav k hk ?_, ?_⟩
      · have := img_of_codeAddr hL hf hc
        rwa [spv_modelOf, BitVec.ofNat_add, ← BitVec.add_assoc] at this
      · rw [spv_modelOf, read_mem_bytes_congr _ _ hbytes]; exact hby
  · intro off v hm
    obtain ⟨-, hav, -⟩ := ho.args (.stack off) v hm
    rw [spv_modelOf]; exact hav
  · -- the live CLIF bytes (the body-entry memory is after the stack probes, #581)
    have hni := ((ho.valid a 1 hv).2 0 (by omega)).1
    simp only [Nat.add_zero] at hni
    show probeMem (art I f).af (modelOf I f r) (BitVec.ofNat 64 a) = b
    rw [probeMem_congr (by rw [spv_modelOf]) (mem_modelOf_not hni)]
    exact ho.bytes a b hv hb
  · obtain ⟨hfit, hk⟩ := ho.valid a n hv
    exact ⟨hfit, fun k hkn => not_worldF hL hf hN (hk k hkn).1 (hk k hkn).2⟩
  · -- the slots
    rw [Rel.slotReg, hspb]; exact hr.slots
  · -- the outgoing area: free stack below the slot region
    refine ⟨show (RAFrame.compute (art I f).vcp (art I f).rf).intBase ≤ 2 ^ 64 by omega,
      fun j hj => ?_, fun a n hv k hk j hj e => ?_⟩
    · change j < (RAFrame.compute (art I f).vcp (art I f).rf).intBase at hj
      rw [hspb]
      obtain ⟨hb, -⟩ := hbelow j (by omega)
      exact not_worldF_out hL hf hN hj (fun hi => ho.stackFree _ hi hb)
    · change j < (RAFrame.compute (art I f).vcp (art I f).rf).intBase at hj
      rw [hspb] at e
      obtain ⟨hb, ho'⟩ := hbelow j (by omega)
      have := ((ho.valid a n hv).2 k hk).2 (by rw [e]; exact hb)
      rw [e] at this
      unfold SemanticBinary.SlotArea at this
      omega
  · intro hN'; rw [hspb]; exact hr.place hN'


end E2E.BinaryBoundaryFacts
