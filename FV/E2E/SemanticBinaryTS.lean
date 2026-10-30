import FV.E2E.SemanticBinary
import FV.E2E.SemanticStackBoundTS
import FV.E2E.BinaryT

/-! # Typed copies of `FV.E2E.SemanticBinary` (#722)

The declarations of `FV.E2E.SemanticBinary` that depend on the link contract
(`LinkSys.OkSemanticNI`, `okB`, `ArmRefines`), for the typed contract `LinkSys.OkT` and the
typed checks `SemanticStackBound.okBTS` (suffix `TS`; as `FV/E2E/DeadCleanupBinaryT.lean` is of
`FV/E2E/DeadCleanupBinary.lean`). -/

namespace E2E.SemanticBinary
set_option autoImplicit false
open Backend Backend.Proof E2E.LinkCheck

/-- The model state's code addresses are the program's. -/
theorem img_of_codeAddrTS {I : SemanticStackBound.CompilerInput} {B : BaseEnv}
    {F : BitVec 64 → Prop} (hL : (SemanticStackBound.ofInput I B F).OkT) {f : Clif.Function}
    (hf : f ∈ (prog I).funcs) {r : Arm.ArmState} {a : BitVec 64} (h : CodeAddr (modelOf I f r) a) :
    img I a := by
  obtain ⟨p, hp, hpa⟩ := h
  rw [program_modelOf] at hp
  exact hL.imgAddr f hf a ⟨p, hp, hpa⟩

/-- The frame facts of a compiled function. -/
theorem frame_factsTS {I : SemanticStackBound.CompilerInput} {B : BaseEnv} {F : BitVec 64 → Prop}
    (hL : (SemanticStackBound.ofInput I B F).OkT) {f : Clif.Function} (hf : f ∈ (prog I).funcs) :
    frameDrop (art I f).af = (art I f).af.frameSize + 16 ∧
    (art I f).af.slotBase = (RAFrame.compute (art I f).vcp (art I f).rf).size ∧
    (RAFrame.compute (art I f).vcp (art I f).rf).intBase ≤
      (RAFrame.compute (art I f).vcp (art I f).rf).size ∧
    (RAFrame.compute (art I f).vcp (art I f).rf).size ≤
      (art I f).af.frameSize - clobberBytes (art I f).af.saves := by
  have hc := hL.compiled f hf
  have hfr : (art I f).af.frame = true := lowerRFunc_frame hc.alloc
  exact ⟨by simp [frameDrop, hfr], (lowerRFunc_ok hc.alloc).1.2.1, intBase_le_size _ _,
    size_le_frameBody hc.alloc⟩

/-- A byte of the free stack outside the slot region, or of the code, is outside the world; a
byte that is neither is not. -/
theorem not_worldFTS {I : SemanticStackBound.CompilerInput} {B : BaseEnv} {F : BitVec 64 → Prop}
    (hL : (SemanticStackBound.ofInput I B F).OkT) {f : Clif.Function} (hf : f ∈ (prog I).funcs)
    {K : Nat} {r : Arm.ArmState} (hN : frameDrop (art I f).af + K ≤ (spv r).toNat)
    {x : BitVec 64} (hx : ¬ img I x)
    (hs : StackBelow (frameDrop (art I f).af + K) (spv r) x → SlotArea (art I f).af r x) :
    ¬ worldF I f K r x := by
  obtain ⟨hd, hsb, hib, hsz⟩ := frame_factsTS hL hf
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
  · exact hx (img_of_codeAddrTS hL hf hc)
  · rw [hoff.2.2] at h1 h2
    obtain ⟨-, hs2⟩ := hs ⟨by omega, by omega⟩
    simp only [spBody, BitVec.toNat_sub, hoff.2.2] at hs2
    rw [Nat.mod_eq_of_lt (by omega)] at hs2
    omega
  · exact hx hi

/-- A byte of the outgoing-argument area `[sp_body, sp_body + intBase)` that is not code is in
the world. -/
theorem not_worldF_outTS {I : SemanticStackBound.CompilerInput} {B : BaseEnv}
    {F : BitVec 64 → Prop}
    (hL : (SemanticStackBound.ofInput I B F).OkT) {f : Clif.Function} (hf : f ∈ (prog I).funcs)
    {K : Nat} {r : Arm.ArmState} (hN : frameDrop (art I f).af + K ≤ (spv r).toNat)
    {j : Nat} (hj : j < (RAFrame.compute (art I f).vcp (art I f).rf).intBase)
    (hx : ¬ img I (spBody (art I f).af r + BitVec.ofNat 64 j)) :
    ¬ worldF I f K r (spBody (art I f).af r + BitVec.ofNat 64 j) := by
  obtain ⟨hd, hsb, hib, hsz⟩ := frame_factsTS hL hf
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
  · exact hx (img_of_codeAddrTS hL hf hc)
  · rw [spv_modelOf, show spv r - BitVec.ofNat 64 (frameDrop (art I f).af) = spBody (art I f).af r
      from rfl, hxN] at h1
    omega
  · exact hx hi

/-- **The per-run premises of `backend_correct_programT` from the boundary contract**
(`premises` under `OkT`; as there the stack premise is the room `StackRoom` only, #581). -/
theorem premisesTS {I : SemanticStackBound.CompilerInput} {B : BaseEnv} {f : Clif.Function}
    {K : Nat} {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hL : (SemanticStackBound.ofInput I B (worldF I f K r)).OkT) (hf : f ∈ (prog I).funcs)
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
  obtain ⟨hd, hsb, hib, hsz⟩ := frame_factsTS hL hf
  have hsp := (spv r).isLt
  have hN := ho.stack
  have himg : ∀ a, img I a → (modelOf I f r).mem a = imgMem I a := fun a h => mem_modelOf_img h
  have hspb : spv (bodyOf (art I f).af (modelOf I f r)) = spBody (art I f).af r := by
    rw [spv_bodyOf, spv_modelOf]; rfl
  have hspbN : (spBody (art I f).af r).toNat = (spv r).toNat - frameDrop (art I f).af :=
    (off_toNat 0 (spv r) _ (by omega)).2.2
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
  · obtain ⟨w, hw⟩ : ∃ w, (art I f).fb.words[k]? = some w := ⟨_, Array.getElem?_eq_getElem hk⟩
    apply ho.ra
    rw [e]
    have := codeAddr_word (s := modelOf I f r) (base := (art I f).base) (by simp) hw (i := 0) (by omega)
    rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at this
    exact img_of_codeAddrTS hL hf this
  · refine stackRoom_of (by rw [spv_modelOf, ← hd]; exact hN) fun a hc hb => ?_
    rw [spv_modelOf, ← hd] at hb
    exact ho.stackFree a (img_of_codeAddrTS hL hf hc) hb
  · intro a ha
    rw [spv_modelOf]
    exact ho.stackFree a ha
  · intro loc v hm
    have h := ho.args loc v hm
    cases loc with
    | reg x => simp only at h ⊢; rw [regVal_modelOf]; exact h
    | stack off =>
      obtain ⟨hfit, hav, hby⟩ := h
      have hbytes : ∀ k < v.ty.bytes, (modelOf I f r).mem (spv r + BitVec.ofNat 64 off + BitVec.ofNat 64 k) =
          r.mem (spv r + BitVec.ofNat 64 off + BitVec.ofNat 64 k) := fun k hk => mem_modelOf_not (hav k hk)
      refine ⟨by rw [spv_modelOf]; exact hfit, fun k hk hc => hav k hk ?_, ?_⟩
      · have := img_of_codeAddrTS hL hf hc
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
    exact ⟨hfit, fun k hkn => not_worldFTS hL hf hN (hk k hkn).1 (hk k hkn).2⟩
  · rw [Rel.slotReg, hspb]; exact hr.slots
  · refine ⟨show (RAFrame.compute (art I f).vcp (art I f).rf).intBase ≤ 2 ^ 64 by omega,
      fun j hj => ?_, fun a n hv k hk j hj e => ?_⟩
    · change j < (RAFrame.compute (art I f).vcp (art I f).rf).intBase at hj
      rw [hspb]
      obtain ⟨hb, -⟩ := hbelow j (by omega)
      exact not_worldF_outTS hL hf hN hj (fun hi => ho.stackFree _ hi hb)
    · change j < (RAFrame.compute (art I f).vcp (art I f).rf).intBase at hj
      rw [hspb] at e
      obtain ⟨hb, ho'⟩ := hbelow j (by omega)
      have := ((ho.valid a n hv).2 k hk).2 (by rw [e]; exact hb)
      rw [e] at this
      unfold SlotArea at this
      omega
  · intro hN'; rw [hspb]; exact hr.place hN'

/-- **The binary facts** (`BinFacts` with the typed checks `okBTS`). -/
structure BinFactsTS (I : SemanticStackBound.CompilerInput) (X : Image) (R : BitVec 64 → Prop)
    (roB : BitVec 64 → Option (BitVec 8)) : Prop where
  ok : SemanticStackBound.okBTS I = true
  code : ∀ a, img I a → X.kept a ∧ (X.mem a = some (imgMem I a) ∨ R a)
  data : ∀ a b, roB a = some b → X.kept a ∧ X.mem a = some b

/-- **The binary-level theorem** (`binary_correct` with `ArmRefinesT`). -/
theorem binary_correctTS {I : SemanticStackBound.CompilerInput} {X : Image} {R : BitVec 64 → Prop}
    {roB : BitVec 64 → Option (BitVec 8)} (hbin : BinFactsTS I X R roB) (B : BaseEnv)
    (hB : BaseOk (sys I B)) {n : String} (hn : SemanticStackBound.goodN I n = true)
    {f : Clif.Function} (hf : (prog I).func? n = some f) (M : Nat) {r : Arm.ArmState}
    {args : List Clif.Val} {cs : Clif.State} (hX : X.Intact r)
    (ho : OutsideCall I roB f (SemanticStackBound.stackFn I f) r args cs.mem)
    (hr : ClifRun I B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) (prog I).bare cs) :
    ArmRefinesT (art I f).fb (art I f).base (xreg 30 r) ((sys I B).mach M f) (modelOf I f r)
      (Clif.runLoop B.env (prog I) (M + 1) cs) ∧
    ∀ a, (modelOf I f r).mem a ≠ r.mem a → R a := by
  refine ⟨?_, fun a hne => ?_⟩
  · have hB' : BaseOk (SemanticStackBound.ofInput I B (worldF I f (SemanticStackBound.bud I f) r)) :=
      baseOk_F hB
    have himgF : ∀ a, (SemanticStackBound.ofInput I B (worldF I f (SemanticStackBound.bud I f) r)).Img a →
        worldF I f (SemanticStackBound.bud I f) r a := fun _ h => .inr h
    have hL := SemanticStackBound.okBTS_sound hbin.ok hB' himgF
    have hro : ∀ a b, roB a = some b → r.mem a = b := fun a b h =>
      hX a b (hbin.data a b h).1 (hbin.data a b h).2
    obtain ⟨hent, -, hgfree, himg, hbe, hargs, hsav, hrel, hpl⟩ :=
      premisesTS hL (Clif.Program.func?_some hf).1 hro ho hr
    rw [mach_F I B (fun _ => False) (worldF I f (SemanticStackBound.bud I f) r)]
    exact SemanticStackBound.crate_correct_stackNTS hbin.ok hn B _ hB' himgF f hf M _ _ _ args cs hent
      (by rw [spv_modelOf]; exact ho.stack) hgfree rfl himg hbe hargs hr.entry hsav hrel hpl htr
  · by_cases hi : img I a
    · rw [mem_modelOf_img hi] at hne
      rcases (hbin.code a hi).2 with h | h
      · exact absurd (hX a _ (hbin.code a hi).1 h).symm hne
      · exact h
    · exact absurd (mem_modelOf_not hi) hne

/-- **The binary facts from the checks** (`binFacts_of_checks` with `okBTS`). -/
theorem binFacts_of_checksTS {I : SemanticStackBound.CompilerInput} {D : List Clif.DataObject}
    {file : ByteArray} (hI : SemanticStackBound.okBTS I = true)
    (hB : BinCheck.BinOkWithResults I I.results D file) :
    BinFactsTS I (imageOf file) (BinCheck.RelocAtWithResults I I.results) (BinCheck.roByte I D) where
  ok := hI
  code := fun _ ha =>
    have himg : imgB (tabOf I.results) = true :=
      SemanticStackBound.okBTS_global hI ("imgCode: the image reads back", imgB (tabOf I.results))
        (by simp [globalChks])
    have h := BinCheck.img_bytesWithResults hB himg ha
    ⟨.inl h.1, h.2⟩
  data := fun _ _ h =>
    have h' := BinCheck.roByte_sound hB.data h
    ⟨h'.2, h'.1⟩

/-- **The binary-level theorem for an executable file** that passes the checks
(`binary_correct_of_checks` with `okBTS`, `ArmRefinesT`). -/
theorem binary_correct_of_checksTS {I : SemanticStackBound.CompilerInput}
    {D : List Clif.DataObject} {file : ByteArray}
    (hI : SemanticStackBound.okBTS I = true) (hbin : BinCheck.BinOkWithResults I I.results D file)
    (B : BaseEnv) (hB : BaseOk (sys I B))
    {n : String} (hn : SemanticStackBound.goodN I n = true) {f : Clif.Function}
    (hf : (prog I).func? n = some f) (M : Nat) {r : Arm.ArmState} {args : List Clif.Val}
    {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (SemanticStackBound.stackFn I f) r args cs.mem)
    (hr : ClifRun I B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) (prog I).bare cs) :
    ArmRefinesT (art I f).fb (art I f).base (xreg 30 r) ((sys I B).mach M f) (modelOf I f r)
      (Clif.runLoop B.env (prog I) (M + 1) cs) ∧
    ∀ a, (modelOf I f r).mem a ≠ r.mem a → BinCheck.RelocAtWithResults I I.results a :=
  binary_correctTS (binFacts_of_checksTS hI hbin) B hB hn hf M hX ho hr htr

end E2E.SemanticBinary
