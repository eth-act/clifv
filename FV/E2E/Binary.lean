import FV.E2E.StackBound

/-! # The binary-level theorem (M9, docs/contracts/e2e.md, "Binary level (M9)")

`crate_correct` (`FV/E2E/LinkCheck.lean`) is `backend_correct_program` for every function of a
crate's linked program, with the per-run premises of an Arm entry state `s`, a body-entry world
`w₀` and a CLIF entry state `cs`. Here those premises are stated as a **boundary contract** on
the real machine state `r` in which code outside the program (std's `lang_start`, a fallback
function, a callback) enters a function `f` of the program:

* `OutsideCall I roB f N r args cm` — what the outside caller guarantees at the call: the AAPCS64
  entry (pc at `f`'s link address, return address outside the program's code, `sp` 16-aligned),
  `N` bytes of free stack below `sp` that hold no code, the arguments where AAPCS64 puts them,
  and the CLIF-visible memory `cm` related to `r` (its live bytes are `r`'s, none of them in the
  code or in the free stack except `f`'s own CLIF slot region, the symbol table the CLIF image's).
* `ClifRun I B f r args cs` — the choice of the reference CLIF run (not an obligation on the
  outside code): `cs` is an entry state of `f` on `args`, its stack slots where the compiled frame
  puts them, and (with slotted program callees) the slot-placement oracle at the body's `sp`.
  CLIF leaves slot addresses unspecified; this picks the run the compiled code realises.
* the model state `modelOf I f r`: `r` with the machine's program `f`'s compiled words and the
  memory at the program's code addresses the compiled image (`LinkSys.withImg`). The compiled
  image holds relocated instructions with zero relocation fields, which the model machine runs by
  their link-map semantics (`ArmStepX`); the binary checks (`FV/E2E/BinCheck.lean`) show the
  executable differs from it only there, holding the resolved encodings.

Every other premise of `backend_correct_program` is discharged here: `AbiEntry` (program, code
words, pc, error, return address, alignment, fits), the stack premises (`StackAvail`, the world
complement `F`, the code outside the stack, `hgfree`), `himg`, `BodyEntry` (the body-entry world
is `bodyOf af s`), `ArgsIn` and `StackArgsAvoid` (from `OutsideCall.args` on `r`), and
`Rel.holds`' memory part, `OutRel` (the outgoing area is free stack). `TrapsExplicit` (the CLIF
run traps only explicitly) stays a premise about the CLIF run; `BaseOk` (the contracts of the code
outside the program) stays as in `crate_correct`.

`binary_correct_depth` uses `crate_correct` (a stack of `frameDrop + D * M` bytes for runs of
depth `M`: the statement for recursive programs); `binary_correct` uses the stack bound of a
non-recursive program (`FV/E2E/StackBound.lean`) and the executable's checks.
-/

namespace E2E.Binary

open Backend Backend.Proof E2E.LinkCheck

/-! ## The compiled program of an input -/

/-- The program of the input (`LinkSys.ofInput`'s `P`). -/
abbrev prog (I : LinkInput) : Clif.Program := progOf I.results

/-- The compiled image of `f` (`LinkSys.ofInput`'s `A f`). -/
abbrev art (I : LinkInput) (f : Clif.Function) : Art := artOf I.results f

/-- The program's code addresses (`LinkSys.ofInput`'s `Img`). -/
abbrev img (I : LinkInput) : BitVec 64 → Prop := ImgT (tabOf I.results)

/-- The program's compiled code bytes (`LinkSys.ofInput`'s `imgMem`). -/
abbrev imgMem (I : LinkInput) : Arm.Memory := memT (tabOf I.results)

/-- The linked system with no addresses outside the world (`F` only enters premises; `mach`,
`NeedSlots`, `PlaceAt`, `base`, `P` do not depend on it). -/
abbrev sys (I : LinkInput) (B : BaseEnv) : LinkSys := LinkSys.ofInput I B fun _ => False

/-- The body's stack pointer of an activation of a function with frame `af` entered in `r`. -/
def spBody (af : AFunc) (r : Arm.ArmState) : BitVec 64 := spv r - BitVec.ofNat 64 (frameDrop af)

/-- `a` is in the CLIF stack-slot region of the frame of `af` entered in `r`
(`[sp_body + slotBase, sp_body + frameSize)`). -/
def SlotArea (af : AFunc) (r : Arm.ArmState) (a : BitVec 64) : Prop :=
  af.slotBase ≤ (a - spBody af r).toNat ∧ (a - spBody af r).toNat < af.frameSize

/-- The arguments `args` of a call with signature `sig` where AAPCS64 puts them in `r`: a
register parameter in its register, a stack parameter in the caller's outgoing area at
`sp + off` (inside the address space, outside the code `G`, holding its bits). -/
def ArgsOut (G : BitVec 64 → Prop) (sig : Clif.Signature) (args : List Clif.Val)
    (r : Arm.ArmState) : Prop :=
  ∀ loc v, (loc, v) ∈ (locsOf sig).zip args → match loc with
    | .reg x => VHolds v (regVal r x)
    | .stack off => (spv r).toNat + off + v.ty.bytes ≤ 2 ^ 64 ∧
        Avoids G v.ty.bytes (spv r + BitVec.ofNat 64 off) ∧
        (Arm.read_mem_bytes v.ty.bytes (spv r + BitVec.ofNat 64 off) r).setWidth v.ty.width = v.bits

/-- **The boundary contract**: what code outside the program guarantees when it calls the
function `f` of the program in the machine state `r`, with arguments `args`, its CLIF-visible
memory being `cm`, and `N` bytes of stack. `roB a = some b`: the executable holds the byte `b` of
the CLIF image's read-only data at `a` (`fun _ => none`: no data facts, every live CLIF byte is
required of the caller). -/
structure OutsideCall (I : LinkInput) (roB : BitVec 64 → Option (BitVec 8)) (f : Clif.Function)
    (N : Nat) (r : Arm.ArmState)
    (args : List Clif.Val) (cm : Clif.Mem) : Prop where
  /-- the pc is `f`'s address (its link-map address) -/
  pc : Arm.r .PC r = (art I f).base
  /-- no model error -/
  err : Arm.r .ERR r = .None
  /-- the return address (x30) is outside the program's code: the caller is outside code -/
  ra : ¬ img I (xreg 30 r)
  /-- AAPCS64: `sp` is 16-aligned -/
  spAligned : (spv r).toNat % 16 = 0
  /-- `N` bytes below `sp` without wrapping -/
  stack : N ≤ (spv r).toNat
  /-- none of them is code -/
  stackFree : ∀ a, img I a → ¬ StackBelow N (spv r) a
  /-- the arguments where AAPCS64 puts them (stack arguments outside the code) -/
  args : ArgsOut (img I) f.sig args r
  /-- the live CLIF bytes outside the executable's read-only CLIF data (`roB`) are the
  machine's -/
  bytes : ∀ a b, cm.valid a 1 = true → cm.bytes a = some b → roB (BitVec.ofNat 64 a) = none →
    Arm.read_mem (BitVec.ofNat 64 a) r = b
  /-- the live CLIF bytes at the read-only CLIF data are the CLIF image's (a CLIF-level fact: a
  store into read-only data is stuck) -/
  image : ∀ a b b', cm.valid a 1 = true → cm.bytes a = some b → roB (BitVec.ofNat 64 a) = some b' →
    b = b'
  /-- the live CLIF allocations fit the address space, hold no code, and lie in the free stack
  only in `f`'s CLIF slot region -/
  valid : ∀ a n, cm.valid a n = true → a + n ≤ 2 ^ 64 ∧ ∀ k < n,
    ¬ img I (BitVec.ofNat 64 (a + k)) ∧
    (StackBelow N (spv r) (BitVec.ofNat 64 (a + k)) → SlotArea (art I f).af r (BitVec.ofNat 64 (a + k)))
  /-- the CLIF symbol table is the CLIF image's -/
  symbols : cm.symbols = fun n => I.syms.lookup n

/-- **The reference CLIF run** of an outside call of `f` in `r` (a choice, not an obligation of
the outside code): an entry state of `f` on `args` whose stack slots are where the compiled frame
puts them, and whose slot-placement oracle (needed only with slotted program callees) is at the
body's `sp` with the program's compiled frames. -/
structure ClifRun (I : LinkInput) (B : BaseEnv) (f : Clif.Function) (r : Arm.ArmState)
    (args : List Clif.Val) (cs : Clif.State) : Prop where
  entry : ClifEntry f args cs
  slots : SlotRel f ((spBody (art I f).af r).toNat + (art I f).af.slotBase) cs.frame.slots
  place : (sys I B).NeedSlots → (sys I B).PlaceAt cs.mem (spBody (art I f).af r)

open Classical in
/-- **The model state** of the machine state `r` entering `f`: `r` with the machine's program
`f`'s compiled words and the compiled code bytes at the program's code addresses. -/
noncomputable def modelOf (I : LinkInput) (f : Clif.Function) (r : Arm.ArmState) : Arm.ArmState :=
  Arm.set_program (setMem r fun a => if img I a then imgMem I a else r.mem a)
    ((art I f).fb.program (art I f).base)

theorem r_modelOf (I : LinkInput) (f : Clif.Function) (r : Arm.ArmState) (fld : Arm.StateField) :
    Arm.r fld (modelOf I f r) = Arm.r fld r := by
  simp only [modelOf]
  rw [r_set_program, r_setMem]

theorem spv_modelOf (I : LinkInput) (f : Clif.Function) (r : Arm.ArmState) :
    spv (modelOf I f r) = spv r := r_modelOf I f r _

theorem regVal_modelOf (I : LinkInput) (f : Clif.Function) (r : Arm.ArmState) (x : Reg) :
    regVal (modelOf I f r) x = regVal r x := by
  cases x <;> simp only [regVal, r_modelOf]

open Classical in
theorem mem_modelOf (I : LinkInput) (f : Clif.Function) (r : Arm.ArmState) (a : BitVec 64) :
    (modelOf I f r).mem a = if img I a then imgMem I a else r.mem a := by
  simp only [modelOf, mem_set_program, mem_setMem]

theorem mem_modelOf_img {I : LinkInput} {f : Clif.Function} {r : Arm.ArmState} {a : BitVec 64}
    (h : img I a) : (modelOf I f r).mem a = imgMem I a := by
  rw [mem_modelOf]; simp [h]

theorem mem_modelOf_not {I : LinkInput} {f : Clif.Function} {r : Arm.ArmState} {a : BitVec 64}
    (h : ¬ img I a) : (modelOf I f r).mem a = r.mem a := by
  rw [mem_modelOf]; simp [h]

@[simp] theorem program_modelOf (I : LinkInput) (f : Clif.Function) (r : Arm.ArmState) :
    (modelOf I f r).program = (art I f).fb.program (art I f).base := by
  simp only [modelOf, program_set_program]

/-- The body-entry world `bodyOf af s` is a body entry of `s`. -/
theorem bodyEntry_bodyOf (af : AFunc) (s : Arm.ArmState) : BodyEntry af s (bodyOf af s) where
  sp := spv_bodyOf af s
  fp := x29_bodyOf af s
  args := fun i hi => r_bodyOf af s
    (fun e => by
      have := congrArg (fun f => match f with | Arm.StateField.GPR j => j.toNat | _ => 0) e
      simp at this; omega)
    (fun e => by
      have := congrArg (fun f => match f with | Arm.StateField.GPR j => j.toNat | _ => 0) e
      simp at this; omega)
  argsV := fun i _ => r_bodyOf af s (by simp) (by simp)
  other := fun _ _ h29 h31 => r_bodyOf af s h29 h31
  mem := mem_bodyOf af s
  program := program_bodyOf af s

/-- `BaseOk` does not depend on the addresses `F` outside the world. -/
theorem baseOk_F {I : LinkInput} {B : BaseEnv} {F F' : BitVec 64 → Prop}
    (h : BaseOk (LinkSys.ofInput I B F)) : BaseOk (LinkSys.ofInput I B F') :=
  ⟨h.baseNoAlloc, h.keepSyms, h.aliasSyms, h.baseOs, h.basePc, h.baseExt, h.baseX, h.baseXI,
    h.baseTls, h.baseTry, h.baseNI, h.baseTlsNI, h.baseKeepsPlace, h.baseKeepsAllocs⟩

/-- **The addresses outside the entry activation's world** with callees' budget `K`
(`backend_correct_program`'s `hF`): the frame-private addresses, the callees' dead stack and the
program's code. -/
def worldF (I : LinkInput) (f : Clif.Function) (K : Nat) (r : Arm.ArmState) : BitVec 64 → Prop :=
  frameWG K (RAFrame.compute (art I f).vcp (art I f).rf).intBase
    (RAFrame.compute (art I f).vcp (art I f).rf).size (art I f).af (img I) (modelOf I f r)

/-- The model state's code addresses are the program's. -/
theorem img_of_codeAddr {I : LinkInput} {B : BaseEnv} {F : BitVec 64 → Prop}
    (hL : (LinkSys.ofInput I B F).Ok) {f : Clif.Function} (hf : f ∈ (prog I).funcs)
    {r : Arm.ArmState} {a : BitVec 64} (h : CodeAddr (modelOf I f r) a) : img I a := by
  obtain ⟨p, hp, hpa⟩ := h
  rw [program_modelOf] at hp
  exact hL.imgAddr f hf a ⟨p, hp, hpa⟩

/-- The frame facts of a compiled function. -/
theorem frame_facts {I : LinkInput} {B : BaseEnv} {F : BitVec 64 → Prop}
    (hL : (LinkSys.ofInput I B F).Ok) {f : Clif.Function} (hf : f ∈ (prog I).funcs) :
    frameDrop (art I f).af = (art I f).af.frameSize + 16 ∧
    (art I f).af.slotBase = (RAFrame.compute (art I f).vcp (art I f).rf).size ∧
    (RAFrame.compute (art I f).vcp (art I f).rf).intBase ≤
      (RAFrame.compute (art I f).vcp (art I f).rf).size ∧
    (RAFrame.compute (art I f).vcp (art I f).rf).size ≤ (art I f).af.frameSize := by
  have hc := hL.compiled f hf
  have hfr : (art I f).af.frame = true := lowerRFunc_frame hc.alloc
  exact ⟨by simp [frameDrop, hfr], (lowerRFunc_ok hc.alloc).1.2.1, intBase_le_size _ _,
    size_le_frameSize hc.alloc⟩

/-- A byte of the free stack outside the slot region, or of the code, is outside the world; a
byte that is neither is not. -/
theorem not_worldF {I : LinkInput} {B : BaseEnv} {F : BitVec 64 → Prop}
    (hL : (LinkSys.ofInput I B F).Ok) {f : Clif.Function} (hf : f ∈ (prog I).funcs)
    {K : Nat} {r : Arm.ArmState} (hN : frameDrop (art I f).af + K ≤ (spv r).toNat)
    {x : BitVec 64} (hx : ¬ img I x)
    (hs : StackBelow (frameDrop (art I f).af + K) (spv r) x → SlotArea (art I f).af r x) :
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
theorem not_worldF_out {I : LinkInput} {B : BaseEnv} {F : BitVec 64 → Prop}
    (hL : (LinkSys.ofInput I B F).Ok) {f : Clif.Function} (hf : f ∈ (prog I).funcs)
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
the addresses outside the world `worldF I f K r`. -/
theorem premises {I : LinkInput} {B : BaseEnv} {f : Clif.Function} {K : Nat} {r : Arm.ArmState}
    {args : List Clif.Val} {cs : Clif.State}
    (hL : (LinkSys.ofInput I B (worldF I f K r)).Ok) (hf : f ∈ (prog I).funcs)
    {roB : BitVec 64 → Option (BitVec 8)} (hro : ∀ a b, roB a = some b → r.mem a = b)
    (ho : OutsideCall I roB f (frameDrop (art I f).af + K) r args cs.mem)
    (hr : ClifRun I B f r args cs) :
    AbiEntry (art I f).fb (art I f).base (xreg 30 r) (modelOf I f r) ∧
    StackAvail K (art I f).af (modelOf I f r) ∧
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
  · -- the live CLIF bytes
    have hni := ((ho.valid a 1 hv).2 0 (by omega)).1
    simp only [Nat.add_zero] at hni
    simp only [Arm.read_mem, mem_bodyOf]
    rw [show Arm.read_store (BitVec.ofNat 64 a) (modelOf I f r).mem = (modelOf I f r).mem (BitVec.ofNat 64 a)
      from rfl, mem_modelOf_not hni]
    cases hroa : roB (BitVec.ofNat 64 a) with
    | none => exact ho.bytes a b hv hb hroa
    | some b' => rw [hro _ _ hroa, ho.image a b b' hv hb hroa]
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
      unfold SlotArea at this
      omega
  · intro hN'; rw [hspb]; exact hr.place hN'

/-- The linked machine does not depend on the addresses `F` outside the world. -/
theorem hooks_F (I : LinkInput) (B : BaseEnv) (F F' : BitVec 64 → Prop) :
    ∀ M, (LinkSys.ofInput I B F).hooks M = (LinkSys.ofInput I B F').hooks M
  | 0 => rfl
  | M + 1 => by
    simp only [LinkSys.hooks]
    rw [hooks_F I B F F' M]
    rfl

theorem mach_F (I : LinkInput) (B : BaseEnv) (F F' : BitVec 64 → Prop) (M : Nat)
    (f : Clif.Function) : (LinkSys.ofInput I B F).mach M f = (LinkSys.ofInput I B F').mach M f := by
  simp only [LinkSys.mach]
  rw [hooks_F I B F F' M]
  rfl

/-! ## The binary-level theorems -/

/-- **The binary-level theorem at depth `M`** (any program, recursive ones included: the stack
premise is `frameDrop + D * M` bytes, `backend_correct_program`'s budget): for a crate input that
passes the checker, a function `f` of the program called by outside code that meets the boundary
contract `OutsideCall` in the machine state `r`, the linked machine of depth `M` from the model
state of `r` refines the whole-program CLIF run of at most `M + 1` steps from the reference entry
state `cs` (`ClifRun`), returning to the caller's return address (x30 of `r`). The premises left:
the base environment's contracts (`BaseOk`) and the CLIF run's explicit traps (`TrapsExplicit`). -/
theorem binary_correct_depth {I : LinkInput} (hI : okB I = true) (B : BaseEnv)
    (hB : BaseOk (sys I B)) {n : String} {f : Clif.Function} (hf : (prog I).func? n = some f)
    (M : Nat) {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (ho : OutsideCall I (fun _ => none) f (frameDrop (art I f).af + I.D * M) r args cs.mem)
    (hr : ClifRun I B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) ((prog I).only f) cs) :
    ArmRefines (art I f).fb (art I f).base (xreg 30 r) ((sys I B).mach M f) (modelOf I f r)
      (Clif.runLoop B.env (prog I) (M + 1) cs) := by
  have hB' : BaseOk (LinkSys.ofInput I B (worldF I f (I.D * M) r)) := baseOk_F hB
  have himgF : ∀ a, (LinkSys.ofInput I B (worldF I f (I.D * M) r)).Img a →
      worldF I f (I.D * M) r a := fun _ h => .inr h
  have hL := okB_sound hI hB' himgF
  obtain ⟨hent, hres, hgfree, himg, hbe, hargs, hsav, hrel, hpl⟩ :=
    premises hL (Clif.Program.func?_some hf).1 (fun _ _ h => by cases h) ho hr
  rw [mach_F I B (fun _ => False) (worldF I f (I.D * M) r)]
  exact crate_correct hI n B _ hB' himgF f hf M _ _ _ args cs hent hres rfl hgfree himg hbe hargs
    hr.entry hsav hrel hpl htr

/-- A contract with more stack gives one with less. -/
theorem OutsideCall.mono {I : LinkInput} {roB : BitVec 64 → Option (BitVec 8)} {f : Clif.Function}
    {N N' : Nat} {r : Arm.ArmState} {args : List Clif.Val} {cm : Clif.Mem}
    (h : OutsideCall I roB f N' r args cm) (hN : N ≤ N') : OutsideCall I roB f N r args cm where
  pc := h.pc
  err := h.err
  ra := h.ra
  spAligned := h.spAligned
  stack := Nat.le_trans hN h.stack
  stackFree := fun a ha hb => h.stackFree a ha ⟨hb.1, by have := hb.2; omega⟩
  args := h.args
  bytes := h.bytes
  image := h.image
  valid := fun a n hv => ⟨(h.valid a n hv).1, fun k hk => ⟨((h.valid a n hv).2 k hk).1,
    fun hb => ((h.valid a n hv).2 k hk).2 ⟨hb.1, by have := hb.2; omega⟩⟩⟩
  symbols := h.symbols

/-- A returning whole-program CLIF run of `f` satisfies `TrapsExplicit` (as in
`backend_correct_program_returned`): the premise is needed only for trapping runs. -/
theorem trapsExplicit_of_run {L : LinkSys} (hL : L.Ok) {f : Clif.Function} (hf : f ∈ L.P.funcs)
    {M : Nat} {args : List Clif.Val} {cs : Clif.State} {vals : List Clif.Val} {cm : Clif.Mem}
    (hcs : ClifEntry f args cs) (hsym : cs.mem.symbols = L.syms)
    (hrun : Clif.runLoop L.base L.P (M + 1) cs = .returned vals cm) :
    TrapsExplicit (Clif.linkEnvN L.P L.base M) (L.P.only f) cs := by
  have hIf : Clif.LInv (L.P.only f) cs := runInv_entry (by simp [Clif.Program.only]) hcs
  obtain ⟨m, hm⟩ := Clif.runLoop_linkN (base := L.base) (syms := L.syms) M hL.names hf hL.free
    (hL.indScope f hf) (E := Clif.linkEnvN L.P L.base M) rfl (fun _ _ => rfl) (fun _ _ _ _ => rfl)
    (M + 1) cs (Nat.le_refl _) (runInv_entry hf hcs) hIf
    (fun _ => hsym) (by rw [hrun]; exact fun _ h => nomatch h)
    (by rw [hrun]; exact fun h => nomatch h)
  rw [hrun] at hm
  refine trapsExplicit_of_returned (fun hnf s hr g' hg' => ?_) hm
  rw [hcs.func] at hnf
  simp only [Clif.Program.only, List.mem_cons, List.not_mem_nil, or_false] at hg'
  subst hg'
  have hPf : ∀ g ∈ (L.P.only g').funcs, Clif.LinkFree g := fun g hg => by
    simp only [Clif.Program.only, List.mem_cons, List.not_mem_nil, or_false] at hg
    subst hg; exact hL.free g hf
  rw [(reach_symbols hPf (Clif.linkEnvN_keeps hL.free (hL.indScope g' hf hnf).keep) hr hIf).1, hsym]
  exact hL.indNoSym g' hf hnf

/-! ## The binary facts -/

/-- **The executable's loaded segments** as the binary checks read them: the byte at each loaded
address (`mem`), and the addresses nothing writes after loading (`kept`: the read-only segments;
the relocation-read-only data, `PT_GNU_RELRO`). -/
structure Image where
  mem : BitVec 64 → Option (BitVec 8)
  kept : BitVec 64 → Prop

/-- **The loader premise**: the machine state `r` holds the executable's kept bytes (the OS maps
the segments at their link addresses; read-only segments are never written, and no code writes
the relocation-read-only data). -/
def Image.Intact (X : Image) (r : Arm.ArmState) : Prop := ∀ a, X.kept a → X.mem a = some (r.mem a)

/-- **The binary facts** of an executable `X` for a crate input `I` (what the binary checks
establish, `binary_correct_of_checks`): the input passes the crate checker (`okB`); the program's
code bytes are kept bytes of the executable, equal to the compiled image except at the bytes `R`
of relocated instructions (which hold the resolved encodings, `FV/E2E/BinCheck.lean`); the CLIF
image's read-only data `roB` are kept bytes of the executable. -/
structure BinFacts (I : LinkInput) (X : Image) (R : BitVec 64 → Prop)
    (roB : BitVec 64 → Option (BitVec 8)) : Prop where
  ok : okB I = true
  code : ∀ a, img I a → X.kept a ∧ (X.mem a = some (imgMem I a) ∨ R a)
  data : ∀ a b, roB a = some b → X.kept a ∧ X.mem a = some b

/-- **The binary-level theorem** (`docs/contracts/e2e.md`, "Binary level (M9)"): for an
executable with the binary facts of a crate input (`BinFacts`), whose loaded kept bytes the
machine state `r` holds (`Image.Intact`), a function `f` of the program whose calls reach no call
cycle (`goodN`, the stack check of `FV/E2E/StackBound.lean`) called by outside code that meets
the boundary contract (`OutsideCall`, with `f`'s stack bound `stackFn I f`), the linked machine
(at every depth `M`) from the model state of `r` refines the whole-program CLIF run of at most
`M + 1` steps from the reference entry state (`ClifRun`), returning to the caller's return
address; and the model state differs from `r` only at the relocated instruction bytes `R`. The
premises left: the base environment's contracts (`BaseOk`) and the CLIF run's explicit traps
(`TrapsExplicit`). -/
theorem binary_correct {I : LinkInput} {X : Image} {R : BitVec 64 → Prop}
    {roB : BitVec 64 → Option (BitVec 8)} (hbin : BinFacts I X R roB) (B : BaseEnv)
    (hB : BaseOk (sys I B)) {n : String} (hn : StackBound.goodN I n = true) {f : Clif.Function}
    (hf : (prog I).func? n = some f) (M : Nat) {r : Arm.ArmState}
    {args : List Clif.Val} {cs : Clif.State} (hX : X.Intact r)
    (ho : OutsideCall I roB f (StackBound.stackFn I f) r args cs.mem)
    (hr : ClifRun I B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) ((prog I).only f) cs) :
    ArmRefines (art I f).fb (art I f).base (xreg 30 r) ((sys I B).mach M f) (modelOf I f r)
      (Clif.runLoop B.env (prog I) (M + 1) cs) ∧
    ∀ a, (modelOf I f r).mem a ≠ r.mem a → R a := by
  refine ⟨?_, fun a hne => ?_⟩
  · have hB' : BaseOk (LinkSys.ofInput I B (worldF I f (StackBound.bud I f) r)) := baseOk_F hB
    have himgF : ∀ a, (LinkSys.ofInput I B (worldF I f (StackBound.bud I f) r)).Img a →
        worldF I f (StackBound.bud I f) r a := fun _ h => .inr h
    have hL := okB_sound hbin.ok hB' himgF
    have hro : ∀ a b, roB a = some b → r.mem a = b := fun a b h => by
      have h1 := hbin.data a b h
      have h2 := hX a h1.1
      rw [h1.2] at h2
      exact (Option.some.inj h2).symm
    obtain ⟨hent, -, hgfree, himg, hbe, hargs, hsav, hrel, hpl⟩ :=
      premises hL (Clif.Program.func?_some hf).1 hro ho hr
    rw [mach_F I B (fun _ => False) (worldF I f (StackBound.bud I f) r)]
    exact StackBound.crate_correct_stackN hbin.ok hn B _ hB' himgF f hf M _ _ _ args cs hent
      (by rw [spv_modelOf]; exact ho.stack) hgfree rfl himg hbe hargs hr.entry hsav hrel hpl htr
  · by_cases hi : img I a
    · rw [mem_modelOf_img hi] at hne
      rcases (hbin.code a hi).2 with h | h
      · have h2 := hX a (hbin.code a hi).1
        rw [h] at h2
        exact absurd (Option.some.inj h2) hne
      · exact h
    · exact absurd (mem_modelOf_not hi) hne

/-- **`binary_correct` for a non-recursive program** (`stackB I = some S`): every function, with
`S` bytes of stack. -/
theorem binary_correct_bound {I : LinkInput} {X : Image} {R : BitVec 64 → Prop}
    {roB : BitVec 64 → Option (BitVec 8)} (hbin : BinFacts I X R roB) {S : Nat}
    (hS : StackBound.stackB I = some S) (B : BaseEnv) (hB : BaseOk (sys I B)) {n : String}
    {f : Clif.Function} (hf : (prog I).func? n = some f) (M : Nat) {r : Arm.ArmState}
    {args : List Clif.Val} {cs : Clif.State} (hX : X.Intact r)
    (ho : OutsideCall I roB f S r args cs.mem) (hr : ClifRun I B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) ((prog I).only f) cs) :
    ArmRefines (art I f).fb (art I f).base (xreg 30 r) ((sys I B).mach M f) (modelOf I f r)
      (Clif.runLoop B.env (prog I) (M + 1) cs) ∧
    ∀ a, (modelOf I f r).mem a ≠ r.mem a → R a := by
  have hn : StackBound.goodN I n = true := by
    unfold StackBound.goodN; rw [show (progOf I.results).func? n = some f from hf]
    exact (StackBound.stackB_some hS).1 f (Clif.Program.func?_some hf).1
  exact binary_correct hbin B hB hn hf M hX
    (ho.mono (StackBound.stackFn_le hS (Clif.Program.func?_some hf).1)) hr htr

end E2E.Binary
