import FV.E2E.ExecGoodRun

/-! # D4: the GOT slots of the executable's `adrp`/`ldr` pairs (L3 (c))

`binary_correct_exec_of_reads` leaves `RunReadsN`: at every guarded state of the model's run the
memory-read facts D2 (`insn`) and D4 (`got`). Here D4 is discharged:

* **which addresses** (`GotSlot I file`): the 8 bytes of every slot `G` that the file's resolved
  `adrp`/`ldr` words of a GOT pair of a function of the program address (in the checked form of
  `PairOk.adrpLdr`: `rd < 31`, `G` aligned, the page in range). The decidable check `gotB` (on an
  excerpt of the file, `gotB_sound`) shows `GotOk`: each such byte is loaded, `ro`/`relro` (so
  `Image.Intact` gives it in `r`) and no relocated instruction byte (`RelocAt`);
* **the kept set** (`LinkSys.extImg`): the linked system of the proof with the code image
  extended by the slots (`Img ∨ S`, holding the model state's bytes). Its `Ok` is the program's
  (`Ok.extImg`), its machine the same (`hooks_extImg`); so every activation keeps the slots
  (`GoodAt`: `Img ⊆ G`, the entry's image bytes) and `RL.GoodX.got` gives the slot's entry bytes at
  a GOT `ldr`, which are the model state's, which are the file's;
* **the outside code** keeps the slots: the base contracts (`BaseOk.baseOs`, `baseTry`, `baseTls`)
  are stated for every kept set; what the outside caller guarantees in addition
  (`OutsideAvoids`): the slots are not in the free stack, the stack arguments, or the live CLIF
  memory (the conditions `OutsideCall` states for the code image).

`binary_correct_exec_of_insn`: `binary_correct_exec_of_reads` with D2 only (`RunInsnN`). -/

namespace E2E

open Backend Backend.Proof E2E.LinkCheck E2E.BinCheck Elf

/-! ## The extended code image -/

namespace LinkSys

/-- `L` with exterior `F` and the code image extended by `S`, holding `m`. -/
def extImg (L : LinkSys) (F S : BitVec 64 → Prop) (m : Arm.Memory) : LinkSys :=
  { L with F := F, Img := fun a => L.Img a ∨ S a, imgMem := m }

theorem hooks_extImg (L : LinkSys) (F S : BitVec 64 → Prop) (m : Arm.Memory) :
    ∀ M, (L.extImg F S m).hooks M = L.hooks M
  | 0 => rfl
  | M + 1 => by
    simp only [LinkSys.hooks]
    rw [hooks_extImg L F S m M]
    rfl

theorem mach_extImg (L : LinkSys) (F S : BitVec 64 → Prop) (m : Arm.Memory) (M : Nat)
    (g : Clif.Function) : (L.extImg F S m).mach M g = L.mach M g := by
  simp only [LinkSys.mach]
  rw [hooks_extImg]
  rfl

/-- **The extended system is a linked program**: the code image's facts hold for any extension
holding the image's bytes on the image, inside the exterior. -/
theorem Ok.extImg {L : LinkSys} (hL : L.Ok) {F S : BitVec 64 → Prop} {m : Arm.Memory}
    (hm : ∀ a, L.Img a → m a = L.imgMem a) (hF : ∀ a, L.Img a ∨ S a → F a) :
    (L.extImg F S m).Ok :=
  { hL with
    imgAddr := fun g hg a ha => .inl (hL.imgAddr g hg a ha)
    imgCode := fun g hg t ht => hL.imgCode g hg t fun a ha => (ht a (.inl ha)).trans (hm a ha)
    imgF := hF }

theorem Budget.extImg {L : LinkSys} {κ : Nat → Clif.Function → Nat} (h : L.Budget κ)
    (F S : BitVec 64 → Prop) (m : Arm.Memory) : (L.extImg F S m).Budget κ := h

theorem reachL_extImg {L : LinkSys} {F S : BitVec 64 → Prop} {m : Arm.Memory} {M : Nat}
    {f : Clif.Function} {c : Arm.ArmState} {M' : Nat} {g : Clif.Function} {c' t : Arm.ArmState}
    (h : L.ReachL M f c M' g c' t) : (L.extImg F S m).ReachL M f c M' g c' t := by
  induction h with
  | act hj =>
    rw [← mach_extImg L F S m] at hj ⊢
    exact .act hj
  | nest hj hc herr _ ih =>
    rw [← mach_extImg L F S m] at hj hc herr ih
    exact .nest hj hc herr ih

end LinkSys

namespace ExecBytes

open Binary

variable {I : LinkInput} {B : BaseEnv} {file : ByteArray}

/-! ## The GOT slots and their check -/

/-- **The GOT slot bytes of the executable**: the 8 bytes at `G` for every GOT pair (`adrGotPage`
relocation) of a function of the program whose words in the file are `adrp`/`ldr` of the slot
`G` (aligned, page in range, `rd < 31`: the form of `PairOk.adrpLdr`). -/
def GotSlot (I : LinkInput) (file : ByteArray) (a : BitVec 64) : Prop :=
  ∃ e ∈ tabOf I.results, ∃ rl ∈ e.2.fb.relocs, rl.type = .adrGotPage ∧ ∃ rd G, rd < 31 ∧
    G % 8 = 0 ∧ inR (-2 ^ 20) (2 ^ 20) (BinCheck.pageOf G - BinCheck.pageOf (wAt e.2 rl.offset).toNat) = true ∧
    fileWord file (wAt e.2 rl.offset) =
      some (adrpW rd (BinCheck.pageOf G - BinCheck.pageOf (wAt e.2 rl.offset).toNat)) ∧
    fileWord file (wAt e.2 (rl.offset + 4)) = some (ldrW rd rd (G % 4096 / 8)) ∧
    ∃ i < 8, a = BitVec.ofNat 64 G + BitVec.ofNat 64 i

/-- **The GOT slots are kept, loaded, unrelocated bytes of the file.** -/
def GotOk (I : LinkInput) (file : ByteArray) : Prop :=
  ∀ a, GotSlot I file a →
    (Elf.ro file a ∨ Elf.relro file a) ∧ (Elf.loadMem file a).isSome = true ∧ ¬ RelocAt I a

/-- `a` is a byte of a relocated word of the images `T`. -/
def relocAtB (T : List (Clif.Function × Art)) (a : BitVec 64) : Bool :=
  T.any fun e => e.2.fb.relocs.any fun r => (List.range 4).any fun i => a == wAt e.2 (r.offset + i)

theorem not_relocAt_of {a : BitVec 64} (h : relocAtB (tabOf I.results) a = false) :
    ¬ RelocAt I a := by
  rintro ⟨e, he, r, hr, i, hi, rfl⟩
  have : relocAtB (tabOf I.results) (wAt e.2 (r.offset + i)) = true := by
    simp only [relocAtB, List.any_eq_true, List.mem_range, beq_iff_eq]
    exact ⟨e, he, r, hr, i, hi, rfl⟩
  rw [this] at h; cases h

/-- **The GOT check** on an excerpt of the file: for every GOT pair of every function, the 8
bytes of the slot its words address (`gotOf`) are loaded, `ro` or `relro`, and no relocated
instruction byte. -/
def gotB (I : LinkInput) (ex : Excerpt) : Bool :=
  match phdrs (exRd ex) with
  | some phs =>
    let m := memIn (exRd ex) phs
    (tabOf I.results).all fun e => e.2.fb.relocs.all fun rl =>
      !decide (rl.type = .adrGotPage) ||
      match readN m 4 (wAt e.2 rl.offset), readN m 4 (wAt e.2 (rl.offset + 4)) with
      | some x0, some x1 =>
        (List.range 8).all fun i =>
          let a := BitVec.ofNat 64 (BinCheck.gotOf (wAt e.2 rl.offset).toNat x0 x1) + BitVec.ofNat 64 i
          (roB phs a || relroB phs a) && (m a).isSome && !relocAtB (tabOf I.results) a
      | _, _ => false
  | none => false

private theorem ldr_imm {k rd : Nat} (hk : k < 512) (hrd : rd < 32) :
    (0xf9400000 + k * 1024 + rd * 32 + rd) / 1024 % 4096 = k := by
  have e : 0xf9400000 + k * 1024 + rd * 32 + rd = rd * 33 + (4083712 + k) * 1024 := by omega
  rw [e, Nat.add_mul_div_right _ _ (by decide), Nat.div_eq_of_lt (by omega)]
  omega

private theorem adrp_imm {q rd : Nat} (hq : q < 2 ^ 21) (hrd : rd < 32) :
    (1 * 2 ^ 31 + q % 4 * 2 ^ 29 + 0x10000000 + q / 4 * 32 + rd) / 32 % 2 ^ 19 * 4 +
      (1 * 2 ^ 31 + q % 4 * 2 ^ 29 + 0x10000000 + q / 4 * 32 + rd) / 2 ^ 29 % 4 = q := by
  have hu : q % 4 < 4 := Nat.mod_lt _ (by decide)
  have hv : q / 4 < 524288 := by omega
  have hq' : q = q / 4 * 4 + q % 4 := by omega
  generalize q % 4 = u at *
  generalize q / 4 = v at *
  subst hq'
  simp only [Nat.reducePow, Nat.one_mul]
  omega

/-- The slot of a checked `adrp`/`ldr` pair is the one its words decode to. -/
theorem gotOf_pair {P G rd : Nat} (hrd : rd < 32) (h8 : G % 8 = 0)
    (hin : inR (-2 ^ 20) (2 ^ 20) (BinCheck.pageOf G - BinCheck.pageOf P) = true) :
    BinCheck.gotOf P (adrpW rd (BinCheck.pageOf G - BinCheck.pageOf P)) (ldrW rd rd (G % 4096 / 8)) = G := by
  simp only [inR, Bool.and_eq_true, decide_eq_true_eq] at hin
  simp only [BinCheck.gotOf, adrpW, adrLike, ldrW, imm21, BinCheck.pageOf, BitVec.toNat_ofNat] at hin ⊢
  generalize hd : ((G / 4096 : Nat) : Int) - ((P / 4096 : Nat) : Int) = d at hin ⊢
  generalize hq : (d % 2 ^ 21).toNat = q
  have hq1 : q < 2 ^ 21 := by omega
  have hk : G % 4096 / 8 < 512 := by omega
  rw [Nat.mod_eq_of_lt (by omega : 1 * 2 ^ 31 + q % 4 * 2 ^ 29 + 0x10000000 + q / 4 * 32 + rd < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega : 0xf9400000 + G % 4096 / 8 * 1024 + rd * 32 + rd < 2 ^ 32)]
  have e1 : (1 * 2 ^ 31 + q % 4 * 2 ^ 29 + 0x10000000 + q / 4 * 32 + rd) / 32 % 2 ^ 19 * 4 +
      (1 * 2 ^ 31 + q % 4 * 2 ^ 29 + 0x10000000 + q / 4 * 32 + rd) / 2 ^ 29 % 4 = q :=
    adrp_imm hq1 hrd
  have e2 : (0xf9400000 + G % 4096 / 8 * 1024 + rd * 32 + rd) / 1024 % 4096 * 8 = G % 4096 := by
    rw [ldr_imm hk hrd]; omega
  rw [e1, e2]
  have hs : (if q < 2 ^ 20 then (q : Int) else (q : Int) - 2 ^ 21) = d := by
    split <;> omega
  rw [hs]
  omega

theorem gotB_sound {ex : Excerpt} (h : gotB I ex = true) (hA : Agrees file ex) : GotOk I file := by
  unfold gotB at h
  split at h
  · rename_i phs hp
    have hm := memIn_ext hA hp
    rintro a ⟨e, he, rl, hrl, ht, rd, G, hrd, h8, hin, hw0, hw1, i, hi, rfl⟩
    have h1 := List.all_eq_true.1 (List.all_eq_true.1 h e he) rl hrl
    simp only [ht, decide_true, Bool.not_true, Bool.false_or] at h1
    split at h1
    · rename_i x0 x1 e0 e1
      have e0' : x0 = adrpW rd (BinCheck.pageOf G - BinCheck.pageOf (wAt e.2 rl.offset).toNat) := by
        have := readN_ext hm e0
        rw [show readN (loadMem file) 4 (wAt e.2 rl.offset) = fileWord file (wAt e.2 rl.offset)
          from rfl, hw0] at this
        cases this; rfl
      have e1' : x1 = ldrW rd rd (G % 4096 / 8) := by
        have := readN_ext hm e1
        rw [show readN (loadMem file) 4 (wAt e.2 (rl.offset + 4)) =
          fileWord file (wAt e.2 (rl.offset + 4)) from rfl, hw1] at this
        cases this; rfl
      subst e0' e1'
      have h2 := List.all_eq_true.1 h1 i (List.mem_range.2 hi)
      rw [gotOf_pair (rd := rd) (by omega) h8 hin] at h2
      simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h2
      obtain ⟨⟨hro, hsome⟩, hrel⟩ := h2
      refine ⟨?_, ?_, not_relocAt_of hrel⟩
      · rcases hro with hro | hro
        · exact .inl (roB_sound hA hp hro)
        · exact .inr (relroB_sound hA hp hro)
      · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hsome
        simp [hm _ _ hb]
    · cases h1
  · cases h

/-! ## The outside caller and the slots -/

/-- **The slots are outside the caller's stack and CLIF memory**: what the outside caller of
`OutsideCall` (stack `N`) guarantees about the addresses `S` besides the code: none is in the free
stack, in a stack argument, or in a live CLIF allocation. -/
structure OutsideAvoids (S : BitVec 64 → Prop) (f : Clif.Function) (N : Nat) (r : Arm.ArmState)
    (args : List Clif.Val) (cm : Clif.Mem) : Prop where
  stack : ∀ a, S a → ¬ StackBelow N (spv r) a
  args : ∀ off v, (ArgLoc.stack off, v) ∈ (locsOf f.sig).zip args →
    Avoids S v.ty.bytes (spv r + BitVec.ofNat 64 off)
  valid : ∀ a n, cm.valid a n = true → ∀ k < n, ¬ S (BitVec.ofNat 64 (a + k))

/-- `worldF` with the code image extended by `S`. -/
def worldFS (I : LinkInput) (f : Clif.Function) (K : Nat) (r : Arm.ArmState)
    (S : BitVec 64 → Prop) : BitVec 64 → Prop :=
  frameWG K (RAFrame.compute (art I f).vcp (art I f).rf).intBase
    (RAFrame.compute (art I f).vcp (art I f).rf).size (art I f).af (fun a => img I a ∨ S a)
    (modelOf I f r)

theorem not_worldFS {f : Clif.Function} {K : Nat} {r : Arm.ArmState} {S : BitVec 64 → Prop}
    {a : BitVec 64} (h1 : ¬ worldF I f K r a) (h2 : ¬ S a) : ¬ worldFS I f K r S a := by
  rintro (h | h | h)
  · exact h1 (.inl h)
  · exact h1 (.inr h)
  · exact h2 h

/-- The proof's linked system of an outside call of `f` in `r` with the slots `S` kept. -/
noncomputable def sysS (I : LinkInput) (B : BaseEnv) (f : Clif.Function) (r : Arm.ArmState)
    (S : BitVec 64 → Prop) : LinkSys :=
  (LinkSys.ofInput I B (worldF I f (StackBound.bud I f) r)).extImg
    (worldFS I f (StackBound.bud I f) r S) S (modelOf I f r).mem

theorem mach_sysS (f : Clif.Function) (r : Arm.ArmState) (S : BitVec 64 → Prop) (M : Nat)
    (g : Clif.Function) : (sysS I B f r S).mach M g = (sys I B).mach M g := by
  rw [sysS, LinkSys.mach_extImg, mach_F]

/-- **`RunGoodL` of the system keeping the slots**, for a returning or trapping outcome. -/
theorem runGood_sysS {D : List Clif.DataObject} (hI : okB I = true) (hbin : BinOk I D file)
    (hB : BaseOk (sys I B)) {n : String} (hn : StackBound.goodN I n = true) {f : Clif.Function}
    (hf : (prog I).func? n = some f) (M : Nat) {r : Arm.ArmState} {args : List Clif.Val}
    {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (StackBound.stackFn I f) r args cs.mem)
    {S : BitVec 64 → Prop} (hav : OutsideAvoids S f (StackBound.stackFn I f) r args cs.mem)
    (hr : ClifRun I B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) ((prog I).only f) cs)
    (hout : (∃ vals cm, Clif.runLoop B.env (prog I) (M + 1) cs = .returned vals cm) ∨
      (∃ c, Clif.runLoop B.env (prog I) (M + 1) cs = .trapped c)) :
    (sysS I B f r S).RunGoodL M f (modelOf I f r) := by
  have hB' : BaseOk (LinkSys.ofInput I B (worldF I f (StackBound.bud I f) r)) := baseOk_F hB
  have himgF : ∀ a, (LinkSys.ofInput I B (worldF I f (StackBound.bud I f) r)).Img a →
      worldF I f (StackBound.bud I f) r a := fun _ h => .inr h
  have hL0 := okB_sound hI hB' himgF
  have hfm := (Clif.Program.func?_some hf).1
  have hfacts := binFacts_of_checks hI hbin
  have hro : ∀ a b, BinCheck.roByte I D a = some b → r.mem a = b := fun a b h =>
    hX a b (hfacts.data a b h).1 (hfacts.data a b h).2
  obtain ⟨hent, -, hgfree, -, hbe, hargs, hsav, hrel, hpl⟩ := premises hL0 hfm hro ho hr
  have hL : (sysS I B f r S).Ok := LinkSys.Ok.extImg hL0
    (fun a ha => mem_modelOf_img ha) fun a ha => by
      rcases ha with ha | ha
      · exact .inr (.inl ha)
      · exact .inr (.inr ha)
  have hf' : (progOf I.results).func? n = some f := hf
  have hn' := hn
  unfold StackBound.goodN at hn'
  rw [hf'] at hn'
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hn'
  have hbud : StackBound.bud I f = b := by simp [StackBound.bud, hb]
  obtain ⟨hd, hsb, hib, hsz⟩ := frame_facts hL0 hfm
  have hN := ho.stack
  have hN' : frameDrop (art I f).af + StackBound.bud I f ≤ (spv r).toNat := hN
  have hsp := (spv r).isLt
  have hspbN : (spBody (art I f).af r).toNat = (spv r).toNat - frameDrop (art I f).af :=
    (off_toNat 0 (spv r) _ (by omega)).2.2
  have hspb : spv (bodyOf (art I f).af (modelOf I f r)) = spBody (art I f).af r := by
    rw [spv_bodyOf, spv_modelOf]; rfl
  refine (backend_correct_program_stackX (sysS I B f r S) hL
    ((StackBound.budget_of hI B (worldF I f (StackBound.bud I f) r)).extImg _ _ _)
    (StackBound.bud I f) (fun M => by simp [LinkSys.hybrid, hb, hbud]) hfm M hent
    (by rw [spv_modelOf]; exact hN) (fun a ha => ?_) rfl (fun a _ => rfl) hbe hargs hr.entry
    (fun off v hm k hk hx => ?_) ⟨⟨hrel.1.bytes, fun a n hv => ?_, hrel.1.symbols⟩, hrel.2.1,
      hrel.2.2.1, fun j hj => ?_, hrel.2.2.2.2⟩ hpl htr).2 hout
  · rcases ha with ha | ha
    · exact hgfree a ha
    · rw [spv_modelOf]; exact hav.stack a ha
  · rcases hx with hx | hx
    · exact hsav off v hm k hk hx
    · rw [spv_modelOf] at hx; exact hav.args off v hm k hk hx
  · obtain ⟨hfit, hk⟩ := hrel.1.valid a n hv
    exact ⟨hfit, fun k hkn => not_worldFS (hk k hkn) (hav.valid a n hv k hkn)⟩
  · refine not_worldFS (hrel.2.2.2.1 j hj) fun hS => hav.stack _ hS ?_
    change j < (RAFrame.compute (art I f).vcp (art I f).rf).intBase at hj
    rw [hspb]
    show StackBelow (frameDrop (art I f).af + StackBound.bud I f) _ _
    simp only [StackBelow, BitVec.toNat_add, BitVec.toNat_ofNat, hspbN]
    rw [Nat.mod_eq_of_lt (by omega : j < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
    omega

/-! ## D4 at a state of the run -/

/-- **D4 from the per-state facts** of the system keeping the GOT slots: at the `ldr` of a GOT
pair, the slot's bytes are the activation's entry bytes (`RL.GoodX.got`, the slots kept), which
are the model state's, which are the file's (`GotOk`, `img_bytes`, `Image.Intact`). -/
theorem got_of_good {D : List Clif.DataObject} (hI : okB I = true) (hbin : BinOk I D file)
    (hgot : GotOk I file) {f : Clif.Function} {r : Arm.ArmState} (hX : (imageOf file).Intact r)
    {g : Clif.Function} (hg : g ∈ (prog I).funcs) (hFg : FnOk I file g) {M : Nat}
    {c t : Arm.ArmState} (hgood : (sysS I B f r (GotSlot I file)).GoodAt M g c t) :
    ∀ rl ∈ (art I g).fb.relocs, rl.type = .adrGotPage →
    Arm.r .PC t = wAt (art I g) (rl.offset + 4) → ∀ (rd G : Nat), rd < 31 → G % 8 = 0 →
    inR (-2 ^ 20) (2 ^ 20) (BinCheck.pageOf G - BinCheck.pageOf (wAt (art I g) rl.offset).toNat) = true →
    fileWord file (wAt (art I g) rl.offset) =
      some (adrpW rd (BinCheck.pageOf G - BinCheck.pageOf (wAt (art I g) rl.offset).toNat)) →
    fileWord file (wAt (art I g) (rl.offset + 4)) = some (ldrW rd rd (G % 4096 / 8)) → ∀ i < 8,
    ¬ RelocAt I (BitVec.ofNat 64 G + BitVec.ofNat 64 i) ∧
    t.mem (BitVec.ofNat 64 G + BitVec.ofNat 64 i) =
      (Elf.loadMem file (BitVec.ofNat 64 G + BitVec.ofNat 64 i)).getD 0 := by
  intro rl hrl ht hpc rd G hrd h8 hin hw0 hw1 i hi
  obtain ⟨X, K, G', gv, -, hG, himgG, himgS, -⟩ := hgood
  unfold actGoodX at hG
  have hS : GotSlot I file (BitVec.ofNat 64 G + BitVec.ofNat 64 i) :=
    ⟨_, tab_mem (okB_names hI) hg, rl, hrl, ht, rd, G, hrd, h8, hin, hw0, hw1, i, hi, rfl⟩
  obtain ⟨hkept, hsome, hnr⟩ := hgot _ hS
  refine ⟨hnr, ?_⟩
  -- the `ldr` line
  obtain ⟨-, -, r', hr', hr'o, hr't⟩ := pair_facts hFg hrl (.inl ht)
  obtain ⟨j2, i2, t2, hj2, hi2, ho2⟩ := (FnAsm.layout_relocs hFg.layout r').1 hr'
  obtain ⟨a1, b1, c1, rfl⟩ : ∃ a b c, i2 = .ldrGotLo12 a b c := by
    rw [hr't, ht] at hi2
    cases i2 <;> simp [Insn.reloc?, loOf] at hi2
    exact ⟨_, _, _, rfl⟩
  have hat := hG.got a1 b1 c1 ⟨j2, t2, hj2, by
    rw [hpc, ← hr'o, ← ho2]; rfl⟩ _ (himgG _ (.inr hS))
  rw [hat, himgS _ (.inr hS)]
  show (modelOf I f r).mem _ = _
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hsome
  rw [hb, Option.getD_some]
  by_cases hii : img I (BitVec.ofNat 64 G + BitVec.ofNat 64 i)
  · rw [mem_modelOf_img hii]
    rcases (BinCheck.img_bytes hbin hI hii).2 with h | h
    · rw [hb] at h; cases h; rfl
    · exact absurd h hnr
  · rw [mem_modelOf_not hii]
    exact hX _ _ hkept hb

/-! ## The binary theorem with D2 only -/

/-- **The memory-read fact D2 of a model state** (`StepOkR.insn`). -/
def StepOkI (I : LinkInput) (file : ByteArray) (g : Clif.Function) (m : Arm.ArmState) : Prop :=
  ∀ i, insnAt (art I g).fa (art I g).base (Arm.r .PC m) = some i → i.hooked = false →
    ∀ a, (fileWord file (Arm.r .PC m)).bind Arm.decode_raw_inst = some a →
    ∀ e, Sim I m e → Sim I (Arm.exec_inst a m) (Arm.exec_inst a e)

/-- **The D2 hypothesis**: `StepOkI` at the states of `ReachN` whose step ends without error. -/
def RunInsnN (I : LinkInput) (B : BaseEnv) (file : ByteArray) (M : Nat) (f : Clif.Function)
    (c : Arm.ArmState) : Prop :=
  ∀ M' g t, ReachN I B M f c M' g t → Arm.r .ERR ((sys I B).mach M' g t) = .None →
    StepOkI I file g t

/-- **`binary_correct_exec_of_reads` with D4 discharged**: under the premises of
`binary_correct_of_checks_acyclic`, the outside-code contract `HooksSim`, the code map check
`codeMapB`, the GOT check's fact `GotOk` (`gotB_sound`), the outside caller keeping the GOT slots
off its stack and CLIF memory (`OutsideAvoids`), and only the memory-read fact D2 (`RunInsnN`)
of the model's run, the executable machine run from `r` refines the whole-program CLIF run. -/
theorem binary_correct_exec_of_insn {I : LinkInput} {D : List Clif.DataObject}
    {file : ByteArray} (hI : okB I = true) (hcm : codeMapB I (tabOf I.results) = true)
    (hbin : BinCheck.BinOk I D file) (hgot : GotOk I file) (B : BaseEnv) (hB : BaseOk (sys I B))
    (hH : HooksSim I B) {n : String} {f : Clif.Function} (hf : (prog I).func? n = some f)
    (hc : ¬ StackBound.CycleFrom (StackBound.Calls I I.results) f) (M : Nat) {r : Arm.ArmState}
    {args : List Clif.Val} {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (StackBound.stackFn I f) r args cs.mem)
    (hav : OutsideAvoids (GotSlot I file) f (StackBound.stackFn I f) r args cs.mem)
    (hr : ClifRun I B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) ((prog I).only f) cs)
    (hins : RunInsnN I B file M f (modelOf I f r)) :
    ExecRefines (art I f).fb (art I f).base (xreg 30 r) (step I B file) r (RelocAt I)
      (Clif.runLoop B.env (prog I) (M + 1) cs) := by
  have hn := (StackBound.goodN_iff hI).2 ⟨f, hf, hc⟩
  by_cases hout : (∃ vals cm, Clif.runLoop B.env (prog I) (M + 1) cs = .returned vals cm) ∨
      (∃ c, Clif.runLoop B.env (prog I) (M + 1) cs = .trapped c)
  · obtain ⟨-, -, hG⟩ := binary_correct_of_checksX hI hbin B hB hn hf M hX ho hr htr
    have hgS := runGood_sysS hI hbin hB hn hf M hX ho hav hr htr hout
    have hfm := (Clif.Program.func?_some hf).1
    have hL' := okB_sound hI (baseOk_F (F' := img I) hB) fun _ h => h
    have hF : ∀ g ∈ (prog I).funcs, FnOk I file g := fun g hg => fnOk hI hbin hL' hg
    have hent : ∀ k < (art I f).fb.words.size,
        xreg 30 (modelOf I f r) ≠ (art I f).base + BitVec.ofNat 64 (4 * k) := by
      have hB'' : BaseOk (LinkSys.ofInput I B (worldF I f (StackBound.bud I f) r)) := baseOk_F hB
      have hL0 := okB_sound hI hB'' fun _ h => .inr h
      have hfacts := binFacts_of_checks hI hbin
      have hro : ∀ a b, BinCheck.roByte I D a = some b → r.mem a = b := fun a b h =>
        hX a b (hfacts.data a b h).1 (hfacts.data a b h).2
      obtain ⟨he, -⟩ := premises hL0 hfm hro ho hr
      simp only [xreg, r_modelOf]; exact he.raOutside
    refine binary_correct_exec_of_reads hI hcm hbin B hB hH hf hc M hX ho hr htr
      fun M' g t hR he => ⟨hins M' g t hR he, ?_⟩
    obtain ⟨c', hRL, -⟩ := reachL_of_reachN hI hcm hF hR hfm (hG hout)
      (raNotSecond_top (hF f hfm) hent)
    have hRL' : (sysS I B f r (GotSlot I file)).ReachL M f (modelOf I f r) M' g c' t := by
      exact LinkSys.reachL_extImg (F := worldFS I f (StackBound.bud I f) r (GotSlot I file))
        (S := GotSlot I file) (m := (modelOf I f r).mem)
        (Binary.reachL_F (F := worldF I f (StackBound.bud I f) r) (F' := fun _ => False) hRL)
    have hg := reachN_mem hR hfm
    exact got_of_good hI hbin hgot hX hg (hF g hg)
      (hgS _ _ _ _ hRL' (by rw [mach_sysS]; exact he))
  · cases h : Clif.runLoop B.env (prog I) (M + 1) cs with
    | returned vals cm => exact absurd (.inl ⟨vals, cm, h⟩) hout
    | trapped c => exact absurd (.inr ⟨c, h⟩) hout
    | stuck _ => trivial
    | outOfFuel => trivial

end ExecBytes

end E2E
