import FV.E2E.ExecGoodRun
import FV.E2E.ExecFrameSim

/-! # D2 of `StepOkR` from the register-level per-state facts (L3 (c))

`RL.GoodX.reads` (every state of the model's run): the memory reads (`MemReads`) of the unhooked
instruction at the pc are outside the activation's kept addresses `G`, or bytes of one of its
jump-table words. At the link level the code image is in `G` (`GoodAt`'s last conjunct, from
`MachEntry.imgG`) and every relocated byte is a code byte (`relocAt_img`) of an instruction line
(`FnAsm.layout_relocs`), never of a jump-table word (`word_static`); the word at an unhooked
instruction line outside the TLS tail is the compiled one (`fileWord_plain`), which decodes to
the instruction's `toArmInst`. So the reads of the decoded word avoid `RelocAt I`, and
`exec_sim` gives `StepOkR.insn` (`insn_of_good`).

`binary_correct_exec_of_got`: `binary_correct_exec_of_reads` with only the GOT fact (D4,
`RunGotN`) as hypothesis.
-/

namespace E2E.ExecBytes

open Backend Backend.Proof E2E.LinkCheck E2E.Binary E2E.BinCheck

variable {I : LinkInput} {B : BaseEnv} {file : ByteArray}

/-- Lines of size 4 at the same offset are the same line. -/
theorem lineOffset_inj4 {L : List Line} {j j' : Nat} {ln ln' : Line} (hj : L[j]? = some ln)
    (hj' : L[j']? = some ln') (hs : ln.size = 4) (hs' : ln'.size = 4)
    (he : lineOffset L j = lineOffset L j') : j = j' := by
  rcases Nat.lt_trichotomy j j' with h | h | h
  · have h1 := lineOffset_succ L j _ hj
    have h2 := lineOffset_mono L (show j + 1 ≤ j' by omega)
    omega
  · exact h
  · have h1 := lineOffset_succ L j' _ hj'
    have h2 := lineOffset_mono L (show j' + 1 ≤ j by omega)
    omega

/-- **A relocated byte is a code byte of the image.** -/
theorem relocAt_img (hI : okB I = true) (hF : ∀ g ∈ (prog I).funcs, FnOk I file g)
    {a : BitVec 64} (h : RelocAt I a) : ImgT (tabOf I.results) a := by
  obtain ⟨g, hg, rl, hrl, i, hi, rfl⟩ := relocAt_inv hI h
  obtain ⟨j, x, t, hj, -, ho⟩ := (FnAsm.layout_relocs (hF g hg).layout rl).1 hrl
  obtain ⟨lm, hm⟩ := FnAsm.layout_labelOffsets (hF g hg).layout
  obtain ⟨h4, w, -, hk⟩ := FnAsm.layout_word (hF g hg).layout hm hj rfl
  have hl := line_lt (hF g hg) hj
  have hfit := (hF g hg).fits
  refine ⟨(g, art I g), tab_mem (okB_names hI) hg,
    ((art I g).base + BitVec.ofNat 64 (4 * (0 + lineOffset (art I g).fa.lines.toList j / 4)), w),
    ?_, ?_⟩
  · have := wordsAt_mem (base := (art I g).base) (k := 0) (ws := (art I g).fb.words.toList)
      (j := lineOffset (art I g).fa.lines.toList j / 4) (w := w) (by simpa using hk)
    simpa [FnBin.program] using this
  show ((wAt (art I g) (rl.offset + i)) - _).toNat < 4
  simp only [wAt, ← ho]
  rw [Nat.zero_add, Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h4), BitVec.ofNat_add,
    ← BitVec.add_assoc, BitVec.add_comm _ (BitVec.ofNat 64 i), BitVec.add_sub_cancel]
  simp only [BitVec.toNat_ofNat]
  omega

/-- **The bytes of a jump-table word of a function are no relocated bytes** (relocations are
at instruction lines, and code ranges are disjoint). -/
theorem word_static (hI : okB I = true) (hc : codeMapB I (tabOf I.results) = true)
    (hF : ∀ g ∈ (prog I).funcs, FnOk I file g) {g : Clif.Function} (hg : g ∈ (prog I).funcs)
    {j : Nat} {tg bs : Lbl} (hj : (art I g).fa.lines.toList[j]? = some (.word tg bs)) :
    ∀ k < 4, ¬ RelocAt I (wAt (art I g) (lineOffset (art I g).fa.lines.toList j) +
      BitVec.ofNat 64 k) := by
  intro k hk hR
  obtain ⟨h, hh, rl, hrl, i', hi', he⟩ := relocAt_inv hI hR
  obtain ⟨j', i2, t2, hj', -, ho⟩ := (FnAsm.layout_relocs (hF h hh).layout rl).1 hrl
  have hl' := line_lt (hF h hh) hj'
  have hfit := (hF h hh).fits
  have hfit' := (hF g hg).fits
  have hlw : lineOffset (art I g).fa.lines.toList j + 4 ≤ 4 * (art I g).fb.words.size := by
    have h1 := lineOffset_succ _ j _ hj
    have h2 := lineOffset_le_size (art I g).fa.lines.toList (j + 1)
    rw [layout_sum (hF g hg).layout] at h2
    simp only [Line.size] at h1
    omega
  have he' := congrArg BitVec.toNat he
  rw [BitVec.toNat_add, wAt, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : k < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : lineOffset (art I g).fa.lines.toList j < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), wAt, BitVec.toNat_add,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : rl.offset + i' < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega)] at he'
  by_cases hn : h.name = g.name
  · have hart := art_of_name (I := I) hn
    rw [hart] at hj' he' ho hl'
    obtain ⟨lm, hm⟩ := FnAsm.layout_labelOffsets (hF g hg).layout
    have h4 := (FnAsm.layout_word (hF g hg).layout hm hj rfl).1
    have h4' := (FnAsm.layout_word (hF g hg).layout hm hj' rfl).1
    have := lineOffset_inj4 hj hj' rfl rfl (by omega)
    subst this
    rw [hj] at hj'
    cases hj'
  · have hd := (codeMap_sound hI hc hh).2 g hg hn
    simp only [art] at hl' he' hfit hfit' ho hd hlw
    omega

/-- **`StepOkR.insn` (D2) from the per-state facts**: the reads of the decoded word at the pc
avoid the relocated bytes. -/
theorem insn_of_good (hI : okB I = true) (hc : codeMapB I (tabOf I.results) = true)
    (hF : ∀ g ∈ (prog I).funcs, FnOk I file g) {M : Nat} {g : Clif.Function}
    (hg : g ∈ (prog I).funcs) {c t : Arm.ArmState} (hgood : (sys I B).GoodAt M g c t) :
    ∀ i, insnAt (art I g).fa (art I g).base (Arm.r .PC t) = some i → i.hooked = false →
      ∀ a, (fileWord file (Arm.r .PC t)).bind Arm.decode_raw_inst = some a →
      ∀ e, Sim I t e → Sim I (Arm.exec_inst a t) (Arm.exec_inst a e) := by
  obtain ⟨X, K, G, gv, -, hG, himg, -⟩ := hgood
  unfold actGoodX at hG
  have hFg := hF g hg
  obtain ⟨lm, hm⟩ := FnAsm.layout_labelOffsets hFg.layout
  intro i hi hh a ha e hsim
  refine exec_sim a hsim fun p hp k hk hR => ?_
  have hrdA := hG.reads
  obtain ⟨j, tt, hj, hpc⟩ := insnAt_spec hi
  -- the line at the pc is outside the TLS tail, so it carries no relocation
  obtain ⟨x, ⟨jx, tx, hjx, hpcx⟩, htl⟩ := hG.line
  have hxi : x = i := by
    have h1 := insnAt_of_line hFg hjx
    have h2 : wAt (art I g) (lineOffset (art I g).fa.lines.toList jx) = Arm.r .PC t := hpcx.symm
    rw [h2, hi] at h1
    exact (Option.some.inj h1).symm
  subst hxi
  have hr : x.reloc? = none := (Insn.reloc_of_tlsTail htl).resolve_right (by rw [hh]; decide)
  -- the file's word is the compiled one
  obtain ⟨w, hw, hfw⟩ := fileWord_plain hFg hm hj hr
  have hpcw : Arm.r .PC t = wAt (art I g) (lineOffset (art I g).fa.lines.toList j) := hpc.symm
  rw [hpcw, hfw, Option.bind_some] at ha
  obtain ⟨a', ha', hd⟩ := Insn.decode_encode hw
  rw [ha] at hd
  cases hd
  -- the register-level fact
  have hrd := hrdA j x tt hj hpcw hh _ a ha' p hp k hk
  rcases hrd with hnG | ⟨j', tg, bs, hj', q, hq, he⟩
  · exact hnG (himg _ (relocAt_img hI hF hR))
  · rw [he] at hR
    exact word_static hI hc hF hg hj' q hq hR

/-- **The GOT hypothesis** (D4 of `StepOkR`) at the states of `ReachN` whose step ends without
error. -/
def RunGotN (I : LinkInput) (B : BaseEnv) (file : ByteArray) (M : Nat) (f : Clif.Function)
    (c : Arm.ArmState) : Prop :=
  ∀ M' g t, ReachN I B M f c M' g t → Arm.r .ERR ((sys I B).mach M' g t) = .None →
    ∀ rl ∈ (art I g).fb.relocs, rl.type = .adrGotPage →
    Arm.r .PC t = wAt (art I g) (rl.offset + 4) → ∀ (rd G : Nat), rd < 31 → G % 8 = 0 →
    inR (-2 ^ 20) (2 ^ 20) (pageOf G - pageOf (wAt (art I g) rl.offset).toNat) = true →
    fileWord file (wAt (art I g) rl.offset) =
      some (adrpW rd (pageOf G - pageOf (wAt (art I g) rl.offset).toNat)) →
    fileWord file (wAt (art I g) (rl.offset + 4)) = some (ldrW rd rd (G % 4096 / 8)) → ∀ i < 8,
    ¬ RelocAt I (BitVec.ofNat 64 G + BitVec.ofNat 64 i) ∧
    t.mem (BitVec.ofNat 64 G + BitVec.ofNat 64 i) =
      (Elf.loadMem file (BitVec.ofNat 64 G + BitVec.ofNat 64 i)).getD 0

/-- **`RunReadsN` from the per-state facts and the GOT hypothesis.** -/
theorem runReadsN_of_good (hI : okB I = true) (hc : codeMapB I (tabOf I.results) = true)
    (hF : ∀ g ∈ (prog I).funcs, FnOk I file g) {M : Nat} {f : Clif.Function}
    (hf : f ∈ (prog I).funcs) {c : Arm.ArmState}
    (hra : ∀ k < (art I f).fb.words.size, xreg 30 c ≠ (art I f).base + BitVec.ofNat 64 (4 * k))
    (hgood : (sys I B).RunGoodL M f c) (hgot : RunGotN I B file M f c) :
    RunReadsN I B file M f c := fun M' g t hR he => by
  obtain ⟨c', hRL, -⟩ := reachL_of_reachN hI hc hF hR hf hgood (raNotSecond_top (hF f hf) hra)
  exact ⟨insn_of_good hI hc hF (reachN_mem hR hf) (hgood _ _ _ _ hRL he), hgot M' g t hR he⟩

/-- **`binary_correct_exec_static` with the per-state facts of the register-level proof and only
the GOT hypothesis**: under the premises of `binary_correct_of_checks_acyclic`, the outside-code
contract `HooksSim`, the code map check `codeMapB` and the GOT fact `RunGotN` (D4) of the model's
run, the executable machine run from `r` refines the whole-program CLIF run. -/
theorem binary_correct_exec_of_got {I : LinkInput} {D : List Clif.DataObject}
    {file : ByteArray} (hI : okB I = true) (hcm : codeMapB I (tabOf I.results) = true)
    (hbin : BinCheck.BinOk I D file) (B : BaseEnv) (hB : BaseOk (sys I B)) (hH : HooksSim I B)
    {n : String} {f : Clif.Function} (hf : (prog I).func? n = some f)
    (hc : ¬ StackBound.CycleFrom (StackBound.Calls I I.results) f) (M : Nat) {r : Arm.ArmState}
    {args : List Clif.Val} {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (StackBound.stackFn I f) r args cs.mem)
    (hr : ClifRun I B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) ((prog I).only f) cs)
    (hgot : RunGotN I B file M f (modelOf I f r)) :
    ExecRefines (art I f).fb (art I f).base (xreg 30 r) (step I B file) r (RelocAt I)
      (Clif.runLoop B.env (prog I) (M + 1) cs) := by
  have hn := (StackBound.goodN_iff hI).2 ⟨f, hf, hc⟩
  obtain ⟨-, -, hG⟩ := binary_correct_of_checksX hI hbin B hB hn hf M hX ho hr htr
  by_cases hout : (∃ vals cm, Clif.runLoop B.env (prog I) (M + 1) cs = .returned vals cm) ∨
      (∃ c, Clif.runLoop B.env (prog I) (M + 1) cs = .trapped c)
  · have hfm := (Clif.Program.func?_some hf).1
    have hB' : BaseOk (LinkSys.ofInput I B (worldF I f (StackBound.bud I f) r)) := baseOk_F hB
    have hL := okB_sound hI hB' fun _ h => .inr h
    have hfacts := binFacts_of_checks hI hbin
    have hro : ∀ a b, BinCheck.roByte I D a = some b → r.mem a = b := fun a b h =>
      hX a b (hfacts.data a b h).1 (hfacts.data a b h).2
    obtain ⟨hent, -⟩ := premises hL hfm hro ho hr
    have hL' := okB_sound hI (baseOk_F (F' := img I) hB) fun _ h => h
    have hF : ∀ g ∈ (prog I).funcs, FnOk I file g := fun g hg => fnOk hI hbin hL' hg
    have hra : ∀ k < (art I f).fb.words.size,
        xreg 30 (modelOf I f r) ≠ (art I f).base + BitVec.ofNat 64 (4 * k) := by
      simp only [xreg, r_modelOf]; exact hent.raOutside
    exact binary_correct_exec_staticN hI hcm hbin B hB hH hf hc M hX ho hr htr
      (runOkN_of_good hI hcm hF (fun g hg => destsInt_of_ok hL' hg) hfm hra (hG hout)
        (runReadsN_of_good hI hcm hF hfm hra (hG hout) hgot))
  · cases h : Clif.runLoop B.env (prog I) (M + 1) cs with
    | returned vals cm => exact absurd (.inl ⟨vals, cm, h⟩) hout
    | trapped c => exact absurd (.inr ⟨c, h⟩) hout
    | stuck _ => trivial
    | outOfFuel => trivial

end E2E.ExecBytes
