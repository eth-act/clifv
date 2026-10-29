import FV.E2E.ExecGoodReads
import FV.E2E.ExecGoodRunT
import FV.E2E.BinCheckT
import FV.E2E.BinaryGoodT
import FV.E2E.BinaryT
import FV.E2E.ExecBytesT
import FV.E2E.ExecRunNT
import FV.E2E.ExecStaticT
import FV.E2E.LinkArmT
import FV.E2E.LinkCheckT
import FV.E2E.LinkGoodT
import FV.E2E.StackBoundT

/-! # Typed copies of `FV.E2E.ExecGoodReads` (S11e5 Stage C, slice 8)

The declarations of `FV.E2E.ExecGoodReads` that depend on the integer link contract
(`LinkSys.Ok`, `LinkSys.Thm`, `okB`, `ArmRefines`), for the typed contract `LinkSys.OkT`
(suffix `T`; `LinkSys.Ok.*` as `LinkSys.OkT.*`). -/

namespace E2E.ExecBytes
open Backend Backend.Proof E2E.LinkCheck E2E.Binary E2E.BinCheck
variable {I : LinkInput} {B : BaseEnv} {file : ByteArray}

/-- **A relocated byte is a code byte of the image.** -/
theorem relocAt_imgT (hI : okBT I = true) (hF : ∀ g ∈ (prog I).funcs, FnOk I file g)
    {a : BitVec 64} (h : RelocAt I a) : ImgT (tabOf I.results) a := by
  obtain ⟨g, hg, rl, hrl, i, hi, rfl⟩ := relocAt_invT hI h
  obtain ⟨j, x, t, hj, -, ho⟩ := (FnAsm.layout_relocs (hF g hg).layout rl).1 hrl
  obtain ⟨lm, hm⟩ := FnAsm.layout_labelOffsets (hF g hg).layout
  obtain ⟨h4, w, -, hk⟩ := FnAsm.layout_word (hF g hg).layout hm hj rfl
  have hl := line_lt (hF g hg) hj
  have hfit := (hF g hg).fits
  refine ⟨(g, art I g), tab_mem (okB_namesT hI) hg,
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
theorem word_staticT (hI : okBT I = true) (hc : codeMapB I (tabOf I.results) = true)
    (hF : ∀ g ∈ (prog I).funcs, FnOk I file g) {g : Clif.Function} (hg : g ∈ (prog I).funcs)
    {j : Nat} {tg bs : Lbl} (hj : (art I g).fa.lines.toList[j]? = some (.word tg bs)) :
    ∀ k < 4, ¬ RelocAt I (wAt (art I g) (lineOffset (art I g).fa.lines.toList j) +
      BitVec.ofNat 64 k) := by
  intro k hk hR
  obtain ⟨h, hh, rl, hrl, i', hi', he⟩ := relocAt_invT hI hR
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
  have hal := line_overlapT hI hc hF hg hh hj hj' rfl rfl hk hi' (by rw [ho]; omega)
  simp [lineAlikeB] at hal

/-- **The bytes of a literal-pool word of a function are no relocated bytes** (#565;
`word_staticT` for a `.data` line). -/
theorem data_staticT (hI : okBT I = true) (hc : codeMapB I (tabOf I.results) = true)
    (hF : ∀ g ∈ (prog I).funcs, FnOk I file g) {g : Clif.Function} (hg : g ∈ (prog I).funcs)
    {j d : Nat} (hj : (art I g).fa.lines.toList[j]? = some (.data d)) :
    ∀ k < 4, ¬ RelocAt I (wAt (art I g) (lineOffset (art I g).fa.lines.toList j) +
      BitVec.ofNat 64 k) := by
  intro k hk hR
  obtain ⟨h, hh, rl, hrl, i', hi', he⟩ := relocAt_invT hI hR
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
  have hal := line_overlapT hI hc hF hg hh hj hj' rfl rfl hk hi' (by rw [ho]; omega)
  simp [lineAlikeB] at hal

/-- **`StepOkR.insn` (D2) from the per-state facts**: the reads of the decoded word at the pc
avoid the relocated bytes. -/
theorem insn_of_goodT (hI : okBT I = true) (hc : codeMapB I (tabOf I.results) = true)
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
  have hrd := hrdA j x tt hj hpcw hh a
    (by simpa [RL.envL, RL.L, hm, Except.toOption] using ha') p hp k hk
  rcases hrd with hnG | ⟨j', tg, bs, hj', q, hq, he⟩ | ⟨j', d, hj', q, hq, he⟩
  · exact hnG (himg _ (relocAt_imgT hI hF hR))
  · rw [he] at hR
    exact word_staticT hI hc hF hg hj' q hq hR
  · rw [he] at hR
    exact data_staticT hI hc hF hg hj' q hq hR
end E2E.ExecBytes
