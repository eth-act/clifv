import FV.E2E.ReturnPinBinary
import FV.E2E.SemanticExecGoodReads

namespace E2E.ReturnPinExecBytes
open Backend Backend.Proof E2E.LinkCheck E2E.SemanticBinary E2E.BinCheck E2E.SemanticExecBytes
set_option autoImplicit false
set_option Elab.async false
variable {I : SemanticStackBound.CompilerInput} {B : BaseEnv} {file : ByteArray}

/-- The existing executable contract follows from the checked allocation and image. -/
theorem fnOk {D : List Clif.DataObject} (hI : ReturnPinStackBound.okB I = true)
    (hbin : BinOkWithResults I I.results D file)
    {F : BitVec 64 → Prop} (hL : (SemanticStackBound.ofInput I B F).OkSemanticReturnPins)
    {g : Clif.Function} (hg : g ∈ (prog I).funcs) : FnOk I file g := by
  obtain ⟨-, -, -, hla, hb⟩ := (ReturnPinStackBound.facts hI hg).pipe
  exact ⟨hla, hL.fits g hg, hbin.code _ (tab_mem (ReturnPinStackBound.okB_names hI) hg), hb⟩

theorem codeMap_sound {I : SemanticStackBound.CompilerInput} (hI : ReturnPinStackBound.okB I = true) (hc : codeMapB I (tabOf I.results) = true)
    {g : Clif.Function} (hg : g ∈ (prog I).funcs) :
    (I.symAddr g.name 0 = (art I g).base ∨ noBlrB I (tabOf I.results) g.name = true) ∧
    ∀ g' ∈ (prog I).funcs, g.name ≠ g'.name →
      ((art I g).base.toNat + 4 * (art I g).fb.words.size ≤ (art I g').base.toNat ∨
        (art I g').base.toNat + 4 * (art I g').fb.words.size ≤ (art I g).base.toNat) ∨
      ((art I g).base = (art I g').base ∧
        linesAlikeB (prog I) (art I g).fa.lines.toList (art I g').fa.lines.toList = true) := by
  simp only [codeMapB, progT_tabOf, List.all_eq_true, Bool.and_eq_true, beq_iff_eq,
    Bool.or_eq_true, decide_eq_true_eq] at hc
  have hn := ReturnPinStackBound.okB_names hI
  have hgt := hc _ (tab_mem hn hg)
  refine ⟨hgt.1, fun g' hg' hne => ?_⟩
  rcases hgt.2 _ (tab_mem hn hg') with (h | h) | h
  · exact absurd h hne
  · exact .inl h
  · exact .inr h


theorem relocAt_inv (hI : ReturnPinStackBound.okB I = true) {a : BitVec 64} (h : RelocAtWithResults I I.results a) :
    ∃ g ∈ (prog I).funcs, ∃ rl ∈ (art I g).fb.relocs, ∃ i < 4, a = wAt (art I g) (rl.offset + i) := by
  obtain ⟨e, he, rl, hrl, i, hi, rfl⟩ := h
  obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
  have hart : art I e0.1 = getOk e0.2 := by
    simp only [art, artOf, find_name (ReturnPinStackBound.okB_names hI) he0]
  exact ⟨e0.1, List.mem_map_of_mem he0, rl, by rw [hart]; exact hrl, i, hi, by rw [hart]⟩


theorem line_overlap (hI : ReturnPinStackBound.okB I = true) (hc : codeMapB I (tabOf I.results) = true)
    (hF : ∀ g ∈ (prog I).funcs, FnOk I file g) {g h : Clif.Function} (hg : g ∈ (prog I).funcs)
    (hh : h ∈ (prog I).funcs) {j j' : Nat} {l l' : Line}
    (hj : (art I g).fa.lines.toList[j]? = some l) (hj' : (art I h).fa.lines.toList[j']? = some l')
    (hl : l.isLabel = false) (hl' : l'.isLabel = false) {k k' : Nat} (hk : k < 4) (hk' : k' < 4)
    (he : (art I g).base.toNat + lineOffset (art I g).fa.lines.toList j + k =
      (art I h).base.toNat + lineOffset (art I h).fa.lines.toList j' + k') :
    lineAlikeB (prog I) l l' = true := by
  obtain ⟨hs, h4, hlt⟩ := line_word (hF g hg) hj hl
  obtain ⟨hs', h4', hlt'⟩ := line_word (hF h hh) hj' hl'
  by_cases hn : g.name = h.name
  · have hart := art_of_name (I := I) hn
    rw [← hart] at hj' he h4'
    obtain rfl := lineOffset_inj4 hj hj' hs hs' (by omega)
    rw [hj] at hj'; cases hj'
    exact lineAlikeB_refl _ _
  · rcases (codeMap_sound hI hc hg).2 h hh hn with hd | ⟨hb, ha⟩
    · exfalso
      have hfit := (hF g hg).fits
      have hfit' := (hF h hh).fits
      omega
    · rw [hb] at he
      have hoff := linesAlikeB_offset ha j
      obtain ⟨l'', hj'', hal⟩ := linesAlikeB_get ha hj
      have hs'' : l''.size = 4 := by rw [← lineAlikeB_size hal]; exact hs
      obtain rfl := lineOffset_inj4 hj'' hj' hs'' hs' (by omega)
      rw [hj''] at hj'; cases hj'
      exact hal


theorem relocAt_img (hI : ReturnPinStackBound.okB I = true) (hF : ∀ g ∈ (prog I).funcs, FnOk I file g)
    {a : BitVec 64} (h : RelocAtWithResults I I.results a) : ImgT (tabOf I.results) a := by
  obtain ⟨g, hg, rl, hrl, i, hi, rfl⟩ := relocAt_inv hI h
  obtain ⟨j, x, t, hj, -, ho⟩ := (FnAsm.layout_relocs (hF g hg).layout rl).1 hrl
  obtain ⟨lm, hm⟩ := FnAsm.layout_labelOffsets (hF g hg).layout
  obtain ⟨h4, w, -, hk⟩ := FnAsm.layout_word (hF g hg).layout hm hj rfl
  have hl := line_lt (hF g hg) hj
  have hfit := (hF g hg).fits
  refine ⟨(g, art I g), tab_mem (ReturnPinStackBound.okB_names hI) hg,
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


theorem word_static (hI : ReturnPinStackBound.okB I = true) (hc : codeMapB I (tabOf I.results) = true)
    (hF : ∀ g ∈ (prog I).funcs, FnOk I file g) {g : Clif.Function} (hg : g ∈ (prog I).funcs)
    {j : Nat} {tg bs : Lbl} (hj : (art I g).fa.lines.toList[j]? = some (.word tg bs)) :
    ∀ k < 4, ¬ RelocAtWithResults I I.results (wAt (art I g) (lineOffset (art I g).fa.lines.toList j) +
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
  have hal := line_overlap hI hc hF hg hh hj hj' rfl rfl hk hi' (by rw [ho]; omega)
  simp [lineAlikeB] at hal

/-- **The bytes of a literal-pool word of a function are no relocated bytes** (#565;
`word_static` for a `.data` line). -/
theorem data_static (hI : ReturnPinStackBound.okB I = true) (hc : codeMapB I (tabOf I.results) = true)
    (hF : ∀ g ∈ (prog I).funcs, FnOk I file g) {g : Clif.Function} (hg : g ∈ (prog I).funcs)
    {j d : Nat} (hj : (art I g).fa.lines.toList[j]? = some (.data d)) :
    ∀ k < 4, ¬ RelocAtWithResults I I.results (wAt (art I g) (lineOffset (art I g).fa.lines.toList j) +
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
  have hal := line_overlap hI hc hF hg hh hj hj' rfl rfl hk hi' (by rw [ho]; omega)
  simp [lineAlikeB] at hal


theorem insn_of_good (hI : ReturnPinStackBound.okB I = true) (hc : codeMapB I (tabOf I.results) = true)
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
    (by simpa [RL.envL, RL.L, show (sys I B).A g = art I g from rfl, hm, Except.toOption] using ha')
    p hp k hk
  rcases hrd with hnG | ⟨j', tg, bs, hj', q, hq, he⟩ | ⟨j', d, hj', q, hq, he⟩
  · exact hnG (himg _ (relocAt_img hI hF hR))
  · rw [he] at hR
    exact word_static hI hc hF hg hj' q hq hR
  · rw [he] at hR
    exact data_static hI hc hF hg hj' q hq hR


theorem symAddr_of_blrTo {I : SemanticStackBound.CompilerInput} {B : BaseEnv} (hI : ReturnPinStackBound.okB I = true)
    (hc : codeMapB I (tabOf I.results) = true) {g h : Clif.Function} (hg : g ∈ (prog I).funcs)
    (hh : h ∈ (prog I).funcs) {info : CallInfo} {t : Nat} (hs : (art I g).vcp.CallSite info)
    (hd : info.dest = .reg (.vreg t .int)) (hb : (sys I B).BlrTo g t h) :
    I.symAddr h.name 0 = (art I h).base := by
  refine ((codeMap_sound hI hc hh).1).resolve_right fun hn => ?_
  simp only [noBlrB, Bool.and_eq_true, Option.isNone_iff_eq_none, List.all_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', List.any_eq_false, beq_iff_eq] at hn
  obtain ⟨⟨hmay, -⟩, hgot⟩ := hb
  rcases hmay with hdecl | ⟨-, hsym, -⟩
  · rcases hn.2 _ (tab_mem (ReturnPinStackBound.okB_names hI) hg) with hx | hx
    · obtain ⟨x, hx', he⟩ := List.mem_map.1 hdecl
      exact hx x hx' he
    · obtain ⟨n', hv, hn'⟩ := blrGotB_sound hx hs hd
      exact hn' (hgot n' hv)
  · exact hsym hn.1


variable {I : SemanticStackBound.CompilerInput} {B : BaseEnv} {file : ByteArray}


theorem siteAt_static (hI : ReturnPinStackBound.okB I = true) (hc : codeMapB I (tabOf I.results) = true) (hF : ∀ g ∈ (prog I).funcs, FnOk I file g)
    {g : Clif.Function} (hg : g ∈ (prog I).funcs) {a : BitVec 64} {i : Insn}
    (hi : insnAt (art I g).fa (art I g).base a = some i) :
    siteAt I a = some (siteOf (prog I) i) := by
  unfold siteAt
  split
  · rename_i hex
    have hs := hex.choose_spec
    generalize hex.choose = g0 at hs ⊢
    obtain ⟨hg0, hsome⟩ := hs
    obtain ⟨i0, hi0⟩ := Option.isSome_iff_exists.mp hsome
    rw [hi0, Option.map_some]
    obtain ⟨j, t, hj, ha, -⟩ := insn_range (hF g hg) hi
    obtain ⟨j0, t0, hj0, ha0, -⟩ := insn_range (hF g0 hg0) hi0
    have hal := line_overlap hI hc hF hg0 hg hj0 hj rfl rfl (k := 0) (k' := 0) (by omega)
      (by omega) (by omega)
    simp only [lineAlikeB] at hal
    rw [insnAlikeB_site hal]
  · rename_i hne
    exact absurd ⟨g, hg, by rw [hi]; rfl⟩ hne


theorem plain_static (hI : ReturnPinStackBound.okB I = true) (hc : codeMapB I (tabOf I.results) = true) (hF : ∀ g ∈ (prog I).funcs, FnOk I file g)
    {g : Clif.Function} (hg : g ∈ (prog I).funcs) {a : BitVec 64} {i : Insn}
    (hi : insnAt (art I g).fa (art I g).base a = some i) (hr : i.reloc? = none) :
    ∀ k < 4, ¬ RelocAtWithResults I I.results (a + BitVec.ofNat 64 k) := by
  intro k hk hR
  obtain ⟨j, t, hj, ha, hl⟩ := insn_range (hF g hg) hi
  obtain ⟨h, hh, rl, hrl, i', hi', he⟩ := relocAt_inv hI hR
  obtain ⟨j', i2, t2, hj', hri, ho⟩ := (FnAsm.layout_relocs (hF h hh).layout rl).1 hrl
  have hl' := line_lt (hF h hh) hj'
  have hfit := (hF h hh).fits
  have hfit' := (hF g hg).fits
  have he' := congrArg BitVec.toNat he
  rw [BitVec.toNat_add, ha, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : k < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega), wAt, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : rl.offset + i' < 2 ^ 64), Nat.mod_eq_of_lt (by omega)] at he'
  have hal := line_overlap hI hc hF hg hh hj hj' rfl rfl hk hi' (by rw [ho]; omega)
  simp only [lineAlikeB] at hal
  rw [insnAlikeB_reloc hal hr] at hri
  cases hri


theorem stepOk_of_d (hI : ReturnPinStackBound.okB I = true) (hc : codeMapB I (tabOf I.results) = true) (hF : ∀ g ∈ (prog I).funcs, FnOk I file g)
    (hH : HooksSim I B) {M : Nat} {g : Clif.Function} (hg : g ∈ (prog I).funcs)
    {m : Arm.ArmState} (h : StepOkD I B file M g m) : StepOk I B file M g m where
  err := h.err
  program := h.program
  site := by
    obtain ⟨i, hi, hr⟩ := h.site
    exact ⟨i, hi, siteAt_static hI hc hF hg hi, hr⟩
  cf := h.cf
  insn := h.insn
  call d e _ hs := hH.call d m e hs
  tls tmp _ n e _ hs := hH.tls n tmp m e hs
  got := h.got
  blr := h.blr
  plain i hi hr := plain_static hI hc hF hg hi hr


theorem runOkSN_of_n (hI : ReturnPinStackBound.okB I = true) (hc : codeMapB I (tabOf I.results) = true)
    (hF : ∀ g ∈ (prog I).funcs, FnOk I file g) (hH : HooksSim I B) {M : Nat}
    {f : Clif.Function} (hf : f ∈ (prog I).funcs) {c : Arm.ArmState}
    (h : RunOkN I B file M f c) : RunOkSN I B file M f c :=
  fun M' g t hR he => stepOk_of_d hI hc hF hH (reachN_mem hR hf) (h M' g t hR he)


theorem pairsClosed_art (hI : ReturnPinStackBound.okB I = true) {g : Clif.Function} (hg : g ∈ (prog I).funcs) :
    PairsClosed (art I g).fa.lines.toList := by
  exact emitFunc_pairsClosed (ReturnPinStackBound.facts hI hg).pipe.2.2.1


theorem raNotSecond_enter (hI : ReturnPinStackBound.okB I = true) (hc : codeMapB I (tabOf I.results) = true)
    (hF : ∀ g ∈ (prog I).funcs, FnOk I file g) {g h : Clif.Function} (hg : g ∈ (prog I).funcs)
    {u : Arm.ArmState} (hp : u.program = (art I g).fb.program (art I g).base)
    (hcall : CallsAt I B g u h) : ¬ Second I h (xreg 30 (enterAt (art I h) u)) := by
  rintro ⟨rl, hrl, ht, he⟩
  have hh := callee_mem hcall
  rw [x30_enterAt] at he
  have hpcu : Arm.r .PC u = wAt (art I h) rl.offset := by
    have h2 : Arm.r .PC u + 4 = wAt (art I h) rl.offset + 4 := by rw [he, wAt_add4]
    exact (BitVec.add_left_inj _).mp h2
  obtain ⟨lm, hm⟩ := FnAsm.layout_labelOffsets (hF g hg).layout
  have hins0 : ∃ i0, insnAt (art I g).fa (progBase u) (Arm.r .PC u) = some i0 ∧
      siteOf (prog I) i0 ≠ .real := by
    rcases hcall with ⟨n, hins, hn⟩ | ⟨⟨x, hins⟩, -⟩
    · exact ⟨_, hins, by simp [siteOf, hn]⟩
    · exact ⟨_, hins, by simp [siteOf]⟩
  obtain ⟨i0, hi0, hr0⟩ := hins0
  obtain ⟨j0, t0, hj0, -⟩ := insnAt_spec hi0
  rw [progBase_of (hF g hg) hm hp hj0] at hi0
  have hs0 := siteAt_static hI hc hF hg hi0
  obtain ⟨j, i1, t1, hj, hi1, ho⟩ := (FnAsm.layout_relocs (hF h hh).layout rl).1 hrl
  have hs1 := siteAt_static hI hc hF hh (insnAt_of_line (hF h hh) hj)
  rw [ho, ← hpcu, hs0, siteOf_pairFirst hi1 ht] at hs1
  exact hr0 (Option.some.inj hs1)


theorem reachL_of_reachN (hI : ReturnPinStackBound.okB I = true) (hc : codeMapB I (tabOf I.results) = true)
    (hF : ∀ g ∈ (prog I).funcs, FnOk I file g) {M : Nat} {f : Clif.Function} {c : Arm.ArmState}
    {M' : Nat} {g : Clif.Function} {t : Arm.ArmState} (h : ReachN I B M f c M' g t) :
    f ∈ (prog I).funcs → (sys I B).RunGoodL M f c → ¬ Second I f (xreg 30 c) →
    ∃ c', (sys I B).ReachL M f c M' g c' t ∧ ¬ Second I g (xreg 30 c') := by
  induction h with
  | act hj => exact fun _ _ hs => ⟨_, .act hj, hs⟩
  | nest hj hcall herr _ ih =>
    intro hf hrun _
    have hu := hrun _ _ _ _ (.act hj) (by rw [runX_succ'] at herr; exact herr)
    obtain ⟨X, K, G, gv, -, hG, -⟩ := hu
    unfold actGoodX at hG
    obtain ⟨c', hR', hs'⟩ := ih (callee_mem hcall)
      (fun _ _ _ _ hr he => hrun _ _ _ _ (.nest hj hcall herr hr) he)
      (raNotSecond_enter hI hc hF hf hG.prog hcall)
    exact ⟨c', .nest hj hcall herr hR', hs'⟩


theorem destsInt_of_ok {L : LinkSys} {modes : Clif.Function → E2E.ReturnPinMode} (hL : L.OkReturnPins modes) {g : Clif.Function} (hg : g ∈ L.P.funcs) :
    (L.A g).vcp.DestsInt := by
  intro b vb k info hb hi r hd
  obtain ⟨t, Lu, Ld, he, -⟩ := hL.blrRegs g hg info ⟨b, vb, k, hb, hi⟩ (fun n => by rw [hd]; simp)
  subst he
  simp only [CallDest.reg.injEq] at hd
  exact ⟨t, hd.symm⟩


theorem stepOkD_of_good (hI : ReturnPinStackBound.okB I = true) (hc : codeMapB I (tabOf I.results) = true)
    (hF : ∀ g ∈ (prog I).funcs, FnOk I file g)
    (hD : ∀ g ∈ (prog I).funcs, (art I g).vcp.DestsInt)
    {M : Nat} {g : Clif.Function} (hg : g ∈ (prog I).funcs) {c t : Arm.ArmState}
    (hgood : (sys I B).GoodAt M g c t) (hs : ¬ Second I g (xreg 30 c))
    (he : Arm.r .ERR ((sys I B).mach M g t) = .None) (hr : StepOkR I B file M g t) :
    StepOkD I B file M g t := by
  obtain ⟨X, K, G, gv, heq, hG, -, -, hba⟩ := hgood
  unfold actGoodX at hG
  have hFg := hF g hg
  have hfit := hFg.fits
  have hsum := layout_sum hFg.layout
  obtain ⟨lm, hm⟩ := FnAsm.layout_labelOffsets hFg.layout
  refine ⟨hG.err, hG.prog, ?_, ?_, hr.insn, hr.got, ?_⟩
  · -- site
    obtain ⟨x, ⟨j, tt, hj, hpc⟩, htl⟩ := hG.line
    exact ⟨x, by rw [hpc]; exact insnAt_of_line hFg hj, Insn.reloc_of_tlsTail htl⟩
  · -- cf
    intro rl hrl ht hpcv
    have hn := hG.next
    have hstep : ArmStepX X ((sys I B).hooks M) ((sys I B).A g).fa t = (sys I B).mach M g t :=
      congrFun heq t
    simp only [RL.step] at hn
    rw [hstep] at hn
    rcases hn with h | h | h | ⟨j, hj, hpf⟩
    · exact absurd he h
    · exact absurd ⟨rl, hrl, ht, by rw [← h]; exact hpcv⟩ hs
    · have h2 : Arm.r .PC t + 4 = wAt (art I g) rl.offset + 4 := by
        rw [← h, hpcv, wAt_add4]
      exact (BitVec.add_left_inj _).mp h2
    · exfalso
      obtain ⟨-, hlt, r', hr', hr'o, hr't⟩ := pair_facts hFg hrl ht
      obtain ⟨j2, i2, t2, hj2, hi2, ho2⟩ := (FnAsm.layout_relocs hFg.layout r').1 hr'
      have hsec : i2.pairSecond = true := by
        refine Insn.pairSecond_of_reloc hi2 ?_
        rw [hr't]; rcases ht with h' | h' <;> rw [h'] <;> simp [loOf]
      obtain ⟨k', y, t', rfl, hy, hy'⟩ := pairsClosed_art hI hg _ _ _ hj2 hsec
      have hyf : y.pairFirst = true := by
        rcases hy' with ⟨a, b, rfl⟩ | ⟨a, b, d, rfl⟩ <;> rfl
      -- the offsets
      have hoff : BitVec.ofNat 64 (lineOffset (art I g).fa.lines.toList (j + 1)) =
          BitVec.ofNat 64 (rl.offset + 4) := by
        have h1 : (art I g).base + BitVec.ofNat 64 (lineOffset (art I g).fa.lines.toList (j + 1)) =
            (art I g).base + BitVec.ofNat 64 (rl.offset + 4) := by
          exact hj.symm.trans hpcv
        exact (BitVec.add_right_inj _).mp h1
      have hoff' := congrArg BitVec.toNat hoff
      simp only [BitVec.toNat_ofNat] at hoff'
      have hk1 := lineOffset_succ _ k' _ hy
      have hk2 := lineOffset_succ _ (k' + 1) _ hj2
      simp only [Line.size] at hk1 hk2
      have hle := lineOffset_le_size (art I g).fa.lines.toList (j + 1)
      rcases Nat.lt_trichotomy (j + 1) (k' + 1) with hlt' | heq' | hgt'
      · have hmono := lineOffset_mono (art I g).fa.lines.toList (show j + 1 ≤ k' by omega)
        rw [Nat.mod_eq_of_lt (by omega : rl.offset + 4 < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega)] at hoff'
        omega
      · obtain rfl : j = k' := by omega
        rw [hpf y t' hy] at hyf
        cases hyf
      · have hmono := lineOffset_mono (art I g).fa.lines.toList (show k' + 1 + 1 ≤ j + 1 by omega)
        rw [Nat.mod_eq_of_lt (by omega : rl.offset + 4 < 2 ^ 64)] at hoff'
        by_cases hx : lineOffset (art I g).fa.lines.toList (j + 1) < 2 ^ 64
        · rw [Nat.mod_eq_of_lt hx] at hoff'
          omega
        · have hx' : lineOffset (art I g).fa.lines.toList (j + 1) = 2 ^ 64 := by omega
          rw [hx'] at hoff'
          simp at hoff'
  · -- blr
    intro x h' hx ht
    obtain ⟨j, tt, hj, hpc⟩ := insnAt_spec hx
    obtain ⟨hxz, hcode⟩ := hG.blr x ⟨j, tt, hj, hpc.symm⟩
    replace hxz := hxz (hD g hg)
    obtain ⟨h4, w, -, hk⟩ := FnAsm.layout_word hFg.layout hm hj rfl
    have hfw := hFg.bin.plain _ w hk (fun r hr' ho => by
      obtain ⟨j', i', t', hj', hi', ho'⟩ := (FnAsm.layout_relocs hFg.layout r).1 hr'
      have := line_unique hj hj' (by omega)
      subst this
      simp [Insn.reloc?] at hi')
    have hrd := hcode _ w hk
    rw [show 4 * (lineOffset (art I g).fa.lines.toList j / 4) =
      lineOffset (art I g).fa.lines.toList j by omega] at hfw hrd
    obtain ⟨info, tv, hsi, hd, hbt⟩ := hba x h' hx ht
    have hh' : h' ∈ (prog I).funcs := by
      obtain ⟨a, -, ha⟩ := Option.bind_eq_some_iff.1 ht
      exact List.mem_of_find?_eq_some ha
    refine ⟨hxz, ?_, symAddr_of_blrTo hI hc hg hh' hsi hd hbt⟩
    rw [← hpc]
    exact hfw.trans (congrArg some hrd.symm)


theorem runOkN_of_good (hI : ReturnPinStackBound.okB I = true) (hc : codeMapB I (tabOf I.results) = true)
    (hF : ∀ g ∈ (prog I).funcs, FnOk I file g) (hD : ∀ g ∈ (prog I).funcs, (art I g).vcp.DestsInt)
    {M : Nat} {f : Clif.Function}
    (hf : f ∈ (prog I).funcs) {c : Arm.ArmState}
    (hra : ∀ k < (art I f).fb.words.size, xreg 30 c ≠ (art I f).base + BitVec.ofNat 64 (4 * k))
    (hgood : (sys I B).RunGoodL M f c) (hreads : RunReadsN I B file M f c) :
    RunOkN I B file M f c := fun M' g t hR he => by
  obtain ⟨c', hRL, hs⟩ := reachL_of_reachN hI hc hF hR hf hgood (raNotSecond_top (hF f hf) hra)
  exact stepOkD_of_good hI hc hF hD (reachN_mem hR hf) (hgood _ _ _ _ hRL he) hs he
    (hreads _ _ _ hR he)


theorem image_checked (hI : ReturnPinStackBound.okB I = true) : imgB (tabOf I.results) = true :=
  okRSemanticFor_global returnPinCallsExtra I.stage (Bool.and_eq_true_iff.mp hI).1
    ("imgCode: the image reads back",imgB (tabOf I.results)) (by simp [globalChks])

end E2E.ReturnPinExecBytes
