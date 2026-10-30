import FV.E2E.DeadCleanupExecStatic
import FV.E2E.DeadCleanupLinkCheckT
import FV.E2E.LinkArmT
import FV.E2E.LinkCheckT
import FV.E2E.PipelineCheckT

/-! # Typed copies of `FV.E2E.DeadCleanupExecStatic` (S11e5 Stage C, slice 8)

The declarations of `FV.E2E.DeadCleanupExecStatic` that depend on the integer link contract
(`LinkSys.Ok`, `LinkSys.Thm`, `okB`, `ArmRefines`), for the typed contract `LinkSys.OkT`
(suffix `T`; `LinkSys.Ok.*` as `LinkSys.OkT.*`). -/

namespace E2E.DeadCleanupExecBytes
set_option autoImplicit false
open Backend Backend.Proof E2E.LinkCheck E2E.DeadCleanupBinary E2E.BinCheck
section Defs
variable (I : LinkInput) (B : BaseEnv) (file : ByteArray)
end Defs

theorem codeMap_soundT {I : LinkInput} (hI : okBCleanupT I = true) (hc : codeMapB I (tabOf I.resultsCleanup) = true)
    {g : Clif.Function} (hg : g ∈ (prog I).funcs) :
    (I.symAddr g.name 0 = (art I g).base ∨ noBlrB I (tabOf I.resultsCleanup) g.name = true) ∧
    ∀ g' ∈ (prog I).funcs, g.name ≠ g'.name →
      ((art I g).base.toNat + 4 * (art I g).fb.words.size ≤ (art I g').base.toNat ∨
        (art I g').base.toNat + 4 * (art I g').fb.words.size ≤ (art I g).base.toNat) ∨
      ((art I g).base = (art I g').base ∧
        linesAlikeB (prog I) (art I g).fa.lines.toList (art I g').fa.lines.toList = true) := by
  simp only [codeMapB, progT_tabOf, List.all_eq_true, Bool.and_eq_true, beq_iff_eq,
    Bool.or_eq_true, decide_eq_true_eq] at hc
  have hn := okBCleanup_namesT hI
  have hgt := hc _ (tab_mem hn hg)
  refine ⟨hgt.1, fun g' hg' hne => ?_⟩
  rcases hgt.2 _ (tab_mem hn hg') with (h | h) | h
  · exact absurd h hne
  · exact .inl h
  · exact .inr h

/-- **The callee of a `blr` of the program has its link-map address at its load address**: a
`blr` of `g` through `t` may enter `h` (`BlrTo`) only if `h`'s link-map address is its load
address (`codeMapB`). -/
theorem symAddr_of_blrToT {I : LinkInput} {B : BaseEnv} (hI : okBCleanupT I = true)
    (hc : codeMapB I (tabOf I.resultsCleanup) = true) {g h : Clif.Function} (hg : g ∈ (prog I).funcs)
    (hh : h ∈ (prog I).funcs) {info : CallInfo} {t : Nat} (hs : (art I g).vcp.CallSite info)
    (hd : info.dest = .reg (.vreg t .int)) (hb : (sys I B).BlrTo g t h) :
    I.symAddr h.name 0 = (art I h).base := by
  refine ((codeMap_soundT hI hc hh).1).resolve_right fun hn => ?_
  simp only [noBlrB, Bool.and_eq_true, Option.isNone_iff_eq_none, List.all_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', List.any_eq_false, beq_iff_eq] at hn
  obtain ⟨⟨hmay, -⟩, hgot⟩ := hb
  rcases hmay with hdecl | ⟨-, hsym, -⟩
  · rcases hn.2 _ (tab_mem (okBCleanup_namesT hI) hg) with hx | hx
    · obtain ⟨x, hx', he⟩ := List.mem_map.1 hdecl
      exact hx x hx' he
    · obtain ⟨n', hv, hn'⟩ := blrGotB_sound hx hs hd
      exact hn' (hgot n' hv)
  · exact hsym hn.1
section Static
variable {I : LinkInput} {B : BaseEnv} {file : ByteArray}

/-- A relocated byte is in a relocated word of a function of the program. -/
theorem relocAt_invT (hI : okBCleanupT I = true) {a : BitVec 64} (h : E2E.DeadCleanupBinCheck.RelocAt I a) :
    ∃ g ∈ (prog I).funcs, ∃ rl ∈ (art I g).fb.relocs, ∃ i < 4, a = wAt (art I g) (rl.offset + i) := by
  obtain ⟨e, he, rl, hrl, i, hi, rfl⟩ := h
  obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
  have hart : art I e0.1 = getOk e0.2 := by
    simp only [art, artOf, find_name (okBCleanup_namesT hI) he0]
  exact ⟨e0.1, List.mem_map_of_mem he0, rl, by rw [hart]; exact hrl, i, hi, by rw [hart]⟩

/-- **Overlapping words of two functions are alike lines** (`codeMapB`): the same function's
same line, or the lines at the same offset of two functions sharing their code. -/
theorem line_overlapT (hI : okBCleanupT I = true) (hc : codeMapB I (tabOf I.resultsCleanup) = true)
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
  · rcases (codeMap_soundT hI hc hg).2 h hh hn with hd | ⟨hb, ha⟩
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

/-- **The site lookup finds the kind of site of the function's instruction** (the code of
another function there has an alike instruction). -/
theorem siteAt_staticT (hI : okBCleanupT I = true) (hc : codeMapB I (tabOf I.resultsCleanup) = true) (hF : ∀ g ∈ (prog I).funcs, FnOk I file g)
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
    have hal := line_overlapT hI hc hF hg0 hg hj0 hj rfl rfl (k := 0) (k' := 0) (by omega)
      (by omega) (by omega)
    simp only [lineAlikeB] at hal
    rw [insnAlikeB_site hal]
  · rename_i hne
    exact absurd ⟨g, hg, by rw [hi]; rfl⟩ hne

/-- **An instruction word without relocation is no relocated byte.** -/
theorem plain_staticT (hI : okBCleanupT I = true) (hc : codeMapB I (tabOf I.resultsCleanup) = true) (hF : ∀ g ∈ (prog I).funcs, FnOk I file g)
    {g : Clif.Function} (hg : g ∈ (prog I).funcs) {a : BitVec 64} {i : Insn}
    (hi : insnAt (art I g).fa (art I g).base a = some i) (hr : i.reloc? = none) :
    ∀ k < 4, ¬ E2E.DeadCleanupBinCheck.RelocAt I (a + BitVec.ofNat 64 k) := by
  intro k hk hR
  obtain ⟨j, t, hj, ha, hl⟩ := insn_range (hF g hg) hi
  obtain ⟨h, hh, rl, hrl, i', hi', he⟩ := relocAt_invT hI hR
  obtain ⟨j', i2, t2, hj', hri, ho⟩ := (FnAsm.layout_relocs (hF h hh).layout rl).1 hrl
  have hl' := line_lt (hF h hh) hj'
  have hfit := (hF h hh).fits
  have hfit' := (hF g hg).fits
  have he' := congrArg BitVec.toNat he
  rw [BitVec.toNat_add, ha, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : k < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega), wAt, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : rl.offset + i' < 2 ^ 64), Nat.mod_eq_of_lt (by omega)] at he'
  have hal := line_overlapT hI hc hF hg hh hj hj' rfl rfl hk hi' (by rw [ho]; omega)
  simp only [lineAlikeB] at hal
  rw [insnAlikeB_reloc hal hr] at hri
  cases hri

/-- **`StepOk` from `StepOkD`**, the checks and the hooks' contract. -/
theorem stepOk_of_dT (hI : okBCleanupT I = true) (hc : codeMapB I (tabOf I.resultsCleanup) = true) (hF : ∀ g ∈ (prog I).funcs, FnOk I file g)
    (hH : HooksSim I B) {M : Nat} {g : Clif.Function} (hg : g ∈ (prog I).funcs)
    {m : Arm.ArmState} (h : StepOkD I B file M g m) : StepOk I B file M g m where
  err := h.err
  program := h.program
  site := by
    obtain ⟨i, hi, hr⟩ := h.site
    exact ⟨i, hi, siteAt_staticT hI hc hF hg hi, hr⟩
  cf := h.cf
  insn := h.insn
  call d e _ hs := hH.call d m e hs
  tls tmp _ n e _ hs := hH.tls n tmp m e hs
  got := h.got
  blr := h.blr
  plain i hi hr := plain_staticT hI hc hF hg hi hr
end Static
end E2E.DeadCleanupExecBytes
