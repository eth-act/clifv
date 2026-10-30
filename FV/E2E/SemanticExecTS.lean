import FV.E2E.SemanticExecProven
import FV.E2E.SemanticBinaryGoodTS
import FV.E2E.ExecBytesT
import FV.E2E.ExecGoodRunT
import FV.E2E.LinkGoodT

/-! # Typed copies of the executable-level theorems of the Stock chain (#722)

The declarations of `FV.E2E.SemanticExecBytes`, `…ExecStatic`, `…ExecRunN`, `…ExecGoodRun`,
`…ExecGoodReads`, `…ExecGot` and `…ExecProven` that depend on the link contract
(`LinkSys.OkSemanticNI`, `okB`, `ArmRefines`), for the typed contract `LinkSys.OkT` and the typed
checks `SemanticStackBound.okBTS` (suffix `TS`; as the `DeadCleanupExec*T` files are of the
`DeadCleanupExec*` ones). The conclusions are the typed refinement `ExecBytes.ExecRefinesT`
(each returned value in the ABI return register of its class):
`binary_correct_exec_provenTS`, `binary_correct_exec_depth_provenTS`,
`binary_correct_exec_peak_provenTS`. -/

namespace E2E
set_option autoImplicit false
open Backend Backend.Proof E2E.LinkCheck E2E.BinCheck Elf

namespace LinkSys

/-- `OkSemanticNI.extImgProduction` for `OkT`. -/
theorem OkT.extImgProduction {L : LinkSys} (hL : L.OkT) {F S : BitVec 64 → Prop}
    {m : Arm.Memory} (hm : ∀ a, L.Img a → m a = L.imgMem a) (hF : ∀ a, L.Img a ∨ S a → F a) :
    (L.extImgProduction F S m).OkT :=
  { hL with
    imgAddr := fun g hg a ha => .inl (hL.imgAddr g hg a ha)
    imgCode := fun g hg t ht => hL.imgCode g hg t fun a ha => (ht a (.inl ha)).trans (hm a ha)
    imgF := hF }

end LinkSys

namespace SemanticExecBytes
open SemanticBinary

section Static
variable {I : SemanticStackBound.CompilerInput} {B : BaseEnv} {file : ByteArray}

theorem fnOkTS {D : List Clif.DataObject} (hI : SemanticStackBound.okBTS I = true)
    (hbin : BinOkWithResults I I.results D file)
    {F : BitVec 64 → Prop} (hL : (SemanticStackBound.ofInput I B F).OkT) {g : Clif.Function}
    (hg : g ∈ (prog I).funcs) : FnOk I file g := by
  obtain ⟨-, -, -, hla, hb⟩ := (SemanticStackBound.factsTS hI hg).pipe
  exact ⟨hla, hL.fits g hg, hbin.code _ (tab_mem (SemanticStackBound.okBTS_names hI) hg), hb⟩

theorem codeMap_soundTS (hI : SemanticStackBound.okBTS I = true)
    (hc : codeMapB I (tabOf I.results) = true) {g : Clif.Function} (hg : g ∈ (prog I).funcs) :
    (I.symAddr g.name 0 = (art I g).base ∨ noBlrB I (tabOf I.results) g.name = true) ∧
    ∀ g' ∈ (prog I).funcs, g.name ≠ g'.name →
      ((art I g).base.toNat + 4 * (art I g).fb.words.size ≤ (art I g').base.toNat ∨
        (art I g').base.toNat + 4 * (art I g').fb.words.size ≤ (art I g).base.toNat) ∨
      ((art I g).base = (art I g').base ∧
        linesAlikeB (prog I) (art I g).fa.lines.toList (art I g').fa.lines.toList = true) := by
  simp only [codeMapB, progT_tabOf, List.all_eq_true, Bool.and_eq_true, beq_iff_eq,
    Bool.or_eq_true, decide_eq_true_eq] at hc
  have hn := SemanticStackBound.okBTS_names hI
  have hgt := hc _ (tab_mem hn hg)
  refine ⟨hgt.1, fun g' hg' hne => ?_⟩
  rcases hgt.2 _ (tab_mem hn hg') with (h | h) | h
  · exact absurd h hne
  · exact .inl h
  · exact .inr h

/-- `symAddr_of_blrTo` under `okBTS`. -/
theorem symAddr_of_blrToTS (hI : SemanticStackBound.okBTS I = true)
    (hc : codeMapB I (tabOf I.results) = true) {g h : Clif.Function} (hg : g ∈ (prog I).funcs)
    (hh : h ∈ (prog I).funcs) {info : CallInfo} {t : Nat} (hs : (art I g).vcp.CallSite info)
    (hd : info.dest = .reg (.vreg t .int)) (hb : (sys I B).BlrTo g t h) :
    I.symAddr h.name 0 = (art I h).base := by
  refine ((codeMap_soundTS hI hc hh).1).resolve_right fun hn => ?_
  simp only [noBlrB, Bool.and_eq_true, Option.isNone_iff_eq_none, List.all_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', List.any_eq_false, beq_iff_eq] at hn
  obtain ⟨⟨hmay, -⟩, hgot⟩ := hb
  rcases hmay with hdecl | ⟨-, hsym, -⟩
  · rcases hn.2 _ (tab_mem (SemanticStackBound.okBTS_names hI) hg) with hx | hx
    · obtain ⟨x, hx', he⟩ := List.mem_map.1 hdecl
      exact hx x hx' he
    · obtain ⟨n', hv, hn'⟩ := blrGotB_sound hx hs hd
      exact hn' (hgot n' hv)
  · exact hsym hn.1

/-- A relocated byte is in a relocated word of a function of the program. -/
theorem relocAt_invTS (hI : SemanticStackBound.okBTS I = true) {a : BitVec 64}
    (h : RelocAtWithResults I I.results a) :
    ∃ g ∈ (prog I).funcs, ∃ rl ∈ (art I g).fb.relocs, ∃ i < 4, a = wAt (art I g) (rl.offset + i) := by
  obtain ⟨e, he, rl, hrl, i, hi, rfl⟩ := h
  obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
  have hart : art I e0.1 = getOk e0.2 := by
    simp only [art, artOf, find_name (SemanticStackBound.okBTS_names hI) he0]
  exact ⟨e0.1, List.mem_map_of_mem he0, rl, by rw [hart]; exact hrl, i, hi, by rw [hart]⟩

/-- **Overlapping words of two functions are alike lines** (`line_overlap` under `okBTS`). -/
theorem line_overlapTS (hI : SemanticStackBound.okBTS I = true)
    (hc : codeMapB I (tabOf I.results) = true)
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
  · rcases (codeMap_soundTS hI hc hg).2 h hh hn with hd | ⟨hb, ha⟩
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

/-- **The site lookup finds the kind of site of the function's instruction** (under `okBTS`). -/
theorem siteAt_staticTS (hI : SemanticStackBound.okBTS I = true)
    (hc : codeMapB I (tabOf I.results) = true) (hF : ∀ g ∈ (prog I).funcs, FnOk I file g)
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
    have hal := line_overlapTS hI hc hF hg0 hg hj0 hj rfl rfl (k := 0) (k' := 0) (by omega)
      (by omega) (by omega)
    simp only [lineAlikeB] at hal
    rw [insnAlikeB_site hal]
  · rename_i hne
    exact absurd ⟨g, hg, by rw [hi]; rfl⟩ hne

/-- **An instruction word without relocation is no relocated byte** (under `okBTS`). -/
theorem plain_staticTS (hI : SemanticStackBound.okBTS I = true)
    (hc : codeMapB I (tabOf I.results) = true) (hF : ∀ g ∈ (prog I).funcs, FnOk I file g)
    {g : Clif.Function} (hg : g ∈ (prog I).funcs) {a : BitVec 64} {i : Insn}
    (hi : insnAt (art I g).fa (art I g).base a = some i) (hr : i.reloc? = none) :
    ∀ k < 4, ¬ RelocAtWithResults I I.results (a + BitVec.ofNat 64 k) := by
  intro k hk hR
  obtain ⟨j, t, hj, ha, hl⟩ := insn_range (hF g hg) hi
  obtain ⟨h, hh, rl, hrl, i', hi', he⟩ := relocAt_invTS hI hR
  obtain ⟨j', i2, t2, hj', hri, ho⟩ := (FnAsm.layout_relocs (hF h hh).layout rl).1 hrl
  have hl' := line_lt (hF h hh) hj'
  have hfit := (hF h hh).fits
  have hfit' := (hF g hg).fits
  have he' := congrArg BitVec.toNat he
  rw [BitVec.toNat_add, ha, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : k < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega), wAt, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : rl.offset + i' < 2 ^ 64), Nat.mod_eq_of_lt (by omega)] at he'
  have hal := line_overlapTS hI hc hF hg hh hj hj' rfl rfl hk hi' (by rw [ho]; omega)
  simp only [lineAlikeB] at hal
  rw [insnAlikeB_reloc hal hr] at hri
  cases hri

/-- **`StepOk` from `StepOkD`**, the checks and the hooks' contract (under `okBTS`). -/
theorem stepOk_of_dTS (hI : SemanticStackBound.okBTS I = true)
    (hc : codeMapB I (tabOf I.results) = true) (hF : ∀ g ∈ (prog I).funcs, FnOk I file g)
    (hH : HooksSim I B) {M : Nat} {g : Clif.Function} (hg : g ∈ (prog I).funcs)
    {m : Arm.ArmState} (h : StepOkD I B file M g m) : StepOk I B file M g m where
  err := h.err
  program := h.program
  site := by
    obtain ⟨i, hi, hr⟩ := h.site
    exact ⟨i, hi, siteAt_staticTS hI hc hF hg hi, hr⟩
  cf := h.cf
  insn := h.insn
  call d e _ hs := hH.call d m e hs
  tls tmp _ n e _ hs := hH.tls n tmp m e hs
  got := h.got
  blr := h.blr
  plain i hi hr := plain_staticTS hI hc hF hg hi hr

theorem runOkSN_of_nTS (hI : SemanticStackBound.okBTS I = true)
    (hc : codeMapB I (tabOf I.results) = true)
    (hF : ∀ g ∈ (prog I).funcs, FnOk I file g) (hH : HooksSim I B) {M : Nat}
    {f : Clif.Function} (hf : f ∈ (prog I).funcs) {c : Arm.ArmState}
    (h : RunOkN I B file M f c) : RunOkSN I B file M f c :=
  fun M' g t hR he => stepOk_of_dTS hI hc hF hH (reachN_mem hR hf) (h M' g t hR he)

/-- **The model's outcome transfers to the executable machine, typed** (`exec_of_modelN` with
`ArmRefinesT`, `ExecRefinesT`). -/
theorem exec_of_modelNTS (hF : ∀ g ∈ (prog I).funcs, FnOk I file g) {M : Nat}
    {f : Clif.Function}
    (hf : f ∈ (prog I).funcs) {r : Arm.ArmState} (hpc : Arm.r .PC r = (art I f).base)
    (hra : ∀ k < (art I f).fb.words.size, xreg 30 r ≠ (art I f).base + BitVec.ofNat 64 (4 * k))
    (hd : ∀ a, (modelOf I f r).mem a ≠ r.mem a → RelocAtWithResults I I.results a)
    (hrun : RunOkSN I B file M f (modelOf I f r)) {o : Clif.Outcome}
    (h : ArmRefinesT (art I f).fb (art I f).base (xreg 30 r) ((sys I B).mach M f) (modelOf I f r) o) :
    ExecBytes.ExecRefinesT (art I f).fb (art I f).base (xreg 30 r) (step I B file) r
      (RelocAtWithResults I I.results) o := by
  have hFf := hF f hf
  have hsim := sim_modelOf hd
  have hra' : ∀ k < (art I f).fb.words.size,
      xreg 30 (modelOf I f r) ≠ (art I f).base + BitVec.ofNat 64 (4 * k) := by
    simp only [xreg, r_modelOf]; exact hra
  have hpc' : Arm.r .PC (modelOf I f r) = (art I f).base := by rw [r_modelOf]; exact hpc
  have hsimN := act_simN (B := B) hF M f _ r hf hpc' hsim hrun
  cases o with
  | returned vals cm =>
    obtain ⟨n, hret, hx, hmem⟩ := h
    obtain ⟨k', hk'⟩ := hsimN n (no_return hFf hra' hret.err) (fun hs => by
      obtain ⟨k, hk, he⟩ := second_code hFf hs
      exact hra k hk (by rw [← he, hret.pc])) hret.err
    refine ⟨k', ⟨?_, ?_, ?_, fun n hn => ?_, fun n h8 h16 => ?_⟩, fun j v q hv hq => ?_,
      fun a b hv hb hR => ?_⟩
    · rw [hk'.1, hret.pc]
    · rw [hk'.1, hret.err]
    · simp only [spv]; rw [hk'.1]; exact (hret.sp.trans (spv_modelOf I f r))
    · simp only [xreg]; rw [hk'.1]; exact (hret.savedX n hn).trans (r_modelOf I f r _)
    · rw [hk'.1, hret.savedV n h8 h16, r_modelOf]
    · have hxq := hx j v q hv hq
      cases q <;> simp only [regVal] at hxq ⊢ <;> (try rw [hk'.1]) <;> exact hxq
    · show Arm.read_store _ _ = b
      rw [show Arm.read_store (BitVec.ofNat 64 a) (runX (step I B file) k' r).mem =
        (runX (step I B file) k' r).mem (BitVec.ofNat 64 a) from rfl, hk'.2 _ hR]
      exact hmem a b hv hb
  | trapped c0 =>
    obtain ⟨n, htrap⟩ := h
    have hguard := no_return (B := B) hFf hra' htrap.err
    by_cases hs : Second I f (Arm.r .PC (runX ((sys I B).mach M f) n (modelOf I f r)))
    · obtain ⟨rl, hrl, ht, he⟩ := hs
      cases n with
      | zero => exact (not_second_base hFf ⟨rl, hrl, ht, hpc'.symm.trans he⟩).elim
      | succ n1 =>
      have hok1 := hrun _ _ _ (ReachN.act (k := n1) fun j hj => hguard j (by omega))
        (by rw [← runX_succ' ((sys I B).mach M f)]; exact htrap.err)
      have hpc1 := hok1.cf rl hrl ht (by rw [← runX_succ' ((sys I B).mach M f) n1]; exact he)
      obtain ⟨k', hk'⟩ := hsimN n1 (fun j hj => hguard j (by omega))
        (by rw [hpc1]; exact first_not_second hFf hrl ht) hok1.err
      obtain ⟨hpcE, herrE⟩ := pair_first_pc hFf hrl ht hpc1 hok1 hk'
      refine ⟨k' + 1, ?_⟩
      rw [runX_succ'] at htrap ⊢
      exact ⟨by rw [← herrE]; exact htrap.err, by rw [← hpcE]; exact htrap.site⟩
    · obtain ⟨k', hk'⟩ := hsimN n hguard hs htrap.err
      exact ⟨k', by rw [hk'.1]; exact htrap.err, by rw [hk'.1]; exact htrap.site⟩
  | stuck _ => trivial
  | outOfFuel => trivial

/-- The lines of a function of the program keep `adrp` pairs adjacent. -/
theorem pairsClosed_artTS (hI : SemanticStackBound.okBTS I = true) {g : Clif.Function}
    (hg : g ∈ (prog I).funcs) : PairsClosed (art I g).fa.lines.toList := by
  exact emitFunc_pairsClosed (SemanticStackBound.factsTS hI hg).pipe.2.2.1

/-- `raNotSecond_enter` under `okBTS`. -/
theorem raNotSecond_enterTS (hI : SemanticStackBound.okBTS I = true)
    (hc : codeMapB I (tabOf I.results) = true)
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
  have hs0 := siteAt_staticTS hI hc hF hg hi0
  obtain ⟨j, i1, t1, hj, hi1, ho⟩ := (FnAsm.layout_relocs (hF h hh).layout rl).1 hrl
  have hs1 := siteAt_staticTS hI hc hF hh (insnAt_of_line (hF h hh) hj)
  rw [ho, ← hpcu, hs0, siteOf_pairFirst hi1 ht] at hs1
  exact hr0 (Option.some.inj hs1)

/-- **The states of `ReachN` are states of `ReachL`** (under `okBTS`). -/
theorem reachL_of_reachNTS (hI : SemanticStackBound.okBTS I = true)
    (hc : codeMapB I (tabOf I.results) = true)
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
      (raNotSecond_enterTS hI hc hF hf hG.prog hcall)
    exact ⟨c', .nest hj hcall herr hR', hs'⟩

/-- **`StepOkD` from the register-level per-state facts** and the memory-read facts (under
`okBTS`). -/
theorem stepOkD_of_goodTS (hI : SemanticStackBound.okBTS I = true)
    (hc : codeMapB I (tabOf I.results) = true)
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
  · obtain ⟨x, ⟨j, tt, hj, hpc⟩, htl⟩ := hG.line
    exact ⟨x, by rw [hpc]; exact insnAt_of_line hFg hj, Insn.reloc_of_tlsTail htl⟩
  · intro rl hrl ht hpcv
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
      obtain ⟨k', y, t', rfl, hy, hy'⟩ := pairsClosed_artTS hI hg _ _ _ hj2 hsec
      have hyf : y.pairFirst = true := by
        rcases hy' with ⟨a, b, rfl⟩ | ⟨a, b, d, rfl⟩ <;> rfl
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
  · intro x h' hx ht
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
    refine ⟨hxz, ?_, symAddr_of_blrToTS hI hc hg hh' hsi hd hbt⟩
    rw [← hpc]
    exact hfw.trans (congrArg some hrd.symm)

/-- **`RunOkN` from the register-level per-state facts** (under `okBTS`). -/
theorem runOkN_of_goodTS (hI : SemanticStackBound.okBTS I = true)
    (hc : codeMapB I (tabOf I.results) = true)
    (hF : ∀ g ∈ (prog I).funcs, FnOk I file g) (hD : ∀ g ∈ (prog I).funcs, (art I g).vcp.DestsInt)
    {M : Nat} {f : Clif.Function}
    (hf : f ∈ (prog I).funcs) {c : Arm.ArmState}
    (hra : ∀ k < (art I f).fb.words.size, xreg 30 c ≠ (art I f).base + BitVec.ofNat 64 (4 * k))
    (hgood : (sys I B).RunGoodL M f c) (hreads : RunReadsN I B file M f c) :
    RunOkN I B file M f c := fun M' g t hR he => by
  obtain ⟨c', hRL, hs⟩ := reachL_of_reachNTS hI hc hF hR hf hgood (raNotSecond_top (hF f hf) hra)
  exact stepOkD_of_goodTS hI hc hF hD (reachN_mem hR hf) (hgood _ _ _ _ hRL he) hs he
    (hreads _ _ _ hR he)

/-- **A relocated byte is a code byte of the image** (under `okBTS`). -/
theorem relocAt_imgTS (hI : SemanticStackBound.okBTS I = true)
    (hF : ∀ g ∈ (prog I).funcs, FnOk I file g)
    {a : BitVec 64} (h : RelocAtWithResults I I.results a) : ImgT (tabOf I.results) a := by
  obtain ⟨g, hg, rl, hrl, i, hi, rfl⟩ := relocAt_invTS hI h
  obtain ⟨j, x, t, hj, -, ho⟩ := (FnAsm.layout_relocs (hF g hg).layout rl).1 hrl
  obtain ⟨lm, hm⟩ := FnAsm.layout_labelOffsets (hF g hg).layout
  obtain ⟨h4, w, -, hk⟩ := FnAsm.layout_word (hF g hg).layout hm hj rfl
  have hl := line_lt (hF g hg) hj
  have hfit := (hF g hg).fits
  refine ⟨(g, art I g), tab_mem (SemanticStackBound.okBTS_names hI) hg,
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

/-- **The bytes of a jump-table word of a function are no relocated bytes** (under `okBTS`). -/
theorem word_staticTS (hI : SemanticStackBound.okBTS I = true)
    (hc : codeMapB I (tabOf I.results) = true)
    (hF : ∀ g ∈ (prog I).funcs, FnOk I file g) {g : Clif.Function} (hg : g ∈ (prog I).funcs)
    {j : Nat} {tg bs : Lbl} (hj : (art I g).fa.lines.toList[j]? = some (.word tg bs)) :
    ∀ k < 4, ¬ RelocAtWithResults I I.results (wAt (art I g) (lineOffset (art I g).fa.lines.toList j) +
      BitVec.ofNat 64 k) := by
  intro k hk hR
  obtain ⟨h, hh, rl, hrl, i', hi', he⟩ := relocAt_invTS hI hR
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
  have hal := line_overlapTS hI hc hF hg hh hj hj' rfl rfl hk hi' (by rw [ho]; omega)
  simp [lineAlikeB] at hal

/-- **`StepOkR.insn` (D2) from the per-state facts** (under `okBTS`). -/
theorem insn_of_goodTS (hI : SemanticStackBound.okBTS I = true)
    (hc : codeMapB I (tabOf I.results) = true)
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
  obtain ⟨x, ⟨jx, tx, hjx, hpcx⟩, htl⟩ := hG.line
  have hxi : x = i := by
    have h1 := insnAt_of_line hFg hjx
    have h2 : wAt (art I g) (lineOffset (art I g).fa.lines.toList jx) = Arm.r .PC t := hpcx.symm
    rw [h2, hi] at h1
    exact (Option.some.inj h1).symm
  subst hxi
  have hr : x.reloc? = none := (Insn.reloc_of_tlsTail htl).resolve_right (by rw [hh]; decide)
  obtain ⟨w, hw, hfw⟩ := fileWord_plain hFg hm hj hr
  have hpcw : Arm.r .PC t = wAt (art I g) (lineOffset (art I g).fa.lines.toList j) := hpc.symm
  rw [hpcw, hfw, Option.bind_some] at ha
  obtain ⟨a', ha', hd⟩ := Insn.decode_encode hw
  rw [ha] at hd
  cases hd
  have hrd := hrdA j x tt hj hpcw hh _ a ha' p hp k hk
  rcases hrd with hnG | ⟨j', tg, bs, hj', q, hq, he⟩
  · exact hnG (himg _ (relocAt_imgTS hI hF hR))
  · rw [he] at hR
    exact word_staticTS hI hc hF hg hj' q hq hR

/-- **The entry premises of the whole-program theorems for the system keeping the slots**
(`sysS_entry` under `okBTS`, `OkT`; as there the stack premise is the room `StackRoom` only,
#581). -/
theorem sysS_entryTS {D : List Clif.DataObject} (hI : SemanticStackBound.okBTS I = true)
    (hbin : BinOkWithResults I I.results D file)
    (hB : BaseOk (sys I B)) {f : Clif.Function} (hfm : f ∈ (prog I).funcs)
    {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State} (hX : (imageOf file).Intact r)
    {K : Nat}
    (ho : OutsideCall I (BinCheck.roByte I D) f (frameDrop (art I f).af + K) r args cs.mem)
    {S : BitVec 64 → Prop} (hav : OutsideAvoids S f (frameDrop (art I f).af + K) r args cs.mem)
    (hr : ClifRun I B f r args cs) :
    (sysS I B f K r S).OkT ∧
    AbiEntry (art I f).fb (art I f).base (xreg 30 r) (modelOf I f r) ∧
    StackRoom ((art I f).af.frameSize + 16 + K) (modelOf I f r) ∧
    (∀ a, (sysS I B f K r S).Img a →
      ¬ StackBelow (frameDrop (art I f).af + K) (spv (modelOf I f r)) a) ∧
    BodyEntry (art I f).af (modelOf I f r) (bodyOf (art I f).af (modelOf I f r)) ∧
    ArgsIn f.sig args (modelOf I f r) ∧
    StackArgsAvoid (sysS I B f K r S).Img f.sig args (modelOf I f r) ∧
    Rel.holds ⟨(sysS I B f K r S).F, (sysS I B f K r S).syms, (art I f).af.slotBase,
      (RAFrame.compute (art I f).vcp (art I f).rf).intBase⟩ f cs.frame.slots cs.mem
      (bodyOf (art I f).af (modelOf I f r)) ∧
    ((sysS I B f K r S).NeedSlots →
      (sysS I B f K r S).PlaceAt cs.mem (spv (bodyOf (art I f).af (modelOf I f r)))) := by
  have hB' : BaseOk (SemanticStackBound.ofInput I B (worldF I f K r)) := baseOk_F hB
  have himgF : ∀ a, (SemanticStackBound.ofInput I B (worldF I f K r)).Img a →
      worldF I f K r a := fun _ h => .inr h
  have hL0 := SemanticStackBound.okBTS_sound hI hB' himgF
  have hfacts := binFacts_of_checksTS hI hbin
  have hro : ∀ a b, BinCheck.roByte I D a = some b → r.mem a = b := fun a b h =>
    hX a b (hfacts.data a b h).1 (hfacts.data a b h).2
  obtain ⟨hent, hres, hgfree, -, hbe, hargs, hsav, hrel, hpl⟩ := premisesTS hL0 hfm hro ho hr
  have hL : (sysS I B f K r S).OkT := LinkSys.OkT.extImgProduction hL0
    (fun a ha => mem_modelOf_img ha) fun a ha => by
      rcases ha with ha | ha
      · exact .inr (.inl ha)
      · exact .inr (.inr ha)
  obtain ⟨hd, hsb, hib, hsz⟩ := frame_factsTS hL0 hfm
  have hN := ho.stack
  have hsp := (spv r).isLt
  have hspbN : (spBody (art I f).af r).toNat = (spv r).toNat - frameDrop (art I f).af :=
    (off_toNat 0 (spv r) _ (by omega)).2.2
  have hspb : spv (bodyOf (art I f).af (modelOf I f r)) = spBody (art I f).af r := by
    rw [spv_bodyOf, spv_modelOf]; rfl
  refine ⟨hL, hent, hres, fun a ha => ?_, hbe, hargs, fun off v hm k hk hx => ?_,
    ⟨⟨hrel.1.bytes, fun a n hv => ?_, hrel.1.symbols⟩, hrel.2.1, hrel.2.2.1, fun j hj => ?_,
      hrel.2.2.2.2⟩, hpl⟩
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
    show StackBelow (frameDrop (art I f).af + K) _ _
    simp only [StackBelow, BitVec.toNat_add, BitVec.toNat_ofNat, hspbN]
    rw [Nat.mod_eq_of_lt (by omega : j < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
    omega

/-- **`RunGoodL` of the system keeping the slots** for any callees' budget (under `okBTS`). -/
theorem runGood_sysS_ofTS {D : List Clif.DataObject} (hI : SemanticStackBound.okBTS I = true)
    (hbin : BinOkWithResults I I.results D file)
    (hB : BaseOk (sys I B)) {f : Clif.Function} (hfm : f ∈ (prog I).funcs) (M : Nat)
    {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State} (hX : (imageOf file).Intact r)
    {K : Nat} {κ : Nat → Clif.Function → Nat}
    (hκ : (SemanticStackBound.ofInput I B (worldF I f K r)).Budget κ) (hK : κ M f = K)
    (ho : OutsideCall I (BinCheck.roByte I D) f (frameDrop (art I f).af + K) r args cs.mem)
    {S : BitVec 64 → Prop} (hav : OutsideAvoids S f (frameDrop (art I f).af + K) r args cs.mem)
    (hr : ClifRun I B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) (prog I).bare cs)
    (hout : (∃ vals cm, Clif.runLoop B.env (prog I) (M + 1) cs = .returned vals cm) ∨
      (∃ c, Clif.runLoop B.env (prog I) (M + 1) cs = .trapped c)) :
    (sysS I B f K r S).RunGoodL M f (modelOf I f r) := by
  subst hK
  obtain ⟨hL, hent, hres, hgfree, hbe, hargs, hsav, hrel, hpl⟩ :=
    sysS_entryTS hI hbin hB hfm hX ho hav hr
  exact (backend_correct_program_budgetXT (sysS I B f (κ M f) r S) hL (hκ.extImgProduction _ _ _)
    hfm M hent ⟨hres, (hκ.extImgProduction _ _ _).2 M f hfm⟩ rfl hgfree (fun a _ => rfl) hbe hargs
    hr.entry hsav hrel hpl htr).2 hout

/-- **`RunGoodL` of the system keeping the slots**, the stack bound of a non-recursive program
(under `okBTS`). -/
theorem runGood_sysSTS {D : List Clif.DataObject} (hI : SemanticStackBound.okBTS I = true)
    (hbin : BinOkWithResults I I.results D file)
    (hB : BaseOk (sys I B)) {n : String} (hn : SemanticStackBound.goodN I n = true)
    {f : Clif.Function}
    (hf : (prog I).func? n = some f) (M : Nat) {r : Arm.ArmState} {args : List Clif.Val}
    {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (SemanticStackBound.stackFn I f) r args cs.mem)
    {S : BitVec 64 → Prop} (hav : OutsideAvoids S f (SemanticStackBound.stackFn I f) r args cs.mem)
    (hr : ClifRun I B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) (prog I).bare cs)
    (hout : (∃ vals cm, Clif.runLoop B.env (prog I) (M + 1) cs = .returned vals cm) ∨
      (∃ c, Clif.runLoop B.env (prog I) (M + 1) cs = .trapped c)) :
    (sysS I B f (SemanticStackBound.bud I f) r S).RunGoodL M f (modelOf I f r) := by
  have hf' : (progOf I.results).func? n = some f := hf
  have hn' := hn
  unfold SemanticStackBound.goodN at hn'
  rw [hf'] at hn'
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hn'
  have hbud : SemanticStackBound.bud I f = b := by simp [SemanticStackBound.bud, hb]
  exact runGood_sysS_ofTS hI hbin hB (Clif.Program.func?_some hf).1 M hX
    (SemanticStackBound.budget_ofTS hI B (worldF I f (SemanticStackBound.bud I f) r))
    (by simp [LinkSys.hybrid, hb, hbud]) ho hav hr htr hout

/-- **`RunGoodL` of the system keeping the slots for any program** (under `okBTS`; the budget
`D * M + pbMax I`, #581). -/
theorem runGood_sysS_depthTS {D : List Clif.DataObject} (hI : SemanticStackBound.okBTS I = true)
    (hbin : BinOkWithResults I I.results D file)
    (hB : BaseOk (sys I B)) {f : Clif.Function} (hfm : f ∈ (prog I).funcs) (M : Nat)
    {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (frameDrop (art I f).af + (I.D * M + pbMax I)) r
      args cs.mem)
    {S : BitVec 64 → Prop}
    (hav : OutsideAvoids S f (frameDrop (art I f).af + (I.D * M + pbMax I)) r args cs.mem)
    (hr : ClifRun I B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) (prog I).bare cs)
    (hout : (∃ vals cm, Clif.runLoop B.env (prog I) (M + 1) cs = .returned vals cm) ∨
      (∃ c, Clif.runLoop B.env (prog I) (M + 1) cs = .trapped c)) :
    (sysS I B f (I.D * M + pbMax I) r S).RunGoodL M f (modelOf I f r) :=
  runGood_sysS_ofTS hI hbin hB hfm M hX
    (LinkSys.budget_KT _ (SemanticStackBound.okBTS_sound hI (baseOk_F hB) fun _ h => .inr h))
    rfl ho hav hr htr hout

/-- **`RunGoodL` of the system keeping the slots for the run's peak call depth** (under
`okBTS`; the budget `D * d + pbMax I`, #581). -/
theorem runGood_sysS_peakTS {D : List Clif.DataObject} (hI : SemanticStackBound.okBTS I = true)
    (hbin : BinOkWithResults I I.results D file)
    (hB : BaseOk (sys I B)) {f : Clif.Function} (hfm : f ∈ (prog I).funcs) (F d : Nat)
    {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (frameDrop (art I f).af + (I.D * d + pbMax I)) r
      args cs.mem)
    {S : BitVec 64 → Prop}
    (hav : OutsideAvoids S f (frameDrop (art I f).af + (I.D * d + pbMax I)) r args cs.mem)
    (hr : ClifRun I B f r args cs) (hd : Clif.DepthLe B.env (prog I) d cs)
    (htr : TrapsExplicit (Clif.linkEnvD (prog I) B.env F d) (prog I).bare cs)
    (hout : (∃ vals cm, Clif.runLoop B.env (prog I) (F + 1) cs = .returned vals cm) ∨
      (∃ c, Clif.runLoop B.env (prog I) (F + 1) cs = .trapped c)) :
    (sysS I B f (I.D * d + pbMax I) r S).RunGoodL d f (modelOf I f r) := by
  obtain ⟨hL, hent, hres, hgfree, hbe, hargs, hsav, hrel, hpl⟩ :=
    sysS_entryTS hI hbin hB hfm hX ho hav hr
  exact (backend_correct_program_peakXT (sysS I B f (I.D * d + pbMax I) r S) hL
    ((LinkSys.budget_KT _ (SemanticStackBound.okBTS_sound hI (baseOk_F hB) fun _ h => .inr h)).extImgProduction
      _ _ _) hfm F d
    hent ⟨hres, ((LinkSys.budget_KT _ (SemanticStackBound.okBTS_sound hI (baseOk_F hB)
      fun _ h => .inr h)).extImgProduction _ _ _).2 d f hfm⟩ rfl hgfree (fun a _ => rfl) hbe hargs
    hr.entry hsav hrel hpl hd htr).2 hout

/-- **D4 from the per-state facts** of the system keeping the GOT slots (under `okBTS`). -/
theorem got_of_goodTS {D : List Clif.DataObject} (hI : SemanticStackBound.okBTS I = true)
    (hbin : BinOkWithResults I I.results D file)
    (hgot : GotOk I file) {f : Clif.Function} {r : Arm.ArmState} (hX : (imageOf file).Intact r)
    {g : Clif.Function} (hg : g ∈ (prog I).funcs) (hFg : FnOk I file g) {M Kc : Nat}
    {c t : Arm.ArmState} (hgood : (sysS I B f Kc r (GotSlot I file)).GoodAt M g c t) :
    ∀ rl ∈ (art I g).fb.relocs, rl.type = .adrGotPage →
    Arm.r .PC t = wAt (art I g) (rl.offset + 4) → ∀ (rd G : Nat), rd < 31 → G % 8 = 0 →
    inR (-2 ^ 20) (2 ^ 20) (BinCheck.pageOf G - BinCheck.pageOf (wAt (art I g) rl.offset).toNat) = true →
    fileWord file (wAt (art I g) rl.offset) =
      some (adrpW rd (BinCheck.pageOf G - BinCheck.pageOf (wAt (art I g) rl.offset).toNat)) →
    fileWord file (wAt (art I g) (rl.offset + 4)) = some (ldrW rd rd (G % 4096 / 8)) → ∀ i < 8,
    ¬ RelocAtWithResults I I.results (BitVec.ofNat 64 G + BitVec.ofNat 64 i) ∧
    t.mem (BitVec.ofNat 64 G + BitVec.ofNat 64 i) =
      (Elf.loadMem file (BitVec.ofNat 64 G + BitVec.ofNat 64 i)).getD 0 := by
  intro rl hrl ht hpc rd G hrd h8 hin hw0 hw1 i hi
  obtain ⟨X, K, G', gv, -, hG, himgG, himgS, -⟩ := hgood
  unfold actGoodX at hG
  have hS : GotSlot I file (BitVec.ofNat 64 G + BitVec.ofNat 64 i) :=
    ⟨_, tab_mem (SemanticStackBound.okBTS_names hI) hg, rl, hrl, ht, rd, G, hrd, h8, hin, hw0, hw1,
      i, hi, rfl⟩
  obtain ⟨hkept, hsome, hnr⟩ := hgot _ hS
  refine ⟨hnr, ?_⟩
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
  have himgB : imgB (tabOf I.results) = true :=
    SemanticStackBound.okBTS_global hI ("imgCode: the image reads back", imgB (tabOf I.results))
      (by simp [globalChks])
  by_cases hii : img I (BitVec.ofNat 64 G + BitVec.ofNat 64 i)
  · rw [mem_modelOf_img hii]
    rcases (E2E.BinCheck.img_bytesWithResults hbin himgB hii).2 with h | h
    · rw [hb] at h; cases h; rfl
    · exact absurd h hnr
  · rw [mem_modelOf_not hii]
    exact hX _ _ hkept hb

end Static

/-- **The executable's run from the model-level facts, typed** (`exec_of_runGood` with
`ArmRefinesT`, `ExecRefinesT`, under `okBTS`). -/
theorem exec_of_runGoodTS {I : SemanticStackBound.CompilerInput} {D : List Clif.DataObject}
    {file : ByteArray}
    (hI : SemanticStackBound.okBTS I = true) (hcm : codeMapB I (tabOf I.results) = true)
    (hbin : BinCheck.BinOkWithResults I I.results D file) (hgot : GotOk I file) {B : BaseEnv}
    (hB : BaseOk (sys I B))
    (hH : HooksSim I B) {f : Clif.Function} (hfm : f ∈ (prog I).funcs) {M K : Nat}
    {r : Arm.ArmState} (hX : (imageOf file).Intact r)
    (hent : AbiEntry (art I f).fb (art I f).base (xreg 30 r) (modelOf I f r))
    (hd : ∀ a, (modelOf I f r).mem a ≠ r.mem a → RelocAtWithResults I I.results a)
    {o : Clif.Outcome}
    (hA : ArmRefinesT (art I f).fb (art I f).base (xreg 30 r) ((sys I B).mach M f) (modelOf I f r) o)
    (hgood : ((∃ vals cm, o = .returned vals cm) ∨ (∃ c, o = .trapped c)) →
      (sys I B).RunGoodL M f (modelOf I f r) ∧
        (sysS I B f K r (GotSlot I file)).RunGoodL M f (modelOf I f r)) :
    ExecBytes.ExecRefinesT (art I f).fb (art I f).base (xreg 30 r) (step I B file) r
      (RelocAtWithResults I I.results) o := by
  by_cases hout : (∃ vals cm, o = .returned vals cm) ∨ (∃ c, o = .trapped c)
  · obtain ⟨hG, hgS⟩ := hgood hout
    have hL' := SemanticStackBound.okBTS_sound hI (baseOk_F (F' := img I) hB) fun _ h => h
    have hF : ∀ g ∈ (prog I).funcs, FnOk I file g := fun g hg => fnOkTS hI hbin hL' hg
    have hra : ∀ k < (art I f).fb.words.size,
        xreg 30 (modelOf I f r) ≠ (art I f).base + BitVec.ofNat 64 (4 * k) := by
      simp only [xreg, r_modelOf]; exact hent.raOutside
    refine exec_of_modelNTS hF hfm (by rw [← r_modelOf I f r]; exact hent.pc) hent.raOutside hd
      (runOkSN_of_nTS hI hcm hF hH hfm (runOkN_of_goodTS hI hcm hF
        (fun g hg => ExecBytes.destsInt_of_okT hL' hg)
        hfm hra hG fun M' g t hR he => ?_)) hA
    obtain ⟨c', hRL, -⟩ := reachL_of_reachNTS hI hcm hF hR hfm hG (raNotSecond_top (hF f hfm) hra)
    have hg := reachN_mem hR hfm
    have hRL' : (sysS I B f K r (GotSlot I file)).ReachL M f (modelOf I f r) M' g c' t :=
      LinkSys.reachL_extImg_semantic (SemanticBinary.reachL_F (F' := fun _ => False) hRL)
    exact ⟨insn_of_goodTS hI hcm hF hg (hG _ _ _ _ hRL he), got_of_goodTS hI hbin hgot hX hg (hF g hg)
      (hgS _ _ _ _ hRL' (by rw [mach_sysS]; exact he))⟩
  · cases o with
    | returned vals cm => exact absurd (.inl ⟨vals, cm, rfl⟩) hout
    | trapped c => exact absurd (.inr ⟨c, rfl⟩) hout
    | stuck _ => trivial
    | outOfFuel => trivial

/-- **The binary theorem about the executable's own words, typed** (`binary_correct_exec_proven`
for the typed checks `okBTS`): the executable machine run from `r` refines the whole-program
CLIF run, each returned value in the ABI return register of its class (`ExecRefinesT`). -/
theorem binary_correct_exec_provenTS {I : SemanticStackBound.CompilerInput}
    {D : List Clif.DataObject}
    {file : ByteArray} (hI : SemanticStackBound.okBTS I = true)
    (hcm : codeMapB I (tabOf I.results) = true)
    (hbin : BinCheck.BinOkWithResults I I.results D file) (hgot : GotOk I file) (B : BaseEnv)
    (hB : BaseOk (sys I B))
    (hH : HooksSim I B) {n : String} {f : Clif.Function} (hf : (prog I).func? n = some f)
    (hc : ¬ SemanticStackBound.CycleFrom (SemanticStackBound.Calls I I.results) f) (M : Nat)
    {r : Arm.ArmState}
    {args : List Clif.Val} {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (SemanticStackBound.stackFn I f) r args cs.mem)
    (hav : OutsideAvoids (GotSlot I file) f (SemanticStackBound.stackFn I f) r args cs.mem)
    (hr : ClifRun I B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) (prog I).bare cs) :
    ExecBytes.ExecRefinesT (art I f).fb (art I f).base (xreg 30 r) (step I B file) r
      (RelocAtWithResults I I.results) (Clif.runLoop B.env (prog I) (M + 1) cs) := by
  have hn := (SemanticStackBound.goodN_iffTS hI).2 ⟨f, hf, hc⟩
  obtain ⟨hA, hd, hG⟩ := binary_correct_of_checksXTS hI hbin B hB hn hf M hX ho hr htr
  have hfm := (Clif.Program.func?_some hf).1
  have hL := SemanticStackBound.okBTS_sound hI
    (baseOk_F (F' := worldF I f (SemanticStackBound.bud I f) r) hB) fun _ h => .inr h
  have hfacts := binFacts_of_checksTS hI hbin
  have hro : ∀ a b, BinCheck.roByte I D a = some b → r.mem a = b := fun a b h =>
    hX a b (hfacts.data a b h).1 (hfacts.data a b h).2
  obtain ⟨hent, -⟩ := premisesTS hL hfm hro ho hr
  exact exec_of_runGoodTS hI hcm hbin hgot hB hH hfm hX hent hd hA fun hout =>
    ⟨hG hout, runGood_sysSTS hI hbin hB hn hf M hX ho hav hr htr hout⟩

/-- **`binary_correct_exec_provenTS` for any program**, recursive ones included, with the stack
`frameDrop + (D * M + pbMax)` of the depth-`M` budget (#581: the deepest activation's stack
probes write up to `pbMax` bytes below its frame). -/
theorem binary_correct_exec_depth_provenTS {I : SemanticStackBound.CompilerInput}
    {D : List Clif.DataObject}
    {file : ByteArray} (hI : SemanticStackBound.okBTS I = true)
    (hcm : codeMapB I (tabOf I.results) = true)
    (hbin : BinCheck.BinOkWithResults I I.results D file) (hgot : GotOk I file) (B : BaseEnv)
    (hB : BaseOk (sys I B))
    (hH : HooksSim I B) {n : String} {f : Clif.Function} (hf : (prog I).func? n = some f)
    (M : Nat) {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (frameDrop (art I f).af + (I.D * M + pbMax I)) r
      args cs.mem)
    (hav : OutsideAvoids (GotSlot I file) f (frameDrop (art I f).af + (I.D * M + pbMax I)) r args
      cs.mem)
    (hr : ClifRun I B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) (prog I).bare cs) :
    ExecBytes.ExecRefinesT (art I f).fb (art I f).base (xreg 30 r) (step I B file) r
      (RelocAtWithResults I I.results) (Clif.runLoop B.env (prog I) (M + 1) cs) := by
  have hfacts := binFacts_of_checksTS hI hbin
  obtain ⟨hA, hd, hG⟩ := binary_correct_depthXTS hfacts B hB hf M hX ho hr htr
  have hfm := (Clif.Program.func?_some hf).1
  have hL := SemanticStackBound.okBTS_sound hI (baseOk_F (F' := worldF I f (I.D * M + pbMax I) r) hB)
    fun _ h => .inr h
  have hro : ∀ a b, BinCheck.roByte I D a = some b → r.mem a = b := fun a b h =>
    hX a b (hfacts.data a b h).1 (hfacts.data a b h).2
  obtain ⟨hent, -⟩ := premisesTS hL hfm hro ho hr
  exact exec_of_runGoodTS hI hcm hbin hgot hB hH hfm hX hent hd hA fun hout =>
    ⟨hG hout, runGood_sysS_depthTS hI hbin hB hfm M hX ho hav hr htr hout⟩

/-- **`binary_correct_exec_provenTS` for the run's peak call depth** (L1d), with the stack
`frameDrop + (D * d + pbMax)` (#581). -/
theorem binary_correct_exec_peak_provenTS {I : SemanticStackBound.CompilerInput}
    {D : List Clif.DataObject}
    {file : ByteArray} (hI : SemanticStackBound.okBTS I = true)
    (hcm : codeMapB I (tabOf I.results) = true)
    (hbin : BinCheck.BinOkWithResults I I.results D file) (hgot : GotOk I file) (B : BaseEnv)
    (hB : BaseOk (sys I B))
    (hH : HooksSim I B) {n : String} {f : Clif.Function} (hf : (prog I).func? n = some f)
    (F d : Nat) {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (frameDrop (art I f).af + (I.D * d + pbMax I)) r
      args cs.mem)
    (hav : OutsideAvoids (GotSlot I file) f (frameDrop (art I f).af + (I.D * d + pbMax I)) r args
      cs.mem)
    (hr : ClifRun I B f r args cs) (hd : Clif.DepthLe B.env (prog I) d cs)
    (htr : TrapsExplicit (Clif.linkEnvD (prog I) B.env F d) (prog I).bare cs) :
    ExecBytes.ExecRefinesT (art I f).fb (art I f).base (xreg 30 r) (step I B file) r
      (RelocAtWithResults I I.results) (Clif.runLoop B.env (prog I) (F + 1) cs) := by
  have hfacts := binFacts_of_checksTS hI hbin
  obtain ⟨hA, hdiff, hG⟩ := binary_correct_peakXTS hfacts B hB hf F d hX ho hr hd htr
  have hfm := (Clif.Program.func?_some hf).1
  have hL := SemanticStackBound.okBTS_sound hI (baseOk_F (F' := worldF I f (I.D * d + pbMax I) r) hB)
    fun _ h => .inr h
  have hro : ∀ a b, BinCheck.roByte I D a = some b → r.mem a = b := fun a b h =>
    hX a b (hfacts.data a b h).1 (hfacts.data a b h).2
  obtain ⟨hent, -⟩ := premisesTS hL hfm hro ho hr
  exact exec_of_runGoodTS hI hcm hbin hgot hB hH hfm hX hent hdiff hA fun hout =>
    ⟨hG hout, runGood_sysS_peakTS hI hbin hB hfm F d hX ho hav hr hd htr hout⟩

end SemanticExecBytes

end E2E
