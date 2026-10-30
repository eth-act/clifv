import FV.E2E.ExecGoodRun
import FV.E2E.ExecStaticT
import FV.E2E.LinkArmT
import FV.E2E.LinkCheckT

/-! # Typed copies of `FV.E2E.ExecGoodRun` (S11e5 Stage C, slice 8)

The declarations of `FV.E2E.ExecGoodRun` that depend on the integer link contract
(`LinkSys.Ok`, `LinkSys.Thm`, `okB`, `ArmRefines`), for the typed contract `LinkSys.OkT`
(suffix `T`; `LinkSys.Ok.*` as `LinkSys.OkT.*`). -/

namespace E2E.ExecBytes
open Backend Backend.Proof E2E.LinkCheck E2E.Binary E2E.BinCheck
section Conv
variable {I : LinkInput} {B : BaseEnv} {file : ByteArray}

/-- The lines of a function of the program keep `adrp` pairs adjacent. -/
theorem pairsClosed_artT (hI : okBT I = true) {g : Clif.Function} (hg : g ∈ (prog I).funcs) :
    PairsClosed (art I g).fa.lines.toList := by
  exact emitFunc_pairsClosed (factsT hI hg).pipe.2.2.2.1

/-- The return address of a callee entered at a call of the program is no second word of the
callee: the call's word would be the first word of the callee's pair. -/
theorem raNotSecond_enterT (hI : okBT I = true) (hc : codeMapB I (tabOf I.results) = true)
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
  have hs0 := siteAt_staticT hI hc hF hg hi0
  obtain ⟨j, i1, t1, hj, hi1, ho⟩ := (FnAsm.layout_relocs (hF h hh).layout rl).1 hrl
  have hs1 := siteAt_staticT hI hc hF hh (insnAt_of_line (hF h hh) hj)
  rw [ho, ← hpcu, hs0, siteOf_pairFirst hi1 ht] at hs1
  exact hr0 (Option.some.inj hs1)

/-- **The states of `ReachN` are states of `ReachL`**, of an activation entered at an entry whose
return address is no second word. -/
theorem reachL_of_reachNT (hI : okBT I = true) (hc : codeMapB I (tabOf I.results) = true)
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
      (raNotSecond_enterT hI hc hF hf hG.prog hcall)
    exact ⟨c', .nest hj hcall herr hR', hs'⟩

/-- The calls through a register of a function of a linked system with `Ok` are through integer
vregs (`LinkSys.OkT.blrRegs`). -/
theorem destsInt_of_okT {L : LinkSys} (hL : L.OkT) {g : Clif.Function} (hg : g ∈ L.P.funcs) :
    (L.A g).vcp.DestsInt := by
  intro b vb k info hb hi r hd
  obtain ⟨t, Lc, Dc, hshape, -⟩ := hL.blrRegs g hg info ⟨b, vb, k, hb, hi⟩ (fun n => by rw [hd]; simp)
  rw [hshape] at hd
  simp only [CallDest.reg.injEq] at hd
  exact ⟨t, hd.symm⟩

/-- **`StepOkD` from the register-level per-state facts** and the memory-read facts. -/
theorem stepOkD_of_goodT (hI : okBT I = true) (hc : codeMapB I (tabOf I.results) = true)
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
      obtain ⟨k', y, t', rfl, hy, hy'⟩ := pairsClosed_artT hI hg _ _ _ hj2 hsec
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
    refine ⟨hxz, ?_, symAddr_of_blrToT hI hc hg hh' hsi hd hbt⟩
    rw [← hpc]
    exact hfw.trans (congrArg some hrd.symm)

/-- **`RunOkN` from the register-level per-state facts** (`RunGoodL`) and the memory-read
factsT (`RunReadsN`), for an activation whose return address is outside its code. -/
theorem runOkN_of_goodT (hI : okBT I = true) (hc : codeMapB I (tabOf I.results) = true)
    (hF : ∀ g ∈ (prog I).funcs, FnOk I file g) (hD : ∀ g ∈ (prog I).funcs, (art I g).vcp.DestsInt)
    {M : Nat} {f : Clif.Function}
    (hf : f ∈ (prog I).funcs) {c : Arm.ArmState}
    (hra : ∀ k < (art I f).fb.words.size, xreg 30 c ≠ (art I f).base + BitVec.ofNat 64 (4 * k))
    (hgood : (sys I B).RunGoodL M f c) (hreads : RunReadsN I B file M f c) :
    RunOkN I B file M f c := fun M' g t hR he => by
  obtain ⟨c', hRL, hs⟩ := reachL_of_reachNT hI hc hF hR hf hgood (raNotSecond_top (hF f hf) hra)
  exact stepOkD_of_goodT hI hc hF hD (reachN_mem hR hf) (hgood _ _ _ _ hRL he) hs he
    (hreads _ _ _ hR he)
end Conv
end E2E.ExecBytes
