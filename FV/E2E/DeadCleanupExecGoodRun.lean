import FV.E2E.DeadCleanupBinaryGood
import FV.E2E.DeadCleanupExecRunN
import FV.E2E.PairLines
import FV.E2E.ExecGoodRun
import FV.E2E.DeadCleanupBinary
import FV.E2E.DeadCleanupBinCheck

namespace E2E.DeadCleanupExecBytes
set_option autoImplicit false

open Backend Backend.Proof E2E.LinkCheck E2E.DeadCleanupBinary E2E.BinCheck

/-- **The memory-read facts of a model state** (`StepOkD`'s D2 `insn` and D4 `got`). -/
structure StepOkR (I : LinkInput) (B : BaseEnv) (file : ByteArray) (M : Nat) (g : Clif.Function)
    (m : Arm.ArmState) : Prop where
  /-- D2 -/
  insn : ∀ i, insnAt (art I g).fa (art I g).base (Arm.r .PC m) = some i → i.hooked = false →
    ∀ a, (fileWord file (Arm.r .PC m)).bind Arm.decode_raw_inst = some a →
    ∀ e, Sim I m e → Sim I (Arm.exec_inst a m) (Arm.exec_inst a e)
  /-- D4 -/
  got : ∀ rl ∈ (art I g).fb.relocs, rl.type = .adrGotPage →
    Arm.r .PC m = wAt (art I g) (rl.offset + 4) → ∀ (rd G : Nat), rd < 31 → G % 8 = 0 →
    inR (-2 ^ 20) (2 ^ 20) (pageOf G - pageOf (wAt (art I g) rl.offset).toNat) = true →
    fileWord file (wAt (art I g) rl.offset) =
      some (adrpW rd (pageOf G - pageOf (wAt (art I g) rl.offset).toNat)) →
    fileWord file (wAt (art I g) (rl.offset + 4)) = some (ldrW rd rd (G % 4096 / 8)) → ∀ i < 8,
    ¬ E2E.DeadCleanupBinCheck.RelocAt I (BitVec.ofNat 64 G + BitVec.ofNat 64 i) ∧
    m.mem (BitVec.ofNat 64 G + BitVec.ofNat 64 i) =
      (Elf.loadMem file (BitVec.ofNat 64 G + BitVec.ofNat 64 i)).getD 0

/-- **The memory-read hypothesis**: `StepOkR` at the states of `ReachN` whose step ends without
error. -/
def RunReadsN (I : LinkInput) (B : BaseEnv) (file : ByteArray) (M : Nat) (f : Clif.Function)
    (c : Arm.ArmState) : Prop :=
  ∀ M' g t, ReachN I B M f c M' g t → Arm.r .ERR ((sys I B).mach M' g t) = .None →
    StepOkR I B file M' g t

section Conv

variable {I : LinkInput} {B : BaseEnv} {file : ByteArray}

theorem Insn.reloc_of_tlsTail {x : Insn} (h : x.tlsTail = false) :
    x.reloc? = none ∨ x.hooked = true := by
  cases x <;> simp_all [Insn.tlsTail, Insn.reloc?, Insn.hooked]

theorem Insn.pairSecond_of_reloc {i : Insn} {ty : RelocType} {s : String} {a : Int}
    (h : i.reloc? = some (ty, s, a)) (ht : ty = .ld64GotLo12Nc ∨ ty = .addAbsLo12Nc) :
    i.pairSecond = true := by
  cases i <;> simp only [Insn.reloc?, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at h <;>
    first | rfl | (obtain ⟨rfl, -⟩ := h; rcases ht with h' | h' <;> cases h')

/-- The lines of a function of the program keep `adrp` pairs adjacent. -/
theorem pairsClosed_art (hI : okBCleanup I = true) {g : Clif.Function} (hg : g ∈ (prog I).funcs) :
    PairsClosed (art I g).fa.lines.toList := by
  exact emitFunc_pairsClosed (factsCleanup hI hg).pipe.2.2.2.1

/-- The top entry's return address, outside the code, is no second word. -/
theorem raNotSecond_top {f : Clif.Function} (hF : FnOk I file f) {c : Arm.ArmState}
    (hra : ∀ k < (art I f).fb.words.size, xreg 30 c ≠ (art I f).base + BitVec.ofNat 64 (4 * k)) :
    ¬ Second I f (xreg 30 c) := fun hs => by
  obtain ⟨k, hk, he⟩ := second_code hF hs
  exact hra k hk he

/-- The return address of a callee entered at a call of the program is no second word of the
callee: the call's word would be the first word of the callee's pair. -/
theorem raNotSecond_enter (hI : okBCleanup I = true) (hc : codeMapB I (tabOf I.resultsCleanup) = true)
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

/-- **The states of `ReachN` are states of `ReachL`**, of an activation entered at an entry whose
return address is no second word. -/
theorem reachL_of_reachN (hI : okBCleanup I = true) (hc : codeMapB I (tabOf I.resultsCleanup) = true)
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

/-- The calls through a register of a function of a linked system with `Ok` are through integer
vregs (`LinkSys.Ok.blrRegs`). -/
theorem destsInt_of_ok {L : LinkSys} (hL : L.Ok) {g : Clif.Function} (hg : g ∈ L.P.funcs) :
    (L.A g).vcp.DestsInt := by
  intro b vb k info hb hi r hd
  obtain ⟨t, Lu, Ld, he, -⟩ := hL.blrRegs g hg info ⟨b, vb, k, hb, hi⟩ (fun n => by rw [hd]; simp)
  subst he
  simp only [CallDest.reg.injEq] at hd
  exact ⟨t, hd.symm⟩

/-- **`StepOkD` from the register-level per-state facts** and the memory-read facts. -/
theorem stepOkD_of_good (hI : okBCleanup I = true) (hc : codeMapB I (tabOf I.resultsCleanup) = true)
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

/-- **`RunOkN` from the register-level per-state facts** (`RunGoodL`) and the memory-read
facts (`RunReadsN`), for an activation whose return address is outside its code. -/
theorem runOkN_of_good (hI : okBCleanup I = true) (hc : codeMapB I (tabOf I.resultsCleanup) = true)
    (hF : ∀ g ∈ (prog I).funcs, FnOk I file g) (hD : ∀ g ∈ (prog I).funcs, (art I g).vcp.DestsInt)
    {M : Nat} {f : Clif.Function}
    (hf : f ∈ (prog I).funcs) {c : Arm.ArmState}
    (hra : ∀ k < (art I f).fb.words.size, xreg 30 c ≠ (art I f).base + BitVec.ofNat 64 (4 * k))
    (hgood : (sys I B).RunGoodL M f c) (hreads : RunReadsN I B file M f c) :
    RunOkN I B file M f c := fun M' g t hR he => by
  obtain ⟨c', hRL, hs⟩ := reachL_of_reachN hI hc hF hR hf hgood (raNotSecond_top (hF f hf) hra)
  exact stepOkD_of_good hI hc hF hD (reachN_mem hR hf) (hgood _ _ _ _ hRL he) hs he
    (hreads _ _ _ hR he)

end Conv

/-- **`binary_correct_exec_static` with the per-state facts of the register-level proof**: under
the premises of `binary_correct_of_checks_acyclic`, the outside-code contract `HooksSim`, the
code map check `codeMapB` and only the memory-read facts `RunReadsN` (D2, D4) of the model's run,
the executable machine run from `r` refines the whole-program CLIF run. -/
theorem binary_correct_exec_of_reads {I : LinkInput} {D : List Clif.DataObject}
    {file : ByteArray} (hI : okBCleanup I = true) (hcm : codeMapB I (tabOf I.resultsCleanup) = true)
    (hbin : DeadCleanupBinCheck.BinOk I D file) (B : BaseEnv) (hB : BaseOk (sys I B)) (hH : HooksSim I B)
    {n : String} {f : Clif.Function} (hf : (prog I).func? n = some f)
    (hc : ¬ DeadCleanupStackBound.CycleFrom (DeadCleanupStackBound.Calls I I.resultsCleanup) f) (M : Nat) {r : Arm.ArmState}
    {args : List Clif.Val} {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (DeadCleanupStackBound.stackFn I f) r args cs.mem)
    (hr : ClifRun I B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) (prog I).bare cs)
    (hreads : RunReadsN I B file M f (modelOf I f r)) :
    ExecRefines (art I f).fb (art I f).base (xreg 30 r) (step I B file) r (E2E.DeadCleanupBinCheck.RelocAt I)
      (Clif.runLoop B.env (prog I) (M + 1) cs) := by
  have hn := (DeadCleanupStackBound.goodN_iff hI).2 ⟨f, hf, hc⟩
  obtain ⟨-, -, hG⟩ := binary_correct_of_checksX hI hbin B hB hn hf M hX ho hr htr
  by_cases hout : (∃ vals cm, Clif.runLoop B.env (prog I) (M + 1) cs = .returned vals cm) ∨
      (∃ c, Clif.runLoop B.env (prog I) (M + 1) cs = .trapped c)
  · have hfm := (Clif.Program.func?_some hf).1
    have hB' : BaseOk (LinkSys.ofInputCleanup I B (worldF I f (DeadCleanupStackBound.bud I f) r)) := baseOk_F hB
    have hL := okBCleanup_sound hI hB' fun _ h => .inr h
    have hfacts := binFacts_of_checks hI hbin
    have hro : ∀ a b, BinCheck.roByte I D a = some b → r.mem a = b := fun a b h =>
      hX a b (hfacts.data a b h).1 (hfacts.data a b h).2
    obtain ⟨hent, -⟩ := premises hL hfm hro ho hr
    have hL' := okBCleanup_sound hI (baseOk_F (F' := img I) hB) fun _ h => h
    have hF : ∀ g ∈ (prog I).funcs, FnOk I file g := fun g hg => fnOk hI hbin hL' hg
    have hra : ∀ k < (art I f).fb.words.size,
        xreg 30 (modelOf I f r) ≠ (art I f).base + BitVec.ofNat 64 (4 * k) := by
      simp only [xreg, r_modelOf]; exact hent.raOutside
    exact binary_correct_exec_staticN hI hcm hbin B hB hH hf hc M hX ho hr htr
      (runOkN_of_good hI hcm hF (fun g hg => destsInt_of_ok hL' hg) hfm hra (hG hout) hreads)
  · cases h : Clif.runLoop B.env (prog I) (M + 1) cs with
    | returned vals cm => exact absurd (.inl ⟨vals, cm, h⟩) hout
    | trapped c => exact absurd (.inr ⟨c, h⟩) hout
    | stuck _ => trivial
    | outOfFuel => trivial

end E2E.DeadCleanupExecBytes
