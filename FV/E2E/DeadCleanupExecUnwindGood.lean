import FV.E2E.DeadCleanupExecUnwind
import FV.E2E.DeadCleanupExecGoodReads
import FV.E2E.DeadCleanupExecGot
import FV.E2E.LinkArmUGood

/-!
# The per-state facts of the executable machine with unwinding, from the register level (S10g, #404)

`RunOkU` (`FV/E2E/DeadCleanupExecUnwind.lean`), the per-state hypothesis of the simulation of
the linked machine with unwinding by the executable machine with unwinding (`act_simU`), from the
per-state facts of the linked machine's run with unwinding (`LinkSysU.RunGoodLU`, exported by the
linking statement `ThmGU`), as `runOkN_of_good` (`FV/E2E/DeadCleanupExecGoodRun.lean`) does for
the machine without unwinding:

* `runGoodLU_uSys`: `RunGoodLU` of a linked program with unwinding of the input is `uSys`'s.
* `reachLU_of_reachU`: the states of `ReachU` are states of `ReachLU`, of an activation entered at
  an entry whose return address is no second word of an `adrp` pair.
* `stepOkU_of_good`: `StepOkU` at a state with the per-state facts (`GoodAtU`): the static facts
  (`siteAt_static`, `plain_static`), D1 (`GoodX.next`/`RaiseXF.next`), D2 (`GoodX.reads`; a
  raising call is hooked), D4 (no GOT slot), the hooks (`HooksSim`), a `blr`'s facts, and the save
  slots that a raising call's frame unwinding reads in the activation's frame (`FrameOkU`), off the
  code; and a step leaving the frame by unwinding lands on the activation's return
  (`RaiseXF.exit`).
* `runOkU_of_good`: `RunOkU` from `RunGoodLU`.
-/

namespace E2E.DeadCleanupExecBytes
set_option autoImplicit false

open Backend Backend.Proof E2E.LinkCheck E2E.DeadCleanupBinary E2E.BinCheck

section Good

variable {I : LinkInput} {B : BaseEnv} {file : ByteArray} {U : LinkSysU}

/-- **`RunGoodLU` of a linked program with unwinding of the input is `uSys`'s** (the exterior
`F` plays no role in the machine nor in the per-state facts). -/
theorem runGoodLU_uSys {F : BitVec 64 → Prop} (hU : U.toLinkSys = LinkSys.ofInputCleanup I B F)
    {M : Nat} {f : Clif.Function} {c : Arm.ArmState} (h : U.RunGoodLU M f c) :
    (uSys I B U).RunGoodLU M f c := by
  have hl := layer_uSys hU
  have hm := machU_uSys hU
  have hh : ∀ M, U.hooksU M = (uSys I B U).hooksU M := fun M => by
    simp only [LinkSysU.hooksU, hl M]
  have hu : ∀ M, U.UU M = (uSys I B U).UU M := fun M => by
    simp only [LinkSysU.UU, hl M]
  obtain ⟨L0, Ub, envX, XRb, crunX⟩ := U
  change L0 = _ at hU
  subst hU
  have hR : ∀ {M f c M' g c' t}, (uSys I B ⟨LinkSys.ofInputCleanup I B F, Ub, envX, XRb, crunX⟩).ReachLU
      M f c M' g c' t →
      (⟨LinkSys.ofInputCleanup I B F, Ub, envX, XRb, crunX⟩ : LinkSysU).ReachLU M f c M' g c' t := by
    intro M f c M' g c' t h
    induction h with
    | act hj =>
      rw [← hm] at hj ⊢
      exact .act hj
    | nest hj hc herr _ ih =>
      rw [← hm] at hj hc herr ih
      exact .nest hj hc herr ih
  intro M' g c' t hr he
  obtain ⟨X, XR, K, G, gv, heq, hg, hi⟩ := h M' g c' t (hR hr) (by rw [hm]; exact he)
  rw [hh, hu, hm] at heq
  rw [hh, hu] at hg
  exact ⟨X, XR, K, G, gv, heq, hg, hi⟩

/-- The program at a state with the per-state facts with unwinding. -/
theorem prog_of_actGoodXU {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    {base : BitVec 64} {s0 : Arm.ArmState} {X : ExtSem} {H : ArmHooks} {XR : XRaise}
    {Uh : Unw.UnwHooks} {T : Unw.FnTables} {K : Nat} {G : BitVec 64 → Prop}
    {gv : Nat → String → Prop} {u : Arm.ArmState}
    (h : actGoodXU vcp rf af fa fb base s0 X H XR Uh T K G gv u) : u.program = fb.program base := by
  rcases h with ⟨g, -⟩ | ⟨r, -⟩
  · exact g.prog
  · exact r.prog

/-- **The states of `ReachU` are states of `ReachLU`** of `uSys`, of an activation entered at an
entry whose return address is no second word. -/
theorem reachLU_of_reachU (hI : okBCleanup I = true) (hc : codeMapB I (tabOf I.resultsCleanup) = true)
    (hF : ∀ g ∈ (prog I).funcs, FnOk I file g) {M : Nat} {f : Clif.Function} {c : Arm.ArmState}
    {M' : Nat} {g : Clif.Function} {c' t : Arm.ArmState} (h : ReachU I B U M f c M' g c' t) :
    f ∈ (prog I).funcs → (uSys I B U).RunGoodLU M f c → ¬ Second I f (xreg 30 c) →
    (uSys I B U).ReachLU M f c M' g c' t ∧ ¬ Second I g (xreg 30 c') := by
  induction h with
  | act hj => exact fun _ _ hs => ⟨.act hj, hs⟩
  | nest hj hcall herr _ ih =>
    intro hf hrun _
    have hu := hrun _ _ _ _ (.act hj) (by rw [runX_succ'] at herr; exact herr)
    obtain ⟨X, XR, K, G, gv, -, hG, -⟩ := hu
    obtain ⟨hR', hs'⟩ := ih (callee_mem hcall)
      (fun _ _ _ _ hr he => hrun _ _ _ _ (.nest hj hcall herr hr) he)
      (raNotSecond_enter hI hc hF hf (prog_of_actGoodXU hG) hcall)
    exact ⟨.nest hj hcall herr hR', hs'⟩

/-- The machine with unwinding steps as `ArmStepX` when the callee of the call line (if any)
does not raise. -/
theorem armStepU_desc {X : ExtSem} {H : ArmHooks} {Uh : Unw.UnwHooks} {T : Unw.FnTables}
    {fa : FnAsm} {s : Arm.ArmState} (h : ∀ d, callDescAt fa s = some d → Uh.raise d s = none) :
    Unw.ArmStepU X H Uh T fa s = ArmStepX X H fa s := by
  unfold Unw.ArmStepU
  unfold callDescAt at h
  dsimp only
  split
  · rename_i n heq
    simp only [heq] at h
    simp only [h (some n) rfl]
    unfold ArmStepX; simp only [heq]
  · rename_i r heq
    simp only [heq] at h
    simp only [h none rfl]
    unfold ArmStepX; simp only [heq]
  · rfl

theorem nextOk_imp {R : RL} {u v w : Arm.ArmState} (h : R.NextOk u v) (e : v = w) :
    R.NextOk u w := e ▸ h

/-- **D1 from the register-level next-pc fact** (`RL.NextOk`) at a state of an activation of `g`
entered at `c` whose return address is no second word. -/
theorem cf_of_next (hI : okBCleanup I = true) (hF : ∀ g ∈ (prog I).funcs, FnOk I file g)
    {g : Clif.Function} (hg : g ∈ (prog I).funcs) {c t v : Arm.ArmState}
    (hs : ¬ Second I g (xreg 30 c)) (he : Arm.r .ERR v = .None)
    (hn : Arm.r .ERR v ≠ .None ∨ Arm.r .PC v = xreg 30 c ∨ Arm.r .PC v = Arm.r .PC t + 4 ∨
      ∃ j, Arm.r .PC v = (art I g).base +
          BitVec.ofNat 64 (lineOffset (art I g).fa.lines.toList (j + 1)) ∧
        ∀ x tt, (art I g).fa.lines.toList[j]? = some (.ins x tt) → x.pairFirst = false) :
    ∀ rl ∈ (art I g).fb.relocs, (rl.type = .adrGotPage ∨ rl.type = .adrPrelPgHi21) →
      Arm.r .PC v = wAt (art I g) (rl.offset + 4) → Arm.r .PC t = wAt (art I g) rl.offset := by
  have hFg := hF g hg
  have hfit := hFg.fits
  have hsum := layout_sum hFg.layout
  intro rl hrl ht hpcv
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

/-- **`StepOkU` from the per-state facts with unwinding** (`GoodAtU`) at a state of an activation
of `g` entered at `c` whose return address is no second word, and the return of a step leaving
the frame by unwinding. -/
theorem stepOkU_of_good (hI : okBCleanup I = true) (hc : codeMapB I (tabOf I.resultsCleanup) = true)
    (hF : ∀ g ∈ (prog I).funcs, FnOk I file g) (hH : HooksSim I B)
    (hgot : ∀ a, ¬ GotSlot I file a) (hD : ∀ g ∈ (prog I).funcs, (art I g).vcp.DestsInt)
    {M : Nat} {g : Clif.Function} (hg : g ∈ (prog I).funcs) {c t : Arm.ArmState}
    (hgood : (uSys I B U).GoodAtU M g c t) (hs : ¬ Second I g (xreg 30 c))
    (he : Arm.r .ERR ((uSys I B U).machU M g t) = .None) :
    StepOkU I B file U M g t ∧
      (UnwExit ((uSys I B U).UU M) (art I g).tables (art I g).fa t →
        Returned (art I g) c ((uSys I B U).machU M g t)) := by
  obtain ⟨X, XR, K, G, gv, heq, hG, himg, -, hgf, hba⟩ := hgood
  have hFg := hF g hg
  obtain ⟨lm, hm⟩ := FnAsm.layout_labelOffsets hFg.layout
  have hstep : Unw.ArmStepU X ((uSys I B U).hooksU M) ((uSys I B U).UU M) (art I g).tables
      (art I g).fa t = (uSys I B U).machU M g t := congrFun heq t
  -- the line at the pc and the facts common to both kinds of states
  obtain ⟨x, j, tt, hj, hpc, herr, hprog, hcall, hblr, hcf, hnext⟩ : ∃ x j tt,
      (art I g).fa.lines.toList[j]? = some (.ins x tt) ∧
      Arm.r .PC t = (art I g).base + BitVec.ofNat 64 (lineOffset (art I g).fa.lines.toList j) ∧
      Arm.r .ERR t = .None ∧ t.program = (art I g).fb.program (art I g).base ∧
      (((∃ n, x = .bl n) ∨ ∃ r, x = .blr r) → x.hooked = true) ∧
      (∀ r, x = .blr r → ((art I g).vcp.DestsInt → r ≠ .xzr) ∧
        ∀ k w, (art I g).fb.words[k]? = some w →
          Arm.read_mem_bytes 4 ((art I g).base + BitVec.ofNat 64 (4 * k)) t = w) ∧
      (x.tlsTail = false) ∧
      (Arm.r .ERR ((uSys I B U).machU M g t) ≠ .None ∨
        Arm.r .PC ((uSys I B U).machU M g t) = xreg 30 c ∨
        Arm.r .PC ((uSys I B U).machU M g t) = Arm.r .PC t + 4 ∨
        ∃ j, Arm.r .PC ((uSys I B U).machU M g t) = (art I g).base +
            BitVec.ofNat 64 (lineOffset (art I g).fa.lines.toList (j + 1)) ∧
          ∀ x tt, (art I g).fa.lines.toList[j]? = some (.ins x tt) → x.pairFirst = false) := by
    rcases hG with ⟨g0, hnr⟩ | ⟨r0, -⟩
    · obtain ⟨x, ⟨j, tt, hj, hpc⟩, htl⟩ := g0.line
      have hn := nextOk_imp g0.next
        ((armStepU_desc (X := X) (H := (uSys I B U).hooksU M) (T := (art I g).tables) hnr).symm.trans
          hstep)
      unfold RL.NextOk at hn
      exact ⟨x, j, tt, hj, hpc, g0.err, g0.prog, fun h => by
        rcases h with ⟨n, rfl⟩ | ⟨r, rfl⟩ <;> rfl,
        fun r hr => by subst hr; exact g0.blr r ⟨j, tt, hj, hpc⟩, htl, hn⟩
    · obtain ⟨x, d, obj, t', ⟨j, tt, hj, hpc⟩, hd, -⟩ := r0.raise
      have hn := nextOk_imp r0.next hstep
      unfold RL.NextOk at hn
      refine ⟨x, j, tt, hj, hpc, r0.err, r0.prog, fun _ => ?_,
        fun r hr => by subst hr; exact r0.blr r ⟨j, tt, hj, hpc⟩, ?_, hn⟩
      · rcases hd with ⟨n, rfl, -⟩ | ⟨r, rfl, -⟩ <;> rfl
      · rcases hd with ⟨n, rfl, -⟩ | ⟨r, rfl, -⟩ <;> rfl
  have hins : insnAt (art I g).fa (art I g).base (Arm.r .PC t) = some x := by
    rw [hpc]; exact insnAt_of_line hFg hj
  refine ⟨⟨herr, hprog, ⟨x, hins, siteAt_static hI hc hF hg hins, Insn.reloc_of_tlsTail hcf⟩,
    cf_of_next hI hF hg hs he hnext, ?_, fun d e _ hs' => hH.call d t e hs',
    fun tmp _ n e _ hs' => hH.tls n tmp t e hs', ?_, ?_,
    fun i hi hr => plain_static hI hc hF hg hi hr, ?_⟩, ?_⟩
  · -- D2
    intro i hi hh a ha e hsim
    rw [hins] at hi
    cases hi
    rcases hG with ⟨g0, -⟩ | ⟨r0, -⟩
    · refine exec_sim a hsim fun p hp k hk hR => ?_
      have hrdA := g0.reads
      have hr : x.reloc? = none := (Insn.reloc_of_tlsTail hcf).resolve_right (by rw [hh]; decide)
      obtain ⟨w, hw, hfw⟩ := fileWord_plain hFg hm hj hr
      have hpcw : Arm.r .PC t = wAt (art I g) (lineOffset (art I g).fa.lines.toList j) := hpc
      rw [hpcw, hfw, Option.bind_some] at ha
      obtain ⟨a', ha', hd⟩ := Insn.decode_encode hw
      rw [ha] at hd
      cases hd
      have hrd := hrdA j x tt hj hpcw hh a
        (by simpa [RL.envL, RL.L, hm, Except.toOption] using ha') p hp k hk
      rcases hrd with hnG | ⟨j', tg, bs, hj', q, hq, he'⟩ | ⟨j', d', hj', q, hq, he'⟩
      · exact hnG (himg _ (relocAt_img hI hF hR))
      · rw [he'] at hR
        exact word_static hI hc hF hg hj' q hq hR
      · rw [he'] at hR
        exact data_static hI hc hF hg hj' q hq hR
    · obtain ⟨x', d, obj, t', ⟨j', tt', hj', hpc'⟩, hd, -⟩ := r0.raise
      have hx' : x' = x := by
        have h1 : insnAt (art I g).fa (art I g).base (Arm.r .PC t) = some x' := by
          rw [hpc']; exact insnAt_of_line hFg hj'
        rw [hins] at h1
        exact (Option.some.inj h1).symm
      subst hx'
      rcases hd with ⟨n, rfl, -⟩ | ⟨r, rfl, -⟩ <;> cases hh
  · -- D4: no GOT slot
    intro rl hrl ht _ rd G0 hrd hG8 hin h1 h2 i hi
    exact absurd ⟨(g, art I g), tab_mem (okBCleanup_names hI) hg, rl, hrl, ht, rd, G0, hrd, hG8,
      hin, h1, h2, 0, by decide, rfl⟩ (hgot (BitVec.ofNat 64 G0 + BitVec.ofNat 64 0))
  · -- a `blr`
    intro xr h' hx ht
    rw [hins] at hx
    cases hx
    obtain ⟨hxz, hcode⟩ := hblr xr rfl
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
    obtain ⟨info, tv, hsi, hd, hbt⟩ := hba xr h' hins ht
    have hh' : h' ∈ (prog I).funcs := by
      obtain ⟨a, -, ha⟩ := Option.bind_eq_some_iff.1 ht
      exact List.mem_of_find?_eq_some ha
    refine ⟨hxz, ?_, symAddr_of_blrTo hI hc hg hh' hsi hd hbt⟩
    rw [hpc]
    exact hfw.trans (congrArg some hrd.symm)
  · -- the save slots a raising call's frame unwinding reads
    intro d obj t' hd hr cfa hcfa p hp k hk hR
    rcases hG with ⟨-, hnr⟩ | ⟨-, hfr⟩
    · rw [hnr d hd] at hr
      cases hr
    · exact hgf _ (relocAt_img hI hF hR) (hfr d obj t' hd hr cfa hcfa p hp k hk)
  · -- a step leaving the frame by unwinding lands on the return
    rintro ⟨d, obj, t', hd, hr, hp⟩
    rcases hG with ⟨-, hnr⟩ | ⟨r0, -⟩
    · rw [hnr d hd] at hr
      cases hr
    · obtain ⟨hret, hprog'⟩ := r0.exit hp
      exact ⟨by rw [← hstep]; exact hret.pc, by rw [← hstep]; exact hret.err,
        by rw [← hstep]; exact hprog', by rw [← hstep]; exact hret.sp⟩

/-- **`RunOkU` from the per-state facts of the linked machine's run with unwinding**
(`RunGoodLU` of `uSys`), for an activation whose return address is outside its code. -/
theorem runOkU_of_good (hI : okBCleanup I = true) (hc : codeMapB I (tabOf I.resultsCleanup) = true)
    (hF : ∀ g ∈ (prog I).funcs, FnOk I file g) (hH : HooksSim I B)
    (hgot : ∀ a, ¬ GotSlot I file a) (hD : ∀ g ∈ (prog I).funcs, (art I g).vcp.DestsInt)
    {M : Nat} {f : Clif.Function} (hf : f ∈ (prog I).funcs) {c : Arm.ArmState}
    (hra : ∀ k < (art I f).fb.words.size, xreg 30 c ≠ (art I f).base + BitVec.ofNat 64 (4 * k))
    (hgood : (uSys I B U).RunGoodLU M f c) : RunOkU I B file U M f c := fun M' g c' t hR he => by
  obtain ⟨hRL, hs⟩ := reachLU_of_reachU hI hc hF hR hf hgood (raNotSecond_top (hF f hf) hra)
  exact stepOkU_of_good hI hc hF hH hgot hD (hR.mem hf) (hgood _ _ _ _ hRL he) hs he

end Good

end E2E.DeadCleanupExecBytes
