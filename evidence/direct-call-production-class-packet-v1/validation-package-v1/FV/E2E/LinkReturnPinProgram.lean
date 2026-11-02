import FV.E2E.LinkReturnPinCallbacks
import FV.Backend.Proof.SretStable

namespace Clif
private theorem step_done_tys_with_frame {P Q : Program} (hP : ∀ g ∈ P.funcs, LinkFree g) {env : Env} {s : State}
    {v : List Val} {m : Mem} (hI : LInv P s) (h : step env Q s = .done v m) :
    s.callers = [] ∧ v.map (·.ty) = AbiParam.tys s.frame.func.sig.returns := by
  rcases step_shape s with ⟨fn, args, et, hb, ht⟩ | ⟨callee, args, et, hb, ht⟩ |
    ⟨st, rest, sig, callee, args, hb, hi⟩ | hci
  · rw [step_try env Q s hb ht] at h
    obtain ⟨⟨n, b, bc⟩, -, h⟩ := ofRes_eq_done h
    obtain ⟨⟨ext, vals⟩, -, h⟩ := ofRes_eq_done h
    exact absurd h callCont_ne_done
  · rw [step_tryInd env Q s hb ht] at h
    obtain ⟨⟨n, b, bc⟩, -, h⟩ := ofRes_eq_done h
    obtain ⟨⟨d, a, w⟩, -, h⟩ := ofRes_eq_done h
    exact absurd h indCont_ne_done
  · rw [step_ind env Q s hb hi] at h
    obtain ⟨⟨d, a, w⟩, -, h⟩ := ofRes_eq_done h
    exact absurd h indCont_ne_done
  · rw [Opt.step_eq_lift env Q s hci] at h
    cases hl : Opt.lstep s.frame s.mem with
    | ret vals =>
      rw [hl] at h
      obtain ⟨hc, rfl, ht⟩ := returnValues_done h
      exact ⟨hc, ht⟩
    | call ext vals rs rest => rw [hl] at h; exact absurd h callCont_ne_done
    | tail ext vals => exact absurd hl (lstep_ne_tail hP hI.1)
    | next fr1 m1 => rw [hl] at h; cases h
    | trap c => rw [hl] at h; cases h
    | stuck m => rw [hl] at h; cases h


end Clif

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver Clif Opt
variable {modes : Clif.Function → ReturnPinMode}
set_option autoImplicit false
set_option Elab.async false
namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat} {modes : Clif.Function → ReturnPinMode}

/-- Physical return selection leaves the existing TLS hook contract unchanged. -/
theorem tlsOk_hooks_mode {F F' : BitVec 64 → Prop} {K M : Nat} {g : Clif.Function}
    (h : TlsOk F K L.Xb L.Hb) : TlsOk F K (L.XMode modes κ M g F') (L.hooks M) := by
  cases M <;> exact ⟨h.pc,h.seq,h.flags⟩

theorem actInv_step_return_pins (hL : L.OkReturnPins modes) [hR : L.CrunOk] {M : Nat} {g : Clif.Function} (hg : g ∈ L.P.funcs) {c : BitVec 64}
    {s s1 : Clif.State} (hJ : L.ActInv g c s)
    (hs : Clif.step (Clif.linkEnvR L.P L.base (L.crun M)) L.P.bare s = .next s1) :
    L.ActInv g c s1 := by
  obtain ⟨hI, hc, hpl⟩ := hJ
  have hPf : ∀ f ∈ (L.P.only g).funcs, Clif.LinkFree f := fun f hf => by
    simp only [Clif.Program.only, List.mem_cons, List.not_mem_nil, or_false] at hf
    subst hf; exact hL.free f hg
  have hc1 := Clif.step_bare_callers hPf hI.1 hc hs
  refine ⟨(Clif.step_next_linv hPf hI hs (fun _ h => by simp at h)).1, hc1, fun hN => ?_⟩
  obtain ⟨sps, hp⟩ := hpl hN
  refine ⟨sps, ?_⟩
  rcases Clif.step_next_cases hPf hI hs with ⟨-, -, ⟨hpl', -⟩ | ⟨n, G, vals, rv, hG, hr⟩⟩ |
    ⟨cc, hcc, -⟩ | ⟨cc, hcc, -⟩
  · rw [hpl', hp]
  · rw [Clif.linkEnvR_keepsPlace0 (hR.runs M) hL.free (hL.baseKeepsPlace hN) n G hG vals s.mem rv
      s1.mem (fun pl h => by rw [hp] at h; cases h; rfl) hr, hp]
  · rw [hc1] at hcc; cases hcc
  · rw [hc] at hcc; cases hcc
end LinkSys

namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat} {modes : Clif.Function → ReturnPinMode}

theorem step_envOf_link_return_pins (hL : L.OkReturnPins modes) {M : Nat} {g : Clif.Function} (hg : g ∈ L.P.funcs)
    {c : BitVec 64} {s : Clif.State} (hJ : L.ActInv g c s) {r : Clif.StepResult}
    (hs : Clif.step (L.envOf M g c) L.P.bare s = r) (hr : ∀ m, r ≠ .stuck m) :
    Clif.step (Clif.linkEnvR L.P L.base (L.crun M)) L.P.bare s = r := by
  have hPf : ∀ f ∈ (L.P.only g).funcs, Clif.LinkFree f := fun f hf => by
    simp only [Clif.Program.only, List.mem_cons, List.not_mem_nil, or_false] at hf
    subst hf; exact hL.free f hg
  rw [L.step_envOf (hL.free g hg) hJ.1.1 hJ.2.2] at hs
  exact step_of_restrict L.envR_restricts hPf hJ.1.1 hs hr
end LinkSys

namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat} {modes : Clif.Function → ReturnPinMode}

theorem runLoop_envOf_return_pins (hL : L.OkReturnPins modes) [L.CrunOk] {M : Nat} {g : Clif.Function} (hg : g ∈ L.P.funcs)
    {c : BitVec 64} :
    ∀ (n : Nat) (s : Clif.State), L.ActInv g c s →
      Clif.runLoop (L.envOf M g c) L.P.bare n s = Clif.runLoop (L.envR M g) L.P.bare n s
  | 0, _, _ => rfl
  | n + 1, s, hJ => by
    rw [Clif.runLoop_succ', Clif.runLoop_succ', L.step_envOf (hL.free g hg) hJ.1.1 hJ.2.2]
    cases hs : Clif.step (L.envR M g) L.P.bare s with
    | next s1 =>
      have hs' := L.step_envOf_link_return_pins hL hg hJ
        ((L.step_envOf (hL.free g hg) hJ.1.1 hJ.2.2).trans hs) (fun _ h => nomatch h)
      exact runLoop_envOf_return_pins hL hg n s1 (L.actInv_step_return_pins hL hg hJ hs')
    | _ => rfl
end LinkSys

namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat} {modes : Clif.Function → ReturnPinMode}

theorem reach_envOf_return_pins (hL : L.OkReturnPins modes) [L.CrunOk] {M : Nat} {g : Clif.Function} (hg : g ∈ L.P.funcs)
    {c : BitVec 64} {cs s : Clif.State} (hr : Reach (L.envOf M g c) L.P.bare cs s)
    (hJ : L.ActInv g c cs) :
    Reach (Clif.linkEnvR L.P L.base (L.crun M)) L.P.bare cs s ∧ L.ActInv g c s := by
  induction hr with
  | refl => exact ⟨.refl _, hJ⟩
  | step hs _ ih =>
    have hs' := L.step_envOf_link_return_pins hL hg hJ hs (fun _ h => nomatch h)
    obtain ⟨h1, h2⟩ := ih (L.actInv_step_return_pins hL hg hJ hs')
    exact ⟨.step hs' h1, h2⟩
end LinkSys

namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat} {modes : Clif.Function → ReturnPinMode}

theorem trapsExplicit_envOf_return_pins (hL : L.OkReturnPins modes) [L.CrunOk] {M : Nat} {g : Clif.Function} (hg : g ∈ L.P.funcs)
    {c : BitVec 64} {cs : Clif.State} (hJ : L.ActInv g c cs)
    (h : TrapsExplicit (Clif.linkEnvR L.P L.base (L.crun M)) L.P.bare cs) :
    TrapsExplicit (L.envOf M g c) L.P.bare cs where
  stmt := fun s c st rest hr hs hb => by
    obtain ⟨hr', hJs⟩ := L.reach_envOf_return_pins hL hg hr hJ
    exact h.stmt s c st rest hr' (L.step_envOf_link_return_pins hL hg hJs hs (fun _ h => nomatch h)) hb
  tryCall := fun s c fn args et hr hs hb ht => by
    obtain ⟨hr', hJs⟩ := L.reach_envOf_return_pins hL hg hr hJ
    exact h.tryCall s c fn args et hr' (L.step_envOf_link_return_pins hL hg hJs hs (fun _ h => nomatch h)) hb ht
  tryCallInd := fun s c callee args et hr hs hb ht => by
    obtain ⟨hr', hJs⟩ := L.reach_envOf_return_pins hL hg hr hJ
    exact h.tryCallInd s c callee args et hr'
      (L.step_envOf_link_return_pins hL hg hJs hs (fun _ h => nomatch h)) hb ht
  indirect := fun s st rest sig callee args hr hb hi hst =>
    h.indirect s st rest sig callee args (L.reach_envOf_return_pins hL hg hr hJ).1 hb hi hst
  tryIndirect := fun s callee args et hr hb ht hB =>
    h.tryIndirect s callee args et (L.reach_envOf_return_pins hL hg hr hJ).1 hb ht hB
end LinkSys

namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat} {modes : Clif.Function → ReturnPinMode}

theorem thm_of_return_pins (hL : L.OkReturnPins modes) [L.CrunOk] (hκ : L.Budget κ) {M : Nat} (ih : 0 < M → L.ThmReturnPins modes κ (M - 1)) : L.ThmReturnPins modes κ M := by
  intro g hg F vals cs w₀ fuel rvals cm' hWE hrun
  have hc := hL.compiled g hg
  have hI : Clif.LInv (L.P.only g) cs := runInv_entry (by simp [Clif.Program.only]) hWE.clif
  have hJ : L.ActInv g (spv w₀) cs := ⟨hI, hWE.clif.callers, hWE.place⟩
  have hrun' : Clif.runLoop (L.envOf M g (spv w₀)) L.P.bare fuel cs = .returned rvals cm' := by
    rw [L.runLoop_envOf_return_pins hL hg fuel cs hJ]; exact hrun
  have h := backend_correct_world_ni_return_pins (hL.subset g hg) hc.artifact
    (X := L.XMode modes κ M g F) (syms := L.syms)
    (env := L.envOf M g (spv w₀)) (K := κ M g) (F := F) (c := spv w₀) (hL.covered g hg)
    (L.xCallsOk_return_pins hL hκ ih hg hWE.img hWE.room hWE.dead hWE.align)
    (L.xCallsIndOk_return_pins hL hκ ih hg hWE.img hWE.room hWE.dead hWE.align)
    (fun n b hn => hL.symOk n b hn) rfl hWE.clif hWE.rel hWE.args
    (trapsExplicit_of_returned hrun') fuel
  obtain ⟨us, outs, wf, hus, hlen, hhold, hmem, hrs, hall, hni⟩ := h rvals cm' hrun'
  have hAE : ∀ G ra s w₀', L.MachEntry κ M g F G ra s w₀' →
      ActEntry (L.A g).vcp (L.A g).rf (L.A g).af (L.A g).fa (L.A g).fb (κ M g) F G (L.XMode modes κ M g F)
        (L.hooks M) (L.A g).base ra s w₀' := fun G ra s w₀' hME =>
    ⟨hME.abi, hME.stack, hME.gfree, hME.hF, L.calleeOk_return_pins hL hκ ih hg hME,
      fun _ => L.calleeTryOk_return_pins hL hκ ih hg hME,
      fun ht => L.tlsOk_hooks_mode (hL.baseTls g hg (hasTls_of_vcode_return_pins hc ht) F (κ M g)), hME.body⟩
  refine ⟨us, outs, wf, hus, hlen, hhold, hmem, hrs, fun G ra s hME => hall (L.hooks M) G
    (L.A g).base ra s (hAE G ra s w₀ hME), fun hN D w₀' hrel' hsw hreg hstk G ra s hME => ?_⟩
  exact hni (L.xni_return_pins hL hN ih hg hWE.img (spv w₀)) (L.xTls_return_pins hL hN) D w₀' hrel' hsw hreg hstk
    (L.hooks M) G
    (L.A g).base ra s (hAE G ra s w₀' hME)
end LinkSys

namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat} {modes : Clif.Function → ReturnPinMode}

theorem thm_return_pins (hL : L.OkReturnPins modes) [L.CrunOk] (hκ : L.Budget κ) : ∀ M, L.ThmReturnPins modes κ M
  | 0 => L.thm_of_return_pins hL hκ fun h => absurd h (Nat.lt_irrefl 0)
  | M + 1 => L.thm_of_return_pins hL hκ fun _ => thm_return_pins hL hκ M
end LinkSys

namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat} {modes : Clif.Function → ReturnPinMode}

theorem OkReturnPins.withCrun {L : LinkSys} (hL : L.OkReturnPins modes) (c : Nat → Clif.State → Clif.Outcome) :
    (L.withCrun c).OkReturnPins modes := by
  have compilation : ∀ g ∈ (L.withCrun c).P.funcs,
      CompiledProgramReturnPins (L.withCrun c) g modes := fun g hg =>
    ⟨(hL.compiled g hg).artifact,
      ⟨(hL.compiled g hg).calls.direct,(hL.compiled g hg).calls.indirect⟩⟩
  cases hL
  constructor <;> first | assumption | exact compilation
end LinkSys

namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat} {modes : Clif.Function → ReturnPinMode}

theorem crunOk_std_return_pins (hL : L.OkReturnPins modes) : L.std.CrunOk where
  runs M := Clif.runsOf_runLoop L.base L.P M
  zero _ _ _ h := by simp [std, withCrun] at h
  link M hM _ hf s hI hIf hsy _ hEn hEs hEb hEp hst hof :=
    Clif.runLoop_linkN (base := L.base) (syms := L.syms) (M - 1) hL.names hf hL.free
      (hL.indScope _ hf) hEn hEs hEb hEp M s (by omega) hI hIf hsy hst hof
end LinkSys

namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat} {modes : Clif.Function → ReturnPinMode}

theorem crunOk_peak_return_pins (hL : L.OkReturnPins modes) (F : Nat) : (L.peak F).CrunOk where
  runs M := Clif.runsOf_runD L.base L.P F M
  zero _ _ _ h := by simp [peak, withCrun, Clif.runD] at h
  link M _ _ hf s hI hIf hsy _ hEn hEs hEb hEp hst hof := by
    have hd : 0 < M ∧ Clif.DepthLe L.base L.P (M - 1) s := by
      refine Classical.byContradiction fun hc => hof ?_
      show Clif.runD L.base L.P F M s = _
      simp only [Clif.runD, hc, ↓reduceIte]
    have he : Clif.runD L.base L.P F M s = Clif.runLoop L.base L.P F s := by
      simp only [Clif.runD, hd, and_self, ↓reduceIte]
    obtain ⟨m, hm⟩ := Clif.runLoop_linkD (base := L.base) (syms := L.syms) F (M - 1) hL.names hf
      hL.free (hL.indScope _ hf) hEn hEs hEb hEp F s (by omega) hd.2 hI hIf hsy
      (by rw [← he]; exact hst) (by rw [← he]; exact hof)
    exact ⟨m, hm.trans he.symm⟩
end LinkSys

theorem backend_correct_program_core_return_pins (L : LinkSys) (hL : L.OkReturnPins modes) [L.CrunOk]
    {κ : Nat → Clif.Function → Nat} (hκ : L.Budget κ) {f : Clif.Function}
    (hf : f ∈ L.P.funcs) (M : Nat) {ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val}
    {cs : Clif.State}
    (hent : AbiEntry (L.A f).fb (L.A f).base ra s) (hres : StackAvail (κ M f) (L.A f).af s)
    (hF : L.F = frameWG (κ M f) (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase
      (RAFrame.compute (L.A f).vcp (L.A f).rf).size (L.A f).af L.Img s)
    (hgfree : ∀ a, L.Img a → ¬ StackBelow (frameDrop (L.A f).af + κ M f) (spv s) a)
    (himg : ∀ a, L.Img a → s.mem a = L.imgMem a)
    (hbe : BodyEntry (L.A f).af s w₀) (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hsav : StackArgsAvoid L.Img f.sig args s)
    (hrel : Rel.holds ⟨L.F, L.syms, (L.A f).af.slotBase,
      (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (hpl : L.NeedSlots → L.PlaceAt cs.mem (spv w₀))
    (htr : TrapsExplicit (Clif.linkEnvR L.P L.base (L.crun M)) L.P.bare cs) {o : Clif.Outcome}
    (hlink : ((∃ vals cm, o = .returned vals cm) ∨ ∃ c, o = .trapped c) →
      ∃ m, Clif.runLoop (L.envR M f) L.P.bare m cs = o) :
    ArmRefines (L.A f).fb (L.A f).base ra (L.mach M f) s o := by
  have hc := hL.compiled f hf
  have hfr := lowerRFunc_frame hc.alloc
  have hst := hres
  obtain ⟨hB, hK⟩ := spBody_toNat hres
  have hd : frameDrop (L.A f).af = (L.A f).af.frameSize + 16 := by simp [frameDrop, hfr]
  -- the world side
  have hWE : L.WorldEntry κ M f L.F args cs w₀ := by
    refine ⟨hcs, ⟨hrel, rfl, ?_⟩, ?_, ?_, ?_, ?_, hL.imgF, hpl⟩
    · rw [hbe.other .ERR (by simp [Masked]) (by simp) (by simp)]; exact hent.err
    · refine argsAtEntry_body hfr hc.entryRegs hbe hargs fun off v hm k hk hk' => ?_
      rw [hF] at hk'
      rcases hk' with hw | hi
      · exact stackArgsAvoid_frameW_return_pins hc hres hent hargs off v hm k hk hw
      · exact hsav off v hm k hk hi
    · rw [hbe.sp, hB]; omega
    · intro a ha
      rw [hbe.sp] at ha
      refine ⟨by rw [hF]; exact .inl (.inr ha), fun hi => hgfree a hi ?_⟩
      obtain ⟨h1, h2⟩ := ha
      rw [hB] at h1 h2
      exact ⟨by omega, by omega⟩
    · rw [hbe.sp, hB, hd]
      have := hent.spAligned
      have := L.frameSize_mod_return_pins hL hf
      omega
  -- the machine side
  have hME : L.MachEntry κ M f L.F L.Img ra s w₀ :=
    ⟨hent.toCall, hres, hgfree, hF.symm, fun _ h => h, himg,
      hbe.w L.F fun r ⟨_, _, hvb, hi, _, hv⟩ =>
        ((ctlCheck_args (lowerRFunc_ok hc.alloc).2.2 hvb hi).2.2 _ hv).2⟩
  -- the whole-program run is a run of the program without functions
  have hIf : Clif.LInv (L.P.only f) cs := runInv_entry (by simp [Clif.Program.only]) hcs
  cases o with
  | stuck m => trivial
  | outOfFuel => trivial
  | returned vals cm =>
    obtain ⟨m, hm⟩ := hlink (.inl ⟨_, _, rfl⟩)
    obtain ⟨us, outs, wf, hus, hlen, hhold, hmemR, -, hall, -⟩ :=
      L.thm_return_pins hL hκ M f hf L.F args cs w₀ m vals cm hWE hm
    obtain ⟨n, hret, -⟩ := hall L.Img ra s hME
    have invariant : L.ActInv f (spv w₀) cs := ⟨hIf,hcs.callers,hpl⟩
    have atomic : Clif.runLoop (L.envOf M f (spv w₀)) L.P.bare m cs = .returned vals cm := by
      rw [L.runLoop_envOf_return_pins hL hf m cs invariant]
      exact hm
    obtain ⟨last,reached,done⟩ := runLoop_returned_reach m cs atomic
    have inv := (L.reach_envOf_return_pins hL hf reached invariant).2
    have free : ∀ g ∈ (L.P.only f).funcs,Clif.LinkFree g := by
      intro g member
      have same : g = f := by simpa only [Clif.Program.only,List.mem_singleton] using member
      subst g
      exact hL.free f hf
    have types := (Clif.step_done_tys_with_frame free inv.1 done).2
    have source : last.frame.func = f := by
      simpa only [Clif.Program.only,List.mem_singleton] using inv.1.1.1
    rw [source] at types
    exact armRefines_of_actRet_return_pins hus (hL.subset f hf).abiSigs.1 types hlen hhold hmemR hret
  | trapped c =>
    obtain ⟨m, hm⟩ := hlink (.inr ⟨_, rfl⟩)
    have ih : 0 < M → L.ThmReturnPins modes κ (M - 1) := fun _ => L.thm_return_pins hL hκ (M - 1)
    have hJ : L.ActInv f (spv w₀) cs := ⟨hIf, hcs.callers, hpl⟩
    have hm' : Clif.runLoop (L.envOf M f (spv w₀)) L.P.bare m cs = .trapped c := by
      rw [L.runLoop_envOf_return_pins hL hf m cs hJ]; exact hm
    have h := backend_correct_world_return_pins (hL.subset f hf) hc.artifact
      (X := L.XMode modes κ M f L.F) (syms := L.syms)
      (env := L.envOf M f (spv w₀)) (K := κ M f) (F := L.F) (c := spv w₀) (hL.covered f hf)
      (L.xCallsOk_return_pins hL hκ ih hf hL.imgF hWE.room hWE.dead hWE.align)
      (L.xCallsIndOk_return_pins hL hκ ih hf hL.imgF hWE.room hWE.dead hWE.align)
      (fun n b hn => hL.symOk n b hn) rfl hWE.clif hWE.rel hWE.args
      (L.trapsExplicit_envOf_return_pins hL hf hJ htr) m
    exact h.2 c hm' (L.hooks M) L.Img (L.A f).base ra s ⟨hME.abi, hME.stack, hME.gfree, hME.hF,
      L.calleeOk_return_pins hL hκ ih hf hME,
      fun _ => L.calleeTryOk_return_pins hL hκ ih hf hME,
      fun ht => L.tlsOk_hooks_mode (hL.baseTls f hf (hasTls_of_vcode_return_pins hc ht) L.F (κ M f)), hME.body⟩

theorem backend_correct_program_budget_return_pins (L : LinkSys) (hL : L.OkReturnPins modes)
    {κ : Nat → Clif.Function → Nat} (hκ : L.Budget κ) {f : Clif.Function}
    (hf : f ∈ L.P.funcs) (M : Nat) {ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val}
    {cs : Clif.State}
    (hent : AbiEntry (L.A f).fb (L.A f).base ra s) (hres : StackAvail (κ M f) (L.A f).af s)
    (hF : L.F = frameWG (κ M f) (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase
      (RAFrame.compute (L.A f).vcp (L.A f).rf).size (L.A f).af L.Img s)
    (hgfree : ∀ a, L.Img a → ¬ StackBelow (frameDrop (L.A f).af + κ M f) (spv s) a)
    (himg : ∀ a, L.Img a → s.mem a = L.imgMem a)
    (hbe : BodyEntry (L.A f).af s w₀) (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hsav : StackArgsAvoid L.Img f.sig args s)
    (hrel : Rel.holds ⟨L.F, L.syms, (L.A f).af.slotBase,
      (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (hpl : L.NeedSlots → L.PlaceAt cs.mem (spv w₀))
    (htr : TrapsExplicit (Clif.linkEnvN L.P L.base M) L.P.bare cs) :
    ArmRefines (L.A f).fb (L.A f).base ra (L.mach M f) s (Clif.runLoop L.base L.P (M + 1) cs) := by
  haveI := L.crunOk_std_return_pins hL
  rw [← L.mach_std]
  have hIf : Clif.LInv (L.P.only f) cs := runInv_entry (by simp [Clif.Program.only]) hcs
  refine backend_correct_program_core_return_pins L.std (hL.withCrun _) hκ hf M hent hres hF hgfree himg hbe
    hargs hcs hsav hrel hpl htr fun ho => ?_
  exact Clif.runLoop_linkN (base := L.base) (syms := L.syms) M hL.names hf hL.free
    (hL.indScope f hf) (E := L.std.envR M f)
    rfl rfl (fun _ hn => L.std.envR_of (.inl hn))
    (L.std.envR_link hL.names) (M + 1) cs (Nat.le_refl _) (runInv_entry hf hcs) hIf
    (fun _ => hrel.1.symbols)
    (by rcases ho with ⟨_, _, ho⟩ | ⟨_, ho⟩ <;> rw [ho] <;> exact fun _ h => nomatch h)
    (by rcases ho with ⟨_, _, ho⟩ | ⟨_, ho⟩ <;> rw [ho] <;> exact fun h => nomatch h)

theorem backend_correct_program_peak_return_pins (L : LinkSys) (hL : L.OkReturnPins modes)
    {κ : Nat → Clif.Function → Nat} (hκ : L.Budget κ) {f : Clif.Function}
    (hf : f ∈ L.P.funcs) (F d : Nat) {ra : BitVec 64} {s w₀ : Arm.ArmState}
    {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry (L.A f).fb (L.A f).base ra s) (hres : StackAvail (κ d f) (L.A f).af s)
    (hF : L.F = frameWG (κ d f) (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase
      (RAFrame.compute (L.A f).vcp (L.A f).rf).size (L.A f).af L.Img s)
    (hgfree : ∀ a, L.Img a → ¬ StackBelow (frameDrop (L.A f).af + κ d f) (spv s) a)
    (himg : ∀ a, L.Img a → s.mem a = L.imgMem a)
    (hbe : BodyEntry (L.A f).af s w₀) (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hsav : StackArgsAvoid L.Img f.sig args s)
    (hrel : Rel.holds ⟨L.F, L.syms, (L.A f).af.slotBase,
      (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (hpl : L.NeedSlots → L.PlaceAt cs.mem (spv w₀))
    (hd : Clif.DepthLe L.base L.P d cs)
    (htr : TrapsExplicit (Clif.linkEnvD L.P L.base F d) L.P.bare cs) :
    ArmRefines (L.A f).fb (L.A f).base ra (L.mach d f) s (Clif.runLoop L.base L.P (F + 1) cs) := by
  haveI := L.crunOk_peak_return_pins hL F
  rw [← L.mach_peak F]
  have hIf : Clif.LInv (L.P.only f) cs := runInv_entry (by simp [Clif.Program.only]) hcs
  refine backend_correct_program_core_return_pins (L.peak F) (hL.withCrun _) hκ hf d hent hres hF hgfree himg
    hbe hargs hcs hsav hrel hpl htr fun ho => ?_
  exact Clif.runLoop_linkD (base := L.base) (syms := L.syms) F d hL.names hf hL.free
    (hL.indScope f hf) (E := (L.peak F).envR d f)
    rfl rfl (fun _ hn => (L.peak F).envR_of (.inl hn))
    ((L.peak F).envR_link hL.names) (F + 1) cs (Nat.le_refl _) hd (runInv_entry hf hcs) hIf
    (fun _ => hrel.1.symbols)
    (by rcases ho with ⟨_, _, ho⟩ | ⟨_, ho⟩ <;> rw [ho] <;> exact fun _ h => nomatch h)
    (by rcases ho with ⟨_, _, ho⟩ | ⟨_, ho⟩ <;> rw [ho] <;> exact fun h => nomatch h)

theorem backend_correct_program_return_pins (L : LinkSys) (hL : L.OkReturnPins modes) {f : Clif.Function}
    (hf : f ∈ L.P.funcs) (M : Nat) {ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val}
    {cs : Clif.State}
    (hent : AbiEntry (L.A f).fb (L.A f).base ra s) (hres : StackAvail (L.K M) (L.A f).af s)
    (hF : L.F = frameWG (L.K M) (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase
      (RAFrame.compute (L.A f).vcp (L.A f).rf).size (L.A f).af L.Img s)
    (hgfree : ∀ a, L.Img a → ¬ StackBelow (frameDrop (L.A f).af + L.K M) (spv s) a)
    (himg : ∀ a, L.Img a → s.mem a = L.imgMem a)
    (hbe : BodyEntry (L.A f).af s w₀) (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hsav : StackArgsAvoid L.Img f.sig args s)
    (hrel : Rel.holds ⟨L.F, L.syms, (L.A f).af.slotBase,
      (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (hpl : L.NeedSlots → L.PlaceAt cs.mem (spv w₀))
    (htr : TrapsExplicit (Clif.linkEnvN L.P L.base M) L.P.bare cs) :
    ArmRefines (L.A f).fb (L.A f).base ra (L.mach M f) s (Clif.runLoop L.base L.P (M + 1) cs) :=
  backend_correct_program_budget_return_pins L hL (κ := fun M _ => L.K M) (L.budget_K_return_pins hL) hf M hent hres hF
    hgfree himg hbe hargs hcs hsav hrel hpl htr

theorem backend_correct_program_returned_budget_return_pins (L : LinkSys) (hL : L.OkReturnPins modes)
    {κ : Nat → Clif.Function → Nat} (hκ : L.Budget κ) {f : Clif.Function}
    (hf : f ∈ L.P.funcs) (M : Nat) {ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val}
    {cs : Clif.State}
    (hent : AbiEntry (L.A f).fb (L.A f).base ra s) (hres : StackAvail (κ M f) (L.A f).af s)
    (hF : L.F = frameWG (κ M f) (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase
      (RAFrame.compute (L.A f).vcp (L.A f).rf).size (L.A f).af L.Img s)
    (hgfree : ∀ a, L.Img a → ¬ StackBelow (frameDrop (L.A f).af + κ M f) (spv s) a)
    (himg : ∀ a, L.Img a → s.mem a = L.imgMem a)
    (hbe : BodyEntry (L.A f).af s w₀) (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hsav : StackArgsAvoid L.Img f.sig args s)
    (hrel : Rel.holds ⟨L.F, L.syms, (L.A f).af.slotBase,
      (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (hpl : L.NeedSlots → L.PlaceAt cs.mem (spv w₀))
    {vals : List Clif.Val} {cm : Clif.Mem}
    (hrun : Clif.runLoop L.base L.P (M + 1) cs = .returned vals cm) :
    ArmRefines (L.A f).fb (L.A f).base ra (L.mach M f) s (.returned vals cm) := by
  have hIf : Clif.LInv (L.P.only f) cs := runInv_entry (by simp [Clif.Program.only]) hcs
  obtain ⟨m, hm⟩ := Clif.runLoop_linkN (base := L.base) (syms := L.syms) M hL.names hf hL.free
    (hL.indScope f hf)
    (E := Clif.linkEnvN L.P L.base M) rfl rfl (fun _ _ => rfl) (fun _ _ _ => rfl)
    (M + 1) cs (Nat.le_refl _) (runInv_entry hf hcs) hIf
    (fun _ => hrel.1.symbols) (by rw [hrun]; exact fun _ h => nomatch h)
    (by rw [hrun]; exact fun h => nomatch h)
  rw [hrun] at hm
  rw [← hrun]
  exact backend_correct_program_budget_return_pins L hL hκ hf M hent hres hF hgfree himg hbe hargs hcs hsav hrel hpl
    (trapsExplicit_of_returned hm)

theorem backend_correct_program_returned_return_pins (L : LinkSys) (hL : L.OkReturnPins modes) {f : Clif.Function}
    (hf : f ∈ L.P.funcs) (M : Nat) {ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val}
    {cs : Clif.State}
    (hent : AbiEntry (L.A f).fb (L.A f).base ra s) (hres : StackAvail (L.K M) (L.A f).af s)
    (hF : L.F = frameWG (L.K M) (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase
      (RAFrame.compute (L.A f).vcp (L.A f).rf).size (L.A f).af L.Img s)
    (hgfree : ∀ a, L.Img a → ¬ StackBelow (frameDrop (L.A f).af + L.K M) (spv s) a)
    (himg : ∀ a, L.Img a → s.mem a = L.imgMem a)
    (hbe : BodyEntry (L.A f).af s w₀) (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hsav : StackArgsAvoid L.Img f.sig args s)
    (hrel : Rel.holds ⟨L.F, L.syms, (L.A f).af.slotBase,
      (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (hpl : L.NeedSlots → L.PlaceAt cs.mem (spv w₀))
    {vals : List Clif.Val} {cm : Clif.Mem}
    (hrun : Clif.runLoop L.base L.P (M + 1) cs = .returned vals cm) :
    ArmRefines (L.A f).fb (L.A f).base ra (L.mach M f) s (.returned vals cm) :=
  backend_correct_program_returned_budget_return_pins L hL (κ := fun M _ => L.K M) (L.budget_K_return_pins hL) hf M hent
    hres hF hgfree himg hbe hargs hcs hsav hrel hpl hrun

end E2E
