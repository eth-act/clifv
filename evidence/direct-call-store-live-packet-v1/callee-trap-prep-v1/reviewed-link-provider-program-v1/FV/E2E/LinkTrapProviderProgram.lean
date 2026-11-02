import FV.E2E.LinkTrapCallInd

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup
set_option autoImplicit false
set_option Elab.async false

theorem backend_correct_program_trap_budget_provider (L : LinkSys) {modes : Clif.Function → ReturnPinMode} (hL : L.OkReturnPins modes) (providers : ∀ g ∈ L.P.funcs,WorldTrapStopProvider L.P.bare g
      (L.A g).vcp (L.A g).rf (L.A g).af (L.A g).fa (L.A g).fb)
    (hB : L.BaseTrapsOk) {κ : Nat → Clif.Function → Nat} (hκ : L.Budget κ) {f : Clif.Function}
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
    (htr : L.std.TrapsD M f cs) {tc : Clif.TrapCode}
    (hrun : Clif.runLoop L.base L.P (M + 1) cs = .trapped tc) :
    L.TrapIn M f s tc := by
  haveI := L.crunOk_std_return_pins hL
  have hIf : Clif.LInv (L.P.only f) cs := runInv_entry (by simp [Clif.Program.only]) hcs
  obtain ⟨m, hm⟩ := Clif.runLoop_linkN (base := L.base) (syms := L.syms) M hL.names hf hL.free
    (hL.indScope f hf) (E := L.std.envR M f)
    rfl rfl (fun _ hn => L.std.envR_of (.inl hn))
    (L.std.envR_link hL.names) (M + 1) cs (Nat.le_refl _) (runInv_entry hf hcs) hIf
    (fun _ => hrel.1.symbols) (by rw [hrun]; exact fun _ h => nomatch h)
    (by rw [hrun]; exact fun h => nomatch h)
  rw [hrun] at hm
  exact L.trapIn_withCrun _ (backend_correct_program_trap_core_provider L.std (hL.withCrun _) providers (hB.withCrun _) hκ hf M
    hent hres hF hgfree himg hbe hargs hcs hsav hrel hpl htr hm)


theorem backend_correct_program_trap_provider (L : LinkSys) {modes : Clif.Function → ReturnPinMode} (hL : L.OkReturnPins modes) (providers : ∀ g ∈ L.P.funcs,WorldTrapStopProvider L.P.bare g
      (L.A g).vcp (L.A g).rf (L.A g).af (L.A g).fa (L.A g).fb)
    (hB : L.BaseTrapsOk) {f : Clif.Function}
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
    (htr : L.std.TrapsD M f cs) {tc : Clif.TrapCode}
    (hrun : Clif.runLoop L.base L.P (M + 1) cs = .trapped tc) :
    L.TrapIn M f s tc :=
  backend_correct_program_trap_budget_provider L hL providers hB (κ := fun M _ => L.K M) (L.budget_K_return_pins hL) hf M
    hent hres hF hgfree himg hbe hargs hcs hsav hrel hpl htr hrun


theorem backend_correct_program_trap_peak_provider (L : LinkSys) {modes : Clif.Function → ReturnPinMode} (hL : L.OkReturnPins modes) (providers : ∀ g ∈ L.P.funcs,WorldTrapStopProvider L.P.bare g
      (L.A g).vcp (L.A g).rf (L.A g).af (L.A g).fa (L.A g).fb)
    (hB : L.BaseTrapsOk) {κ : Nat → Clif.Function → Nat} (hκ : L.Budget κ) {f : Clif.Function}
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
    (htr : (L.peak F).TrapsD d f cs) {tc : Clif.TrapCode}
    (hrun : Clif.runLoop L.base L.P (F + 1) cs = .trapped tc) :
    L.TrapIn d f s tc := by
  haveI := L.crunOk_peak_return_pins hL F
  have hIf : Clif.LInv (L.P.only f) cs := runInv_entry (by simp [Clif.Program.only]) hcs
  obtain ⟨m, hm⟩ := Clif.runLoop_linkD (base := L.base) (syms := L.syms) F d hL.names hf hL.free
    (hL.indScope f hf) (E := (L.peak F).envR d f)
    rfl rfl (fun _ hn => (L.peak F).envR_of (.inl hn))
    ((L.peak F).envR_link hL.names) (F + 1) cs (Nat.le_refl _) hd (runInv_entry hf hcs) hIf
    (fun _ => hrel.1.symbols) (by rw [hrun]; exact fun _ h => nomatch h)
    (by rw [hrun]; exact fun h => nomatch h)
  rw [hrun] at hm
  exact L.trapIn_withCrun _ (backend_correct_program_trap_core_provider (L.peak F) (hL.withCrun _) providers (hB.withCrun _) hκ
    hf d hent hres hF hgfree himg hbe hargs hcs hsav hrel hpl htr hm)


end E2E
