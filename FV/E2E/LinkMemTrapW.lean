import FV.E2E.LinkMemTrap
import FV.E2E.LinkGoodW
import FV.E2E.WorldMemTrapW

/-!
# Memory traps in the linked program with the writes (A3, #412, slice F8c)

`LinkMemTrap`'s `RunGoodLB` and `backend_correct_program_memtrap_{core,budget,peak}` with the
writes: `RunGoodLBW` (`GoodAtW`: `actGoodXW`, the per-state facts and `RL.WritesAt`, at every
state of the entry activation before the trap state and of the activations it calls before it),
`backend_correct_program_memtrapW_{core,budget,peak}`.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

namespace LinkSys

variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

/-- **The per-state facts before step `n`** (`RunGoodL` bounded): at every `ReachLB n` state
whose step ends without error. -/
def RunGoodLBW (n M : Nat) (f : Clif.Function) (c : Arm.ArmState) : Prop :=
  ∀ M' g c' t, L.ReachLB n M f c M' g c' t → Arm.r .ERR (L.mach M' g t) = .None → L.GoodAtW M' g c' t

/-- **The states of an activation's run before step `n`** from its trace (`runGood_of_trace`
without the bound on the run's other states). -/
theorem runGoodB_of_traceW (hL : L.Ok) [L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ihG : 0 < M → L.ThmGW κ (M - 1))
    {g : Clif.Function} (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {ra : BitVec 64}
    {s w₀ : Arm.ArmState} (he : L.MachEntry κ M g F G ra s w₀) {n : Nat}
    (hgood : ∀ i < n, actGoodXW (L.A g).vcp (L.A g).rf (L.A g).af (L.A g).fa (L.A g).fb
      (L.A g).base s (L.X κ M g F) (L.hooks M) (κ M g) G (GotV (L.A g).vcp)
      (runX (L.mach M g) i s)) :
    L.RunGoodLBW n M g s := by
  intro M' g' c' t hR herrt
  rcases hR with ⟨k, hk, hno, e1, e2, e3, e4⟩ | ⟨M0, k, h, e1, hk, hno, hcall, herr1, hR'⟩
  · subst M' g' c' t
    have hG : (L.actRL κ M g F G s).GoodXW (runX (L.mach M g) k s) := hgood k hk
    refine ⟨L.X κ M g F, κ M g, G, GotV (L.A g).vcp, rfl, hG, he.imgG, he.imgS, ?_⟩
    intro xr h hx hb
    obtain ⟨x, ⟨j, tt, hj, hpc⟩, -⟩ := hG.1.line
    have hj' : (L.A g).fa.lines.toList[j]? = some (.ins x tt) := hj
    have hc := hL.compiled g hg
    obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hc.layout
    have hsz : ((L.A g).fa.lines.toList.map Line.size).sum ≤ 2 ^ 64 := by
      rw [layout_sum hc.layout]; have := hL.fits g hg; omega
    have hx' : insnAt (L.A g).fa (L.A g).base (Arm.r .PC (runX (L.mach M g) k s)) = some x := by
      rw [hpc]; exact insnAt_line hsz hj'
    rw [hx'] at hx; cases hx
    have hins : insnAt (L.A g).fa (progBase (runX (L.mach M g) k s))
        (Arm.r .PC (runX (L.mach M g) k s)) = some (.blr xr) := by
      rw [hpc]; exact insnAt_ofLine hc.layout hlm (by have := hL.fits g hg; omega) hG.1.prog hj'
    exact L.blrTo_of_pre hL hg he (hG.1.call _ ⟨j, tt, hj, hpc⟩ (.inr ⟨xr, rfl⟩)) hG.1.prog hins hb
  · subst M
    have hG : (L.actRL κ (M0 + 1) g F G s).GoodXW (runX (L.mach (M0 + 1) g) k s) := hgood k hk
    obtain ⟨x, ⟨j, tt, hj, hpc⟩, -⟩ := hG.1.line
    have hj' : (L.A g).fa.lines.toList[j]? = some (.ins x tt) := hj
    have hc := hL.compiled g hg
    obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hc.layout
    have hins : insnAt (L.A g).fa (progBase (runX (L.mach (M0 + 1) g) k s))
        (Arm.r .PC (runX (L.mach (M0 + 1) g) k s)) = some x := by
      rw [hpc]; exact insnAt_ofLine hc.layout hlm (by have := hL.fits g hg; omega) hG.1.prog hj'
    have hpre : (L.actRL κ (M0 + 1) g F G s).CallPre (runX (L.mach (M0 + 1) g) k s) := by
      rcases hcall with ⟨n', hn', -⟩ | ⟨⟨r', hr'⟩, -⟩
      · rw [hins] at hn'; cases hn'; exact hG.1.call _ ⟨j, tt, hj, hpc⟩ (.inl ⟨n', rfl⟩)
      · rw [hins] at hr'; cases hr'; exact hG.1.call _ ⟨j, tt, hj, hpc⟩ (.inr ⟨r', rfl⟩)
    exact L.callGoodW hL hκ ihG hg he hpre hG.1.prog hcall _ _ _ _ hR' herrt

end LinkSys

theorem goodAtW_withCrun {L : LinkSys} {cr : Nat → Clif.State → Clif.Outcome} {M : Nat}
    {g : Clif.Function} {c t : Arm.ArmState} (h : (L.withCrun cr).GoodAtW M g c t) :
    L.GoodAtW M g c t := by
  obtain ⟨X, K, G, gv, heq, hg, hi⟩ := h
  rw [L.hooks_withCrun, L.mach_withCrun] at heq
  rw [L.hooks_withCrun] at hg
  exact ⟨X, K, G, gv, heq, hg, hi⟩

/-- **`RunGoodLBW` does not depend on the callee runs** of the linked system. -/
theorem runGoodLBW_withCrun {L : LinkSys} {cr : Nat → Clif.State → Clif.Outcome} {n M : Nat}
    {f : Clif.Function} {c : Arm.ArmState} (h : (L.withCrun cr).RunGoodLBW n M f c) :
    L.RunGoodLBW n M f c := fun M' g c' t hR he =>
  goodAtW_withCrun (h M' g c' t (reachLB_withCrun hR) (by rw [L.mach_withCrun]; exact he))

/-- **A memory trap of the entry function in the linked program, for any callee runs**: under
the run premise `TrapsExplicitM` of the linked environment and `MapFaults mp`, a trapping run of
the entry activation of `f` (whose code is the dead-cleanup chain's, `CompiledCleanup`) reaches a
state of the linked machine of depth `M` at a trap site of `f` with the code (`TrapAtM`), every
earlier state with the per-state facts (`RunGoodLBW`). -/
theorem backend_correct_program_memtrapW_core (L : LinkSys) (hL : L.Ok) [L.CrunOk]
    {κ : Nat → Clif.Function → Nat} (hκ : L.Budget κ) {f : Clif.Function}
    (hf : f ∈ L.P.funcs)
    (hcl : CompiledCleanup f (L.A f).k (L.A f).vc (L.A f).vcp (L.A f).rf (L.A f).af (L.A f).fa
      (L.A f).fb)
    (M : Nat) {ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val}
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
    (htr : TrapsExplicitM (Clif.linkEnvR L.P L.base (L.crun M)) L.P.bare cs)
    {mp : ArmFault.MemMap} (hmf : MapFaults mp (Clif.linkEnvR L.P L.base (L.crun M)) L.P.bare cs)
    {c : Clif.TrapCode} (hlink : ∃ m, Clif.runLoop (L.envR M f) L.P.bare m cs = .trapped c) :
    ∃ n, TrapAtM mp (L.A f).fa (L.A f).fb (L.A f).base c (runX (L.mach M f) n s) ∧
      L.RunGoodLBW n M f s := by
  have hc := hL.compiled f hf
  have hfr := lowerRFunc_frame hc.alloc
  obtain ⟨hB, hK⟩ := spBody_toNat hres
  have hd : frameDrop (L.A f).af = (L.A f).af.frameSize + 16 := by simp [frameDrop, hfr]
  -- the world side
  have hWE : L.WorldEntry κ M f L.F args cs w₀ := by
    refine ⟨hcs, ⟨hrel, rfl, ?_⟩, ?_, ?_, ?_, ?_, hL.imgF, hpl⟩
    · rw [hbe.other .ERR (by simp [Masked]) (by simp) (by simp)]; exact hent.err
    · refine argsAtEntry_body hfr (entryRegs_of_check hc.lowerOk) hbe hargs (fun off v hm k hk hk' => ?_) hres
      rw [hF] at hk'
      rcases hk' with hw | hi
      · exact stackArgsAvoid_frameW_pipeline hc hres hent hargs off v hm k hk hw
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
      have := L.frameSize_mod hL hf
      omega
  -- the machine side
  have hME : L.MachEntry κ M f L.F L.Img ra s w₀ :=
    ⟨hent.toCall, hres, hgfree, hF.symm, fun _ h => h, himg,
      hbe.w L.F fun r ⟨_, _, hvb, hi, _, hv⟩ =>
        ((ctlCheck_args (lowerRFunc_ok hc.alloc).2.2 hvb hi).2.2 _ hv).2⟩
  have hIf : Clif.LInv (L.P.only f) cs := runInv_entry (by simp [Clif.Program.only]) hcs
  obtain ⟨m, hm⟩ := hlink
  have ih : 0 < M → L.Thm κ (M - 1) := fun _ => L.thm hL hκ (M - 1)
  have hJ : L.ActInv f (spv w₀) cs := ⟨hIf, hcs.callers, hpl⟩
  have hm' : Clif.runLoop (L.envOf M f (spv w₀)) L.P.bare m cs = .trapped c := by
    rw [L.runLoop_envOf hL hf m cs hJ]; exact hm
  obtain ⟨n, htrap, hgood⟩ := backend_correct_worldX_cleanup_memtrapW (hL.subset f hf) hcl
    (X := L.X κ M f L.F) (syms := L.syms)
    (env := L.envOf M f (spv w₀)) (K := κ M f) (F := L.F) (c := spv w₀) (hL.covered f hf)
    (L.xCallsOk hL hκ ih hf hL.imgF hWE.room hWE.dead hWE.align)
    (L.xCallsIndOk hL hκ ih hf hL.imgF hWE.room hWE.dead hWE.align)
    (fun n b hn => hL.symOk n b hn) rfl hWE.clif hWE.rel hWE.args
    (L.trapsExplicitM_envOf hL hf hJ htr) (L.mapFaults_envOf hL hf hJ hmf) m c hm'
    (L.hooks M) L.Img (L.A f).base ra s
    ⟨hME.abi, hME.stack, hME.gfree, hME.hF,
      L.calleeOk hL hκ ih hf hME,
      fun _ => L.calleeTryOk hL hκ ih hf hME,
      fun ht => L.tlsOk_hooks (hL.baseTls f hf (hasTls_of_vcode_pipeline hc ht) L.F (κ M f)), hME.body⟩
  exact ⟨n, htrap, L.runGoodB_of_traceW hL hκ (fun _ => L.thmGW hL hκ (M - 1)) hf hME hgood⟩

/-- **A memory trap of the entry function in the linked program** (the callees run at most `M`
steps, `LinkSys.std`): a whole-program run of `f` that traps with `c` under `TrapsExplicitM` and
`MapFaults mp` reaches a state of the linked machine at a trap site of `f` with `c` (`TrapAtM`),
every earlier state with the per-state facts (`RunGoodLBW`). -/
theorem backend_correct_program_memtrapW_budget (L : LinkSys) (hL : L.Ok)
    {κ : Nat → Clif.Function → Nat} (hκ : L.Budget κ) {f : Clif.Function}
    (hf : f ∈ L.P.funcs)
    (hcl : CompiledCleanup f (L.A f).k (L.A f).vc (L.A f).vcp (L.A f).rf (L.A f).af (L.A f).fa
      (L.A f).fb)
    (M : Nat) {ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val}
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
    (htr : TrapsExplicitM (Clif.linkEnvN L.P L.base M) L.P.bare cs)
    {mp : ArmFault.MemMap} (hmf : MapFaults mp (Clif.linkEnvN L.P L.base M) L.P.bare cs)
    {c : Clif.TrapCode} (hrun : Clif.runLoop L.base L.P (M + 1) cs = .trapped c) :
    ∃ n, TrapAtM mp (L.A f).fa (L.A f).fb (L.A f).base c (runX (L.mach M f) n s) ∧
      L.RunGoodLBW n M f s := by
  haveI := L.crunOk_std hL
  have hIf : Clif.LInv (L.P.only f) cs := runInv_entry (by simp [Clif.Program.only]) hcs
  obtain ⟨m, hm⟩ := Clif.runLoop_linkN (base := L.base) (syms := L.syms) M hL.names hf hL.free
    (hL.indScope f hf) (E := L.std.envR M f)
    rfl rfl (fun _ hn => L.std.envR_of (.inl hn))
    (L.std.envR_link hL.names) (M + 1) cs (Nat.le_refl _) (runInv_entry hf hcs) hIf
    (fun _ => hrel.1.symbols) (by rw [hrun]; exact fun _ h => nomatch h)
    (by rw [hrun]; exact fun h => nomatch h)
  have h := backend_correct_program_memtrapW_core L.std (hL.withCrun _) hκ hf hcl M hent hres hF
    hgfree himg hbe hargs hcs hsav hrel hpl htr hmf ⟨m, hm.trans hrun⟩
  rw [L.mach_std] at h
  obtain ⟨n, h1, h2⟩ := h
  exact ⟨n, h1, runGoodLBW_withCrun h2⟩

/-- **`backend_correct_program_memtrapW_budget` for the run's peak call depth** `d`
(`Clif.DepthLe`; the program callees with fuel `F` and bounded depth, `Clif.linkEnvD`). -/
theorem backend_correct_program_memtrapW_peak (L : LinkSys) (hL : L.Ok)
    {κ : Nat → Clif.Function → Nat} (hκ : L.Budget κ) {f : Clif.Function}
    (hf : f ∈ L.P.funcs)
    (hcl : CompiledCleanup f (L.A f).k (L.A f).vc (L.A f).vcp (L.A f).rf (L.A f).af (L.A f).fa
      (L.A f).fb)
    (F d : Nat) {ra : BitVec 64} {s w₀ : Arm.ArmState}
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
    (htr : TrapsExplicitM (Clif.linkEnvD L.P L.base F d) L.P.bare cs)
    {mp : ArmFault.MemMap} (hmf : MapFaults mp (Clif.linkEnvD L.P L.base F d) L.P.bare cs)
    {c : Clif.TrapCode} (hrun : Clif.runLoop L.base L.P (F + 1) cs = .trapped c) :
    ∃ n, TrapAtM mp (L.A f).fa (L.A f).fb (L.A f).base c (runX (L.mach d f) n s) ∧
      L.RunGoodLBW n d f s := by
  haveI := L.crunOk_peak hL F
  have hIf : Clif.LInv (L.P.only f) cs := runInv_entry (by simp [Clif.Program.only]) hcs
  obtain ⟨m, hm⟩ := Clif.runLoop_linkD (base := L.base) (syms := L.syms) F d hL.names hf hL.free
    (hL.indScope f hf) (E := (L.peak F).envR d f)
    rfl rfl (fun _ hn => (L.peak F).envR_of (.inl hn))
    ((L.peak F).envR_link hL.names) (F + 1) cs (Nat.le_refl _) hd (runInv_entry hf hcs) hIf
    (fun _ => hrel.1.symbols) (by rw [hrun]; exact fun _ h => nomatch h)
    (by rw [hrun]; exact fun h => nomatch h)
  have h := backend_correct_program_memtrapW_core (L.peak F) (hL.withCrun _) hκ hf hcl d hent hres
    hF hgfree himg hbe hargs hcs hsav hrel hpl htr hmf ⟨m, hm.trans hrun⟩
  rw [L.mach_peak] at h
  obtain ⟨n, h1, h2⟩ := h
  exact ⟨n, h1, runGoodLBW_withCrun h2⟩

end E2E
