import FV.E2E.BackendPrefixAtGE

/-!
# The prefix theorems for a run that returns or traps (SEM1 #537, traps under the slot-byte oracle)

The prefix theorems up to call `N` (`BackendPrefixAt`, `BackendPrefixAtCleanup`,
`BackendPrefixAtGE`) take a **returning** CLIF run: they use it only to know that a calling state
of the run passes its call (`iselSim_prefixWI_next`). A run that **traps** passes its calls too:
under `TrapsExplicit` a call step does not trap (a statement traps only when it is an explicitly
trapping instruction, a `try_call` terminator of the entered function never does), and the run
does not get stuck. Same proofs, with `RunEnds` (the run returns or traps) for the returning run:

* `RunEnds`, `runEnds_returned`, `runEnds_trapped`, `runLoop_ends_reachN`, `next_of_ends`;
* `iselSim_prefixWI_next_ends`, `iselSim_prefixWI_next_cleanup_ends`;
* `backend_prefixPRI_atS_ends`, `prefix_relatedPRI_atS_ends`, `backend_prefix_cleanupPRI_at_ends`,
  `prefix_related_cleanupPRI_at_ends`, `prefix_relatedPRI_atE_ends`;
* `backend_prefixPRI_atSGE_ends`, `backend_prefix_cleanupPRI_atGE_ends`,
  `backend_prefixPRI_atEGE_ends`, **`prefix_relatedPRI_atEG_ends`**.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

/-- **The run ends**: it returns or traps (it neither gets stuck nor runs out of fuel). -/
def RunEnds (o : Clif.Outcome) : Prop := (∃ v m, o = .returned v m) ∨ ∃ c, o = .trapped c

theorem runEnds_returned {o : Clif.Outcome} {v : List Clif.Val} {m : Clif.Mem}
    (h : o = .returned v m) : RunEnds o := .inl ⟨v, m, h⟩

theorem runEnds_trapped {o : Clif.Outcome} {c : Clif.TrapCode} (h : o = .trapped c) : RunEnds o :=
  .inr ⟨c, h⟩

/-- **The run from a reached state of an ending run ends.** -/
theorem runLoop_ends_reachN {env : Clif.Env} {p : Clif.Program} {cs : Clif.State} {fuel : Nat}
    (hrun : RunEnds (Clif.runLoop env p fuel cs)) {t : Clif.State} {n : Nat}
    (hr : ReachN env p cs t n) : ∃ fuel', RunEnds (Clif.runLoop env p fuel' t) := by
  induction hr with
  | refl => exact ⟨fuel, hrun⟩
  | @snoc s s' k _ hs ih =>
    obtain ⟨f, hf⟩ := ih
    cases f with
    | zero => rcases hf with ⟨_, _, h⟩ | ⟨_, h⟩ <;> simp at h
    | succ f =>
      rw [Clif.runLoop_succ, hs] at hf
      exact ⟨f, hf⟩

/-- **A state of an ending run that neither returns nor traps steps.** -/
theorem next_of_ends {env : Clif.Env} {p : Clif.Program} {t : Clif.State} {fuel : Nat}
    (hrun : RunEnds (Clif.runLoop env p fuel t)) (hnd : ∀ v m, Clif.step env p t ≠ .done v m)
    (hnt : ∀ c, Clif.step env p t ≠ .trapped c) :
    ∃ t' fuel', Clif.step env p t = .next t' ∧ RunEnds (Clif.runLoop env p fuel' t') := by
  cases fuel with
  | zero => rcases hrun with ⟨_, _, h⟩ | ⟨_, h⟩ <;> simp at h
  | succ f =>
    rw [Clif.runLoop_succ] at hrun
    cases hs : Clif.step env p t with
    | next t' => rw [hs] at hrun; exact ⟨t', f, rfl, hrun⟩
    | done v' m' => exact absurd hs (hnd v' m')
    | trapped c => exact absurd hs (hnt c)
    | stuck msg => rw [hs] at hrun; rcases hrun with ⟨_, _, h⟩ | ⟨_, h⟩ <;> cases h

/-- A call-like statement is not an explicitly trapping instruction. -/
theorem not_explicitTrap_of_callLike {i : Clif.Inst} (hcl : i.isCallLike = true) :
    explicitTrapInst i = false := by
  unfold explicitTrapInst
  split
  · cases hcl
  · rfl

/-- **The counted VCode run passes the call of a calling state of an ending run**
(`iselSim_prefixWI_next` for `RunEnds`). -/
theorem iselSim_prefixWI_next_ends {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : Compiled f k vc vcp rf af fa fb)
    (hone : InstCallsOne f) (htc : TryCallsOne f)
    {XI : ExtSemI} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    {F : BitVec 64 → Prop} {c : BitVec 64} {args : List Clif.Val} {cs : Clif.State}
    (hX : ∀ s n, ReachN env p cs s n →
      XCallsOk (env.only (Clif.Invoked env p s)) (f.externs.map (·.2))
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n) ∧
      XCallsIndOk (env.only (Clif.Invoked env p s)) (indSigs f)
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n))
    (hsym : ∀ n b, syms n = some b → XI.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {w₀ : Arm.ArmState} (ρ₀ : Nat → CV)
    (hce : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀) (htr : TrapsExplicit env p cs)
    {fuel : Nat} (hrun : RunEnds (Clif.runLoop env p fuel cs)) :
    ∀ t n, ReachN env p cs t n → callNum t = 1 →
      ∃ b k ρ w, Star (VStep vc (csemI F ⟨fa.k, af.slotBase⟩ XI)) (.run ⟨0, 0, ρ₀, (w₀, 0)⟩)
        (.run ⟨b, k, ρ, (w, n + 1)⟩) := by
  intro t n hr hcn
  obtain ⟨ctx, st0, R, gn, bl, A, hshape, hcert, hbr⟩ := loweringObligations_of_check hc.lowerOk
  let Γ : Rel := ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩
  have Hb : ∀ n, DriverHyp f vc ctx st0 R gn bl A (csem F ⟨fa.k, af.slotBase⟩ (XI.at n).noCall)
      (RelW Γ f c) (env.only fun _ _ _ => False) p := fun n =>
    driverHyp_relW hsub hc hshape hcert hbr (xCallsOk_none _ _ _ _) (xCallsIndOk_none _ _ _ _)
      hsym hslot
  have Hs : ∀ s n, ReachN env p cs s n → DriverHyp f vc ctx st0 R gn bl A
      (csem F ⟨fa.k, af.slotBase⟩ (XI.at n)) (RelW Γ f c) (env.only (Clif.Invoked env p s)) p :=
    fun s n hr => driverHyp_relW hsub hc hshape hcert hbr (hX s n hr).1 (hX s n hr).2 hsym hslot
  have hseg : ∀ b B j stm, f.blocks[b]? = some B → B.body[j]? = some stm →
      stm.inst.isCallLike = true → callsI (seg f R bl b j) = 1 :=
    fun _ _ _ _ hB hstm hcl => segCalls_of (Hb 0) hone hB hstm hcl
  obtain ⟨B0, hent, hbody, hterm, hty, hregs⟩ := hce.entry
  have hB0 : f.blocks[0]? = some B0 := by
    simpa [Clif.Function.entry?, List.head?_eq_getElem?] using hent
  have hP : RunPrem env p f cs := by
    have hf := hce.func
    exact ⟨htr.stmt, fun s c fn args et hr hs hb hT B hB => htr.tryCall s c fn args et hr hs hb hT B
        (hf ▸ hB),
      fun s c callee args et hr hs hb hT B hB =>
        htr.tryCallInd s c callee args et hr hs hb hT B (hf ▸ hB),
      fun s st rest sig callee args hr hb hi ⟨B, hB, hst⟩ =>
        htr.indirect s st rest sig callee args hr hb hi ⟨B, hf ▸ hB, hst⟩,
      fun s callee args et hr hb hT ⟨B, hB, e⟩ =>
        htr.tryIndirect s callee args et hr hb hT ⟨B, hf ▸ hB, e⟩⟩
  obtain ⟨k0, ρ₁, w₁, hstar, hm⟩ := entry_step (Hb 0)
    (driverSem_csem F ⟨fa.k, af.slotBase⟩ (XI.at 0).noCall)
    (memRefines_csem _ _ (XI.at 0).noCall hslot hsym) (mrStable_relW Γ f c) hB0 hce.callers
    hce.func rfl hbody hterm hregs hty.symm hce.sig (ρ₀ := ρ₀) hrel hargs
  obtain ⟨b, k', ρ, w, hst, hmt⟩ :=
    sim_prefix_call (sem := fun n => csem F ⟨fa.k, af.slotBase⟩ (XI.at n))
      (semB := fun n => csem F ⟨fa.k, af.slotBase⟩ (XI.at n).noCall) (noncallIndep_csem _ _ XI)
      (probeOf_csem _ _ XI) hP Hb Hs hseg htc hm hr hcn
  have hpre := (vstar_mapW (csem_noCall_proj F ⟨fa.k, af.slotBase⟩ XI 0) hstar).trans hst
  obtain ⟨fuel', hrun'⟩ := runLoop_ends_reachN hrun hr
  cases hbt : t.frame.body with
  | cons st rest =>
    have hcl : st.inst.isCallLike = true := by
      simp only [callNum, hbt] at hcn
      split at hcn
      · assumption
      · cases hcn
    have hnt : ∀ c, Clif.step env p t ≠ .trapped c := fun c hs => by
      have hd := hP.stmt t c st rest hr.reach hs hbt
      rw [not_explicitTrap_of_callLike hcl] at hd
      cases hd
    obtain ⟨t', -, hs', -⟩ := next_of_ends hrun' (step_ne_done_of_callNum hcn) hnt
    obtain ⟨-, -, -, -, B, j, hB, -, -, hbd, -⟩ := id hmt
    have hst : st ∈ B.body := by
      rw [hbd] at hbt
      exact List.mem_of_mem_drop (hbt ▸ List.mem_cons_self)
    have hBmem : B ∈ f.blocks := List.mem_of_getElem? hB
    have hind : ∀ sig callee args, st.inst = .callIndirect sig callee args → ∀ cv,
        t.frame.get callee = .ok cv → ∀ g ∈ p.funcs, t.mem.symbols g.name ≠ some cv.toNat :=
      fun sig callee args hi => hP.indirect t st rest sig callee args hr.reach hbt hi
        ⟨B, hBmem, hst⟩
    obtain ⟨S1, -⟩ := stmt_stepG_call (sem := fun n => csem F ⟨fa.k, af.slotBase⟩ (XI.at n))
      (noncallIndep_csem _ _ XI) (Hs t n hr) hseg hmt hbt hcl hind
    obtain ⟨b', k'', ρ', w', hst', -⟩ := S1 t' hs'
    exact ⟨b', k'', ρ', w', hpre.trans hst'⟩
  | nil =>
    have hty : t.frame.term.isTry = true := by
      simp only [callNum, hbt] at hcn
      split at hcn
      · assumption
      · cases hcn
    obtain ⟨B, j, hB, hterm, -⟩ := hmt.2.2.2.2
    have hBmem : B ∈ f.blocks := List.mem_of_getElem? hB
    obtain ⟨et, hT⟩ : ∃ et, IsTryWith t.frame.term et := by
      cases ht : t.frame.term with
      | tryCall fn args et => exact ⟨et, .inl ⟨fn, args, rfl⟩⟩
      | tryCallIndirect c args et => exact ⟨et, .inr ⟨c, args, rfl⟩⟩
      | _ => rw [ht] at hty; cases hty
    have hnt : ∀ c, Clif.step env p t ≠ .trapped c := fun c hs => by
      rcases hT with ⟨fn, args, ht⟩ | ⟨callee, args, ht⟩
      · exact hP.tryCall t c fn args et hr.reach hs hbt ht B hBmem (hterm.symm.trans ht)
      · exact hP.tryCallInd t c callee args et hr.reach hs hbt ht B hBmem (hterm.symm.trans ht)
    obtain ⟨t', fuel'', hs', hrun''⟩ := next_of_ends hrun' (step_ne_done_of_callNum hcn) hnt
    have hind : ∀ callee args, t.frame.term = .tryCallIndirect callee args et → ∀ cv,
        t.frame.get callee = .ok cv → ∀ g ∈ p.funcs, t.mem.symbols g.name ≠ some cv.toNat :=
      fun callee args ht => hP.tryIndirect t callee args et hr.reach hbt ht
        ⟨B, hBmem, hterm.symm.trans ht⟩
    obtain ⟨-, Tnx⟩ := term_step_tryG (sem := fun n => csem F ⟨fa.k, af.slotBase⟩ (XI.at n))
      (noncallIndep_csem _ _ XI) (Hs t n hr) htc hmt hbt hT hind
    have hstep : Clif.step (env.only (Clif.Invoked env p t)) p t = Clif.step env p t :=
      Clif.step_only fun _ _ _ h => h
    obtain ⟨-, hnt', hnd, N3⟩ := Tnx t' (hstep.trans hs')
    have hstep' : Clif.step (env.only (Clif.Invoked env p t)) p t' = Clif.step env p t' := by
      apply Clif.step_only
      intro _ _ _ ⟨_, hI⟩
      obtain ⟨⟨hb', -⟩, -⟩ := Tnx t' (hstep.trans hs')
      obtain ⟨bc, hj⟩ := (Tnx t' (hstep.trans hs')).1.2
      simp [hb', hj] at hI
    obtain ⟨t'', -, hs'', -⟩ := next_of_ends hrun'' (fun v m h => hnd v m (hstep'.trans h))
      (fun c h => hnt' c (hstep'.trans h))
    obtain ⟨b', k'', ρ', w', hst2, -⟩ := N3 t'' (hstep'.trans hs'')
    exact ⟨b', k'', ρ', w', hpre.trans hst2⟩

/-- **`iselSim_prefixWI_next_cleanup` for an ending run.** -/
theorem iselSim_prefixWI_next_cleanup_ends {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledCleanup f k vc vcp rf af fa fb)
    (hone : InstCallsOne f) (htc : TryCallsOne f)
    {XI : ExtSemI} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    {F : BitVec 64 → Prop} {c : BitVec 64} {args : List Clif.Val} {cs : Clif.State}
    (hX : ∀ s n, ReachN env p cs s n →
      XCallsOk (env.only (Clif.Invoked env p s)) (f.externs.map (·.2))
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n) ∧
      XCallsIndOk (env.only (Clif.Invoked env p s)) (indSigs f)
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n))
    (hsym : ∀ n b, syms n = some b → XI.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {w₀ : Arm.ArmState} (ρ₀ : Nat → CV)
    (hce : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀) (htr : TrapsExplicit env p cs)
    {fuel : Nat} (hrun : RunEnds (Clif.runLoop env p fuel cs)) :
    ∀ t n, ReachN env p cs t n → callNum t = 1 →
      ∃ b k ρ w, Star (VStep vc (valueSemI F ⟨fa.k, af.slotBase⟩ XI)) (.run ⟨0, 0, ρ₀, (w₀, 0)⟩)
        (.run ⟨b, k, ρ, (w, n + 1)⟩) := by
  intro t n hr hcn
  obtain ⟨ctx, st0, R, gn, bl, A, hshape, hcert, hbr⟩ := loweringObligations_of_check hc.lowerOk
  let Γ : Rel := ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩
  have Hb : ∀ n, DriverHyp f vc ctx st0 R gn bl A
      (valueSem F ⟨fa.k, af.slotBase⟩ (XI.at n).noCall)
      (RelW Γ f c) (env.only fun _ _ _ => False) p := fun n =>
    driverHyp_relW_cleanup hsub hc hshape hcert hbr (xCallsOk_none _ _ _ _)
      (xCallsIndOk_none _ _ _ _) hsym hslot
  have Hs : ∀ s n, ReachN env p cs s n → DriverHyp f vc ctx st0 R gn bl A
      (valueSem F ⟨fa.k, af.slotBase⟩ (XI.at n)) (RelW Γ f c) (env.only (Clif.Invoked env p s)) p :=
    fun s n hr => driverHyp_relW_cleanup hsub hc hshape hcert hbr (hX s n hr).1 (hX s n hr).2
      hsym hslot
  have hseg : ∀ b B j stm, f.blocks[b]? = some B → B.body[j]? = some stm →
      stm.inst.isCallLike = true → callsI (seg f R bl b j) = 1 :=
    fun _ _ _ _ hB hstm hcl => segCalls_of (Hb 0) hone hB hstm hcl
  obtain ⟨B0, hent, hbody, hterm, hty, hregs⟩ := hce.entry
  have hB0 : f.blocks[0]? = some B0 := by
    simpa [Clif.Function.entry?, List.head?_eq_getElem?] using hent
  have hP : RunPrem env p f cs := by
    have hf := hce.func
    exact ⟨htr.stmt, fun s c fn args et hr hs hb hT B hB => htr.tryCall s c fn args et hr hs hb hT B
        (hf ▸ hB),
      fun s c callee args et hr hs hb hT B hB =>
        htr.tryCallInd s c callee args et hr hs hb hT B (hf ▸ hB),
      fun s st rest sig callee args hr hb hi ⟨B, hB, hst⟩ =>
        htr.indirect s st rest sig callee args hr hb hi ⟨B, hf ▸ hB, hst⟩,
      fun s callee args et hr hb hT ⟨B, hB, e⟩ =>
        htr.tryIndirect s callee args et hr hb hT ⟨B, hf ▸ hB, e⟩⟩
  have hPr := probeOf_valueSem F ⟨fa.k, af.slotBase⟩ XI
  obtain ⟨k0, ρ₁, w₁, hstar, hm⟩ := entry_step (Hb 0)
    (driverSem_valueSem F ⟨fa.k, af.slotBase⟩ (XI.at 0).noCall)
    (memRefines_valueSem _ _ (XI.at 0).noCall hslot hsym) (mrStable_relW Γ f c) hB0 hce.callers
    hce.func rfl hbody hterm hregs hty.symm hce.sig (ρ₀ := ρ₀) hrel hargs
  obtain ⟨b, k', ρ, w, hst, hmt⟩ :=
    sim_prefix_call (noncallIndep_valueSem F ⟨fa.k, af.slotBase⟩ XI) hPr hP Hb Hs hseg htc hm hr hcn
  have hpre := (vstar_mapW (counted_probe_proj hPr 0) hstar).trans hst
  obtain ⟨fuel', hrun'⟩ := runLoop_ends_reachN hrun hr
  cases hbt : t.frame.body with
  | cons st rest =>
    have hcl : st.inst.isCallLike = true := by
      simp only [callNum, hbt] at hcn
      split at hcn
      · assumption
      · cases hcn
    have hnt : ∀ c, Clif.step env p t ≠ .trapped c := fun c hs => by
      have hd := hP.stmt t c st rest hr.reach hs hbt
      rw [not_explicitTrap_of_callLike hcl] at hd
      cases hd
    obtain ⟨t', -, hs', -⟩ := next_of_ends hrun' (step_ne_done_of_callNum hcn) hnt
    obtain ⟨-, -, -, -, B, j, hB, -, -, hbd, -⟩ := id hmt
    have hst : st ∈ B.body := by
      rw [hbd] at hbt
      exact List.mem_of_mem_drop (hbt ▸ List.mem_cons_self)
    have hBmem : B ∈ f.blocks := List.mem_of_getElem? hB
    have hind : ∀ sig callee args, st.inst = .callIndirect sig callee args → ∀ cv,
        t.frame.get callee = .ok cv → ∀ g ∈ p.funcs, t.mem.symbols g.name ≠ some cv.toNat :=
      fun sig callee args hi => hP.indirect t st rest sig callee args hr.reach hbt hi
        ⟨B, hBmem, hst⟩
    obtain ⟨S1, -⟩ := stmt_stepG_call (sem := fun n => valueSem F ⟨fa.k, af.slotBase⟩ (XI.at n))
      (noncallIndep_valueSem F ⟨fa.k, af.slotBase⟩ XI) (Hs t n hr) hseg hmt hbt hcl hind
    obtain ⟨b', k'', ρ', w', hst', -⟩ := S1 t' hs'
    exact ⟨b', k'', ρ', w', hpre.trans hst'⟩
  | nil =>
    have hty : t.frame.term.isTry = true := by
      simp only [callNum, hbt] at hcn
      split at hcn
      · assumption
      · cases hcn
    obtain ⟨B, j, hB, hterm, -⟩ := hmt.2.2.2.2
    have hBmem : B ∈ f.blocks := List.mem_of_getElem? hB
    obtain ⟨et, hT⟩ : ∃ et, IsTryWith t.frame.term et := by
      cases ht : t.frame.term with
      | tryCall fn args et => exact ⟨et, .inl ⟨fn, args, rfl⟩⟩
      | tryCallIndirect c args et => exact ⟨et, .inr ⟨c, args, rfl⟩⟩
      | _ => rw [ht] at hty; cases hty
    have hnt : ∀ c, Clif.step env p t ≠ .trapped c := fun c hs => by
      rcases hT with ⟨fn, args, ht⟩ | ⟨callee, args, ht⟩
      · exact hP.tryCall t c fn args et hr.reach hs hbt ht B hBmem (hterm.symm.trans ht)
      · exact hP.tryCallInd t c callee args et hr.reach hs hbt ht B hBmem (hterm.symm.trans ht)
    obtain ⟨t', fuel'', hs', hrun''⟩ := next_of_ends hrun' (step_ne_done_of_callNum hcn) hnt
    have hind : ∀ callee args, t.frame.term = .tryCallIndirect callee args et → ∀ cv,
        t.frame.get callee = .ok cv → ∀ g ∈ p.funcs, t.mem.symbols g.name ≠ some cv.toNat :=
      fun callee args ht => hP.tryIndirect t callee args et hr.reach hbt ht
        ⟨B, hBmem, hterm.symm.trans ht⟩
    obtain ⟨-, Tnx⟩ := term_step_tryG (sem := fun n => valueSem F ⟨fa.k, af.slotBase⟩ (XI.at n))
      (noncallIndep_valueSem F ⟨fa.k, af.slotBase⟩ XI) (Hs t n hr) htc hmt hbt hT hind
    have hstep : Clif.step (env.only (Clif.Invoked env p t)) p t = Clif.step env p t :=
      Clif.step_only fun _ _ _ h => h
    obtain ⟨-, hnt', hnd, N3⟩ := Tnx t' (hstep.trans hs')
    have hstep' : Clif.step (env.only (Clif.Invoked env p t)) p t' = Clif.step env p t' := by
      apply Clif.step_only
      intro _ _ _ ⟨_, hI⟩
      obtain ⟨⟨hb', -⟩, -⟩ := Tnx t' (hstep.trans hs')
      obtain ⟨bc, hj⟩ := (Tnx t' (hstep.trans hs')).1.2
      simp [hb', hj] at hI
    obtain ⟨t'', -, hs'', -⟩ := next_of_ends hrun'' (fun v m h => hnd v m (hstep'.trans h))
      (fun c h => hnt' c (hstep'.trans h))
    obtain ⟨b', k'', ρ', w', hst2, -⟩ := N3 t'' (hstep'.trans hs'')
    exact ⟨b', k'', ρ', w', hpre.trans hst2⟩

/-- **`iselSim_prefixWI_next_cleanup_ends` for the code after the skip of unused instructions**
(`skipStage f vc`, which the cleanup stage prunes and prepares). -/
theorem iselSim_prefixWI_next_cleanup_ends_stage {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledCleanup f k vc vcp rf af fa fb)
    (hone : InstCallsOne f) (htc : TryCallsOne f)
    {XI : ExtSemI} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    {F : BitVec 64 → Prop} {c : BitVec 64} {args : List Clif.Val} {cs : Clif.State}
    (hX : ∀ s n, ReachN env p cs s n →
      XCallsOk (env.only (Clif.Invoked env p s)) (f.externs.map (·.2))
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n) ∧
      XCallsIndOk (env.only (Clif.Invoked env p s)) (indSigs f)
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n))
    (hsym : ∀ n b, syms n = some b → XI.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {w₀ : Arm.ArmState} (ρ₀ : Nat → CV)
    (hce : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀) (htr : TrapsExplicit env p cs)
    {fuel : Nat} (hrun : RunEnds (Clif.runLoop env p fuel cs)) :
    ∀ t n, ReachN env p cs t n → callNum t = 1 →
      ∃ b k ρ w, Star (VStep (skipStage f vc) (valueSemI F ⟨fa.k, af.slotBase⟩ XI))
        (.run ⟨0, 0, ρ₀, (w₀, 0)⟩) (.run ⟨b, k, ρ, (w, n + 1)⟩) := by
  intro t n hr hcn
  obtain ⟨ctx, st0, R, gn, bl, A, hshape, hcert, hbr, hsk⟩ := skipStage_spec hc.lowerOk
  rcases hsk with heq | hK
  · rw [heq]
    exact iselSim_prefixWI_next_cleanup_ends hsub hc hone htc hX hsym hslot ρ₀ hce hrel hargs htr
      hrun t n hr hcn
  let Γ : Rel := ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩
  have Hb : ∀ n, DriverHyp f vc ctx st0 R gn bl A
      (valueSem F ⟨fa.k, af.slotBase⟩ (XI.at n).noCall)
      (RelW Γ f c) (env.only fun _ _ _ => False) p := fun n =>
    driverHyp_relW_cleanup hsub hc hshape hcert hbr (xCallsOk_none _ _ _ _)
      (xCallsIndOk_none _ _ _ _) hsym hslot
  have Hs : ∀ s n, ReachN env p cs s n → DriverHyp f vc ctx st0 R gn bl A
      (valueSem F ⟨fa.k, af.slotBase⟩ (XI.at n)) (RelW Γ f c) (env.only (Clif.Invoked env p s)) p :=
    fun s n hr => driverHyp_relW_cleanup hsub hc hshape hcert hbr (hX s n hr).1 (hX s n hr).2
      hsym hslot
  have hseg : ∀ b B j stm, f.blocks[b]? = some B → B.body[j]? = some stm →
      stm.inst.isCallLike = true → callsI (seg f R bl b j) = 1 :=
    fun _ _ _ _ hB hstm hcl => segCalls_of (Hb 0) hone hB hstm hcl
  obtain ⟨B0, hent, hbody, hterm, hty, hregs⟩ := hce.entry
  have hB0 : f.blocks[0]? = some B0 := by
    simpa [Clif.Function.entry?, List.head?_eq_getElem?] using hent
  have hP : RunPrem env p f cs := by
    have hf := hce.func
    exact ⟨htr.stmt, fun s c fn args et hr hs hb hT B hB => htr.tryCall s c fn args et hr hs hb hT B
        (hf ▸ hB),
      fun s c callee args et hr hs hb hT B hB =>
        htr.tryCallInd s c callee args et hr hs hb hT B (hf ▸ hB),
      fun s st rest sig callee args hr hb hi ⟨B, hB, hst⟩ =>
        htr.indirect s st rest sig callee args hr hb hi ⟨B, hf ▸ hB, hst⟩,
      fun s callee args et hr hb hT ⟨B, hB, e⟩ =>
        htr.tryIndirect s callee args et hr hb hT ⟨B, hf ▸ hB, e⟩⟩
  have hPr := probeOf_valueSem F ⟨fa.k, af.slotBase⟩ XI
  obtain ⟨k0, ρ₁, w₁, hstar, hm⟩ := entry_stepP (Hb 0)
    (driverSem_valueSem F ⟨fa.k, af.slotBase⟩ (XI.at 0).noCall)
    (memRefines_valueSem _ _ (XI.at 0).noCall hslot hsym) (mrStable_relW Γ f c) hB0 hce.callers
    hce.func rfl hbody hterm hregs hty.symm hce.sig (ρ₀ := ρ₀) hrel hargs
  obtain ⟨⟨b1, k1, ρ1, w1⟩, hsK, hmK⟩ := entry_matchK hK hB0 hbody hstar hm
  obtain ⟨b, k', ρ, w, hst, hmt⟩ :=
    sim_prefix_callK hK (noncallIndep_valueSem F ⟨fa.k, af.slotBase⟩ XI) hPr hP Hb Hs hseg htc hmK
      hr hcn
  have hpre := (vstar_mapW (counted_probe_proj hPr 0) hsK).trans hst
  obtain ⟨vsF, -, hMF⟩ := id hmt
  obtain ⟨fuel', hrun'⟩ := runLoop_ends_reachN hrun hr
  cases hbt : t.frame.body with
  | cons st rest =>
    have hcl : st.inst.isCallLike = true := by
      simp only [callNum, hbt] at hcn
      split at hcn
      · assumption
      · cases hcn
    have hnt : ∀ c, Clif.step env p t ≠ .trapped c := fun c hs => by
      have hd := hP.stmt t c st rest hr.reach hs hbt
      rw [not_explicitTrap_of_callLike hcl] at hd
      cases hd
    obtain ⟨t', -, hs', -⟩ := next_of_ends hrun' (step_ne_done_of_callNum hcn) hnt
    obtain ⟨-, -, -, -, B, j, hB, -, -, hbd, -⟩ := id hMF
    have hst : st ∈ B.body := by
      rw [hbd] at hbt
      exact List.mem_of_mem_drop (hbt ▸ List.mem_cons_self)
    have hBmem : B ∈ f.blocks := List.mem_of_getElem? hB
    have hind : ∀ sig callee args, st.inst = .callIndirect sig callee args → ∀ cv,
        t.frame.get callee = .ok cv → ∀ g ∈ p.funcs, t.mem.symbols g.name ≠ some cv.toNat :=
      fun sig callee args hi => hP.indirect t st rest sig callee args hr.reach hbt hi
        ⟨B, hBmem, hst⟩
    obtain ⟨S1, -⟩ := stmt_stepG_callK hK (sem := fun n => valueSem F ⟨fa.k, af.slotBase⟩ (XI.at n))
      (noncallIndep_valueSem F ⟨fa.k, af.slotBase⟩ XI) (Hs t n hr) hseg hmt hbt hcl hind
    obtain ⟨b', k'', ρ', w', hst', -⟩ := S1 t' hs'
    exact ⟨b', k'', ρ', w', hpre.trans hst'⟩
  | nil =>
    have hty : t.frame.term.isTry = true := by
      simp only [callNum, hbt] at hcn
      split at hcn
      · assumption
      · cases hcn
    obtain ⟨B, j, hB, hterm, -⟩ := hMF.2.2.2.2
    have hBmem : B ∈ f.blocks := List.mem_of_getElem? hB
    obtain ⟨et, hT⟩ : ∃ et, IsTryWith t.frame.term et := by
      cases ht : t.frame.term with
      | tryCall fn args et => exact ⟨et, .inl ⟨fn, args, rfl⟩⟩
      | tryCallIndirect c args et => exact ⟨et, .inr ⟨c, args, rfl⟩⟩
      | _ => rw [ht] at hty; cases hty
    have hnt : ∀ c, Clif.step env p t ≠ .trapped c := fun c hs => by
      rcases hT with ⟨fn, args, ht⟩ | ⟨callee, args, ht⟩
      · exact hP.tryCall t c fn args et hr.reach hs hbt ht B hBmem (hterm.symm.trans ht)
      · exact hP.tryCallInd t c callee args et hr.reach hs hbt ht B hBmem (hterm.symm.trans ht)
    obtain ⟨t', fuel'', hs', hrun''⟩ := next_of_ends hrun' (step_ne_done_of_callNum hcn) hnt
    have hind : ∀ callee args, t.frame.term = .tryCallIndirect callee args et → ∀ cv,
        t.frame.get callee = .ok cv → ∀ g ∈ p.funcs, t.mem.symbols g.name ≠ some cv.toNat :=
      fun callee args ht => hP.tryIndirect t callee args et hr.reach hbt ht
        ⟨B, hBmem, hterm.symm.trans ht⟩
    obtain ⟨-, Tnx⟩ := term_step_tryGK hK (sem := fun n => valueSem F ⟨fa.k, af.slotBase⟩ (XI.at n))
      (noncallIndep_valueSem F ⟨fa.k, af.slotBase⟩ XI) (Hs t n hr) htc hmt hbt hT hind
    have hstep : Clif.step (env.only (Clif.Invoked env p t)) p t = Clif.step env p t :=
      Clif.step_only fun _ _ _ h => h
    obtain ⟨-, hnt', hnd, N3⟩ := Tnx t' (hstep.trans hs')
    have hstep' : Clif.step (env.only (Clif.Invoked env p t)) p t' = Clif.step env p t' := by
      apply Clif.step_only
      intro _ _ _ ⟨_, hI⟩
      obtain ⟨⟨hb', -⟩, -⟩ := Tnx t' (hstep.trans hs')
      obtain ⟨bc, hj⟩ := (Tnx t' (hstep.trans hs')).1.2
      simp [hb', hj] at hI
    obtain ⟨t'', -, hs'', -⟩ := next_of_ends hrun'' (fun v m h => hnd v m (hstep'.trans h))
      (fun c h => hnt' c (hstep'.trans h))
    obtain ⟨b', k'', ρ', w', hst2, -⟩ := N3 t'' (hstep'.trans hs'')
    exact ⟨b', k'', ρ', w', hpre.trans hst2⟩

/-- **`backend_prefix_cleanupPRI_at` for an ending run.** -/
theorem backend_prefix_cleanupPRI_at_ends {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledCleanup f k vc vcp rf af fa fb)
    (hone : InstCallsOne f) (htc : TryCallsOne f)
    {XI : ExtSemI} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hX : ∀ s n, ReachN env p cs s n →
      XCallsOk (env.only (Clif.Invoked env p s)) (f.externs.map (·.2))
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n) ∧
      XCallsIndOk (env.only (Clif.Invoked env p s)) (indSigs f)
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n))
    (hsym : ∀ n b, syms n = some b → XI.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : TrapsExplicit env p cs) {fuel : Nat} (hrun : RunEnds (Clif.runLoop env p fuel cs))
    {N : Nat} {H : ArmHooks}
    {G : BitVec 64 → Prop} {base ra : BitVec 64} {Kp : Nat} {cc : BitVec 64}
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {s : Arm.ArmState}
    (he : ActEntryPRN vcp rf af fa fb K F G XI H base ra Kp cc P R s w₀ N)
    {t : Clif.State} (hr : ReachN env p cs t N) (hcn : callNum t = 1) :
    ∀ j ≤ N, ∃ u i info uses w r, OnCallG (ArmStepX (XI.at 0) H fa) fa base s
        (fun t => ¬ PostCall fa base (Arm.r .PC t) ∨
          spOf t = spv s - BitVec.ofNat 64 (frameDrop af)) j u ∧
      spOf u = spv s - BitVec.ofNat 64 (frameDrop af) ∧ CallSiteAt F K G s fa base i uses w u ∧
      (i = .call info ∨ ∃ ti, i = .tryCall info ti) ∧ vcp.CallSite info ∧
      gotGuard (GotV vcp) (XI.at 0) info uses ∧
      (XI.at j).call (callDest info) uses w = some r := by
  intro j hj
  obtain ⟨b, k, ρ, w, hstar⟩ :=
    iselSim_prefixWI_next_cleanup_ends_stage hsub hc hone htc hX hsym hslot (fun _ => 0) hcs hrel
      hargs
      htr hrun t N hr hcn
  obtain ⟨b1, k1, ρ1, w1, vb, i, ops, r, hs1, hvb, hi, hcall, hops, hsem⟩ :=
    vstar_call_at (j := j) hstar (Nat.zero_le _) (by simp only [vctr]; omega)
  obtain ⟨info, hci⟩ := callLike_of_isCallI hcall
  have hsemC : csem F ⟨fa.k, af.slotBase⟩ (XI.at j) i
      ((ops.toList.filter Operand.isUse).map (ρ1 ·.vreg)) w1 = some r := by
    rw [← valueSem_callLike hci]; exact hsem
  obtain ⟨r', hr'⟩ := csem_call_some hci hsemC
  have hkeep : pureForm i = false ∧ cmpForm i = false ∧ isJump i = false := by
    rcases hci with rfl | ⟨ti, rfl⟩ <;> exact ⟨rfl, rfl, rfl⟩
  obtain ⟨vb2, k2, a2, hs2, hvb2, hi2, hu2⟩ := prune_prefixW (sem := valueSemI F ⟨fa.k, af.slotBase⟩ XI)
    (fun _ _ _ _ _ _ hi hs => counted_pure (fun _ _ _ _ _ _ _ hp he => valueSem_pure hp he) hi hs)
    (cmpOverwrite_counted fun n => valueSem_cmpOverwrite _ _ _) hs1 hvb hi hops hkeep.1 hkeep.2.1
    hkeep.2.2
  have hds := DriverSemG.counted fun m =>
    (driverSem_valueSem F ⟨fa.k, af.slotBase⟩ (XI.at m)).toDriverSemG
  obtain ⟨b3, hs3, hins⟩ := prep_prefixW hds hc.prepOk hs2
  obtain ⟨vb3, i3, hvb3, hi3, hsame⟩ := hins vb2 i hvb2 hi2
  obtain ⟨hs4, hinv4⟩ := gotInvI_star_value
    (show GotInvI vcp XI ⟨0, 0, fun _ => 0, (w₀, 0)⟩ from gotInv_entry vcp (XI.at 0) _ w₀) hs3
  have hci3 := sameInst_callLike hsame hci
  have hops3 : i3.operands = .ok ops := by rw [(sameInst_factsW hds hsame).1, hops]
  have hM := regLevel_value_prefixPRSG hc.check hc.alloc hc.emit hc.layout (XI := XI) (H := H)
    (K := K) (G := G) (gv := GotV vcp) (N := j) hcov he.abi he.stack he.gfree he.proph he.regp
    (fun n hn => by rw [he.hF]; exact he.calls n (by omega))
    (fun ht n hn => by rw [he.hF]; exact he.tries ht n (by omega)) he.pc
    (by rw [he.hF]; exact he.tls) (by rw [he.hF]; exact he.body) (fun _ => 0)
  rw [he.hF] at hM
  obtain ⟨u, hon, hsp, hsite⟩ := hM b3 k2 a2 w1 vb3 i3 hs4 hvb3 hi3 ⟨info, hci3⟩ ops hops3
  have hgd := gotGuard_of_inv hinv4 hvb3 hi3 hops3 info hci3
  refine ⟨u, i3, info, _, w1, r', hon, hsp, hsite, hci3, ⟨b3, vb3, k2, hvb3, ?_⟩, hgd, ?_⟩
  · rcases hci3 with rfl | ⟨ti, rfl⟩
    · exact .inl hi3
    · exact .inr ⟨ti, hi3⟩
  have hu2' : (ops.toList.filter Operand.isUse).map (a2 ·.vreg) =
      (ops.toList.filter Operand.isUse).map (ρ1 ·.vreg) := hu2.symm
  rw [hu2']; exact hr'

/-- **`prefix_related_cleanupPRI_at` for an ending run.** -/
theorem prefix_related_cleanupPRI_at_ends {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledCleanup f k vc vcp rf af fa fb)
    (hone : InstCallsOne f) (htc : TryCallsOne f)
    {XI : ExtSemI} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hnrc : NoRetCall env p cs)
    (hX : ∀ s n, ReachN env p cs s n →
      XCallsOk (env.only (Clif.Invoked env p s)) (f.externs.map (·.2))
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n) ∧
      XCallsIndOk (env.only (Clif.Invoked env p s)) (indSigs f)
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n))
    (hsym : ∀ n b, syms n = some b → XI.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : TrapsExplicit env p cs) {fuel : Nat} (hrun : RunEnds (Clif.runLoop env p fuel cs))
    {N : Nat} {H : ArmHooks}
    {G : BitVec 64 → Prop} {base ra : BitVec 64} {Kp : Nat} {cc : BitVec 64}
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {s : Arm.ArmState}
    (he : ActEntryPRN vcp rf af fa fb K F G XI H base ra Kp cc P R s w₀ N)
    {t : Clif.State} (hr : ReachN env p cs t N) (hcn : callNum t = 1) :
    ∀ j ≤ N, ∃ u i info uses w r, OnCallG (ArmStepX (XI.at 0) H fa) fa base s
        (fun t => ¬ PostCall fa base (Arm.r .PC t) ∨
          spOf t = spv s - BitVec.ofNat 64 (frameDrop af)) j u ∧
      spOf u = spv s - BitVec.ofNat 64 (frameDrop af) ∧ CallSiteAt F K G s fa base i uses w u ∧
      (i = .call info ∨ ∃ ti, i = .tryCall info ti) ∧ vcp.CallSite info ∧
      gotGuard (GotV vcp) (XI.at 0) info uses ∧
      (XI.at j).call (callDest info) uses w = some r ∧
      RelatedN env p cs (f.externs.map (·.2)) (indSigs f)
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) XI.sym j (callDest info) uses w := by
  intro j hj
  obtain ⟨u, i, info, uses, w, r, hon, hsp, hsite, hci, hcs', hgd, hx⟩ :=
    backend_prefix_cleanupPRI_at_ends (XI := XI.relOnly (RelatedN env p cs (f.externs.map (·.2))
      (indSigs f) (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) XI.sym))
      hsub hc hone htc hcov (fun s n hs => xCalls_relOnly hnrc hs (hX s n hs)) hsym hslot hcs hrel
      hargs htr hrun (he.relOnly _) hr hcn j hj
  obtain ⟨hq, hx'⟩ := relOnly_call_some hx
  exact ⟨u, i, info, uses, w, r, hon, hsp, hsite, hci, hcs', hgd, hx', hq⟩

/-- **`backend_prefixPRI_atS` for an ending run.** -/
theorem backend_prefixPRI_atS_ends {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : Compiled f k vc vcp rf af fa fb)
    (hone : InstCallsOne f) (htc : TryCallsOne f)
    {XI : ExtSemI} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hX : ∀ s n, ReachN env p cs s n →
      XCallsOk (env.only (Clif.Invoked env p s)) (f.externs.map (·.2))
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n) ∧
      XCallsIndOk (env.only (Clif.Invoked env p s)) (indSigs f)
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n))
    (hsym : ∀ n b, syms n = some b → XI.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : TrapsExplicit env p cs) {fuel : Nat} (hrun : RunEnds (Clif.runLoop env p fuel cs))
    {N : Nat} {H : ArmHooks}
    {G : BitVec 64 → Prop} {base ra : BitVec 64} {Kp : Nat} {cc : BitVec 64}
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {s : Arm.ArmState}
    (he : ActEntryPRN vcp rf af fa fb K F G XI H base ra Kp cc P R s w₀ N)
    {t : Clif.State} (hr : ReachN env p cs t N) (hcn : callNum t = 1) :
    ∀ j ≤ N, ∃ u i info uses w r, OnCallG (ArmStepX (XI.at 0) H fa) fa base s
        (fun t => ¬ PostCall fa base (Arm.r .PC t) ∨
          spOf t = spv s - BitVec.ofNat 64 (frameDrop af)) j u ∧
      spOf u = spv s - BitVec.ofNat 64 (frameDrop af) ∧ CallSiteAt F K G s fa base i uses w u ∧
      (i = .call info ∨ ∃ ti, i = .tryCall info ti) ∧ vcp.CallSite info ∧
      gotGuard (GotV vcp) (XI.at 0) info uses ∧
      (XI.at j).call (callDest info) uses w = some r := by
  intro j hj
  obtain ⟨b, k, ρ, w, hstar⟩ :=
    iselSim_prefixWI_next_ends hsub hc hone htc hX hsym hslot (fun _ => 0) hcs hrel hargs htr hrun
      t N hr hcn
  obtain ⟨b', hstar', -⟩ := prep_prefixW (DriverSemG.csemI fun m =>
    (driverSem_csem F ⟨fa.k, af.slotBase⟩ (XI.at m)).toDriverSemG) hc.prepOk hstar
  obtain ⟨hstar'', -⟩ := gotInvI_star
    (show GotInvI vcp XI ⟨0, 0, fun _ => 0, (w₀, 0)⟩ from gotInv_entry vcp (XI.at 0) _ w₀) hstar'
  obtain ⟨b1, k1, ρ1, w1, vb, i, ops, r, hs1, hvb, hi, hcall, hops, hsem⟩ :=
    vstar_call_at (j := j) hstar'' (Nat.zero_le _) (by simp only [vctr]; omega)
  have hM := regLevel_prefixPRSG hc.check hc.alloc hc.emit hc.layout (XI := XI) (H := H)
    (K := K) (G := G) (gv := GotV vcp) (N := j) hcov he.abi he.stack he.gfree he.proph he.regp
    (fun n hn => by rw [he.hF]; exact he.calls n (by omega))
    (fun ht n hn => by rw [he.hF]; exact he.tries ht n (by omega)) he.pc
    (by rw [he.hF]; exact he.tls) (by rw [he.hF]; exact he.body) (fun _ => 0)
  rw [he.hF] at hM
  obtain ⟨info, hci⟩ := callLike_of_isCallI hcall
  obtain ⟨u, hon, hsp, hsite⟩ := hM b1 k1 ρ1 w1 vb i hs1 hvb hi ⟨info, hci⟩ ops hops
  obtain ⟨r', hr'⟩ := csem_call_some hci (csemV_sub hsem)
  have hgd : gotGuard (GotV vcp) (XI.at j) info ((ops.toList.filter Operand.isUse).map (ρ1 ·.vreg)) := by
    rcases hci with rfl | ⟨ti, rfl⟩
    · exact csemV_guard hsem
    · exact csemV_guard_try hsem
  refine ⟨u, i, info, _, w1, r', hon, hsp, hsite, hci, ⟨b1, vb, k1, hvb, ?_⟩, hgd, hr'⟩
  rcases hci with rfl | ⟨ti, rfl⟩
  · exact .inl hi
  · exact .inr ⟨ti, hi⟩

/-- **`prefix_relatedPRI_atS` for an ending run.** -/
theorem prefix_relatedPRI_atS_ends {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : Compiled f k vc vcp rf af fa fb)
    (hone : InstCallsOne f) (htc : TryCallsOne f)
    {XI : ExtSemI} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hnrc : NoRetCall env p cs)
    (hX : ∀ s n, ReachN env p cs s n →
      XCallsOk (env.only (Clif.Invoked env p s)) (f.externs.map (·.2))
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n) ∧
      XCallsIndOk (env.only (Clif.Invoked env p s)) (indSigs f)
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n))
    (hsym : ∀ n b, syms n = some b → XI.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : TrapsExplicit env p cs) {fuel : Nat} (hrun : RunEnds (Clif.runLoop env p fuel cs))
    {N : Nat} {H : ArmHooks}
    {G : BitVec 64 → Prop} {base ra : BitVec 64} {Kp : Nat} {cc : BitVec 64}
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {s : Arm.ArmState}
    (he : ActEntryPRN vcp rf af fa fb K F G XI H base ra Kp cc P R s w₀ N)
    {t : Clif.State} (hr : ReachN env p cs t N) (hcn : callNum t = 1) :
    ∀ j ≤ N, ∃ u i info uses w r, OnCallG (ArmStepX (XI.at 0) H fa) fa base s
        (fun t => ¬ PostCall fa base (Arm.r .PC t) ∨
          spOf t = spv s - BitVec.ofNat 64 (frameDrop af)) j u ∧
      spOf u = spv s - BitVec.ofNat 64 (frameDrop af) ∧ CallSiteAt F K G s fa base i uses w u ∧
      (i = .call info ∨ ∃ ti, i = .tryCall info ti) ∧ vcp.CallSite info ∧
      gotGuard (GotV vcp) (XI.at 0) info uses ∧
      (XI.at j).call (callDest info) uses w = some r ∧
      RelatedN env p cs (f.externs.map (·.2)) (indSigs f)
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) XI.sym j (callDest info) uses w := by
  intro j hj
  obtain ⟨u, i, info, uses, w, r, hon, hsp, hsite, hci, hcs', hgd, hx⟩ :=
    backend_prefixPRI_atS_ends (XI := XI.relOnly (RelatedN env p cs (f.externs.map (·.2))
      (indSigs f) (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) XI.sym))
      hsub hc hone htc hcov (fun s n hs => xCalls_relOnly hnrc hs (hX s n hs)) hsym hslot hcs hrel
      hargs htr hrun (he.relOnly _) hr hcn j hj
  obtain ⟨hq, hx'⟩ := relOnly_call_some hx
  exact ⟨u, i, info, uses, w, r, hon, hsp, hsite, hci, hcs', hgd, hx', hq⟩

/-- **`prefix_relatedPRI_atE` for an ending run.** -/
theorem prefix_relatedPRI_atE_ends {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledEither f k vc vcp rf af fa fb)
    (hone : InstCallsOne f) (htc : TryCallsOne f)
    {XI : ExtSemI} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hnrc : NoRetCall env p cs)
    (hX : ∀ s n, ReachN env p cs s n →
      XCallsOk (env.only (Clif.Invoked env p s)) (f.externs.map (·.2))
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n) ∧
      XCallsIndOk (env.only (Clif.Invoked env p s)) (indSigs f)
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n))
    (hsym : ∀ n b, syms n = some b → XI.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : TrapsExplicit env p cs) {fuel : Nat} (hrun : RunEnds (Clif.runLoop env p fuel cs))
    {N : Nat} {H : ArmHooks}
    {G : BitVec 64 → Prop} {base ra : BitVec 64} {Kp : Nat} {cc : BitVec 64}
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {s : Arm.ArmState}
    (he : ActEntryPRN vcp rf af fa fb K F G XI H base ra Kp cc P R s w₀ N)
    {t : Clif.State} (hr : ReachN env p cs t N) (hcn : callNum t = 1) :
    ∀ j ≤ N, ∃ u i info uses w r, OnCallG (ArmStepX (XI.at 0) H fa) fa base s
        (fun t => ¬ PostCall fa base (Arm.r .PC t) ∨
          spOf t = spv s - BitVec.ofNat 64 (frameDrop af)) j u ∧
      spOf u = spv s - BitVec.ofNat 64 (frameDrop af) ∧ CallSiteAt F K G s fa base i uses w u ∧
      (i = .call info ∨ ∃ ti, i = .tryCall info ti) ∧ vcp.CallSite info ∧
      gotGuard (GotV vcp) (XI.at 0) info uses ∧
      (XI.at j).call (callDest info) uses w = some r ∧
      RelatedN env p cs (f.externs.map (·.2)) (indSigs f)
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) XI.sym j (callDest info) uses w := by
  cases hc with
  | legacy hc =>
    exact prefix_relatedPRI_atS_ends hsub hc hone htc hcov hnrc hX hsym hslot hcs hrel hargs htr
      hrun he hr hcn
  | cleanup hc =>
    exact prefix_related_cleanupPRI_at_ends hsub hc hone htc hcov hnrc hX hsym hslot hcs hrel hargs
      htr hrun he hr hcn

/-- **`backend_prefixPRI_atSGE` for an ending run.** -/
theorem backend_prefixPRI_atSGE_ends {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : Compiled f k vc vcp rf af fa fb)
    (hone : InstCallsOne f) (htc : TryCallsOne f)
    {XI : ExtSemI} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hX : ∀ s n, ReachN env p cs s n →
      XCallsOk (env.only (Clif.Invoked env p s)) (f.externs.map (·.2))
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n) ∧
      XCallsIndOk (env.only (Clif.Invoked env p s)) (indSigs f)
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n))
    (hsym : ∀ n b, syms n = some b → XI.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : TrapsExplicit env p cs) {fuel : Nat} (hrun : RunEnds (Clif.runLoop env p fuel cs))
    {N : Nat} {H : ArmHooks}
    {G : BitVec 64 → Prop} {base ra : BitVec 64} {Kp : Nat} {cc : BitVec 64}
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {s : Arm.ArmState}
    (he : ActEntryPRN vcp rf af fa fb K F G XI H base ra Kp cc P R s w₀ N)
    {t : Clif.State} (hr : ReachN env p cs t N) (hcn : callNum t = 1) :
    ∀ j ≤ N, ∃ u, OnCallG (ArmStepX (XI.at 0) H fa) fa base s
        (fun t => (¬ PostCall fa base (Arm.r .PC t) ∨
          spOf t = spv s - BitVec.ofNat 64 (frameDrop af)) ∧ Arm.r .ERR t = .None ∧
          t.program = fb.program base) j u ∧
      CallPc fa base (Arm.r .PC u) := by
  intro j hj
  obtain ⟨b, k, ρ, w, hstar⟩ :=
    iselSim_prefixWI_next_ends hsub hc hone htc hX hsym hslot (fun _ => 0) hcs hrel hargs htr hrun
      t N hr hcn
  obtain ⟨b', hstar', -⟩ := prep_prefixW (DriverSemG.csemI fun m =>
    (driverSem_csem F ⟨fa.k, af.slotBase⟩ (XI.at m)).toDriverSemG) hc.prepOk hstar
  obtain ⟨hstar'', -⟩ := gotInvI_star
    (show GotInvI vcp XI ⟨0, 0, fun _ => 0, (w₀, 0)⟩ from gotInv_entry vcp (XI.at 0) _ w₀) hstar'
  obtain ⟨b1, k1, ρ1, w1, vb, i, ops, r, hs1, hvb, hi, hcall, hops, hsem⟩ :=
    vstar_call_at (j := j) hstar'' (Nat.zero_le _) (by simp only [vctr]; omega)
  have hM := regLevel_prefixPRSGE hc.check hc.alloc hc.emit hc.layout (XI := XI) (H := H)
    (K := K) (G := G) (gv := GotV vcp) (N := j) hcov he.abi he.stack he.gfree he.proph he.regp
    (fun n hn => by rw [he.hF]; exact he.calls n (by omega))
    (fun ht n hn => by rw [he.hF]; exact he.tries ht n (by omega)) he.pc
    (by rw [he.hF]; exact he.tls) (by rw [he.hF]; exact he.body) (fun _ => 0)
  rw [he.hF] at hM
  obtain ⟨info, hci⟩ := callLike_of_isCallI hcall
  obtain ⟨u, hon, -, hsite⟩ := hM b1 k1 ρ1 w1 vb i hs1 hvb hi ⟨info, hci⟩ ops hops
  obtain ⟨-, -, -, _, _, _, _, _, -, -, -, hpi, -⟩ := hsite
  exact ⟨u, hon, hpi.callPc⟩

/-- **`backend_prefix_cleanupPRI_atGE` for an ending run.** -/
theorem backend_prefix_cleanupPRI_atGE_ends {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledCleanup f k vc vcp rf af fa fb)
    (hone : InstCallsOne f) (htc : TryCallsOne f)
    {XI : ExtSemI} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hX : ∀ s n, ReachN env p cs s n →
      XCallsOk (env.only (Clif.Invoked env p s)) (f.externs.map (·.2))
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n) ∧
      XCallsIndOk (env.only (Clif.Invoked env p s)) (indSigs f)
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n))
    (hsym : ∀ n b, syms n = some b → XI.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : TrapsExplicit env p cs) {fuel : Nat} (hrun : RunEnds (Clif.runLoop env p fuel cs))
    {N : Nat} {H : ArmHooks}
    {G : BitVec 64 → Prop} {base ra : BitVec 64} {Kp : Nat} {cc : BitVec 64}
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {s : Arm.ArmState}
    (he : ActEntryPRN vcp rf af fa fb K F G XI H base ra Kp cc P R s w₀ N)
    {t : Clif.State} (hr : ReachN env p cs t N) (hcn : callNum t = 1) :
    ∀ j ≤ N, ∃ u, OnCallG (ArmStepX (XI.at 0) H fa) fa base s
        (fun t => (¬ PostCall fa base (Arm.r .PC t) ∨
          spOf t = spv s - BitVec.ofNat 64 (frameDrop af)) ∧ Arm.r .ERR t = .None ∧
          t.program = fb.program base) j u ∧
      CallPc fa base (Arm.r .PC u) := by
  intro j hj
  obtain ⟨b, k, ρ, w, hstar⟩ :=
    iselSim_prefixWI_next_cleanup_ends_stage hsub hc hone htc hX hsym hslot (fun _ => 0) hcs hrel
      hargs
      htr hrun t N hr hcn
  obtain ⟨b1, k1, ρ1, w1, vb, i, ops, r, hs1, hvb, hi, hcall, hops, hsem⟩ :=
    vstar_call_at (j := j) hstar (Nat.zero_le _) (by simp only [vctr]; omega)
  obtain ⟨info, hci⟩ := callLike_of_isCallI hcall
  have hkeep : pureForm i = false ∧ cmpForm i = false ∧ isJump i = false := by
    rcases hci with rfl | ⟨ti, rfl⟩ <;> exact ⟨rfl, rfl, rfl⟩
  obtain ⟨vb2, k2, a2, hs2, hvb2, hi2, hu2⟩ := prune_prefixW (sem := valueSemI F ⟨fa.k, af.slotBase⟩ XI)
    (fun _ _ _ _ _ _ hi hs => counted_pure (fun _ _ _ _ _ _ _ hp he => valueSem_pure hp he) hi hs)
    (cmpOverwrite_counted fun n => valueSem_cmpOverwrite _ _ _) hs1 hvb hi hops hkeep.1 hkeep.2.1
    hkeep.2.2
  have hds := DriverSemG.counted fun m =>
    (driverSem_valueSem F ⟨fa.k, af.slotBase⟩ (XI.at m)).toDriverSemG
  obtain ⟨b3, hs3, hins⟩ := prep_prefixW hds hc.prepOk hs2
  obtain ⟨vb3, i3, hvb3, hi3, hsame⟩ := hins vb2 i hvb2 hi2
  obtain ⟨hs4, -⟩ := gotInvI_star_value
    (show GotInvI vcp XI ⟨0, 0, fun _ => 0, (w₀, 0)⟩ from gotInv_entry vcp (XI.at 0) _ w₀) hs3
  have hci3 := sameInst_callLike hsame hci
  have hops3 : i3.operands = .ok ops := by rw [(sameInst_factsW hds hsame).1, hops]
  have hM := regLevel_value_prefixPRSGE hc.check hc.alloc hc.emit hc.layout (XI := XI) (H := H)
    (K := K) (G := G) (gv := GotV vcp) (N := j) hcov he.abi he.stack he.gfree he.proph he.regp
    (fun n hn => by rw [he.hF]; exact he.calls n (by omega))
    (fun ht n hn => by rw [he.hF]; exact he.tries ht n (by omega)) he.pc
    (by rw [he.hF]; exact he.tls) (by rw [he.hF]; exact he.body) (fun _ => 0)
  rw [he.hF] at hM
  obtain ⟨u, hon, -, hsite⟩ := hM b3 k2 a2 w1 vb3 i3 hs4 hvb3 hi3 ⟨info, hci3⟩ ops hops3
  obtain ⟨-, -, -, _, _, _, _, _, -, -, -, hpi, -⟩ := hsite
  exact ⟨u, hon, hpi.callPc⟩

/-- **`backend_prefixPRI_atEGE` for an ending run.** -/
theorem backend_prefixPRI_atEGE_ends {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledEither f k vc vcp rf af fa fb)
    (hone : InstCallsOne f) (htc : TryCallsOne f)
    {XI : ExtSemI} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hX : ∀ s n, ReachN env p cs s n →
      XCallsOk (env.only (Clif.Invoked env p s)) (f.externs.map (·.2))
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n) ∧
      XCallsIndOk (env.only (Clif.Invoked env p s)) (indSigs f)
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n))
    (hsym : ∀ n b, syms n = some b → XI.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : TrapsExplicit env p cs) {fuel : Nat} (hrun : RunEnds (Clif.runLoop env p fuel cs))
    {N : Nat} {H : ArmHooks}
    {G : BitVec 64 → Prop} {base ra : BitVec 64} {Kp : Nat} {cc : BitVec 64}
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {s : Arm.ArmState}
    (he : ActEntryPRN vcp rf af fa fb K F G XI H base ra Kp cc P R s w₀ N)
    {t : Clif.State} (hr : ReachN env p cs t N) (hcn : callNum t = 1) :
    ∀ j ≤ N, ∃ u, OnCallG (ArmStepX (XI.at 0) H fa) fa base s
        (fun t => (¬ PostCall fa base (Arm.r .PC t) ∨
          spOf t = spv s - BitVec.ofNat 64 (frameDrop af)) ∧ Arm.r .ERR t = .None ∧
          t.program = fb.program base) j u ∧
      CallPc fa base (Arm.r .PC u) := by
  cases hc with
  | legacy hc =>
    exact backend_prefixPRI_atSGE_ends hsub hc hone htc hcov hX hsym hslot hcs hrel hargs htr hrun
      he hr hcn
  | cleanup hc =>
    exact backend_prefix_cleanupPRI_atGE_ends hsub hc hone htc hcov hX hsym hslot hcs hrel hargs
      htr hrun he hr hcn

/-- **`prefix_relatedPRI_atEG` for an ending run** (module doc). -/
theorem prefix_relatedPRI_atEG_ends {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledEither f k vc vcp rf af fa fb)
    (hone : InstCallsOne f) (htc : TryCallsOne f)
    {XI : ExtSemI} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hnrc : NoRetCall env p cs)
    (hX : ∀ s n, ReachN env p cs s n →
      XCallsOk (env.only (Clif.Invoked env p s)) (f.externs.map (·.2))
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n) ∧
      XCallsIndOk (env.only (Clif.Invoked env p s)) (indSigs f)
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n))
    (hsym : ∀ n b, syms n = some b → XI.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : TrapsExplicit env p cs) {fuel : Nat} (hrun : RunEnds (Clif.runLoop env p fuel cs))
    {N : Nat} {H : ArmHooks}
    {G : BitVec 64 → Prop} {base ra : BitVec 64} {Kp : Nat} {cc : BitVec 64}
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {s : Arm.ArmState}
    (he : ActEntryPRN vcp rf af fa fb K F G XI H base ra Kp cc P R s w₀ N)
    {t : Clif.State} (hr : ReachN env p cs t N) (hcn : callNum t = 1) :
    ∀ j ≤ N, ∃ u i info uses w r, OnCallG (ArmStepX (XI.at 0) H fa) fa base s
        (fun t => (¬ PostCall fa base (Arm.r .PC t) ∨
          spOf t = spv s - BitVec.ofNat 64 (frameDrop af)) ∧ Arm.r .ERR t = .None ∧
          t.program = fb.program base) j u ∧
      spOf u = spv s - BitVec.ofNat 64 (frameDrop af) ∧ CallSiteAt F K G s fa base i uses w u ∧
      (i = .call info ∨ ∃ ti, i = .tryCall info ti) ∧ vcp.CallSite info ∧
      gotGuard (GotV vcp) (XI.at 0) info uses ∧
      (XI.at j).call (callDest info) uses w = some r ∧
      RelatedN env p cs (f.externs.map (·.2)) (indSigs f)
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) XI.sym j (callDest info) uses w := by
  intro j hj
  obtain ⟨u, i, info, uses, w, r, ⟨n₁, hn₁, hcb₁, -⟩, hsp, hsite, hci, hcs', hgd, hx, hq⟩ :=
    prefix_relatedPRI_atE_ends hsub hc hone htc hcov hnrc hX hsym hslot hcs hrel hargs htr hrun he
      hr hcn j hj
  obtain ⟨u', ⟨n₂, hn₂, hcb₂, htr₂⟩, hcp₂⟩ :=
    backend_prefixPRI_atEGE_ends hsub hc hone htc hcov hX hsym hslot hcs hrel hargs htr hrun he hr
      hcn j hj
  have hcp₁ : CallPc fa base (Arm.r .PC (runX (ArmStepX (XI.at 0) H fa) n₁ s)) := by
    obtain ⟨-, -, -, _, _, _, _, _, -, -, -, hpi, -⟩ := hsite
    rw [hn₁]; exact hpi.callPc
  have hcp₂' : CallPc fa base (Arm.r .PC (runX (ArmStepX (XI.at 0) H fa) n₂ s)) := by
    rw [hn₂]; exact hcp₂
  obtain rfl : n₁ = n₂ := callIdx_unique hcp₁ hcp₂' (hcb₁.trans hcb₂.symm)
  exact ⟨u, i, info, uses, w, r, ⟨n₁, hn₁, hcb₁, htr₂⟩, hsp, hsite, hci, hcs', hgd, hx, hq⟩

end E2E
