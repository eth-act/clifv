import FV.E2E.IselSimIPrefixCleanup
import FV.E2E.IselSimISkip

/-!
# The counted prefix simulation for the kept code (#552, SEM1 item (d))

`sim_prefixG` / `sim_prefix_call` (`FV/E2E/IselSimIPrefix.lean`) for `vcK`, the lowering with the
unused statements skipped (`SkipHyp`), with the kept-code steps of `FV/E2E/IselSimISkip.lean`, and
**`iselSim_prefixWI_cleanup_stage`**: `iselSim_prefixWI_cleanup` for `skipStage f vc`.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

section
variable {f : Clif.Function} {vc vcK : VCode} {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
  {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId} {W : Type}
  {env : Clif.Env} {p : Clif.Program} {slots : List (Clif.SlotId × Nat)}
  {drop : Nat → Nat → Bool} {sem semB : Nat → ISem CV W} {MRW : MemRelTW W}

/-- The kept code's state reached with counter `n` corresponds to one of `vc` matching `t`. -/
def PrefixAtK (f : Clif.Function) (vc vcK : VCode) (ctx : Ctx) (R : Reg → Reg) (gn : Nat → Nat)
    (bl : List BLow) (A : Nat → Nat → List Clif.ValueId) (drop : Nat → Nat → Bool)
    (sem : Nat → ISem CV W) (MRW : MemRelTW W) (slots : List (Clif.SlotId × Nat))
    (v0 : VState CV (W × Nat)) (t : Clif.State) (n : Nat) : Prop :=
  ∃ b k ρ w, Star (VStep vcK (ISem.counted sem)) (.run v0) (.run ⟨b, k, ρ, (w, n)⟩) ∧
    MatchK f ctx R gn bl A MRW slots (skipMask f R bl vc drop)
      (DeadDef vc (skipMask f R bl vc drop)) t ⟨b, k, ρ, w⟩

variable (hK : SkipHyp f vc R bl drop vcK)
include hK

/-- **Run prefixes of the kept code, counted, for a family** (`sim_prefixG` for `vcK`). -/
theorem sim_prefixGK (hni : NoncallIndep sem) (hPr : ProbeOf semB sem) {cs : Clif.State}
    (hP : RunPrem env p f cs)
    (Hb : ∀ n, DriverHyp f vc ctx st0 R gn bl A (semB n) MRW (env.only fun _ _ _ => False) p)
    (Hs : ∀ s n, ReachN env p cs s n → DriverHyp f vc ctx st0 R gn bl A (sem n) MRW
      (env.only (Clif.Invoked env p s)) p)
    (hseg : ∀ b B j stm, f.blocks[b]? = some B → B.body[j]? = some stm →
      stm.inst.isCallLike = true → callsI (seg f R bl b j) = 1)
    (htc : TryCallsOne f) {b0 k0 : Nat} {ρ0 : Nat → CV} {w0 : W}
    (hm0 : MatchK f ctx R gn bl A MRW slots (skipMask f R bl vc drop)
      (DeadDef vc (skipMask f R bl vc drop)) cs ⟨b0, k0, ρ0, w0⟩) :
    ∀ t n, ReachN env p cs t n →
      PrefixAtK f vc vcK ctx R gn bl A drop sem MRW slots ⟨b0, k0, ρ0, (w0, 0)⟩ t n ∨
      ((t.frame.body = [] ∧ ∃ bc, t.frame.term = .jump bc) ∧
        ∃ t0 n0, ReachN env p cs t0 n0 ∧ n = n0 + 1 ∧ t0.frame.body = [] ∧
          t0.frame.term.isTry = true ∧ Clif.step env p t0 = .next t ∧
          PrefixAtK f vc vcK ctx R gn bl A drop sem MRW slots ⟨b0, k0, ρ0, (w0, 0)⟩ t0 n0) := by
  intro t n hr
  induction hr with
  | refl => exact .inl ⟨b0, k0, ρ0, w0, .refl _, hm0⟩
  | @snoc s s' n hr hs ih =>
    rcases ih with ⟨b, k, ρ, w, hstar, hm⟩ | ⟨⟨hb, bc, hj⟩, t0, n0, hr0, rfl, hb0, ht0, hs0,
        b, k, ρ, w, hstar, hm⟩
    · -- `s` is matched
      obtain ⟨vsF, -, hMF⟩ := id hm
      cases hbody : s.frame.body with
      | nil =>
        cases hty : s.frame.term.isTry with
        | false =>
          obtain ⟨T1, -, -⟩ := term_stepGK hK hPr (Hb n) hm hbody hty
          obtain ⟨b', k', ρ', w', hst, hm'⟩ := T1 s' hs
          have hc0 : callNum s = 0 := by simp [callNum, hbody, hty]
          rw [hc0, Nat.add_zero]
          exact .inl ⟨b', k', ρ', w', hstar.trans hst, hm'⟩
        | true =>
          obtain ⟨B, j, hB, hterm, -⟩ := hMF.2.2.2.2
          have hBmem : B ∈ f.blocks := List.mem_of_getElem? hB
          obtain ⟨et, hT⟩ : ∃ et, IsTryWith s.frame.term et := by
            cases ht : s.frame.term with
            | tryCall fn args et => exact ⟨et, .inl ⟨fn, args, rfl⟩⟩
            | tryCallIndirect c args et => exact ⟨et, .inr ⟨c, args, rfl⟩⟩
            | _ => rw [ht] at hty; cases hty
          have hind : ∀ callee args, s.frame.term = .tryCallIndirect callee args et → ∀ cv,
              s.frame.get callee = .ok cv → ∀ g ∈ p.funcs, s.mem.symbols g.name ≠ some cv.toNat :=
            fun callee args ht => hP.tryIndirect s callee args et hr.reach hbody ht
              ⟨B, hBmem, hterm.symm.trans ht⟩
          obtain ⟨-, Tnx⟩ := term_step_tryGK hK hni (Hs s n hr) htc hm hbody hT hind
          have hst : Clif.step (env.only (Clif.Invoked env p s)) p s = Clif.step env p s :=
            Clif.step_only fun _ _ _ h => h
          obtain ⟨hmid, -⟩ := Tnx s' (hst.trans hs)
          have hc1 : callNum s = 1 := by simp [callNum, hbody, hty]
          rw [hc1]
          exact .inr ⟨hmid, s, n, hr, rfl, hbody, hty, hs, b, k, ρ, w, hstar, hm⟩
      | cons st rest =>
        obtain ⟨-, -, -, -, B, j, hB, -, -, hbd, -⟩ := id hMF
        have hst : st ∈ B.body := by
          rw [hbd] at hbody
          exact List.mem_of_mem_drop (hbody ▸ List.mem_cons_self)
        have hBmem : B ∈ f.blocks := List.mem_of_getElem? hB
        have hind : ∀ sig callee args, st.inst = .callIndirect sig callee args → ∀ cv,
            s.frame.get callee = .ok cv → ∀ g ∈ p.funcs, s.mem.symbols g.name ≠ some cv.toNat :=
          fun sig callee args hi => hP.indirect s st rest sig callee args hr.reach hbody hi
            ⟨B, hBmem, hst⟩
        cases hcl : st.inst.isCallLike with
        | false =>
          obtain ⟨S1, -⟩ := stmt_stepG_noCallK hK hPr (Hb n) hm hbody hcl hind
          obtain ⟨b', k', ρ', w', hst', hm'⟩ := S1 s' hs
          have hc0 : callNum s = 0 := by simp [callNum, hbody, hcl]
          rw [hc0, Nat.add_zero]
          exact .inl ⟨b', k', ρ', w', hstar.trans hst', hm'⟩
        | true =>
          obtain ⟨S1, -⟩ := stmt_stepG_callK hK hni (Hs s n hr) hseg hm hbody hcl hind
          obtain ⟨b', k', ρ', w', hst', hm'⟩ := S1 s' hs
          have hc1 : callNum s = 1 := by simp [callNum, hbody, hcl]
          rw [hc1]
          exact .inl ⟨b', k', ρ', w', hstar.trans hst', hm'⟩
    · -- `s` is the pending `jump` of the `try_call` state `t0`
      obtain ⟨vsF, -, hMF⟩ := id hm
      obtain ⟨B, j, hB, hterm, -⟩ := hMF.2.2.2.2
      have hBmem : B ∈ f.blocks := List.mem_of_getElem? hB
      obtain ⟨et, hT⟩ : ∃ et, IsTryWith t0.frame.term et := by
        cases ht : t0.frame.term with
        | tryCall fn args et => exact ⟨et, .inl ⟨fn, args, rfl⟩⟩
        | tryCallIndirect c args et => exact ⟨et, .inr ⟨c, args, rfl⟩⟩
        | _ => rw [ht] at ht0; cases ht0
      have hind : ∀ callee args, t0.frame.term = .tryCallIndirect callee args et → ∀ cv,
          t0.frame.get callee = .ok cv → ∀ g ∈ p.funcs, t0.mem.symbols g.name ≠ some cv.toNat :=
        fun callee args ht => hP.tryIndirect t0 callee args et hr0.reach hb0 ht
          ⟨B, hBmem, hterm.symm.trans ht⟩
      obtain ⟨-, Tnx⟩ := term_step_tryGK hK hni (Hs t0 n0 hr0) htc hm hb0 hT hind
      have hst : Clif.step (env.only (Clif.Invoked env p t0)) p t0 = Clif.step env p t0 :=
        Clif.step_only fun _ _ _ h => h
      obtain ⟨-, -, -, N3⟩ := Tnx s (hst.trans hs0)
      have hst' : Clif.step (env.only (Clif.Invoked env p t0)) p s = Clif.step env p s := by
        apply Clif.step_only
        intro _ _ _ ⟨_, hI⟩
        simp [hb, hj] at hI
      obtain ⟨b', k', ρ', w', hst2, hm'⟩ := N3 s' (hst'.trans hs)
      have hc0 : callNum s = 0 := by simp [callNum, hb, hj, Clif.Terminator.isTry]
      rw [hc0, Nat.add_zero]
      exact .inl ⟨b', k', ρ', w', hstar.trans hst2, hm'⟩

/-- **Calling states are matched in the kept code** (`sim_prefix_call` for `vcK`). -/
theorem sim_prefix_callK (hni : NoncallIndep sem) (hPr : ProbeOf semB sem) {cs : Clif.State}
    (hP : RunPrem env p f cs)
    (Hb : ∀ n, DriverHyp f vc ctx st0 R gn bl A (semB n) MRW (env.only fun _ _ _ => False) p)
    (Hs : ∀ s n, ReachN env p cs s n → DriverHyp f vc ctx st0 R gn bl A (sem n) MRW
      (env.only (Clif.Invoked env p s)) p)
    (hseg : ∀ b B j stm, f.blocks[b]? = some B → B.body[j]? = some stm →
      stm.inst.isCallLike = true → callsI (seg f R bl b j) = 1)
    (htc : TryCallsOne f) {b0 k0 : Nat} {ρ0 : Nat → CV} {w0 : W}
    (hm0 : MatchK f ctx R gn bl A MRW slots (skipMask f R bl vc drop)
      (DeadDef vc (skipMask f R bl vc drop)) cs ⟨b0, k0, ρ0, w0⟩) {t : Clif.State} {n : Nat}
    (hr : ReachN env p cs t n) (hc : callNum t = 1) :
    PrefixAtK f vc vcK ctx R gn bl A drop sem MRW slots ⟨b0, k0, ρ0, (w0, 0)⟩ t n := by
  rcases sim_prefixGK hK hni hPr hP Hb Hs hseg htc hm0 t n hr with h | ⟨⟨hb, bc, hj⟩, -⟩
  · exact h
  · simp [callNum, hb, hj, Clif.Terminator.isTry] at hc

end

/-- **`iselSim_prefixWI_cleanup` for the code after the skip of unused instructions**
(`skipStage f vc`, which the cleanup stage prunes and prepares). -/
theorem iselSim_prefixWI_cleanup_stage {p : Clif.Program} {f : Clif.Function} {k : Nat}
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
    (hargs : ArgsAtEntry F f.sig args w₀) (htr : TrapsExplicit env p cs) :
    ∀ t n, ReachN env p cs t n → callNum t = 1 →
      ∃ b k ρ w, Star (VStep (skipStage f vc) (valueSemI F ⟨fa.k, af.slotBase⟩ XI))
        (.run ⟨0, 0, ρ₀, (w₀, 0)⟩) (.run ⟨b, k, ρ, (w, n)⟩) ∧
        RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c t.frame.slots t.mem w := by
  intro t n hr hcn
  obtain ⟨ctx, st0, R, gn, bl, A, hshape, hcert, hbr, hsk⟩ := skipStage_spec hc.lowerOk
  rcases hsk with heq | hK
  · rw [heq]
    exact iselSim_prefixWI_cleanup hsub hc hone htc hX hsym hslot ρ₀ hce hrel hargs htr t n hr hcn
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
  obtain ⟨b, k', ρ, w, hst, vsF, hC, hmt⟩ :=
    sim_prefix_callK hK (noncallIndep_valueSem F ⟨fa.k, af.slotBase⟩ XI) hPr hP Hb Hs hseg htc hmK
      hr hcn
  obtain ⟨-, -, hw, -⟩ := hC
  simp only at hw
  refine ⟨b, k', ρ, w, (vstar_mapW (counted_probe_proj hPr 0) hsK).trans hst, ?_⟩
  rw [hmt.2.2.1, hw]
  exact hmt.2.2.2.1

end E2E
