import FV.E2E.IselSimINT
import FV.E2E.IselSimISkip

/-!
# The counted CLIF → VCode simulation for the kept code, with the call counts (#552, SEM1)

`sim_runGNT` (`FV/E2E/IselSimINT.lean`) for `vcK`, the lowering with the unused statements
skipped (`SkipHyp`), as `sim_runGK` (`FV/E2E/IselSimISkip.lean`) is `sim_runG` for `vcK`:

* `stmt_stepG_noCall_trapNK`, `term_stepG_trapNK`: the traps of the kept code stay at the
  counter;
* **`sim_runGNTK`**;
* **`iselSim_relWI_cleanupNT_stage`**, **`iselSim_relWI_cleanupN_stage`**:
  `iselSim_relWI_cleanupNT` / `iselSim_relWI_cleanupN` for `skipStage f vc`.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

section
variable {f : Clif.Function} {vc vcK : VCode} {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
  {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId} {W : Type}
  {env : Clif.Env} {p : Clif.Program} {slots : List (Clif.SlotId × Nat)}
  {drop : Nat → Nat → Bool} {sem semB : Nat → ISem CV W} {MRW : MemRelTW W}

variable (hK : SkipHyp f vc R bl drop vcK)
include hK

/-- **The trap of a statement without an extern call of the kept code stays at the counter**
(`stmt_stepG_noCall_trapN`). -/
theorem stmt_stepG_noCall_trapNK (hB : ProbeOf semB sem) {n : Nat}
    (Hb : DriverHyp f vc ctx st0 R gn bl A (semB n) MRW (env.only fun _ _ _ => False) p)
    {s : Clif.State} {b k : Nat} {ρ : Nat → CV} {w : W}
    (hm : MatchK f ctx R gn bl A MRW slots (skipMask f R bl vc drop)
      (DeadDef vc (skipMask f R bl vc drop)) s ⟨b, k, ρ, w⟩)
    {stm : Clif.Stmt} {rest : List Clif.Stmt} (hbody : s.frame.body = stm :: rest)
    (hnc : stm.inst.isCallLike = false)
    (hind : ∀ sig callee args, stm.inst = .callIndirect sig callee args → ∀ cv,
      s.frame.get callee = .ok cv → ∀ g ∈ p.funcs, s.mem.symbols g.name ≠ some cv.toNat) :
    ∀ c, Clif.step env p s = .trapped c → explicitTrapInst stm.inst = true →
      VTrapFromW vcK (ISem.counted sem) ⟨b, k, ρ, (w, n)⟩ c (fun w => w.2 = n) := by
  have hstep : Clif.step (env.only fun _ _ _ => False) p s = Clif.step env p s :=
    step_none_of_callNum (by simp [callNum, hbody, hnc]) (fun _ _ h => by rw [hbody] at h; cases h)
  obtain ⟨-, S2⟩ := stmt_stepK hK Hb hm hbody hind
  exact fun c hs hexp => vTrapFromW_counted hB (S2 c (hstep.trans hs) hexp)

/-- **The trap of a terminator other than `try_call` of the kept code stays at the counter**
(`term_stepG_trapN`). -/
theorem term_stepG_trapNK (hB : ProbeOf semB sem) {n : Nat}
    (Hb : DriverHyp f vc ctx st0 R gn bl A (semB n) MRW (env.only fun _ _ _ => False) p)
    {s : Clif.State} {b k : Nat} {ρ : Nat → CV} {w : W}
    (hm : MatchK f ctx R gn bl A MRW slots (skipMask f R bl vc drop)
      (DeadDef vc (skipMask f R bl vc drop)) s ⟨b, k, ρ, w⟩) (hbody : s.frame.body = [])
    (hnt : s.frame.term.isTry = false) :
    ∀ c, Clif.step env p s = .trapped c →
      VTrapFromW vcK (ISem.counted sem) ⟨b, k, ρ, (w, n)⟩ c (fun w => w.2 = n) := by
  have hnr : ∀ fn args, s.frame.body = [] → s.frame.term ≠ .returnCall fn args := by
    intro fn args _ h
    obtain ⟨_, -, -, -, -, -, B, j, hB, hterm, -⟩ := hm
    exact Hb.noTail B (List.mem_of_getElem? hB) fn args (hterm.symm.trans h)
  have hstep : Clif.step (env.only fun _ _ _ => False) p s = Clif.step env p s :=
    step_none_of_callNum (by simp [callNum, hbody, hnt]) hnr
  obtain ⟨-, -, T3⟩ := term_step_abiK hK Hb hm hbody hnt
  exact fun c hs => vTrapFromW_counted hB (T3 c (hstep.trans hs))

/-- **Whole runs of the kept code, counted, with the call counts at the return and the trap**
(`sim_runGNT` for `vcK`). -/
theorem sim_runGNTK (hni : NoncallIndep sem) (hPr : ProbeOf semB sem) {cs : Clif.State}
    (hP : RunPrem env p f cs)
    (Hb : ∀ n, DriverHyp f vc ctx st0 R gn bl A (semB n) MRW (env.only fun _ _ _ => False) p)
    (Hs : ∀ s n, ReachN env p cs s n → DriverHyp f vc ctx st0 R gn bl A (sem n) MRW
      (env.only (Clif.Invoked env p s)) p)
    (hseg : ∀ b B j stm, f.blocks[b]? = some B → B.body[j]? = some stm →
      stm.inst.isCallLike = true → callsI (seg f R bl b j) = 1)
    (htc : TryCallsOne f) :
    ∀ fuel s n b k ρ w, ReachN env p cs s n →
      MatchK f ctx R gn bl A MRW slots (skipMask f R bl vc drop)
        (DeadDef vc (skipMask f R bl vc drop)) s ⟨b, k, ρ, w⟩ →
        RunOkAbiNT env p cs vcK (ISem.counted sem) (fun sl cm w => MRW sl cm w.1) slots
          (fun _ => True) ⟨b, k, ρ, (w, n)⟩ (Clif.runLoop env p fuel s) := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | _ fuel ih =>
  intro s n b k ρ w hr hm
  cases fuel with
  | zero => trivial
  | succ m =>
    rw [Clif.runLoop_succ]
    obtain ⟨vsF, -, hMF⟩ := id hm
    have hfunc : s.frame.func = f := hMF.2.1
    cases hbody : s.frame.body with
    | nil =>
      cases hty : s.frame.term.isTry with
      | false =>
        obtain ⟨T1, T2, -⟩ := term_stepGK hK hPr (Hb n) hm hbody hty
        have hc0 : callNum s = 0 := by simp [callNum, hbody, hty]
        cases hs : Clif.step env p s with
        | next s' =>
          obtain ⟨b', k', ρ', w', hstar, hm'⟩ := T1 s' hs
          have h := ih m (by omega) s' (n + callNum s) b' k' ρ' w' (hr.snoc hs) hm'
          rw [hc0, Nat.add_zero] at h
          exact RunOkAbiNT.prefix hstar h
        | done vals cm =>
          obtain ⟨us, outs, w', sv, hret, h1, h2, hsv, h3, h4, h5⟩ := T2 vals cm hs
          exact ⟨us, outs, (w', n), s.mem, sv, hret, h1, h2, trivial, h3, h4, h5, s, hr, hs⟩
        | trapped c => exact ⟨n, term_stepG_trapNK hK hPr (Hb n) hm hbody hty c hs, s, hr, hs⟩
        | stuck => trivial
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
        obtain ⟨Tnd, Tnx⟩ := term_step_tryGK hK hni (Hs s n hr) htc hm hbody hT hind
        have hst : Clif.step (env.only (Clif.Invoked env p s)) p s = Clif.step env p s :=
          Clif.step_only fun _ _ _ h => h
        have hc1 : callNum s = 1 := by simp [callNum, hbody, hty]
        cases hs : Clif.step env p s with
        | next s' =>
          obtain ⟨⟨hb', bc, ht'⟩, N1, N2, N3⟩ := Tnx s' (hst.trans hs)
          have hst' : Clif.step (env.only (Clif.Invoked env p s)) p s' = Clif.step env p s' := by
            apply Clif.step_only
            intro _ _ _ ⟨_, hI⟩
            simp [hb', ht'] at hI
          have hc0 : callNum s' = 0 := by simp [callNum, hb', ht', Clif.Terminator.isTry]
          cases m with
          | zero => trivial
          | succ m' =>
            show RunOkAbiNT env p cs vcK (ISem.counted sem) (fun sl cm w => MRW sl cm w.1) slots
              (fun _ => True) _ (Clif.runLoop env p (m' + 1) s')
            rw [Clif.runLoop_succ]
            cases hs' : Clif.step env p s' with
            | next s'' =>
              obtain ⟨b', k', ρ', w', hstar, hm'⟩ := N3 s'' (hst'.trans hs')
              have h := ih m' (by omega) s'' (n + callNum s + callNum s') b' k' ρ' w'
                ((hr.snoc hs).snoc hs') hm'
              rw [hc1, hc0, Nat.add_zero] at h
              exact RunOkAbiNT.prefix hstar h
            | done vals cm => exact absurd (hst'.trans hs') (N2 vals cm)
            | trapped c => exact absurd (hst'.trans hs') (N1 c)
            | stuck => trivial
        | done vals cm => exact absurd (hst.trans hs) (Tnd vals cm)
        | trapped c =>
          rcases hT with ⟨fn, args, hT⟩ | ⟨callee, args, hT⟩
          · exact absurd (hterm.symm.trans hT)
              (hP.tryCall s c fn args et hr.reach hs hbody hT B hBmem)
          · exact absurd (hterm.symm.trans hT)
              (hP.tryCallInd s c callee args et hr.reach hs hbody hT B hBmem)
        | stuck => trivial
    | cons st rest =>
      obtain ⟨-, -, -, -, B, j, hB, -, -, hbd, -⟩ := id hMF
      have hst : st ∈ B.body := by
        rw [hbd] at hbody
        exact List.mem_of_mem_drop (hbody ▸ List.mem_cons_self)
      have hBmem : B ∈ f.blocks := List.mem_of_getElem? hB
      have hext : ∀ fn args, st.inst = .call fn args → ∀ e, s.frame.func.extern? fn = some e →
          p.func? e.name = none := by
        intro fn args hi e he
        exact (Hb n).ext B hBmem st hst fn args hi e (hfunc ▸ he)
      have hind : ∀ sig callee args, st.inst = .callIndirect sig callee args → ∀ cv,
          s.frame.get callee = .ok cv → ∀ g ∈ p.funcs, s.mem.symbols g.name ≠ some cv.toNat :=
        fun sig callee args hi => hP.indirect s st rest sig callee args hr.reach hbody hi
          ⟨B, hBmem, hst⟩
      cases hcl : st.inst.isCallLike with
      | false =>
        obtain ⟨S1, -⟩ := stmt_stepG_noCallK hK hPr (Hb n) hm hbody hcl hind
        have hc0 : callNum s = 0 := by simp [callNum, hbody, hcl]
        cases hs : Clif.step env p s with
        | next s' =>
          obtain ⟨b', k', ρ', w', hstar, hm'⟩ := S1 s' hs
          have h := ih m (by omega) s' (n + callNum s) b' k' ρ' w' (hr.snoc hs) hm'
          rw [hc0, Nat.add_zero] at h
          exact RunOkAbiNT.prefix hstar h
        | done vals cm => exact absurd hs (stmt_not_done hbody hext hind)
        | trapped c =>
          exact ⟨n, stmt_stepG_noCall_trapNK hK hPr (Hb n) hm hbody hcl hind c hs
            (hP.stmt s c st rest hr.reach hs hbody), s, hr, hs⟩
        | stuck => trivial
      | true =>
        obtain ⟨S1, -⟩ := stmt_stepG_callK hK hni (Hs s n hr) hseg hm hbody hcl hind
        have hc1 : callNum s = 1 := by simp [callNum, hbody, hcl]
        cases hs : Clif.step env p s with
        | next s' =>
          obtain ⟨b', k', ρ', w', hstar, hm'⟩ := S1 s' hs
          have h := ih m (by omega) s' (n + callNum s) b' k' ρ' w' (hr.snoc hs) hm'
          rw [hc1] at h
          exact RunOkAbiNT.prefix hstar h
        | done vals cm => exact absurd hs (stmt_not_done hbody hext hind)
        | trapped c =>
          have hd := hP.stmt s c st rest hr.reach hs hbody
          rw [not_explicitTrap_of_callLike hcl] at hd
          cases hd
        | stuck => trivial

end

/-- **`iselSim_relWI_cleanupNT` and `iselSim_relWI_cleanupN` together for the code after the skip
of unused instructions** (`skipStage f vc`): the counted run with the call counts at the return
and at the trap. -/
theorem iselSim_relWI_cleanupNT_stage_both {p : Clif.Program} {f : Clif.Function} {k : Nat}
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
    (hargs : ArgsAtEntry F f.sig args w₀) (htr : TrapsExplicit env p cs) (fuel : Nat) :
    RunOkAbiNT env p cs (skipStage f vc) (valueSemI F ⟨fa.k, af.slotBase⟩ XI)
      (fun sl cm w => RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c sl cm w.1)
      cs.frame.slots (fun _ => True) ⟨0, 0, ρ₀, (w₀, 0)⟩ (Clif.runLoop env p fuel cs) := by
  obtain ⟨ctx, st0, R, gn, bl, A, hshape, hcert, hbr, hsk⟩ := skipStage_spec hc.lowerOk
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
  rcases hsk with heq | hK
  · rw [heq]
    exact RunOkAbiNT.prefix
      (vstar_mapW (counted_probe_proj hPr 0) hstar.star)
      (sim_runGNT (noncallIndep_valueSem F ⟨fa.k, af.slotBase⟩ XI) hPr hP Hb Hs hseg htc fuel cs
        0 0 k0 ρ₁ w₁ .refl hm)
  obtain ⟨⟨b1, k1, ρ1, w1⟩, hsK, hmK⟩ := entry_matchK hK hB0 hbody hstar hm
  exact RunOkAbiNT.prefix
    (vstar_mapW (counted_probe_proj hPr 0) hsK)
    (sim_runGNTK hK (noncallIndep_valueSem F ⟨fa.k, af.slotBase⟩ XI) hPr hP Hb Hs hseg htc fuel
      cs 0 b1 k1 ρ1 w1 .refl hmK)

/-- **`iselSim_relWI_cleanupNT` for the code after the skip of unused instructions**
(`skipStage f vc`). -/
theorem iselSim_relWI_cleanupNT_stage {p : Clif.Program} {f : Clif.Function} {k : Nat}
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
    (hargs : ArgsAtEntry F f.sig args w₀) (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ∀ c', Clif.runLoop env p fuel cs = .trapped c' →
      ∃ nc, VTrapFromW (skipStage f vc) (valueSemI F ⟨fa.k, af.slotBase⟩ XI) ⟨0, 0, ρ₀, (w₀, 0)⟩ c'
        (fun w => w.2 = nc) ∧ ∃ u, ReachN env p cs u nc ∧ Clif.step env p u = .trapped c' := by
  have hrun := iselSim_relWI_cleanupNT_stage_both hsub hc hone htc hX hsym hslot ρ₀ hce hrel hargs
    htr fuel
  intro c' h
  rw [h] at hrun
  exact hrun

/-- **`iselSim_relWI_cleanupN` for the code after the skip of unused instructions**
(`skipStage f vc`). -/
theorem iselSim_relWI_cleanupN_stage {p : Clif.Program} {f : Clif.Function} {k : Nat}
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
    (hargs : ArgsAtEntry F f.sig args w₀) (htr : TrapsExplicit env p cs) (fuel : Nat) :
    (∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ us outs w, VRetFrom (skipStage f vc) (valueSemI F ⟨fa.k, af.slotBase⟩ XI)
          ⟨0, 0, ρ₀, (w₀, 0)⟩ us outs w ∧
        us.map (·.2) = (List.range us.length).map Reg.x ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w.1 ∧
        ∃ u, ReachN env p cs u w.2 ∧ Clif.step env p u = .done vals cm) ∧
    (∀ c', Clif.runLoop env p fuel cs = .trapped c' →
      VTrapFrom (skipStage f vc) (valueSemI F ⟨fa.k, af.slotBase⟩ XI) ⟨0, 0, ρ₀, (w₀, 0)⟩ c') := by
  have hrun := iselSim_relWI_cleanupNT_stage_both hsub hc hone htc hX hsym hslot ρ₀ hce hrel hargs
    htr fuel
  refine ⟨fun vals cm h => ?_, fun c' h => ?_⟩
  · rw [h] at hrun
    obtain ⟨us, outs, w, cm0, sv, hret, h1, h2, -, h3, h4, h5, u, hu, hd⟩ := hrun
    exact ⟨us, outs, w, hret, h1, h2, AllHold.prefix_append h3,
      h5 ▸ memRel_leave (memRel_free h4.1.1 _), u, hu, hd⟩
  · rw [h] at hrun
    obtain ⟨nc, ht, -⟩ := hrun
    exact ht.toVTrapFrom

end E2E
