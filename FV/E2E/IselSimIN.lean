import FV.E2E.IselSimICleanup

/-!
# CLIF → counted VCode with the call count at the return (SEM1 #537, #680 (3), `CountPRB` (b))

`sim_runG`/`RunOkAbi` do not say which counter the VCode return has. Here the counter of the
VCode return is the CLIF run's call count up to its returning state:

* `RunOkAbiN`: `RunOkAbi` whose return also has a state `u` of the CLIF run from `cs` reached
  after `w.2` calls (`ReachN`) whose step returns; `RunOkAbiN.prefix`, `RunOkAbiN.runOkAbi`;
* `sim_runGN`: `sim_runG` (same proof) concluding `RunOkAbiN`;
* **`iselSim_relWIN`**, **`iselSim_relWI_cleanupN`**: `iselSim_relWI`/`_cleanup` with
  `∃ u, ReachN env p cs u w.2 ∧ Clif.step env p u = .done vals cm` at the return.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

section
variable {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
  {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId}
  {env : Clif.Env} {p : Clif.Program} {slots : List (Clif.SlotId × Nat)} {W : Type}
  {sem semB : Nat → ISem CV W} {MRW : MemRelTW W}

/-- **`RunOkAbi` with the CLIF call count at the return**: the VCode return's counter `w.2` is the
call count of a state `u` of the CLIF run from `cs` whose step returns. -/
def RunOkAbiN {W : Type} (env : Clif.Env) (p : Clif.Program) (cs : Clif.State) (vc : VCode)
    (sem : ISem CV (W × Nat)) (MR : MemRelTW (W × Nat)) (slots : List (Clif.SlotId × Nat))
    (Q : List Clif.Val → Prop) (vs : VState CV (W × Nat)) : Clif.Outcome → Prop
  | .returned vals cm => ∃ us outs w cm0 sv, VRetFrom vc sem vs us outs w ∧
      RetPins vals us ∧ us.length = outs.length ∧
      Q sv ∧ AllHold (vals ++ sv) outs ∧ MR slots cm0 w ∧ cm = (cm0.free (slots.map (·.2))).leave ∧
      ∃ u, ReachN env p cs u w.2 ∧ Clif.step env p u = .done vals cm
  | o => RunOkAbi vc sem MR slots Q vs o

theorem RunOkAbiN.prefix {W : Type} {cs : Clif.State} {sem : ISem CV (W × Nat)}
    {MR : MemRelTW (W × Nat)} {Q : List Clif.Val → Prop} {vs vs' : VState CV (W × Nat)}
    {o : Clif.Outcome} (h : Star (VStep vc sem) (.run vs) (.run vs'))
    (h' : RunOkAbiN env p cs vc sem MR slots Q vs' o) : RunOkAbiN env p cs vc sem MR slots Q vs o := by
  cases o with
  | returned vals cm =>
    obtain ⟨us, outs, w, cm0, sv, hr, h1⟩ := h'
    exact ⟨us, outs, w, cm0, sv, VRetFrom.prefix h hr, h1⟩
  | trapped c => exact VTrapFrom.prefix h h'
  | _ => trivial

theorem RunOkAbiN.runOkAbi {W : Type} {cs : Clif.State} {sem : ISem CV (W × Nat)}
    {MR : MemRelTW (W × Nat)} {Q : List Clif.Val → Prop} {vs : VState CV (W × Nat)}
    {o : Clif.Outcome} (h : RunOkAbiN env p cs vc sem MR slots Q vs o) :
    RunOkAbi vc sem MR slots Q vs o := by
  cases o with
  | returned vals cm =>
    obtain ⟨us, outs, w, cm0, sv, hr, h1, h2, h3, h4, h5, h6, -⟩ := h
    exact ⟨us, outs, w, cm0, sv, hr, h1, h2, h3, h4, h5, h6⟩
  | _ => exact h

/-- **`sim_runG` with the CLIF call count at the return** (`RunOkAbiN`). Original doc: **Whole runs, counted, for a family**: from matching states at CLIF call count `n`, every
CLIF outcome is realised by the counted VCode run from counter `n` (call number `n` with
`sem n`): the steps without extern call by the probe `semB n` (`Hb`), the calling ones with the
environment restricted to their invocation (`Hs`). -/
theorem sim_runGN (hni : NoncallIndep sem) (hPr : ProbeOf semB sem) {cs : Clif.State}
    (hP : RunPrem env p f cs)
    (Hb : ∀ n, DriverHyp f vc ctx st0 R gn bl A (semB n) MRW (env.only fun _ _ _ => False) p)
    (Hs : ∀ s n, ReachN env p cs s n → DriverHyp f vc ctx st0 R gn bl A (sem n) MRW
      (env.only (Clif.Invoked env p s)) p)
    (hseg : ∀ b B j stm, f.blocks[b]? = some B → B.body[j]? = some stm →
      stm.inst.isCallLike = true → callsI (seg f R bl b j) = 1)
    (htc : TryCallsOne f) :
    ∀ fuel s n b k ρ w, ReachN env p cs s n →
      Match f ctx R gn bl A MRW slots s ⟨b, k, ρ, w⟩ →
        RunOkAbiN env p cs vc (ISem.counted sem) (fun sl cm w => MRW sl cm w.1) slots (fun _ => True)
          ⟨b, k, ρ, (w, n)⟩
          (Clif.runLoop env p fuel s) := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | _ fuel ih =>
  intro s n b k ρ w hr hm
  cases fuel with
  | zero => trivial
  | succ m =>
    rw [Clif.runLoop_succ]
    have hfunc : s.frame.func = f := hm.2.1
    cases hbody : s.frame.body with
    | nil =>
      cases hty : s.frame.term.isTry with
      | false =>
        obtain ⟨T1, T2, T3⟩ := term_stepG hPr (Hb n) hm hbody hty
        have hc0 : callNum s = 0 := by simp [callNum, hbody, hty]
        cases hs : Clif.step env p s with
        | next s' =>
          obtain ⟨b', k', ρ', w', hstar, hm'⟩ := T1 s' hs
          have h := ih m (by omega) s' (n + callNum s) b' k' ρ' w' (hr.snoc hs) hm'
          rw [hc0, Nat.add_zero] at h
          exact RunOkAbiN.prefix hstar h
        | done vals cm =>
          obtain ⟨us, outs, w', sv, hret, h1, h2, hsv, h3, h4, h5⟩ := T2 vals cm hs
          exact ⟨us, outs, (w', n), s.mem, sv, hret, h1, h2, trivial, h3, h4, h5, s, hr, hs⟩
        | trapped c => exact T3 c hs
        | stuck => trivial
      | true =>
        obtain ⟨B, j, hB, hterm, -⟩ := hm.2.2.2.2
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
        obtain ⟨Tnd, Tnx⟩ := term_step_tryG hni (Hs s n hr) htc hm hbody hT hind
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
            show RunOkAbiN env p cs vc (ISem.counted sem) (fun sl cm w => MRW sl cm w.1) slots (fun _ => True) _
              (Clif.runLoop env p (m' + 1) s')
            rw [Clif.runLoop_succ]
            cases hs' : Clif.step env p s' with
            | next s'' =>
              obtain ⟨b', k', ρ', w', hstar, hm'⟩ := N3 s'' (hst'.trans hs')
              have h := ih m' (by omega) s'' (n + callNum s + callNum s') b' k' ρ' w'
                ((hr.snoc hs).snoc hs') hm'
              rw [hc1, hc0, Nat.add_zero] at h
              exact RunOkAbiN.prefix hstar h
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
      obtain ⟨-, -, -, -, B, j, hB, -, -, hbd, -⟩ := id hm
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
        obtain ⟨S1, S2⟩ := stmt_stepG_noCall hPr (Hb n) hm hbody hcl hind
        have hc0 : callNum s = 0 := by simp [callNum, hbody, hcl]
        cases hs : Clif.step env p s with
        | next s' =>
          obtain ⟨b', k', ρ', w', hstar, hm'⟩ := S1 s' hs
          have h := ih m (by omega) s' (n + callNum s) b' k' ρ' w' (hr.snoc hs) hm'
          rw [hc0, Nat.add_zero] at h
          exact RunOkAbiN.prefix hstar h
        | done vals cm => exact absurd hs (stmt_not_done hbody hext hind)
        | trapped c => exact S2 c hs (hP.stmt s c st rest hr.reach hs hbody)
        | stuck => trivial
      | true =>
        obtain ⟨S1, S2⟩ := stmt_stepG_call hni (Hs s n hr) hseg hm hbody hcl hind
        have hc1 : callNum s = 1 := by simp [callNum, hbody, hcl]
        cases hs : Clif.step env p s with
        | next s' =>
          obtain ⟨b', k', ρ', w', hstar, hm'⟩ := S1 s' hs
          have h := ih m (by omega) s' (n + callNum s) b' k' ρ' w' (hr.snoc hs) hm'
          rw [hc1] at h
          exact RunOkAbiN.prefix hstar h
        | done vals cm => exact absurd hs (stmt_not_done hbody hext hind)
        | trapped c => exact S2 c hs (hP.stmt s c st rest hr.reach hs hbody)
        | stuck => trivial


end

/-- **`iselSim_relWI` with the CLIF call count at the return**: the VCode return's counter `w.2`
is the call count of the CLIF run up to its returning state. Original doc: **CLIF → counted VCode for the backend's `csem`** (`iselSim_relW` for the counted run
`csemI F ctx XI` from counter `0`), with the callee contract of call number `n` needed only at
the states of the CLIF run reached after `n` extern calls, for the environment restricted to
that state's invocation; under the ISLE call-count properties `InstCallsOne`, `TryCallsOne`. -/
theorem iselSim_relWIN {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
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
    (hargs : ArgsAtEntry F f.sig args w₀) (htr : TrapsExplicit env p cs) (fuel : Nat) :
    (∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ us outs w, VRetFrom vc (csemI F ⟨fa.k, af.slotBase⟩ XI) ⟨0, 0, ρ₀, (w₀, 0)⟩ us outs w ∧
        RetPins vals us ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w.1 ∧
        ∃ u, ReachN env p cs u w.2 ∧ Clif.step env p u = .done vals cm) ∧
    (∀ c', Clif.runLoop env p fuel cs = .trapped c' →
      VTrapFrom vc (csemI F ⟨fa.k, af.slotBase⟩ XI) ⟨0, 0, ρ₀, (w₀, 0)⟩ c') := by
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
  have hrun := RunOkAbiN.prefix
    (vstar_mapW (csem_noCall_proj F ⟨fa.k, af.slotBase⟩ XI 0) hstar)
    (sim_runGN (sem := fun n => csem F ⟨fa.k, af.slotBase⟩ (XI.at n))
      (semB := fun n => csem F ⟨fa.k, af.slotBase⟩ (XI.at n).noCall)
      (noncallIndep_csem F ⟨fa.k, af.slotBase⟩ XI) (probeOf_csem F ⟨fa.k, af.slotBase⟩ XI)
      hP Hb Hs hseg htc fuel cs 0 0 k0 ρ₁ w₁ .refl hm)
  refine ⟨fun vals cm h => ?_, fun c' h => ?_⟩
  · rw [h] at hrun
    obtain ⟨us, outs, w, cm0, sv, hret, h1, h2, -, h3, h4, h5, u, hu, hd⟩ := hrun
    exact ⟨us, outs, w, hret, h1, h2, AllHold.prefix_append h3,
      h5 ▸ memRel_leave (memRel_free h4.1.1 _), u, hu, hd⟩
  · rw [h] at hrun
    exact hrun

/-- **`iselSim_relWI_cleanup` with the CLIF call count at the return.** Original doc: **CLIF → counted VCode on the cleanup path** (`iselSim_relW_cleanup` for the counted run
`valueSemI F ctx XI` from counter `0`), with the callee contract of call number `n` needed only at
the states of the CLIF run reached after `n` extern calls, for the environment restricted to that
state's invocation; under the ISLE call-count properties `InstCallsOne`, `TryCallsOne`. -/
theorem iselSim_relWI_cleanupN {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
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
      ∃ us outs w, VRetFrom vc (valueSemI F ⟨fa.k, af.slotBase⟩ XI) ⟨0, 0, ρ₀, (w₀, 0)⟩ us outs w ∧
        RetPins vals us ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w.1 ∧
        ∃ u, ReachN env p cs u w.2 ∧ Clif.step env p u = .done vals cm) ∧
    (∀ c', Clif.runLoop env p fuel cs = .trapped c' →
      VTrapFrom vc (valueSemI F ⟨fa.k, af.slotBase⟩ XI) ⟨0, 0, ρ₀, (w₀, 0)⟩ c') := by
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
  have hrun := RunOkAbiN.prefix
    (vstar_mapW (counted_probe_proj hPr 0) hstar)
    (sim_runGN (noncallIndep_valueSem F ⟨fa.k, af.slotBase⟩ XI) hPr hP Hb Hs hseg htc fuel cs 0 0
      k0 ρ₁ w₁ .refl hm)
  refine ⟨fun vals cm h => ?_, fun c' h => ?_⟩
  · rw [h] at hrun
    obtain ⟨us, outs, w, cm0, sv, hret, h1, h2, -, h3, h4, h5, u, hu, hd⟩ := hrun
    exact ⟨us, outs, w, hret, h1, h2, AllHold.prefix_append h3,
      h5 ▸ memRel_leave (memRel_free h4.1.1 _), u, hu, hd⟩
  · rw [h] at hrun
    exact hrun

end E2E
