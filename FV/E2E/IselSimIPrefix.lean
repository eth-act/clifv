module

public import FV.E2E.IselSimITry

@[expose] public section

/-!
# The counted CLIF → VCode simulation of run prefixes (SEM1 item (d), `docs/plans/uninit.md` §5.9)

`sim_runG` relates whole runs. The induction step of the slot-byte statement needs, at the
machine's call `n`, the CLIF invocation of count `n` related to the VCode state the counted run has
reached there (Finding "stage 2 needs the CLIF/machine call correspondence"). `sim_prefixG`: every
state reached from the entry after `n` calls is matched (`Match`) by a VCode state the counted run
reaches with counter `n`, except the pending `jump` after a `try_call` (whose next state is
matched); `sim_prefix_call` restates it for calling states (`callNum = 1`).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

section
variable {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
  {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId}
  {env : Clif.Env} {p : Clif.Program} {slots : List (Clif.SlotId × Nat)} {W : Type}
  {sem semB : Nat → ISem CV W} {MRW : MemRelTW W}

/-- The VCode state reached with counter `n` matches `t`. -/
def PrefixAt (f : Clif.Function) (vc : VCode) (ctx : Ctx) (R : Reg → Reg) (gn : Nat → Nat)
    (bl : List BLow) (A : Nat → Nat → List Clif.ValueId) (sem : Nat → ISem CV W)
    (MRW : MemRelTW W) (slots : List (Clif.SlotId × Nat)) (v0 : VState CV (W × Nat))
    (t : Clif.State) (n : Nat) : Prop :=
  ∃ b k ρ w, Star (VStep vc (ISem.counted sem)) (.run v0) (.run ⟨b, k, ρ, (w, n)⟩) ∧
    Match f ctx R gn bl A MRW slots t ⟨b, k, ρ, w⟩

/-- **Run prefixes, counted, for a family**: from a matched entry, every state `t` reached after
`n` calls is matched by a state of the counted VCode run with counter `n`, or is the pending
`jump` of a `try_call` state `t0` (count `n - 1`) that is. -/
theorem sim_prefixG (hni : NoncallIndep sem) (hPr : ProbeOf semB sem) {cs : Clif.State}
    (hP : RunPrem env p f cs)
    (Hb : ∀ n, DriverHyp f vc ctx st0 R gn bl A (semB n) MRW (env.only fun _ _ _ => False) p)
    (Hs : ∀ s n, ReachN env p cs s n → DriverHyp f vc ctx st0 R gn bl A (sem n) MRW
      (env.only (Clif.Invoked env p s)) p)
    (hseg : ∀ b B j stm, f.blocks[b]? = some B → B.body[j]? = some stm →
      stm.inst.isCallLike = true → callsI (seg f R bl b j) = 1)
    (htc : TryCallsOne f) {b0 k0 : Nat} {ρ0 : Nat → CV} {w0 : W}
    (hm0 : Match f ctx R gn bl A MRW slots cs ⟨b0, k0, ρ0, w0⟩) :
    ∀ t n, ReachN env p cs t n →
      PrefixAt f vc ctx R gn bl A sem MRW slots ⟨b0, k0, ρ0, (w0, 0)⟩ t n ∨
      ((t.frame.body = [] ∧ ∃ bc, t.frame.term = .jump bc) ∧
        ∃ t0 n0, ReachN env p cs t0 n0 ∧ n = n0 + 1 ∧ t0.frame.body = [] ∧
          t0.frame.term.isTry = true ∧ Clif.step env p t0 = .next t ∧
          PrefixAt f vc ctx R gn bl A sem MRW slots ⟨b0, k0, ρ0, (w0, 0)⟩ t0 n0) := by
  intro t n hr
  induction hr with
  | refl => exact .inl ⟨b0, k0, ρ0, w0, .refl _, hm0⟩
  | @snoc s s' n hr hs ih =>
    rcases ih with ⟨b, k, ρ, w, hstar, hm⟩ | ⟨⟨hb, bc, hj⟩, t0, n0, hr0, rfl, hb0, ht0, hs0,
        b, k, ρ, w, hstar, hm⟩
    · -- `s` is matched
      have hfunc : s.frame.func = f := hm.2.1
      cases hbody : s.frame.body with
      | nil =>
        cases hty : s.frame.term.isTry with
        | false =>
          obtain ⟨T1, -, -⟩ := term_stepG hPr (Hb n) hm hbody hty
          obtain ⟨b', k', ρ', w', hst, hm'⟩ := T1 s' hs
          have hc0 : callNum s = 0 := by simp [callNum, hbody, hty]
          rw [hc0, Nat.add_zero]
          exact .inl ⟨b', k', ρ', w', hstar.trans hst, hm'⟩
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
          obtain ⟨-, Tnx⟩ := term_step_tryG hni (Hs s n hr) htc hm hbody hT hind
          have hst : Clif.step (env.only (Clif.Invoked env p s)) p s = Clif.step env p s :=
            Clif.step_only fun _ _ _ h => h
          obtain ⟨hmid, -⟩ := Tnx s' (hst.trans hs)
          have hc1 : callNum s = 1 := by simp [callNum, hbody, hty]
          rw [hc1]
          exact .inr ⟨hmid, s, n, hr, rfl, hbody, hty, hs, b, k, ρ, w, hstar, hm⟩
      | cons st rest =>
        obtain ⟨-, -, -, -, B, j, hB, -, -, hbd, -⟩ := id hm
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
          obtain ⟨S1, -⟩ := stmt_stepG_noCall hPr (Hb n) hm hbody hcl hind
          obtain ⟨b', k', ρ', w', hst', hm'⟩ := S1 s' hs
          have hc0 : callNum s = 0 := by simp [callNum, hbody, hcl]
          rw [hc0, Nat.add_zero]
          exact .inl ⟨b', k', ρ', w', hstar.trans hst', hm'⟩
        | true =>
          obtain ⟨S1, -⟩ := stmt_stepG_call hni (Hs s n hr) hseg hm hbody hcl hind
          obtain ⟨b', k', ρ', w', hst', hm'⟩ := S1 s' hs
          have hc1 : callNum s = 1 := by simp [callNum, hbody, hcl]
          rw [hc1]
          exact .inl ⟨b', k', ρ', w', hstar.trans hst', hm'⟩
    · -- `s` is the pending `jump` of the `try_call` state `t0`
      obtain ⟨B, j, hB, hterm, -⟩ := hm.2.2.2.2
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
      obtain ⟨-, Tnx⟩ := term_step_tryG hni (Hs t0 n0 hr0) htc hm hb0 hT hind
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

/-- **Calling states are matched**: a state reached after `n` calls that makes a call is matched
by a state of the counted VCode run with counter `n`. -/
theorem sim_prefix_call (hni : NoncallIndep sem) (hPr : ProbeOf semB sem) {cs : Clif.State}
    (hP : RunPrem env p f cs)
    (Hb : ∀ n, DriverHyp f vc ctx st0 R gn bl A (semB n) MRW (env.only fun _ _ _ => False) p)
    (Hs : ∀ s n, ReachN env p cs s n → DriverHyp f vc ctx st0 R gn bl A (sem n) MRW
      (env.only (Clif.Invoked env p s)) p)
    (hseg : ∀ b B j stm, f.blocks[b]? = some B → B.body[j]? = some stm →
      stm.inst.isCallLike = true → callsI (seg f R bl b j) = 1)
    (htc : TryCallsOne f) {b0 k0 : Nat} {ρ0 : Nat → CV} {w0 : W}
    (hm0 : Match f ctx R gn bl A MRW slots cs ⟨b0, k0, ρ0, w0⟩) {t : Clif.State} {n : Nat}
    (hr : ReachN env p cs t n) (hc : callNum t = 1) :
    PrefixAt f vc ctx R gn bl A sem MRW slots ⟨b0, k0, ρ0, (w0, 0)⟩ t n := by
  rcases sim_prefixG hni hPr hP Hb Hs hseg htc hm0 t n hr with h | ⟨⟨hb, bc, hj⟩, -⟩
  · exact h
  · simp [callNum, hb, hj, Clif.Terminator.isTry] at hc

end

/-- **CLIF → counted VCode at the calls** (the `Compiled` path, the premises of
`iselSim_relWI`): every state reached after `n` calls that makes a call has its memory
`RelW`-related to the world of a state the counted VCode run from the entry reaches with
counter `n`. -/
theorem iselSim_prefixWI {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
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
    (hargs : ArgsAtEntry F f.sig args w₀) (htr : TrapsExplicit env p cs) :
    ∀ t n, ReachN env p cs t n → callNum t = 1 →
      ∃ b k ρ w, Star (VStep vc (csemI F ⟨fa.k, af.slotBase⟩ XI)) (.run ⟨0, 0, ρ₀, (w₀, 0)⟩)
        (.run ⟨b, k, ρ, (w, n)⟩) ∧
        RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c t.frame.slots t.mem w := by
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
  exact ⟨b, k', ρ, w,
    (vstar_mapW (csem_noCall_proj F ⟨fa.k, af.slotBase⟩ XI 0) hstar).trans hst,
    by rw [hmt.2.2.1]; exact hmt.2.2.2.1⟩

end E2E
