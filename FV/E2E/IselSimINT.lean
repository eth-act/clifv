import FV.E2E.IselSimIN
import FV.E2E.BackendPrefixAtEnds

/-!
# CLIF → counted VCode with the call count at the trap (SEM1 #537, traps under the oracle)

`iselSim_relWIN` gives the call count of the CLIF run at the VCode **return** (the counter of the
return's world is the count of a returning CLIF state). Its trap clause (`VTrapFrom`) does not
say which counter the VCode trap has. Here it does:

* `VTrapFromW`: `VTrapFrom` whose trapping instruction runs in a world satisfying `P`;
  `VTrapFromW.prefix`, `VTrapFromW.toVTrapFrom`, `vTrapFromW_mapW` (a world projection);
* `stmt_stepG_noCall_trapN`, `term_stepG_trapN`: the trap of a statement without an extern call /
  of a terminator other than `try_call`, from counter `n`, traps at counter `n` (the probe);
* `RunOkAbiNT`, `sim_runGNT`: `sim_runGN` whose trap is at the counter of a trapping CLIF state of
  the run (a calling statement does not trap under the run premises);
* **`iselSim_relWINT`**, **`iselSim_relWI_cleanupNT`**: the trap clause of `iselSim_relWIN` /
  `iselSim_relWI_cleanupN` with `∃ u, ReachN env p cs u nc ∧ Clif.step env p u = .trapped c` at
  the trap's counter `nc`.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

/-- **`VTrapFrom` with the trap's world**: the trapping instruction runs in a world `w` with
`P w`. -/
def VTrapFromW {W : Type} (vc : VCode) (sem : ISem CV W) (vs : VState CV W) (c : Clif.TrapCode)
    (P : W → Prop) : Prop :=
  ∃ b k ρ w vb i ops outs w', Star (VStep vc sem) (.run vs) (.run ⟨b, k, ρ, w⟩) ∧
    vc.blocks[b]? = some vb ∧ vb.insts[k]? = some i ∧ i.operands = .ok ops ∧
    sem i (vuses ops ρ) w = some (outs, w', .halt) ∧ trapCode? i = some c ∧ P w

theorem VTrapFromW.toVTrapFrom {W : Type} {vc : VCode} {sem : ISem CV W} {vs : VState CV W}
    {c : Clif.TrapCode} {P : W → Prop} (h : VTrapFromW vc sem vs c P) : VTrapFrom vc sem vs c := by
  obtain ⟨b, k, ρ, w, vb, i, ops, outs, w', hs, hvb, hi, hops, hsem, htc, -⟩ := h
  exact ⟨b, k, ρ, w, vb, i, ops, outs, w', hs, hvb, hi, hops, hsem, htc⟩

theorem VTrapFromW.prefix {W : Type} {vc : VCode} {sem : ISem CV W} {vs vs' : VState CV W}
    {c : Clif.TrapCode} {P : W → Prop} (h : Star (VStep vc sem) (.run vs) (.run vs'))
    (h' : VTrapFromW vc sem vs' c P) : VTrapFromW vc sem vs c P := by
  obtain ⟨b, k, ρ, w, vb, i, ops, outs, w', hs, h1⟩ := h'
  exact ⟨b, k, ρ, w, vb, i, ops, outs, w', h.trans hs, h1⟩

/-- A projected trap is a trap at a projected world. -/
theorem vTrapFromW_mapW {W₁ W₂ : Type} {π : W₂ → W₁} {vc : VCode} {sem₂ : ISem CV W₂}
    {sem₁ : ISem CV W₁} (hp : ISem.ProjW π sem₂ sem₁) {b k : Nat} {ρ : Nat → CV} {w : W₂}
    {c : Clif.TrapCode} (h : VTrapFrom vc sem₂ ⟨b, k, ρ, w⟩ c) :
    VTrapFromW vc sem₁ ⟨b, k, ρ, π w⟩ c (fun w₁ => ∃ w₂, w₁ = π w₂) := by
  obtain ⟨b', k', ρ', w', vb, i, ops, outs, w'', hs, hvb, hi, hops, hsem, htc⟩ := h
  exact ⟨b', k', ρ', π w', vb, i, ops, outs, π w'', vstar_mapW hp hs, hvb, hi, hops,
    hp _ _ _ _ _ _ hsem, htc, w', rfl⟩

/-- A trap of the probe at counter `n` is a counted trap at counter `n`. -/
theorem vTrapFromW_counted {W : Type} {sem semB : Nat → ISem CV W} (hB : ProbeOf semB sem)
    {n : Nat} {vc : VCode} {b k : Nat} {ρ : Nat → CV} {w : W} {c : Clif.TrapCode}
    (h : VTrapFrom vc (semB n) ⟨b, k, ρ, w⟩ c) :
    VTrapFromW vc (ISem.counted sem) ⟨b, k, ρ, (w, n)⟩ c (fun w => w.2 = n) := by
  obtain ⟨b', k', ρ', w', vb, i, ops, outs, w'', hs, hvb, hi, hops, hsem, htc, w₂, rfl⟩ :=
    vTrapFromW_mapW (counted_probe_proj hB n) h
  exact ⟨b', k', ρ', (w₂, n), vb, i, ops, outs, w'', hs, hvb, hi, hops, hsem, htc, rfl⟩

section
variable {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
  {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId}
  {env : Clif.Env} {p : Clif.Program} {slots : List (Clif.SlotId × Nat)} {W : Type}
  {sem semB : Nat → ISem CV W} {MRW : MemRelTW W}

/-- **The trap of a statement without an extern call stays at the counter** (`stmt_stepG_noCall`'s
trap clause). -/
theorem stmt_stepG_noCall_trapN (hB : ProbeOf semB sem) {n : Nat}
    (Hb : DriverHyp f vc ctx st0 R gn bl A (semB n) MRW (env.only fun _ _ _ => False) p)
    {s : Clif.State} {b k : Nat} {ρ : Nat → CV} {w : W}
    (hm : Match f ctx R gn bl A MRW slots s ⟨b, k, ρ, w⟩)
    {stm : Clif.Stmt} {rest : List Clif.Stmt} (hbody : s.frame.body = stm :: rest)
    (hnc : stm.inst.isCallLike = false)
    (hind : ∀ sig callee args, stm.inst = .callIndirect sig callee args → ∀ cv,
      s.frame.get callee = .ok cv → ∀ g ∈ p.funcs, s.mem.symbols g.name ≠ some cv.toNat) :
    ∀ c, Clif.step env p s = .trapped c → explicitTrapInst stm.inst = true →
      VTrapFromW vc (ISem.counted sem) ⟨b, k, ρ, (w, n)⟩ c (fun w => w.2 = n) := by
  have hstep : Clif.step (env.only fun _ _ _ => False) p s = Clif.step env p s :=
    step_none_of_callNum (by simp [callNum, hbody, hnc]) (fun _ _ h => by rw [hbody] at h; cases h)
  obtain ⟨-, S2⟩ := stmt_step Hb hm hbody hind
  exact fun c hs hexp => vTrapFromW_counted hB (S2 c (hstep.trans hs) hexp)

/-- **The trap of a terminator other than `try_call` stays at the counter** (`term_stepG`'s trap
clause). -/
theorem term_stepG_trapN (hB : ProbeOf semB sem) {n : Nat}
    (Hb : DriverHyp f vc ctx st0 R gn bl A (semB n) MRW (env.only fun _ _ _ => False) p)
    {s : Clif.State} {b k : Nat} {ρ : Nat → CV} {w : W}
    (hm : Match f ctx R gn bl A MRW slots s ⟨b, k, ρ, w⟩) (hbody : s.frame.body = [])
    (hnt : s.frame.term.isTry = false) :
    ∀ c, Clif.step env p s = .trapped c →
      VTrapFromW vc (ISem.counted sem) ⟨b, k, ρ, (w, n)⟩ c (fun w => w.2 = n) := by
  have hnr : ∀ fn args, s.frame.body = [] → s.frame.term ≠ .returnCall fn args := by
    intro fn args _ h
    obtain ⟨-, -, -, -, B, j, hB, hterm, -⟩ := hm
    exact Hb.noTail B (List.mem_of_getElem? hB) fn args (hterm.symm.trans h)
  have hstep : Clif.step (env.only fun _ _ _ => False) p s = Clif.step env p s :=
    step_none_of_callNum (by simp [callNum, hbody, hnt]) hnr
  obtain ⟨-, -, T3⟩ := term_step_abi Hb hm hbody hnt
  exact fun c hs => vTrapFromW_counted hB (T3 c (hstep.trans hs))

/-- **`RunOkAbiN` with the CLIF call count at the trap**: a trap is at the counter of a trapping
state of the CLIF run from `cs`. -/
def RunOkAbiNT {W : Type} (env : Clif.Env) (p : Clif.Program) (cs : Clif.State) (vc : VCode)
    (sem : ISem CV (W × Nat)) (MR : MemRelTW (W × Nat)) (slots : List (Clif.SlotId × Nat))
    (Q : List Clif.Val → Prop) (vs : VState CV (W × Nat)) : Clif.Outcome → Prop
  | .trapped c => ∃ nc, VTrapFromW vc sem vs c (fun w => w.2 = nc) ∧
      ∃ u, ReachN env p cs u nc ∧ Clif.step env p u = .trapped c
  | o => RunOkAbiN env p cs vc sem MR slots Q vs o

theorem RunOkAbiNT.prefix {W : Type} {cs : Clif.State} {sem : ISem CV (W × Nat)}
    {MR : MemRelTW (W × Nat)} {Q : List Clif.Val → Prop} {vs vs' : VState CV (W × Nat)}
    {o : Clif.Outcome} (h : Star (VStep vc sem) (.run vs) (.run vs'))
    (h' : RunOkAbiNT env p cs vc sem MR slots Q vs' o) :
    RunOkAbiNT env p cs vc sem MR slots Q vs o := by
  cases o with
  | trapped c =>
    obtain ⟨nc, ht, hu⟩ := h'
    exact ⟨nc, VTrapFromW.prefix h ht, hu⟩
  | returned vals cm => exact RunOkAbiN.prefix (o := .returned vals cm) h h'
  | stuck m => trivial
  | outOfFuel => trivial

/-- **`sim_runGN` with the CLIF call count at the trap** (`RunOkAbiNT`; same proof; a calling
statement does not trap under the run premises). -/
theorem sim_runGNT (hni : NoncallIndep sem) (hPr : ProbeOf semB sem) {cs : Clif.State}
    (hP : RunPrem env p f cs)
    (Hb : ∀ n, DriverHyp f vc ctx st0 R gn bl A (semB n) MRW (env.only fun _ _ _ => False) p)
    (Hs : ∀ s n, ReachN env p cs s n → DriverHyp f vc ctx st0 R gn bl A (sem n) MRW
      (env.only (Clif.Invoked env p s)) p)
    (hseg : ∀ b B j stm, f.blocks[b]? = some B → B.body[j]? = some stm →
      stm.inst.isCallLike = true → callsI (seg f R bl b j) = 1)
    (htc : TryCallsOne f) :
    ∀ fuel s n b k ρ w, ReachN env p cs s n →
      Match f ctx R gn bl A MRW slots s ⟨b, k, ρ, w⟩ →
        RunOkAbiNT env p cs vc (ISem.counted sem) (fun sl cm w => MRW sl cm w.1) slots (fun _ => True)
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
        obtain ⟨T1, T2, -⟩ := term_stepG hPr (Hb n) hm hbody hty
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
        | trapped c => exact ⟨n, term_stepG_trapN hPr (Hb n) hm hbody hty c hs, s, hr, hs⟩
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
            show RunOkAbiNT env p cs vc (ISem.counted sem) (fun sl cm w => MRW sl cm w.1) slots
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
        obtain ⟨S1, -⟩ := stmt_stepG_noCall hPr (Hb n) hm hbody hcl hind
        have hc0 : callNum s = 0 := by simp [callNum, hbody, hcl]
        cases hs : Clif.step env p s with
        | next s' =>
          obtain ⟨b', k', ρ', w', hstar, hm'⟩ := S1 s' hs
          have h := ih m (by omega) s' (n + callNum s) b' k' ρ' w' (hr.snoc hs) hm'
          rw [hc0, Nat.add_zero] at h
          exact RunOkAbiNT.prefix hstar h
        | done vals cm => exact absurd hs (stmt_not_done hbody hext hind)
        | trapped c =>
          exact ⟨n, stmt_stepG_noCall_trapN hPr (Hb n) hm hbody hcl hind c hs
            (hP.stmt s c st rest hr.reach hs hbody), s, hr, hs⟩
        | stuck => trivial
      | true =>
        obtain ⟨S1, -⟩ := stmt_stepG_call hni (Hs s n hr) hseg hm hbody hcl hind
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

/-- **`iselSim_relWIN`'s trap clause with the CLIF call count at the trap** (module doc). -/
theorem iselSim_relWINT {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
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
    ∀ c', Clif.runLoop env p fuel cs = .trapped c' →
      ∃ nc, VTrapFromW vc (csemI F ⟨fa.k, af.slotBase⟩ XI) ⟨0, 0, ρ₀, (w₀, 0)⟩ c'
        (fun w => w.2 = nc) ∧ ∃ u, ReachN env p cs u nc ∧ Clif.step env p u = .trapped c' := by
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
  have hrun := RunOkAbiNT.prefix
    (vstar_mapW (csem_noCall_proj F ⟨fa.k, af.slotBase⟩ XI 0) hstar)
    (sim_runGNT (sem := fun n => csem F ⟨fa.k, af.slotBase⟩ (XI.at n))
      (semB := fun n => csem F ⟨fa.k, af.slotBase⟩ (XI.at n).noCall)
      (noncallIndep_csem F ⟨fa.k, af.slotBase⟩ XI) (probeOf_csem F ⟨fa.k, af.slotBase⟩ XI)
      hP Hb Hs hseg htc fuel cs 0 0 k0 ρ₁ w₁ .refl hm)
  intro c' h
  rw [h] at hrun
  exact hrun

/-- **`iselSim_relWI_cleanupN`'s trap clause with the CLIF call count at the trap.** -/
theorem iselSim_relWI_cleanupNT {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
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
    ∀ c', Clif.runLoop env p fuel cs = .trapped c' →
      ∃ nc, VTrapFromW vc (valueSemI F ⟨fa.k, af.slotBase⟩ XI) ⟨0, 0, ρ₀, (w₀, 0)⟩ c'
        (fun w => w.2 = nc) ∧ ∃ u, ReachN env p cs u nc ∧ Clif.step env p u = .trapped c' := by
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
  have hrun := RunOkAbiNT.prefix
    (vstar_mapW (counted_probe_proj hPr 0) hstar)
    (sim_runGNT (noncallIndep_valueSem F ⟨fa.k, af.slotBase⟩ XI) hPr hP Hb Hs hseg htc fuel cs 0 0
      k0 ρ₁ w₁ .refl hm)
  intro c' h
  rw [h] at hrun
  exact hrun

end E2E
