import FV.Backend.Proof.LowerSimSkip
import FV.Backend.Proof.LowerSimMemTrap

/-!
# Memory traps of the kept code (`skipDead`)

`driver_memtrap` (`FV/Backend/Proof/LowerSimMemTrap.lean`) for `vcK`, the VCode without the
unused statements (`SkipHyp`): an atomic's statement is not `skippable`, so its first instruction
(the LL/SC loop) is kept, with the same address use (`stmt_memtrapK`); the continuing steps and the
explicit traps are the kept code's (`stmt_stepK`, `term_step_abiK`, `term_step_tryK`).
-/

namespace Backend.Proof.Driver
open Backend Backend.Proof

theorem skippable_of_memTrapInst {i : Clif.Inst} (h : Clif.memTrapInst i = true) :
    skippable i = false := by
  cases i <;> simp_all [skippable, Clif.memTrapInst]

section
variable {f : Clif.Function} {vc vcK : VCode} {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
  {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId} {W : Type}
  {sem : ISem CV W} {MR : MemRelTW W} {env : Clif.Env} {p : Clif.Program}
  {slots : List (Clif.SlotId × Nat)} {drop : Nat → Nat → Bool}

/-- **A memory trap of the kept code** (`stmt_memtrap` for `vcK`). -/
theorem stmt_memtrapK (H : DriverHyp f vc ctx st0 R gn bl A sem MR env p)
    (hK : SkipHyp f vc R bl drop vcK) {s : Clif.State} {vsK : VState CV W}
    (hm : MatchK f ctx R gn bl A MR slots (skipMask f R bl vc drop)
      (DeadDef vc (skipMask f R bl vc drop)) s vsK)
    {stm : Clif.Stmt} {rest : List Clif.Stmt} (hbody : s.frame.body = stm :: rest)
    (hmt : Clif.memTrapInst stm.inst = true) {c : Clif.TrapCode}
    (hs : Clif.step env p s = .trapped c) {Q : Nat → Nat → Prop}
    (hQ : ∀ a n, Clif.MemTrapAt env p s c a n → Q a n) :
    VMemTrapFrom vcK sem vsK c (addrPred Q) := by
  have hD := hK.deletes
  obtain ⟨⟨b, k, ρ, w⟩, hC, hM⟩ := hm
  obtain ⟨B, j, hB, hstm, rfl, hpos, vb, i, ops, u, us, n, hvb, hi, hops, hvu, hlt, hA⟩ :=
    stmt_memtrap0 H hM hbody hmt hs hQ
  have hjlt : j < B.body.length := (List.getElem?_eq_some_iff.mp hstm).1
  have hdrop : drop b j = false := by
    cases hd : drop b j
    · rfl
    · have hsk := hK.skip b j B stm hd hB hstm
      rw [skippable_of_memTrapInst hmt] at hsk
      cases hsk
  have hmk : (skipMask f R bl vc drop b)[pos f R bl b j]? = some true := by
    have := skipMask_seg (vc := vc) (drop := drop) hB hjlt hpos
    rw [Nat.add_zero, hdrop] at this
    exact this
  obtain ⟨vbK, hvbK, hins, -, -⟩ := hD.blk b vb hvb
  have hiK : vbK.insts[kidx (skipMask f R bl vc drop b) (pos f R bl b j)]? = some i := by
    rw [← Array.getElem?_toList, hins,
      maskKeep_getElem? (by rw [hD.len b vb hvb]; simp) hmk, Array.getElem?_toList]
    exact hi
  obtain ⟨bK, kK, ρK, wK⟩ := vsK
  obtain ⟨hb, hk, hw, hρ⟩ := hC
  simp only at hb hk hw hρ
  subst bK kK wK
  have hvu' := vuses_congr_of hops (fun u hu => hρ u (hD.uses b vb _ i hvb hi hmk u hu))
  exact ⟨b, _, ρK, w, vbK, i, ops, u, us, n, .refl _, hvbK, hiK, hops, by rw [← hvu']; exact hvu,
    hlt, hA⟩

/-- **A matched state of the kept code, or the state between the two steps of a `try_call`**
(`MatchT` for `vcK`). -/
def MatchTK (_H : DriverHyp f vc ctx st0 R gn bl A sem MR env p)
    (_hK : SkipHyp f vc R bl drop vcK) (s : Clif.State) (vs : VState CV W) : Prop :=
  MatchK f ctx R gn bl A MR slots (skipMask f R bl vc drop)
      (DeadDef vc (skipMask f R bl vc drop)) s vs ∨
    ((∀ c, Clif.step env p s ≠ .trapped c) ∧ ∀ s', Clif.step env p s = .next s' →
      ∃ vs', Star (VStep vcK sem) (.run vs) (.run vs') ∧
        MatchK f ctx R gn bl A MR slots (skipMask f R bl vc drop)
          (DeadDef vc (skipMask f R bl vc drop)) s' vs')

/-- One continuing step of the kept code (`matchT_step` for `vcK`). -/
theorem matchT_stepK (H : DriverHyp f vc ctx st0 R gn bl A sem MR env p)
    (hK : SkipHyp f vc R bl drop vcK) {cs s s' : Clif.State}
    (hP : RunPremM env p f cs) (hr : Reach env p cs s) {vs : VState CV W}
    (hm : MatchTK (slots := slots) H hK s vs) (hs : Clif.step env p s = .next s') :
    ∃ vs', Star (VStep vcK sem) (.run vs) (.run vs') ∧ MatchTK (slots := slots) H hK s' vs' := by
  rcases hm with hm | ⟨-, hnx⟩
  · obtain ⟨vsF, -, hMF⟩ := id hm
    cases hbody : s.frame.body with
    | nil =>
      cases hty : s.frame.term.isTry with
      | false =>
        obtain ⟨vs', hstar, hm'⟩ := (term_step_abiK hK H hm hbody hty).1 s' hs
        exact ⟨vs', hstar, .inl hm'⟩
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
          fun callee args ht => hP.tryIndirect s callee args et hr hbody ht
            ⟨B, hBmem, hterm.symm.trans ht⟩
        obtain ⟨-, Tnx⟩ := term_step_tryK hK H hm hbody hT hind
        obtain ⟨N1, -, N3⟩ := Tnx s' hs
        exact ⟨_, .refl _, .inr ⟨N1, N3⟩⟩
    | cons st rest =>
      obtain ⟨-, -, -, -, B, j, hB, -, -, hbd, -⟩ := id hMF
      have hst : st ∈ B.body := by
        rw [hbd] at hbody
        exact List.mem_of_mem_drop (hbody ▸ List.mem_cons_self)
      have hBmem : B ∈ f.blocks := List.mem_of_getElem? hB
      have hind : ∀ sig callee args, st.inst = .callIndirect sig callee args → ∀ cv,
          s.frame.get callee = .ok cv → ∀ g ∈ p.funcs, s.mem.symbols g.name ≠ some cv.toNat :=
        fun sig callee args hi => hP.indirect s st rest sig callee args hr hbody hi ⟨B, hBmem, hst⟩
      obtain ⟨vs', hstar, hm'⟩ := (stmt_stepK hK H hm hbody hind).1 s' hs
      exact ⟨vs', hstar, .inl hm'⟩
  · obtain ⟨vs', hstar, hm'⟩ := hnx s' hs
    exact ⟨vs', hstar, .inl hm'⟩

/-- **Every reachable state is matched** by a state of the kept code's run. -/
theorem reach_matchK (H : DriverHyp f vc ctx st0 R gn bl A sem MR env p)
    (hK : SkipHyp f vc R bl drop vcK) {cs : Clif.State} (hP : RunPremM env p f cs) :
    ∀ {s s' : Clif.State}, Reach env p s s' → Reach env p cs s → ∀ {vs : VState CV W},
      MatchTK (slots := slots) H hK s vs →
      ∃ vs', Star (VStep vcK sem) (.run vs) (.run vs') ∧ MatchTK (slots := slots) H hK s' vs' := by
  intro s s' h
  induction h with
  | refl => intro _ vs hm; exact ⟨vs, .refl _, hm⟩
  | step h1 _ ih =>
    intro hr vs hm
    obtain ⟨vs1, hst1, hm1⟩ := matchT_stepK H hK hP hr hm h1
    obtain ⟨vs2, hst2, hm2⟩ := ih (hr.snoc h1) hm1
    exact ⟨vs2, hst1.trans hst2, hm2⟩

/-- **The trapping state of the kept code** (`trap_matchT` for `vcK`). -/
theorem trap_matchTK (H : DriverHyp f vc ctx st0 R gn bl A sem MR env p)
    (hK : SkipHyp f vc R bl drop vcK) {cs s : Clif.State}
    (hP : RunPremM env p f cs) (hr : Reach env p cs s) {vs : VState CV W}
    (hm : MatchTK (slots := slots) H hK s vs) {c : Clif.TrapCode}
    (hs : Clif.step env p s = .trapped c) {Q : Nat → Nat → Prop}
    (hQ : ∀ a n, Clif.MemTrapAt env p s c a n → Q a n) :
    VTrapFrom vcK sem vs c ∨ VMemTrapFrom vcK sem vs c (addrPred Q) := by
  rcases hm with hm | ⟨hnt, -⟩
  · obtain ⟨vsF, -, hMF⟩ := id hm
    cases hbody : s.frame.body with
    | nil =>
      cases hty : s.frame.term.isTry with
      | false => exact .inl ((term_step_abiK hK H hm hbody hty).2.2 c hs)
      | true =>
        obtain ⟨B, j, hB, hterm, -⟩ := hMF.2.2.2.2
        have hBmem : B ∈ f.blocks := List.mem_of_getElem? hB
        cases ht : s.frame.term with
        | tryCall fn args et =>
          exact absurd (hterm.symm.trans ht) (hP.tryCall s c fn args et hr hs hbody ht B hBmem)
        | tryCallIndirect callee args et =>
          exact absurd (hterm.symm.trans ht)
            (hP.tryCallInd s c callee args et hr hs hbody ht B hBmem)
        | _ => rw [ht] at hty; cases hty
    | cons st rest =>
      obtain ⟨-, -, -, -, B, j, hB, -, -, hbd, -⟩ := id hMF
      have hst : st ∈ B.body := by
        rw [hbd] at hbody
        exact List.mem_of_mem_drop (hbody ▸ List.mem_cons_self)
      have hBmem : B ∈ f.blocks := List.mem_of_getElem? hB
      have hind : ∀ sig callee args, st.inst = .callIndirect sig callee args → ∀ cv,
          s.frame.get callee = .ok cv → ∀ g ∈ p.funcs, s.mem.symbols g.name ≠ some cv.toNat :=
        fun sig callee args hi => hP.indirect s st rest sig callee args hr hbody hi ⟨B, hBmem, hst⟩
      rcases hP.stmt s c st rest hr hs hbody with hexp | hmt
      · exact .inl ((stmt_stepK hK H hm hbody hind).2 c hs hexp)
      · exact .inr (stmt_memtrapK H hK hm hbody hmt hs hQ)
  · exact absurd hs (hnt c)

end

section
variable {f : Clif.Function} {vc vcK : VCode} {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
  {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId} {sem : Sem}
  {MR : MemRelT} {env : Clif.Env} {p : Clif.Program} {slots : List (Clif.SlotId × Nat)}
  {drop : Nat → Nat → Bool}

/-- **The driver lemma for traps with memory traps of the kept code** (`driver_memtrap` for
`vcK`). -/
theorem driver_memtrap_skip (H : DriverHyp f vc ctx st0 R gn bl A sem MR env p)
    (hK : SkipHyp f vc R bl drop vcK) (hds : DriverSem sem)
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    (hMem : MemRefines F sb syms sem) (hMR : MRStable F MR)
    {cs : Clif.State} {B0 : Clif.Block} (hB0 : f.blocks[0]? = some B0)
    (hcall : cs.callers = []) (hfunc : cs.frame.func = f) (hslots : cs.frame.slots = slots)
    (hbody : cs.frame.body = B0.body) (hterm : cs.frame.term = B0.term) {args : List Clif.Val}
    (hregs : Clif.Regs.empty.setMany (B0.params.map (·.1)) args = some cs.frame.regs)
    (hty : args.map (·.ty) = B0.params.map (·.2))
    (hsig : args.map (·.ty) = f.sig.params.map (·.ty))
    {ρ₀ : Nat → CV} {w₀ : Arm.ArmState} (hmr : MR slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (hP : RunPremM env p f cs) {Q : Nat → Nat → Prop}
    (hQ : ∀ s c a n, Reach env p cs s → Clif.MemTrapAt env p s c a n → Q a n)
    (fuel : Nat) (c : Clif.TrapCode) (hrun : Clif.runLoop env p fuel cs = .trapped c) :
    VTrapFrom vcK sem ⟨0, 0, ρ₀, w₀⟩ c ∨ VMemTrapFrom vcK sem ⟨0, 0, ρ₀, w₀⟩ c (addrPred Q) := by
  obtain ⟨k, ρ₁, w₁, hstar, hm⟩ := entry_stepP H hds hMem hMR hB0 hcall hfunc hslots hbody hterm
    hregs hty hsig hmr hargs (ρ₀ := ρ₀)
  obtain ⟨vsK, hsK, hmK⟩ := entry_matchK hK hB0 hbody hstar hm
  obtain ⟨s, hr, hs⟩ := runLoop_trapped_reach fuel cs c hrun
  obtain ⟨vs, hstar', hm'⟩ := reach_matchK (slots := slots) H hK hP hr (.refl _) (.inl hmK)
  rcases trap_matchTK H hK hP hr hm' hs (hQ s c · · hr) with h | h
  · exact .inl (VTrapFrom.prefix (hsK.trans hstar') h)
  · exact .inr (VMemTrapFrom.prefix (hsK.trans hstar') h)

/-- **The driver lemma for traps with memory traps for `vc` or its kept code.** -/
theorem driver_memtrap_stage (H : DriverHyp f vc ctx st0 R gn bl A sem MR env p)
    (hsk : vcK = vc ∨ SkipHyp f vc R bl drop vcK) (hds : DriverSem sem)
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    (hMem : MemRefines F sb syms sem) (hMR : MRStable F MR)
    {cs : Clif.State} {B0 : Clif.Block} (hB0 : f.blocks[0]? = some B0)
    (hcall : cs.callers = []) (hfunc : cs.frame.func = f) (hslots : cs.frame.slots = slots)
    (hbody : cs.frame.body = B0.body) (hterm : cs.frame.term = B0.term) {args : List Clif.Val}
    (hregs : Clif.Regs.empty.setMany (B0.params.map (·.1)) args = some cs.frame.regs)
    (hty : args.map (·.ty) = B0.params.map (·.2))
    (hsig : args.map (·.ty) = f.sig.params.map (·.ty))
    {ρ₀ : Nat → CV} {w₀ : Arm.ArmState} (hmr : MR slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (hP : RunPremM env p f cs) {Q : Nat → Nat → Prop}
    (hQ : ∀ s c a n, Reach env p cs s → Clif.MemTrapAt env p s c a n → Q a n)
    (fuel : Nat) (c : Clif.TrapCode) (hrun : Clif.runLoop env p fuel cs = .trapped c) :
    VTrapFrom vcK sem ⟨0, 0, ρ₀, w₀⟩ c ∨ VMemTrapFrom vcK sem ⟨0, 0, ρ₀, w₀⟩ c (addrPred Q) := by
  rcases hsk with rfl | hK
  · exact driver_memtrap H hds hMem hMR hB0 hcall hfunc hslots hbody hterm hregs hty hsig hmr
      hargs hP hQ fuel c hrun
  · exact driver_memtrap_skip H hK hds hMem hMR hB0 hcall hfunc hslots hbody hterm hregs hty
      hsig hmr hargs hP hQ fuel c hrun

end

end Backend.Proof.Driver
