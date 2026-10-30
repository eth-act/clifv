import FV.E2E.LinkArmCallDecode
import FV.E2E.LinkArmTabCount
import FV.E2E.LinkArmInvokedStep

/-!
# One step of the caller's table and of the CLIF counter (SEM1 #537, #680 (3), stage 2 glue (2))

The count invariant of an activation (the caller table's count before call `j` is the CLIF
counter's advance `Σ_{k<j} advAt k`) advances over one machine step:

* `tabUpTo_succ_noCall`: a step that is no call keeps the table;
* `tabUpTo_succ_base`: a call of no function of `P` (no `CallsTo`) adds nothing;
* `callDecodeBase`: a call site whose callee (by name or through its address) is no function of
  `P` calls none (`¬ CallsTo`);
* `envOfB_base_extern`, `envOfB_prog_returned`: `envOfB`'s externs;
* `adv_base`, `adv_prog`: the CLIF step of a calling state invoking a base extern keeps the
  placement (advance `0`); invoking a function of `P`, it has the memory the callee's run returns.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

namespace LinkSys

variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

/-- **A step that is no call keeps the table.** -/
theorem tabUpTo_succ_noCall {M : Nat} {g : Clif.Function} {s : Arm.ArmState}
    {b : Nat → Nat → BitVec 8} {k i e : Nat}
    (hnc : ¬ CallPc (L.A g).fa (L.A g).base (Arm.r .PC (runX (L.mach (M + 1) g) i s)))
    (h : L.TabUpTo (M + 1) g s b k (i + 1) e) : L.TabUpTo (M + 1) g s b k i e := by
  obtain ⟨E, rfl, hE⟩ := h
  refine ⟨E, ?_, fun i' hi' => hE i' (by omega)⟩
  simp only [callsBefore, hnc, ↓reduceIte, Nat.add_zero]

/-- **A call of no function of `P` adds nothing to the table.** -/
theorem tabUpTo_succ_base {M : Nat} {g : Clif.Function} {s : Arm.ArmState}
    {b : Nat → Nat → BitVec 8} {k i e e' : Nat}
    (hpc : CallPc (L.A g).fa (L.A g).base (Arm.r .PC (runX (L.mach (M + 1) g) i s)))
    (hn : ∀ h, ¬ L.CallsTo g (runX (L.mach (M + 1) g) i s) h)
    (h1 : L.TabUpTo (M + 1) g s b k (i + 1) e') (h0 : L.TabUpTo (M + 1) g s b k i e) : e' = e := by
  obtain ⟨E, rfl, hE⟩ := h1
  have hE0 := (hE i (Nat.lt_succ_self i) hpc).1 hn
  have h0' : L.TabUpTo (M + 1) g s b k i
      (Clif.sumTo E (callsBefore (L.mach (M + 1) g) (L.A g).fa (L.A g).base s i)) :=
    ⟨E, rfl, fun i' hi' => hE i' (by omega)⟩
  rw [L.tabUpTo_count _ _ _ _ _ _ _ _ _ _ h0 h0']
  simp only [callsBefore, hpc, ↓reduceIte, Clif.sumTo, hE0, Nat.add_zero]

/-- **A call site of a callee that is no function of `P` calls none.** -/
theorem callDecodeBase (hL : L.Ok) {g : Clif.Function} (hg : g ∈ L.P.funcs) {u : Arm.ArmState}
    {i : MInst} {info : CallInfo} (hi : i = .call info ∨ ∃ ti, i = .tryCall info ti)
    (hS : (L.A g).vcp.CallSite info) {ops : Array Operand} {regs : Array Reg} {i' : MInst}
    (hops : i.operands = .ok ops) {cc : CheckCtx} {wh : String}
    (hst : cc.checkStatic wh ops (regs.map .reg) i.clobbers = .ok ())
    (hasg : i.assign regs = .ok i') (hpi : CallAt (L.A g).fa (L.A g).base (Arm.r .PC u) i')
    (himgU : ∀ a, L.Img a → u.mem a = L.imgMem a) {nm : String} (hnm : L.P.func? nm = none)
    (hd : callDest info = some nm ∨
      callDest info = none ∧ ∃ u0 args, useVals ops regs u = u0 :: args ∧ lo64 u0 = L.Xb.sym nm 0) :
    ∀ h, ¬ L.CallsTo g u h := by
  obtain ⟨hops0, ic, hasg0, hpi0⟩ := call_of_callLike hi hops hasg hpi
  obtain ⟨x, hins, hx⟩ := L.insnAt_callAt hL hg hpi0
  intro h hct
  rcases hd with hdn | ⟨hdn, u0, args, huse, hlo⟩
  · have hdest : info.dest = .sym nm := by
      unfold callDest at hdn
      split at hdn
      · rename_i n e; cases hdn; exact e
      · cases hdn
    obtain ⟨d, us, ds⟩ := info
    simp only at hdest
    subst hdest
    obtain ⟨us', ds', he⟩ := assign_call_sym hasg0
    injection he with he
    subst he
    simp only [MInst.callInsn?, Option.some.injEq] at hx
    subst hx
    rcases hct with ⟨n, hn, hpf⟩ | ⟨⟨x', hx'⟩, -⟩
    · rw [hins] at hn; cases hn
      rw [hnm] at hpf; cases hpf
    · rw [hins] at hx'; cases hx'
  · have hreg : ∀ n, info.dest ≠ .sym n := by
      intro n e
      unfold callDest at hdn
      rw [e] at hdn
      cases hdn
    obtain ⟨tv, Lu, Ld, rfl, -⟩ := hL.blrRegs g hg info hS hreg
    obtain ⟨hsz', hloc, -, -⟩ := checkStatic_facts hst
    rw [operands_call_reg] at hops0
    cases hops0
    obtain ⟨r0, hregs0⟩ := callRegs_eq_reg (regs := regs) (by simpa using hsz')
      (fun p hp r hr => (hloc p hp).2 r hr)
    obtain ⟨n0, rfl, hn0, -⟩ : ∃ n, r0 = .x n ∧ n < 29 ∧ n ≠ 16 := by
      have hmem : (tgtOp tv, Loc.reg r0) ∈
          (((tgtOp tv :: (retOps Lu ++ callDefOps Ld)).toArray).zip (regs.map Loc.reg)).toList := by
        simp [Array.toList_zip, Array.toList_map, hregs0]
      obtain ⟨n, hn, h29, h16, -⟩ := locOk_int (hloc _ hmem).1
      exact ⟨n, hn, h29, h16⟩
    rw [call_useVals_reg (tv := tv) (s := u) hregs0] at huse
    simp only [List.cons.injEq] at huse
    obtain ⟨rfl, -⟩ := huse
    obtain ⟨r1, us', ds', hr1, he⟩ := assign_call_reg hasg0
    injection he with he
    subst he
    have h0 : regs[0]? = some (.x n0) := by
      rw [← Array.getElem?_toList, hregs0]; rfl
    rw [h0] at hr1
    cases hr1
    have hc := hL.compiled g hg
    obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hc.layout
    have htgt : blrTarget u = some (lo64 (regVal u (.x n0))) := by
      obtain ⟨j, x', tt, hj, hx', hpc⟩ := hpi0
      simp only [MInst.callInsn?, Option.some.injEq] at hx'
      subst hx'
      rw [lo64_regVal_x]
      exact blrTarget_of hc.layout hlm hj hn0 hpc
        (fun k wd hk => hL.imgCode g hg u himgU k wd hk)
    have hs : symCallee L.Xb L.P (lo64 (regVal u (.x n0))) = none := by
      show L.P.funcs.find? (fun h' => L.Xb.sym h'.name 0 == lo64 (regVal u (.x n0))) = none
      rw [hlo]; exact (L.find_sym hL nm).2 hnm
    simp only [MInst.callInsn?, Option.some.injEq] at hx
    subst hx
    rcases hct with ⟨n, hn, -⟩ | ⟨-, hb⟩
    · rw [hins] at hn; cases hn
    · rw [htgt] at hb
      simp only [Option.bind_some] at hb
      rw [hs] at hb; cases hb

theorem envOfB_base_extern {M : Nat} {g : Clif.Function} {c : BitVec 64} {nm : String}
    (hpf : L.P.func? nm = none) : (L.envOfB M g c).extern nm = L.base.extern nm := by
  simp [envOfB, hpf, Clif.linkEnvR_none hpf]

theorem envOfB_prog_returned {M : Nat} {g h : Clif.Function} {c : BitVec 64} {nm : String}
    (hpf : L.P.func? nm = some h) {G : List Clif.Val → Clif.Mem → Clif.Outcome}
    (hG : (L.envOfB M g c).extern nm = some G) {vals : List Clif.Val} {cm : Clif.Mem}
    {cs' : Clif.State} {rvals : List Clif.Val} {cm' : Clif.Mem}
    (hinit : Clif.initState L.P nm vals cm = .ok cs') (hrun : L.crun M cs' = .returned rvals cm')
    {rv : List Clif.Val} {m1 : Clif.Mem} (hr : G vals cm = .returned rv m1) : m1 = cm' := by
  simp only [envOfB, hpf, Option.isSome_some, true_and, Clif.linkEnvR_some hpf,
    Option.map_some] at hG
  split at hG
  · exact absurd hG (by simp)
  · injection hG with hG
    subst hG
    simp only at hr
    split at hr
    · rw [hinit] at hr
      simp only at hr
      rw [hrun] at hr
      cases hr
      rfl
    · cases hr

/-- **The CLIF step of a calling state invoking a base extern keeps the placement.** -/
theorem adv_base (hL : L.Ok) (hN : L.NeedSlots) {M : Nat} {g : Clif.Function}
    (hgf : Clif.LinkFree g) {c : BitVec 64} {t t1 : Clif.State} (hI : Clif.LInv (L.P.only g) t)
    (hc : t.callers = []) {nm : String} {vals : List Clif.Val} {cm : Clif.Mem}
    (hinv : Clif.Invoked (L.envOfB M g c) L.P.bare t nm vals cm) (hpf : L.P.func? nm = none)
    (hst : Clif.step (L.envOfB M g c) L.P.bare t = .next t1) : Clif.NextAdv t.mem t1.mem 0 := by
  have hPf : ∀ f ∈ (L.P.only g).funcs, Clif.LinkFree f := fun f hf => by
    simp only [Clif.Program.only, List.mem_cons, List.not_mem_nil, or_false] at hf
    subst hf; exact hgf
  have hc1 := Clif.step_bare_callers hPf hI.1 hc hst
  obtain ⟨G, rv, hG, hr⟩ := invoked_step hPf hI hinv hst (hc1.trans hc.symm)
  rw [L.envOfB_base_extern hpf] at hG
  have hp := hL.baseKeepsPlace hN nm G hG vals cm rv t1.mem hr
  rw [hinv.1] at hp
  exact Clif.NextAdv.of_place hp

/-- **The CLIF step of a calling state invoking a function of `P`** has the memory the callee's
run returns. -/
theorem adv_prog {M : Nat} {g : Clif.Function} (hgf : Clif.LinkFree g) {c : BitVec 64}
    {t t1 : Clif.State} (hI : Clif.LInv (L.P.only g) t) (hc : t.callers = []) {h : Clif.Function}
    {vals : List Clif.Val} {cm : Clif.Mem}
    (hinv : Clif.Invoked (L.envOfB M g c) L.P.bare t h.name vals cm)
    (hpf : L.P.func? h.name = some h) {cs' : Clif.State} {rvals : List Clif.Val} {cm' : Clif.Mem}
    (hinit : Clif.initState L.P h.name vals cm = .ok cs') (hrun : L.crun M cs' = .returned rvals cm')
    (hst : Clif.step (L.envOfB M g c) L.P.bare t = .next t1) : t1.mem = cm' := by
  have hPf : ∀ f ∈ (L.P.only g).funcs, Clif.LinkFree f := fun f hf => by
    simp only [Clif.Program.only, List.mem_cons, List.not_mem_nil, or_false] at hf
    subst hf; exact hgf
  have hc1 := Clif.step_bare_callers hPf hI.1 hc hst
  obtain ⟨G, rv, hG, hr⟩ := invoked_step hPf hI hinv hst (hc1.trans hc.symm)
  exact L.envOfB_prog_returned hpf hG hinit hrun hr

end LinkSys

end E2E
