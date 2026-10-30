import FV.E2E.LinkArmTableB
import FV.E2E.BackendPrefixI
import FV.E2E.LinkTrapCallInd

/-!
# The program call at a call site of the machine (SEM1 #537, #680 (3), stage 2 glue (1))

At a call site of `g`'s compiled code (`VCode.CallSite`) allocated to the machine call at the
state `u`'s pc (`CallAt`), under the GOT guard, a call of the function `h` of `P` that stage 2
answers (`stage2_answerF`'s shape: by name with the arguments `args`, or through a register
holding `h`'s address followed by `args`) passes `args` in `h`'s parameter registers
(`Ok.callRegs`, `Ok.blrRegs`), the machine step at `u` calls `h` (`CallsTo`), and the return
address is good for `h` (`Ok.raCall`, `Ok.raBlr`).

* `call_of_callLike`: a `call`/`try_call` site as its plain call;
* **`callDecode`**.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- **A call or a `try_call`'s call as the plain call**: its operands, its allocated call and
its call line. -/
theorem call_of_callLike {i : MInst} {info : CallInfo} (hi : i = .call info ∨ ∃ ti, i = .tryCall info ti)
    {ops : Array Operand} (hops : i.operands = .ok ops) {regs : Array Reg} {i' : MInst}
    (hasg : i.assign regs = .ok i') {fa : FnAsm} {base pc : BitVec 64} (hpi : CallAt fa base pc i') :
    (MInst.call info).operands = .ok ops ∧ ∃ ic, (MInst.call info).assign regs = .ok (.call ic) ∧
      CallAt fa base pc (.call ic) := by
  rcases hi with rfl | ⟨ti, rfl⟩
  · obtain ⟨ic, rfl⟩ := (assign_call_tryCall info regs).1 i' hasg
    exact ⟨hops, ic, hasg, hpi⟩
  · obtain ⟨ic, rfl, hasg'⟩ := (assign_call_tryCall info regs).2 ti i' hasg
    exact ⟨by rw [← operands_tryCall_call info ti]; exact hops, ic, hasg', callAt_tryCall_call hpi⟩

namespace LinkSys

variable (L : LinkSys)

/-- **The program call at a call site** (module doc). -/
theorem callDecode (hL : L.Ok) {g : Clif.Function} (hg : g ∈ L.P.funcs) {u : Arm.ArmState}
    {i : MInst} {info : CallInfo} (hi : i = .call info ∨ ∃ ti, i = .tryCall info ti)
    (hS : (L.A g).vcp.CallSite info) {ops : Array Operand} {regs : Array Reg} {i' : MInst}
    (hops : i.operands = .ok ops) {cc : CheckCtx} {wh : String}
    (hst : cc.checkStatic wh ops (regs.map .reg) i.clobbers = .ok ())
    (hasg : i.assign regs = .ok i') (hpi : CallAt (L.A g).fa (L.A g).base (Arm.r .PC u) i')
    (himgU : ∀ a, L.Img a → u.mem a = L.imgMem a)
    (hgd : gotGuard (GotV (L.A g).vcp) L.Xb info (useVals ops regs u))
    {h : Clif.Function} (hh : h ∈ L.P.funcs) {args : List CV}
    (hd : callDest info = some h.name ∧ useVals ops regs u = args ∨
      callDest info = none ∧ L.IndTo g h ∧
        ∃ u0, useVals ops regs u = u0 :: args ∧ lo64 u0 = L.Xb.sym h.name 0)
    (hlen : args.length = (regLocs h.sig).length) :
    ∃ Lu : List (Nat × Reg), Lu.map (·.2) = regLocs h.sig ∧
      args = Lu.map (fun q => regVal u q.2) ∧ L.CallsTo g u h ∧ RaOk (L.A h) (Arm.r .PC u) := by
  obtain ⟨hops0, ic, hasg0, hpi0⟩ := call_of_callLike hi hops hasg hpi
  obtain ⟨hsz', hloc, -, -⟩ := checkStatic_facts hst
  have hpf : L.P.func? h.name = some h := func?_of_mem hL.names hh
  obtain ⟨x, hins, hx⟩ := L.insnAt_callAt hL hg hpi0
  rcases hd with ⟨hdn, huse⟩ | ⟨hdn, hto, u0, huse, hlo⟩
  · -- a direct call of `h`
    have hdest : info.dest = .sym h.name := by
      unfold callDest at hdn
      split at hdn
      · rename_i n e; cases hdn; exact e
      · cases hdn
    have hsite : L.ProgSite g info h := ⟨hS, h.name, hdest, hpf⟩
    obtain ⟨n', Lu, Ld, hinfo, hLu, -⟩ := hL.callRegs g hg info h hsite
    subst hinfo
    cases hdest
    rw [operands_call_sym] at hops0
    cases hops0
    have hregs := callRegs_eq (regs := regs) (by simpa using hsz')
      (fun p hp r hr => (hloc p hp).2 r hr)
    rw [call_useVals hregs] at huse
    obtain ⟨us', ds', he⟩ := assign_call_sym hasg0
    injection he with he
    subst he
    simp only [MInst.callInsn?, Option.some.injEq] at hx
    subst hx
    exact ⟨Lu, hLu, huse.symm, .inl ⟨h.name, hins, hpf⟩,
      hL.raCall g hg _ h hsite _ hpi0.callPc⟩
  · -- a call through a register holding `h`'s address
    have hreg : ∀ n, info.dest ≠ .sym n := by
      intro n e
      unfold callDest at hdn
      rw [e] at hdn
      cases hdn
    obtain ⟨tv, Lu, Ld, rfl, hregs⟩ := hL.blrRegs g hg info hS hreg
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
    have huv := call_useVals_reg (tv := tv) (s := u) hregs0
    rw [huv] at huse hgd
    simp only [List.cons.injEq] at huse
    obtain ⟨rfl, rfl⟩ := huse
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
    have hs : symCallee L.Xb L.P (lo64 (regVal u (.x n0))) = some h := by
      show L.P.funcs.find? (fun h' => L.Xb.sym h'.name 0 == lo64 (regVal u (.x n0))) = some h
      rw [hlo]; exact (L.find_sym hL h.name).1 h hpf
    have hgot : ∀ n, GotV (L.A g).vcp tv n → n = h.name := by
      intro n hn
      have e := hgd tv n _ rfl hn (operands_call_reg tv Lu Ld) (by simp [tgtOp, Operand.isUse])
      simp only [List.head?_cons, Option.map_some, Option.some.injEq] at e
      exact L.got_target hL hs e
    obtain ⟨hLu, -⟩ := hregs h hh ⟨hto, hgot⟩ (by rw [← hlen, List.length_map])
    simp only [MInst.callInsn?, Option.some.injEq] at hx
    subst hx
    exact ⟨Lu, hLu, rfl, .inr ⟨⟨_, hins⟩, by rw [htgt]; exact hs⟩,
      hL.raBlr g hg _ hS hreg h hh hto.1 _ hpi0.callPc⟩

end LinkSys

end E2E
