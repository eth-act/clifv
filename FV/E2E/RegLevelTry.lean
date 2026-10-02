import FV.E2E.RegLevelGoto
import FV.E2E.RegLevelCall

/-!
# The call of a `try_call` on the machine (M6)

The allocated `tryCall` runs as `bl name` / `blr xn` (the hooked callee, `H.call`), then
`b continuation` (dropped by `fallthrough` when the continuation is the next block). Only the
normal return is covered: `csem` continues at the normal-return successor.

* `CalleeTryOk F X H S`: the def clause of the callee contract for the call of a `try_call`: on a
  normal return the def registers hold the values `csem` gives them — the results (as
  `CalleeOk.os` says of a call), then the exception payload registers that are not return
  registers (x0/x1 after fewer than two results), as the callee's world `X.call` says. It is
  the only callee assumption beyond `CalleeOk` (`os_tryCall`).
* `realizes_tryCall`: the `op`/`goto` case of `Realizes` for `tryCall`.
-/

namespace Backend.Proof

open Backend E2E

/-- **The callee contract of a `try_call`'s call** beyond `CalleeOk` (a normal return): the
hooked callee leaves in the call's def registers the values `csem` gives them — the results,
then the exception payload registers that are not return registers, as the callee's world
says, for the call sites `S`. -/
def CalleeTryOk (F : BitVec 64 → Prop) (X : ExtSem) (H : ArmHooks) (S : CallInfo → Prop) : Prop :=
  ∀ (ctx : FnCtx) (info : CallInfo) (ti : TryInfo), S info → ∀ (c : CheckCtx) (wh : String)
    (ops : Array Operand) (regs : Array Reg) (i' : MInst) (s w : Arm.ArmState) (outs : List CV)
    (w' : Arm.ArmState),
    (MInst.tryCall info ti).operands = .ok ops →
    c.checkStatic wh ops (regs.map .reg) (MInst.tryCall info ti).clobbers = .ok () →
    (MInst.tryCall info ti).assign regs = .ok i' →
    SameWorld F s w → Arm.CheckSPAlignment s → Arm.r .ERR s = .None →
    csem F ctx X (.tryCall info ti) (useVals ops regs s) w =
      some (outs, w', .goto ti.handlers.length) →
    ∃ s', callExec H i' s = some s' ∧ ∀ p ∈ defRegs ops regs outs, regVal s' p.1.2 = p.2

theorem hasTryCall_of_mem {vc : VCode} {b k : Nat} {vb : VBlock} {info : CallInfo} {ti : TryInfo}
    (hvb : vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some (.tryCall info ti)) :
    vc.hasTryCall = true := by
  simp only [VCode.hasTryCall, Array.any_eq_true]
  obtain ⟨hb, rfl⟩ := Array.getElem?_eq_some_iff.mp hvb
  obtain ⟨hk, hk'⟩ := Array.getElem?_eq_some_iff.mp hi
  exact ⟨b, hb, k, hk, by rw [hk']⟩

theorem clobbers_tryCall {info : CallInfo} {ti : TryInfo} (h : ti.clobberAll = false) :
    (MInst.tryCall info ti).clobbers = (MInst.call info).clobbers := by
  simp [MInst.clobbers, h]

/-- **`CallSoundCtl` of the call of a `try_call`** (control: the normal-return successor), from
the callee contract of calls and `CalleeTryOk`. -/
theorem os_tryCall {F : BitVec 64 → Prop} {K : Nat} {X : ExtSem} {H : ArmHooks}
    {S : CallInfo → Prop} (hC : CalleeOk F K X H S) (hT : CalleeTryOk F X H S) (ctx : FnCtx)
    (info : CallInfo) {ti : TryInfo} (hS : S info) (hcl : ti.clobberAll = false) :
    CallSoundCtl F K (callExec H) (csem F ctx X) (.tryCall info ti) (.goto ti.handlers.length) := by
  intro s hK hD c wh ops regs i' w outs w' hops hst hasg hw hal herr hsem
  obtain ⟨ic, rfl, hasg'⟩ := (assign_call_tryCall info regs).2 ti i' hasg
  have hsem0 := hsem
  simp only [csem, Option.map_eq_some_iff] at hsem0
  obtain ⟨⟨xo, w2⟩, hx, he⟩ := hsem0
  simp only [Prod.mk.injEq] at he
  obtain ⟨-, rfl, -⟩ := he
  have hsemc : csem F ctx X (.call info) (useVals ops regs s) w = some (xo, w2, .next) := by
    simp [csem, hx]
  obtain ⟨s', hex, hW, hK, -, hoth, hkeep⟩ := hC.os ctx info hS s hK hD c wh ops regs (.call ic) w xo
    w2 (by rw [← operands_tryCall_call info ti]; exact hops) (by rw [← clobbers_tryCall hcl]; exact hst)
    hasg' hw hal herr hsemc
  obtain ⟨s'', hex', hdef⟩ := hT ctx info ti hS c wh ops regs (.tryCall ic ti) s w outs w2 hops hst
    hasg hw hal herr hsem
  have hss : s'' = s' := by
    simp only [callExec, if_pos hal, Option.some.injEq] at hex hex'
    rw [← hex, ← hex']
  subst hss
  exact ⟨s'', hex', hW, hK, hdef, fun r ha hnd hnc => hoth r ha hnd (by rw [← clobbers_tryCall hcl]; exact hnc),
    fun r hr hcs => hkeep r (by rw [clobbers_tryCall hcl] at hr; exact hr) hcs⟩

/-- **The call of a `try_call` on the machine**: from `Q` at a `tryCall` item, the machine runs
the hooked callee and the branch to the normal-return successor, reaching `Q` at that
successor's items (an `MStep` of the allocated code). -/
theorem realizes_tryCall {R : RL} (hR : R.Wf) (hC : CalleeOk R.F R.K R.X R.H R.vc.CallSite)
    (hT : CalleeTryOk R.F R.X R.H R.vc.CallSite) {s : Arm.ArmState} {b k : Nat} {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩))
    {vb : VBlock} {info : CallInfo} {ti : TryInfo} {ops : Array Operand} {outs : List CV}
    {w' : Arm.ArmState} {ctl : Ctl}
    (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some (.tryCall info ti))
    (hops : (MInst.tryCall info ti).operands = .ok ops) (hsz : allocs.size = ops.size)
    (hsem : R.sem (.tryCall info ti) (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w =
      some (outs, w', ctl))
    (hlen : outs.length = ((ops.zip allocs).toList.filter (·.1.isDef)).length)
    {j st : Nat} {items : Array RItem} (hk1 : k + 1 = vb.insts.size)
    (hsucc : succOf R.vc b j = some st) (hitems : R.rf.blocks[st]? = some items)
    (hctl : ctl = .goto j) :
    ∃ n c'', MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c'' ∧
      Q R (iterN R.step n s) c'' := by
  have hck := (lowerRFunc_ok hR.alloc).2.2.2
  obtain ⟨j0, vb0, items0, pre, code, ls, ps1, ps2, T, hvb0, hit, hsplit, hchk, hcode, hls, htr,
    hdrop, hpc, hst⟩ := hq
  rw [hvb] at hvb0; cases hvb0
  obtain ⟨c1, c2, hc1, hc2, rfl⟩ := itemsCode_cons hcode
  obtain ⟨regs, i0, i', rfl, hi0, hasg, hc1'⟩ := itemCode_op hc1
  rw [hi] at hi0; cases hi0
  obtain ⟨cc, wh, i2, ops2, hi2, hops2, hstat, hchk'⟩ := op_checked hchk
  rw [hi] at hi2; cases hi2
  rw [hops] at hops2; cases hops2
  -- the control outcome and the callee's world
  have hsem0 := hsem
  simp only [RL.sem, csem, Option.map_eq_some_iff] at hsem0
  obtain ⟨⟨xo, w2⟩, hx, he⟩ := hsem0
  simp only [Prod.mk.injEq] at he
  obtain ⟨-, rfl, rfl⟩ := he
  obtain rfl : j = ti.handlers.length := by cases hctl; rfl
  have herr : Arm.r .ERR w = .None := by
    rw [← hst.world.1 .ERR (by simp [Masked]), hst.err]
  have hW' : Arm.r .ERR w2 = .None ∧ w2.program = w.program := hC.ext _ _ _ _ _ hx herr
  -- the instruction's effect
  have hcl : ti.clobberAll = false := by
    have := ctlCheck_inst hck hvb hi
    simpa [ctlInstOk] using this
  have hm : ∀ r, r.allocatable = true → m (.reg r) = regVal s r := fun r hr =>
    hst.store (.reg r) (fun r' e => by cases e; exact hr) trivial
  obtain ⟨s', m2, hex, hW, hK, hc2', hr2, hl2⟩ := operandsSound_stepAt
    (RL.callAt hR (os_tryCall hC hT R.ctx info ⟨b, vb, k, hvb, .inr ⟨ti, hi⟩⟩ hcl) hst.sp) hops hstat hasg hm hst.world hst.align
    hst.err hsem hlen
  obtain ⟨ic, rfl, -⟩ := (assign_call_tryCall info regs).2 ti i' hasg
  -- the successor's label
  obtain ⟨c, ins, hc⟩ := checked_of_checkAlloc hR.check
  obtain ⟨preds, hcfg⟩ := hc.cfg
  obtain ⟨t0, ts, hback, hss, hlab⟩ := cfg_block hcfg hvb
  have hti : t0 = .tryCall info ti := by
    rw [Array.back?_eq_getElem?, show vb.insts.size - 1 = k by omega, hi] at hback
    cases hback; rfl
  subst hti
  have hsucc' := hsucc
  simp only [succOf, hcfg, hss, Option.bind_some] at hsucc'
  obtain ⟨vs, hvs, hlj⟩ := hlab _ st hsucc'
  have hst0 : st ≠ 0 := ctlCheck_succ hck hsucc
  have hcont : vs.label = ti.continuation := by
    simp only [MInst.targets] at hlj
    rw [List.getElem?_append_right (by simp), List.length_map, Nat.sub_self] at hlj
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hlj
    exact hlj.symm
  -- the lines: the call, then `b continuation`
  obtain rfl : c1 = [.inst (.tryCall ic ti)] := by
    rcases hc1' with ⟨h, -, -⟩ | ⟨_, h, -⟩ | ⟨_, h, -⟩
    · exact h
    · cases h
    · cases h
  obtain ⟨ls1, ls2, psm, h1, h2, rfl⟩ := codeLinesE_append _ _ _ _ _ hls
  have hl1 := codeLinesE_single h1
  obtain ⟨x, hxl, hxs, hplain⟩ : ∃ x : Insn, ls1 = [.ins x, .ins (.b (.block ti.continuation))] ∧
      (∀ s0 : Arm.ArmState, ∀ jj, R.L[jj]? = some (.ins x) → s0.program = R.fb.program R.base →
        Arm.r .PC s0 = R.pcOf jj → R.step s0 = R.H.call
          (match ic.dest with | .sym n => some n | .reg _ => none) s0) ∧
      (Line.ins x none).plain = true := by
    cases hd : ic.dest with
    | sym n =>
      simp only [MInst.lines, hd, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hl1
      refine ⟨.bl n, hl1.1.symm, fun s0 jj hj hprog hpc0 => ?_, by simp [Line.plain, Insn.condTarget?]⟩
      exact step_bl (off := 0) (r := .xzr) (rd := .xzr) (rn := .xzr) hR hj hprog hpc0
    | reg r =>
      simp only [MInst.lines, hd, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hl1
      refine ⟨.blr r, hl1.1.symm, fun s0 jj hj hprog hpc0 => ?_, by simp [Line.plain, Insn.condTarget?]⟩
      exact step_blr (off := 0) (n := "") (rd := .xzr) (rn := .xzr) hR hj hprog hpc0
  subst hxl
  have hZ : ∀ n, (Line.ins (.b (.block ti.continuation)) none :: (ls2 ++ nxtOf R.af b))[1]? ≠
      some (.label (.trap n)) := by
    intro n e
    simp only [List.getElem?_cons_succ] at e
    have hm := List.mem_of_getElem? e
    rcases List.mem_append.1 hm with hm | hm
    · exact codeLinesE_noTrap _ _ _ _ h2 _ hm n rfl
    · simp only [nxtOf] at hm
      split at hm <;> simp at hm
  have hdrop' : R.L.drop j0 = Line.ins x none ::
      (ftList (.ins (.b (.block ti.continuation)) none :: (ls2 ++ nxtOf R.af b)) ++ T) := by
    rw [hdrop, List.append_assoc]
    rw [show [Line.ins x, .ins (.b (.block ti.continuation))] ++ (ls2 ++ nxtOf R.af b) =
      [Line.ins x none] ++ (.ins (.b (.block ti.continuation)) none :: (ls2 ++ nxtOf R.af b)) from rfl,
      ftList_plain_append _ _ (by simpa using hplain) hZ]
    rfl
  have hj0 : R.L[j0]? = some (.ins x none) := drop_get (Z := []) hdrop'
  -- the machine: the callee, then `b continuation`
  have hs1 : R.step s = s' := by
    rw [hxs s j0 hj0 hst.prog hpc]
    simp only [callExec, if_pos hst.align, Option.some.injEq] at hex
    exact hex
  have herr' : Arm.r .ERR s' = .None := by rw [hW.1 .ERR (by simp [Masked]), hW'.1]
  have hprog' : s'.program = R.fb.program R.base := by
    rw [hW.2.2, hW'.2, ← hst.world.2.2, hst.prog]
  have hpc1 : Arm.r .PC s' = R.pcOf (j0 + 1) := by
    rw [← hs1, hxs s j0 hj0 hst.prog hpc, hC.pc _ _ hst.err hst.align, hpc, pcOf_succ hj0]
  have hdrop1 : R.L.drop (j0 + 1) =
      ftList (.ins (.b (.block ti.continuation)) none :: (ls2 ++ nxtOf R.af b)) ++ T := by
    rw [← List.drop_drop, hdrop']; rfl
  obtain ⟨n, jl, hn, hjl⟩ := reach_b hR hdrop1 hprog' hpc1 herr'
  refine ⟨n + 1, _, MStep.op hvb hi hops hsz hsem hlen (HavocOuts.refl _ _) hc2'
    (MNext.goto hk1 hsucc hitems), ?_⟩
  have hiter : iterN R.step (n + 1) s = Arm.w .PC (R.pcOf jl) s' := by
    simp only [iterN]; rw [hs1, hn]
  rw [hiter]
  have hfr := R.frameOkK hR
  have hsp' : spOf s' = R.spB := hK.1.trans hst.sp
  have hstr : StRel R s' (writeM m2 ((((ops.zip (regs.map Loc.reg)).toList.filter (·.1.isDef)).zip
      outs).filter (·.1.1.isLate))) w2 := by
    refine ⟨fun l hl hL => ?_, hW, herr', hprog', hsp', align_of_sp (by rw [hsp', hst.sp]) hst.align,
      fun hframe => ?_, code_keep hR.prog0 hst.code fun a ha => hK.2 a (.inr (.inr ha))⟩
    · cases l with
      | reg r => exact hr2 r (hl r rfl)
      | stack k' c =>
        rw [hl2 _ (fun r h => by cases h), hst.store _ hl hL,
          locVal_frame_keep hfr hst.sp hK hL (fun r h => by cases h)]
      | save r =>
        rw [hl2 _ (fun r h => by cases h), hst.store _ hl hL,
          locVal_frame_keep hfr hst.sp hK hL (fun r h => by cases h)]
    · rw [← hst.fplr hframe]
      exact read_mem_bytes_congr _ _ (fun k hk => hK.2 _ (fplr_inF hR hframe k hk))
  exact q_entry hR hst0 hvs hitems (by rw [hjl, hcont]) (Arm.r_of_w_same ..) (hstr.pc _)

end Backend.Proof
