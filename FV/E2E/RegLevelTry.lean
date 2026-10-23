import FV.E2E.RegLevelGoto
import FV.E2E.RegLevelCall

/-!
# The call of a `try_call` on the machine (M6)

The allocated `tryCall` runs as `bl name` / `blr xn` (the hooked callee, `H.call`), then
`b continuation` (dropped by `fallthrough` when the continuation is the next block). Only the
normal return is covered: `csem` continues at the normal-return successor.

The call's defs are its results, then the exception payload registers that are not return
registers (x0/x1 after fewer than two results, `gen_try_call_rets`); the latter are dead on the
normal return (the allocated-code semantics havocs them, `havocFrom`, and the regalloc checker
forgets them on that edge, `CheckCtx.edgeForget`), so the callee may leave anything there.

* `VCode.TrySite vc info ti`: the `try_call` call sites of `vc` (`info` with its `TryInfo`).
* `CalleeTryOk F X H S`: the def clause of the callee contract for the call of a `try_call` at
  the sites `S`: on a normal return its results (the first `ti.rets` defs) hold the values
  `csem` gives them. It is the only callee assumption beyond `CalleeOk`, which already says so
  of the results the callee's world `X.call` returns (`calleeTryOk_of_rets0`: vacuous at sites
  without results).
* `realizes_tryCall`: the `op`/`goto` case of `Realizes` for `tryCall`.
-/

namespace Backend.Proof

open Backend E2E

/-- The `try_call` call sites of `vc`: a `tryCall info ti` in one of its blocks. -/
def _root_.Backend.VCode.TrySite (vc : VCode) (info : CallInfo) (ti : TryInfo) : Prop :=
  ∃ (b : Nat) (vb : VBlock) (k : Nat), vc.blocks[b]? = some vb ∧
    vb.insts[k]? = some (MInst.tryCall info ti)

/-- **The callee contract of a `try_call`'s call** beyond `CalleeOk` (a normal return), for the
sites `S`: the hooked callee leaves in the call's result registers (the first `ti.rets` defs)
the values `csem` gives them. The exception payload registers past them are unconstrained. -/
def CalleeTryOk (F : BitVec 64 → Prop) (X : ExtSem) (H : ArmHooks)
    (S : CallInfo → TryInfo → Prop) : Prop :=
  ∀ (ctx : FnCtx) (info : CallInfo) (ti : TryInfo), S info ti → ∀ (c : CheckCtx) (wh : String)
    (ops : Array Operand) (regs : Array Reg) (i' : MInst) (s w : Arm.ArmState) (outs : List CV)
    (w' s' : Arm.ArmState),
    (MInst.tryCall info ti).operands = .ok ops →
    c.checkStatic wh ops (regs.map .reg) (MInst.tryCall info ti).clobbers = .ok () →
    (MInst.tryCall info ti).assign regs = .ok i' →
    SameWorld F s w → Arm.CheckSPAlignment s → Arm.r .ERR s = .None →
    csem F ctx X (.tryCall info ti) (useVals ops regs s) w =
      some (outs, w', .goto ti.handlers.length) →
    callExec H i' s = some s' →
    ∀ p ∈ (defRegs ops regs outs).take ti.rets, regVal s' p.1.2 = p.2

/-- `CalleeTryOk` at the states a calling activation reaches (as `CallSoundCtlG`): the callees'
`K`-byte dead stack below `sp` fits and lies in `F`, the addresses `G` the activation keeps hold
what they held at its entry `s0`, the pc is a call instruction (`Pc`), and the call is one the
VCode run reaches (`csemV gv`). A linked callee runs the code it finds in memory, so its contract
needs the kept code image. -/
def CalleeTryOkG (F : BitVec 64 → Prop) (K : Nat) (G : BitVec 64 → Prop) (s0 : Arm.ArmState)
    (Pc : BitVec 64 → MInst → Prop) (X : ExtSem) (H : ArmHooks) (S : CallInfo → TryInfo → Prop)
    (gv : Nat → String → Prop) : Prop :=
  ∀ (ctx : FnCtx) (info : CallInfo) (ti : TryInfo), S info ti → ∀ (c : CheckCtx) (wh : String)
    (ops : Array Operand) (regs : Array Reg) (i' : MInst) (s w : Arm.ArmState) (outs : List CV)
    (w' s' : Arm.ArmState),
    K ≤ (spOf s).toNat → (∀ a, StackBelow K (spOf s) a → F a) →
    (∀ a, G a → s.mem a = s0.mem a) →
    (MInst.tryCall info ti).operands = .ok ops →
    c.checkStatic wh ops (regs.map .reg) (MInst.tryCall info ti).clobbers = .ok () →
    (MInst.tryCall info ti).assign regs = .ok i' → Pc (Arm.r .PC s) i' →
    SameWorld F s w → Arm.CheckSPAlignment s → Arm.r .ERR s = .None →
    csemV gv F ctx X (.tryCall info ti) (useVals ops regs s) w =
      some (outs, w', .goto ti.handlers.length) →
    callExec H i' s = some s' →
    ∀ p ∈ (defRegs ops regs outs).take ti.rets, regVal s' p.1.2 = p.2

theorem CalleeTryOk.g {F : BitVec 64 → Prop} {X : ExtSem} {H : ArmHooks}
    {S : CallInfo → TryInfo → Prop} (h : CalleeTryOk F X H S) (K : Nat) (G : BitVec 64 → Prop)
    (s0 : Arm.ArmState) (Pc : BitVec 64 → MInst → Prop) (gv : Nat → String → Prop) :
    CalleeTryOkG F K G s0 Pc X H S gv :=
  fun ctx info ti hS c wh ops regs i' s w outs w' s' _ _ _ hops hst hasg _ hw hal herr hsem =>
    h ctx info ti hS c wh ops regs i' s w outs w' s' hops hst hasg hw hal herr (csemV_sub hsem)

/-- At `try_call` sites without results (`ti.rets = 0`: the callee returns nothing, its defs
are the exception payload registers only), `CalleeTryOk` holds for every callee. -/
theorem calleeTryOk_of_rets0 {F : BitVec 64 → Prop} {X : ExtSem} {H : ArmHooks}
    {S : CallInfo → TryInfo → Prop} (h : ∀ info ti, S info ti → ti.rets = 0) :
    CalleeTryOk F X H S := by
  intro _ info ti hS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p hp
  rw [h info ti hS, List.take_zero] at hp
  cases hp

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

theorem mem_zip_map_self {α β : Type} (f : α → β) :
    ∀ (L : List α) (p : α × β), p ∈ L.zip (L.map f) → p.2 = f p.1
  | [], _, h => by simp at h
  | a :: L, p, h => by
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at h
    rcases h with rfl | h
    · rfl
    · exact mem_zip_map_self f L p h

/-- The values the machine leaves in the def registers agree with `outs` on the first `n` defs
when every one of those def registers holds its value of `outs`. -/
theorem take_machine_defs {ops : Array Operand} {regs : Array Reg} {outs : List CV}
    {s' : Arm.ArmState} {n : Nat}
    (hlen : outs.length = ((ops.zip regs).toList.filter (·.1.isDef)).length)
    (h : ∀ p ∈ (defRegs ops regs outs).take n, regVal s' p.1.2 = p.2) :
    (((ops.zip regs).toList.filter (·.1.isDef)).map (fun p => regVal s' p.2)).take n =
      outs.take n := by
  apply List.ext_getElem?
  intro k
  simp only [List.getElem?_take]
  split
  · rename_i hk
    rw [List.getElem?_map]
    cases hD : ((ops.zip regs).toList.filter (·.1.isDef))[k]? with
    | none =>
      have : outs[k]? = none := by
        rw [List.getElem?_eq_none_iff] at hD ⊢; omega
      rw [this]; rfl
    | some d =>
      obtain ⟨o, ho⟩ : ∃ o, outs[k]? = some o := by
        have : k < outs.length := by
          rw [hlen]; exact (List.getElem?_eq_some_iff.mp hD).1
        exact ⟨outs[k], List.getElem?_eq_getElem this⟩
      rw [ho]
      have hm : (d, o) ∈ (defRegs ops regs outs).take n := by
        apply List.mem_of_getElem? (i := k)
        rw [List.getElem?_take]
        simp only [hk, ↓reduceIte]
        rw [defRegs, List.getElem?_zip_eq_some]
        exact ⟨hD, ho⟩
      simp [h _ hm]
  · rfl

/-- A `try_call`'s allocated form is at the pc where its plain call's is (the same `bl`/`blr`). -/
theorem callAt_tryCall_call {fa : FnAsm} {base pc : BitVec 64} {ic : CallInfo} {ti : TryInfo}
    (h : CallAt fa base pc (.tryCall ic ti)) : CallAt fa base pc (.call ic) := h

/-- **The call of a `try_call` on the machine**: from `Q` at a `tryCall` item, the machine runs
the hooked callee and the branch to the normal-return successor, reaching `Q` at that
successor's items (an `MStep` of the allocated code, whose exception payload defs take the
values the callee left in their registers), every state before it satisfying `GoodX`. (`q_entry`
now takes a `RepL` for the successor's label, which `reach_jumpX` provides from the branch
check's `termOk_tryCall`; the old label-line argument is gone with `ftList`.) -/
theorem realizes_tryCall {R : RL} (hR : R.Wf) (hC : CalleeOkG R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H R.vc.CallSite R.gv)
    (hT : CalleeTryOkG R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H R.vc.TrySite R.gv) {s : Arm.ArmState} {b k : Nat} {allocs : Array Loc}
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
      Q R (iterN R.step n s) c'' ∧ ∀ i < n, R.GoodX (iterN R.step i s) := by
  have hck := (lowerRFunc_ok hR.alloc).2.2
  have hcpc := callAt_of_q hR hq hvb hi tryCall_hcall
  rcases Q.cases hq with hqs | ⟨vbf, allocsf, regsf, if_, xf, bx, hvbf, he, hits, half, hins, hasgf,
    hsuccf, itx, hitx, hqx⟩
  rotate_left
  · -- a forwarding block: its `jump` takes no machine step, but a `try_call`'s allocated form
    -- is no `jump`
    rw [hvb] at hvbf
    cases hvbf
    simp only [RItem.op.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    subst hits
    have hi1 := hi
    rw [hins] at hi1
    simp only [List.getElem?_toArray, List.getElem?_cons_zero, Option.some.injEq] at hi1
    subst hi1
    obtain ⟨ic, e, -⟩ := (assign_call_tryCall info regsf).2 ti (.jump xf) hasgf
    cases e
  obtain ⟨_, vb0, _, _, code, _, _, _, _, _, hvb0, -, -, hchk0, hcode, -⟩ := id hqs
  rw [hvb] at hvb0; cases hvb0
  obtain rfl : its = [] := hchk0.tail_nil hk1
  obtain ⟨j0, vb0, items, pre, c1, X, ps1, psm, ps2, x, hvb0, hit, hsplit, hchk, hc1, hX, hTq, htr,
    hdrop, hpc, hst, hterm⟩ := qs_term hR hqs
  rw [hvb] at hvb0; cases hvb0
  obtain ⟨regs, i0, i', rfl, hi0, hasg, hc1'⟩ := itemCode_op hc1
  rw [hi] at hi0; cases hi0
  obtain ⟨cc, wh, i2, ops2, hi2, hops2, hstat, -⟩ := op_checked hchk
  rw [hi] at hi2; cases hi2
  rw [hops] at hops2; cases hops2
  have hm : ∀ r, r.allocatable = true → m (.reg r) = regVal s r := fun r hr =>
    hst.store (.reg r) (fun r' e => by cases e; exact hr) trivial
  have hsemU := hsem
  rw [useVals_of_store hstat hm] at hsemU
  -- the callee contract's premise at the call state
  have hpre : R.CallPre s := ⟨R.ctx, .tryCall info ti, ctl,
    ⟨info, ⟨b, vb, k, hvb, .inr ⟨ti, hi⟩⟩, .inr ⟨ti, rfl⟩⟩,
    by rw [hst.sp]; exact RL.K_le hR, fun a ha => by rw [hst.sp] at ha; exact RL.below_F ha,
    hst.gkeep, cc, wh, ops, regs, i', w, outs, w', hops, hstat, hasg, hcpc regs i' rfl hasg,
    hst.world, hst.align, hst.err, hsemU⟩
  -- the control outcome and the callee's world
  have hsem0 := hsemU
  replace hsem0 := R.sem_csem hsem0
  simp only [csem, Option.map_eq_some_iff, Option.filter_eq_some_iff] at hsem0
  obtain ⟨⟨xo, w2⟩, ⟨hx, -⟩, he⟩ := hsem0
  simp only [Prod.mk.injEq] at he
  obtain ⟨-, rfl, rfl⟩ := he
  obtain rfl : j = ti.handlers.length := by cases hctl; rfl
  have herr : Arm.r .ERR w = .None := by
    rw [← hst.world.1 .ERR (by simp [Masked]), hst.err]
  have hW' : Arm.r .ERR w2 = .None ∧ w2.program = w.program := hC.ext _ _ _ _ _ hx herr
  -- the instruction's effect: the callee contract of the plain call, then the results
  have hcl : ti.clobberAll = false := by
    have := ctlCheck_inst hck hvb hi
    simpa [ctlInstOk] using this
  have hcpcT := hcpc regs i' rfl hasg
  obtain ⟨ic, rfl, hasg'⟩ := (assign_call_tryCall info regs).2 ti i' hasg
  have hsemC : csemV R.gv R.F R.ctx R.X (.call info) (useVals ops regs s) w =
      some (xo, w2, .next) := by
    have hg := csemV_guard_try hsemU
    simp only [csemV, hg, ↓reduceIte]
    simp [csem, hx]
  obtain ⟨s', hex, hW, hK, -, hoth, hkeep⟩ :=
    RL.callAtG hR (hC.os R.ctx info ⟨b, vb, k, hvb, .inr ⟨ti, hi⟩⟩) hst.sp hst.gkeep
      (P := (· = .call ic)) (fun _ e => e ▸ callAt_tryCall_call hcpcT) cc wh ops regs (.call ic)
      w xo w2 (by rw [← operands_tryCall_call info ti]; exact hops)
      (by rw [← clobbers_tryCall hcl]; exact hstat) hasg' rfl hst.world hst.align hst.err hsemC
  have hexT : callExec R.H (.tryCall ic ti) s = some s' := by
    simp only [callExec] at hex ⊢; exact hex
  have hres := hT R.ctx info ti ⟨b, vb, k, hvb, hi⟩ cc wh ops regs (.tryCall ic ti) s w outs w2 s'
    (by rw [hst.sp]; exact RL.K_le hR) (fun a ha => by rw [hst.sp] at ha; exact RL.below_F ha)
    hst.gkeep hops hstat hasg hcpcT hst.world hst.align hst.err hsemU hexT
  -- the def values the allocated code writes: what the callee left in the def registers
  have hlenD : outs.length = ((ops.zip regs).toList.filter (·.1.isDef)).length := by
    rw [hlen, pairs_regs, List.filter_map, List.length_map]; rfl
  have hlen' : (((ops.zip regs).toList.filter (·.1.isDef)).map (fun p => regVal s' p.2)).length =
      ((ops.zip (regs.map Loc.reg)).toList.filter (·.1.isDef)).length := by
    rw [List.length_map, ← hlenD, hlen]
  have hho : HavocOuts (MInst.tryCall ic ti) (.goto ti.handlers.length) outs
      (((ops.zip regs).toList.filter (·.1.isDef)).map (fun p => regVal s' p.2)) := by
    have hh : havocFrom (MInst.tryCall ic ti) (.goto ti.handlers.length) = some ti.rets := by
      simp [havocFrom, MInst.keptDefs, MInst.isBranch, MInst.normalDead]
    refine ⟨by rw [List.length_map, ← hlenD], fun h => (by rw [hh] at h; cases h), fun n h => ?_⟩
    rw [hh] at h; cases h
    exact take_machine_defs hlenD hres
  obtain ⟨m2, hc2', hr2, hl2⟩ := operandsSound_post (s' := s') hstat hm hlen'
    (fun p hp => (mem_zip_map_self _ _ p hp).symm)
    (fun r ha hnd hnc => hoth r ha hnd (by rw [← clobbers_tryCall hcl]; exact hnc))
    (fun r hr hcs => hkeep r (by rw [clobbers_tryCall hcl] at hr; exact hr) hcs)
  -- the successor's label
  obtain ⟨c, ins, _, hc, -⟩ := hR.check
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
  -- the lines: the call, then `b continuation` (the try_call's own lines, the segment's term)
  obtain rfl : c1 = [.inst (.tryCall ic ti)] := by
    rcases hc1' with ⟨h, -, -⟩ | ⟨_, h, -⟩ | ⟨_, h, -⟩
    · exact h
    · cases h
    · cases h
  simp only [List.dropLast_singleton, codeLinesE, bind, Except.bind, pure, Except.pure,
    Except.ok.injEq, Prod.mk.injEq] at hX
  obtain ⟨rfl, rfl⟩ := hX
  have hdrop0 : R.L.drop j0 = relaxLines R.far x.2.1 ++
      R.L.drop (rix R.far (planLines R.fa.k R.af) x.2.2) := by simpa using hdrop
  rw [show [AInst.inst (.tryCall ic ti)].getLast?.toList = [AInst.inst (.tryCall ic ti)] from by simp] at hTq
  have hlT := codeLinesE_single hTq
  obtain ⟨xI, hxterm, hxs, hplain, hxk⟩ : ∃ xI : Insn,
      x.1.term = [.ins xI none, .ins (.b (.block ti.continuation)) none] ∧
      (∀ s0 : Arm.ArmState, ∀ jj, R.L[jj]? = some (.ins xI) → s0.program = R.fb.program R.base →
        Arm.r .PC s0 = R.pcOf jj → R.step s0 = R.H.call
          (match ic.dest with | .sym n => some n | .reg _ => none) s0) ∧
      (Line.ins xI none).plain = true ∧
      ((∃ n, xI = .bl n) ∨ ∃ r, xI = .blr r ∧ (R.vc.DestsInt → r ≠ .xzr)) := by
    cases hd : ic.dest with
    | sym n =>
      simp only [MInst.lines, hd, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hlT
      refine ⟨.bl n, hlT.1.symm, fun s0 jj hj hprog hpc0 => ?_, by simp [Line.plain, Insn.condTarget?],
        .inl ⟨n, rfl⟩⟩
      exact step_bl (off := 0) (r := .xzr) (rd := .xzr) (rn := .xzr) hR hj hprog hpc0
    | reg r =>
      simp only [MInst.lines, hd, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hlT
      refine ⟨.blr r, hlT.1.symm, fun s0 jj hj hprog hpc0 => ?_, by simp [Line.plain, Insn.condTarget?],
        .inr ⟨r, rfl, fun hD => callDest_ne_xzr (hD b vb k info hvb (.inr ⟨ti, hi⟩)) hstat hasg' hd⟩⟩
      exact step_blr (off := 0) (n := "") (rd := .xzr) (rn := .xzr) hR hj hprog hpc0
  -- the branch check's verdict on the final lines
  obtain ⟨call, b0, htermL, hcase⟩ := termOk_tryCall hterm
  rw [hxterm] at htermL
  obtain ⟨rfl, rfl⟩ := htermL
  obtain ⟨O, hx21O, hcaseO⟩ : ∃ O, x.2.1 = .ins xI none :: O ∧
      ((∃ l', O = [.ins (.b l') none] ∧
          RepLbl (planRep R.fa.k R.af) (blockLabelIdx (planLines R.fa.k R.af)) ti.continuation l') ∨
        (O = [] ∧ planRep R.fa.k R.af ti.continuation x.2.2 = true)) := by
    rcases hcase with ⟨l', hx21, hrl⟩ | ⟨hx21, hrn⟩
    · exact ⟨[.ins (.b l') none], hx21.trans rfl, .inl ⟨l', rfl, hrl⟩⟩
    · exact ⟨[], hx21.trans rfl, .inr ⟨rfl, hrn⟩⟩
  have hj0 : R.L[j0]? = some (.ins xI none) :=
    drop_get (Z := relaxLines R.far O) (by
      rw [hdrop0, hx21O, relaxLines_cons,
        relaxLine_of_none (by rcases hxk with ⟨_, rfl⟩ | ⟨_, rfl, _⟩ <;> rfl),
        List.singleton_append])
  -- the machine: the callee, then the branch to the successor
  have hs1 : R.step s = s' := by
    rw [hxs s j0 hj0 hst.prog hpc]
    simp only [callExec, if_pos hst.align, Option.some.injEq] at hex
    exact hex
  have herr' : Arm.r .ERR s' = .None := by rw [hW.1 .ERR (by simp [Masked]), hW'.1]
  have hprog' : s'.program = R.fb.program R.base := by
    rw [hW.2.2, hW'.2, ← hst.world.2.2, hst.prog]
  have hpc1 : Arm.r .PC s' = R.pcOf (j0 + 1) := by
    rw [← hs1, hxs s j0 hj0 hst.prog hpc, hC.pc _ _ hst.err hst.align, hpc, pcOf_succ hj0]
  have hsp' : spOf s' = R.spB := hK.1.trans hst.sp
  have hdrop1 : R.L.drop (j0 + 1) = relaxLines R.far O ++
      R.L.drop (rix R.far (planLines R.fa.k R.af) x.2.2) := by
    rw [← List.drop_drop, hdrop0, hx21O, relaxLines_cons,
      relaxLine_of_none (by rcases hxk with ⟨_, rfl⟩ | ⟨_, rfl, _⟩ <;> rfl)]
    simp
  have hoo : (∃ l', O = [.ins (.b l') none] ∧
        RepLbl (planRep R.fa.k R.af) (blockLabelIdx (planLines R.fa.k R.af)) vs.label l') ∨
      (O = [] ∧ planRep R.fa.k R.af vs.label x.2.2 = true) := by
    rcases hcaseO with ⟨l', hO, hrl⟩ | ⟨hO, hrn⟩
    · exact .inl ⟨l', hO, by rw [hcont]; exact hrl⟩
    · exact .inr ⟨hO, by rw [hcont]; exact hrn⟩
  obtain ⟨n, jl, hn, hrep, -, hgx⟩ := reach_jumpX hR hdrop1 hoo hprog' hpc1 herr' hsp'
  refine ⟨n + 1, _, MStep.op hvb hi hops hsz hsem hlen hho hc2'
    (MNext.goto hk1 hsucc hitems), ?_, fun i hi => ?_⟩
  rotate_right
  · cases i with
    | zero =>
      show R.GoodX s
      exact RL.goodX_line hR hj0 hpc (by rcases hxk with ⟨_, rfl⟩ | ⟨_, rfl, _⟩ <;> rfl)
        (RL.good_of_sp hst.sp) hst.err hst.prog
        (RL.nextOk_pc4 (by rw [hs1, hpc1, pcOf_succ hj0, hpc]))
        (fun _ _ _ e => by rcases hxk with ⟨_, rfl⟩ | ⟨_, rfl, _⟩ <;> cases e)
        (fun r e => by
          rcases hxk with ⟨_, rfl⟩ | ⟨_, rfl, hr⟩
          · cases e
          · cases e; exact ⟨hr, hst.code⟩)
        (fun _ => hpre)
        (RL.readsAt_hooked hR hj0 hpc (by rcases hxk with ⟨_, rfl⟩ | ⟨_, rfl, _⟩ <;> rfl))
    | succ i =>
      simp only [iterN]; rw [hs1]
      exact hgx i (by omega)
  have hiter : iterN R.step (n + 1) s = Arm.w .PC (R.pcOf jl) s' := by
    simp only [iterN]; rw [hs1, hn]
  rw [hiter]
  have hfr := R.frameOkK hR
  have hstr : StRel R s' (writeM m2 ((((ops.zip (regs.map Loc.reg)).toList.filter (·.1.isDef)).zip
      (((ops.zip regs).toList.filter (·.1.isDef)).map (fun p => regVal s' p.2))).filter
        (·.1.1.isLate))) w2 := by
    refine ⟨fun l hl hL => ?_, hW, herr', hprog', hsp', align_of_sp (by rw [hsp', hst.sp]) hst.align,
      fun hframe => ?_, code_keep hR.prog0 hst.code fun a ha => hK.2 a (.inl (.inr (.inr ha))),
      fun a ha => (hK.2 a (.inr ha)).trans (hst.gkeep a ha)⟩
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
  exact q_entry hR hst0 hvs hitems hrep (Arm.r_of_w_same ..) (hstr.pc _)

/-- A `try_call` site of checked allocated code clobbers what a call clobbers. -/
theorem trySite_clobberAll {vc : VCode} {rf : RFunc} {af : AFunc} (halloc : lowerRFunc vc rf = .ok af)
    {info : CallInfo} {ti : TryInfo} (h : vc.TrySite info ti) : ti.clobberAll = false := by
  obtain ⟨b, vb, k, hvb, hi⟩ := h
  have := ctlCheck_inst (lowerRFunc_ok halloc).2.2 hvb hi
  simpa [ctlInstOk] using this

/-- A `try_call` site is a call site. -/
theorem _root_.Backend.VCode.TrySite.callSite {vc : VCode} {info : CallInfo} {ti : TryInfo}
    (h : vc.TrySite info ti) : vc.CallSite info := by
  obtain ⟨b, vb, k, hvb, hi⟩ := h
  exact ⟨b, vb, k, hvb, .inr ⟨ti, hi⟩⟩

/-- **A `try_call`'s results from the plain call's contract**, at one state: where the plain
call's contract holds (`CallSoundCtlG`), the results the machine's callee leaves are the ones
`csem` gives (`csem` defines a `try_call` only when `X.call` returns at least `ti.rets`
results). -/
theorem calleeTry_at {F : BitVec 64 → Prop} {K : Nat} {G : BitVec 64 → Prop}
    {s0 : Arm.ArmState} {Pc : BitVec 64 → MInst → Prop} {X : ExtSem} {H : ArmHooks}
    {ctx : FnCtx} {info : CallInfo} {ti : TryInfo} {gv : Nat → String → Prop}
    (hos : CallSoundCtlG F K G s0 Pc (callExec H) (csemV gv F ctx X) (.call info) .next)
    (hPc : ∀ pc ic, Pc pc (.tryCall ic ti) → Pc pc (.call ic))
    (hcl : ti.clobberAll = false)
    {c : CheckCtx} {wh : String} {ops : Array Operand} {regs : Array Reg} {i' : MInst}
    {s w : Arm.ArmState} {outs : List CV} {w' s' : Arm.ArmState}
    (hK : K ≤ (spOf s).toNat) (hD : ∀ a, StackBelow K (spOf s) a → F a)
    (hG : ∀ a, G a → s.mem a = s0.mem a)
    (hops : (MInst.tryCall info ti).operands = .ok ops)
    (hst : c.checkStatic wh ops (regs.map .reg) (MInst.tryCall info ti).clobbers = .ok ())
    (hasg : (MInst.tryCall info ti).assign regs = .ok i') (hP : Pc (Arm.r .PC s) i')
    (hsw : SameWorld F s w) (hal : Arm.CheckSPAlignment s) (herr : Arm.r .ERR s = .None)
    (hsem : csemV gv F ctx X (.tryCall info ti) (useVals ops regs s) w =
      some (outs, w', .goto ti.handlers.length))
    (hex : callExec H i' s = some s') :
    ∀ p ∈ (defRegs ops regs outs).take ti.rets, regVal s' p.1.2 = p.2 := by
  intro p hp
  obtain ⟨ic, rfl, hasg'⟩ := (assign_call_tryCall info regs).2 ti i' hasg
  have hsem0 := csemV_sub hsem
  simp only [csem, Option.map_eq_some_iff, Option.filter_eq_some_iff] at hsem0
  obtain ⟨⟨xo, w2⟩, ⟨hx, hr⟩, he⟩ := hsem0
  simp only [decide_eq_true_eq] at hr
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, -⟩ := he
  have hsemC : csemV gv F ctx X (.call info) (useVals ops regs s) w = some (xo, w2, .next) := by
    have hg := csemV_guard_try hsem
    simp only [csemV, hg, ↓reduceIte]
    simp [csem, hx]
  obtain ⟨s1, hex1, -, -, hd, -, -⟩ := hos s hK hD hG c wh ops regs (.call ic) w
    xo w2 (by rw [← operands_tryCall_call info ti]; exact hops)
    (by rw [← clobbers_tryCall hcl]; exact hst) hasg' (hPc _ _ hP) hsw hal herr hsemC
  have hs1 : s1 = s' := by
    simp only [callExec, hal, ↓reduceIte, Option.some.injEq] at hex hex1
    rw [← hex, ← hex1]
  subst hs1
  obtain ⟨a, b⟩ := p
  apply hd
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hp
  rw [List.getElem?_take] at hj
  split at hj
  · rename_i hjn
    rw [defRegs, List.getElem?_zip_eq_some] at hj
    rw [List.getElem?_append_left (by omega)] at hj
    exact List.mem_of_getElem? (by rw [defRegs, List.getElem?_zip_eq_some]; exact hj)
  · cases hj

/-- **`CalleeTryOkG` from the plain call's contract**: at `try_call` sites where the callee
contract of the plain call holds (`CallSoundCtlG`), the results the machine's callee leaves are
the ones `csem` gives. -/
theorem calleeTryOkG_of_call {F : BitVec 64 → Prop} {K : Nat} {G : BitVec 64 → Prop}
    {s0 : Arm.ArmState} {Pc : BitVec 64 → MInst → Prop} {X : ExtSem} {H : ArmHooks}
    {S : CallInfo → TryInfo → Prop} {gv : Nat → String → Prop}
    (hos : ∀ ctx info ti, S info ti →
      CallSoundCtlG F K G s0 Pc (callExec H) (csemV gv F ctx X) (.call info) .next)
    (hPc : ∀ pc ic ti, Pc pc (.tryCall ic ti) → Pc pc (.call ic))
    (hcl : ∀ info ti, S info ti → ti.clobberAll = false) :
    CalleeTryOkG F K G s0 Pc X H S gv := by
  intro ctx info ti hS c wh ops regs i' s w outs w' s' hK hD hG hops hst hasg hP hsw hal herr hsem
    hex
  exact calleeTry_at (hos ctx info ti hS) (fun pc ic => hPc pc ic ti) (hcl info ti hS) hK hD
    hG hops hst hasg hP hsw hal herr hsem hex

end Backend.Proof
