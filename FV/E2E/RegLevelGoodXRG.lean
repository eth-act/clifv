import FV.E2E.RegLevelCorrectR

/-!
# Per-state facts with the guarded call premise (#753, stage R3')

The per-state facts of the activation's run (`RL.GoodX`, `actGoodX`) state the callee contract's
premise at a `bl`/`blr` line as a step of the unguarded `csemV` (`RL.CallPre`). The linking layer
needs the guarded step there (a `blr` enters a function only with its registers, `RegGuard`): the
register-guarded world theorems keep it in their per-state facts with:

* `RL.CallPreR P`: `RL.CallPre` with the step of `csemVR P` (`CallPreR.toCallPre` forgets the guard);
* `ExtSem.noCall`, `RL.noCall`: the external semantics without calls (the machine step, the symbol
  addresses, `RL.Wf` and the realisation relation `Q` are those of `R`, `RL.noCall_step`,
  `RL.Wf.noCall`, `Q.noCall`); at `R.noCall` no call step is defined, so a `GoodX` state of
  `R.noCall` is at no call line (`RL.noCall_callPre`);
* `RL.GoodXR P`: a `GoodX` state of `R.noCall` (a state of a step that is no call), or a `GoodX`
  state of `R` with `CallPreR P` (the state of a call); `RL.GoodXR.toGoodX`, and at a call line the
  guarded premise holds (`RL.GoodXR.callR`);
* `actGoodXR P`: `actGoodX` with `GoodXR` (`RL.GoodXR.act`, `actGoodXR.toX`, `actGoodXR.callR`).
-/

namespace Backend.Proof

open Backend E2E

set_option autoImplicit false

/-- **The external semantics `X` without calls** (every call undefined). -/
def ExtSem.noCall (X : ExtSem) : ExtSem := { X with call := fun _ _ _ => none }

/-- **The activation `R` with an external semantics that makes no call.** -/
def RL.noCall (R : RL) : RL := { R with X := R.X.noCall }

theorem RL.noCall_step (R : RL) : R.noCall.step = R.step := rfl

theorem RL.Wf.noCall {R : RL} (h : R.Wf) : R.noCall.Wf :=
  ⟨h.check, h.alloc, h.emit, h.layout, h.lm, h.fit, h.stack, h.psF, h.prog0, h.gfree, h.leaf⟩

theorem StRel.noCall {R : RL} {s : Arm.ArmState} {m : Loc → CV} {w : Arm.ArmState}
    (h : StRel R s m w) : StRel R.noCall s m w :=
  ⟨h.store, h.world, h.err, h.prog, h.sp, h.align, h.fplr, h.code, h.gkeep, h.fp⟩

theorem StRel.ofNoCall {R : RL} {s : Arm.ArmState} {m : Loc → CV} {w : Arm.ArmState}
    (h : StRel R.noCall s m w) : StRel R s m w :=
  ⟨h.store, h.world, h.err, h.prog, h.sp, h.align, h.fplr, h.code, h.gkeep, h.fp⟩

theorem Qs.noCall {R : RL} {s : Arm.ArmState} {b : Nat} {its : List RItem} {m : Loc → CV}
    {w : Arm.ArmState} (h : Qs R s b its m w) : Qs R.noCall s b its m w := by
  obtain ⟨j, vb, items, pre, code, X, ps1, psm, ps2, x, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    hst, h12, h13⟩ := h
  exact ⟨j, vb, items, pre, code, X, ps1, psm, ps2, x, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    hst.noCall, h12, h13⟩

theorem Qs.ofNoCall {R : RL} {s : Arm.ArmState} {b : Nat} {its : List RItem} {m : Loc → CV}
    {w : Arm.ArmState} (h : Qs R.noCall s b its m w) : Qs R s b its m w := by
  obtain ⟨j, vb, items, pre, code, X, ps1, psm, ps2, x, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    hst, h12, h13⟩ := h
  exact ⟨j, vb, items, pre, code, X, ps1, psm, ps2, x, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    hst.ofNoCall, h12, h13⟩

theorem QE.noCall {R : RL} {s : Arm.ArmState} {m : Loc → CV} {w : Arm.ArmState} {b : Nat}
    (h : QE R s m w b) : QE R.noCall s m w b := by
  induction h with
  | std h1 h2 => exact .std h1 h2.noCall
  | fwd h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 _ ih => exact .fwd h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 ih

theorem QE.ofNoCall {R : RL} {s : Arm.ArmState} {m : Loc → CV} {w : Arm.ArmState} {b : Nat}
    (h : QE R.noCall s m w b) : QE R s m w b := by
  induction h with
  | std h1 h2 => exact .std h1 h2.ofNoCall
  | fwd h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 _ ih => exact .fwd h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 ih

theorem Q.noCall {R : RL} {s : Arm.ArmState} {c : MConf CV Arm.ArmState} (h : Q R s c) :
    Q R.noCall s c := by
  cases c with
  | run vs =>
    obtain ⟨b, its, m, w⟩ := vs
    rcases h with h | ⟨items, h1, h2, h3⟩
    · exact .inl h.noCall
    · exact .inr ⟨items, h1, h2, h3.noCall⟩
  | _ => trivial

theorem Q.ofNoCall {R : RL} {s : Arm.ArmState} {c : MConf CV Arm.ArmState} (h : Q R.noCall s c) :
    Q R s c := by
  cases c with
  | run vs =>
    obtain ⟨b, its, m, w⟩ := vs
    rcases h with h | ⟨items, h1, h2, h3⟩
    · exact .inl h.ofNoCall
    · exact .inr ⟨items, h1, h2, h3.ofNoCall⟩
  | _ => trivial

theorem AInv.noCall {R : RL} {c : MConf CV Arm.ArmState} (h : AInv R c) : AInv R.noCall c := h

theorem AInv.ofNoCall {R : RL} {c : MConf CV Arm.ArmState} (h : AInv R.noCall c) : AInv R c := h

theorem QA.noCall {R : RL} {s : Arm.ArmState} {c : MConf CV Arm.ArmState} (h : QA R s c) :
    QA R.noCall s c := by
  rcases h with ⟨h1, h2⟩ | h
  · exact .inl ⟨h1.noCall, h2⟩
  · refine .inr ?_
    cases c with
    | run vs =>
      obtain ⟨b, its, m, w⟩ := vs
      obtain ⟨mt, D, h1, h2, h3⟩ := h
      exact ⟨mt, D, h1.noCall, h2, h3⟩
    | _ => exact h

theorem QA.ofNoCall {R : RL} {s : Arm.ArmState} {c : MConf CV Arm.ArmState} (h : QA R.noCall s c) :
    QA R s c := by
  rcases h with ⟨h1, h2⟩ | h
  · exact .inl ⟨h1.ofNoCall, h2⟩
  · refine .inr ?_
    cases c with
    | run vs =>
      obtain ⟨b, its, m, w⟩ := vs
      obtain ⟨mt, D, h1, h2, h3⟩ := h
      exact ⟨mt, D, h1.ofNoCall, h2, h3⟩
    | _ => exact h

/-- `TlsOk` reads the symbols, the thread pointer and the flags of `X`, not its calls. -/
theorem TlsOk.noCall {F : BitVec 64 → Prop} {K : Nat} {X : ExtSem} {H : ArmHooks}
    (h : TlsOk F K X H) : TlsOk F K X.noCall H :=
  ⟨h.pc, h.seq, h.flags⟩

/-- Off the calls, the semantics of `R.noCall` is that of `R`. -/
theorem RL.noCall_sem {R : RL} {i : MInst} (hc : ∀ info, i ≠ .call info)
    (ht : ∀ info ti, i ≠ .tryCall info ti) : R.noCall.sem i = R.sem i := by
  funext uses w
  rw [RL.sem_eq _ hc ht, RL.sem_eq _ hc ht]
  cases i <;> first | rfl | exact absurd rfl (hc _) | exact absurd rfl (ht _ _)

/-- At `R.noCall` no call or `try_call` step is defined. -/
theorem RL.noCall_sem_call {R : RL} {i : MInst} {uses : List CV} {w : Arm.ArmState}
    {r : List CV × Arm.ArmState × Ctl} (h : R.noCall.sem i uses w = some r) :
    (∀ info, i ≠ .call info) ∧ ∀ info ti, i ≠ .tryCall info ti := by
  have h' := R.noCall.sem_csem h
  refine ⟨fun info e => ?_, fun info ti e => ?_⟩ <;> subst e <;>
    simp [csem, RL.noCall, ExtSem.noCall] at h'

/-- **A step of `R.noCall` is the step of the guarded semantics wherever that one is defined**
(`MStep.guardLift`'s premise for lifting a realisation at `R.noCall`). -/
theorem RL.noCall_le {R : RL} {P : BitVec 64 → Clif.Signature → Prop} :
    ∀ i us w r r', regG P R.sem i us w = some r → R.noCall.sem i us w = some r' →
      regG P R.sem i us w = some r' := by
  intro i us w r r' h h'
  obtain ⟨hc, ht⟩ := RL.noCall_sem_call h'
  rw [regG_of (regG_inv h).1, ← RL.noCall_sem hc ht]
  exact h'

/-- At `R.noCall` the callee contract's premise never holds. -/
theorem RL.noCall_callPre {R : RL} {u : Arm.ArmState} : ¬ R.noCall.CallPre u := by
  rintro ⟨ctx, i, ctl, ⟨info, -, hi⟩, -, -, -, c, wh, ops, regs, i', w, outs, w', -, -, -, -, -, -,
    -, hsem⟩
  have h' := csemV_sub hsem
  rcases hi with rfl | ⟨ti, rfl⟩ <;> simp [csem, RL.noCall, ExtSem.noCall] at h'

/-- A `GoodX` state of `R.noCall` is one of `R`. -/
theorem RL.GoodX.ofNoCall {R : RL} {u : Arm.ArmState} (h : R.noCall.GoodX u) : R.GoodX u :=
  ⟨h.good, h.err, h.prog, h.line, h.next, h.got, h.blr,
    fun x hx hc => absurd (h.call x hx hc) RL.noCall_callPre, h.reads⟩

/-- **The callee contract's premise with the guarded step** (`RL.CallPre` at `csemVR P`). -/
def RL.CallPreR (P : BitVec 64 → Clif.Signature → Prop) (R : RL) (u : Arm.ArmState) : Prop :=
  ∃ (ctx : FnCtx) (i : MInst) (ctl : Ctl),
    (∃ info : CallInfo, (∃ (b : Nat) (vb : VBlock) (k : Nat), R.vc.blocks[b]? = some vb ∧
        (vb.insts[k]? = some (MInst.call info) ∨ ∃ ti, vb.insts[k]? = some (MInst.tryCall info ti))) ∧
      (i = .call info ∨ ∃ ti, i = .tryCall info ti)) ∧
    R.K ≤ (spOf u).toNat ∧ (∀ a, StackBelow R.K (spOf u) a → R.F a) ∧
    (∀ a, R.G a → u.mem a = R.s0.mem a) ∧
    ∃ (c : CheckCtx) (wh : String) (ops : Array Operand) (regs : Array Reg) (i' : MInst)
      (w : Arm.ArmState) (outs : List CV) (w' : Arm.ArmState),
      i.operands = .ok ops ∧ c.checkStatic wh ops (regs.map .reg) i.clobbers = .ok () ∧
      i.assign regs = .ok i' ∧ CallAt R.fa R.base (Arm.r .PC u) i' ∧
      SameWorld R.F u w ∧ Arm.CheckSPAlignment u ∧ Arm.r .ERR u = .None ∧
      csemVR P R.gv R.F ctx R.X i (useVals ops regs u) w = some (outs, w', ctl)

theorem RL.CallPreR.toCallPre {P : BitVec 64 → Clif.Signature → Prop} {R : RL} {u : Arm.ArmState}
    (h : R.CallPreR P u) : R.CallPre u := by
  obtain ⟨ctx, i, ctl, hi, h1, h2, h3, c, wh, ops, regs, i', w, outs, w', h4, h5, h6, h7, h8, h9,
    h10, hsem⟩ := h
  exact ⟨ctx, i, ctl, hi, h1, h2, h3, c, wh, ops, regs, i', w, outs, w', h4, h5, h6, h7, h8, h9,
    h10, regG_sub hsem⟩

/-- **The per-state facts with the guarded call premise**: a `GoodX` state of `R.noCall` (no call
line), or a `GoodX` state of `R` where the callee contract's premise holds with the guarded step. -/
def RL.GoodXR (P : BitVec 64 → Clif.Signature → Prop) (R : RL) (u : Arm.ArmState) : Prop :=
  R.noCall.GoodX u ∨ (R.GoodX u ∧ R.CallPreR P u)

theorem RL.GoodXR.toGoodX {P : BitVec 64 → Clif.Signature → Prop} {R : RL} {u : Arm.ArmState}
    (h : R.GoodXR P u) : R.GoodX u := by
  rcases h with h | ⟨h, -⟩
  · exact h.ofNoCall
  · exact h

/-- **At a call line, the guarded premise holds.** -/
theorem RL.GoodXR.callR {P : BitVec 64 → Clif.Signature → Prop} {R : RL} {u : Arm.ArmState}
    (h : R.GoodXR P u) {x : Insn} (hx : R.AtLine u x) (hc : (∃ n, x = .bl n) ∨ ∃ r, x = .blr r) :
    R.CallPreR P u := by
  rcases h with h | ⟨-, h⟩
  · exact absurd (h.call x hx hc) RL.noCall_callPre
  · exact h

/-- **`actGoodX` with the guarded call premise.** -/
def actGoodXR (P : BitVec 64 → Clif.Signature → Prop) (vc : VCode) (rf : RFunc) (af : AFunc)
    (fa : FnAsm) (fb : FnBin) (base : BitVec 64) (s0 : Arm.ArmState) (X : ExtSem) (H : ArmHooks)
    (K : Nat) (G : BitVec 64 → Prop) (gv : Nat → String → Prop) (u : Arm.ArmState) : Prop :=
  RL.GoodXR P ⟨vc, rf, af, fa, fb, {}, base, s0, X, H, {}, K, G, gv⟩ u

theorem RL.GoodXR.act {P : BitVec 64 → Clif.Signature → Prop} {R : RL} {u : Arm.ArmState}
    (h : R.GoodXR P u) :
    actGoodXR P R.vc R.rf R.af R.fa R.fb R.base R.s0 R.X R.H R.K R.G R.gv u := by
  rcases h with h | ⟨h, hp⟩
  · exact .inl h.act
  · refine .inr ⟨h.act, ?_⟩
    obtain ⟨ctx, i, ctl, hi, h1, h2, h3, c, wh, ops, regs, i', w, outs, w', h4, h5, h6, h7, h8, h9,
      h10, hsem⟩ := hp
    exact ⟨ctx, i, ctl, hi, h1, h2, h3, c, wh, ops, regs, i', w, outs, w', h4, h5, h6, h7, h8, h9,
      h10, hsem⟩

section
variable {P : BitVec 64 → Clif.Signature → Prop} {vc : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
  {fb : FnBin} {base : BitVec 64} {s0 : Arm.ArmState} {X : ExtSem} {H : ArmHooks} {K : Nat}
  {G : BitVec 64 → Prop} {gv : Nat → String → Prop} {u : Arm.ArmState}

theorem actGoodXR.toX (h : actGoodXR P vc rf af fa fb base s0 X H K G gv u) :
    actGoodX vc rf af fa fb base s0 X H K G gv u :=
  RL.GoodXR.toGoodX h

/-- **At a call line of a state with `actGoodXR`, the guarded premise holds.** -/
theorem actGoodXR.callR (h : actGoodXR P vc rf af fa fb base s0 X H K G gv u) {x : Insn}
    (hx : (⟨vc, rf, af, fa, fb, {}, base, s0, X, H, {}, K, G, gv⟩ : RL).AtLine u x)
    (hc : (∃ n, x = .bl n) ∨ ∃ r, x = .blr r) :
    (⟨vc, rf, af, fa, fb, {}, base, s0, X, H, {}, K, G, gv⟩ : RL).CallPreR P u :=
  RL.GoodXR.callR h hx hc

/-- **Code without call sites**: its `actGoodX` states have `actGoodXR` (no `CallPre` exists). -/
theorem actGoodXR.of_noCallSites (h : actGoodX vc rf af fa fb base s0 X H K G gv u)
    (hnc : NoCallSites vc) : actGoodXR P vc rf af fa fb base s0 X H K G gv u := by
  have hg : RL.GoodX (⟨vc, rf, af, fa, fb, {}, base, s0, X, H, {}, K, G, gv⟩ : RL) u := h
  refine .inl ⟨hg.good, hg.err, hg.prog, hg.line, hg.next, hg.got, hg.blr, fun x hx hc => ?_,
    hg.reads⟩
  obtain ⟨-, -, -, ⟨info, ⟨b, vb, k, hvb, hk⟩, -⟩, -⟩ := hg.call x hx hc
  exact absurd ⟨b, vb, k, hvb, hk⟩ (hnc info)

end

end Backend.Proof
