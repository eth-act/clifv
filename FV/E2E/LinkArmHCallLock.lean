import FV.E2E.LinkArmHCall
import FV.E2E.BackendTwoRunLW
import FV.E2E.RegLevelTwoRunTP

/-!
# The call premise of the two-run lock at the link (SEM1 #537, #713, step 4)

`backend_twoRunLERWZIUPF_either`'s `hcall`: at a `bl`/`blr` line of a segment of the first run
(the segment start, `RL.SegFrom.call`: the first run's call-`n` state with the body's `sp`) and a
second state locked with it by `R.Zc c c'`, the call hook keeps the lock. The first state's
`GoodX.call` gives the callee contract's premise `CallPre`: the call's `csemV` answer of
`XPBTGY … .at n` (so `n < N`), which `Stage2ZS` (`XPBTGY_subZS`) turns into `XPRBT … n`'s; then
`hookLock_callS` (a `call`, or the call of a `try_call`). The line's destination is the call's
(`callDest_of_line`), the lock set is inside `F` and avoids the callees' dead stack, the second
state holds the code image (its own `GoodX.call`, `MachEntry.imgG`/`imgS`).

* `csemV_call_of_tryCall`, `callDest_of_line`;
* **`hookLock_pre`** (`hookLock_callS` from `CallPre`'s data, `call` or `try_call`);
* **`hcallLockXP`** (the premise `hcall` at `XI := XPBTGY` with the canonical prophecies).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- **A `try_call`'s answer gives its plain call's.** -/
theorem csemV_call_of_tryCall {gv : Nat → String → Prop} {F : BitVec 64 → Prop} {ctx : FnCtx}
    {X : ExtSem} {info : CallInfo} {ti : TryInfo} {uses : List CV} {w : Arm.ArmState}
    {r : List CV × Arm.ArmState × Ctl} (h : csemV gv F ctx X (.tryCall info ti) uses w = some r) :
    ∃ xo w2, csemV gv F ctx X (.call info) uses w = some (xo, w2, .next) := by
  have hg := csemV_guard_try h
  have h0 := csemV_sub h
  simp only [csem, Option.map_eq_some_iff, Option.filter_eq_some_iff] at h0
  obtain ⟨⟨xo, w2⟩, ⟨hx, -⟩, -⟩ := h0
  exact ⟨xo, w2, by simp only [csemV, hg, ↓reduceIte]; simp [csem, hx]⟩

namespace LinkSys

variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

/-- **The destination of a call line is the call's** (`bl n` of a call of `n`, `blr` of a call
through a register). -/
theorem callDest_of_line (hL : L.Ok) {g : Clif.Function} (hg : g ∈ L.P.funcs) {info : CallInfo}
    (hsite : (L.A g).vcp.CallSite info) {regs : Array Reg} {i' : MInst}
    (hasg : (MInst.call info).assign regs = .ok i') {x : Insn} (hx : i'.callInsn? = some x)
    {d : Option String} (hld : LineDest x d) : d = callDest info := by
  cases hdi : info.dest with
  | sym nm =>
    obtain ⟨d0, us, ds⟩ := info
    simp only at hdi
    subst hdi
    obtain ⟨us', ds', rfl⟩ := assign_call_sym hasg
    simp only [MInst.callInsn?, Option.some.injEq] at hx
    subst hx
    rcases hld with ⟨m, hm, rfl⟩ | ⟨r, hr, -⟩
    · cases hm; rfl
    · cases hr
  | reg r =>
    obtain ⟨tv, Lu, Ld, rfl, -⟩ := hL.blrRegs g hg info hsite (fun n => by rw [hdi]; simp)
    obtain ⟨r0, us', ds', -, rfl⟩ := assign_call_reg hasg
    simp only [MInst.callInsn?, Option.some.injEq] at hx
    subst hx
    rcases hld with ⟨m, hm, -⟩ | ⟨r', -, rfl⟩
    · cases hm
    · rfl

/-- **The call hook keeps a lock at a call (`call`, or the call of a `try_call`) of the first
run's call-`n` state**, from `XPRBT … n`'s answer (`hookLock_callS`). -/
theorem hookLock_pre (hL : L.Ok) (hκ : L.Budget κ) {M : Nat} (hcl : L.CallLock κ M)
    {F : BitVec 64 → Prop} (hN : HookNIX L.Hb L.BaseDest F)
    {g : Clif.Function} (hg : g ∈ L.P.funcs) {G : BitVec 64 → Prop} {s0 : Arm.ArmState}
    (himgF : ∀ a, L.Img a → F a) (himgG : ∀ a, L.Img a → G a)
    (himgS : ∀ a, L.Img a → s0.mem a = L.imgMem a)
    {info : CallInfo} (hsite : (L.A g).vcp.CallSite info) {i : MInst}
    (hi : i = .call info ∨ ∃ ti, i = .tryCall info ti) (ctx : FnCtx) {ctl : Ctl}
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {n : Nat}
    {t t' : Arm.ArmState}
    (hmskQ : ∀ f, MaskedReg f → Arm.r f t = Arm.r f (R n))
    (hrgnQ : ∀ a, StackBelow (κ M g) (spv t) a → t.mem a = P n a)
    {c : CheckCtx} {wh : String} {ops : Array Operand} {regs : Array Reg} {i' : MInst}
    {w : Arm.ArmState} {outs : List CV} {w' : Arm.ArmState}
    (hops : i.operands = .ok ops)
    (hst : c.checkStatic wh ops (regs.map .reg) i.clobbers = .ok ())
    (hasg : i.assign regs = .ok i')
    (hP : CallAt (L.A g).fa (L.A g).base (Arm.r .PC t) i') (hsw : SameWorld F t w)
    (hG : ∀ a, G a → t.mem a = s0.mem a)
    (hsem : csemV (GotV (L.A g).vcp) F ctx (L.XPRBT κ M g F P R n) i
      (useVals ops regs t) w = some (outs, w', ctl))
    {Z : BitVec 64 → Prop} (hZ : StEqOutX Z t t') (hZF : ∀ a, Z a → F a)
    (hZd : ∀ a, StackBelow (κ M g) (spv t) a → ¬ Z a)
    (himgt' : ∀ a, L.Img a → t'.mem a = L.imgMem a) :
    StEqOutX Z ((L.hooks M).call (callDest info) t) ((L.hooks M).call (callDest info) t') := by
  rcases hi with rfl | ⟨ti, rfl⟩
  · have hc : ctl = .next := by
      have h0 := csemV_sub hsem
      simp only [csem, Option.map_eq_some_iff, Prod.mk.injEq] at h0
      obtain ⟨_, -, -, -, h⟩ := h0
      exact h.symm
    subst hc
    exact L.hookLock_callS hL hκ hcl hN hg himgF himgG himgS hsite ctx hmskQ hrgnQ hops ⟨_, hst⟩
      hasg hP hsw hG hsem hZ hZF hZd himgt'
  · obtain ⟨xo, w2, hsemC⟩ := csemV_call_of_tryCall hsem
    obtain ⟨ic, rfl, hasg'⟩ := (assign_call_tryCall info regs).2 ti i' hasg
    exact L.hookLock_callS hL hκ hcl hN hg himgF himgG himgS hsite ctx hmskQ hrgnQ
      (by rw [← operands_tryCall_call info ti]; exact hops) ⟨_, hst⟩ hasg'
      (callAt_tryCall_call hP) hsw hG hsemC hZ hZF hZd himgt'

set_option maxHeartbeats 4000000 in
/-- **The call premise of the two-run lock at the link** (module doc): `hcall` of
`backend_twoRunLERWZIUPF_either` for the activation of `g` with `XI := XPBTGY` at the canonical
prophecies, the call hook of depth `M` (`CallLock κ M`), the second entry `t0` a `MachEntry`, and
the base hooks not observing `F` (`HookNIX`). -/
theorem hcallLockXP (hL : L.Ok) (hκ : L.Budget κ) {M : Nat} (hcl : L.CallLock κ M)
    {g : Clif.Function} (hg : g ∈ L.P.funcs) {F G G' D : BitVec 64 → Prop} {ra ra' : BitVec 64}
    {s w₀ t0 w₀' : Arm.ArmState}
    (hME : L.MachEntryPR κ M g F G ra s w₀ (L.BP M g s) (L.RP M g s))
    (he' : L.MachEntry κ M g F G' ra' t0 w₀') (hD : ∀ a, D a → F a)
    (hN : HookNIX L.Hb L.BaseDest F) {env : Clif.Env} {cs : Clif.State}
    (h2 : ∀ n, L.Stage2ZS κ M g F (L.BP M g s) (L.RP M g s) env cs (spv w₀)
      (L.CallStPRB κ M g s w₀ n) n)
    {XI : ExtSemI} (hXI : XI = L.XPBTGY κ M g F (L.BP M g s) (L.RP M g s) env cs (spv w₀))
    {lm : Std.HashMap Lbl Nat} {psF : PState} {R : RL}
    (hR : R = Backend.Proof.actRL (L.A g).vcp (L.A g).rf (L.A g).af (L.A g).fa (L.A g).fb lm
      (L.A g).base s XI
      (L.hooks M) psF (κ M g) G (GotV (L.A g).vcp)) :
    ∀ N n n' c c' i u u', ({ R with X := (XI.upTo N).at n } : RL).InSeg (OkDiff F c c') c i u →
      ({ R with X := (XI.upTo N).at n } : RL).SegFrom (fun u =>
        OnCall ({ R with X := (XI.upTo N).at 0 } : RL).step R.fa R.base R.s0 n u ∧
          spOf u = R.spB) c i u →
      ({ R with s0 := t0, G := G', X := (XI.upTo N).at n' } : RL).InSeg (OkDiff F c c') c' i u' →
      ({ R with X := (XI.upTo N).at n } : RL).GoodX u →
      ({ R with s0 := t0, G := G', X := (XI.upTo N).at n' } : RL).GoodX u' →
      StEqOutX (R.Zc c c') u u' → (∀ a, MConf.WDiff c c' a → F a ∨ D a) →
      ∀ x d, ({ R with X := (XI.upTo N).at n } : RL).AtLine u x → LineDest x d →
      StEqOutX (R.Zc c c') ((L.hooks M).call d u) ((L.hooks M).call d u') := by
  intro N n n' c c' i u u' _ hsf _ hgx hgx' hz hwd x d hat hld
  subst hR hXI
  have hF : frameWG (κ M g) (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase
      (RAFrame.compute (L.A g).vcp (L.A g).rf).size (L.A g).af G s = F := hME.entryP.entry.hF
  have hbl : (∃ m, x = .bl m) ∨ ∃ r, x = .blr r := by
    rcases hld with ⟨m, rfl, -⟩ | ⟨r, rfl, -⟩
    · exact .inl ⟨m, rfl⟩
    · exact .inr ⟨r, rfl⟩
  have hcs := RL.callSt_iff.mpr ⟨x, hat, hbl⟩
  obtain ⟨-, hon, hsp⟩ := hsf.call hcs
  have hmach : ArmStepX (((L.XPBTGY κ M g F (L.BP M g s) (L.RP M g s) env cs (spv w₀)).upTo N).at 0)
      (L.hooks M) (L.A g).fa = L.mach M g := armStepX_congr_sym rfl _ _
  have hon' : OnCall (L.mach M g) (L.A g).fa (L.A g).base s n u := by
    rw [← hmach]; exact hon
  have hspu : spv u = spv s - BitVec.ofNat 64 (frameDrop (L.A g).af) := hsp
  have hcsP : L.CallStPRB κ M g s w₀ n u := ⟨onCallPR_of hME.entryP.proph hME.reg hon', hsp⟩
  have hpc : CallPc (L.A g).fa (L.A g).base (Arm.r .PC u) := hcs
  obtain ⟨hmskQ, hrgnQ⟩ := L.callStPRB_q hME.entryP.entry.body.sp n u hcsP hpc
  obtain ⟨ctx, i0, ctl, ⟨info, hsite, hi⟩, -, -, hG, cc, wh, ops, regs, i', w, outs, w', hops, hst,
    hasg, hP, hsw, hal, herr, hsem⟩ := hgx.call x hat hbl
  have hsw' : SameWorld F u w := by rw [← hF]; exact hsw
  have hsem1 : csemV (GotV (L.A g).vcp) F ctx
      (((L.XPBTGY κ M g F (L.BP M g s) (L.RP M g s) env cs (spv w₀)).upTo N).at n) i0
      (useVals ops regs u) w = some (outs, w', ctl) :=
    Eq.rec (motive := fun Y _ => csemV (GotV (L.A g).vcp) Y ctx
      (((L.XPBTGY κ M g F (L.BP M g s) (L.RP M g s) env cs (spv w₀)).upTo N).at n) i0
      (useVals ops regs u) w = some (outs, w', ctl)) hsem hF
  have hn : n < N := by
    refine Classical.byContradiction fun hge => ?_
    rw [ExtSemI.upTo_at_ge _ (by omega)] at hsem1
    have hic : i0.isCallI = true := by rcases hi with rfl | ⟨ti, rfl⟩ <;> rfl
    rw [csemV_noCall_call hic] at hsem1
    cases hsem1
  rw [ExtSemI.upTo_at_lt _ hn] at hsem1
  have hsemX : csemV (GotV (L.A g).vcp) F ctx (L.XPRBT κ M g F (L.BP M g s) (L.RP M g s) n) i0
      (useVals ops regs u) w = some (outs, w', ctl) :=
    csemV_of_call_subAtG (X := L.XPRBT κ M g F (L.BP M g s) (L.RP M g s) n)
      ((L.XPBTGY κ M g F (L.BP M g s) (L.RP M g s) env cs (spv w₀)).at n).call hi
      (fun hgd r hr => L.XPBTGY_subZS hL (h2 n) u w hcsP hsw' i0 info hi hsite ops regs i' hops cc
        wh hst hasg hP hal herr hgd r hr) hsem1
  -- the second state holds the code image
  have himgt' : ∀ a, L.Img a → u'.mem a = L.imgMem a := by
    have hpc' : Arm.r .PC u' = Arm.r .PC u := (hz.1 .PC (by decide)).symm
    obtain ⟨j, tt, hj, hp⟩ := hat
    obtain ⟨-, -, -, -, -, -, hG', -⟩ := hgx'.call x ⟨j, tt, hj, hpc'.trans hp⟩ hbl
    exact fun a ha => (hG' a (he'.imgG a ha)).trans (he'.imgS a ha)
  -- the lock set is inside `F` and avoids the callees' dead stack
  have hZF : ∀ a, RL.Zc (Backend.Proof.actRL (L.A g).vcp (L.A g).rf (L.A g).af (L.A g).fa (L.A g).fb lm
      (L.A g).base s (L.XPBTGY κ M g F (L.BP M g s) (L.RP M g s) env cs (spv w₀)) (L.hooks M) psF
      (κ M g) G (GotV (L.A g).vcp)) c c' a → F a := by
    intro a ⟨_, _, _, h⟩
    rcases h with hf | hw
    · rw [← hF]; exact hf
    · exact (hwd a hw).elim id (hD a)
  have hZd : ∀ a, StackBelow (κ M g) (spv u) a → ¬ RL.Zc (Backend.Proof.actRL (L.A g).vcp (L.A g).rf (L.A g).af
      (L.A g).fa (L.A g).fb lm (L.A g).base s
      (L.XPBTGY κ M g F (L.BP M g s) (L.RP M g s) env cs (spv w₀)) (L.hooks M) psF (κ M g) G
      (GotV (L.A g).vcp)) c c' a := by
    intro a ha hzz
    rw [hspu] at ha
    exact hzz.2.2.1 ha
  -- the line's destination is the call's
  have hd : d = callDest info := by
    have hc := hL.compiled g hg
    obtain ⟨lm', hlm'⟩ := FnAsm.layout_labelOffsets hc.layout
    have hfit : 4 * (L.A g).fb.words.size ≤ 2 ^ 64 := by have := hL.fits g hg; omega
    obtain ⟨j, tt, hj, hp⟩ := hat
    obtain ⟨j', x', tt', hj', hx', hp'⟩ := hP
    have hpj : Arm.r .PC u = (L.A g).base + BitVec.ofNat 64 (lineOffset (L.A g).fa.lines.toList j) :=
      hp
    have e1 : insnAt (L.A g).fa (progBase u) (Arm.r .PC u) = some x := by
      rw [hpj]; exact insnAt_ofLine hc.layout hlm' hfit hgx.prog hj
    have e2 : insnAt (L.A g).fa (progBase u) (Arm.r .PC u) = some x' := by
      rw [hp']; exact insnAt_ofLine hc.layout hlm' hfit hgx.prog hj'
    rw [e1] at e2
    cases e2
    rcases hi with rfl | ⟨ti, rfl⟩
    · exact L.callDest_of_line hL hg hsite hasg hx' hld
    · obtain ⟨ic, rfl, hasg'⟩ := (assign_call_tryCall info regs).2 ti i' hasg
      exact L.callDest_of_line hL hg hsite hasg' hx' hld
  rw [hd]
  exact L.hookLock_pre hL hκ hcl hN hg hME.entryP.entry.imgF hME.entryP.entry.imgG
    hME.entryP.entry.imgS hsite hi ctx hmskQ hrgnQ hops hst hasg hP hsw' hG hsemX hz hZF hZd
    himgt'

end LinkSys

end E2E
