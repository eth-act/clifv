import FV.E2E.LinkArmStage2Z
import FV.E2E.LinkArmStage2ZS

/-!
# The call contracts with the register prophecy but `x30` (SEM1 #537, #713)

`calleeOkXPBTGZ` needs, at the call states `Q`, every masked register (`MaskedReg`, which
includes `x30`) equal to the register prophecy `R n`. The prefix two-run route (#713) supplies it
from the lock of two runs (`StEqOutX`), which leaves `x30` free: at a call state the two runs'
`x30` differ (the first run's is its own entry's return address before its first call, and in
general whatever its last call left). The answer of a program call (`progXPRBT`) does not read
`x30`: it enters the callee at `canon h uses W`, which agrees with the caller on the masked
registers but `x30` and the pc only (`progOsCorePRBRL`'s `hmsk`), and the arguments are in
argument registers, never `x30` (`argReg_ne29`). So the premise without `x30` suffices; same
proofs otherwise (new names, the old theorems kept):

* `progOsCoreXPRRBRL30`, `progOsPRBRL30`, `progOsRegPRBRL30`, **`calleeOkPRBRL30`**,
  **`calleeTryOkPRBRL30`**;
* **`calleeOkXPBTGZ30`**, **`calleeTryOkXPBTGZ30`**.

The `…30R` forms take the determinism premise `DetPRBR` (#719; the names without `R` are their
corollaries), and **`calleeOkXPBTGZS30R`**, **`calleeTryOkXPBTGZS30R`** are the contracts at the
call sites' operands (`Stage2ZS`, as `calleeOkXPBTGZSR`).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

namespace LinkSys

variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

/-- **`progOsCoreXPRRBRL` with the register prophecy but `x30`** (module doc). -/
theorem progOsCoreXPRRBRL30RU (hL : L.Ok) [hR : L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1))
    (hdet : 0 < M → L.DetPRBRU κ (M - 1)) {g h : Clif.Function}
    (hg : g ∈ L.P.funcs) (hh : h ∈ L.P.funcs)
    (hcal : L.Callee g h)
    {F G : BitVec 64 → Prop} {s0 : Arm.ArmState} (himgF : ∀ a, L.Img a → F a)
    (himgG : ∀ a, L.Img a → G a) (himgS : ∀ a, L.Img a → s0.mem a = L.imgMem a)
    {Lu : List (Nat × Reg)} {Ld : List (Reg × Nat)} (hLu : Lu.map (·.2) = regLocs h.sig)
    (hLd : (Ld.map (·.1)).take (sigRets h.sig).length =
      (List.range (min (sigRets h.sig).length Ld.length)).map Reg.x)
    {info : CallInfo} (hdefs0 : info.defs = callDefs Ld)
    {ops : Array Operand} {regs : Array Reg}
    (hdefs : ((ops.zip regs).toList.filter (·.1.isDef)) = (callDefOps Ld).zip (Ld.map (·.1)))
    {t w w' : Arm.ArmState} {o outs : List CV}
    (hK : κ M g ≤ (spOf t).toNat) (hG : ∀ a, G a → t.mem a = s0.mem a)
    (hra : RaOk (L.A h) (Arm.r .PC t))
    (hsw : SameWorld F t w)
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {n : Nat}
    (hmskQ : ∀ f, MaskedReg f → f ≠ .GPR 30#5 → Arm.r f t = Arm.r f (R n))
    (hrgnQ : ∀ a, StackBelow (κ M g) (spv t) a → t.mem a = P n a)
    (hx : L.progXPRBT κ M F h (Lu.map (fun q => regVal t q.2)) (P n) (R n) w = some (o, w'))
    (houts : ∃ n, outs = o.take n) :
    SameWorld F (L.pcall M h t) w' ∧
      FrameKeep (fun a => F a ∧ ¬ StackBelow (κ M g) (spOf t) a) t (L.pcall M h t) ∧
      (∀ p ∈ defRegs ops regs outs, regVal (L.pcall M h t) p.1.2 = p.2) ∧
      (∀ r, r.allocatable = true → (∀ p ∈ (ops.zip regs).toList, p.1.isDef = true → p.2 ≠ r) →
        r ∉ (MInst.call info).clobbers → regVal (L.pcall M h t) r = regVal t r) ∧
      (∀ r ∈ (MInst.call info).clobbers, r ∈ calleeSaved →
        ckeep r (regVal (L.pcall M h t) r) = ckeep r (regVal t r)) := by
  let W := L.worldPR κ M h (P n) (R n) w
  replace hx : L.progXBT κ M F h (Lu.map (fun q => regVal t q.2)) W = some (o, w') := hx
  obtain ⟨-, harg, -⟩ := hL.argRegs h hh
  have hcondW : L.CondBT κ M F h (Lu.map (fun q => regVal t q.2)) W := by
    have hx' := hx
    unfold progXBT at hx'
    exact Classical.byContradiction fun hc => by rw [if_neg (fun h' => hc h'.1)] at hx'; cases hx'
  obtain ⟨hM, -, -, -, hdeadW, -⟩ := hcondW
  have hspW : spv W = spv w :=
    L.r_worldPR_out (κ := κ) (M := M) h (P n) (R n) w (f := .GPR 31#5)
      (fun hm => by simp [MaskedReg, Masked] at hm)
  rw [hspW] at hdeadW
  have hst : spv t = spv w := hsw.1 _ (by simp [Masked])
  have hmaskedF : ∀ (r : Reg) (f : Arm.StateField), r.isArgReg = true → r.field = some f →
      MaskedReg f := by
    intro r f hr hf
    refine ⟨?_, (argReg_ne29 hr hf).2.2.2⟩
    cases r with
    | x k =>
      simp only [Reg.isArgReg, decide_eq_true_eq] at hr
      simp only [Reg.field, Option.some.injEq] at hf
      subst hf
      simp only [Masked, rnum_toNat (show k < 32 by omega)]
      omega
    | v k =>
      simp only [Reg.field, Option.some.injEq] at hf
      subst hf
      trivial
    | _ => simp [Reg.isArgReg] at hr
  have hargW : ∀ r ∈ regLocs h.sig, regVal t r = regVal W r := fun r hr =>
    regVal_eq_of_field (harg r hr) fun f hf => by
      have hm := hmaskedF r f (harg r hr) hf
      rw [hmskQ f hm (argReg_ne29 (harg r hr) hf).2.2.1, L.r_worldPR_in h (P n) w hm]
  have huses : Lu.map (fun q => regVal t q.2) = (regLocs h.sig).map (regVal W) := by
    rw [← hLu, List.map_map]
    exact List.map_congr_left fun q hq => hargW q.2 (by rw [← hLu]; exact List.mem_map_of_mem hq)
  have hmsk : ∀ f, Masked f → f ≠ .PC → f ≠ .GPR 30#5 →
      Arm.r f t = Arm.r f (L.canon h (Lu.map (fun q => regVal t q.2)) W) := by
    intro f hf hpc h30
    rw [huses, L.canon_self_r h W hpc, L.r_worldPR_in h (P n) w ⟨hf, hpc⟩, hmskQ f ⟨hf, hpc⟩ h30]
  have hrgn : ∀ a, StackBelow (frameDrop (L.A h).af + κ (M - 1) h) (spv W) a →
      t.mem a = (L.canon h (Lu.map (fun q => regVal t q.2)) W).mem a := by
    intro a ha
    rw [hspW] at ha
    have hFI := hdeadW a ha
    rw [L.mem_canon, mem_withImg, if_neg hFI.2, L.mem_worldPR, worldP,
      mem_overlay_in (show L.calleeRgn κ M h w a from ha)]
    exact hrgnQ a (stackBelow_mono (by rw [hst]; exact ha) (L.budget_step hκ hM hg hcal))
  have hsw' : SameWorld F t W :=
    ⟨fun f hf => (hsw.1 f hf).trans (L.r_worldPR_out h _ _ w (fun hm => hf hm.1)).symm,
      fun a ha => (hsw.2.1 a ha).trans (by
        rw [L.mem_worldPR, worldP, mem_overlay_out (R := L.calleeRgn κ M h w)
          (fun hr => ha (hdeadW a hr).1)]),
      hsw.2.2.trans (L.program_worldPR h _ _ w).symm⟩
  exact L.progOsCorePRBRLRU hL hκ ih hdet hg hh hcal himgF himgG himgS hLu hLd hdefs0 hdefs hK hG
    hra hsw' hmsk hrgn hx houts

/-- **`progOsPRBRL` with the register prophecy but `x30`.** -/
theorem progOsPRBRL30RU (hL : L.Ok) [L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1))
    (hdet : 0 < M → L.DetPRBRU κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {s0 : Arm.ArmState} (himgF : ∀ a, L.Img a → F a)
    (himgG : ∀ a, L.Img a → G a) (himgS : ∀ a, L.Img a → s0.mem a = L.imgMem a)
    {info : CallInfo} {h : Clif.Function} (hsite : L.ProgSite g info h) (ctx : FnCtx)
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {n : Nat}
    {Q : Arm.ArmState → Prop}
    (hQ : ∀ t, Q t → CallPc (L.A g).fa (L.A g).base (Arm.r .PC t) →
      (∀ f, MaskedReg f → f ≠ .GPR 30#5 → Arm.r f t = Arm.r f (R n)) ∧
        ∀ a, StackBelow (κ M g) (spv t) a → t.mem a = P n a) :
    CallSoundCtlGP Q F (κ M g) G s0 (CallAt (L.A g).fa (L.A g).base) (callExec (L.hooks M))
      (csemV (GotV (L.A g).vcp) F ctx (L.XPRBT κ M g F P R n)) (.call info) .next := by
  have ⟨_, nm, hdest, hpf⟩ := hsite
  obtain ⟨hh, hname⟩ := Clif.Program.func?_some hpf
  subst hname
  obtain ⟨n', Lu, Ld, hinfo, hLu, hLd⟩ := hL.callRegs g hg info h hsite
  subst hinfo
  cases hdest
  intro t hQt hK hD hG c wh ops regs i' w outs w' hops hst hasg hP hsw hal herr hsem
  replace hsem := csemV_sub hsem
  rw [operands_call_sym] at hops
  cases hops
  obtain ⟨hsz', hloc, -, -⟩ := checkStatic_facts hst
  have hregs := callRegs_eq (regs := regs) (by simpa using hsz')
    (fun p hp r hr => (hloc p hp).2 r hr)
  rw [call_useVals hregs] at hsem
  obtain ⟨o, hx, hout⟩ : ∃ o, L.progXPRBT κ M F h (Lu.map (fun q => regVal t q.2)) (P n) (R n) w =
      some (o, w') ∧ outs = o.take (callDefs Ld).length := by
    simp only [csem, Option.map_eq_some_iff, Prod.mk.injEq] at hsem
    obtain ⟨⟨o, w2⟩, hx, rfl, rfl, -⟩ := hsem
    rw [L.XPRBT_prog hpf] at hx
    exact ⟨o, hx, rfl⟩
  obtain ⟨hmskQ, hrgnQ⟩ := hQ t hQt hP.callPc
  obtain ⟨us', ds', rfl⟩ := assign_call_sym hasg
  exact ⟨L.pcall M h t, by simp only [callExec, hal, ↓reduceIte, L.hooks_some hpf],
    L.progOsCoreXPRRBRL30RU hL hκ ih hdet hg hh (.inl ⟨_, hsite⟩) himgF himgG himgS hLu hLd rfl
      (call_defs hregs) hK hG (hL.raCall g hg _ h hsite _ hP.callPc) hsw hmskQ hrgnQ hx ⟨_, hout⟩⟩

/-- **`progOsRegPRBRL` with the register prophecy but `x30`.** -/
theorem progOsRegPRBRL30RU (hL : L.Ok) [L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1))
    (hdet : 0 < M → L.DetPRBRU κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {s0 : Arm.ArmState} (himgF : ∀ a, L.Img a → F a)
    (himgG : ∀ a, L.Img a → G a) (himgS : ∀ a, L.Img a → s0.mem a = L.imgMem a)
    {info : CallInfo} (hsite : (L.A g).vcp.CallSite info) (hreg : ∀ n, info.dest ≠ .sym n)
    (ctx : FnCtx) {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {n : Nat}
    {Q : Arm.ArmState → Prop}
    (hQ : ∀ t, Q t → CallPc (L.A g).fa (L.A g).base (Arm.r .PC t) →
      (∀ f, MaskedReg f → f ≠ .GPR 30#5 → Arm.r f t = Arm.r f (R n)) ∧
        ∀ a, StackBelow (κ M g) (spv t) a → t.mem a = P n a) :
    CallSoundCtlGP Q F (κ M g) G s0 (CallAt (L.A g).fa (L.A g).base) (callExec (L.hooks M))
      (csemV (GotV (L.A g).vcp) F ctx (L.XPRBT κ M g F P R n)) (.call info) .next := by
  obtain ⟨tv, Lu, Ld, rfl, hregs⟩ := hL.blrRegs g hg info hsite hreg
  intro t hQt hK hD hG c wh ops regs i' w outs w' hops hst hasg hP hsw hal herr hsem
  have hguard := csemV_guard hsem
  replace hsem := csemV_sub hsem
  have hops0 := hops
  rw [operands_call_reg] at hops
  cases hops
  obtain ⟨hsz', hloc, -, -⟩ := checkStatic_facts hst
  obtain ⟨r0, hregs0⟩ := callRegs_eq_reg (regs := regs) (by simpa using hsz')
    (fun p hp r hr => (hloc p hp).2 r hr)
  obtain ⟨n0, rfl, hn0, -⟩ : ∃ n, r0 = .x n ∧ n < 29 ∧ n ≠ 16 := by
    have hmem : (tgtOp tv, Loc.reg r0) ∈
        (((tgtOp tv :: (retOps Lu ++ callDefOps Ld)).toArray).zip (regs.map Loc.reg)).toList := by
      simp [Array.toList_zip, Array.toList_map, hregs0]
    obtain ⟨n, hn, h29, h16, -⟩ := locOk_int (hloc _ hmem).1
    exact ⟨n, hn, h29, h16⟩
  have hsem0 := hsem
  rw [call_useVals_reg hregs0] at hsem
  obtain ⟨r1, us', ds', hr1, rfl⟩ := assign_call_reg hasg
  have h0 : regs[0]? = some (.x n0) := by
    rw [← Array.getElem?_toList, hregs0]; rfl
  rw [h0] at hr1
  cases hr1
  have hc := hL.compiled g hg
  obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hc.layout
  have htgt : blrTarget t = some (lo64 (regVal t (.x n0))) := by
    obtain ⟨j, x, tt, hj, hx, hpc⟩ := hP
    simp only [MInst.callInsn?, Option.some.injEq] at hx
    subst hx
    rw [lo64_regVal_x]
    exact blrTarget_of hc.layout hlm hj hn0 hpc
      (fun k wd hk => hL.imgCode g hg t (fun a ha => (hG a (himgG a ha)).trans (himgS a ha)) k wd hk)
  obtain ⟨o, hx, hout⟩ : ∃ o, (L.XPRBT κ M g F P R n).call none
      (regVal t (.x n0) :: Lu.map (fun q => regVal t q.2)) w = some (o, w') ∧
      outs = o.take (callDefs Ld).length := by
    simp only [csem, Option.map_eq_some_iff, Prod.mk.injEq] at hsem
    obtain ⟨⟨o, w2⟩, hx, rfl, rfl, -⟩ := hsem
    exact ⟨o, hx, rfl⟩
  cases hs : symCallee L.Xb L.P (lo64 (regVal t (.x n0))) with
  | none =>
    have hb : (blrTarget t).bind (symCallee L.Xb L.P) = none := by rw [htgt]; exact hs
    rw [L.XPRBT_none hs] at hx
    have hsem' : csem F ctx L.Xb (.call ⟨.reg (.vreg tv .int), retPairs Lu, callDefs Ld⟩)
        (useVals (tgtOp tv :: (retOps Lu ++ callDefOps Ld)).toArray regs t) w =
        some (outs, w', .next) := by
      rw [call_useVals_reg hregs0, hout]; simp [csem, hx]
    obtain ⟨s', hex, rest⟩ := hL.baseOs g hg _ hsite (.inl rfl) F (κ M g) G s0
      (CallAt (L.A g).fa (L.A g).base) ctx t hK hD hG c wh _ regs _ w outs w' hops0 hst hasg hP hsw
      hal herr hsem'
    refine ⟨s', ?_, rest⟩
    simp only [callExec] at hex ⊢
    rw [L.hooks_base (.inl rfl) t (fun _ => hb)]
    exact hex
  | some h =>
    rw [L.XPRBT_ind hs] at hx
    split at hx
    · rename_i hdecl
      have hh : h ∈ L.P.funcs := List.mem_of_find?_eq_some hs
      have hgot : ∀ n, GotV (L.A g).vcp tv n → n = h.name := by
        intro n hn
        have e := hguard tv n _ rfl hn (operands_call_reg tv Lu Ld) (by simp [tgtOp, Operand.isUse])
        rw [call_useVals_reg hregs0] at e
        simp only [List.head?_cons, Option.map_some, Option.some.injEq] at e
        exact L.got_target hL hs e
      obtain ⟨hLu, hLd⟩ := hregs h hh ⟨hdecl.1, hgot⟩ (by rw [← hdecl.2, List.length_map])
      have hb : (blrTarget t).bind (symCallee L.Xb L.P) = some h := by rw [htgt]; exact hs
      exact ⟨L.pcall M h t, by simp only [callExec, hal, ↓reduceIte, L.hooks_none hb],
        L.progOsCoreXPRRBRL30RU hL hκ ih hdet hg hh (.inr (.inr ⟨hh, hdecl.1.1⟩)) himgF himgG himgS
          hLu hLd rfl (call_defs_reg hregs0) hK hG
          (hL.raBlr g hg _ hsite hreg h hh hdecl.1.1 _ hP.callPc) hsw (hQ t hQt hP.callPc).1
          (hQ t hQt hP.callPc).2 hx ⟨_, hout⟩⟩
    · cases hx

/-- **`calleeOkPRBRL` with the register prophecy but `x30`** (module doc). -/
theorem calleeOkPRBRL30RU (hL : L.Ok) [L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1))
    (hdet : 0 < M → L.DetPRBRU κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {ra : BitVec 64} {s w₀ : Arm.ArmState}
    (he : L.MachEntry κ M g F G ra s w₀)
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {n : Nat}
    {Q : Arm.ArmState → Prop}
    (hQ : ∀ t, Q t → CallPc (L.A g).fa (L.A g).base (Arm.r .PC t) →
      (∀ f, MaskedReg f → f ≠ .GPR 30#5 → Arm.r f t = Arm.r f (R n)) ∧
        ∀ a, StackBelow (κ M g) (spv t) a → t.mem a = P n a) :
    CalleeOkGP Q F (κ M g) G s (CallAt (L.A g).fa (L.A g).base) (L.XPRBT κ M g F P R n) (L.hooks M)
      (L.A g).vcp.CallSite (GotV (L.A g).vcp) where
  os ctx info hsite := by
    cases hd : info.dest with
    | reg r =>
      exact L.progOsRegPRBRL30RU hL hκ ih hdet hg he.imgF he.imgG he.imgS hsite
        (fun n => by rw [hd]; simp) ctx hQ
    | sym n =>
    have hdest := hd
    cases hpf : L.P.func? n with
    | some h =>
      exact L.progOsPRBRL30RU hL hκ ih hdet hg he.imgF he.imgG he.imgS ⟨hsite, n, hdest, hpf⟩ ctx hQ
    | none =>
      have hb : L.BaseDest (destOf info) := .inr ⟨n, by simp [destOf, hdest], hpf⟩
      have h0 := hL.baseOs g hg info hsite hb F (κ M g) G s (CallAt (L.A g).fa (L.A g).base) ctx
      intro t _ h1 h2 h3 c wh ops regs i' w outs w' hops hst hasg h4 hsw hal herr hsem
      obtain ⟨d, us, ds⟩ := info
      simp only at hdest
      subst hdest
      have hsem' : csem F ctx L.Xb (.call ⟨.sym n, us, ds⟩) (useVals ops regs t) w =
          some (outs, w', .next) := by
        rw [← csemV_sub hsem]; simp [csem, L.XPRBT_base hpf]
      obtain ⟨s', hex, rest⟩ :=
        h0 t h1 h2 h3 c wh ops regs i' w outs w' hops hst hasg h4 hsw hal herr hsem'
      refine ⟨s', ?_, rest⟩
      obtain ⟨us', ds', rfl⟩ := assign_call_sym hasg
      simp only [callExec] at hex ⊢
      rw [L.hooks_base (.inr ⟨n, rfl, hpf⟩) t (fun h => by cases h)]
      exact hex
  pc := (L.calleeOkPRBRLRU hL hκ ih hdet hg he (Q := fun _ => False) (P := P) (R := R) (n := n)
    (fun _ h => h.elim)).pc
  ext := (L.calleeOkPRBRLRU hL hκ ih hdet hg he (Q := fun _ => False) (P := P) (R := R) (n := n)
    (fun _ h => h.elim)).ext

/-- **`calleeTryOkPRBRL` with the register prophecy but `x30`.** -/
theorem calleeTryOkPRBRL30RU (hL : L.Ok) [L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1))
    (hdet : 0 < M → L.DetPRBRU κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {ra : BitVec 64} {s w₀ : Arm.ArmState}
    (he : L.MachEntry κ M g F G ra s w₀)
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {n : Nat}
    {Q : Arm.ArmState → Prop}
    (hQ : ∀ t, Q t → CallPc (L.A g).fa (L.A g).base (Arm.r .PC t) →
      (∀ f, MaskedReg f → f ≠ .GPR 30#5 → Arm.r f t = Arm.r f (R n)) ∧
        ∀ a, StackBelow (κ M g) (spv t) a → t.mem a = P n a) :
    CalleeTryOkGP Q F (κ M g) G s (CallAt (L.A g).fa (L.A g).base) (L.XPRBT κ M g F P R n)
      (L.hooks M) (L.A g).vcp.TrySite (GotV (L.A g).vcp) := by
  intro ctx info ti hsite
  cases hd : info.dest with
  | sym n =>
    have hdest := hd
    cases hpf : L.P.func? n with
    | some h =>
      exact calleeTryOkGP_of_call (S := fun i t => i = info ∧ t = ti)
        (fun ctx' i t ⟨e1, _⟩ => e1 ▸ (L.calleeOkPRBRL30RU hL hκ ih hdet hg he hQ).os ctx' info
          hsite.callSite)
        (fun _ _ _ h => callAt_tryCall_call h)
        (fun i t ⟨_, e2⟩ => e2 ▸ trySite_clobberAll (hL.compiled g hg).alloc hsite)
        ctx info ti ⟨rfl, rfl⟩
    | none =>
      have hb : L.BaseDest (destOf info) := .inr ⟨n, by simp [destOf, hdest], hpf⟩
      intro c wh ops regs i' t w outs w' s' _ _ _ _ hops hst hasg _ hsw hal herr hsem hex
      obtain ⟨d, us, ds⟩ := info
      simp only at hdest
      subst hdest
      have hsem' : csem F ctx L.Xb (.tryCall ⟨.sym n, us, ds⟩ ti) (useVals ops regs t) w =
          some (outs, w', .goto ti.handlers.length) := by
        rw [← csemV_sub hsem]; simp [csem, L.XPRBT_base hpf]
      obtain ⟨ic, rfl, hasg'⟩ := (assign_call_tryCall _ regs).2 ti i' hasg
      obtain ⟨us', ds', hic⟩ := assign_call_sym hasg'
      cases hic
      have hex' : callExec L.Hb (.tryCall ⟨.sym n, us', ds'⟩ ti) t = some s' := by
        simp only [callExec] at hex ⊢
        rw [← L.hooks_base (M := M) (.inr ⟨n, rfl, hpf⟩) t (fun h => by cases h)]
        exact hex
      exact hL.baseTry g hg F ctx _ ti ⟨hsite, hb⟩ c wh ops regs _ t w outs w' s' hops hst hasg
        hsw hal herr hsem' hex'
  | reg r =>
    obtain ⟨tv, Lu, Ld, hinfo, -⟩ :=
      hL.blrRegs g hg info hsite.callSite (fun n => by rw [hd]; simp)
    subst hinfo
    intro c wh ops regs i' t w outs w' s' hQt hK hD hG hops hst hasg hP hsw hal herr hsem hex
    have hcl := trySite_clobberAll (hL.compiled g hg).alloc hsite
    have hopsC : (MInst.call ⟨.reg (.vreg tv .int), retPairs Lu, callDefs Ld⟩).operands =
        .ok ops := by
      rw [← operands_tryCall_call _ ti]; exact hops
    have hops1 := hopsC
    rw [operands_call_reg] at hops1
    cases hops1
    obtain ⟨hsz', hloc, -, -⟩ := checkStatic_facts hst
    obtain ⟨r0, hregs0⟩ := callRegs_eq_reg (regs := regs)
      (by have := hsz'; simp only [Array.size_map] at this ⊢; simpa using this)
      (fun p hp r hr => (hloc p hp).2 r hr)
    obtain ⟨n0, rfl, hn0, -⟩ : ∃ n, r0 = .x n ∧ n < 29 ∧ n ≠ 16 := by
      have hmem : (tgtOp tv, Loc.reg r0) ∈
          (((tgtOp tv :: (retOps Lu ++ callDefOps Ld)).toArray).zip (regs.map Loc.reg)).toList := by
        simp [Array.toList_zip, Array.toList_map, hregs0]
      obtain ⟨n, hn, h29, h16, -⟩ := locOk_int (hloc _ hmem).1
      exact ⟨n, hn, h29, h16⟩
    obtain ⟨ic, rfl, hasg'⟩ := (assign_call_tryCall _ regs).2 ti i' hasg
    obtain ⟨r1, us', ds', hr1, hic⟩ := assign_call_reg hasg'
    cases hic
    have h0 : regs[0]? = some (.x n0) := by
      rw [← Array.getElem?_toList, hregs0]; rfl
    rw [h0] at hr1
    cases hr1
    have hc := hL.compiled g hg
    obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hc.layout
    have htgt : blrTarget t = some (lo64 (regVal t (.x n0))) := by
      obtain ⟨j, x, tt, hj, hx, hpc⟩ := hP
      simp only [MInst.callInsn?, Option.some.injEq] at hx
      subst hx
      rw [lo64_regVal_x]
      exact blrTarget_of hc.layout hlm hj hn0 hpc
        (fun k wd hk => hL.imgCode g hg t (fun a ha => (hG a (he.imgG a ha)).trans (he.imgS a ha))
          k wd hk)
    have huv := call_useVals_reg (tv := tv) (s := t) hregs0
    cases hs : symCallee L.Xb L.P (lo64 (regVal t (.x n0))) with
    | none =>
      have hb : (blrTarget t).bind (symCallee L.Xb L.P) = none := by rw [htgt]; exact hs
      have hsem' : csem F ctx L.Xb (.tryCall ⟨.reg (.vreg tv .int), retPairs Lu, callDefs Ld⟩ ti)
          (useVals (tgtOp tv :: (retOps Lu ++ callDefOps Ld)).toArray regs t) w =
          some (outs, w', .goto ti.handlers.length) := by
        rw [← csemV_sub hsem, huv]; simp [csem, L.XPRBT_none hs]
      have hex' : callExec L.Hb (.tryCall ⟨.reg (.x n0), us', ds'⟩ ti) t = some s' := by
        simp only [callExec] at hex ⊢
        rw [← L.hooks_base (M := M) (.inl rfl) t (fun _ => hb)]
        exact hex
      exact hL.baseTry g hg F ctx _ ti ⟨hsite, .inl rfl⟩ c wh _ regs _ t w outs w' s' hops hst
        hasg hsw hal herr hsem' hex'
    | some h =>
      exact calleeTryP_at ((L.calleeOkPRBRL30RU hL hκ ih hdet hg he hQ).os ctx _ hsite.callSite)
        (fun _ _ h => callAt_tryCall_call h) hcl hQt hK hD hG hops hst hasg hP hsw hal herr hsem hex

/-! ### The statements with `DetPRBR` (corollaries, `DetPRBR.toU`) -/

/-- **`progOsCoreXPRRBRL` with the register prophecy but `x30`, determinism `DetPRBR`**
(`progOsCoreXPRRBRL30RU`). -/
theorem progOsCoreXPRRBRL30R (hL : L.Ok) [hR : L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1))
    (hdet : 0 < M → L.DetPRBR κ (M - 1)) {g h : Clif.Function}
    (hg : g ∈ L.P.funcs) (hh : h ∈ L.P.funcs)
    (hcal : L.Callee g h)
    {F G : BitVec 64 → Prop} {s0 : Arm.ArmState} (himgF : ∀ a, L.Img a → F a)
    (himgG : ∀ a, L.Img a → G a) (himgS : ∀ a, L.Img a → s0.mem a = L.imgMem a)
    {Lu : List (Nat × Reg)} {Ld : List (Reg × Nat)} (hLu : Lu.map (·.2) = regLocs h.sig)
    (hLd : (Ld.map (·.1)).take (sigRets h.sig).length =
      (List.range (min (sigRets h.sig).length Ld.length)).map Reg.x)
    {info : CallInfo} (hdefs0 : info.defs = callDefs Ld)
    {ops : Array Operand} {regs : Array Reg}
    (hdefs : ((ops.zip regs).toList.filter (·.1.isDef)) = (callDefOps Ld).zip (Ld.map (·.1)))
    {t w w' : Arm.ArmState} {o outs : List CV}
    (hK : κ M g ≤ (spOf t).toNat) (hG : ∀ a, G a → t.mem a = s0.mem a)
    (hra : RaOk (L.A h) (Arm.r .PC t))
    (hsw : SameWorld F t w)
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {n : Nat}
    (hmskQ : ∀ f, MaskedReg f → f ≠ .GPR 30#5 → Arm.r f t = Arm.r f (R n))
    (hrgnQ : ∀ a, StackBelow (κ M g) (spv t) a → t.mem a = P n a)
    (hx : L.progXPRBT κ M F h (Lu.map (fun q => regVal t q.2)) (P n) (R n) w = some (o, w'))
    (houts : ∃ n, outs = o.take n) :
    SameWorld F (L.pcall M h t) w' ∧
      FrameKeep (fun a => F a ∧ ¬ StackBelow (κ M g) (spOf t) a) t (L.pcall M h t) ∧
      (∀ p ∈ defRegs ops regs outs, regVal (L.pcall M h t) p.1.2 = p.2) ∧
      (∀ r, r.allocatable = true → (∀ p ∈ (ops.zip regs).toList, p.1.isDef = true → p.2 ≠ r) →
        r ∉ (MInst.call info).clobbers → regVal (L.pcall M h t) r = regVal t r) ∧
      (∀ r ∈ (MInst.call info).clobbers, r ∈ calleeSaved →
        ckeep r (regVal (L.pcall M h t) r) = ckeep r (regVal t r)) :=
  L.progOsCoreXPRRBRL30RU hL hκ ih (fun h => DetPRBR.toU L (hdet h)) hg hh hcal himgF himgG himgS
    hLu hLd hdefs0 hdefs hK hG hra hsw hmskQ hrgnQ hx houts

/-- **`progOsPRBRL` with the register prophecy but `x30`, determinism `DetPRBR`.** -/
theorem progOsPRBRL30R (hL : L.Ok) [L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1))
    (hdet : 0 < M → L.DetPRBR κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {s0 : Arm.ArmState} (himgF : ∀ a, L.Img a → F a)
    (himgG : ∀ a, L.Img a → G a) (himgS : ∀ a, L.Img a → s0.mem a = L.imgMem a)
    {info : CallInfo} {h : Clif.Function} (hsite : L.ProgSite g info h) (ctx : FnCtx)
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {n : Nat}
    {Q : Arm.ArmState → Prop}
    (hQ : ∀ t, Q t → CallPc (L.A g).fa (L.A g).base (Arm.r .PC t) →
      (∀ f, MaskedReg f → f ≠ .GPR 30#5 → Arm.r f t = Arm.r f (R n)) ∧
        ∀ a, StackBelow (κ M g) (spv t) a → t.mem a = P n a) :
    CallSoundCtlGP Q F (κ M g) G s0 (CallAt (L.A g).fa (L.A g).base) (callExec (L.hooks M))
      (csemV (GotV (L.A g).vcp) F ctx (L.XPRBT κ M g F P R n)) (.call info) .next :=
  L.progOsPRBRL30RU hL hκ ih (fun h => DetPRBR.toU L (hdet h)) hg himgF himgG himgS hsite ctx hQ

/-- **`progOsRegPRBRL` with the register prophecy but `x30`, determinism `DetPRBR`.** -/
theorem progOsRegPRBRL30R (hL : L.Ok) [L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1))
    (hdet : 0 < M → L.DetPRBR κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {s0 : Arm.ArmState} (himgF : ∀ a, L.Img a → F a)
    (himgG : ∀ a, L.Img a → G a) (himgS : ∀ a, L.Img a → s0.mem a = L.imgMem a)
    {info : CallInfo} (hsite : (L.A g).vcp.CallSite info) (hreg : ∀ n, info.dest ≠ .sym n)
    (ctx : FnCtx) {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {n : Nat}
    {Q : Arm.ArmState → Prop}
    (hQ : ∀ t, Q t → CallPc (L.A g).fa (L.A g).base (Arm.r .PC t) →
      (∀ f, MaskedReg f → f ≠ .GPR 30#5 → Arm.r f t = Arm.r f (R n)) ∧
        ∀ a, StackBelow (κ M g) (spv t) a → t.mem a = P n a) :
    CallSoundCtlGP Q F (κ M g) G s0 (CallAt (L.A g).fa (L.A g).base) (callExec (L.hooks M))
      (csemV (GotV (L.A g).vcp) F ctx (L.XPRBT κ M g F P R n)) (.call info) .next :=
  L.progOsRegPRBRL30RU hL hκ ih (fun h => DetPRBR.toU L (hdet h)) hg himgF himgG himgS hsite hreg
    ctx hQ

/-- **`calleeOkPRBRL` with the register prophecy but `x30`, determinism `DetPRBR`.** -/
theorem calleeOkPRBRL30R (hL : L.Ok) [L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1))
    (hdet : 0 < M → L.DetPRBR κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {ra : BitVec 64} {s w₀ : Arm.ArmState}
    (he : L.MachEntry κ M g F G ra s w₀)
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {n : Nat}
    {Q : Arm.ArmState → Prop}
    (hQ : ∀ t, Q t → CallPc (L.A g).fa (L.A g).base (Arm.r .PC t) →
      (∀ f, MaskedReg f → f ≠ .GPR 30#5 → Arm.r f t = Arm.r f (R n)) ∧
        ∀ a, StackBelow (κ M g) (spv t) a → t.mem a = P n a) :
    CalleeOkGP Q F (κ M g) G s (CallAt (L.A g).fa (L.A g).base) (L.XPRBT κ M g F P R n) (L.hooks M)
      (L.A g).vcp.CallSite (GotV (L.A g).vcp) :=
  L.calleeOkPRBRL30RU hL hκ ih (fun h => DetPRBR.toU L (hdet h)) hg he hQ

/-- **`calleeTryOkPRBRL` with the register prophecy but `x30`, determinism `DetPRBR`.** -/
theorem calleeTryOkPRBRL30R (hL : L.Ok) [L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1))
    (hdet : 0 < M → L.DetPRBR κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {ra : BitVec 64} {s w₀ : Arm.ArmState}
    (he : L.MachEntry κ M g F G ra s w₀)
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {n : Nat}
    {Q : Arm.ArmState → Prop}
    (hQ : ∀ t, Q t → CallPc (L.A g).fa (L.A g).base (Arm.r .PC t) →
      (∀ f, MaskedReg f → f ≠ .GPR 30#5 → Arm.r f t = Arm.r f (R n)) ∧
        ∀ a, StackBelow (κ M g) (spv t) a → t.mem a = P n a) :
    CalleeTryOkGP Q F (κ M g) G s (CallAt (L.A g).fa (L.A g).base) (L.XPRBT κ M g F P R n)
      (L.hooks M) (L.A g).vcp.TrySite (GotV (L.A g).vcp) :=
  L.calleeTryOkPRBRL30RU hL hκ ih (fun h => DetPRBR.toU L (hdet h)) hg he hQ

/-! ### The statements with `DetPRB` (corollaries, `DetPRB.toR`) -/

/-- **`progOsCoreXPRRBRL` with the register prophecy but `x30`** (module doc). -/
theorem progOsCoreXPRRBRL30 (hL : L.Ok) [hR : L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1))
    (hdet : 0 < M → L.DetPRB κ (M - 1)) {g h : Clif.Function}
    (hg : g ∈ L.P.funcs) (hh : h ∈ L.P.funcs)
    (hcal : L.Callee g h)
    {F G : BitVec 64 → Prop} {s0 : Arm.ArmState} (himgF : ∀ a, L.Img a → F a)
    (himgG : ∀ a, L.Img a → G a) (himgS : ∀ a, L.Img a → s0.mem a = L.imgMem a)
    {Lu : List (Nat × Reg)} {Ld : List (Reg × Nat)} (hLu : Lu.map (·.2) = regLocs h.sig)
    (hLd : (Ld.map (·.1)).take (sigRets h.sig).length =
      (List.range (min (sigRets h.sig).length Ld.length)).map Reg.x)
    {info : CallInfo} (hdefs0 : info.defs = callDefs Ld)
    {ops : Array Operand} {regs : Array Reg}
    (hdefs : ((ops.zip regs).toList.filter (·.1.isDef)) = (callDefOps Ld).zip (Ld.map (·.1)))
    {t w w' : Arm.ArmState} {o outs : List CV}
    (hK : κ M g ≤ (spOf t).toNat) (hG : ∀ a, G a → t.mem a = s0.mem a)
    (hra : RaOk (L.A h) (Arm.r .PC t))
    (hsw : SameWorld F t w)
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {n : Nat}
    (hmskQ : ∀ f, MaskedReg f → f ≠ .GPR 30#5 → Arm.r f t = Arm.r f (R n))
    (hrgnQ : ∀ a, StackBelow (κ M g) (spv t) a → t.mem a = P n a)
    (hx : L.progXPRBT κ M F h (Lu.map (fun q => regVal t q.2)) (P n) (R n) w = some (o, w'))
    (houts : ∃ n, outs = o.take n) :
    SameWorld F (L.pcall M h t) w' ∧
      FrameKeep (fun a => F a ∧ ¬ StackBelow (κ M g) (spOf t) a) t (L.pcall M h t) ∧
      (∀ p ∈ defRegs ops regs outs, regVal (L.pcall M h t) p.1.2 = p.2) ∧
      (∀ r, r.allocatable = true → (∀ p ∈ (ops.zip regs).toList, p.1.isDef = true → p.2 ≠ r) →
        r ∉ (MInst.call info).clobbers → regVal (L.pcall M h t) r = regVal t r) ∧
      (∀ r ∈ (MInst.call info).clobbers, r ∈ calleeSaved →
        ckeep r (regVal (L.pcall M h t) r) = ckeep r (regVal t r)) :=
  L.progOsCoreXPRRBRL30R hL hκ ih (fun h => DetPRB.toR L (hdet h)) hg hh hcal himgF himgG himgS
    hLu hLd hdefs0 hdefs hK hG hra hsw hmskQ hrgnQ hx houts

/-- **`progOsPRBRL` with the register prophecy but `x30`.** -/
theorem progOsPRBRL30 (hL : L.Ok) [L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1))
    (hdet : 0 < M → L.DetPRB κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {s0 : Arm.ArmState} (himgF : ∀ a, L.Img a → F a)
    (himgG : ∀ a, L.Img a → G a) (himgS : ∀ a, L.Img a → s0.mem a = L.imgMem a)
    {info : CallInfo} {h : Clif.Function} (hsite : L.ProgSite g info h) (ctx : FnCtx)
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {n : Nat}
    {Q : Arm.ArmState → Prop}
    (hQ : ∀ t, Q t → CallPc (L.A g).fa (L.A g).base (Arm.r .PC t) →
      (∀ f, MaskedReg f → f ≠ .GPR 30#5 → Arm.r f t = Arm.r f (R n)) ∧
        ∀ a, StackBelow (κ M g) (spv t) a → t.mem a = P n a) :
    CallSoundCtlGP Q F (κ M g) G s0 (CallAt (L.A g).fa (L.A g).base) (callExec (L.hooks M))
      (csemV (GotV (L.A g).vcp) F ctx (L.XPRBT κ M g F P R n)) (.call info) .next :=
  L.progOsPRBRL30R hL hκ ih (fun h => DetPRB.toR L (hdet h)) hg himgF himgG himgS hsite ctx hQ

/-- **`progOsRegPRBRL` with the register prophecy but `x30`.** -/
theorem progOsRegPRBRL30 (hL : L.Ok) [L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1))
    (hdet : 0 < M → L.DetPRB κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {s0 : Arm.ArmState} (himgF : ∀ a, L.Img a → F a)
    (himgG : ∀ a, L.Img a → G a) (himgS : ∀ a, L.Img a → s0.mem a = L.imgMem a)
    {info : CallInfo} (hsite : (L.A g).vcp.CallSite info) (hreg : ∀ n, info.dest ≠ .sym n)
    (ctx : FnCtx) {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {n : Nat}
    {Q : Arm.ArmState → Prop}
    (hQ : ∀ t, Q t → CallPc (L.A g).fa (L.A g).base (Arm.r .PC t) →
      (∀ f, MaskedReg f → f ≠ .GPR 30#5 → Arm.r f t = Arm.r f (R n)) ∧
        ∀ a, StackBelow (κ M g) (spv t) a → t.mem a = P n a) :
    CallSoundCtlGP Q F (κ M g) G s0 (CallAt (L.A g).fa (L.A g).base) (callExec (L.hooks M))
      (csemV (GotV (L.A g).vcp) F ctx (L.XPRBT κ M g F P R n)) (.call info) .next :=
  L.progOsRegPRBRL30R hL hκ ih (fun h => DetPRB.toR L (hdet h)) hg himgF himgG himgS hsite hreg
    ctx hQ

/-- **`calleeOkPRBRL` with the register prophecy but `x30`** (module doc). -/
theorem calleeOkPRBRL30 (hL : L.Ok) [L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1))
    (hdet : 0 < M → L.DetPRB κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {ra : BitVec 64} {s w₀ : Arm.ArmState}
    (he : L.MachEntry κ M g F G ra s w₀)
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {n : Nat}
    {Q : Arm.ArmState → Prop}
    (hQ : ∀ t, Q t → CallPc (L.A g).fa (L.A g).base (Arm.r .PC t) →
      (∀ f, MaskedReg f → f ≠ .GPR 30#5 → Arm.r f t = Arm.r f (R n)) ∧
        ∀ a, StackBelow (κ M g) (spv t) a → t.mem a = P n a) :
    CalleeOkGP Q F (κ M g) G s (CallAt (L.A g).fa (L.A g).base) (L.XPRBT κ M g F P R n) (L.hooks M)
      (L.A g).vcp.CallSite (GotV (L.A g).vcp) :=
  L.calleeOkPRBRL30R hL hκ ih (fun h => DetPRB.toR L (hdet h)) hg he hQ

/-- **`calleeTryOkPRBRL` with the register prophecy but `x30`.** -/
theorem calleeTryOkPRBRL30 (hL : L.Ok) [L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1))
    (hdet : 0 < M → L.DetPRB κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {ra : BitVec 64} {s w₀ : Arm.ArmState}
    (he : L.MachEntry κ M g F G ra s w₀)
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {n : Nat}
    {Q : Arm.ArmState → Prop}
    (hQ : ∀ t, Q t → CallPc (L.A g).fa (L.A g).base (Arm.r .PC t) →
      (∀ f, MaskedReg f → f ≠ .GPR 30#5 → Arm.r f t = Arm.r f (R n)) ∧
        ∀ a, StackBelow (κ M g) (spv t) a → t.mem a = P n a) :
    CalleeTryOkGP Q F (κ M g) G s (CallAt (L.A g).fa (L.A g).base) (L.XPRBT κ M g F P R n)
      (L.hooks M) (L.A g).vcp.TrySite (GotV (L.A g).vcp) :=
  L.calleeTryOkPRBRL30R hL hκ ih (fun h => DetPRB.toR L (hdet h)) hg he hQ

/-- **`calleeOkXPBTGZ` with the register prophecy but `x30`** (module doc). -/
theorem calleeOkXPBTGZ30 (hL : L.Ok) [L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1))
    (hdet : 0 < M → L.DetPRB κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {ra : BitVec 64} {s w₀ : Arm.ArmState}
    (he : L.MachEntry κ M g F G ra s w₀)
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {n : Nat}
    {Q : Arm.ArmState → Prop}
    (hQ : ∀ t, Q t → CallPc (L.A g).fa (L.A g).base (Arm.r .PC t) →
      (∀ f, MaskedReg f → f ≠ .GPR 30#5 → Arm.r f t = Arm.r f (R n)) ∧
        ∀ a, StackBelow (κ M g) (spv t) a → t.mem a = P n a)
    {env : Clif.Env} {cs : Clif.State} {c : BitVec 64}
    (h2 : L.Stage2Z κ M g F P R env cs c Q n) :
    CalleeOkGP Q F (κ M g) G s (CallAt (L.A g).fa (L.A g).base)
      ((L.XPBTGY κ M g F P R env cs c).at n) (L.hooks M)
      (L.A g).vcp.CallSite (GotV (L.A g).vcp) :=
  (L.calleeOkPRBRL30 hL hκ ih hdet hg he hQ).ofCallSubU _ (L.XPBTGY_subZ hL h2)
    (L.XPBTGY_ext hL n)

/-- **`calleeTryOkXPBTGZ` with the register prophecy but `x30`.** -/
theorem calleeTryOkXPBTGZ30 (hL : L.Ok) [L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1))
    (hdet : 0 < M → L.DetPRB κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {ra : BitVec 64} {s w₀ : Arm.ArmState}
    (he : L.MachEntry κ M g F G ra s w₀)
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {n : Nat}
    {Q : Arm.ArmState → Prop}
    (hQ : ∀ t, Q t → CallPc (L.A g).fa (L.A g).base (Arm.r .PC t) →
      (∀ f, MaskedReg f → f ≠ .GPR 30#5 → Arm.r f t = Arm.r f (R n)) ∧
        ∀ a, StackBelow (κ M g) (spv t) a → t.mem a = P n a)
    {env : Clif.Env} {cs : Clif.State} {c : BitVec 64}
    (h2 : L.Stage2Z κ M g F P R env cs c Q n) :
    CalleeTryOkGP Q F (κ M g) G s (CallAt (L.A g).fa (L.A g).base)
      ((L.XPBTGY κ M g F P R env cs c).at n) (L.hooks M)
      (L.A g).vcp.TrySite (GotV (L.A g).vcp) :=
  (L.calleeTryOkPRBRL30 hL hκ ih hdet hg he hQ).ofCallSubU _ (L.XPBTGY_subZ hL h2)

/-- **The call contract of `XPBTGY … n` at the call sites' operands, with the register prophecy
but `x30`, determinism `DetPRBR`** (`calleeOkXPBTGZSR` with `calleeOkPRBRL30R`). -/
theorem calleeOkXPBTGZS30R (hL : L.Ok) [L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1))
    (hdet : 0 < M → L.DetPRBR κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {ra : BitVec 64} {s w₀ : Arm.ArmState}
    (he : L.MachEntry κ M g F G ra s w₀)
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {n : Nat}
    {Q : Arm.ArmState → Prop}
    (hQ : ∀ t, Q t → CallPc (L.A g).fa (L.A g).base (Arm.r .PC t) →
      (∀ f, MaskedReg f → f ≠ .GPR 30#5 → Arm.r f t = Arm.r f (R n)) ∧
        ∀ a, StackBelow (κ M g) (spv t) a → t.mem a = P n a)
    {env : Clif.Env} {cs : Clif.State} {c : BitVec 64}
    (h2 : L.Stage2ZS κ M g F P R env cs c Q n) :
    CalleeOkGP Q F (κ M g) G s (CallAt (L.A g).fa (L.A g).base)
      ((L.XPBTGY κ M g F P R env cs c).at n) (L.hooks M)
      (L.A g).vcp.CallSite (GotV (L.A g).vcp) :=
  (L.calleeOkPRBRL30R hL hκ ih hdet hg he hQ).ofCallSubS _ (L.XPBTGY_subZS hL h2)
    (L.XPBTGY_ext hL n)

/-- **The try-call contract of `XPBTGY … n` at the call sites' operands, with the register
prophecy but `x30`, determinism `DetPRBR`.** -/
theorem calleeTryOkXPBTGZS30R (hL : L.Ok) [L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1))
    (hdet : 0 < M → L.DetPRBR κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {ra : BitVec 64} {s w₀ : Arm.ArmState}
    (he : L.MachEntry κ M g F G ra s w₀)
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {n : Nat}
    {Q : Arm.ArmState → Prop}
    (hQ : ∀ t, Q t → CallPc (L.A g).fa (L.A g).base (Arm.r .PC t) →
      (∀ f, MaskedReg f → f ≠ .GPR 30#5 → Arm.r f t = Arm.r f (R n)) ∧
        ∀ a, StackBelow (κ M g) (spv t) a → t.mem a = P n a)
    {env : Clif.Env} {cs : Clif.State} {c : BitVec 64}
    (h2 : L.Stage2ZS κ M g F P R env cs c Q n) :
    CalleeTryOkGP Q F (κ M g) G s (CallAt (L.A g).fa (L.A g).base)
      ((L.XPBTGY κ M g F P R env cs c).at n) (L.hooks M)
      (L.A g).vcp.TrySite (GotV (L.A g).vcp) :=
  (L.calleeTryOkPRBRL30R hL hκ ih hdet hg he hQ).ofCallSubS (fun _ _ h => h.callSite) _
    (L.XPBTGY_subZS hL h2)

/-- **`calleeOkXPBTGZS30R` with the determinism premise `DetPRBRU`** (#732). -/
theorem calleeOkXPBTGZS30RU (hL : L.Ok) [L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1))
    (hdet : 0 < M → L.DetPRBRU κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {ra : BitVec 64} {s w₀ : Arm.ArmState}
    (he : L.MachEntry κ M g F G ra s w₀)
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {n : Nat}
    {Q : Arm.ArmState → Prop}
    (hQ : ∀ t, Q t → CallPc (L.A g).fa (L.A g).base (Arm.r .PC t) →
      (∀ f, MaskedReg f → f ≠ .GPR 30#5 → Arm.r f t = Arm.r f (R n)) ∧
        ∀ a, StackBelow (κ M g) (spv t) a → t.mem a = P n a)
    {env : Clif.Env} {cs : Clif.State} {c : BitVec 64}
    (h2 : L.Stage2ZS κ M g F P R env cs c Q n) :
    CalleeOkGP Q F (κ M g) G s (CallAt (L.A g).fa (L.A g).base)
      ((L.XPBTGY κ M g F P R env cs c).at n) (L.hooks M)
      (L.A g).vcp.CallSite (GotV (L.A g).vcp) :=
  (L.calleeOkPRBRL30RU hL hκ ih hdet hg he hQ).ofCallSubS _ (L.XPBTGY_subZS hL h2)
    (L.XPBTGY_ext hL n)

/-- **`calleeTryOkXPBTGZS30R` with the determinism premise `DetPRBRU`** (#732). -/
theorem calleeTryOkXPBTGZS30RU (hL : L.Ok) [L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1))
    (hdet : 0 < M → L.DetPRBRU κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {ra : BitVec 64} {s w₀ : Arm.ArmState}
    (he : L.MachEntry κ M g F G ra s w₀)
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {n : Nat}
    {Q : Arm.ArmState → Prop}
    (hQ : ∀ t, Q t → CallPc (L.A g).fa (L.A g).base (Arm.r .PC t) →
      (∀ f, MaskedReg f → f ≠ .GPR 30#5 → Arm.r f t = Arm.r f (R n)) ∧
        ∀ a, StackBelow (κ M g) (spv t) a → t.mem a = P n a)
    {env : Clif.Env} {cs : Clif.State} {c : BitVec 64}
    (h2 : L.Stage2ZS κ M g F P R env cs c Q n) :
    CalleeTryOkGP Q F (κ M g) G s (CallAt (L.A g).fa (L.A g).base)
      ((L.XPBTGY κ M g F P R env cs c).at n) (L.hooks M)
      (L.A g).vcp.TrySite (GotV (L.A g).vcp) :=
  (L.calleeTryOkPRBRL30RU hL hκ ih hdet hg he hQ).ofCallSubS (fun _ _ h => h.callSite) _
    (L.XPBTGY_subZS hL h2)

end LinkSys

end E2E
