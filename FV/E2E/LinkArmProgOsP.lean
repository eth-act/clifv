import FV.E2E.LinkArmProgCallP
import FV.E2E.LinkArmProphReg
import FV.E2E.RegLevelCallN
import FV.E2E.RegLevelTryP

/-!
# The call contract of call number `n` with both prophecies (SEM1 step 2s, `docs/plans/uninit.md` §5.8)

`progOsP`: `LinkArm.progOs` (a `bl` of a function `h` of `P`) for the external semantics of call
number `n` with the prophecies `P` (bytes) and `R` (masked registers), `XPR … P R n`, on
`ThmPDE κ (M - 1)`, as the restricted contract `CallSoundCtlGP Q`: at every call state `t` with
`Q t`, where `Q` gives the masked registers of `R n` and the `κ M g` bytes below `sp` of `P n`
(`OnCallPR` at the call state). The canonical callee state is `canon` of
`W := worldPR … (P n) (R n) w`; `t` agrees with it on every masked register but the pc (the
arguments are `t`'s own: `canon_self_r`, from `placeArgs_self`) and on the callee's region (both
`P n`), so `progOsCoreP` applies.

* `setReg_self`, `placeArgs_self`: writing a state's own register values changes nothing;
* `canon_self_r`: `canon` with the world's own argument values keeps every register but the pc;
* `progOsCoreXPR`: `progOsCoreP` at `worldPR` from the call state's prophecy facts;
* `progOsP`; `progOsRegP` (a `blr`; `XPR_none`, `XPR_ind`); `calleeOkP` (`XPR_base`, `XPR_ext`); `calleeTryOkP`.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

theorem setReg_self (s : Arm.ArmState) (r : Reg) : setReg s r (regVal s r) = s := by
  cases r with
  | x n => simp only [setReg]; rw [lo64_regVal_x, Arm.w_irrelevant]
  | v n => simp only [setReg, regVal]; rw [Arm.w_irrelevant]
  | _ => rfl

theorem placeArgs_self : ∀ (rs : List Reg) (s : Arm.ArmState), placeArgs rs (rs.map (regVal s)) s = s
  | [], _ => rfl
  | r :: rs, s => by
    rw [List.map_cons, placeArgs_cons, setReg_self, placeArgs_self rs s]

namespace LinkSys

variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

/-- **`canon` with the world's own argument values keeps every register but the pc.** -/
theorem canon_self_r (g : Clif.Function) (W : Arm.ArmState) {f : Arm.StateField} (hf : f ≠ .PC) :
    Arm.r f (L.canon g ((regLocs g.sig).map (regVal W)) W) = Arm.r f W := by
  have hu : (regLocs g.sig).map (regVal W) = (regLocs g.sig).map (regVal (L.withImg W)) :=
    List.map_congr_left fun r _ => by
      cases r <;> simp only [regVal] <;> first | rfl | rw [r_withImg]
  simp only [canon]
  rw [Arm.r_of_w_different hf, hu, placeArgs_self, r_withImg]

/-- **`progOsCoreP` at the world with both prophecies of call `n`**: a caller state `t` with the
masked registers of `R n` and `P n` in the `κ M g` bytes below its `sp` (`hmskQ`, `hrgnQ`) meets
`progOsCoreP`'s agreement premises for the canonical state of `worldPR … (P n) (R n) w`. -/
theorem progOsCoreXPR (hL : L.Ok) [hR : L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPDE κ (M - 1)) {g h : Clif.Function}
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
    (hmskQ : ∀ f, MaskedReg f → Arm.r f t = Arm.r f (R n))
    (hrgnQ : ∀ a, StackBelow (κ M g) (spv t) a → t.mem a = P n a)
    (hx : L.progXPR κ M F h (Lu.map (fun q => regVal t q.2)) (P n) (R n) w = some (o, w'))
    (houts : ∃ n, outs = o.take n) :
    SameWorld F (L.pcall M h t) w' ∧
      FrameKeep (fun a => F a ∧ ¬ StackBelow (κ M g) (spOf t) a) t (L.pcall M h t) ∧
      (∀ p ∈ defRegs ops regs outs, regVal (L.pcall M h t) p.1.2 = p.2) ∧
      (∀ r, r.allocatable = true → (∀ p ∈ (ops.zip regs).toList, p.1.isDef = true → p.2 ≠ r) →
        r ∉ (MInst.call info).clobbers → regVal (L.pcall M h t) r = regVal t r) ∧
      (∀ r ∈ (MInst.call info).clobbers, r ∈ calleeSaved →
        ckeep r (regVal (L.pcall M h t) r) = ckeep r (regVal t r)) := by
  let W := L.worldPR κ M h (P n) (R n) w
  replace hx : L.progX κ M F h (Lu.map (fun q => regVal t q.2)) W = some (o, w') := hx
  obtain ⟨-, harg, -⟩ := hL.argRegs h hh
  -- `Cond` of the world with the prophecies
  have hcondW : L.Cond κ M F h (Lu.map (fun q => regVal t q.2)) W := by
    have hx' := hx
    unfold progX at hx'
    exact Classical.byContradiction fun hc => by rw [if_neg (fun h' => hc h'.1)] at hx'; cases hx'
  obtain ⟨hM, -, -, -, hdeadW, -⟩ := hcondW
  have hspW : spv W = spv w :=
    L.r_worldPR_out (κ := κ) (M := M) h (P n) (R n) w (f := .GPR 31#5)
      (fun hm => by simp [MaskedReg, Masked] at hm)
  rw [hspW] at hdeadW
  have hst : spv t = spv w := hsw.1 _ (by simp [Masked])
  -- `t`'s arguments are `W`'s
  have hmaskedF : ∀ (r : Reg) (f : Arm.StateField), r.isArgReg = true → r.field = some f → MaskedReg f := by
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
      rw [hmskQ f hm, L.r_worldPR_in h (P n) w hm]
  have huses : Lu.map (fun q => regVal t q.2) = (regLocs h.sig).map (regVal W) := by
    rw [← hLu, List.map_map]
    exact List.map_congr_left fun q hq => hargW q.2 (by rw [← hLu]; exact List.mem_map_of_mem hq)
  have hmsk : ∀ f, Masked f → f ≠ .PC → f ≠ .GPR 30#5 →
      Arm.r f t = Arm.r f (L.canon h (Lu.map (fun q => regVal t q.2)) W) := by
    intro f hf hpc _
    rw [huses, L.canon_self_r h W hpc, L.r_worldPR_in h (P n) w ⟨hf, hpc⟩, hmskQ f ⟨hf, hpc⟩]
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
  exact L.progOsCoreP hL hκ ih hg hh hcal himgF himgG himgS hLu hLd hdefs0 hdefs hK hG hra hsw' hmsk
    hrgn hx houts

/-- **`progOs` for call number `n` with both prophecies, on `ThmPDE`** (module doc). -/
theorem progOsP (hL : L.Ok) [L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPDE κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {s0 : Arm.ArmState} (himgF : ∀ a, L.Img a → F a)
    (himgG : ∀ a, L.Img a → G a) (himgS : ∀ a, L.Img a → s0.mem a = L.imgMem a)
    {info : CallInfo} {h : Clif.Function} (hsite : L.ProgSite g info h) (ctx : FnCtx)
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {n : Nat}
    {Q : Arm.ArmState → Prop}
    (hQ : ∀ t, Q t → CallPc (L.A g).fa (L.A g).base (Arm.r .PC t) →
      (∀ f, MaskedReg f → Arm.r f t = Arm.r f (R n)) ∧
        ∀ a, StackBelow (κ M g) (spv t) a → t.mem a = P n a) :
    CallSoundCtlGP Q F (κ M g) G s0 (CallAt (L.A g).fa (L.A g).base) (callExec (L.hooks M))
      (csemV (GotV (L.A g).vcp) F ctx (L.XPR κ M g F P R n)) (.call info) .next := by
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
  obtain ⟨o, hx, hout⟩ : ∃ o, L.progXPR κ M F h (Lu.map (fun q => regVal t q.2)) (P n) (R n) w =
      some (o, w') ∧ outs = o.take (callDefs Ld).length := by
    simp only [csem, Option.map_eq_some_iff, Prod.mk.injEq] at hsem
    obtain ⟨⟨o, w2⟩, hx, rfl, rfl, -⟩ := hsem
    rw [L.XPR_prog hpf] at hx
    exact ⟨o, hx, rfl⟩
  obtain ⟨hmskQ, hrgnQ⟩ := hQ t hQt hP.callPc
  obtain ⟨us', ds', rfl⟩ := assign_call_sym hasg
  exact ⟨L.pcall M h t, by simp only [callExec, hal, ↓reduceIte, L.hooks_some hpf],
    L.progOsCoreXPR hL hκ ih hg hh (.inl ⟨_, hsite⟩) himgF himgG himgS hLu hLd rfl (call_defs hregs)
      hK hG (hL.raCall g hg _ h hsite _ hP.callPc) hsw hmskQ hrgnQ hx ⟨_, hout⟩⟩

theorem XPR_none {M : Nat} {g : Clif.Function} {F : BitVec 64 → Prop}
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {n : Nat} {u : CV} {args : List CV}
    {w : Arm.ArmState} (hn : symCallee L.Xb L.P (lo64 u) = none) :
    (L.XPR κ M g F P R n).call none (u :: args) w = L.Xb.call none (u :: args) w := by
  simp [XPR, hn]

open Classical in
theorem XPR_ind {M : Nat} {g : Clif.Function} {F : BitVec 64 → Prop}
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {n : Nat} {u : CV} {args : List CV}
    {w : Arm.ArmState} {h : Clif.Function} (hs : symCallee L.Xb L.P (lo64 u) = some h) :
    (L.XPR κ M g F P R n).call none (u :: args) w =
      if L.IndTo g h ∧ args.length = (regLocs h.sig).length
      then L.progXPR κ M F h args (P n) (R n) w else none := by
  simp only [XPR, hs]

/-- **`progOsReg` for call number `n` with both prophecies, on `ThmPDE`**: a `blr` to a declared
function of `P` (`progOsCoreXPR`), to another function of `P` (`XPR` undefined), or to no function
of `P` (the base's). -/
theorem progOsRegP (hL : L.Ok) [L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPDE κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {s0 : Arm.ArmState} (himgF : ∀ a, L.Img a → F a)
    (himgG : ∀ a, L.Img a → G a) (himgS : ∀ a, L.Img a → s0.mem a = L.imgMem a)
    {info : CallInfo} (hsite : (L.A g).vcp.CallSite info) (hreg : ∀ n, info.dest ≠ .sym n)
    (ctx : FnCtx) {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {n : Nat}
    {Q : Arm.ArmState → Prop}
    (hQ : ∀ t, Q t → CallPc (L.A g).fa (L.A g).base (Arm.r .PC t) →
      (∀ f, MaskedReg f → Arm.r f t = Arm.r f (R n)) ∧
        ∀ a, StackBelow (κ M g) (spv t) a → t.mem a = P n a) :
    CallSoundCtlGP Q F (κ M g) G s0 (CallAt (L.A g).fa (L.A g).base) (callExec (L.hooks M))
      (csemV (GotV (L.A g).vcp) F ctx (L.XPR κ M g F P R n)) (.call info) .next := by
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
  -- the target register: an allocatable X register
  obtain ⟨n0, rfl, hn0, -⟩ : ∃ n, r0 = .x n ∧ n < 29 ∧ n ≠ 16 := by
    have hmem : (tgtOp tv, Loc.reg r0) ∈
        (((tgtOp tv :: (retOps Lu ++ callDefOps Ld)).toArray).zip (regs.map Loc.reg)).toList := by
      simp [Array.toList_zip, Array.toList_map, hregs0]
    obtain ⟨n, hn, h29, h16, -⟩ := locOk_int (hloc _ hmem).1
    exact ⟨n, hn, h29, h16⟩
  have hsem0 := hsem
  rw [call_useVals_reg hregs0] at hsem
  -- the allocated call: `blr x n0`
  obtain ⟨r1, us', ds', hr1, rfl⟩ := assign_call_reg hasg
  have h0 : regs[0]? = some (.x n0) := by
    rw [← Array.getElem?_toList, hregs0]; rfl
  rw [h0] at hr1
  cases hr1
  -- the target the machine reads
  have hc := hL.compiled g hg
  obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hc.layout
  have htgt : blrTarget t = some (lo64 (regVal t (.x n0))) := by
    obtain ⟨j, x, tt, hj, hx, hpc⟩ := hP
    simp only [MInst.callInsn?, Option.some.injEq] at hx
    subst hx
    rw [lo64_regVal_x]
    exact blrTarget_of hc.layout hlm hj hn0 hpc
      (fun k wd hk => hL.imgCode g hg t (fun a ha => (hG a (himgG a ha)).trans (himgS a ha)) k wd hk)
  -- the external semantics' call
  obtain ⟨o, hx, hout⟩ : ∃ o, (L.XPR κ M g F P R n).call none
      (regVal t (.x n0) :: Lu.map (fun q => regVal t q.2)) w = some (o, w') ∧
      outs = o.take (callDefs Ld).length := by
    simp only [csem, Option.map_eq_some_iff, Prod.mk.injEq] at hsem
    obtain ⟨⟨o, w2⟩, hx, rfl, rfl, -⟩ := hsem
    exact ⟨o, hx, rfl⟩
  cases hs : symCallee L.Xb L.P (lo64 (regVal t (.x n0))) with
  | none =>
    -- no function of `P` at the target: the base's contract
    have hb : (blrTarget t).bind (symCallee L.Xb L.P) = none := by rw [htgt]; exact hs
    rw [L.XPR_none hs] at hx
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
    rw [L.XPR_ind hs] at hx
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
        L.progOsCoreXPR hL hκ ih hg hh (.inr (.inr ⟨hh, hdecl.1.1⟩)) himgF himgG himgS hLu hLd rfl
          (call_defs_reg hregs0) hK hG
          (hL.raBlr g hg _ hsite hreg h hh hdecl.1.1 _ hP.callPc) hsw (hQ t hQt hP.callPc).1
          (hQ t hQt hP.callPc).2 hx ⟨_, hout⟩⟩
    · cases hx

theorem XPR_base {M : Nat} {g : Clif.Function} {F : BitVec 64 → Prop}
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {n : Nat} {m : String}
    (hn : L.P.func? m = none) (uses : List CV) (w : Arm.ArmState) :
    (L.XPR κ M g F P R n).call (some m) uses w = L.Xb.call (some m) uses w := by
  simp [XPR, hn]

theorem progXPR_ext {M : Nat} {F : BitVec 64 → Prop} {h : Clif.Function}
    {uses : List CV} {Pn : BitVec 64 → BitVec 8} {Sn w : Arm.ArmState} {outs : List CV}
    {w' : Arm.ArmState} (hx : L.progXPR κ M F h uses Pn Sn w = some (outs, w')) :
    Arm.r .ERR w' = .None ∧ w'.program = w.program := by
  have := L.progX_ext hx
  exact ⟨this.1, this.2.trans (L.program_worldPR h Pn Sn w)⟩

theorem XPR_ext (hL : L.Ok) {M : Nat} {g : Clif.Function} {F : BitVec 64 → Prop}
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {n : Nat} {d : Option String}
    {uses : List CV} {w : Arm.ArmState} {outs : List CV} {w' : Arm.ArmState}
    (hx : (L.XPR κ M g F P R n).call d uses w = some (outs, w'))
    (herr : Arm.r .ERR w = .None) : Arm.r .ERR w' = .None ∧ w'.program = w.program := by
  cases d with
  | some m =>
    cases hpf : L.P.func? m with
    | none =>
      rw [L.XPR_base hpf] at hx
      exact hL.baseExt _ _ _ _ _ (.inr ⟨m, rfl, hpf⟩) hx herr
    | some h =>
      rw [L.XPR_prog hpf] at hx
      exact L.progXPR_ext hx
  | none =>
    cases uses with
    | nil => exact hL.baseExt _ _ _ _ _ (.inl rfl) hx herr
    | cons u args =>
      cases hs : symCallee L.Xb L.P (lo64 u) with
      | none =>
        rw [L.XPR_none hs] at hx
        exact hL.baseExt _ _ _ _ _ (.inl rfl) hx herr
      | some h =>
        rw [L.XPR_ind hs] at hx
        split at hx
        · exact L.progXPR_ext hx
        · cases hx

/-- **`calleeOk` for call number `n` with both prophecies, on `ThmPDE`**: the call contract of an
activation of `g` for `XPR … n`, at the call states `Q` (masked registers of `R n`, `P n` below
`sp`). -/
theorem calleeOkP (hL : L.Ok) [L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPDE κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {ra : BitVec 64} {s w₀ : Arm.ArmState}
    (he : L.MachEntry κ M g F G ra s w₀)
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {n : Nat}
    {Q : Arm.ArmState → Prop}
    (hQ : ∀ t, Q t → CallPc (L.A g).fa (L.A g).base (Arm.r .PC t) →
      (∀ f, MaskedReg f → Arm.r f t = Arm.r f (R n)) ∧
        ∀ a, StackBelow (κ M g) (spv t) a → t.mem a = P n a) :
    CalleeOkGP Q F (κ M g) G s (CallAt (L.A g).fa (L.A g).base) (L.XPR κ M g F P R n) (L.hooks M)
      (L.A g).vcp.CallSite (GotV (L.A g).vcp) where
  os ctx info hsite := by
    cases hd : info.dest with
    | reg r =>
      exact L.progOsRegP hL hκ ih hg he.imgF he.imgG he.imgS hsite (fun n => by rw [hd]; simp) ctx
        hQ
    | sym n =>
    have hdest := hd
    cases hpf : L.P.func? n with
    | some h => exact L.progOsP hL hκ ih hg he.imgF he.imgG he.imgS ⟨hsite, n, hdest, hpf⟩ ctx hQ
    | none =>
      have hb : L.BaseDest (destOf info) := .inr ⟨n, by simp [destOf, hdest], hpf⟩
      have h0 := hL.baseOs g hg info hsite hb F (κ M g) G s (CallAt (L.A g).fa (L.A g).base) ctx
      intro t _ h1 h2 h3 c wh ops regs i' w outs w' hops hst hasg h4 hsw hal herr hsem
      obtain ⟨d, us, ds⟩ := info
      simp only at hdest
      subst hdest
      have hsem' : csem F ctx L.Xb (.call ⟨.sym n, us, ds⟩) (useVals ops regs t) w =
          some (outs, w', .next) := by
        rw [← csemV_sub hsem]; simp [csem, L.XPR_base hpf]
      obtain ⟨s', hex, rest⟩ :=
        h0 t h1 h2 h3 c wh ops regs i' w outs w' hops hst hasg h4 hsw hal herr hsem'
      refine ⟨s', ?_, rest⟩
      obtain ⟨us', ds', rfl⟩ := assign_call_sym hasg
      simp only [callExec] at hex ⊢
      rw [L.hooks_base (.inr ⟨n, rfl, hpf⟩) t (fun h => by cases h)]
      exact hex
  pc d u herr hal := by
    cases d with
    | none =>
      cases hb : (blrTarget u).bind (symCallee L.Xb L.P) with
      | none =>
        rw [L.hooks_base (.inl rfl) u (fun _ => hb)]; exact hL.basePc _ _ (.inl rfl) herr hal
      | some h => rw [L.hooks_none hb]; exact (L.pcall_pc M h u).2
    | some n =>
      cases hpf : L.P.func? n with
      | none =>
        rw [L.hooks_base (.inr ⟨n, rfl, hpf⟩) u (fun h => by cases h)]
        exact hL.basePc _ _ (.inr ⟨n, rfl, hpf⟩) herr hal
      | some h => rw [L.hooks_some hpf]; exact (L.pcall_pc M h u).2
  ext _ _ _ _ _ hx herr := L.XPR_ext hL hx herr

/-- **`calleeTryOk` for call number `n` with both prophecies, on `ThmPDE`**, at the call states
`Q`. -/
theorem calleeTryOkP (hL : L.Ok) [L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPDE κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {ra : BitVec 64} {s w₀ : Arm.ArmState}
    (he : L.MachEntry κ M g F G ra s w₀)
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {n : Nat}
    {Q : Arm.ArmState → Prop}
    (hQ : ∀ t, Q t → CallPc (L.A g).fa (L.A g).base (Arm.r .PC t) →
      (∀ f, MaskedReg f → Arm.r f t = Arm.r f (R n)) ∧
        ∀ a, StackBelow (κ M g) (spv t) a → t.mem a = P n a) :
    CalleeTryOkGP Q F (κ M g) G s (CallAt (L.A g).fa (L.A g).base) (L.XPR κ M g F P R n)
      (L.hooks M) (L.A g).vcp.TrySite (GotV (L.A g).vcp) := by
  intro ctx info ti hsite
  cases hd : info.dest with
  | sym n =>
    have hdest := hd
    cases hpf : L.P.func? n with
    | some h =>
      exact calleeTryOkGP_of_call (S := fun i t => i = info ∧ t = ti)
        (fun ctx' i t ⟨e1, _⟩ => e1 ▸ (L.calleeOkP hL hκ ih hg he hQ).os ctx' info hsite.callSite)
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
        rw [← csemV_sub hsem]; simp [csem, L.XPR_base hpf]
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
    have hopsC : (MInst.call ⟨.reg (.vreg tv .int), retPairs Lu, callDefs Ld⟩).operands = .ok ops := by
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
        (fun k wd hk => hL.imgCode g hg t (fun a ha => (hG a (he.imgG a ha)).trans (he.imgS a ha)) k wd hk)
    have huv := call_useVals_reg (tv := tv) (s := t) hregs0
    cases hs : symCallee L.Xb L.P (lo64 (regVal t (.x n0))) with
    | none =>
      have hb : (blrTarget t).bind (symCallee L.Xb L.P) = none := by rw [htgt]; exact hs
      have hsem' : csem F ctx L.Xb (.tryCall ⟨.reg (.vreg tv .int), retPairs Lu, callDefs Ld⟩ ti)
          (useVals (tgtOp tv :: (retOps Lu ++ callDefOps Ld)).toArray regs t) w =
          some (outs, w', .goto ti.handlers.length) := by
        rw [← csemV_sub hsem, huv]; simp [csem, L.XPR_none hs]
      have hex' : callExec L.Hb (.tryCall ⟨.reg (.x n0), us', ds'⟩ ti) t = some s' := by
        simp only [callExec] at hex ⊢
        rw [← L.hooks_base (M := M) (.inl rfl) t (fun _ => hb)]
        exact hex
      exact hL.baseTry g hg F ctx _ ti ⟨hsite, .inl rfl⟩ c wh _ regs _ t w outs w' s' hops hst
        hasg hsw hal herr hsem' hex'
    | some h =>
      exact calleeTryP_at ((L.calleeOkP hL hκ ih hg he hQ).os ctx _ hsite.callSite)
        (fun _ _ h => callAt_tryCall_call h) hcl hQt hK hD hG hops hst hasg hP hsw hal herr hsem hex

end LinkSys

end E2E
