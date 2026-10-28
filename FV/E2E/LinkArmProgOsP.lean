import FV.E2E.LinkArmProgCallP
import FV.E2E.LinkArmProphReg
import FV.E2E.RegLevelCallN

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
* `progOsP`.
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
  let W := L.worldPR κ M h (P n) (R n) w
  have hx : L.progX κ M F h (Lu.map (fun q => regVal t q.2)) W = some (outs, w') := by
    simp only [csem, Option.map_eq_some_iff, Prod.mk.injEq] at hsem
    obtain ⟨⟨o, w2⟩, hx, rfl, rfl, -⟩ := hsem
    rw [L.XPR_prog hpf] at hx
    exact hx
  obtain ⟨hmskQ, hrgnQ⟩ := hQ t hQt hP.callPc
  obtain ⟨us', ds', rfl⟩ := assign_call_sym hasg
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
  have hcal : L.Callee g h := .inl ⟨_, hsite⟩
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
  exact ⟨L.pcall M h t, by simp only [callExec, hal, ↓reduceIte, L.hooks_some hpf],
    L.progOsCoreP hL hκ ih hg hh hcal himgF himgG himgS hLu hLd rfl (call_defs hregs) hK hG
      (hL.raCall g hg _ h hsite _ hP.callPc) hsw' hmsk hrgn hx⟩

end LinkSys

end E2E
