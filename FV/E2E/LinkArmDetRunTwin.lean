import FV.E2E.LinkArmLockRet
import FV.E2E.LinkArmThmPRBG

/-!
# The twin runs of the determinism step from the lock (SEM1 #537, #713)

The determinism step `DetRunPRBCRU` and the call twins need `TwinCE` (second, canonical) of two
activations locked to the return (`LockRet`). One level of `TwinCE` follows from the lock
(`twinBaseCE_of_lock`), the nested callee twins at the call states from the call twins one level
down (`CallTwinCET`) applied at the canonical call data of both call states, composed by
`TwinCE.trans`/`symm`. Finding (#713): at the second run's call state `u'` the callee's
`CallerOk` needs `u'`'s memory outside `F` and its code image; the backend two-run theorem now
exports both (`backend_twoRunLERWZIUPF_eitherK`: the lock set inside `F ∪ D`, `RL.GoodK`).

* `callPc_of_insnAt`, `callPc_of_callsTo`, **`callsTo_iff_of_lockB`**, `twinState_of_lockB`,
  **`twinBaseCE_of_lockB`** (`callsTo_iff_of_lock`, `twinState_of_lock`, `twinBaseCE_of_lock`
  with the code image asked only at call lines);
* **`callerOk_of_lock`** (a state locked with a compatible caller state by a set inside `F`
  avoiding the callee region, holding the code image, is compatible too);
* **`twinCE_of_lockK`** (`TwinCE` of two runs locked up to their shared return, from the
  canonical call data at the first run's call states);
* **`canonCallTwin`** (the canonical activation's call data at its call states, from the
  single-run pipeline and the prefix theorem as in `thmPRBG_ofR`: the code image, the body `sp`,
  the callee, and the nested twins with any locked state by `CallTwinCET`).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- **A `bl`/`blr` found by `insnAt` is at a call line.** -/
theorem callPc_of_insnAt {fa : FnAsm} {base pc : BitVec 64} {i : Insn}
    (h : insnAt fa base pc = some i) (hi : (∃ n, i = .bl n) ∨ ∃ r, i = .blr r) :
    CallPc fa base pc := by
  obtain ⟨j, t, hj, hpc⟩ := insnAt_line_of h
  exact ⟨j, i, t, hj, hi, hpc.symm⟩

/-- **A register other than an `x30` alias has equal values in states equal but for `x30`/pc.** -/
theorem regVal_eq_of_ne30 {u v : Arm.ArmState}
    (h : ∀ f, f ≠ .PC → f ≠ .GPR 30#5 → Arm.r f u = Arm.r f v) {p : Reg}
    (hp : ∀ n, p = .x n → n < 30) : regVal u p = regVal v p := by
  cases p with
  | x n =>
    have hn := hp n rfl
    simp only [regVal]
    rw [h _ (by simp) (fun e => by
      have := congrArg (fun f => match f with | Arm.StateField.GPR i => i.toNat | _ => 0) e
      simp [rnum_toNat (show n < 32 by omega)] at this; omega)]
  | v n => simp only [regVal]; rw [h _ (by simp) (by simp)]
  | _ => rfl

namespace LinkSys

variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

/-- **A program call is at a call line.** -/
theorem callPc_of_callsTo {g : Clif.Function} {u : Arm.ArmState} {h : Clif.Function}
    (hc : L.CallsTo g u h) : CallPc (L.A g).fa (L.A g).base (Arm.r .PC u) := by
  rcases hc with ⟨n, hn, -⟩ | ⟨⟨x, hx⟩, -⟩
  · exact callPc_of_insnAt hn (.inl ⟨n, rfl⟩)
  · exact callPc_of_insnAt hx (.inr ⟨x, rfl⟩)

/-- **`callsTo_iff_of_lock` with the code image at call lines only.** -/
theorem callsTo_iff_of_lockB (hL : L.Ok) {g : Clif.Function} (hg : g ∈ L.P.funcs)
    (hc : (L.A g).fa.blrLow = true) {Z : BitVec 64 → Prop} {u u' : Arm.ArmState}
    (hlk : StEqOutX Z u u')
    (himg : CallPc (L.A g).fa (L.A g).base (Arm.r .PC u) → ∀ a, L.Img a → u.mem a = L.imgMem a)
    (himg' : CallPc (L.A g).fa (L.A g).base (Arm.r .PC u) → ∀ a, L.Img a → u'.mem a = L.imgMem a)
    (h : Clif.Function) : L.CallsTo g u h ↔ L.CallsTo g u' h := by
  have hpc : Arm.r .PC u = Arm.r .PC u' := hlk.1 .PC (by simp)
  have hb : ∀ x, insnAt (L.A g).fa (L.A g).base (Arm.r .PC u) = some (.blr x) →
      blrTarget u = blrTarget u' := by
    intro x hx
    have hcp := callPc_of_insnAt hx (.inr ⟨x, rfl⟩)
    obtain ⟨j, tt, hj, hpj⟩ := insnAt_line_of hx
    have hcc := hL.compiled g hg
    obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hcc.layout
    exact blrTarget_eq_of_lock hcc.layout hlm hc hlk hj hpj.symm
      (fun k w hk => hL.imgCode g hg u (himg hcp) k w hk)
      (fun k w hk => hL.imgCode g hg u' (himg' hcp) k w hk)
  unfold CallsTo
  rw [← hpc]
  constructor
  · rintro (h1 | ⟨⟨x, hi⟩, ht⟩)
    · exact .inl h1
    · exact .inr ⟨⟨x, hi⟩, by rw [← hb x hi]; exact ht⟩
  · rintro (h1 | ⟨⟨x, hi⟩, ht⟩)
    · exact .inl h1
    · exact .inr ⟨⟨x, hi⟩, by rw [hb x hi]; exact ht⟩

/-- **`twinState_of_lock` with the code image at call lines only.** -/
theorem twinState_of_lockB (hL : L.Ok) {g : Clif.Function} (hg : g ∈ L.P.funcs)
    (hc : (L.A g).fa.blrLow = true) {K : Nat} {c : BitVec 64} (hroom : K ≤ c.toNat)
    {Z : BitVec 64 → Prop} {u u' : Arm.ArmState}
    (hK : ∀ h, L.CallsTo g u h → frameDrop (L.A h).af ≤ K)
    (hlk : StEqOutX Z u u') (hZ : ∀ a, StackBelow K c a → ¬ Z a)
    (himg : CallPc (L.A g).fa (L.A g).base (Arm.r .PC u) → ∀ a, L.Img a → u.mem a = L.imgMem a)
    (himg' : CallPc (L.A g).fa (L.A g).base (Arm.r .PC u) → ∀ a, L.Img a → u'.mem a = L.imgMem a)
    (hsp : ∀ h, L.CallsTo g u h → spv u = c) (hcal : ∀ h, L.CallsTo g u h → L.Callee g h) :
    Arm.r .PC u = Arm.r .PC u' ∧ spv u = spv u' ∧
      (∀ h, L.CallsTo g u h ↔ L.CallsTo g u' h) ∧
      ∀ h, L.CallsTo g u h → ∀ a, L.SlotByte h (spv u) a →
        u.mem (BitVec.ofNat 64 a) = u'.mem (BitVec.ofNat 64 a) := by
  refine ⟨hlk.1 .PC (by simp), hlk.1 _ (by simp), L.callsTo_iff_of_lockB hL hg hc hlk himg himg',
    fun h hct a ha => ?_⟩
  rw [hsp h hct] at ha
  have hKh := hK h hct
  exact L.slotByte_eq_of_lock hL hg (hcal h hct) hKh (by omega)
    (fun b hb => hlk.2.2 b (hZ b hb)) ha

/-- **`twinBaseCE_of_lock` with the code image at call lines only.** -/
theorem twinBaseCE_of_lockB (hL : L.Ok) {M : Nat} {g : Clif.Function} (hg : g ∈ L.P.funcs)
    (hc : (L.A g).fa.blrLow = true) {K : Nat} {c : BitVec 64} (hroom : K ≤ c.toNat)
    {s s₀ : Arm.ArmState} {T : Nat}
    (hK : ∀ i < T, ∀ h, L.CallsTo g (runX (L.mach M g) i s) h → frameDrop (L.A h).af ≤ K)
    (hlk : ∀ i < T, ∃ Z, StEqOutX Z (runX (L.mach M g) i s) (runX (L.mach M g) i s₀) ∧
      ∀ a, StackBelow K c a → ¬ Z a)
    (himg : ∀ i < T, CallPc (L.A g).fa (L.A g).base (Arm.r .PC (runX (L.mach M g) i s)) →
      ∀ a, L.Img a → (runX (L.mach M g) i s).mem a = L.imgMem a)
    (himg₀ : ∀ i < T, CallPc (L.A g).fa (L.A g).base (Arm.r .PC (runX (L.mach M g) i s)) →
      ∀ a, L.Img a → (runX (L.mach M g) i s₀).mem a = L.imgMem a)
    (hsp : ∀ i < T, ∀ h, L.CallsTo g (runX (L.mach M g) i s) h → spv (runX (L.mach M g) i s) = c)
    (hcal : ∀ i < T, ∀ h, L.CallsTo g (runX (L.mach M g) i s) h → L.Callee g h)
    (hnr : ∀ i < T, ¬ L.RetAt g s (runX (L.mach M g) i s) ∧
      ¬ L.RetAt g s₀ (runX (L.mach M g) i s₀))
    (hr : L.RetAt g s (runX (L.mach M g) T s) ∧ L.RetAt g s₀ (runX (L.mach M g) T s₀)) :
    L.TwinBaseCE M g s s₀ := by
  refine ⟨?_, ?_⟩
  · intro i hi
    rcases Nat.lt_trichotomy i T with h | rfl | h
    · obtain ⟨n1, n2⟩ := hnr i h
      obtain ⟨Z, hz, hZ⟩ := hlk i h
      exact ⟨⟨fun e => absurd e n1, fun e => absurd e n2⟩, fun _ =>
        L.twinState_of_lockB hL hg hc hroom (hK i h) hz hZ (himg i h) (himg₀ i h) (hsp i h)
          (hcal i h)⟩
    · exact ⟨⟨fun _ => hr.2, fun _ => hr.1⟩, fun hn => absurd hr.1 hn⟩
    · exact absurd hr.1 (hi T h)
  · intro i hi
    rcases Nat.lt_trichotomy i T with h | rfl | h
    · obtain ⟨Z, hz, -⟩ := hlk i h
      rw [hz.1 .ERR (by simp)]
    · exact ⟨fun _ => hr.2.2.1, fun _ => hr.1.2.1⟩
    · exact absurd hr.1 (hi T h)

/-- **A state locked with a compatible caller state is compatible** (module doc): the lock set
inside `F` and outside the callee region `StackBelow K (spv W)`, the code image held. -/
theorem callerOk_of_lock (hL : L.Ok) {F : BitVec 64 → Prop} {h : Clif.Function}
    (hh : h ∈ L.P.funcs) {uses : List CV} {W u u' : Arm.ArmState}
    (hok : L.CallerOk F h uses W u)
    (hmsk : ∀ f, Masked f → f ≠ .PC → f ≠ .GPR 30#5 → Arm.r f u = Arm.r f (L.canon h uses W))
    {K : Nat} (hrgn : ∀ a, StackBelow K (spv W) a → u.mem a = (L.canon h uses W).mem a)
    {Z : BitVec 64 → Prop} (hz : StEqOutX Z u u') (hZF : ∀ a, Z a → F a)
    (hZd : ∀ a, StackBelow K (spv W) a → ¬ Z a)
    (himg : ∀ a, L.Img a → u'.mem a = L.imgMem a) :
    L.CallerOk F h uses W u' ∧
      (∀ f, Masked f → f ≠ .PC → f ≠ .GPR 30#5 → Arm.r f u' = Arm.r f (L.canon h uses W)) ∧
      (∀ a, StackBelow K (spv W) a → u'.mem a = (L.canon h uses W).mem a) := by
  have hr : ∀ f, f ≠ .GPR 30#5 → Arm.r f u' = Arm.r f u := fun f hf => (hz.1 f hf).symm
  have harg := (hL.argRegs h hh).2.1
  refine ⟨⟨⟨fun f hf => ?_, fun a ha => ?_, hz.2.1.symm.trans hok.world.2.2⟩, himg,
    fun r hr' => ?_, ?_⟩, fun f hf hpc h30 => (hr f h30).trans (hmsk f hf hpc h30),
    fun a ha => ?_⟩
  · have h30 : f ≠ .GPR 30#5 := fun e => hf (e ▸ by simp [Masked])
    rw [hr f h30]; exact hok.world.1 f hf
  · rw [← hz.2.2 a (fun hz' => ha (hZF a hz'))]; exact hok.world.2.1 a ha
  · rw [← hok.regs r hr']
    refine regVal_eq_of_ne30 (fun f _ h30 => hr f h30) fun n hn => ?_
    have hA := harg r hr'
    subst hn
    simp only [Reg.isArgReg, decide_eq_true_eq] at hA
    omega
  · rw [← hz.1 .PC (by simp)]; exact hok.ra
  · rw [← hz.2.2 a (hZd a ha)]; exact hrgn a ha

/-- **The twin runs from the lock up to the shared return** (module doc): `TwinCE M g s₀ s` of
two runs locked by sets inside `F` avoiding the callees' dead stack `StackBelow K c`, the second
run holding the code image at its call lines, from the first run's call data (`hcan`: its code
image and `sp = c` at its call lines, and at its program calls the callee and the nested twins
with every state locked with it). -/
theorem twinCE_of_lockK (hL : L.Ok) {M : Nat} {g : Clif.Function} (hg : g ∈ L.P.funcs)
    (hc : (L.A g).fa.blrLow = true) {K : Nat} {c : BitVec 64} (hroom : K ≤ c.toNat)
    {F : BitVec 64 → Prop}
    {s₀ s : Arm.ArmState} {n₀ : Nat}
    (hlk : ∀ i < n₀, ∃ Z, StEqOutX Z (runX (L.mach M g) i s₀) (runX (L.mach M g) i s) ∧
      (∀ a, Z a → F a) ∧ ∀ a, StackBelow K c a → ¬ Z a)
    (himg' : ∀ i < n₀, CallPc (L.A g).fa (L.A g).base (Arm.r .PC (runX (L.mach M g) i s)) →
      ∀ a, L.Img a → (runX (L.mach M g) i s).mem a = L.imgMem a)
    (hcan : ∀ i < n₀, CallPc (L.A g).fa (L.A g).base (Arm.r .PC (runX (L.mach M g) i s₀)) →
      (∀ a, L.Img a → (runX (L.mach M g) i s₀).mem a = L.imgMem a) ∧
      spv (runX (L.mach M g) i s₀) = c ∧
      ∀ h, L.CallsTo g (runX (L.mach M g) i s₀) h → L.Callee g h ∧ frameDrop (L.A h).af ≤ K ∧
        ∀ M', M = M' + 1 → ∀ (Z : BitVec 64 → Prop) (u' : Arm.ArmState),
          StEqOutX Z (runX (L.mach M g) i s₀) u' → (∀ a, Z a → F a) →
          (∀ a, StackBelow K c a → ¬ Z a) → (∀ a, L.Img a → u'.mem a = L.imgMem a) →
          L.TwinCE M' h (enterAt (L.A h) (runX (L.mach M g) i s₀)) (enterAt (L.A h) u'))
    (hnr : ∀ i < n₀, ¬ L.RetAt g s₀ (runX (L.mach M g) i s₀) ∧
      ¬ L.RetAt g s (runX (L.mach M g) i s))
    (hr : L.RetAt g s₀ (runX (L.mach M g) n₀ s₀) ∧ L.RetAt g s (runX (L.mach M g) n₀ s)) :
    L.TwinCE M g s₀ s := by
  have hpc : ∀ i < n₀, Arm.r .PC (runX (L.mach M g) i s₀) = Arm.r .PC (runX (L.mach M g) i s) :=
    fun i hi => let ⟨_, hz, _⟩ := hlk i hi; hz.1 .PC (by simp)
  have hb : L.TwinBaseCE M g s₀ s := L.twinBaseCE_of_lockB hL hg hc hroom
    (fun i hi h hct => ((hcan i hi (L.callPc_of_callsTo hct)).2.2 h hct).2.1)
    (fun i hi => let ⟨Z, hz, _, hZ⟩ := hlk i hi; ⟨Z, hz, hZ⟩)
    (fun i hi hcp => (hcan i hi hcp).1)
    (fun i hi hcp => himg' i hi (by rw [← hpc i hi]; exact hcp))
    (fun i hi _ hct => (hcan i hi (L.callPc_of_callsTo hct)).2.1)
    (fun i hi h hct => ((hcan i hi (L.callPc_of_callsTo hct)).2.2 h hct).1)
    hnr hr
  cases M with
  | zero => exact hb
  | succ M' =>
    refine ⟨hb, fun i hi h hct => ?_⟩
    have hin : i < n₀ := Nat.lt_of_not_le fun hle => hi n₀ (by omega) hr.1
    obtain ⟨Z, hz, hZF, hZ⟩ := hlk i hin
    have hcp := L.callPc_of_callsTo hct
    exact ((hcan i hin hcp).2.2 h hct).2.2 M' rfl Z _ hz hZF hZ
      (himg' i hin (by rw [← hpc i hin]; exact hcp))

set_option maxHeartbeats 8000000 in
/-- **The canonical activation's call data at its call lines** (module doc). -/
theorem canonCallTwin (hL : L.Ok) [hR : L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1)) (hdet : 0 < M → L.DetPRBRU κ (M - 1))
    (hret : L.RetOkPRB κ M) (h2 : L.Stage2PRBZSE κ M) (htw : 0 < M → L.CallTwinCET κ M)
    {g : Clif.Function} (hg : g ∈ L.P.funcs) {F : BitVec 64 → Prop} {vals : List Clif.Val}
    {cs : Clif.State} {w₀ : Arm.ArmState} {fuel : Nat} {rvals : List Clif.Val} {cm' : Clif.Mem}
    {ini : Clif.SlotInit} {G : BitVec 64 → Prop} {ra : BitVec 64} {s : Arm.ArmState}
    (hWE : L.WorldEntryB κ M g F vals cs w₀ ini)
    (hME : L.MachEntryPR κ M g F G ra s w₀ (prophOf (L.mach M g) (L.A g).fa (L.A g).base s)
      (prophStOf (L.mach M g) (L.A g).fa (L.A g).base s))
    (hra : RaOk (L.A g) (ra - 4)) (htab : L.TableOfE M g s ini)
    (hrun : Clif.runLoop (L.envR M g) L.P.bare fuel cs = .returned rvals cm') :
    ∀ i, (∀ j ≤ i, ¬ RetL (L.A g) s (runX (L.mach M g) j s)) →
      CallPc (L.A g).fa (L.A g).base (Arm.r .PC (runX (L.mach M g) i s)) →
      (∀ a, L.Img a → (runX (L.mach M g) i s).mem a = L.imgMem a) ∧
      spv (runX (L.mach M g) i s) = spv s - BitVec.ofNat 64 (frameDrop (L.A g).af) ∧
      ∀ h, L.CallsTo g (runX (L.mach M g) i s) h → L.Callee g h ∧ frameDrop (L.A h).af ≤ κ M g ∧
        ∀ M', M = M' + 1 → ∀ (Z : BitVec 64 → Prop) (u' : Arm.ArmState),
          StEqOutX Z (runX (L.mach M g) i s) u' → (∀ a, Z a → F a) →
          (∀ a, StackBelow (κ M g) (spv s - BitVec.ofNat 64 (frameDrop (L.A g).af)) a → ¬ Z a) →
          (∀ a, L.Img a → u'.mem a = L.imgMem a) →
          L.TwinCE M' h (enterAt (L.A h) (runX (L.mach M g) i s)) (enterAt (L.A h) u') := by
  have hc := hL.compiled g hg
  have hI : Clif.LInv (L.P.only g) cs := runInv_entry (by simp [Clif.Program.only]) hWE.clif
  have hJ : L.ActInvB g (spv w₀) cs := ⟨hI, hWE.clif.callers, fun hN => ⟨ini, hWE.place hN⟩⟩
  have hrun' : Clif.runLoop (L.envOfB M g (spv w₀)) L.P.bare fuel cs = .returned rvals cm' := by
    rw [L.runLoop_envOfB hL hg fuel cs hJ]; exact hrun
  have hPf : ∀ f ∈ (L.P.only g).funcs, Clif.LinkFree f := fun f hf => by
    simp only [Clif.Program.only, List.mem_cons, List.not_mem_nil, or_false] at hf
    subst hf; exact hL.free f hg
  have hnrc : NoRetCall (L.envOfB M g (spv w₀)) L.P.bare cs :=
    noRetCall_of_linv hPf (fun _ h => by simp at h) hI
  have hpipe := backend_correct_world_pipelinePRGYNX (hL.subset g hg) hc
    (XI := L.XPBTI κ M g F (L.BP M g s) (L.RP M g s)) (syms := L.syms)
    (env := L.envOfB M g (spv w₀)) (K := κ M g) (F := F) (c := spv w₀) (hL.covered g hg)
    hnrc (hret g hg F vals cs w₀ ini hWE) (fun n b hn => hL.symOk n b hn) rfl hWE.clif hWE.rel
    hWE.args (trapsExplicit_of_returned hrun') fuel
  obtain ⟨_us, _outs, _wf, -, -, -, -, -, hall⟩ := hpipe.1 rvals cm' hrun'
  have he := hME.entryP.entry
  have hQ := L.callStPRB_q (κ := κ) (M := M) he.body.sp
  have hZS := h2 g hg F vals cs w₀ fuel rvals cm' ini G ra s hWE hME hra htab hrun
  have hX := hX_guardRXRI (Γ := ⟨F, L.syms, (L.A g).af.slotBase,
      (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩) (f := g) (c := spv w₀)
    (L.XPBTI κ M g F (L.BP M g s) (L.RP M g s)) hnrc (hret g hg F vals cs w₀ ini hWE)
  have hpc := (L.calleeOkPRBRLRU hL hκ ih hdet hg he (hQ 0)).pc
  have hAE : ActEntryPR (L.A g).vcp (L.A g).rf (L.A g).af (L.A g).fa (L.A g).fb (κ M g) F G
      (L.XPBTGY κ M g F (L.BP M g s) (L.RP M g s) (L.envOfB M g (spv w₀)) cs (spv w₀))
      (L.hooks M) (L.A g).base ra (κ M g) (spv w₀) (L.BP M g s) (L.RP M g s) s w₀ :=
    ⟨he.abi, he.stack, he.gfree, he.hF, hME.entryP.proph, hME.reg,
      fun n => L.calleeOkXPBTGZSRU hL hκ ih hdet hg he (hQ n) (hZS n),
      fun _ n => L.calleeTryOkXPBTGZSRU hL hκ ih hdet hg he (hQ n) (hZS n),
      fun ht _ => by
        have h0 := hL.baseTls g hg (hasTls_of_vcode_pipeline hc ht) F (κ M g)
        cases M <;> exact ⟨h0.pc, h0.seq, h0.flags⟩,
      he.body⟩
  obtain ⟨n, hret', -, -, hgood, u, hu, -⟩ := hall (L.hooks M) G (L.A g).base ra (κ M g) (spv w₀)
    (L.BP M g s) (L.RP M g s) s hAE
  change ReachN _ _ cs u (callsBefore (L.mach M g) (L.A g).fa (L.A g).base s n) at hu
  -- the call data at the machine's call states before the return (the prefix theorem)
  have hcall : ∀ i < n, CallPc (L.A g).fa (L.A g).base (Arm.r .PC (runX (L.mach M g) i s)) →
      ∃ (ins : MInst) (info : CallInfo) (w : Arm.ArmState) (r : List CV × Arm.ArmState)
        (ops : Array Operand) (regs : Array Reg) (i' : MInst) (cc : CheckCtx) (wh : String),
        (ins = .call info ∨ ∃ ti, ins = .tryCall info ti) ∧ (L.A g).vcp.CallSite info ∧
        ins.operands = .ok ops ∧ cc.checkStatic wh ops (regs.map .reg) ins.clobbers = .ok () ∧
        ins.assign regs = .ok i' ∧
        CallAt (L.A g).fa (L.A g).base (Arm.r .PC (runX (L.mach M g) i s)) i' ∧
        SameWorld F (runX (L.mach M g) i s) w ∧
        (∀ a, G a → (runX (L.mach M g) i s).mem a = s.mem a) ∧
        gotGuard (GotV (L.A g).vcp) L.Xb info (useVals ops regs (runX (L.mach M g) i s)) ∧
        (L.XPRBT κ M g F (L.BP M g s) (L.RP M g s)
          (callsBefore (L.mach M g) (L.A g).fa (L.A g).base s i)).call (callDest info)
            (useVals ops regs (runX (L.mach M g) i s)) w = some r ∧
        L.CallStPRB κ M g s w₀ (callsBefore (L.mach M g) (L.A g).fa (L.A g).base s i)
          (runX (L.mach M g) i s) := by
    intro i hi hcp
    have hjn : callsBefore (L.mach M g) (L.A g).fa (L.A g).base s i <
        callsBefore (L.mach M g) (L.A g).fa (L.A g).base s n := callsBefore_lt hcp hi
    obtain ⟨tl, -, hrtl, hcnl, -, -⟩ := reachN_call_at hu
      (callsBefore (L.mach M g) (L.A g).fa (L.A g).base s n - 1) (by omega)
    have hAE' : ActEntryPRN (L.A g).vcp (L.A g).rf (L.A g).af (L.A g).fa (L.A g).fb
        (κ M g) F G
        (L.XPBTGY κ M g F (L.BP M g s) (L.RP M g s) (L.envOfB M g (spv w₀)) cs (spv w₀))
        (L.hooks M) (L.A g).base ra (κ M g) (spv w₀) (L.BP M g s) (L.RP M g s) s w₀
        (callsBefore (L.mach M g) (L.A g).fa (L.A g).base s n - 1) :=
      ⟨he.abi, he.stack, he.gfree, he.hF, hME.entryP.proph, hME.reg,
        fun k _ => L.calleeOkXPBTGZSRU hL hκ ih hdet hg he (hQ k) (hZS k),
        fun _ k _ => L.calleeTryOkXPBTGZSRU hL hκ ih hdet hg he (hQ k) (hZS k),
        hpc,
        fun ht _ => by
          have h0 := hL.baseTls g hg (hasTls_of_vcode_pipeline hc ht) F (κ M g)
          cases M <;> exact ⟨h0.pc, h0.seq, h0.flags⟩,
        he.body⟩
    have hpre := prefix_relatedPRI_atEG (hL.subset g hg) hc (instCallsOne_all g)
      (tryCallsOne_all g) (hL.covered g hg) hnrc hX (fun n b hn => hL.symOk n b hn) rfl hWE.clif
      hWE.rel hWE.args (trapsExplicit_of_returned hrun') hrun' hAE' hrtl hcnl
    obtain ⟨uj, insj, infoj, usesj, wj, rj, ⟨ij, hij, hcbj, -⟩, hspj, hsitej, hcij, hCSj,
      hgdj, hxj, -⟩ := hpre (callsBefore (L.mach M g) (L.A g).fa (L.A g).base s i) (by omega)
    obtain ⟨-, -, hGuj, ccj, whj, opsj, regsj, i'j, hopsj, hstj', hasgj, hpij, hswj, halj, herrj,
      husesj⟩ := hsitej
    have hij' : runX (L.mach M g) ij s = uj := hij
    have hcpj : CallPc (L.A g).fa (L.A g).base (Arm.r .PC (runX (L.mach M g) ij s)) := by
      rw [hij']; exact hpij.callPc
    have hiji : ij = i := callIdx_unique hcpj hcp hcbj
    subst hiji hij' husesj
    have hcs : L.CallStPRB κ M g s w₀ (callsBefore (L.mach M g) (L.A g).fa (L.A g).base s ij)
        (runX (L.mach M g) ij s) :=
      ⟨onCallPR_of hME.entryP.proph hME.reg ⟨ij, rfl, rfl⟩, hspj⟩
    have hxP := L.XPBTGY_subZS hL (hZS (callsBefore (L.mach M g) (L.A g).fa (L.A g).base s ij))
      _ wj hcs hswj insj infoj hcij hCSj opsj regsj i'j hopsj ccj whj hstj' hasgj hpij halj herrj
      hgdj rj hxj
    exact ⟨insj, infoj, wj, rj, opsj, regsj, i'j, ccj, whj, hcij, hCSj, hopsj, hstj', hasgj, hpij,
      hswj, hGuj, hgdj, hxP, hcs⟩
  -- every state before the return whose step ends without error is before `n`
  have hbound : ∀ k, (∀ j ≤ k, ¬ RetL (L.A g) s (runX (L.mach M g) j s)) → k < n :=
    fun k hno => Nat.lt_of_not_le fun hle => hno n hle (L.retL_of_actRet he.abi hret')
  intro i hno hcp
  have hin : i < n := hbound i hno
  obtain ⟨ins, info, w, r, ops, regs, i', cc, wh, hci, hCS, hops, hst, hasg, hpi, hsw, hGu, hgd,
    hxP, hcs⟩ := hcall i hin hcp
  have himgU : ∀ a, L.Img a → (runX (L.mach M g) i s).mem a = L.imgMem a :=
    fun a ha => (hGu a (he.imgG a ha)).trans (he.imgS a ha)
  refine ⟨himgU, hcs.2, fun h hct => ?_⟩
  obtain ⟨hh, hcal, Lu, hLu, hrah, hx2, -⟩ := L.ansDecode hL hg hci hCS hops hst hasg hpi himgU
    hgd hxP hct
  have hcond := hx2
  unfold progXPRBT progXBT at hcond
  split at hcond
  · rename_i hcd
    obtain ⟨⟨hM, herrW, halW, hroomW, hdeadW, vals', cm, cs', rvals', cm'', ini', hmr, hargs,
      hsav, hpl, htabC, hinit, hrun2⟩, -⟩ := hcd
    have hbud := L.budget_step hκ hM hg hcal
    refine ⟨hcal, by omega, fun M' hM' Z u' hz hZF hZd himg' => ?_⟩
    subst hM'
    have hspW : spv (L.worldPR κ (M' + 1) h
        (L.BP (M' + 1) g s (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i))
        (L.RP (M' + 1) g s (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i)) w) =
        spv w :=
      L.r_worldPR_out (κ := κ) (M := M' + 1) h _ _ w (f := .GPR 31#5)
        (fun hm => by simp [MaskedReg, Masked] at hm)
    obtain ⟨hmskQ, hrgnQ⟩ := hQ _ _ hcs hcp
    obtain ⟨hcOk, hmsk, hrgn, -⟩ := L.callerFacts hL hκ hM hg hh hcal hWE.img hLu hsw himgU hrah
      hmskQ hrgnQ (fun a ha => hdeadW a (by rw [hspW]; exact ha))
    have hpf := func?_of_mem hL.names hh
    have hsu : spv w = spv (runX (L.mach (M' + 1) g) i s) := (hsw.1 _ (by simp [Masked])).symm
    have hZd' : ∀ a, StackBelow (frameDrop (L.A h).af + κ (M' + 1 - 1) h)
        (spv (L.worldPR κ (M' + 1) h
          (L.BP (M' + 1) g s (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i))
          (L.RP (M' + 1) g s (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i)) w))
        a → ¬ Z a := fun a ha => by
      have hsp' : spv (runX (L.mach (M' + 1) g) i s) =
          spv s - BitVec.ofNat 64 (frameDrop (L.A g).af) := hcs.2
      rw [hspW, hsu, hsp'] at ha
      exact hZd a (stackBelow_mono ha (L.budget_step hκ hM hg hcal))
    obtain ⟨hcOk', hmsk', hrgn'⟩ := L.callerOk_of_lock hL hh hcOk hmsk hrgn hz hZF hZd' himg'
    have t1 := htw hM h.name h hpf ⟨g, hg, hcal⟩ F hWE.img _ _ herrW halW hroomW hdeadW vals' cm
      cs' rvals' cm'' ini' hmr hargs hsav (fun hN => (hpl hN).1) (fun hN => (hpl hN).2)
      (L.tableOfE_of htabC) hinit hrun2 _ hcOk hmsk hrgn
    have t2 := htw hM h.name h hpf ⟨g, hg, hcal⟩ F hWE.img _ _ herrW halW hroomW hdeadW vals' cm
      cs' rvals' cm'' ini' hmr hargs hsav (fun hN => (hpl hN).1) (fun hN => (hpl hN).2)
      (L.tableOfE_of htabC) hinit hrun2 _ hcOk' hmsk' hrgn'
    exact TwinCE.trans L t1 (TwinCE.symm L t2)
  · cases hcond

end LinkSys

end E2E
