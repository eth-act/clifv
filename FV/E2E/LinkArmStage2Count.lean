import FV.E2E.LinkArmThmPRBROf
import FV.E2E.LinkArmCallCount
import FV.E2E.LinkArmCountStep

/-!
# The oracle at a call, and one call of the count invariant (SEM1 #537, #680 (3), stage 2 glue)

For an activation of `g` at depth `M' + 1` (`WorldEntryB`, `MachEntryPR` with the run's
prophecies, `RaOk`, `TableOf … ini`), at the machine's call state `runX … i s` reached with the
`Good` trace, at a call site (`CallAt`, under the GOT guard), in a world `w` of it:

* **`oracleAt_at`**: a program invocation of `h` behind the call (`ProgInst`'s facts), placed
  with `ini.adv x` where `x` is the caller table's count at `i`, has the oracle facts (`OracleAt`);
  the call's arguments are in `h`'s registers and the machine calls `h` (`callDecode`);
* **`countStep_prog`**: the count invariant (the table count at step `i` is the CLIF counter's
  advance `Σ_{k < callsBefore i} advAt k`) passes the call of a function of `P` (`callCount`,
  `adv_prog`, `advAt_eq`);
* **`countStep_base`**: it passes a call of a base extern (`tabUpTo_succ_base`, `adv_base`).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

namespace LinkSys

variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

/-- **The oracle facts at a program call** (module doc). -/
theorem oracleAt_at (hL : L.Ok) (hκ : L.Budget κ) {M' : Nat} (hdt : L.DetTabPRB κ (M' + 1))
    {g : Clif.Function} (hg : g ∈ L.P.funcs) {F : BitVec 64 → Prop} {vals : List Clif.Val}
    {cs : Clif.State} {w₀ : Arm.ArmState} {ini : Clif.SlotInit} {G : BitVec 64 → Prop}
    {ra : BitVec 64} {s : Arm.ArmState}
    (hWE : L.WorldEntryB κ (M' + 1) g F vals cs w₀ ini)
    (hME : L.MachEntryPR κ (M' + 1) g F G ra s w₀ (L.BP (M' + 1) g s) (L.RP (M' + 1) g s))
    (hra : RaOk (L.A g) (ra - 4)) (htab : L.TableOf (M' + 1) g s ini) {i : Nat}
    (htr : ∀ j < i, ¬ PostCall (L.A g).fa (L.A g).base (Arm.r .PC (runX (L.mach (M' + 1) g) j s)) ∨
      spOf (runX (L.mach (M' + 1) g) j s) = spv s - BitVec.ofNat 64 (frameDrop (L.A g).af))
    (hsp : spOf (runX (L.mach (M' + 1) g) i s) = spv s - BitVec.ofNat 64 (frameDrop (L.A g).af))
    {ins : MInst} {info : CallInfo} (hi : ins = .call info ∨ ∃ ti, ins = .tryCall info ti)
    (hS : (L.A g).vcp.CallSite info) {ops : Array Operand} {regs : Array Reg} {i' : MInst}
    (hops : ins.operands = .ok ops) {cc : CheckCtx} {wh : String}
    (hst : cc.checkStatic wh ops (regs.map .reg) ins.clobbers = .ok ())
    (hasg : ins.assign regs = .ok i')
    (hpi : CallAt (L.A g).fa (L.A g).base (Arm.r .PC (runX (L.mach (M' + 1) g) i s)) i')
    (herr : Arm.r .ERR (runX (L.mach (M' + 1) g) i s) = .None)
    (hgd : gotGuard (GotV (L.A g).vcp) L.Xb info (useVals ops regs (runX (L.mach (M' + 1) g) i s)))
    (hGu : ∀ a, G a → (runX (L.mach (M' + 1) g) i s).mem a = s.mem a)
    {w : Arm.ArmState} (hsw : SameWorld F (runX (L.mach (M' + 1) g) i s) w)
    {h : Clif.Function} (hh : h ∈ L.P.funcs) {args : List CV}
    (hd : callDest info = some h.name ∧ useVals ops regs (runX (L.mach (M' + 1) g) i s) = args ∨
      callDest info = none ∧ L.IndTo g h ∧ ∃ u0,
        useVals ops regs (runX (L.mach (M' + 1) g) i s) = u0 :: args ∧ lo64 u0 = L.Xb.sym h.name 0)
    (hcal : L.Callee g h) {vals' : List Clif.Val} {cm : Clif.Mem} {cs' : Clif.State}
    {rvals' : List Clif.Val} {cm'' : Clif.Mem}
    (hmrW : MemRel F L.syms cm (L.worldPR κ (M' + 1) h
      (L.BP (M' + 1) g s (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i))
      (L.RP (M' + 1) g s (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i)) w))
    (hargsW : ArgsAt h.sig vals' args (L.worldPR κ (M' + 1) h
      (L.BP (M' + 1) g s (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i))
      (L.RP (M' + 1) g s (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i)) w))
    (hsavW : StackArgsAvoid F h.sig vals' (L.worldPR κ (M' + 1) h
      (L.BP (M' + 1) g s (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i))
      (L.RP (M' + 1) g s (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i)) w))
    (hspw : spv w = spv w₀)
    (hinit : Clif.initState L.P h.name vals' cm = .ok cs')
    (hrun : L.crun (M' + 1) cs' = .returned rvals' cm'') {x : Nat}
    (hpl : L.NeedSlots → L.PlaceAtB cm (spv w₀) (ini.adv x))
    (hcnt : ∀ e, L.TabUpTo (M' + 1) g s ini.bytes ini.next i e → e = x) :
    ∃ Lu : List (Nat × Reg), Lu.map (·.2) = regLocs h.sig ∧
      args = Lu.map (fun q => regVal (runX (L.mach (M' + 1) g) i s) q.2) ∧
      L.CallsTo g (runX (L.mach (M' + 1) g) i s) h ∧
      RaOk (L.A h) (Arm.r .PC (runX (L.mach (M' + 1) g) i s)) ∧
      L.OracleAt κ (M' + 1) h (spv w₀) cm args (L.worldPR κ (M' + 1) h
        (L.BP (M' + 1) g s (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i))
        (L.RP (M' + 1) g s (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i)) w) := by
  have he := hME.entryP.entry
  have himgU : ∀ a, L.Img a → (runX (L.mach (M' + 1) g) i s).mem a = L.imgMem a :=
    fun a ha => (hGu a (he.imgG a ha)).trans (he.imgS a ha)
  obtain ⟨Lu, hLu, hargs, hct, hrah⟩ :=
    L.callDecode hL hg hi hS hops hst hasg hpi himgU hgd hh hd (argsAt_regLocs hargsW)
  have hcp := hpi.callPc
  obtain ⟨hmskQ, hrgnQ⟩ := L.callStPRB_q (κ := κ) (M := M' + 1) he.body.sp
    (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i) (runX (L.mach (M' + 1) g) i s)
    ⟨onCallPR_of hME.entryP.proph hME.reg ⟨i, rfl, rfl⟩, hsp⟩ hcp
  subst hargs
  exact ⟨Lu, hLu, rfl, hct, hrah, L.oracleAt_of_call hL hκ hdt hg he hra htab hWE.img hWE.room
    hWE.dead hWE.align htr hsp herr hcp (func?_of_mem hL.names hh) hcal hct hmskQ hrgnQ hLu hsw
    hspw himgU hrah hmrW hargsW hsavW hpl hcnt hinit hrun⟩

/-- **The count invariant passes a call of a function of `P`** (module doc). -/
theorem countStep_prog (hL : L.Ok) [hR : L.CrunOk] (hκ : L.Budget κ) (hN : L.NeedSlots)
    {M' : Nat} (ih : L.ThmPRBRL κ M') (hdet : L.DetPRB κ M') (hdt : L.DetTabPRB κ (M' + 1))
    {g : Clif.Function} (hg : g ∈ L.P.funcs) {F : BitVec 64 → Prop} {vals : List Clif.Val}
    {cs : Clif.State} {w₀ : Arm.ArmState} {ini : Clif.SlotInit} {G : BitVec 64 → Prop}
    {ra : BitVec 64} {s : Arm.ArmState}
    (hWE : L.WorldEntryB κ (M' + 1) g F vals cs w₀ ini)
    (hME : L.MachEntryPR κ (M' + 1) g F G ra s w₀ (L.BP (M' + 1) g s) (L.RP (M' + 1) g s))
    (hra : RaOk (L.A g) (ra - 4)) (htab : L.TableOf (M' + 1) g s ini) {i : Nat}
    (htr : ∀ j < i, ¬ PostCall (L.A g).fa (L.A g).base (Arm.r .PC (runX (L.mach (M' + 1) g) j s)) ∨
      spOf (runX (L.mach (M' + 1) g) j s) = spv s - BitVec.ofNat 64 (frameDrop (L.A g).af))
    (hsp : spOf (runX (L.mach (M' + 1) g) i s) = spv s - BitVec.ofNat 64 (frameDrop (L.A g).af))
    {ins : MInst} {info : CallInfo} (hi : ins = .call info ∨ ∃ ti, ins = .tryCall info ti)
    (hS : (L.A g).vcp.CallSite info) {ops : Array Operand} {regs : Array Reg} {i' : MInst}
    (hops : ins.operands = .ok ops) {cc : CheckCtx} {wh : String}
    (hst : cc.checkStatic wh ops (regs.map .reg) ins.clobbers = .ok ())
    (hasg : ins.assign regs = .ok i')
    (hpi : CallAt (L.A g).fa (L.A g).base (Arm.r .PC (runX (L.mach (M' + 1) g) i s)) i')
    (herr : Arm.r .ERR (runX (L.mach (M' + 1) g) i s) = .None)
    (hgd : gotGuard (GotV (L.A g).vcp) L.Xb info (useVals ops regs (runX (L.mach (M' + 1) g) i s)))
    (hGu : ∀ a, G a → (runX (L.mach (M' + 1) g) i s).mem a = s.mem a)
    {w : Arm.ArmState} (hsw : SameWorld F (runX (L.mach (M' + 1) g) i s) w)
    {h : Clif.Function} (hh : h ∈ L.P.funcs) {args : List CV}
    (hd : callDest info = some h.name ∧ useVals ops regs (runX (L.mach (M' + 1) g) i s) = args ∨
      callDest info = none ∧ L.IndTo g h ∧ ∃ u0,
        useVals ops regs (runX (L.mach (M' + 1) g) i s) = u0 :: args ∧ lo64 u0 = L.Xb.sym h.name 0)
    (hcal : L.Callee g h) {vals' : List Clif.Val} {cm : Clif.Mem} {cs' : Clif.State}
    {rvals' : List Clif.Val} {cm'' : Clif.Mem}
    (hmrW : MemRel F L.syms cm (L.worldPR κ (M' + 1) h
      (L.BP (M' + 1) g s (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i))
      (L.RP (M' + 1) g s (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i)) w))
    (hargsW : ArgsAt h.sig vals' args (L.worldPR κ (M' + 1) h
      (L.BP (M' + 1) g s (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i))
      (L.RP (M' + 1) g s (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i)) w))
    (hsavW : StackArgsAvoid F h.sig vals' (L.worldPR κ (M' + 1) h
      (L.BP (M' + 1) g s (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i))
      (L.RP (M' + 1) g s (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i)) w))
    (hspw : spv w = spv w₀)
    (hinit : Clif.initState L.P h.name vals' cm = .ok cs')
    (hrun : L.crun (M' + 1) cs' = .returned rvals' cm'')
    {tj tj1 : Clif.State}
    (hrtj : ReachN (L.envOfB (M' + 1) g (spv w₀)) L.P.bare cs tj
      (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i))
    (hcnj : callNum tj = 1)
    (hstj : Clif.step (L.envOfB (M' + 1) g (spv w₀)) L.P.bare tj = .next tj1)
    (hinvj : Clif.Invoked (L.envOfB (M' + 1) g (spv w₀)) L.P.bare tj h.name vals' cm)
    (hItj : Clif.LInv (L.P.only g) tj) (hctj : tj.callers = [])
    (hptj : L.PlaceAtB tj.mem (spv w₀) (ini.adv (Clif.sumTo
      (advAt (L.envOfB (M' + 1) g (spv w₀)) L.P.bare cs)
      (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i))))
    (hcnt : ∀ e, L.TabUpTo (M' + 1) g s ini.bytes ini.next i e →
      e = Clif.sumTo (advAt (L.envOfB (M' + 1) g (spv w₀)) L.P.bare cs)
        (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i)) :
    ∀ e', L.TabUpTo (M' + 1) g s ini.bytes ini.next (i + 1) e' →
      e' = Clif.sumTo (advAt (L.envOfB (M' + 1) g (spv w₀)) L.P.bare cs)
        (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s (i + 1)) := by
  have he := hME.entryP.entry
  have hcm : cm = tj.mem := hinvj.1
  have hpl : L.NeedSlots → L.PlaceAtB cm (spv w₀) (ini.adv (Clif.sumTo
      (advAt (L.envOfB (M' + 1) g (spv w₀)) L.P.bare cs)
      (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i))) := fun _ => by
    rw [hcm]; exact hptj
  obtain ⟨Lu, hLu, hargs, hct, hrah, hor⟩ := L.oracleAt_at hL hκ hdt hg hWE hME hra htab htr hsp
    hi hS hops hst hasg hpi herr hgd hGu hsw hh hd hcal hmrW hargsW hsavW hspw hinit hrun hpl hcnt
  have himgU : ∀ a, L.Img a → (runX (L.mach (M' + 1) g) i s).mem a = L.imgMem a :=
    fun a ha => (hGu a (he.imgG a ha)).trans (he.imgS a ha)
  have hcp := hpi.callPc
  obtain ⟨hmskQ, hrgnQ⟩ := L.callStPRB_q (κ := κ) (M := M' + 1) he.body.sp
    (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i) (runX (L.mach (M' + 1) g) i s)
    ⟨onCallPR_of hME.entryP.proph hME.reg ⟨i, rfl, rfl⟩, hsp⟩ hcp
  subst hargs
  obtain ⟨d, hnd, hgrow⟩ := L.callCount hL hκ ih hdet hg he hra htab hWE.img hWE.room hWE.dead
    hWE.align htr hsp herr hcp (func?_of_mem hL.names hh) hcal hct hmskQ hrgnQ hLu hsw hspw
    himgU hrah hmrW hargsW hsavW hor hinit hrun
  have hm1 : tj1.mem = cm'' := L.adv_prog (hL.free g hg) hItj hctj hinvj
    (func?_of_mem hL.names hh) hinit hrun hstj
  obtain ⟨sps, hp⟩ := hptj
  have hadv : advAt (L.envOfB (M' + 1) g (spv w₀)) L.P.bare cs
      (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i) = d :=
    advAt_eq hrtj hcnj hstj (by rw [hm1, ← hcm]; exact hnd hN) hp rfl
  intro e' h1
  obtain ⟨e, h0⟩ := L.tabUpTo_mono h1 (Nat.le_succ i)
  rw [hgrow e e' h0 h1, hcnt e h0]
  simp only [callsBefore, hcp, ↓reduceIte, Clif.sumTo, hadv]

/-- **The count invariant passes a call of a base extern** (module doc). -/
theorem countStep_base (hL : L.Ok) (hN : L.NeedSlots) {M' : Nat} {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {cs : Clif.State} {c : BitVec 64} {s : Arm.ArmState} {ini : Clif.SlotInit}
    {i : Nat}
    (hcp : CallPc (L.A g).fa (L.A g).base (Arm.r .PC (runX (L.mach (M' + 1) g) i s)))
    (hn : ∀ h, ¬ L.CallsTo g (runX (L.mach (M' + 1) g) i s) h)
    {tj tj1 : Clif.State}
    (hrtj : ReachN (L.envOfB (M' + 1) g c) L.P.bare cs tj
      (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i))
    (hcnj : callNum tj = 1)
    (hstj : Clif.step (L.envOfB (M' + 1) g c) L.P.bare tj = .next tj1)
    {nm : String} {vals' : List Clif.Val} {cm : Clif.Mem}
    (hinvj : Clif.Invoked (L.envOfB (M' + 1) g c) L.P.bare tj nm vals' cm)
    (hpf : L.P.func? nm = none)
    (hItj : Clif.LInv (L.P.only g) tj) (hctj : tj.callers = [])
    {ini' : Clif.SlotInit} (hptj : L.PlaceAtB tj.mem c ini')
    (hcnt : ∀ e, L.TabUpTo (M' + 1) g s ini.bytes ini.next i e →
      e = Clif.sumTo (advAt (L.envOfB (M' + 1) g c) L.P.bare cs)
        (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i)) :
    ∀ e', L.TabUpTo (M' + 1) g s ini.bytes ini.next (i + 1) e' →
      e' = Clif.sumTo (advAt (L.envOfB (M' + 1) g c) L.P.bare cs)
        (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s (i + 1)) := by
  have h0adv := L.adv_base hL hN (hL.free g hg) hItj hctj hinvj hpf hstj
  obtain ⟨sps, hp⟩ := hptj
  have hadv : advAt (L.envOfB (M' + 1) g c) L.P.bare cs
      (callsBefore (L.mach (M' + 1) g) (L.A g).fa (L.A g).base s i) = 0 :=
    advAt_eq hrtj hcnj hstj h0adv hp rfl
  intro e' h1
  obtain ⟨e, h0⟩ := L.tabUpTo_mono h1 (Nat.le_succ i)
  rw [L.tabUpTo_succ_base hcp hn h1 h0, hcnt e h0]
  simp only [callsBefore, hcp, ↓reduceIte, Clif.sumTo, hadv, Nat.add_zero]

end LinkSys

end E2E
