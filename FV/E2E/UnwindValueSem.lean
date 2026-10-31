import FV.E2E.RegLevelU
import FV.E2E.DeadCleanupContracts
import FV.E2E.DeadCleanupRealizes

/-!
# The dead-cleanup value semantics with unwinding (S10e, #232)

The shipped labels rest on the dead-cleanup chain (`E2E.backend_correct_final_cleanup`), whose
VCode semantics is the value semantics `valueSem` (pure producers and compares by `mspec`,
everything else, calls included, by `csem`) and, at the register level, `valueSemV` (`csemV` in place of
`csem`). Their counterparts with unwinding, additive:

* `valueSemU F ctx X XR`: `valueSem` with `csemU` in place of `csem` — so at `call`/`tryCall`
  (never pure) it is `csemU` (a raising `call` ends the activation, a raising `tryCall`
  continues at its first handler with `payloadOuts`), and where no callee raises (`NoRaise`) it
  is `valueSem`;
* `valueSemVU gv F ctx X XR`: `valueSemV` with `csemVU` in place of `csemV`;
  `valueSemVU_bot`: without GOT pins it is `valueSemU`;
* the facts the cleanup chain uses of `valueSem` hold for `valueSemU`: `driverSem_valueSemU`,
  `refines_valueSemU`, `memRefines_valueSemU`, `valueSemU_pure`, and — with the callees'
  exclusivity (a callee that returns normally does not raise, `CalleeUnwOkG.excl`) —
  `callsRefine_valueSemU`, `indCallsRefine_valueSemU`;
* M6: `realizes_value_allU`, the value-semantics `Realizes` of the activation with unwinding,
  from the old `realizes_value_all` (`FV/E2E/DeadCleanupRealizes.lean`) by `realizes_allU`, the
  raising `tryCall` case from `realizes_tryCall_raiseU` with `tryRaiseSem_valueSemVU`;
  `valueSemVU_rets`, `valueSemVU_halt_trap`: returns and traps are `csem`'s.
-/

namespace Backend.DeadCleanup

open Backend Backend.Proof Backend.Proof.Driver

/-! ## The value semantics with unwinding -/

/-- **The value semantics with unwinding**: pure producers and compares by `mspec`, everything
else by `csemU`. -/
noncomputable def valueSemU (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) (XR : XRaise) :
    Sem :=
  fun i us w => if specForm i then mspec ctx.slotBase i us w else csemU F ctx X XR i us w

section
variable {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {XR : XRaise}

/-- Off the pure producers and compares `valueSemU` is `csemU`. -/
theorem valueSemU_not_pure {i : MInst} (hp : specForm i = false) :
    valueSemU F ctx X XR i = csemU F ctx X XR i := by
  funext us w
  simp only [valueSemU, hp, Bool.false_eq_true, ↓reduceIte]

/-- At a `call`, `valueSemU` is `csemU`. -/
theorem valueSemU_call (info : CallInfo) :
    valueSemU F ctx X XR (.call info) = csemU F ctx X XR (.call info) :=
  valueSemU_not_pure rfl

/-- At a `tryCall`, `valueSemU` is `csemU`. -/
theorem valueSemU_tryCall (info : CallInfo) (ti : TryInfo) :
    valueSemU F ctx X XR (.tryCall info ti) = csemU F ctx X XR (.tryCall info ti) :=
  valueSemU_not_pure rfl

/-- `valueSemU` is `valueSem` on every instruction but `call`/`tryCall`. -/
theorem valueSemU_of_not_call {i : MInst} (hc : ∀ info, i ≠ .call info)
    (ht : ∀ info ti, i ≠ .tryCall info ti) : valueSemU F ctx X XR i = valueSem F ctx X i := by
  funext us w
  simp only [valueSemU, valueSem, csemU_of_not_call hc ht]

/-- **Where no callee raises, `valueSemU` is `valueSem`.** -/
theorem valueSemU_noRaise {i : MInst} {us : List CV} {w : Arm.ArmState} (h : NoRaise XR i us w) :
    valueSemU F ctx X XR i us w = valueSem F ctx X i us w := by
  simp only [valueSemU, valueSem]
  split
  · rfl
  · exact csemU_noRaise h

/-- Without exceptional semantics `valueSemU` is `valueSem`. -/
theorem valueSemU_none (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) :
    valueSemU F ctx X XRaise.none = valueSem F ctx X := by
  funext i us w
  simp only [valueSemU, valueSem, csemU_none]

/-- A raising `call` ends the activation. -/
theorem valueSemU_call_raise {info : CallInfo} {uses : List CV} {w : Arm.ArmState}
    {obj : BitVec 64} {w' : Arm.ArmState} (h : XR.raise (callDest info) uses w = some (obj, w')) :
    valueSemU F ctx X XR (.call info) uses w =
      some ((defCons (.call info)).map (fun _ => ofX 0), w', .halt) := by
  rw [valueSemU_call]; exact csemU_call_raise h

/-- A supported raising `tryCall` continues at its first handler with the payload. -/
theorem valueSemU_try_raise {info : CallInfo} {ti : TryInfo} {uses : List CV} {w : Arm.ArmState}
    {obj : BitVec 64} {w' : Arm.ArmState} (h : XR.raise (callDest info) uses w = some (obj, w'))
    (hok : tryUOk info ti = true) :
    valueSemU F ctx X XR (.tryCall info ti) uses w =
      some (payloadOuts (.call info) obj, w', .goto 0) := by
  rw [valueSemU_tryCall]; exact csemU_try_raise h hok

/-- Pure producers keep the world and continue (`cleanup_correct`'s premise). -/
theorem valueSemU_pure {i : MInst} {us outs : List CV} {w w' : Arm.ArmState} {ctl : Ctl}
    (hp : pureForm i = true) (h : valueSemU F ctx X XR i us w = some (outs, w', ctl)) :
    w' = w ∧ ctl = .next := by
  simp only [valueSemU, specForm_of_pure hp, ↓reduceIte] at h
  exact mspec_pure hp h

/-- The value semantics with unwinding lets the next compare overwrite a compare's flags. -/
theorem valueSemU_cmpOverwrite (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) (XR : XRaise) :
    CmpOverwrite (valueSemU F ctx X XR) :=
  cmpOverwrite_of_mspec (sb := ctx.slotBase)
    (fun i hs => by funext us w; simp only [valueSemU, hs, ↓reduceIte])
    (jumpPlain_of_csem (F := F) (ctx := ctx) (X := X) fun l => by
      funext us w; simp [valueSemU, csemU, specForm, pureForm, cmpForm])

/-- With the callees' exclusivity, a `csem` step is a `csemU` step. -/
theorem csemU_of_csem
    (hex : ∀ d uses w, X.call d uses w ≠ none → XR.raise d uses w = none)
    {i : MInst} {us : List CV} {w : Arm.ArmState} {r : List CV × Arm.ArmState × Ctl}
    (h : csem F ctx X i us w = some r) : csemU F ctx X XR i us w = some r := by
  rw [csemU_noRaise (fun info hi => hex _ _ _ (csem_call_ne_none hi h))]
  exact h

/-- With the callees' exclusivity, a `valueSem` step is a `valueSemU` step. -/
theorem valueSemU_of_valueSem
    (hex : ∀ d uses w, X.call d uses w ≠ none → XR.raise d uses w = none)
    {i : MInst} {us : List CV} {w : Arm.ArmState} {r : List CV × Arm.ArmState × Ctl}
    (h : valueSem F ctx X i us w = some r) : valueSemU F ctx X XR i us w = some r := by
  unfold valueSem at h
  unfold valueSemU
  split
  · simpa only [*, ↓reduceIte] using h
  · rename_i hp
    simp only [hp, Bool.false_eq_true, ↓reduceIte] at h
    exact csemU_of_csem hex h

end

/-! ## The facts of the cleanup chain -/

/-- **`DriverSem` for `valueSemU`.** -/
theorem driverSem_valueSemU (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) (XR : XRaise) :
    DriverSem (valueSemU F ctx X XR) := by
  have hd := driverSem_csemU F ctx X XR
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro l w; simpa [valueSemU, specForm, pureForm, cmpForm] using hd.jump l w
  · intro g gn hg i
    funext us w
    simp only [valueSemU, specForm_mapRegs hg]
    by_cases hp : specForm i = true
    · simp only [hp]
      exact mspec_mapRegs hg _ _ _ _
    · simp only [hp]
      exact congrFun (congrFun (hd.rename g gn hg i) us) w
  · intro i ls i' h
    have he := specForm_setTargets h
    funext us w
    simp only [valueSemU, he]
    by_cases hp : specForm i = true
    · cases i <;> simp [MInst.setTargets] at h <;> simp [specForm, pureForm, cmpForm] at hp
    · simp only [hp]
      exact congrFun (congrFun (hd.retarget i ls i' h) us) w
  · intro ds w; simpa [valueSemU, specForm, pureForm, cmpForm] using hd.args ds w

/-- **The instruction specification is preserved** (`ispec` has no calls). -/
theorem refines_valueSemU (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) (XR : XRaise) :
    Refines F (valueSemU F ctx X XR) := by
  intro i us w outs w' ctl h
  obtain ⟨w'', h1, h2⟩ := refines_valueSem F ctx X i us w outs w' h
  refine ⟨w'', ?_, h2⟩
  rw [valueSemU_of_not_call (fun info e => by subst e; simp [ispec] at h)
    (fun info ti e => by subst e; simp [ispec] at h)]
  exact h1

/-- **The memory forms** (no call among them). -/
theorem memRefines_valueSemU (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) (XR : XRaise)
    {sb : Nat} {syms : String → Option Nat} (hsb : ctx.slotBase = sb)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b) :
    MemRefines F sb syms (valueSemU F ctx X XR) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := memRefines_valueSem F ctx X hsb hsym
  have e : ∀ i, (∀ info, i ≠ .call info) → (∀ info ti, i ≠ .tryCall info ti) →
      valueSemU F ctx X XR i = valueSem F ctx X i := fun _ hc ht => valueSemU_of_not_call hc ht
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro op d am fl uses w a h0 ha hav
    rw [e _ (fun _ h => by cases h) (fun _ _ h => by cases h)]; exact h1 op d am fl uses w a h0 ha hav
  · intro op d am fl v uses w a h0 ha hav
    rw [e _ (fun _ h => by cases h) (fun _ _ h => by cases h)]
    exact h2 op d am fl v uses w a h0 ha hav
  · intro d off w
    rw [e _ (fun _ h => by cases h) (fun _ _ h => by cases h)]; exact h3 d off w
  · intro d n b w hb
    rw [e _ (fun _ h => by cases h) (fun _ _ h => by cases h)]; exact h4 d n b w hb
  · intro ty d r fl u w hty hav
    rw [e _ (fun _ h => by cases h) (fun _ _ h => by cases h)]; exact h5 ty d r fl u w hty hav
  · intro ty d r fl u v w hty hav
    rw [e _ (fun _ h => by cases h) (fun _ _ h => by cases h)]; exact h6 ty d r fl u v w hty hav
  · intro ty op fl ra ro rd r1 r2 u x w hty hav
    rw [e _ (fun _ h => by cases h) (fun _ _ h => by cases h)]
    exact h7 ty op fl ra ro rd r1 r2 u x w hty hav
  · intro ty fl ra re rx rd r1 u e' x w hty hav
    rw [e _ (fun _ h => by cases h) (fun _ _ h => by cases h)]
    exact h8 ty fl ra re rx rd r1 u e' x w hty hav
  · intro d t n b w hb
    rw [e _ (fun _ h => by cases h) (fun _ _ h => by cases h)]; exact h9 d t n b w hb

/-- **The callee contract**, under the callees' exclusivity (a callee that returns normally does
not raise: `CalleeUnwOkG.excl`). -/
theorem callsRefine_valueSemU {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {XR : XRaise}
    {env : Clif.Env} {exts : List Clif.ExtFunc} {MR : MemRelT} (hX : XCallsOk env exts MR X)
    (hex : ∀ d uses w, X.call d uses w ≠ none → XR.raise d uses w = none) :
    CallsRefine F env exts MR (valueSemU F ctx X XR) := by
  obtain ⟨sym, h1, h2, h3⟩ := callsRefine_valueSem (F := F) (ctx := ctx) hX
  refine ⟨sym, fun rd n w => ?_, ?_, ?_⟩
  · obtain ⟨w', hs, hw⟩ := h1 rd n w
    exact ⟨w', valueSemU_of_valueSem hex hs, hw⟩
  · intro ext hext g sl cm w dest us ds uses args vals rvals cm' a b c d e f g'
    obtain ⟨outs, w', hs, rest⟩ := h2 ext hext g sl cm w dest us ds uses args vals rvals cm' a b c d e f g'
    exact ⟨outs, w', valueSemU_of_valueSem hex hs, rest⟩
  · intro ext hext g sl cm w dest us ds ti uses args vals rvals cm' a b c d e f g' h'
    obtain ⟨outs, w', hs, rest⟩ :=
      h3 ext hext g sl cm w dest us ds ti uses args vals rvals cm' a b c d e f g' h'
    exact ⟨outs, w', valueSemU_of_valueSem hex hs, rest⟩

/-- **The indirect-call contract**, under the callees' exclusivity. -/
theorem indCallsRefine_valueSemU {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {XR : XRaise}
    {env : Clif.Env} {sigs : List Clif.Signature} {MR : MemRelT} {syms : String → Option Nat}
    (hX : XCallsIndOk env sigs MR X) (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hMR : ∀ sl cm w, MR sl cm w → cm.symbols = syms)
    (hex : ∀ d uses w, X.call d uses w ≠ none → XR.raise d uses w = none) :
    IndCallsRefine env sigs MR (valueSemU F ctx X XR) := by
  obtain ⟨h1, h2⟩ := indCallsRefine_valueSem (F := F) (ctx := ctx) hX hsym hMR
  refine ⟨?_, ?_⟩
  · intro sig hsig n g sl cm w a r us ds u args vals rvals cm' a1 a2 a3 a4 a5 a6 a7 a8 a9 a10
    obtain ⟨outs, w', hs, rest⟩ :=
      h1 sig hsig n g sl cm w a r us ds u args vals rvals cm' a1 a2 a3 a4 a5 a6 a7 a8 a9 a10
    exact ⟨outs, w', valueSemU_of_valueSem hex hs, rest⟩
  · intro sig hsig n g sl cm w a r us ds ti u args vals rvals cm' a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
    obtain ⟨outs, w', hs, rest⟩ := h2 sig hsig n g sl cm w a r us ds ti u args vals rvals cm' a1 a2
      a3 a4 a5 a6 a7 a8 a9 a10 a11
    exact ⟨outs, w', valueSemU_of_valueSem hex hs, rest⟩

end Backend.DeadCleanup

namespace Backend.Proof

open Backend Backend.DeadCleanup E2E

/-! ## The register-level value semantics with unwinding -/

/-- **`valueSemV` with unwinding**: pure producers and compares by `mspec`, everything else by
`csemVU`. -/
noncomputable def valueSemVU (gv : Nat → String → Prop) (F : BitVec 64 → Prop) (ctx : FnCtx)
    (X : ExtSem) (XR : XRaise) : Sem :=
  fun i us w => if specForm i then mspec ctx.slotBase i us w else csemVU gv F ctx X XR i us w

/-- The value semantics of the activation with unwinding. -/
noncomputable def RLU.valueSemU (R : RLU) : Sem := valueSemVU R.gv R.F R.ctx R.X R.XR

section
variable {gv : Nat → String → Prop} {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem}
  {XR : XRaise}

/-- Without GOT pins `valueSemVU` is `valueSemU`. -/
theorem valueSemVU_bot (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) (XR : XRaise) :
    valueSemVU (fun _ _ => False) F ctx X XR = valueSemU F ctx X XR := by
  funext i us w
  simp only [valueSemVU, valueSemU, csemVU_bot]

/-- Off the pure producers and compares `valueSemVU` is `csemVU`. -/
theorem valueSemVU_not_pure {i : MInst} (hp : specForm i = false) :
    valueSemVU gv F ctx X XR i = csemVU gv F ctx X XR i := by
  funext us w
  simp only [valueSemVU, hp, Bool.false_eq_true, ↓reduceIte]

/-- The register-level value semantics with unwinding lets the next compare overwrite a
compare's flags. -/
theorem valueSemVU_cmpOverwrite (gv : Nat → String → Prop) (F : BitVec 64 → Prop) (ctx : FnCtx)
    (X : ExtSem) (XR : XRaise) : CmpOverwrite (valueSemVU gv F ctx X XR) :=
  cmpOverwrite_of_mspec (sb := ctx.slotBase)
    (fun i hs => by funext us w; simp only [valueSemVU, hs, ↓reduceIte])
    (jumpPlain_of_csem (F := F) (ctx := ctx) (X := X) fun l => by
      funext us w; simp [valueSemVU, csemVU, csemU, specForm, pureForm, cmpForm])

/-- **Where no callee raises, `valueSemVU` is `valueSemV`.** -/
theorem valueSemVU_noRaise {i : MInst} {us : List CV} {w : Arm.ArmState}
    (h : NoRaise XR i us w) : valueSemVU gv F ctx X XR i us w = valueSemV gv F ctx X i us w := by
  simp only [valueSemVU, valueSemV]
  split
  · rfl
  · exact csemVU_noRaise h

/-- `valueSemVU` is `valueSemV` on every instruction but `call`/`tryCall`. -/
theorem valueSemVU_of_not_call {i : MInst} (hc : ∀ info, i ≠ .call info)
    (ht : ∀ info ti, i ≠ .tryCall info ti) : valueSemVU gv F ctx X XR i = valueSemV gv F ctx X i := by
  funext us w
  exact valueSemVU_noRaise fun info hi => by
    rcases hi with rfl | ⟨ti, rfl⟩
    · exact absurd rfl (hc info)
    · exact absurd rfl (ht info ti)

/-- A raising `call` ends the activation (`valueSemVU`). -/
theorem valueSemVU_call_raise {info : CallInfo} {uses : List CV} {w : Arm.ArmState}
    {r : List CV × Arm.ArmState × Ctl} (h : valueSemVU gv F ctx X XR (.call info) uses w = some r)
    {obj : BitVec 64} {w' : Arm.ArmState} (hr : XR.raise (callDest info) uses w = some (obj, w')) :
    r = ((defCons (.call info)).map (fun _ => ofX 0), w', .halt) := by
  rw [valueSemVU_not_pure rfl] at h
  exact csemVU_call_raise h hr

/-- A raising `tryCall` continues at its first handler with the payload (`valueSemVU`). -/
theorem valueSemVU_try_raise {info : CallInfo} {ti : TryInfo} {uses : List CV}
    {w : Arm.ArmState} {r : List CV × Arm.ArmState × Ctl}
    (h : valueSemVU gv F ctx X XR (.tryCall info ti) uses w = some r)
    {obj : BitVec 64} {w' : Arm.ArmState} (hr : XR.raise (callDest info) uses w = some (obj, w')) :
    tryUOk info ti = true ∧ r = (payloadOuts (.call info) obj, w', .goto 0) := by
  rw [valueSemVU_not_pure rfl] at h
  exact csemVU_try_raise h hr

/-- The raising-`tryCall` clause of the value semantics with unwinding (`TryRaiseSem`, the
premise of `realizes_tryCall_raiseU`). -/
theorem tryRaiseSem_valueSemVU (gv : Nat → String → Prop) (F : BitVec 64 → Prop) (ctx : FnCtx)
    (X : ExtSem) (XR : XRaise) : TryRaiseSem XR (valueSemVU gv F ctx X XR) :=
  fun _ _ _ _ _ _ _ h hr => valueSemVU_try_raise h hr

/-- The value semantics with unwinding passes the GOT guard of its pins (`GotSem`). -/
theorem gotSem_valueSemVU (gv : Nat → String → Prop) (F : BitVec 64 → Prop) (ctx : FnCtx)
    (X : ExtSem) (XR : XRaise) : GotSem gv X (valueSemVU gv F ctx X XR) := by
  intro info uses w r
  refine ⟨fun h => ?_, fun ti h => ?_⟩
  · rw [valueSemVU_not_pure rfl] at h
    exact (gotSem_csemVU gv F ctx X XR info uses w r).1 h
  · rw [valueSemVU_not_pure rfl] at h
    exact (gotSem_csemVU gv F ctx X XR info uses w r).2 ti h

/-- At a return `valueSemVU` is `csem`. -/
theorem valueSemVU_rets (us : List (Reg × Reg)) :
    valueSemVU gv F ctx X XR (.rets us) = csem F ctx X (.rets us) := by
  funext uses w
  rw [valueSemVU_not_pure rfl]
  simp only [csemVU, csemU]

/-- A trap instruction's `.halt` under `valueSemVU` is one of `csem`. -/
theorem valueSemVU_halt_trap {i : MInst} {uses : List CV} {w : Arm.ArmState} {outs : List CV}
    {w' : Arm.ArmState} (ht : trapCode? i ≠ none)
    (h : valueSemVU gv F ctx X XR i uses w = some (outs, w', .halt)) :
    csem F ctx X i uses w = some (outs, w', .halt) := by
  cases i <;> simp only [trapCode?, ne_eq, not_true_eq_false] at ht <;>
    rw [valueSemVU_not_pure rfl] at h <;> simpa only [csemVU, csemU] using h

end

/-- **`Realizes` of the value semantics with unwinding**: the old value realiser
(`realizes_value_all`) transferred by `realizes_allU`; the raising `tryCall` case `htry` from
`realizes_tryCall_raiseU` with `tryRaiseSem_valueSemVU`. -/
theorem realizes_value_allU {R : RLU} (hR : R.Wf)
    (hC : CalleeOkG R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H R.vc.CallSite R.gv)
    (hT : R.vc.hasTryCall = true → CalleeTryOkG R.F R.K R.G R.s0
      (CallAt R.fa R.base) R.X R.H R.vc.TrySite R.gv)
    (hTls : R.vc.hasTls = true → TlsOk R.F R.K R.X R.H)
    (hcov : FormsCovered R.ctx R.vc)
    (hU : CalleeUnwOkG R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.XR R.U R.vc.CallSite R.gv)
    (htry : RealizesTryRaise R R.valueSemU) :
    Realizes R.vc R.rf R.valueSemU ckeep R.stepU
      (QA R.toRL) R.GoodXU :=
  realizes_allU hR hU (realizes_value_all hR hC hT hTls hcov)
    (fun _ _ _ h => valueSemVU_noRaise h)
    (fun _ _ _ _ _ _ h hr => by rw [valueSemVU_call_raise h hr])
    htry

/-- **`realizes_value_allU` with the raising-call states' step facts** (trace `R.GoodXUF`;
`htry` from `realizes_tryCall_raiseUF`). -/
theorem realizes_value_allUF {R : RLU} (hR : R.Wf)
    (hC : CalleeOkG R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H R.vc.CallSite R.gv)
    (hT : R.vc.hasTryCall = true → CalleeTryOkG R.F R.K R.G R.s0
      (CallAt R.fa R.base) R.X R.H R.vc.TrySite R.gv)
    (hTls : R.vc.hasTls = true → TlsOk R.F R.K R.X R.H)
    (hcov : FormsCovered R.ctx R.vc)
    (hU : CalleeUnwOkG R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.XR R.U R.vc.CallSite R.gv)
    (htry : RealizesTryRaiseP R R.valueSemU R.GoodXUF) :
    Realizes R.vc R.rf R.valueSemU ckeep R.stepU
      (QA R.toRL) R.GoodXUF :=
  realizes_allUP hR (fun _ h => .inl h) hU (realizes_value_all hR hC hT hTls hcov)
    (fun _ _ _ h => valueSemVU_noRaise h)
    (fun _ _ _ _ _ _ h hr => by rw [valueSemVU_call_raise h hr])
    htry

/-! ## Non-vacuity -/

namespace UnwindValueSemWitness

open UnwindSemWitness

/-- The raising callee: under the value semantics the `try_call` continues at its handler with
x0 = 77, x1 = 0, and a plain call of it ends the activation; a pure producer is `mspec`. -/
example (F : BitVec 64 → Prop) (X : ExtSem) (w : Arm.ArmState) (uses : List CV) :
    valueSemU F ⟨0, 0⟩ X XR (.tryCall info ti) uses w = some ([ofX 77, ofX 0], w, .goto 0) ∧
    valueSemU F ⟨0, 0⟩ X XR (.call info) uses w = some ([ofX 0, ofX 0], w, .halt) ∧
    valueSemVU (fun _ _ => False) F ⟨0, 0⟩ X XR (.call info) uses w =
      some ([ofX 0, ofX 0], w, .halt) ∧
    valueSemU F ⟨0, 0⟩ X XR deadMvn [0#128] w = some ([ofX (~~~(0#64))], w, .next) := by
  refine ⟨?_, ?_, ?_, rfl⟩
  · rw [valueSemU_try_raise (obj := 77) (w' := w) rfl tryUOk_ok]; rfl
  · rw [valueSemU_call_raise (obj := 77) (w' := w) rfl]; rfl
  · rw [valueSemVU_bot, valueSemU_call_raise (obj := 77) (w' := w) rfl]; rfl

end UnwindValueSemWitness

end Backend.Proof
