import FV.E2E.RegLevelCall
import FV.E2E.RegLevelFrame
import FV.E2E.UnwindSem
import FV.Unw.Model

/-!
# The register-level simulation with unwinding: framework (S10e, #232)

The activation of `FV/E2E/RegLevelSim.lean` (`RL`) with the outside contract of
`FV/Unw/Model.lean`: the instruction semantics `csemVU` (`csemV` with `csemU`'s raising calls)
and the machine `Unw.ArmStepU` (`ArmStepX` whose calls may raise, the unwinder and the
personality reading the tables `T`).

* `UnwSoundAtI`/`UnwSoundG`/`CalleeUnwOkG`: **the raising callees' contract**, `CalleeOkG`'s
  counterpart (`OperandsSoundCtlAtI`'s shape): at a call of the activation where the callees'
  exceptional semantics `XR` raises `obj` with world `w'`, the machine's callee raises the
  same object and the unwinder restores a state `t` at our call with that world, the frame (and
  `sp`) kept, the allocatable registers outside the clobbers kept and the callee-saved part of
  the clobbered callee-saved registers kept (the unwinder restores them from the callee's CFI),
  no error, the same program. `noRaise`: at a call whose callee returns normally (`X.call`) the
  machine's callee of that call (its descriptor) does not raise; `excl`: a callee that returns
  normally does not raise (`XR`).
* `RLU.stepU_eq`: at every state of the old realisation's trace (`RL.GoodX`) the machine with
  unwinding steps as the old one: a call there is a normal call (`RL.CallPre`, `excl`).
* `RLU.RaiseX`/`RLU.GoodXU`: a raising-call state (the pc at a `bl`/`blr` whose machine callee
  raises), where `RL.GoodX`'s call clause (a normal callee result) fails; `GoodXU` = `GoodX` or
  `RaiseX`, the trace predicate of the runs with unwinding. `RLU.stepU_q_raise`: at `Q` at a
  call item whose callee raises, the machine enters the unwinder from a `RaiseX` state
  (`stepU_q_raiseF`: with the call line's descriptor). `RLU.RaiseXF`/`RLU.GoodXUF`: a raising-call
  state with the facts the executable machine needs of its step (D1, the exit lands on the
  return, the restored `sp`, a `blr`'s facts, the raising callees' contract premise).
* `TryRaiseSem`: `csemU`'s raising-`tryCall` clause, for any semantics (`csemVU`, `csemU`, the
  dead-cleanup chain's value semantics).
* `mstep_congr`: an allocated-code step under one semantics is one under another that agrees on
  the stepped instruction.
* `realizes_allU`: every `Realizes` of a semantics `sem₀` (e.g. `RL.sem`, or the shipped
  compiler's value semantics) transfers to the semantics with unwinding: steps without a raising
  callee are realised as before (the trace is the same run of both machines), a raising `call`
  ends the activation (`.halt`, nothing to realise here: the final dispatch unwinds the frame),
  and a raising `tryCall` is realised by `htry` (`realizes_tryCall_raiseU`).
-/

namespace Backend.Proof

open Backend E2E

/-! ## The activation semantics with unwinding -/

open Classical in
/-- **`csemV` with unwinding**: the calls through the GOT pinned as in `csemV`, `csemU`'s
raising calls. -/
noncomputable def csemVU (gv : Nat → String → Prop) (F : BitVec 64 → Prop) (ctx : FnCtx)
    (X : ExtSem) (XR : XRaise) : ISem CV Arm.ArmState := fun i uses w =>
  match i with
  | .call info | .tryCall info _ =>
    if gotGuard gv X info uses then csemU F ctx X XR i uses w else none
  | _ => csemU F ctx X XR i uses w

/-- No callee of `i` raises (at these uses, from this world). -/
def NoRaise (XR : XRaise) (i : MInst) (uses : List CV) (w : Arm.ArmState) : Prop :=
  ∀ info, (i = .call info ∨ ∃ ti, i = .tryCall info ti) → XR.raise (callDest info) uses w = none

theorem csemVU_noRaise {gv : Nat → String → Prop} {F : BitVec 64 → Prop} {ctx : FnCtx}
    {X : ExtSem} {XR : XRaise} {i : MInst} {uses : List CV} {w : Arm.ArmState}
    (h : NoRaise XR i uses w) : csemVU gv F ctx X XR i uses w = csemV gv F ctx X i uses w := by
  cases i with
  | call info => simp only [csemVU, csemV, csemU_noRaise h]
  | tryCall info ti => simp only [csemVU, csemV, csemU_noRaise h]
  | _ => simp only [csemVU, csemV]; exact csemU_noRaise h

theorem csemVU_bot (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) (XR : XRaise) :
    csemVU (fun _ _ => False) F ctx X XR = csemU F ctx X XR := by
  funext i uses w
  have hg : ∀ info, gotGuard (fun _ _ => False) X info uses := fun _ _ _ _ _ h => h.elim
  cases i <;> simp [csemVU, hg]

/-- A raising `call` ends the activation (`csemVU`, under the GOT guard). -/
theorem csemVU_call_raise {gv : Nat → String → Prop} {F : BitVec 64 → Prop} {ctx : FnCtx}
    {X : ExtSem} {XR : XRaise} {info : CallInfo} {uses : List CV} {w : Arm.ArmState}
    {r : List CV × Arm.ArmState × Ctl} (h : csemVU gv F ctx X XR (.call info) uses w = some r)
    {obj : BitVec 64} {w' : Arm.ArmState} (hr : XR.raise (callDest info) uses w = some (obj, w')) :
    r = ((defCons (.call info)).map (fun _ => ofX 0), w', .halt) := by
  simp only [csemVU] at h
  split at h
  · rw [csemU_call_raise hr] at h; exact (Option.some.inj h).symm
  · cases h

/-- A raising `tryCall` continues at its first handler with the payload (`csemVU`). -/
theorem csemVU_try_raise {gv : Nat → String → Prop} {F : BitVec 64 → Prop} {ctx : FnCtx}
    {X : ExtSem} {XR : XRaise} {info : CallInfo} {ti : TryInfo} {uses : List CV}
    {w : Arm.ArmState} {r : List CV × Arm.ArmState × Ctl}
    (h : csemVU gv F ctx X XR (.tryCall info ti) uses w = some r)
    {obj : BitVec 64} {w' : Arm.ArmState} (hr : XR.raise (callDest info) uses w = some (obj, w')) :
    tryUOk info ti = true ∧ r = (payloadOuts (.call info) obj, w', .goto 0) := by
  simp only [csemVU] at h
  split at h
  · simp only [csemU, hr] at h
    split at h
    · exact ⟨by assumption, (Option.some.inj h).symm⟩
    · cases h
  · cases h

/-- **A raising `tryCall` under `sem`** (`csemU`'s clause): where the callee raises, `sem` has a
supported shape (`tryUOk`) and continues at the first handler (`.goto 0`) with the payload. -/
def TryRaiseSem (XR : XRaise) (sem : ISem CV Arm.ArmState) : Prop :=
  ∀ (info : CallInfo) (ti : TryInfo) (uses : List CV) (w : Arm.ArmState)
    (r : List CV × Arm.ArmState × Ctl) (obj : BitVec 64) (w' : Arm.ArmState),
    sem (.tryCall info ti) uses w = some r → XR.raise (callDest info) uses w = some (obj, w') →
    tryUOk info ti = true ∧ r = (payloadOuts (.call info) obj, w', .goto 0)

theorem tryRaiseSem_csemVU (gv : Nat → String → Prop) (F : BitVec 64 → Prop) (ctx : FnCtx)
    (X : ExtSem) (XR : XRaise) : TryRaiseSem XR (csemVU gv F ctx X XR) :=
  fun _ _ _ _ _ _ _ h hr => csemVU_try_raise h hr

theorem tryRaiseSem_csemU (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) (XR : XRaise) :
    TryRaiseSem XR (csemU F ctx X XR) := by
  intro info ti uses w r obj w' h hr
  simp only [csemU, hr] at h
  split at h
  · exact ⟨by assumption, (Option.some.inj h).symm⟩
  · cases h

/-- **The GOT guard of a semantics**: every `call`/`tryCall` it defines passes the GOT guard of
`gv` (`gotGuard`: at a call through the GOT the target is the symbol's address). -/
def GotSem (gv : Nat → String → Prop) (X : ExtSem) (sem : ISem CV Arm.ArmState) : Prop :=
  ∀ info uses w r, (sem (.call info) uses w = some r → gotGuard gv X info uses) ∧
    ∀ ti, sem (.tryCall info ti) uses w = some r → gotGuard gv X info uses

theorem gotSem_csemVU (gv : Nat → String → Prop) (F : BitVec 64 → Prop) (ctx : FnCtx)
    (X : ExtSem) (XR : XRaise) : GotSem gv X (csemVU gv F ctx X XR) := by
  intro info uses w r
  refine ⟨fun h => ?_, fun ti h => ?_⟩ <;>
  · simp only [csemVU] at h
    split at h
    · assumption
    · cases h

/-- Without GOT pins every semantics passes the guard. -/
theorem gotSem_bot (X : ExtSem) (sem : ISem CV Arm.ArmState) : GotSem (fun _ _ => False) X sem :=
  fun _ _ _ _ => ⟨fun _ _ _ _ _ h => h.elim, fun _ _ _ _ _ _ h => h.elim⟩

/-! ## The activation with unwinding -/

/-- The fixed data of one activation with unwinding: the callees' exceptional semantics `XR`,
the machine's raising callees `U` and the tables `T` the unwinder reads. -/
structure RLU extends RL where
  XR : XRaise
  U : Unw.UnwHooks
  T : Unw.FnTables

namespace RLU
variable (R : RLU)

/-- The instruction semantics of the activation with unwinding. -/
noncomputable def semU : ISem CV Arm.ArmState := csemVU R.gv R.F R.ctx R.X R.XR

/-- The machine with unwinding. -/
noncomputable def stepU : Arm.ArmState → Arm.ArmState := Unw.ArmStepU R.X R.H R.U R.T R.fa

end RLU

/-- **A raising-call state of the activation**: the pc at a call line (`bl n`/`blr r`) whose
machine callee (descriptor `some n`/`none`) raises, the body's `sp`, no error, the program. -/
structure RLU.RaiseX (R : RLU) (u : Arm.ArmState) : Prop where
  good : R.Good u
  err : Arm.r .ERR u = .None
  prog : u.program = R.fb.program R.base
  sp : spOf u = R.spB
  raise : ∃ x d obj t, R.AtLine u x ∧
    ((∃ n, x = .bl n ∧ d = some n) ∨ (∃ r, x = .blr r ∧ d = none)) ∧ R.U.raise d u = some (obj, t)

/-- **The premise of the raising callees' contract at a call state `u`** (`RL.CallPre`'s
counterpart): the antecedent of `UnwSoundG` at the allocated call whose code is at the pc, the
callees' exceptional semantics raising `obj` with world `w'`. The linking layer turns it into
the facts of the raising callee's run. -/
def RLU.CallPreU (R : RLU) (u : Arm.ArmState) : Prop :=
  ∃ (i : MInst) (info : CallInfo), R.vc.CallSite info ∧ (i = .call info ∨ ∃ ti, i = .tryCall info ti) ∧
    R.K ≤ (spOf u).toNat ∧ (∀ a, StackBelow R.K (spOf u) a → R.F a) ∧
    (∀ a, R.G a → u.mem a = R.s0.mem a) ∧
    ∃ (c : CheckCtx) (wh : String) (ops : Array Operand) (regs : Array Reg) (i' : MInst)
      (w : Arm.ArmState) (obj : BitVec 64) (w' : Arm.ArmState),
      i.operands = .ok ops ∧ c.checkStatic wh ops (regs.map .reg) i.clobbers = .ok () ∧
      i.assign regs = .ok i' ∧ CallAt R.fa R.base (Arm.r .PC u) i' ∧
      SameWorld R.F u w ∧ Arm.CheckSPAlignment u ∧ Arm.r .ERR u = .None ∧
      gotGuard R.gv R.X info (useVals ops regs u) ∧
      R.XR.raise (callDest info) (useVals ops regs u) w = some (obj, w')

/-- **A raising-call state of the activation with the facts the executable machine needs of its
step** (`RaiseX` and `RL.GoodX`'s counterpart): D1 at the unwinder's step, a step that continues
the unwinding lands on the activation's ABI return (the restored frame is the caller's), the
unwinder restores the call's state with the body's `sp`, a `blr`'s facts, and the raising
callees' contract premise (`CallPreU`). -/
structure RLU.RaiseXF (R : RLU) (u : Arm.ArmState) : Prop extends RLU.RaiseX R u where
  /-- D1 at the unwinder's step -/
  next : R.NextOk u (R.stepU u)
  /-- a step continuing the unwinding (the personality) lands on the activation's return -/
  exit : Unw.personality R.T.lsda (Arm.r .PC u + 4 - 1 - progBase u).toNat = .continue →
    ArmRet (xreg 30 R.s0) R.s0 (R.stepU u) ∧ (R.stepU u).program = R.fb.program R.base
  /-- the unwinder restores the call's state with the body's `sp` -/
  tsp : ∀ x d obj t, R.AtLine u x → ((∃ n, x = .bl n ∧ d = some n) ∨ (∃ r, x = .blr r ∧ d = none)) →
    R.U.raise d u = some (obj, t) → spOf t = R.spB
  /-- the unwinder restores the call's frame pointer: x29 = the entry `sp` − 16 (Cranelift's
  frame: the call-site row's CFA is x29 + 16) -/
  tfp : ∀ x d obj t, R.AtLine u x → ((∃ n, x = .bl n ∧ d = some n) ∨ (∃ r, x = .blr r ∧ d = none)) →
    R.U.raise d u = some (obj, t) → xreg 29 t = spv R.s0 - 16#64
  /-- a `blr`: not through `xzr` (calls through int vregs), the code words readable as data -/
  blr : ∀ x, R.AtLine u (.blr x) → (R.vc.DestsInt → x ≠ .xzr) ∧ ∀ k w, R.fb.words[k]? = some w →
    Arm.read_mem_bytes 4 (R.base + BitVec.ofNat 64 (4 * k)) u = w
  /-- the raising callees' contract premise -/
  pre : R.CallPreU u

/-- **The per-state facts of a run with unwinding**: a state of the old trace (`RL.GoodX`), or
a raising-call state (where `RL.GoodX`'s call clause, a normal callee result, fails). -/
def RLU.GoodXU (R : RLU) (u : Arm.ArmState) : Prop := R.GoodX u ∨ R.RaiseX u

/-- **The per-state facts of a run with unwinding, with the raising-call states' step facts**:
a state of the old trace (`RL.GoodX`), or a raising-call state with `RaiseXF`. -/
def RLU.GoodXUF (R : RLU) (u : Arm.ArmState) : Prop := R.GoodX u ∨ R.RaiseXF u

theorem RLU.GoodXUF.goodXU {R : RLU} {u : Arm.ArmState} (h : R.GoodXUF u) : R.GoodXU u :=
  h.imp id RLU.RaiseXF.toRaiseX

/-- At a raising-call state the machine with unwinding enters the unwinder. -/
theorem RLU.stepU_raiseX {R : RLU} (hR : R.Wf) {u : Arm.ArmState} (h : R.RaiseX u) :
    ∃ d obj t, R.U.raise d u = some (obj, t) ∧
      R.stepU u = Unw.unwindAt R.T (progBase u) (Arm.r .PC u) obj t := by
  obtain ⟨x, d, obj, t, ⟨j, tt, hj, hpc⟩, hd, hr⟩ := h.raise
  exact ⟨d, obj, t, hr, Unw.armStepU_raise (insnAt_pc hR hj h.prog hpc) hd hr⟩

theorem callVisit_callDest {m : Type → Type} [Monad m] [LawfulMonad m] (f : OpSpec → Reg → m Reg)
    (info : CallInfo) :
    callDest <$> callVisit f info = (fun _ => callDest info) <$> callVisit f info := by
  obtain ⟨dest, uses, defs⟩ := info
  cases dest <;> simp [callVisit, map_bind, callDest]

theorem callVisit_run_callDest (f : OpSpec → Reg → StateT Nat (Except String) Reg)
    (info : CallInfo) (q : CallInfo × Nat) (h : (callVisit f info).run 0 = .ok q) :
    callDest q.1 = callDest info := by
  have e := congrArg (fun x => StateT.run x 0) (callVisit_callDest f info)
  simp only [StateT.run_map, h] at e
  simpa [Functor.map, Except.map] using e

/-- The allocated call has the callee descriptor of the VCode call. -/
theorem assign_callDest {info ic : CallInfo} {regs : Array Reg}
    (h : (MInst.call info).assign regs = .ok (.call ic)) : callDest ic = callDest info := by
  unfold MInst.assign at h
  dsimp only at h
  rw [visit_call_eq, StateT.run_map] at h
  simp only [bind_map_left] at h
  cases hq : (callVisit (m := StateT Nat (Except String)) _ info).run 0 with
  | error e => rw [hq] at h; cases h
  | ok q =>
    rw [hq] at h
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    · simp only [pure, Except.pure, Except.ok.injEq, MInst.call.injEq] at h
      subst h
      exact callVisit_run_callDest _ info q hq

/-- **A raising call on the machine, with the call line's facts**: at `Q` at a `call`/`tryCall`
item whose machine callee raises (the descriptor of the VCode call), the machine with unwinding
enters the unwinder, the state is a raising-call state (`RaiseX`), the call line's descriptor is
the VCode call's, and a `blr` there is not through `xzr` (calls through int vregs). -/
theorem RLU.stepU_q_raiseF {R : RLU} (hR : R.Wf) {s : Arm.ArmState} {b k : Nat}
    {allocs : Array Loc} {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    (hq : Q R.toRL s (.run ⟨b, .op k allocs :: its, m, w⟩)) {vb : VBlock} {i : MInst}
    {info : CallInfo} (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some i)
    (hik : i = .call info ∨ ∃ ti, i = .tryCall info ti) {obj : BitVec 64} {t : Arm.ArmState}
    (hr : R.U.raise (callDest info) s = some (obj, t)) :
    R.stepU s = Unw.unwindAt R.T (progBase s) (Arm.r .PC s) obj t ∧ R.RaiseX s ∧
      (∀ x' d', R.AtLine s x' → ((∃ n, x' = .bl n ∧ d' = some n) ∨ (∃ r, x' = .blr r ∧ d' = none)) →
        d' = callDest info) ∧
      (∀ x', R.AtLine s (.blr x') → R.vc.DestsInt → x' ≠ .xzr) := by
  obtain ⟨j0, items, pre, regs, i', c1, c2, ls1, ls2, ps1, psm, ps2, T, cc, wh, ops, hal, -, -, hasg,
    -, -, hstat, -, -, -, -, -, -, -, hst⟩ := q_op hq hvb hi
  obtain ⟨ic, hic, hdest, hasgC⟩ : ∃ ic, (i' = .call ic ∨ ∃ ti, i' = .tryCall ic ti) ∧
      callDest ic = callDest info ∧ (MInst.call info).assign regs = .ok (.call ic) := by
    rcases hik with rfl | ⟨ti, rfl⟩
    · obtain ⟨ic, rfl⟩ := assign_call_form hasg
      exact ⟨ic, .inl rfl, assign_callDest hasg, hasg⟩
    · obtain ⟨ic, rfl, hc⟩ := (assign_call_tryCall info regs).2 ti i' hasg
      exact ⟨ic, .inr ⟨ti, rfl⟩, assign_callDest hc, hc⟩
  have hcpc : CallAt R.fa R.base (Arm.r .PC s) i' := by
    rcases hik with rfl | ⟨ti, rfl⟩
    · exact callAt_of_q hq hvb hi call_hcall regs i' hal hasg
    · exact callAt_of_q hq hvb hi tryCall_hcall regs i' hal hasg
  obtain ⟨j, x, tt, hj, hx, hpc⟩ := hcpc
  have hd0 : (∃ n, x = .bl n ∧ ic.dest = .sym n) ∨ (∃ r, x = .blr r ∧ ic.dest = .reg r) := by
    obtain ⟨dest, us, ds⟩ := ic
    rcases hic with rfl | ⟨ti, rfl⟩ <;> cases dest <;> simp [MInst.callInsn?] at hx <;>
      subst hx <;> simp
  have hd : (∃ n, x = .bl n ∧ callDest ic = some n) ∨ (∃ r, x = .blr r ∧ callDest ic = none) := by
    rcases hd0 with ⟨n, rfl, he⟩ | ⟨r, rfl, he⟩
    · exact .inl ⟨n, rfl, by simp [callDest, he]⟩
    · exact .inr ⟨r, rfl, by simp [callDest, he]⟩
  rw [hdest] at hd
  have hins := insnAt_pc hR hj hst.prog hpc
  have hat : R.AtLine s x := ⟨j, tt, hj, hpc⟩
  refine ⟨Unw.armStepU_raise hins hd hr, ⟨RL.good_of_sp hst.sp, hst.err, hst.prog, hst.sp,
    x, _, obj, t, hat, hd, hr⟩, fun x' d' hx' hd' => ?_, fun x' hx' hD => ?_⟩
  · obtain rfl := RL.atLine_unique hR hat hx'
    rcases hd with ⟨n, rfl, h1⟩ | ⟨r, rfl, h1⟩ <;>
      rcases hd' with ⟨n', h2, h3⟩ | ⟨r', h2, h3⟩ <;> cases h2 <;> rw [h1, h3]
  · obtain rfl := RL.atLine_unique hR hat hx'
    rcases hd0 with ⟨n, h1, -⟩ | ⟨r, h1, he⟩
    · cases h1
    · cases h1
      have hsite : R.vc.CallSite info := by
        rcases hik with rfl | ⟨ti, rfl⟩
        · exact ⟨b, vb, k, hvb, .inl hi⟩
        · exact ⟨b, vb, k, hvb, .inr ⟨ti, hi⟩⟩
      obtain ⟨b1, vb1, k1, hvb1, hi1⟩ := hsite
      exact callDest_ne_xzr (hD b1 vb1 k1 info hvb1 hi1) hstat hasgC he

/-- **A raising call on the machine**: at `Q` at a `call`/`tryCall` item whose machine callee
raises (the descriptor of the VCode call), the machine with unwinding enters the unwinder, and
the state is a raising-call state. -/
theorem RLU.stepU_q_raise {R : RLU} (hR : R.Wf) {s : Arm.ArmState} {b k : Nat}
    {allocs : Array Loc} {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    (hq : Q R.toRL s (.run ⟨b, .op k allocs :: its, m, w⟩)) {vb : VBlock} {i : MInst}
    {info : CallInfo} (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some i)
    (hik : i = .call info ∨ ∃ ti, i = .tryCall info ti) {obj : BitVec 64} {t : Arm.ArmState}
    (hr : R.U.raise (callDest info) s = some (obj, t)) :
    R.stepU s = Unw.unwindAt R.T (progBase s) (Arm.r .PC s) obj t ∧ R.RaiseX s :=
  let ⟨h1, h2, _⟩ := RLU.stepU_q_raiseF hR hq hvb hi hik hr
  ⟨h1, h2⟩

/-! ## The raising callees' contract -/

/-- **The raising callees' obligation at one state** (`OperandsSoundCtlAtI`'s shape) for the
allocated calls `i'` satisfying `P` of the VCode call `i` (with `CallInfo` `info`), under the
GOT guard of `gv` (`gotGuard`, as the normal-return contract `CalleeOkG`). -/
def UnwSoundAtI (F FK : BitVec 64 → Prop) (P : MInst → Prop) (gv : Nat → String → Prop)
    (X : ExtSem) (XR : XRaise) (U : Unw.UnwHooks) (info : CallInfo) (i : MInst)
    (s : Arm.ArmState) : Prop :=
  ∀ (c : CheckCtx) (wh : String) (ops : Array Operand) (regs : Array Reg) (i' : MInst)
    (w : Arm.ArmState),
    i.operands = .ok ops → c.checkStatic wh ops (regs.map .reg) i.clobbers = .ok () →
    i.assign regs = .ok i' → P i' → SameWorld F s w → Arm.CheckSPAlignment s →
    Arm.r .ERR s = .None → gotGuard gv X info (useVals ops regs s) →
    ∀ obj w', XR.raise (callDest info) (useVals ops regs s) w = some (obj, w') →
      ∃ t, U.raise (callDest info) s = some (obj, t) ∧ SameWorld F t w' ∧ FrameKeep FK s t ∧
        Arm.r .ERR t = .None ∧ t.program = s.program ∧
        (∀ r, r.allocatable = true → (∀ p ∈ (ops.zip regs).toList, p.1.isDef = true → p.2 ≠ r) →
          r ∉ i.clobbers → regVal t r = regVal s r) ∧
        (∀ r ∈ i.clobbers, r ∈ calleeSaved → ckeep r (regVal t r) = ckeep r (regVal s r))

/-- `UnwSoundAtI` at the states of an activation with a dead stack of `K` bytes below `sp`
and kept addresses `G` (`CallSoundCtlG`'s shape). -/
def UnwSoundG (F : BitVec 64 → Prop) (K : Nat) (G : BitVec 64 → Prop) (s0 : Arm.ArmState)
    (Pc : BitVec 64 → MInst → Prop) (gv : Nat → String → Prop) (X : ExtSem) (XR : XRaise)
    (U : Unw.UnwHooks) (info : CallInfo) (i : MInst) : Prop :=
  ∀ s, K ≤ (spOf s).toNat → (∀ a, StackBelow K (spOf s) a → F a) →
    (∀ a, G a → s.mem a = s0.mem a) →
    UnwSoundAtI F (fun a => F a ∧ ¬ StackBelow K (spOf s) a) (Pc (Arm.r .PC s)) gv X XR U info i s

/-- **The raising callees' contract** of an activation (`CalleeOkG`'s counterpart) for its call
sites `S`, under the GOT guard of `gv`. -/
structure CalleeUnwOkG (F : BitVec 64 → Prop) (K : Nat) (G : BitVec 64 → Prop)
    (s0 : Arm.ArmState) (Pc : BitVec 64 → MInst → Prop) (X : ExtSem) (XR : XRaise)
    (U : Unw.UnwHooks) (S : CallInfo → Prop) (gv : Nat → String → Prop) : Prop where
  os : ∀ info i, S info → (i = .call info ∨ ∃ ti, i = .tryCall info ti) →
    UnwSoundG F K G s0 Pc gv X XR U info i
  /-- at a call whose callee returns normally (`X.call`), the machine's callee of that call does
  not raise (`UnwSoundG`'s states and premises) -/
  noRaise : ∀ info (i : MInst), S info → (i = .call info ∨ ∃ ti, i = .tryCall info ti) →
    ∀ s : Arm.ArmState, K ≤ (spOf s).toNat → (∀ a, StackBelow K (spOf s) a → F a) →
    (∀ a, G a → s.mem a = s0.mem a) →
    ∀ (c : CheckCtx) (wh : String) (ops : Array Operand) (regs : Array Reg) (i' : MInst)
      (w : Arm.ArmState),
      i.operands = .ok ops → c.checkStatic wh ops (regs.map .reg) i.clobbers = .ok () →
      i.assign regs = .ok i' → Pc (Arm.r .PC s) i' → SameWorld F s w →
      Arm.CheckSPAlignment s → Arm.r .ERR s = .None → gotGuard gv X info (useVals ops regs s) →
      X.call (callDest info) (useVals ops regs s) w ≠ none → U.raise (callDest info) s = none
  /-- a callee that returns normally does not raise -/
  excl : ∀ d uses w, X.call d uses w ≠ none → XR.raise d uses w = none

/-- Without raising callees and without exceptional semantics the contract holds. -/
theorem calleeUnwOkG_none (F : BitVec 64 → Prop) (K : Nat) (G : BitVec 64 → Prop)
    (s0 : Arm.ArmState) (Pc : BitVec 64 → MInst → Prop) (X : ExtSem) (S : CallInfo → Prop)
    (gv : Nat → String → Prop) :
    CalleeUnwOkG F K G s0 Pc X XRaise.none Unw.UnwHooks.none S gv where
  os := by
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h
    cases h
  noRaise := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl
  excl := fun _ _ _ _ => rfl

/-! ## The trace of the old realisation is a run of the machine with unwinding -/

theorem csem_call_ne_none {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {i : MInst}
    {info : CallInfo} (hi : i = .call info ∨ ∃ ti, i = .tryCall info ti) {uses : List CV}
    {w : Arm.ArmState} {r : List CV × Arm.ArmState × Ctl} (h : csem F ctx X i uses w = some r) :
    X.call (callDest info) uses w ≠ none := by
  intro hn
  obtain ⟨dest, us, ds⟩ := info
  rcases hi with rfl | ⟨ti, rfl⟩ <;> cases dest <;> simp_all [csem, callDest]

/-- At a call of the old realisation's trace (`RL.GoodX`: the callee contract's premise, a
normal call) the callee of the call line does not raise. -/
theorem RLU.noRaise_of_goodX {R : RLU} (hR : R.Wf)
    (hU : CalleeUnwOkG R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.XR R.U R.vc.CallSite R.gv)
    {u : Arm.ArmState} (hg : R.GoodX u) {x : Insn} (hx : R.AtLine u x) {d : Option String}
    (hd : (∃ n, x = .bl n ∧ d = some n) ∨ (∃ r, x = .blr r ∧ d = none)) : R.U.raise d u = none := by
  have hc : (∃ n, x = .bl n) ∨ ∃ r, x = .blr r := by
    rcases hd with ⟨n, rfl, -⟩ | ⟨r, rfl, -⟩
    · exact .inl ⟨n, rfl⟩
    · exact .inr ⟨r, rfl⟩
  obtain ⟨ctx, i, ctl, ⟨info, hsite, hi⟩, hK, hD, hG, c, wh, ops, regs, i', w, outs, w', hops,
    hstat, hasg, hcall, hsw, hal, herr, hsem⟩ := hg.call x hx hc
  have hX := csem_call_ne_none hi (csemV_sub hsem)
  have hgg : gotGuard R.gv R.X info (useVals ops regs u) := by
    rcases hi with rfl | ⟨ti, rfl⟩
    · exact csemV_guard hsem
    · exact csemV_guard_try hsem
  have hn := hU.noRaise info i hsite hi u hK hD hG c wh ops regs i' w hops hstat hasg hcall hsw hal
    herr hgg hX
  obtain ⟨ic, hic, hdest⟩ : ∃ ic, (i' = .call ic ∨ ∃ ti, i' = .tryCall ic ti) ∧
      callDest ic = callDest info := by
    rcases hi with rfl | ⟨ti, rfl⟩
    · obtain ⟨ic, rfl⟩ := assign_call_form hasg
      exact ⟨ic, .inl rfl, assign_callDest hasg⟩
    · obtain ⟨ic, rfl, hc⟩ := (assign_call_tryCall info regs).2 ti i' hasg
      exact ⟨ic, .inr ⟨ti, rfl⟩, assign_callDest hc⟩
  obtain ⟨j', x', tt', hj', hx', hpc'⟩ := hcall
  have hd' : (∃ n, x' = .bl n ∧ callDest ic = some n) ∨ (∃ r, x' = .blr r ∧ callDest ic = none) := by
    obtain ⟨dest, us, ds⟩ := ic
    rcases hic with rfl | ⟨ti, rfl⟩ <;> cases dest <;> simp [MInst.callInsn?] at hx' <;>
      subst hx' <;> simp [callDest]
  rw [hdest] at hd'
  obtain ⟨j, t, hj, hpc⟩ := hx
  have e : x' = x := by
    have h1 := insnAt_pc hR hj' hg.prog hpc'
    rw [insnAt_pc hR hj hg.prog hpc] at h1
    exact (Option.some.inj h1).symm
  subst e
  have hdd : d = callDest info := by
    rcases hd with ⟨n, rfl, rfl⟩ | ⟨r, rfl, rfl⟩ <;>
      rcases hd' with ⟨n', h1, h2⟩ | ⟨r', h1, h2⟩ <;> simp_all
  rw [hdd]
  exact hn

/-- **At a state of the old realisation's trace, the machine with unwinding steps as the old
one.** -/
theorem RLU.stepU_eq {R : RLU} (hR : R.Wf)
    (hU : CalleeUnwOkG R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.XR R.U R.vc.CallSite R.gv)
    {u : Arm.ArmState} (hg : R.GoodX u) : R.stepU u = R.step u := by
  obtain ⟨x, ⟨j, t, hj, hpc⟩, -⟩ := hg.line
  have hins := insnAt_pc hR hj hg.prog hpc
  have hat : R.AtLine u x := ⟨j, t, hj, hpc⟩
  unfold RLU.stepU RL.step
  cases x with
  | bl n => simp only [Unw.ArmStepU, ArmStepX, hins,
      RLU.noRaise_of_goodX hR hU hg hat (.inl ⟨n, rfl, rfl⟩)]
  | blr r => simp only [Unw.ArmStepU, ArmStepX, hins,
      RLU.noRaise_of_goodX hR hU hg hat (.inr ⟨r, rfl, rfl⟩)]
  | _ => simp only [Unw.ArmStepU, hins]

/-- Along the old realisation's trace both machines run the same states. -/
theorem RLU.iterN_stepU {R : RLU} (hR : R.Wf)
    (hU : CalleeUnwOkG R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.XR R.U R.vc.CallSite R.gv) :
    ∀ (n : Nat) (s : Arm.ArmState), (∀ i < n, R.GoodX (iterN R.step i s)) →
      iterN R.stepU n s = iterN R.step n s
  | 0, _, _ => rfl
  | n + 1, s, h => by
    simp only [iterN]
    have h0 : R.GoodX s := h 0 (by omega)
    rw [RLU.stepU_eq hR hU h0]
    exact RLU.iterN_stepU hR hU n _ fun i hi => h (i + 1) (by omega)

/-! ## Changing the semantics of one step -/

/-- An allocated-code step under `sem₁` is one under `sem₂` when the two agree on the stepped
instruction's uses and world. -/
theorem mstep_congr {V W : Type} {vc : VCode} {rf : RFunc} {keep : Reg → V → V}
    {sem₁ sem₂ : ISem V W} {c c' : MConf V W} (h : MStep vc sem₁ keep rf c c')
    (he : ∀ b k allocs its m w vb i ops, c = .run ⟨b, .op k allocs :: its, m, w⟩ →
      vc.blocks[b]? = some vb → vb.insts[k]? = some i → i.operands = .ok ops →
      sem₁ i (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w =
        sem₂ i (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w) :
    MStep vc sem₂ keep rf c c' := by
  cases h with
  | move => exact .move
  | op hvb hi hops hsz hsem hlen hho hcl hn =>
    exact .op hvb hi hops hsz (by rw [← he _ _ _ _ _ _ _ _ _ rfl hvb hi hops]; exact hsem) hlen hho
      hcl hn

/-- `AInv` is kept by every step of the allocated code from a `Q` state, for any semantics. -/
theorem aInv_stepS {R : RL} {sem : Sem} (hR : R.Wf) {s : Arm.ArmState}
    {c c' : MConf CV Arm.ArmState} (hq : Q R s c) (hA : AInv R c)
    (h : MStep R.vc sem ckeep R.rf c c') : AInv R c' := by
  have hck := (lowerRFunc_ok hR.alloc).2.2
  cases h with
  | @move b src dst its m w =>
    intro hb hop
    subst hb
    obtain ⟨j, vb, items, pre, -, -, -, -, -, -, hit, hsplit, -⟩ := hq
    obtain ⟨hmv, hrd⟩ := ctlCheck_before hck hit hsplit hop
    have hA' := hA rfl (by obtain ⟨a, ha⟩ := hop; exact ⟨a, List.mem_cons_of_mem _ ha⟩)
    intro r hr
    have hne : Loc.reg r ≠ dst := by
      intro e; subst e; simp [RItem.regDst] at hrd
    rw [upd_other hne]
    exact hA' r hr
  | op _ _ _ _ _ _ _ _ hn =>
    cases hn with
    | next =>
      intro hb hop
      subst hb
      obtain ⟨j, vb0, items, pre, -, -, -, -, -, -, hit, hsplit, -⟩ := hq
      have := (ctlCheck_before hck hit hsplit hop).1
      simp [RItem.isMove] at this
    | goto _ hs _ =>
      intro hb
      exact absurd hb (ctlCheck_succ hck hs)
    | ret => trivial
    | halt => trivial

/-! ## `Realizes` with unwinding -/

/-- The raising `tryCall` case of `realizes_allU`: from `Q` at a `tryCall` item whose callee
raises, the machine with unwinding reaches `Q` at an `MStep` successor (the landing pad), the
states before it `GoodXU` (the raising call state itself is `RaiseX`). -/
def RealizesTryRaise (R : RLU) (semU : Sem) : Prop :=
  ∀ (s : Arm.ArmState) (b k : Nat) (allocs : Array Loc) (its : List RItem) (m : Loc → CV)
    (w : Arm.ArmState) (vb : VBlock) (info : CallInfo) (ti : TryInfo) (ops : Array Operand)
    (c' : MConf CV Arm.ArmState) (obj : BitVec 64) (w' : Arm.ArmState),
    Q R.toRL s (.run ⟨b, .op k allocs :: its, m, w⟩) → AInv R.toRL (.run ⟨b, .op k allocs :: its, m, w⟩) →
    R.vc.blocks[b]? = some vb → vb.insts[k]? = some (.tryCall info ti) →
    (MInst.tryCall info ti).operands = .ok ops →
    R.XR.raise (callDest info) (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w =
      some (obj, w') →
    MStep R.vc semU ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c' →
    ∃ n c'', MStep R.vc semU ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c'' ∧
      Q R.toRL (iterN R.stepU n s) c'' ∧ ∀ i < n, R.GoodXU (iterN R.stepU i s)

/-- `RealizesTryRaise` with any trace predicate `P` (`RealizesTryRaise R semU` is
`RealizesTryRaiseP R semU R.GoodXU`). -/
def RealizesTryRaiseP (R : RLU) (semU : Sem) (P : Arm.ArmState → Prop) : Prop :=
  ∀ (s : Arm.ArmState) (b k : Nat) (allocs : Array Loc) (its : List RItem) (m : Loc → CV)
    (w : Arm.ArmState) (vb : VBlock) (info : CallInfo) (ti : TryInfo) (ops : Array Operand)
    (c' : MConf CV Arm.ArmState) (obj : BitVec 64) (w' : Arm.ArmState),
    Q R.toRL s (.run ⟨b, .op k allocs :: its, m, w⟩) → AInv R.toRL (.run ⟨b, .op k allocs :: its, m, w⟩) →
    R.vc.blocks[b]? = some vb → vb.insts[k]? = some (.tryCall info ti) →
    (MInst.tryCall info ti).operands = .ok ops →
    R.XR.raise (callDest info) (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w =
      some (obj, w') →
    MStep R.vc semU ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c' →
    ∃ n c'', MStep R.vc semU ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c'' ∧
      Q R.toRL (iterN R.stepU n s) c'' ∧ ∀ i < n, P (iterN R.stepU i s)

theorem RealizesTryRaiseP.mono {R : RLU} {semU : Sem} {P P' : Arm.ArmState → Prop}
    (h : RealizesTryRaiseP R semU P) (hP : ∀ u, P u → P' u) : RealizesTryRaiseP R semU P' :=
  fun s b k allocs its m w vb info ti ops c' obj w' h1 h2 h3 h4 h5 h6 h7 =>
    let ⟨n, c'', a, b', c⟩ := h s b k allocs its m w vb info ti ops c' obj w' h1 h2 h3 h4 h5 h6 h7
    ⟨n, c'', a, b', fun i hi => hP _ (c i hi)⟩

/-- **`Realizes` with unwinding, for any trace predicate `P` above the old trace's `GoodX`**
(`realizes_allU`'s generalisation): from any `Realizes` of a semantics `sem₀` with which `semU`
agrees off raising calls and which raises (`.halt`) at a raising `call`, and the raising
`tryCall`s realised with trace `P`. -/
theorem realizes_allUP {R : RLU} (hR : R.Wf) {sem₀ semU : Sem} {P : Arm.ArmState → Prop}
    (hP : ∀ u, R.GoodX u → P u)
    (hU : CalleeUnwOkG R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.XR R.U R.vc.CallSite R.gv)
    (hreal : Realizes R.vc R.rf sem₀ ckeep R.step (QA R.toRL) R.GoodX)
    (hagree : ∀ i uses w, NoRaise R.XR i uses w → semU i uses w = sem₀ i uses w)
    (hcall : ∀ info uses w r obj w', semU (.call info) uses w = some r →
      R.XR.raise (callDest info) uses w = some (obj, w') → r.2.2 = .halt)
    (htry : RealizesTryRaiseP R semU P) :
    Realizes R.vc R.rf semU ckeep R.stepU (QA R.toRL) P := by
  intro s c c' hqa hm
  -- a step without a raising callee: the old realisation, on the same run
  have old : MStep R.vc sem₀ ckeep R.rf c c' →
      (∀ b k allocs its m w vb i ops, c = .run ⟨b, .op k allocs :: its, m, w⟩ →
        R.vc.blocks[b]? = some vb → vb.insts[k]? = some i → i.operands = .ok ops →
        NoRaise R.XR i (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w) →
      ∃ n c'', MStep R.vc semU ckeep R.rf c c'' ∧
        QA R.toRL (iterN R.stepU n s) c'' ∧ ∀ i < n, P (iterN R.stepU i s) := by
    intro hm0 hnr
    obtain ⟨n, c'', hm'', hqa'', ht⟩ := hreal s c c' hqa hm0
    have hit := RLU.iterN_stepU hR hU n s ht
    refine ⟨n, c'', mstep_congr hm'' fun b k allocs its m w vb i ops hc hvb hi hops =>
      (hagree _ _ _ (hnr b k allocs its m w vb i ops hc hvb hi hops)).symm, by rw [hit]; exact hqa'',
      fun i hi => ?_⟩
    rw [RLU.iterN_stepU hR hU i s fun i' hi' => ht i' (by omega)]
    exact hP _ (ht i hi)
  cases hm with
  | move =>
    exact old .move fun _ _ _ _ _ _ _ _ _ hc => by cases hc
  | @op b k allocs its m w vb i ops outs outs' w' ctl m2 c' hvb hi hops hsz hsem hlen hho hcl hn =>
    have hstep : MStep R.vc semU ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c' :=
      MStep.op hvb hi hops hsz hsem hlen hho hcl hn
    by_cases hr : NoRaise R.XR i (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w
    · refine old (mstep_congr hstep fun b' k' allocs' its' m' w'' vb' i' ops' hc hvb' hi' hops' => ?_)
        fun b' k' allocs' its' m' w'' vb' i' ops' hc hvb' hi' hops' => ?_
      · cases hc
        rw [hvb] at hvb'; cases hvb'
        rw [hi] at hi'; cases hi'
        rw [hops] at hops'; cases hops'
        exact hagree _ _ _ hr
      · cases hc
        rw [hvb] at hvb'; cases hvb'
        rw [hi] at hi'; cases hi'
        rw [hops] at hops'; cases hops'
        exact hr
    · -- a raising callee
      simp only [NoRaise, Classical.not_forall] at hr
      obtain ⟨info, hik, hraise⟩ := hr
      obtain ⟨⟨obj, w2⟩, hraise⟩ := Option.ne_none_iff_exists'.mp hraise
      have hqA := qa_op hqa hvb hi (by rcases hik with rfl | ⟨ti, rfl⟩ <;> intro us h <;> cases h)
      rcases hik with rfl | ⟨ti, rfl⟩
      · -- a raising `call`: the activation ends (nothing to realise)
        have hc := hcall info _ w (outs, w', ctl) obj w2 hsem hraise
        simp only at hc
        subst hc
        cases hn with
        | halt => exact ⟨0, _, hstep, .inl ⟨trivial, trivial⟩, fun _ h => absurd h (Nat.not_lt_zero _)⟩
      · obtain ⟨n, c'', hm'', hq'', ht⟩ := htry s b k allocs its m w vb info ti ops c' obj w2 hqA.1
          hqA.2 hvb hi hops hraise hstep
        exact ⟨n, c'', hm'', .inl ⟨hq'', aInv_stepS hR hqA.1 hqA.2 hm''⟩, ht⟩

/-- **`Realizes` with unwinding**, from any `Realizes` of a semantics `sem₀` with which `semU`
agrees off raising calls and which raises (`.halt`) at a raising `call`; the trace predicate
`GoodXU` (the old trace's `GoodX` states and the raising-call states). -/
theorem realizes_allU {R : RLU} (hR : R.Wf) {sem₀ semU : Sem}
    (hU : CalleeUnwOkG R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.XR R.U R.vc.CallSite R.gv)
    (hreal : Realizes R.vc R.rf sem₀ ckeep R.step (QA R.toRL) R.GoodX)
    (hagree : ∀ i uses w, NoRaise R.XR i uses w → semU i uses w = sem₀ i uses w)
    (hcall : ∀ info uses w r obj w', semU (.call info) uses w = some r →
      R.XR.raise (callDest info) uses w = some (obj, w') → r.2.2 = .halt)
    (htry : RealizesTryRaise R semU) :
    Realizes R.vc R.rf semU ckeep R.stepU (QA R.toRL) R.GoodXU :=
  realizes_allUP hR (fun _ h => .inl h) hU hreal hagree hcall htry

end Backend.Proof
