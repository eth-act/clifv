module

public import FV.E2E.LinkArm
public import FV.E2E.UnwindStatement
public import FV.E2E.WorldUnwindCore
public import FV.Backend.Proof.LowerSimUCheck
public import FV.Backend.Proof.LowerSimURaise
public import FV.Clif.LinkClifXN

@[expose] public section

/-!
# Linking at the Arm level with unwinding: the linked machine (S10f, #233)

`FV/E2E/LinkArm.lean`'s linked machine (`LinkSys.hooks`, `LinkSys.mach`), with unwinding: the
program callees run their compiled code on the machine with unwinding (`Unw.ArmStepU`), and a
program callee whose run leaves its frame by unwinding raises at the call (`Unw.UnwHooks`).

* `LinkSysU`: a `LinkSys` with the base environment's raising callees on the machine (`Ub`;
  `Unw.UnwHooks.none`: none raises), the CLIF base with unwinding (`envX`, `envX.toEnv = base`),
  the base callees' exceptional results at the VCode level (`XRb`), and the callee runs with
  unwinding (`crunX M`: by default the whole-program run with unwinding of at most `M` steps).
* `Art.tables`: the unwind tables of a compiled function as the unwinder reads them (the emitted
  CIE, the FDE rows `unwindRows`, the LSDA call-site table `callSites`).
* `ExitU`: the callee's run leaves its frame by unwinding at its first return (the step into it
  is an `UnwExit`, `FV/E2E/WorldUnwindCore.lean`).
* `LinkSysU.layer M`: the hooks and the raising callees of depth `M`. At depth `M + 1` a call of a
  function `g` of `P` runs `g`'s code on `machU M g` up to its first return (`RetOf`, as
  `linkedCall`); if the step into that return left `g`'s frame by unwinding (`ExitU`), the call
  raises (`raise`: the exception object in x0 and that state, with the caller's program), else
  it returns there (`call`). Other calls and TLS: the base hooks `Hb`, `Ub`.
* `LinkSysU.machU M g`: the machine of an activation of `g` at depth `M`.
* `layer_none`/`machU_none`: without raising base callees the linked machine with unwinding is
  `LinkArm`'s linked machine (nothing raises at any depth).
* `backend_correct_program_budgetU_none`: the restriction theorem — `backend_correct_program_budget`
  as an `ArmRefinesU` statement about the whole-program run with unwinding (`Clif.runLoopX` of the
  base environment, whose externs never unwind) on the linked machine with unwinding.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.Proof.UnwindTables

/-- **The unwind tables of a compiled function** as the unwinder reads them: the emitted CIE,
the FDE rows (`unwindRows`) and the LSDA call-site table (`callSites`). -/
noncomputable def Art.tables (a : Art) : Unw.FnTables :=
  ⟨cieInsns, insnsFrom 0 ((unwindRows a.af a.fa).toOption.getD []),
    ((callSites a.af a.fa).toOption.getD none).map (List.map (·.entry))⟩

/-- The tables of a compiled function are the emitted ones (the premises `hsites`/`hlsda`,
`hrows`/`hcie`/`hfde` of the per-function theorem with unwinding). -/
theorem Art.tables_eq {a : Art} {lsda : Option (List CallSite)}
    (hs : callSites a.af a.fa = .ok lsda) {rows : List (Nat × Cfi)}
    (hr : unwindRows a.af a.fa = .ok rows) :
    a.tables.lsda = lsda.map (List.map (·.entry)) ∧ a.tables.cie = cieInsns ∧
      a.tables.fde = insnsFrom 0 rows := by
  simp [Art.tables, hs, hr, Except.toOption]

open Classical in
/-- **The callee `a` called at `s`, run by `M`, leaves its frame by unwinding**: its first return
(`RetOf`, as `linkedCall`) is reached by a step that unwinds its frame (`UnwExit` for its raising
callees `U` and tables `T`). -/
def ExitU (M : Arm.ArmState → Arm.ArmState) (U : Unw.UnwHooks) (T : Unw.FnTables) (a : Art)
    (s : Arm.ArmState) : Prop :=
  ∃ h : (∃ n, RetOf a s (runX M n (enterAt a s))),
    0 < firstNat _ h ∧ UnwExit U T a.fa (runX M (firstNat _ h - 1) (enterAt a s))

open Classical in
/-- **A `bl` of `a` that raises**: when the run leaves `a`'s frame by unwinding (`ExitU`), the
exception object in x0 and the state at the return address, with the caller's program. -/
noncomputable def raisedCall (M : Arm.ArmState → Arm.ArmState) (U : Unw.UnwHooks) (T : Unw.FnTables)
    (a : Art) (s : Arm.ArmState) : Option (BitVec 64 × Arm.ArmState) :=
  if ExitU M U T a s then
    some (xreg 0 (linkedCall M a s), linkedCall M a s)
  else Option.none

open Classical in
/-- **A `bl` of `a` that returns**: `linkedCall`, unless the run leaves `a`'s frame by unwinding
(then the call raises, `raisedCall`, and the hook's state is an error). -/
noncomputable def returnedCall (M : Arm.ArmState → Arm.ArmState) (U : Unw.UnwHooks)
    (T : Unw.FnTables) (a : Art) (s : Arm.ArmState) : Arm.ArmState :=
  if ExitU M U T a s then junkAt s else linkedCall M a s

/-- The raising hook of the linked machine: a `bl` of a function `g` of `P`, and a `blr` whose
target register holds `g`'s link-time address, raise as `pr g s`; the other calls: the base's. -/
def raiseHook (Ub : Unw.UnwHooks) (Xb : ExtSem) (P : Clif.Program)
    (pr : Clif.Function → Arm.ArmState → Option (BitVec 64 × Arm.ArmState)) (d : Option String)
    (s : Arm.ArmState) : Option (BitVec 64 × Arm.ArmState) :=
  match d with
  | some n => (match P.func? n with
    | some g => pr g s
    | Option.none => Ub.raise d s)
  | Option.none => (match (blrTarget s).bind (symCallee Xb P) with
    | some g => pr g s
    | Option.none => Ub.raise Option.none s)

/-- **A linked program with unwinding**: `LinkSys` with the base environment's raising callees
(machine `Ub`, VCode `XRb`), the CLIF base with unwinding `envX` and the callee runs with
unwinding `crunX`. -/
structure LinkSysU extends LinkSys where
  Ub : Unw.UnwHooks
  envX : Clif.XEnv
  XRb : XRaise
  crunX : Nat → Clif.State → Clif.XOutcome := fun M s => Clif.runLoopX envX P M s.toX

namespace LinkSysU

variable (L : LinkSysU)

/-- **The hooks and raising callees of the linked machine with unwinding**, by depth: at depth
`M + 1` a call of a function `g` of `P` runs `g`'s code on the machine of depth `M`
(`returnedCall`, `raisedCall`); at depth `0` it gives an error state and does not raise. -/
noncomputable def layer : Nat → ArmHooks × Unw.UnwHooks
  | 0 => (⟨LinkSys.callHook L.Hb L.Xb L.P (fun _ s => junkAt s), L.Hb.tls⟩,
      ⟨raiseHook L.Ub L.Xb L.P fun _ _ => Option.none⟩)
  | M + 1 =>
    (⟨LinkSys.callHook L.Hb L.Xb L.P (fun g s => returnedCall
        (Unw.ArmStepU L.Xb (layer M).1 (layer M).2 (L.A g).tables (L.A g).fa) (layer M).2
        (L.A g).tables (L.A g) s), L.Hb.tls⟩,
      ⟨raiseHook L.Ub L.Xb L.P fun g s => raisedCall
        (Unw.ArmStepU L.Xb (layer M).1 (layer M).2 (L.A g).tables (L.A g).fa) (layer M).2
        (L.A g).tables (L.A g) s⟩)

/-- The hooks of depth `M`. -/
noncomputable def hooksU (M : Nat) : ArmHooks := (L.layer M).1

/-- The raising callees of depth `M`. -/
noncomputable def UU (M : Nat) : Unw.UnwHooks := (L.layer M).2

/-- **The machine with unwinding of an activation of `g` at depth `M`.** -/
noncomputable def machU (M : Nat) (g : Clif.Function) : Arm.ArmState → Arm.ArmState :=
  Unw.ArmStepU L.Xb (L.hooksU M) (L.UU M) (L.A g).tables (L.A g).fa

theorem raiseHook_none (Xb : ExtSem) (P : Clif.Program) :
    raiseHook Unw.UnwHooks.none Xb P (fun _ _ => Option.none) = fun _ _ => Option.none := by
  funext d s
  unfold raiseHook
  split
  · split <;> rfl
  · split <;> rfl

/-- **Without raising base callees the linked machine with unwinding is `LinkArm`'s**: at every
depth the hooks are `LinkSys.hooks` and nothing raises. -/
theorem layer_none (h : L.Ub = Unw.UnwHooks.none) :
    ∀ M, L.layer M = (L.toLinkSys.hooks M, Unw.UnwHooks.none)
  | 0 => by
    rw [layer, h, raiseHook_none]
    rfl
  | M + 1 => by
    have ih := layer_none h M
    have hx : ∀ g s, ¬ ExitU (Unw.ArmStepU L.Xb (L.toLinkSys.hooks M) Unw.UnwHooks.none
        (L.A g).tables (L.A g).fa) Unw.UnwHooks.none (L.A g).tables (L.A g) s :=
      fun g s ⟨_, _, hu⟩ => not_unwExit_none _ _ _ hu
    have e1 : (fun g s => returnedCall (Unw.ArmStepU L.Xb (L.layer M).1 (L.layer M).2
        (L.A g).tables (L.A g).fa) (L.layer M).2 (L.A g).tables (L.A g) s) =
        fun g s => linkedCall (ArmStepX L.Xb (L.toLinkSys.hooks M) (L.A g).fa) (L.A g) s := by
      funext g s
      rw [ih]
      rw [returnedCall, ite_eq_right (hx g s), Unw.armStepU_none]
    have e2 : (fun g s => raisedCall (Unw.ArmStepU L.Xb (L.layer M).1 (L.layer M).2
        (L.A g).tables (L.A g).fa) (L.layer M).2 (L.A g).tables (L.A g) s) =
        fun _ _ => Option.none := by
      funext g s
      rw [ih]
      simp only [raisedCall, hx g s, ↓reduceIte]
    rw [layer, e1, e2, h, raiseHook_none]
    rfl

/-- **Without raising base callees the machine with unwinding is `LinkArm`'s linked machine.** -/
theorem machU_none (h : L.Ub = Unw.UnwHooks.none) (M : Nat) (g : Clif.Function) :
    L.machU M g = L.toLinkSys.mach M g := by
  simp only [machU, hooksU, UU, L.layer_none h M, Unw.armStepU_none]
  rfl

/-- **The premises of the linked program with unwinding** (`LinkSys.Ok`'s extension): the CLIF
base with unwinding is the base's (`envX`); per function, the lowering's unwinding validator and
the tables and checks the unwinder's model needs (`callSites`, `unwindRows`, `padsNonzeroB`,
`lastCallsOk`, `savedCheck`); the indirect-call scope of the runs with unwinding; and the base
environment's raising callees: their exceptional results at the program's call sites
(`XRaiseOk`, `XRaiseIndOk`), exclusivity with normal returns, their effect on the error field and
the program, the machine's raising callees' contract at the base call sites (`baseUnw`: a raise
of `XRb` is one of `Ub`; `baseNoRaise`: a base callee that returns normally does not raise on the
machine), and (when program callees have slots) that the base externs that unwind keep the
slot-placement oracle, and (when program callees have slots or a function of `P` has an
outgoing-argument area) that the base externs create no allocation (`baseKeepsAllocsU`: their
allocations are among their arguments', also when they unwind). -/
structure OkU : Prop where
  envX : L.envX.toEnv = L.base
  lowerU : ∀ g ∈ L.P.funcs, lowerCheckU g (L.A g).vc = true
  sites : ∀ g ∈ L.P.funcs, ∃ lsda, callSites (L.A g).af (L.A g).fa = .ok lsda
  rows : ∀ g ∈ L.P.funcs, ∃ rows, unwindRows (L.A g).af (L.A g).fa = .ok rows
  pads : ∀ g ∈ L.P.funcs, padsNonzeroB (L.A g).af (L.A g).fa = true
  last : ∀ g ∈ L.P.funcs, lastCallsOk (L.A g).af (L.A g).fa = true
  saved : ∀ g ∈ L.P.funcs, savedCheck (L.A g).vcp (L.A g).rf = true
  indScopeX : ∀ g ∈ L.P.funcs, ¬ Clif.IndFree g → Clif.IndScopeX L.P L.envX L.syms
  baseXR : ∀ g ∈ L.P.funcs, ∀ F slotOff out c, XRaiseOk L.envX
    ((g.externs.map (·.2)).filter fun e => (L.P.func? e.name).isNone)
    (RelW ⟨F, L.syms, slotOff, out⟩ g c) L.Xb L.XRb
  baseXRI : ∀ g ∈ L.P.funcs, ∀ F slotOff out c, XRaiseIndOk { L.envX with sigOf := fun _ => none }
    (indSigs g) (RelW ⟨F, L.syms, slotOff, out⟩ g c) L.Xb L.XRb
  baseExcl : ∀ d uses w, L.BaseDest d → L.Xb.call d uses w ≠ none → L.XRb.raise d uses w = none
  baseRaiseExt : ∀ d uses w obj w', L.BaseDest d → L.XRb.raise d uses w = some (obj, w') →
    Arm.r .ERR w = .None → Arm.r .ERR w' = .None ∧ w'.program = w.program
  baseUnw : ∀ g ∈ L.P.funcs, ∀ info, (L.A g).vcp.CallSite info → L.BaseDest (destOf info) →
    ∀ (i : MInst), (i = .call info ∨ ∃ ti, i = .tryCall info ti) →
    ∀ F K G s0 Pc, UnwSoundG F K G s0 Pc (GotV (L.A g).vcp) L.Xb L.XRb L.Ub info i
  baseNoRaise : ∀ g ∈ L.P.funcs, ∀ info, (L.A g).vcp.CallSite info → L.BaseDest (destOf info) →
    ∀ (i : MInst), (i = .call info ∨ ∃ ti, i = .tryCall info ti) →
    ∀ (F : BitVec 64 → Prop) (K : Nat) (G : BitVec 64 → Prop) (s0 : Arm.ArmState)
      (Pc : BitVec 64 → MInst → Prop) (s : Arm.ArmState), K ≤ (spOf s).toNat →
    (∀ a, StackBelow K (spOf s) a → F a) → (∀ a, G a → s.mem a = s0.mem a) →
    ∀ (c : CheckCtx) (wh : String) (ops : Array Operand) (regs : Array Reg) (i' : MInst)
      (w : Arm.ArmState),
      i.operands = .ok ops → c.checkStatic wh ops (regs.map .reg) i.clobbers = .ok () →
      i.assign regs = .ok i' → Pc (Arm.r .PC s) i' → SameWorld F s w →
      Arm.CheckSPAlignment s → Arm.r .ERR s = .None →
      gotGuard (GotV (L.A g).vcp) L.Xb info (useVals ops regs s) →
      L.Xb.call (callDest info) (useVals ops regs s) w ≠ none →
      L.Ub.raise (callDest info) s = none
  baseKeepsPlaceU : L.NeedSlots → ∀ n g, L.envX.extern n = some g → ∀ vals m e m',
    g vals m = .unwound e m' → m'.place = m.place
  baseKeepsAllocsU : (L.NeedSlots ∨
      ∃ g ∈ L.P.funcs, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase ≠ 0) →
    ∀ n g, L.envX.extern n = some g → ∀ vals m,
      (∀ rvals m', g vals m = .returned rvals m' → ∀ x ∈ m'.allocs, x ∈ m.allocs) ∧
      (∀ e m', g vals m = .unwound e m' → ∀ x ∈ m'.allocs, x ∈ m.allocs)

end LinkSysU

/-- `ArmRefines` of an outcome of `Clif.run` is `ArmRefinesU` of its lift to the runs with
unwinding. -/
theorem armRefinesU_toX {fb : FnBin} {base ra : BitVec 64} {astep : Arm.ArmState → Arm.ArmState}
    {s : Arm.ArmState} {o : Clif.Outcome} (h : ArmRefines fb base ra astep s o) :
    ArmRefinesU fb base ra astep s o.toX := by
  cases o <;> exact h

/-- **The restriction theorem**: `backend_correct_program_budget` on the linked machine with
unwinding, against the whole-program run with unwinding of the base environment (whose externs
never unwind), when no base callee raises on the machine (`Ub = none`). -/
theorem backend_correct_program_budgetU_none (L : LinkSysU) (hL : L.Ok)
    (hU : L.Ub = Unw.UnwHooks.none)
    {κ : Nat → Clif.Function → Nat} (hκ : L.Budget κ) {f : Clif.Function}
    (hf : f ∈ L.P.funcs) (M : Nat) {ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val}
    {cs : Clif.State}
    (hent : AbiEntry (L.A f).fb (L.A f).base ra s) (hres : StackAvail (κ M f) (L.A f).af s)
    (hF : L.F = frameWG (κ M f) (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase
      (RAFrame.compute (L.A f).vcp (L.A f).rf).size (L.A f).af L.Img s)
    (hgfree : ∀ a, L.Img a → ¬ StackBelow (frameDrop (L.A f).af + κ M f) (spv s) a)
    (himg : ∀ a, L.Img a → s.mem a = L.imgMem a)
    (hbe : BodyEntry (L.A f).af s w₀) (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hsav : StackArgsAvoid L.Img f.sig args s)
    (hrel : Rel.holds ⟨L.F, L.syms, (L.A f).af.slotBase,
      (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (hpl : L.NeedSlots → L.PlaceAt cs.mem (spv w₀))
    (htr : TrapsExplicit (Clif.linkEnvN L.P L.base M) L.P.bare cs) :
    ArmRefinesU (L.A f).fb (L.A f).base ra (L.machU M f) s
      (Clif.runLoopX L.base.toX L.P (M + 1) cs.toX) := by
  rw [L.machU_none hU, Clif.runLoopX_toX]
  exact armRefinesU_toX (backend_correct_program_budget L.toLinkSys hL hκ hf M hent hres hF hgfree
    himg hbe hargs hcs hsav hrel hpl htr)

end E2E
