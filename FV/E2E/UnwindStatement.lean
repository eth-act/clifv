import FV.E2E.Compose
import FV.E2E.UnwindSem
import FV.Clif.Unwind

/-!
# The per-function theorem with unwinding: observables, layers, conclusion (S10e, #232)

`docs/plans/unwinding.md`, "The exceptional edge in the per-function theorem". Additive: every
statement of `FV/E2E/Statement.lean` is unchanged; the normal-return theorems are the
restriction to runs without unwinding (`armRefines_of_armRefinesU`).

* `ExnRel e obj`: the CLIF exception `e` is the Rust exception with object `obj` as the Arm
  side sees it: a landing pad receives `[obj, 0]` (x0 = the object, x1 = Rust's selector 0),
  and the `tag 0` (cleanup) and `tag 1` (catch-all) handlers catch it (Rust's personality runs
  every landing pad of a Rust panic; `docs/plans/unwinding.md`, "Risks").
* `VUnwFrom`/`VUnwinds`: the VCode run reaches a `call` whose callee raises (`XRaise`) and
  whose step ends the activation (`csemU`'s `.halt`), with the exception object and the world
  after the unwinder restored the call: `VReturns`/`VTraps`' counterpart.
* `ReachX`, `TrapsExplicitX`: `TrapsExplicit` for the runs with unwinding (`Clif.stepX`).
* The layer statements `IselSimU` (CLIF `runLoopX` → VCode), `PrepareCorrectU` (`prepare`),
  `RegLevelCorrectU`/`RegLevelCorrectUEx` (VCode → Arm, the machine `astep` with unwinding),
  each the old one plus the unwinding observable.
* `ArmRefinesU`: `ArmRefines` for an outcome of `runLoopX`; an `unwound e cm` run is matched by
  an Arm run that returns to the caller as the ABI requires (`ArmRet`: at the return address,
  sp and the callee-saved registers as at entry — the unwinder continues there with the
  caller's frame) with the exception object in x0 (`ExnRel`) and the live memory agreeing.
* `backend_correct_of_layersU{,_ex}`: the composition.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- **The CLIF exception `e` is the Rust exception object `obj`.** -/
def ExnRel (e : Clif.Exn) (obj : BitVec 64) : Prop :=
  e.payload = [⟨.i64, obj⟩, ⟨.i64, 0⟩] ∧ e.catches 0 = true ∧ e.catches 1 = true

/-- From `vs`, the VCode run reaches a `call` whose callee raises the exception object `obj`
(`XR`) and whose step ends the activation, the world after the unwinder restored the call
being `w'`. -/
def VUnwFrom (vc : VCode) (sem : Sem) (XR : XRaise) (vs : VState CV Arm.ArmState) (obj : BitVec 64)
    (w' : Arm.ArmState) : Prop :=
  ∃ b k ρ w vb info ops outs, Star (VStep vc sem) (.run vs) (.run ⟨b, k, ρ, w⟩) ∧
    vc.blocks[b]? = some vb ∧ vb.insts[k]? = some (.call info) ∧
    (MInst.call info).operands = .ok ops ∧
    XR.raise (callDest info) (vuses ops ρ) w = some (obj, w') ∧
    sem (.call info) (vuses ops ρ) w = some (outs, w', .halt) ∧
    outs.length = (ops.toList.filter Operand.isDef).length

theorem VUnwFrom.prefix {vc : VCode} {sem : Sem} {XR : XRaise} {vs vs' : VState CV Arm.ArmState}
    {obj : BitVec 64} {w' : Arm.ArmState}
    (h : Star (VStep vc sem) (.run vs) (.run vs')) (h' : VUnwFrom vc sem XR vs' obj w') :
    VUnwFrom vc sem XR vs obj w' := by
  obtain ⟨b, k, ρ, w, vb, info, ops, outs, hs, h1⟩ := h'
  exact ⟨b, k, ρ, w, vb, info, ops, outs, h.trans hs, h1⟩

/-- The VCode run from the entry ends by an exception: `VUnwFrom` from the entry. -/
def VUnwinds (vc : VCode) (sem : Sem) (XR : XRaise) (ρ₀ : Nat → CV) (w₀ : Arm.ArmState)
    (obj : BitVec 64) (w : Arm.ArmState) : Prop :=
  VUnwFrom vc sem XR ⟨0, 0, ρ₀, w₀⟩ obj w

/-- `xs'` is reachable from `xs` by steps with unwinding that continue. -/
inductive ReachX (env : Clif.XEnv) (p : Clif.Program) : Clif.XState → Clif.XState → Prop
  | refl (xs : Clif.XState) : ReachX env p xs xs
  | step {xs xs' xs'' : Clif.XState} : Clif.stepX env p xs = .next xs' → ReachX env p xs' xs'' →
      ReachX env p xs xs''

theorem ReachX.snoc {env : Clif.XEnv} {p : Clif.Program} {xs xs' xs'' : Clif.XState}
    (h : ReachX env p xs xs') (h' : Clif.stepX env p xs' = .next xs'') : ReachX env p xs xs'' := by
  induction h with
  | refl => exact .step h' (.refl _)
  | step h1 _ ih => exact .step h1 (ih h')

/-- **`TrapsExplicit` for the runs with unwinding**: the same clauses, over the states the run
with unwinding reaches (a handler path after a caught exception is reachable only there). -/
structure TrapsExplicitX (env : Clif.XEnv) (p : Clif.Program) (cs : Clif.State) : Prop where
  stmt : ∀ xs c st rest, ReachX env p cs.toX xs → Clif.step env.toEnv p xs.s = .trapped c →
    xs.s.frame.body = st :: rest → explicitTrapInst st.inst = true
  tryCall : ∀ xs c fn args et, ReachX env p cs.toX xs → Clif.step env.toEnv p xs.s = .trapped c →
    xs.s.frame.body = [] → xs.s.frame.term = .tryCall fn args et →
    ∀ B ∈ cs.frame.func.blocks, B.term ≠ .tryCall fn args et
  tryCallInd : ∀ xs c callee args et, ReachX env p cs.toX xs →
    Clif.step env.toEnv p xs.s = .trapped c →
    xs.s.frame.body = [] → xs.s.frame.term = .tryCallIndirect callee args et →
    ∀ B ∈ cs.frame.func.blocks, B.term ≠ .tryCallIndirect callee args et
  indirect : ∀ xs st rest sig callee args, ReachX env p cs.toX xs → xs.s.frame.body = st :: rest →
    st.inst = .callIndirect sig callee args → (∃ B ∈ cs.frame.func.blocks, st ∈ B.body) → ∀ cv,
    xs.s.frame.get callee = .ok cv → ∀ g ∈ p.funcs, xs.s.mem.symbols g.name ≠ some cv.toNat
  tryIndirect : ∀ xs callee args et, ReachX env p cs.toX xs → xs.s.frame.body = [] →
    xs.s.frame.term = .tryCallIndirect callee args et →
    (∃ B ∈ cs.frame.func.blocks, B.term = .tryCallIndirect callee args et) → ∀ cv,
    xs.s.frame.get callee = .ok cv → ∀ g ∈ p.funcs, xs.s.mem.symbols g.name ≠ some cv.toNat

/-! ## The layer statements -/

/-- **CLIF → VCode with unwinding.** `IselSim` for `runLoopX`, plus: a run that ends by an
exception is a VCode run that ends at a raising call (`VUnwinds`) with the exception object,
the memory after the frame was left related to the world after the unwinder. -/
def IselSimU (sem : Sem) (XR : XRaise) (Γ : Rel) (env : Clif.XEnv) (p : Clif.Program)
    (f : Clif.Function) (vc : VCode) : Prop :=
  ∀ args cs w₀ (ρ₀ : Nat → CV), ClifEntry f args cs → Γ.holds f cs.frame.slots cs.mem w₀ →
    ArgsAtEntry Γ.F f.sig args w₀ → TrapsExplicitX env p cs → ∀ fuel,
    (∀ vals cm, Clif.runLoopX env p fuel cs.toX = .returned vals cm →
      ∃ us outs w, VReturns vc sem ρ₀ w₀ us outs w ∧
        RetPins vals us ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel Γ.F Γ.syms cm w) ∧
    (∀ c, Clif.runLoopX env p fuel cs.toX = .trapped c → VTraps vc sem ρ₀ w₀ c) ∧
    (∀ e cm, Clif.runLoopX env p fuel cs.toX = .unwound e cm →
      ∃ obj w, VUnwinds vc sem XR ρ₀ w₀ obj w ∧ ExnRel e obj ∧ MemRel Γ.F Γ.syms cm w)

/-- **`prepare` with unwinding**: `PrepareCorrect`, and the exceptional ends of `vc` are ends of
`vcp`. -/
def PrepareCorrectU (sem : Sem) (XR : XRaise) (vc vcp : VCode) : Prop :=
  PrepareCorrect sem vc vcp ∧
    ∀ ρ₀ w₀ obj w, VUnwinds vc sem XR ρ₀ w₀ obj w → VUnwinds vcp sem XR ρ₀ w₀ obj w

/-- The register-level conclusion for the exceptional ends: the Arm run returns to the caller
as the ABI requires, with the exception object in x0 and the world outside `F` the one after
the unwinder restored the raising call. -/
def RegLevelUnw (sem : Sem) (XR : XRaise) (F : BitVec 64 → Prop)
    (astep : Arm.ArmState → Arm.ArmState) (vcp : VCode) (ra : BitVec 64) (s : Arm.ArmState)
    (ρ₀ : Nat → CV) (w₀ : Arm.ArmState) : Prop :=
  ∀ obj w, VUnwinds vcp sem XR ρ₀ w₀ obj w →
    ∃ n, ArmRet ra s (runX astep n s) ∧ xreg 0 (runX astep n s) = obj ∧
      ∀ a, ¬ F a → (runX astep n s).mem a = w.mem a

/-- **VCode → Arm with unwinding**: `RegLevelCorrect` for the machine with unwinding `astep`,
plus the exceptional ends (`RegLevelUnw`). -/
def RegLevelCorrectU (sem : Arm.ArmState → Sem) (XR : XRaise) (F : Arm.ArmState → BitVec 64 → Prop)
    (K : Nat) (astep : Arm.ArmState → Arm.ArmState) (vcp : VCode) (af : AFunc) (fb : FnBin) : Prop :=
  ∀ base ra s, AbiEntry fb base ra s → StackAvail K af s → ∀ w₀, BodyEntry af s w₀ →
    ∀ ρ₀ : Nat → CV,
    (∀ us vals w, VReturns vcp (sem s) ρ₀ w₀ us vals w →
      ∃ n, ArmRet ra s (runX astep n s) ∧
        (∀ (j : Nat) v p x, us[j]? = some (v, p) → vals[j]? = some x → regVal (runX astep n s) p = x) ∧
        ∀ a, ¬ F s a → (runX astep n s).mem a = w.mem a) ∧
    (∀ c, VTraps vcp (sem s) ρ₀ w₀ c → ∃ n, TrapAt fb base c (runX astep n s)) ∧
    RegLevelUnw (sem s) XR (F s) astep vcp ra s ρ₀ w₀

/-- **`RegLevelCorrectU` for one initial vreg file of the theorem's choice** (as
`RegLevelCorrectEx`). -/
def RegLevelCorrectUEx (sem : Arm.ArmState → Sem) (XR : XRaise) (F : Arm.ArmState → BitVec 64 → Prop)
    (K : Nat) (astep : Arm.ArmState → Arm.ArmState) (vcp : VCode) (af : AFunc) (fb : FnBin) : Prop :=
  ∀ base ra s, AbiEntry fb base ra s → StackAvail K af s → ∀ w₀, BodyEntry af s w₀ →
    ∃ ρ₀ : Nat → CV,
    (∀ us vals w, VReturns vcp (sem s) ρ₀ w₀ us vals w →
      ∃ n, ArmRet ra s (runX astep n s) ∧
        (∀ (j : Nat) v p x, us[j]? = some (v, p) → vals[j]? = some x → regVal (runX astep n s) p = x) ∧
        ∀ a, ¬ F s a → (runX astep n s).mem a = w.mem a) ∧
    (∀ c, VTraps vcp (sem s) ρ₀ w₀ c → ∃ n, TrapAt fb base c (runX astep n s)) ∧
    RegLevelUnw (sem s) XR (F s) astep vcp ra s ρ₀ w₀

theorem RegLevelCorrectU.ex {sem : Arm.ArmState → Sem} {XR : XRaise}
    {F : Arm.ArmState → BitVec 64 → Prop} {K : Nat} {astep : Arm.ArmState → Arm.ArmState}
    {vcp : VCode} {af : AFunc} {fb : FnBin} (h : RegLevelCorrectU sem XR F K astep vcp af fb) :
    RegLevelCorrectUEx sem XR F K astep vcp af fb :=
  fun base ra s he hs w₀ hb => ⟨fun _ => 0, h base ra s he hs w₀ hb _⟩

/-- Without exceptional ends the unwinding part holds vacuously: `RegLevelCorrectEx` gives
`RegLevelCorrectUEx` when no VCode run ends by an exception. -/
theorem RegLevelCorrectUEx.of_ex {sem : Arm.ArmState → Sem} {XR : XRaise}
    {F : Arm.ArmState → BitVec 64 → Prop} {K : Nat} {astep : Arm.ArmState → Arm.ArmState}
    {vcp : VCode} {af : AFunc} {fb : FnBin} (h : RegLevelCorrectEx sem F K astep vcp af fb)
    (hn : ∀ s ρ₀ w₀ obj w, ¬ VUnwinds vcp (sem s) XR ρ₀ w₀ obj w) :
    RegLevelCorrectUEx sem XR F K astep vcp af fb := by
  intro base ra s he hs w₀ hb
  obtain ⟨ρ₀, h1, h2⟩ := h base ra s he hs w₀ hb
  exact ⟨ρ₀, h1, h2, fun obj w hu => absurd hu (hn s ρ₀ w₀ obj w)⟩

/-! ## The conclusion -/

/-- **What the Arm run does for an outcome of the CLIF run with unwinding** (`stuck`/
`outOfFuel`: no claim). -/
def ArmRefinesU (fb : FnBin) (base ra : BitVec 64) (astep : Arm.ArmState → Arm.ArmState)
    (s : Arm.ArmState) : Clif.XOutcome → Prop
  | .returned vals cm => ∃ n, ArmRet ra s (runX astep n s) ∧
      (∀ (j : Nat) v, vals[j]? = some v → XHolds v (xreg j (runX astep n s))) ∧
      MemAgree cm (runX astep n s)
  | .trapped c => ∃ n, TrapAt fb base c (runX astep n s)
  | .unwound e cm => ∃ n, ArmRet ra s (runX astep n s) ∧ ExnRel e (xreg 0 (runX astep n s)) ∧
      MemAgree cm (runX astep n s)
  | .stuck _ | .outOfFuel => True

/-- **The normal-return theorem is the restriction**: `ArmRefinesU` of the run with unwinding
gives `ArmRefines` of `Clif.run`'s run (the externs' unwinding read as `stuck`). -/
theorem armRefines_of_armRefinesU {fb : FnBin} {base ra : BitVec 64}
    {astep : Arm.ArmState → Arm.ArmState} {s : Arm.ArmState} {env : Clif.XEnv} {p : Clif.Program}
    {fuel : Nat} {cs : Clif.State}
    (h : ArmRefinesU fb base ra astep s (Clif.runLoopX env p fuel cs.toX)) :
    ArmRefines fb base ra astep s (Clif.runLoop env.toEnv p fuel cs) := by
  cases hr : Clif.runLoop env.toEnv p fuel cs with
  | returned vals cm =>
    have := Clif.runLoopX_of_returned (env := env) fuel cs.toX hr
    rw [this] at h
    exact h
  | trapped c =>
    have := Clif.runLoopX_of_trapped (env := env) fuel cs.toX hr
    rw [this] at h
    exact h
  | stuck _ => trivial
  | outOfFuel => trivial

/-! ## Composition -/

/-- **Composition with unwinding**, with the register-level theorem's choice of the initial vreg
file. -/
theorem backend_correct_of_layersU_ex {p : Clif.Program} {f : Clif.Function} {vc vcp : VCode}
    {af : AFunc} {fb : FnBin} {sem : Arm.ArmState → Sem} {XR : XRaise}
    {F : Arm.ArmState → BitVec 64 → Prop} {syms : String → Option Nat} {slotOff out K : Nat}
    {astep : Arm.ArmState → Arm.ArmState} {env : Clif.XEnv}
    (hIsel : ∀ s, IselSimU (sem s) XR ⟨F s, syms, slotOff, out⟩ env p f vc)
    (hPrep : ∀ s, PrepareCorrectU (sem s) XR vc vcp)
    (hReg : RegLevelCorrectUEx sem XR F K astep vcp af fb)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsAtEntry (F s) f.sig args w₀)
    (hcs : ClifEntry f args cs) (hrel : Rel.holds ⟨F s, syms, slotOff, out⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicitX env p cs) (fuel : Nat) :
    ArmRefinesU fb base ra astep s (Clif.runLoopX env p fuel cs.toX) := by
  obtain ⟨ρ₀, hR1, hR2, hR3⟩ := hReg base ra s hent hres w₀ hbe
  have hI := hIsel s args cs w₀ ρ₀ hcs hrel hargs htr fuel
  cases hrun : Clif.runLoopX env p fuel cs.toX with
  | returned vals cm =>
    obtain ⟨us, outs, w, hv, hus, hlen, hhold, hmem⟩ := hI.1 vals cm hrun
    obtain ⟨n, hret, hregs, hmemF⟩ := hR1 us outs w (((hPrep s).1 _ _).1 _ _ _ hv)
    refine ⟨n, hret, ?_, memAgree_of hmem hmemF⟩
    intro j v hj
    have hjv : j < vals.length := (List.getElem?_eq_some_iff.mp hj).1
    have hju : j < us.length := by have := hhold.1; omega
    obtain ⟨x, hx⟩ : ∃ x, outs[j]? = some x :=
      ⟨outs[j]'(by have := hhold.1; omega), List.getElem?_eq_getElem _⟩
    have hp : (us[j]'hju).2 = Reg.x j := hus.x hjv hju
    have hr := hregs j (us[j]'hju).1 (us[j]'hju).2 x (by simp [List.getElem?_eq_getElem hju]) hx
    rw [hp, regVal_x] at hr
    show VHolds v (ofX (xreg j (runX astep n s)))
    rw [hr]
    exact hhold.2 j v x hj hx
  | trapped c =>
    exact hR2 c (((hPrep s).1 _ _).2 c (hI.2.1 c hrun))
  | unwound e cm =>
    obtain ⟨obj, w, hv, hex, hmem⟩ := hI.2.2 e cm hrun
    obtain ⟨n, hret, hx0, hmemF⟩ := hR3 obj w ((hPrep s).2 _ _ _ _ hv)
    exact ⟨n, hret, by rw [hx0]; exact hex, memAgree_of hmem hmemF⟩
  | stuck _ => trivial
  | outOfFuel => trivial

/-- **Composition with unwinding.** -/
theorem backend_correct_of_layersU {p : Clif.Program} {f : Clif.Function} {vc vcp : VCode}
    {af : AFunc} {fb : FnBin} {sem : Arm.ArmState → Sem} {XR : XRaise}
    {F : Arm.ArmState → BitVec 64 → Prop} {syms : String → Option Nat} {slotOff out K : Nat}
    {astep : Arm.ArmState → Arm.ArmState} {env : Clif.XEnv}
    (hIsel : ∀ s, IselSimU (sem s) XR ⟨F s, syms, slotOff, out⟩ env p f vc)
    (hPrep : ∀ s, PrepareCorrectU (sem s) XR vc vcp)
    (hReg : RegLevelCorrectU sem XR F K astep vcp af fb)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsAtEntry (F s) f.sig args w₀)
    (hcs : ClifEntry f args cs) (hrel : Rel.holds ⟨F s, syms, slotOff, out⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicitX env p cs) (fuel : Nat) :
    ArmRefinesU fb base ra astep s (Clif.runLoopX env p fuel cs.toX) :=
  backend_correct_of_layersU_ex hIsel hPrep hReg.ex hent hres hbe hargs hcs hrel htr fuel

end E2E
