import FV.E2E.Statement
import FV.Backend.Proof.LowerSimT

/-!
# Typed layer composition (S11e5 Stage C, slice 7)

The end-to-end refinement for functions with `f32`/`f64` values: a returned value is in the ABI
return register of its type's class (`retRegsT`: x0.. for integers, v0.. for floats, separate
counters), not necessarily in an X register (`ArmRefines`' `XHolds v (xreg j _)`).

* `IselSimT`: `IselSim` whose returns put the values in their classes' return registers
  (`RetRegsOk`, from `driver_correctT`).
* `ArmRefinesT`: `ArmRefines` with each returned value held (`VHolds`) by its return register.
* `backend_correct_of_layers_exT`, `backend_correct_of_layersT`: the composition with the
  unchanged `PrepareCorrect` and `RegLevelCorrect[Ex]` (class-generic: the `rets` pairs' physical
  registers hold the returned values).

Integer specialization: `ArmRefinesT.toArmRefines` (returned integers: `ArmRefines`).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- **CLIF → VCode, typed** (`IselSim` with class-aware return registers, `RetRegsOk`). -/
def IselSimT (sem : Sem) (Γ : Rel) (env : Clif.Env) (p : Clif.Program) (f : Clif.Function)
    (vc : VCode) : Prop :=
  ∀ args cs w₀ (ρ₀ : Nat → CV), ClifEntry f args cs → Γ.holds f cs.frame.slots cs.mem w₀ →
    ArgsAtEntry Γ.F f.sig args w₀ → TrapsExplicit env p cs → ∀ fuel,
    (∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ us outs w, VReturns vc sem ρ₀ w₀ us outs w ∧
        RetRegsOk vals us ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel Γ.F Γ.syms cm w ∧
        vals.map (·.ty) = Clif.AbiParam.tys f.sig.returns) ∧
    (∀ c, Clif.runLoop env p fuel cs = .trapped c → VTraps vc sem ρ₀ w₀ c)

/-- **What the Arm run does for a CLIF outcome, typed**: a return reaches the return address
with each returned value held (low bits, `VHolds`) by the ABI return register of its type's
class (`retRegsT`), the callee-saved state restored and memory agreeing; a trap reaches a trap
site with its code. -/
def ArmRefinesT (fb : FnBin) (base ra : BitVec 64) (astep : Arm.ArmState → Arm.ArmState)
    (s : Arm.ArmState) : Clif.Outcome → Prop
  | .returned vals cm => ∃ n, ArmRet ra s (runX astep n s) ∧
      (∀ (j : Nat) v r, vals[j]? = some v →
        (retRegsT (vals.map fun v => tyClass v.ty) 0 0)[j]? = some r →
        VHolds v (regVal (runX astep n s) r)) ∧
      MemAgree cm (runX astep n s)
  | .trapped c => ∃ n, TrapAt fb base c (runX astep n s)
  | .stuck _ | .outOfFuel => True

/-- `memAgree_of` (`Compose.lean`), here to keep this module off `Compose`. -/
theorem memAgree_ofT {F : BitVec 64 → Prop} {syms} {cm : Clif.Mem} {w s : Arm.ArmState}
    (hm : MemRel F syms cm w) (he : ∀ a, ¬ F a → s.mem a = w.mem a) : MemAgree cm s := by
  intro a b hv hb
  have hw := hm.bytes a b hv hb
  have hF := (hm.valid a 1 hv).2 0 (by omega)
  simp only [Nat.add_zero] at hF
  rw [← hw]
  simp only [Arm.read_mem, Arm.read_store]
  rw [he _ hF]

/-- The `j`-th register of `RetRegsOk`'s pairs is the `j`-th return register of the values'
classes. -/
theorem retRegsOk_get {vals : List Clif.Val} {us : List (Reg × Reg)} (h : RetRegsOk vals us)
    {j : Nat} {r : Reg} (hr : (retRegsT (vals.map fun v => tyClass v.ty) 0 0)[j]? = some r) :
    ∃ u, us[j]? = some u ∧ u.2 = r := by
  obtain ⟨cs, hcs⟩ := h
  have hj : (us.map (·.2))[j]? = some r := by
    rw [hcs, List.take_left' (l₁ := vals.map fun v => tyClass v.ty) (i := vals.length)
        (by rw [List.length_map]),
      List.getElem?_append_left (List.getElem?_eq_some_iff.mp hr).1, hr]
  rw [List.getElem?_map] at hj
  obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.mp hj
  exact ⟨u, hu, rfl⟩

/-- **Composition, typed**, with the register-level theorem's choice of the initial vreg file
(`RegLevelCorrectEx`). -/
theorem backend_correct_of_layers_exT {p : Clif.Program} {f : Clif.Function} {vc vcp : VCode}
    {af : AFunc} {fb : FnBin} {sem : Arm.ArmState → Sem} {F : Arm.ArmState → BitVec 64 → Prop}
    {syms : String → Option Nat} {slotOff out K : Nat}
    {astep : Arm.ArmState → Arm.ArmState} {env : Clif.Env}
    (hIsel : ∀ s, IselSimT (sem s) ⟨F s, syms, slotOff, out⟩ env p f vc)
    (hPrep : ∀ s, PrepareCorrect (sem s) vc vcp)
    (hReg : RegLevelCorrectEx sem F K astep vcp af fb)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsAtEntry (F s) f.sig args w₀)
    (hcs : ClifEntry f args cs) (hrel : Rel.holds ⟨F s, syms, slotOff, out⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ArmRefinesT fb base ra astep s (Clif.runLoop env p fuel cs) := by
  obtain ⟨ρ₀, hR⟩ := hReg base ra s hent hres w₀ hbe
  have hI := hIsel s args cs w₀ ρ₀ hcs hrel hargs htr fuel
  cases hrun : Clif.runLoop env p fuel cs with
  | returned vals cm =>
    obtain ⟨us, outs, w, hv, hus, hlen, hhold, hmem, -⟩ := hI.1 vals cm hrun
    obtain ⟨n, hret, hregs, hmemF⟩ := hR.1 us outs w ((hPrep s _ _).1 _ _ _ hv)
    refine ⟨n, hret, ?_, memAgree_ofT hmem hmemF⟩
    intro j v r hj hr
    obtain ⟨u, hu, hur⟩ := retRegsOk_get hus hr
    have hju : j < us.length := (List.getElem?_eq_some_iff.mp hu).1
    obtain ⟨x, hx⟩ : ∃ x, outs[j]? = some x :=
      ⟨outs[j]'(by omega), List.getElem?_eq_getElem _⟩
    have hrv := hregs j u.1 u.2 x (by rw [hu]) hx
    rw [hur] at hrv
    rw [hrv]
    exact hhold.2 j v x hj hx
  | trapped c =>
    exact hR.2 c ((hPrep s _ _).2 c (hI.2 c hrun))
  | stuck _ => trivial
  | outOfFuel => trivial

/-- **Composition, typed.** -/
theorem backend_correct_of_layersT {p : Clif.Program} {f : Clif.Function} {vc vcp : VCode}
    {af : AFunc} {fb : FnBin} {sem : Arm.ArmState → Sem} {F : Arm.ArmState → BitVec 64 → Prop}
    {syms : String → Option Nat} {slotOff out K : Nat}
    {astep : Arm.ArmState → Arm.ArmState} {env : Clif.Env}
    (hIsel : ∀ s, IselSimT (sem s) ⟨F s, syms, slotOff, out⟩ env p f vc)
    (hPrep : ∀ s, PrepareCorrect (sem s) vc vcp)
    (hReg : RegLevelCorrect sem F K astep vcp af fb)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsAtEntry (F s) f.sig args w₀)
    (hcs : ClifEntry f args cs) (hrel : Rel.holds ⟨F s, syms, slotOff, out⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ArmRefinesT fb base ra astep s (Clif.runLoop env p fuel cs) :=
  backend_correct_of_layers_exT hIsel hPrep hReg.ex hent hres hbe hargs hcs hrel htr fuel

/-- **Integer specialization**: when the returned values are integers, `ArmRefinesT` is
`ArmRefines` (the return registers are x0, x1, …). -/
theorem ArmRefinesT.toArmRefines {fb : FnBin} {base ra : BitVec 64}
    {astep : Arm.ArmState → Arm.ArmState} {s : Arm.ArmState} {o : Clif.Outcome}
    (h : ArmRefinesT fb base ra astep s o)
    (hint : ∀ vals cm, o = .returned vals cm → ∀ v ∈ vals, v.ty.isInt = true) :
    ArmRefines fb base ra astep s o := by
  cases o with
  | returned vals cm =>
    obtain ⟨n, hret, hv, hm⟩ := h
    refine ⟨n, hret, fun j v hj => ?_, hm⟩
    have hcl : vals.map (fun v => tyClass v.ty) = List.replicate vals.length .int := by
      rw [List.eq_replicate_iff]
      simp only [List.length_map, List.mem_map, true_and]
      rintro _ ⟨v', hv', rfl⟩
      have hi := hint vals cm rfl v' hv'
      simp only [tyClass, hi, ite_true]
    have hjl : j < vals.length := (List.getElem?_eq_some_iff.mp hj).1
    have hr : (retRegsT (vals.map fun v => tyClass v.ty) 0 0)[j]? = some (.x j) := by
      rw [hcl, retRegsT_int, List.getElem?_map, List.getElem?_range' hjl]; simp
    exact hv j v (.x j) hj hr
  | trapped c => exact h
  | stuck _ => trivial
  | outOfFuel => trivial

/-- The values of a typed CLIF → VCode simulation's returns have the function's return types:
for integer returns, the typed refinement is `ArmRefines`. -/
theorem backend_correct_of_layers_ex_ofT {p : Clif.Program} {f : Clif.Function} {vc vcp : VCode}
    {af : AFunc} {fb : FnBin} {sem : Arm.ArmState → Sem} {F : Arm.ArmState → BitVec 64 → Prop}
    {syms : String → Option Nat} {slotOff out K : Nat}
    {astep : Arm.ArmState → Arm.ArmState} {env : Clif.Env}
    (hint : f.sig.returns.all (·.ty.isInt) = true)
    (hIsel : ∀ s, IselSimT (sem s) ⟨F s, syms, slotOff, out⟩ env p f vc)
    (hPrep : ∀ s, PrepareCorrect (sem s) vc vcp)
    (hReg : RegLevelCorrectEx sem F K astep vcp af fb)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsAtEntry (F s) f.sig args w₀)
    (hcs : ClifEntry f args cs) (hrel : Rel.holds ⟨F s, syms, slotOff, out⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ArmRefines fb base ra astep s (Clif.runLoop env p fuel cs) := by
  refine (backend_correct_of_layers_exT hIsel hPrep hReg hent hres hbe hargs hcs hrel htr
    fuel).toArmRefines fun vals cm hrun v hv => ?_
  obtain ⟨-, -, -, -, -, -, -, -, htys⟩ :=
    (hIsel s args cs w₀ (fun _ => 0) hcs hrel hargs htr fuel).1 vals cm hrun
  have hm : v.ty ∈ Clif.AbiParam.tys f.sig.returns := htys ▸ List.mem_map_of_mem hv
  obtain ⟨q, hq, hqt⟩ := List.mem_map.mp hm
  rw [← hqt]
  exact List.all_eq_true.mp hint q hq

end E2E
