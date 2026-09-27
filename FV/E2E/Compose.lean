import FV.E2E.Statement

/-!
# M7: composing the layers

`backend_correct_of_layers`: CLIF → VCode (`IselSim`), VCode → prepared VCode
(`PrepareCorrect`) and prepared VCode → Arm (`RegLevelCorrect`) give the end-to-end refinement
`Refines` of every CLIF outcome by the Arm run.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

theorem regVal_x (s : Arm.ArmState) (n : Nat) : regVal s (.x n) = ofX (xreg n s) := rfl

theorem memAgree_of {F : BitVec 64 → Prop} {syms} {cm : Clif.Mem} {w s : Arm.ArmState}
    (hm : MemRel F syms cm w) (he : ∀ a, ¬ F a → s.mem a = w.mem a) : MemAgree cm s := by
  intro a b hv hb
  have hw := hm.bytes a b hb
  have hF := (hm.valid a 1 hv).2 0 (by omega)
  simp only [Nat.add_zero] at hF
  rw [← hw]
  simp only [Arm.read_mem, Arm.read_store]
  rw [he _ hF]

/-- **Composition.** -/
theorem backend_correct_of_layers {p : Clif.Program} {f : Clif.Function} {vc vcp : VCode}
    {af : AFunc} {fb : FnBin} {sem : Sem} {F : Arm.ArmState → BitVec 64 → Prop}
    {syms : String → Option Nat} {slotReg : Arm.ArmState → Nat}
    {astep : Arm.ArmState → Arm.ArmState} {env : Clif.Env}
    (hIsel : ∀ s, IselSim sem ⟨F s, syms, slotReg⟩ env p f vc)
    (hPrep : PrepareCorrect sem vc vcp)
    (hReg : RegLevelCorrect sem F astep vcp af fb)
    {base ra : BitVec 64} {s : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail af s) (hargs : ArgsIn args s)
    (hcs : ClifEntry f args cs) (hrel : Rel.holds ⟨F s, syms, slotReg⟩ f cs.frame.slots cs.mem s)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    Refines fb base ra astep s (Clif.runLoop env p fuel cs) := by
  have hI := hIsel s args cs s (fun _ => 0) hcs hrel hargs htr fuel
  have hR := hReg base ra s hent hres (fun _ => 0)
  cases hrun : Clif.runLoop env p fuel cs with
  | returned vals cm =>
    obtain ⟨us, outs, w, hv, hus, hlen, hhold, hmem⟩ := hI.1 vals cm hrun
    obtain ⟨n, hret, hregs, hmemF⟩ := hR.1 us outs w ((hPrep _ _).1 _ _ _ hv)
    refine ⟨n, hret, ?_, memAgree_of hmem hmemF⟩
    intro j v hj
    have hjv : j < vals.length := (List.getElem?_eq_some_iff.mp hj).1
    have hju : j < us.length := by have := hhold.1; omega
    obtain ⟨x, hx⟩ : ∃ x, outs[j]? = some x :=
      ⟨outs[j]'(by have := hhold.1; omega), List.getElem?_eq_getElem _⟩
    have hp : (us[j]'hju).2 = Reg.x j := by
      have := congrArg (fun l => l[j]?) hus
      simp only [List.getElem?_map, List.getElem?_range hju, List.getElem?_eq_getElem hju,
        Option.map_some] at this
      exact Option.some.inj this
    have hr := hregs j (us[j]'hju).1 (us[j]'hju).2 x (by simp [List.getElem?_eq_getElem hju]) hx
    rw [hp, regVal_x] at hr
    show VHolds v (ofX (xreg j (runX astep n s)))
    rw [hr]
    exact hhold.2 j v x hj hx
  | trapped c =>
    exact hR.2 c ((hPrep _ _).2 c (hI.2 c hrun))
  | stuck _ => trivial
  | outOfFuel => trivial

end E2E
