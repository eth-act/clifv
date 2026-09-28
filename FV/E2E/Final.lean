import FV.E2E.Main
import FV.E2E.RegLevelDriverSem
import FV.E2E.RegLevelCorrect
import FV.Backend.Proof.IselLowerAll
import FV.Backend.Proof.IselExcl
import FV.Backend.Proof.IselCtl
import FV.Backend.Proof.IselCtlUnmatch
import FV.Backend.Proof.IselMemRoots
import FV.Backend.Proof.MemRefines
import FV.Backend.Proof.RefinesCSem

/-! # `backend_correct` with every M4 obligation discharged

`backend_correct_of_rules` instantiated with M4's proven rule theorems and with the VCode
semantics fixed to M6's concrete `csem` (per activation `s`: frame `F s`, function context
`ctx s`, external semantics `X s`), which discharges `DriverSem` (`driverSem_csem`) and reduces
`CallsRefine` to the external contract `XCallsOk` (`callsRefine_csem`).

`backend_correct_final`: additionally the register-level layer (`RegLevelCorrect`, hypothesis
`hM6` of `backend_correct_m4`) is discharged by `regLevelCorrect_backend` for the backend's
concrete choices: frame addresses `frameF` of the allocated frame, function context
`⟨fa.k, af.slotBase⟩`, one external semantics `X` and the machine `ArmStepX X H fa`. -/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

theorem backend_correct_m4 {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : Compiled f k vc vcp rf af fa fb)
    {F : Arm.ArmState → BitVec 64 → Prop} {ctx : Arm.ArmState → FnCtx}
    {X : Arm.ArmState → ExtSem}
    {syms : String → Option Nat} {slotOff : Nat} {astep : Arm.ArmState → Arm.ArmState}
    {env : Clif.Env}
    -- M6 + M5
    (hM6 : RegLevelCorrect (fun s => csem (F s) (ctx s) (X s)) F astep vcp af fb)
    (hRef : ∀ s, Refines (F s) (csem (F s) (ctx s) (X s)))
    -- the external contract (callees, linker)
    (hX : ∀ s, XCallsOk env (fun sl cm w => Rel.holds ⟨F s, syms, slotOff⟩ f sl cm w) (X s))
    (hmem : ∀ s, MemRefines (F s) slotOff syms (csem (F s) (ctx s) (X s)))
    -- the run
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn args s) (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨F s, syms, slotOff⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ArmRefines fb base ra astep s (Clif.runLoop env p fuel cs) :=
  backend_correct_of_rules hsub hc
    lowerRulesCorrect_program excludedUnmatchable callRulesCorrect memRulesCorrect_program
    lowerTermRulesCorrect termUnmatchable branchRulesCorrect branchExcludedUnmatchable
    hM6 hRef (fun s' => driverSem_csem (F s') (ctx s') (X s'))
    (fun s' => callsRefine_csem (hX s')) hmem
    hent hres hbe hargs hcs hrel htr fuel

/-- `hRef` of `backend_correct_m4` at the backend's concrete choices (`refines_csem`). -/
theorem refines_final (vcp : VCode) (rf : RFunc) (af : AFunc) (fa : FnAsm) (X : ExtSem) :
    ∀ s, Refines (frameF (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s)
      (csem (frameF (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s)
        ⟨fa.k, af.slotBase⟩ X) :=
  fun _ => refines_csem _ _ X

/-- **The backend's end-to-end theorem** (`docs/contracts/e2e.md`, "Final hypotheses"): the Arm
run of the compiled function refines the CLIF run. M6's `csem` obligations are discharged
(`refines_csem`, `memRefines_csem`). Remaining hypotheses: the form coverage `FormsCovered`
(decided per function by `formsCoveredB`), the callee contract `CalleeOk` of the machine's call
hook, the external contract `XCallsOk`, and the link-time facts `hsym`/`hslot`. -/
theorem backend_correct_final {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : Compiled f k vc vcp rf af fa fb)
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    -- the straight-line forms of the prepared VCode are covered (decided by `formsCoveredB`)
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    -- the callee contract of the machine's call hook (AAPCS64)
    (hC : ∀ s, CalleeOk
      (frameF (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H)
    -- the external contract (callees, linker)
    (hX : ∀ s, XCallsOk env (fun sl cm w =>
      Rel.holds ⟨frameF (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff⟩ f sl cm w) X)
    -- memory forms (`memRefines_csem`): the external semantics' symbol addresses are the linked
    -- ones, and the relation's slot-region offset is the frame's slot base
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    -- the run
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn args s) (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨frameF (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ArmRefines fb base ra (ArmStepX X H fa) s (Clif.runLoop env p fuel cs) :=
  backend_correct_m4 (ctx := fun _ => ⟨fa.k, af.slotBase⟩) (X := fun _ => X) hsub hc
    (regLevelCorrect_backend hc.check hc.alloc hc.emit hc.layout hcov hC)
    (refines_final vcp rf af fa X) hX
    (fun _ => memRefines_csem _ _ X hslot hsym)
    hent hres hbe hargs hcs hrel htr fuel

end E2E
