import FV.E2E.Main
import FV.E2E.RegLevelDriverSem
import FV.Backend.Proof.IselLowerAll
import FV.Backend.Proof.IselExcl
import FV.Backend.Proof.IselCtl
import FV.Backend.Proof.IselCtlUnmatch
import FV.Backend.Proof.IselMemRoots

/-! # `backend_correct` with every M4 obligation discharged

`backend_correct_of_rules` instantiated with M4's proven rule theorems and with the VCode
semantics fixed to M6's concrete `csem` (per activation `s`: frame `F s`, function context
`ctx s`, external semantics `X s`), which discharges `DriverSem` (`driverSem_csem`) and reduces
`CallsRefine` to the external contract `XCallsOk` (`callsRefine_csem`). -/

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

end E2E
