import FV.E2E.DeadCleanupExecBytes
import FV.E2E.ExecBytesT
import FV.E2E.DeadCleanupLinkCheckT
import FV.E2E.LinkArmT
import FV.E2E.LinkCheckT
import FV.E2E.PipelineCheckT

/-! # Typed copies of `FV.E2E.DeadCleanupExecBytes` (S11e5 Stage C, slice 8)

The declarations of `FV.E2E.DeadCleanupExecBytes` that depend on the integer link contract
(`LinkSys.Ok`, `LinkSys.Thm`, `okB`, `ArmRefines`), for the typed contract `LinkSys.OkT`
(suffix `T`; `LinkSys.Ok.*` as `LinkSys.OkT.*`). -/

namespace E2E.DeadCleanupExecBytes
set_option autoImplicit false
open Backend Backend.Proof E2E.LinkCheck E2E.DeadCleanupBinary E2E.BinCheck
section Machine
variable (I : LinkInput) (B : BaseEnv) (file : ByteArray)
end Machine
section Lemmas
variable {I : LinkInput} {B : BaseEnv} {file : ByteArray}

theorem fnOkT {D : List Clif.DataObject} (hI : okBCleanupT I = true) (hbin : E2E.DeadCleanupBinCheck.BinOk I D file)
    {F : BitVec 64 → Prop} (hL : (LinkSys.ofInputCleanup I B F).OkT) {g : Clif.Function}
    (hg : g ∈ (prog I).funcs) : FnOk I file g := by
  obtain ⟨-, -, -, -, hla, hb⟩ := (factsCleanupT hI hg).pipe
  exact ⟨hla, hL.fits g hg, hbin.code _ (tab_mem (okBCleanup_namesT hI) hg), hb⟩
end Lemmas
section Core
variable {I : LinkInput} {B : BaseEnv} {file : ByteArray}
end Core
/-- `ExecRefinesT` (`FV/E2E/ExecBytesT.lean`) for the dead-cleanup chain (whose integer
`ExecRefines` is a copy of `ExecBytes.ExecRefines`). -/
abbrev ExecRefinesT := E2E.ExecBytes.ExecRefinesT

/-- **Integer specialization**: when the returned values are integers, `ExecRefinesT` is the
dead-cleanup chain's `ExecRefines`. -/
theorem ExecRefinesT.toExecRefines {fb : FnBin} {base ra : BitVec 64}
    {astep : Arm.ArmState → Arm.ArmState} {s : Arm.ArmState} {R : BitVec 64 → Prop}
    {o : Clif.Outcome} (h : ExecRefinesT fb base ra astep s R o)
    (hint : ∀ vals cm, o = .returned vals cm → ∀ v ∈ vals, v.ty.isInt = true) :
    ExecRefines fb base ra astep s R o := by
  have h' := E2E.ExecBytes.ExecRefinesT.toExecRefines h hint
  cases o <;> exact h'

section Transfer
variable {I : LinkInput} {B : BaseEnv} {file : ByteArray}
end Transfer
end E2E.DeadCleanupExecBytes
