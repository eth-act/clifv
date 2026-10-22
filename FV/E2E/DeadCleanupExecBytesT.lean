import FV.E2E.DeadCleanupExecBytes
import FV.E2E.BinaryT
import FV.E2E.ExecBytesT
import FV.E2E.DeadCleanupBinaryT
import FV.E2E.BinCheckT
import FV.E2E.DeadCleanupLinkCheckT
import FV.E2E.DeadCleanupStackBoundT
import FV.E2E.LinkArmT
import FV.E2E.LinkCheckT
import FV.E2E.PipelineCheckT
import FV.E2E.StackBoundT

/-! # Typed copies of `FV.E2E.DeadCleanupExecBytes` (S11e5 Stage C, slice 8)

The declarations of `FV.E2E.DeadCleanupExecBytes` that depend on the integer link contract
(`LinkSys.Ok`, `LinkSys.Thm`, `okB`, `ArmRefinesT`), for the typed contract `LinkSys.OkT`
(suffix `T`; `LinkSys.Ok.*` as `LinkSys.OkT.*`). -/

namespace E2E.DeadCleanupExecBytes
set_option autoImplicit false
open Backend Backend.Proof E2E.LinkCheck E2E.DeadCleanupBinary E2E.BinCheck
section Machine
variable (I : LinkInput) (B : BaseEnv) (file : ByteArray)
end Machine
section Lemmas
variable {I : LinkInput} {B : BaseEnv} {file : ByteArray}

theorem fnOkT {D : List Clif.DataObject} (hI : okBCleanup I = true) (hbin : E2E.DeadCleanupBinCheck.BinOk I D file)
    {F : BitVec 64 → Prop} (hL : (LinkSys.ofInputCleanup I B F).OkT) {g : Clif.Function}
    (hg : g ∈ (prog I).funcs) : FnOk I file g := by
  obtain ⟨-, -, -, -, hla, hb⟩ := (factsCleanup hI hg).pipe
  exact ⟨hla, hL.fits g hg, hbin.code _ (tab_mem (okBCleanup_names hI) hg), hb⟩
end Lemmas
section Core
variable {I : LinkInput} {B : BaseEnv} {file : ByteArray}
end Core
section Transfer
variable {I : LinkInput} {B : BaseEnv} {file : ByteArray}
end Transfer
end E2E.DeadCleanupExecBytes
