import FV.E2E.ExecBytes
import FV.E2E.LinkArmT
import FV.E2E.LinkCheckT

/-! # Typed copies of `FV.E2E.ExecBytes` (S11e5 Stage C, slice 8)

The declarations of `FV.E2E.ExecBytes` that depend on the integer link contract
(`LinkSys.Ok`, `LinkSys.Thm`, `okB`, `ArmRefines`), for the typed contract `LinkSys.OkT`
(suffix `T`; `LinkSys.Ok.*` as `LinkSys.OkT.*`), and the typed executable refinement
`ExecRefinesT` (each returned value in the ABI return register of its class, as in
`ArmRefinesT`) with its integer specialization `ExecRefinesT.toExecRefines`. -/

namespace E2E.ExecBytes
open Backend Backend.Proof E2E.LinkCheck E2E.Binary E2E.BinCheck
section Machine
variable (I : LinkInput) (B : BaseEnv) (file : ByteArray)
end Machine
section Lemmas
variable {I : LinkInput} {B : BaseEnv} {file : ByteArray}

theorem fnOkT {D : List Clif.DataObject} (hI : okBT I = true) (hbin : BinOk I D file)
    {F : BitVec 64 → Prop} (hL : (LinkSys.ofInput I B F).OkT) {g : Clif.Function}
    (hg : g ∈ (prog I).funcs) : FnOk I file g := by
  obtain ⟨-, -, -, -, hla, hb⟩ := (factsT hI hg).pipe
  exact ⟨hla, hL.fits g hg, hbin.code _ (tab_mem (okB_namesT hI) hg), hb⟩
end Lemmas
section Core
variable {I : LinkInput} {B : BaseEnv} {file : ByteArray}
end Core

/-- **What the executable machine does for a CLIF outcome, typed** (`ExecRefines` with the
return clause of `ArmRefinesT`): a return reaches the return address with each returned value
held by the ABI return register of its type's class (`retRegsT`: x0, x1, … for integers, v0,
v1, … for floats), the callee-saved state restored, and memory outside `R` agreeing; a trap
reaches a trap site with its code. -/
def ExecRefinesT (fb : FnBin) (base ra : BitVec 64) (astep : Arm.ArmState → Arm.ArmState)
    (s : Arm.ArmState) (R : BitVec 64 → Prop) : Clif.Outcome → Prop
  | .returned vals cm => ∃ n, ArmRet ra s (runX astep n s) ∧
      (∀ (j : Nat) v r, vals[j]? = some v →
        (retRegsT (vals.map fun v => tyClass v.ty) 0 0)[j]? = some r →
        VHolds v (regVal (runX astep n s) r)) ∧
      ∀ a b, cm.valid a 1 = true → cm.bytes a = some b → ¬ R (BitVec.ofNat 64 a) →
        Arm.read_mem (BitVec.ofNat 64 a) (runX astep n s) = b
  | .trapped c => ∃ n, TrapAt fb base c (runX astep n s)
  | .stuck _ | .outOfFuel => True

/-- **Integer specialization**: when the returned values are integers, `ExecRefinesT` is
`ExecRefines` (the return registers are x0, x1, …). -/
theorem ExecRefinesT.toExecRefines {fb : FnBin} {base ra : BitVec 64}
    {astep : Arm.ArmState → Arm.ArmState} {s : Arm.ArmState} {R : BitVec 64 → Prop}
    {o : Clif.Outcome} (h : ExecRefinesT fb base ra astep s R o)
    (hint : ∀ vals cm, o = .returned vals cm → ∀ v ∈ vals, v.ty.isInt = true) :
    ExecRefines fb base ra astep s R o := by
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

section Transfer
variable {I : LinkInput} {B : BaseEnv} {file : ByteArray}
end Transfer
end E2E.ExecBytes
