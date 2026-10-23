import FV.Concurrency.CallResumeLayers
import FV.Concurrency.CallLoadResume

/-!
# Witness: the caller's layer 4 after a call's return (#473, (2c))

On the compiled caller of `atomic_load` (`CallSeg.WitnessC.RC`) at its `bl` (`sBF`, with `Q` at
the `call` item, `prefixF`), returning without any effect but the return address (`yR`: the pc
after the `bl`; a callee that preserves everything): the premises of
`CallResumeL.mstep_call` and `CallSeg.resumeQW` hold, so **`resume_RC`**: the allocated code's
`call` steps under the external semantics returning the result registers' values, to a store
related by `Q` to `yR` after the call.

Checks by `native_decide` (witness only).
-/

namespace Concurrency.CallResumeL.Witness

open Arm ArmThread Backend Backend.Proof VCodeThread PrepThread AllocThread ArmAllocThread E2E
  IselResume CallSeg CallSeg.WitnessC

/-- **The state after a return without effect**: the pc after the `bl`. -/
noncomputable def yR : ArmState := Arm.w .PC (Arm.r .PC sBF + 4#64) sBF

theorem regVal_w_pc (v : BitVec 64) (s : ArmState) (r : Reg) :
    regVal (Arm.w .PC v s) r = regVal s r := by
  cases r <;> simp [regVal, r_of_w_different]

theorem locVal_w_pc (fr : RAFrame) (v : BitVec 64) (s : ArmState) (l : Loc) :
    locVal fr (Arm.w .PC v s) l = locVal fr s l := by
  cases l with
  | reg r => exact regVal_w_pc v s r
  | _ =>
    simp only [locVal, spOf, r_of_w_different (show StateField.GPR 31#5 ≠ .PC by simp)]
    have hm : ∀ n a, Arm.read_mem_bytes n a (Arm.w .PC v s) = Arm.read_mem_bytes n a s :=
      fun n a => read_mem_bytes_congr _ _ fun _ _ => by rw [ArmFoot.w_mem]
    simp only [hm]

/-- The caller's call instruction. -/
def infoC1 : CallInfo := match (vcpC.blocks[0]!).insts[1]? with
  | some (MInst.call i) => i
  | _ => default

/-- Its operands. -/
def opsC1 : Array Operand := match (MInst.call infoC1).operands with
  | .ok o => o
  | .error _ => #[]

theorem callChecksC : (vcpC.blocks[0]!).insts[1]? = some (.call infoC1) ∧
    (MInst.call infoC1).operands = .ok opsC1 ∧
    (#[Loc.reg (.x 0), .reg (.x 0)] : Array Loc).size = opsC1.size := by
  native_decide

/-- **The caller's layer 4 after the call's return** (module doc). -/
theorem resume_RC : ∃ (m m' : Loc → CV) (its : List RItem),
    Q RC sBF (.run ⟨0, .op 1 #[.reg (.x 0), .reg (.x 0)] :: its, m, w₀C⟩) ∧
    MStep RC.vc (csem RC.F RC.ctx (xcallX VCodeThread.Witness.X0
        ((((opsC1.zip #[.reg (.x 0), .reg (.x 0)]).toList.filter (·.1.isDef))).map
          fun p => locVal RC.fr yR p.2) yR))
      ckeep RC.rf (.run ⟨0, .op 1 #[.reg (.x 0), .reg (.x 0)] :: its, m, w₀C⟩)
      (.run ⟨0, its, m', yR⟩) ∧
    Q RC yR (.run ⟨0, its, m', yR⟩) := by
  obtain ⟨m, -, hq, -⟩ := prefixF
  rw [checksPost.2.1] at hq
  obtain ⟨hi, hops, hsz⟩ := callChecksC
  have hk : 1 + 1 < (vcpC.blocks[0]!).insts.size := by rw [← checksPost.2.2.2.2]; decide
  have hpres : ∀ l, ValidLoc l → Live RC.rf l →
      (∀ c ∈ (MInst.call infoC1).clobbers, l ≠ .reg c) → locVal RC.fr yR l = locVal RC.fr sBF l :=
    fun l _ _ _ => locVal_w_pc _ _ _ l
  have hkeep : ∀ c ∈ (MInst.call infoC1).clobbers, c ∈ calleeSaved →
      ckeep c (regVal yR c) = ckeep c (regVal sBF c) :=
    fun c _ _ => by unfold yR; rw [regVal_w_pc]
  obtain ⟨m', hms, hst'⟩ := mstep_call hq vb0C hi hk hops hsz hpres hkeep
    VCodeThread.Witness.X0 yR
  refine ⟨m, m', _, hq, hms, resumeQW wfRC hq vb0C hi (by simp [yR]) ?_ ?_ ?_ ?_ hst'
    (SameWorld.refl _ _)⟩
  · unfold yR; rw [r_of_w_different (by simp)]
    exact (q_stRel hq).err
  · simp only [yR, spOf, r_of_w_different (show StateField.GPR 31#5 ≠ .PC by simp)]
  · intro a _; unfold yR; rw [ArmFoot.w_mem]
  · exact w_program

end Concurrency.CallResumeL.Witness
