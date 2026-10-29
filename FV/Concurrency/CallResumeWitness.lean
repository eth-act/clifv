module

public import FV.Concurrency.CallResumeLayers
public import FV.Concurrency.CallLoadResume
public import FV.Concurrency.CallLayers
public import FV.Concurrency.IselCallWitness

@[expose] public section

/-!
# Witness: the caller's layer 4 after a call's return (#473, (2c))

On the compiled caller of `atomic_load` (`CallSeg.WitnessC.RC`) at its `bl` (`sBF`, with `Q` at
the `call` item, `prefixF`), returning without any effect but the return address (`yR`: the pc
after the `bl`; a callee that preserves everything): the premises of
`CallResumeL.mstep_call` and `CallSeg.resumeQW` hold, so **`resume_RC`**: the allocated code's
`call` steps under the external semantics returning the result registers' values, to a store
related by `Q` to `yR` after the call.

**`isel_alloc_fC`**: every premise of `CallLayers.isel_alloc_refinesC` but the relations and the
run holds for the caller's lowering, `prepare` and allocation (`vcC`, `vcpC`, `rfC`).

Checks by `native_decide` (witness only).
-/

namespace Concurrency.CallResumeL.Witness

open Arm ArmThread Backend Backend.Proof Backend.Proof.Driver VCodeThread PrepThread AllocThread
  ArmAllocThread E2E IselResume CallSeg CallSeg.WitnessC

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

theorem prepC : prepCheck vcC vcpC = true := by native_decide

/-- **Layers 2–4a of the caller from related configurations, pausing at its call** (module doc). -/
theorem isel_alloc_fC {Γ : E2E.Rel} {fctx : FnCtx} {c : BitVec 64} {env : Clif.Env}
    (henv : env.extern "ld" = none) (hc : c.toNat % 16 = 0) (hslot : fctx.slotBase = Γ.slotOff)
    (hsym : ∀ n b, Γ.syms n = some b → VCodeThread.Witness.X0.sym n 0 = BitVec.ofNat 64 b) :
    ∃ (ctx : Ctx) (R : Reg → Reg) (gn : Nat → Nat) (bl : List BLow)
      (A : Nat → Nat → List Clif.ValueId) (L : Nat → Prop) (ss' : Array (Array Nat)) (cc : CheckCtx)
      (ins : Array (Option AState)),
      ∀ (slots : List (Clif.SlotId × Nat)) (s : Clif.State) (vV vP : VState CV ArmState)
        (cM : MState CV ArmState) (r₀ : Reg → CV) (trM : List (List Ev)) (cE : MConf CV ArmState),
        Driver.Match fC ctx R gn bl A (RelW Γ fC c) slots s vV →
        PMatch vcC vcpC (csem Γ.F fctx VCodeThread.Witness.X0) (cEvs Γ.F fctx) L ss' (.run vV)
          (.run vP) →
        MatchRun cc ins ckeep r₀ cM vP →
        MTRun vcpC rfC (csem Γ.F fctx VCodeThread.Witness.X0) ckeep (cEvs Γ.F fctx) (.run cM) trM
          cE →
        ∃ m trS t ψ, m ≤ trM.length ∧ ClifCStepTerm.CRun env pCL (.run s) trS t ∧
          ThreadRefine.Refines Maps (fun _ => False) (ThreadRefine.StepPair (conv (trM.take m)))
            trS (conv (trM.take m)) ψ ∧
          ((((m = trM.length ∧ ∃ cM', MStep vcpC (csem Γ.F fctx VCodeThread.Witness.X0) ckeep rfC
              cE cM') ∨ IselThread.Stop env pCL t) ∧ ∀ v, t = .ret v → m = trM.length) ∨
            (m = trM.length ∧ ∃ s' vV' vP' cM', t = .run s' ∧ IselCall.AtCallS s' ∧
              cE = .run cM' ∧ Driver.Match fC ctx R gn bl A (RelW Γ fC c) slots s' vV' ∧
              PMatch vcC vcpC (csem Γ.F fctx VCodeThread.Witness.X0) (cEvs Γ.F fctx) L ss'
                (.run vV') (.run vP') ∧ MatchRun cc ins ckeep r₀ cM' vP')) := by
  obtain ⟨hlow, hthr, -, hnames, hind, hv, hnt, -, hout0, -, -⟩ := IselCall.Witness.checksFC
  have hext : ∀ e ∈ fC.externs, env.extern e.2.name = none := by
    intro e he
    have : e.2.name ∈ fC.externs.map (·.2.name) := List.mem_map_of_mem he
    rw [hnames, List.mem_singleton] at this
    rw [this]; exact henv
  obtain ⟨ctx, st0, R, gn, bl, A, H, hchk⟩ := driverHypT_of (Γ := Γ) (fctx := fctx)
    (X := VCodeThread.Witness.X0) (c := c) (env := env) (p := pCL) hlow hthr hext
    (List.isEmpty_iff.mp hind) hv hnt IselCall.Witness.cfgFC hout0 hslot hsym
  obtain ⟨L, ss, ss', H3, -, -⟩ := prepFacts_of_check prepC
  obtain ⟨cc, ins, hck⟩ := checked_of_checkAlloc allocC
  obtain ⟨a0, hat, -⟩ := hck.at
  exact ⟨ctx, R, gn, bl, A, L, ss', cc, ins, fun slots s vV vP cM r₀ trM cE hm2 hm3 hm4 hr =>
    CallLayers.isel_alloc_refinesC H hchk (memRelOk_relW Γ fC c)
      (IselRefines.Witness.relW_wf hc) VCodeThread.Witness.X0_tls (fun _ _ _ => rfl) H3 hat
      hm2 hm3 hm4 hr⟩

end Concurrency.CallResumeL.Witness
