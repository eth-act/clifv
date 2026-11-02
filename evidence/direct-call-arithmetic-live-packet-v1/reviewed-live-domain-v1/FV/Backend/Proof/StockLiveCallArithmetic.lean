import FV.Backend.Proof.StockDirectCallResult
import FV.Backend.Proof.IselFamily
import FV.Backend.Proof.IselCmpIcmp

namespace Backend.Stock.Proof.LiveCallArithmetic
open Backend Backend.Proof Backend.Proof.Driver E2E
set_option autoImplicit false
set_option Elab.async false

/-- A call writes its result and preserves every distinct live virtual value. -/
theorem virtual_live (pairs : List (Nat × Reg)) (destination live : Nat)
    (separate : live ≠ destination) (output : CV) (values : Nat → CV) :
    vdefUpd (retOps pairs ++ callDefOps [(.x 0,destination)]).toArray [output] values live =
      values live := by
  rw [DirectCallResult.virtual_result]
  simp only [separate,↓reduceIte]

/-- The source continuation preserves the live parameter and the actual arbitrary callee memory. -/
theorem source_live {s next : Clif.State} {rest : List Clif.Stmt} {source live : Nat}
    {value : Clif.Val} {after : Clif.Mem}
    (continued : Clif.continueWith s rest [source] [value] after = .next next)
    (separate : live ≠ source) :
    next.frame.regs live = s.frame.regs live ∧ next.mem = after := by
  have bound := DirectCallResult.source_result continued
  exact ⟨bound.2.2.2 live separate,bound.2.1⟩

/-- Existing call semantics and the existing ALU theorem compose without a new ALU proof. -/
theorem call_then_add {F : BitVec 64 → Prop} {isem : Sem} (refines : Refines F isem)
    {name : String} {pairs : List (Nat × Reg)} {destination live sum : Nat}
    (separate : live ≠ destination) {values : Nat → CV} {output : CV}
    {before after : Arm.ArmState}
    (called : isem (.call ⟨.sym name,retPairs pairs,callDefs [(.x 0,destination)]⟩)
      (pairs.map (values ·.1)) before = some ([output],after,.next)) :
    ∃ world,seqRun isem
      [.call ⟨.sym name,retPairs pairs,callDefs [(.x 0,destination)]⟩,
       .aluRRR .add .size64 (.vreg sum .int) (.vreg destination .int) (.vreg live .int)]
      values before = some (.fall
        (upd (fun key => if key = destination then output else values key) sum
          (resX .size64 (opnd .size64 output + opnd .size64 (values live)))) world) ∧
      SameWorld F world after := by
  have callRun := seqRun_call_sym called (show [output].length = [(.x 0,destination)].length from rfl)
  have update := DirectCallResult.virtual_result pairs destination output values
  rw [vdefUpd_call] at update
  rw [update] at callRun
  obtain ⟨world,addRun,same⟩ := seqRun_aluRRR refines (op := .add) (sz := .size64)
    (d := sum) (x := destination) (y := live)
    (ρ := fun key => if key = destination then output else values key) (w := after)
    (r := opnd .size64 output + opnd .size64 (values live))
    (by simp only [ite_true,separate,↓reduceIte,aluVal])
  exact ⟨world,seqRun_append_fall' isem callRun addRun,same⟩

/-- The post-call addition uses the exact returned word and the preserved original parameter. -/
theorem sum_holds {returned live : BitVec 64} {output saved : CV}
    (returnedHeld : VHolds ⟨.i64,returned⟩ output) (liveHeld : VHolds ⟨.i64,live⟩ saved) :
    VHolds ⟨.i64,returned+live⟩ (resX .size64 (opnd .size64 output + opnd .size64 saved)) := by
  rw [opnd64_vholds returnedHeld,opnd64_vholds liveHeld]
  simp [VHolds,Clif.Ty.width,resX,ofX] <;> rfl

end Backend.Stock.Proof.LiveCallArithmetic
