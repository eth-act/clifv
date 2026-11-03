import FV.E2E.StockVoidCallDomain
import FV.E2E.PreparedReturnPinCallerBoundaryWitness

namespace E2E.VoidCallViewWitness
open Backend Backend.Proof Backend.Proof.Driver LinkCheck
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def caller : Clif.Function := PreparedReturnPinCallerBoundaryWitness.input.funcs[1]!.func
private def target : String := PreparedReturnPinCallerBoundaryWitness.input.funcs[0]!.func.name
private def callB (i : MInst) : Bool := match i with
  | .call info => decide (info.dest = .sym target) && info.defs.isEmpty &&
      decide (info.uses = retPairs (decU info.uses))
  | _ => false
private def observed : Bool := match Stock.lower caller with
  | .error _ => false
  | .ok result => !result.code.hasTryCall && result.code.blocks.toList.any fun b => b.insts.toList.any callB
attribute [local irreducible] observed
-- witness: native_decide (the unchanged real mixed-program caller only)
private theorem observed_true : observed = true := by native_decide

/-- The real Stock caller's zero-def call executes for every original callee result and world. -/
theorem actual_stock_call_witness :
    ∃ (result : Stock.Result) (block : VBlock) (uses : List (Nat × Reg)),
      Stock.lower caller = .ok result ∧ result.code.hasTryCall = false ∧
      block ∈ result.code.blocks.toList ∧ .call ⟨.sym target,retPairs uses,[]⟩ ∈ block.insts.toList ∧
      ∀ (X : ExtSem) (F : BitVec 64 → Prop) (ctx : FnCtx) (ρ : Nat → CV)
        (w w' : Arm.ArmState) (actual : List CV),
        X.call (some target) (uses.map (ρ ·.1)) w = some (actual,w') →
        seqRun (csem F ctx X.voidCalls) [.call ⟨.sym target,retPairs uses,[]⟩] ρ w = some (.fall ρ w') := by
  have checked := observed_true
  unfold observed at checked
  cases lowered : Stock.lower caller with
  | error message => simp only [lowered,Bool.false_eq_true] at checked
  | ok result =>
    simp only [lowered,Bool.and_eq_true,Bool.not_eq_true',List.any_eq_true] at checked
    obtain ⟨noTry,block,member,i,present,selected⟩ := checked
    cases i <;> simp only [callB,Bool.false_eq_true] at selected
    rename_i info
    simp only [Bool.and_eq_true,decide_eq_true_eq,List.isEmpty_iff] at selected
    obtain ⟨⟨dest,defs⟩,uses⟩ := selected
    have same : info = ⟨.sym target,retPairs (decU info.uses),[]⟩ := by
      cases info
      simp only [CallInfo.mk.injEq]
      exact ⟨dest,uses,defs⟩
    rw [same] at present
    refine ⟨result,block,decU info.uses,rfl,noTry,member,present,?_⟩
    intro X F ctx ρ w w' actual run
    exact seqRun_call_voidCalls_int run

end E2E.VoidCallViewWitness

namespace E2E.VoidCallViewWitness
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.VoidCall
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
private def fullCheck : Bool := match Stock.lower caller with
  | .error _ => false
  | .ok result => Stock.VoidCall.check caller result.code
attribute [local irreducible] fullCheck
-- witness: native_decide (the original caller, signature, and actual Stock records only)
private theorem fullCheck_true : fullCheck = true := by native_decide

/-- The unchanged real mixed-program caller inhabits the complete call-aware source contract. -/
theorem actual_stock_source_domain_witness :
    ∃ result,Stock.lower caller = .ok result ∧ Domain caller result.code := by
  have checked := fullCheck_true
  unfold fullCheck at checked
  cases lowered : Stock.lower caller with
  | error message => simp only [lowered,Bool.false_eq_true] at checked
  | ok result =>
    rw [lowered] at checked
    exact ⟨result,rfl,check_domain checked⟩

end E2E.VoidCallViewWitness
