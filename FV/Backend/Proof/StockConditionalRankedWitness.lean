import FV.Backend.Lowering.StockConditionalRankedCfg
import FV.Backend.Proof.StockConditionalRankedFixture
import FV.Backend.Proof.MemRefines
import FV.Backend.Proof.StockScalarCheck
import FV.Backend.Proof.StockConditionalRankedDomain
import FV.Backend.Proof.RefinesCSem
import FV.E2E.RegLevelDriverSem

namespace Backend.Stock.Proof.ConditionalValues.RankedFixture
open Backend.Proof Backend.Proof.Driver
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000
private theorem scope : LowerScope function := lowerScope_of rfl
private def original : Ctx × Array (Nat × Nat) × LState :=
  (Backend.buildCtx function).toOption.getD (sinkCtx,#[],default)
private theorem original_build : Backend.buildCtx function = .ok original := rfl
private theorem inherited_available : (31 : Nat) ∈ (availIn function original.1).getD 3 [] := by
  have size : original.1.valDef.size = 48 := rfl
  have fixed : FixOk function original.1 id (fun tl x => tl = 3 ∧ x = 31) := by
    constructor
    · rintro tl x ⟨rfl,rfl⟩
      simp [size,function,valueDefs,parsOf]
    · rintro tl x ⟨rfl,rfl⟩ p successor
      rcases p with _ | (_ | (_ | (_ | p)))
      · exact False.elim ((by decide +kernel : (3 : Nat) ∉ succIdx function 0) successor)
      · exact .inr (.inl (by decide +kernel))
      · simp [succIdx,function,succIds,dests] at successor
      · simp [succIdx,function,succIds,dests] at successor
      · simp [succIdx,function,succIds,dests] at successor
    · rintro tl x ⟨rfl,rfl⟩ y member
      change y ∈ ([] : List Nat) at member
      cases member
  exact inFix_greatest fixed ⟨rfl,rfl⟩
private theorem dominated : Dominated function := by
  constructor
  · change ([7,31,47] : List Nat).Nodup; decide +kernel
  · intro ctx ranges st build bi b found
    have bound : bi < 4 := by have h := lt_of_getElem? found; simpa [function] using h
    have cases : bi = 0 ∨ bi = 1 ∨ bi = 2 ∨ bi = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    all_goals
      simp [function] at found
      subst b
      constructor
      · intro j stm present
        cases j <;> simp [function] at present
        all_goals subst stm; intro x member; cases member
      · intro x member
        simp [abiTerm,Driver.termArgs,sretRet,sigRets,function] at member <;>
          subst x <;> simp [availOf,function,defsBefore,defsFrom]
        all_goals
          have context : ctx = original.1 := congrArg Prod.fst (Except.ok.inj (build.symm.trans original_build))
          rw [context]
          rw [← Array.getD_eq_getD_getElem?]
          with_unfolding_all exact inherited_available
  · intro ctx ranges st build tl x available notLocal y member
    have fixed := (inFix_fixOk (f := function) (ctx := ctx) (gn := id)).cand tl x available
    have values : x = 7 ∨ x = 31 ∨ x = 47 := by simpa [valueDefs,function] using fixed.2.2.2.1
    have context : ctx = original.1 := congrArg Prod.fst (Except.ok.inj (build.symm.trans original_build))
    rw [context] at member
    rcases values with rfl | rfl | rfl
    all_goals change y ∈ ([] : List Nat) at member; cases member


open Backend.Stock.Proof.ForwardSource
private theorem tail_terms : NonentryJumpReturnBlocks function := by
  intro bi b found nonentry
  have bound : bi < 4 := by have h := lt_of_getElem? found; simpa [function] using h
  have cases : bi = 0 ∨ bi = 1 ∨ bi = 2 ∨ bi = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  · exact False.elim (nonentry rfl)
  all_goals simp [function] at found; subst b
  all_goals first | exact Or.inl ⟨_,rfl⟩ | exact Or.inr ⟨_,rfl⟩
private theorem ranked : Ranked function id := by
  intro bi b ti destination found present target
  have bound : bi < 4 := by have h := lt_of_getElem? found; simpa [function] using h
  have cases : bi = 0 ∨ bi = 1 ∨ bi = 2 ∨ bi = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  all_goals simp [function] at found; subst b
  all_goals simp [destinations] at present
  all_goals first | subst destination | rcases present with rfl | rfl
  all_goals first
    | change some 1 = some ti at target; cases target; decide
    | change some 2 = some ti at target; cases target; decide
    | change some 3 = some ti at target; cases target; decide
/-- The complete original conditional source has ranked jump/return tails,
real inherited availability, and unchanged original scope/dominance inputs. -/
theorem ranked_input_witness : NonentryJumpReturnBlocks function ∧ Ranked function id ∧
    LowerScope function ∧ Dominated function ∧
    (31 : Nat) ∈ (availIn function original.1).getD 3 [] :=
  ⟨tail_terms,ranked,scope,dominated,inherited_available⟩
end Backend.Stock.Proof.ConditionalValues.RankedFixture
namespace Backend.Stock.Proof.ConditionalValues.RankedFixture
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
/-- A complete conditional source continues through a real scalar jump tail,
with different return values on the two selected paths. -/
theorem source_witness : ∃ result,Stock.lower function = .ok result ∧ LowerScope function ∧ Dominated function ∧
    Clif.enterFunc function [⟨.i64,1⟩] Clif.Mem.empty = .ok (initial 1,Clif.Mem.empty) ∧
    Clif.runLoop Clif.Env.empty {funcs := []} 4 ⟨initial 1,[],Clif.Mem.empty⟩ = .returned [⟨.i64,1⟩] Clif.Mem.empty ∧
    Clif.runLoop Clif.Env.empty {funcs := []} 4 ⟨initial 0,[],Clif.Mem.empty⟩ = .returned [⟨.i64,2⟩] Clif.Mem.empty := by
  have success := lower_success
  cases run : Stock.lower function with
  | error message => rw [run] at success; cases success
  | ok result => exact ⟨result,rfl,scope,dominated,rfl,rfl,rfl⟩

private def ranked_shape : Backend.Stock.ConditionalCfg.RankedShape function where
  entry := function.blocks[0]!
  condition := 7
  yes := ⟨1,[]⟩
  no := ⟨2,[]⟩
  source := rfl
  term := rfl
  parameter := ⟨.i64,by decide +kernel,Or.inr rfl⟩
  targets := by
    intro bc choice
    rcases choice with rfl | rfl
    · exact ⟨rfl,1,rfl,by decide⟩
    · exact ⟨rfl,2,rfl,by decide⟩
  tails := tail_terms
  ranked := ranked
  family := by
    intro b member stm present
    have bodies : function.blocks.all (fun b => b.body.all Backend.Stock.Scalar.maskMixedBodyEligible) = true := by decide +kernel
    exact Backend.Stock.Scalar.maskMixedBodyEligible_sound
      (List.all_eq_true.mp (List.all_eq_true.mp bodies b member) stm present)
/-- The actual compiled four-block conditional source satisfies the unchanged
universal production domain; the source witness executes both branch results. -/
theorem ranked_domain_witness : ∃ result,Stock.lower function = .ok result ∧
    Backend.Stock.Scalar.Domain function := by
  obtain ⟨result,lowered,_,_,_,_,_⟩ := source_witness
  exact ⟨result,lowered,Backend.Stock.ConditionalCfg.domain_of_ranked_shape ranked_shape scope dominated
    (by decide +kernel) (by decide +kernel)⟩
end Backend.Stock.Proof.ConditionalValues.RankedFixture

namespace Backend.Stock.Proof.ConditionalValues.RankedFixture
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
/-- Positive source syntax beyond the existing return-leaf class. -/
theorem ranked_selector_witness : Backend.Stock.ConditionalCfg.rankedEligible function = true ∧
    Backend.Stock.ConditionalCfg.eligible function = false := by decide +kernel
-- Fixed ORIGINAL source/class/scope/dominance/ABI checks only; never compiler output or universal correctness.
private theorem ranked_input_checks : Backend.Stock.ConditionalCfg.rankedSourceOk function = true := by native_decide
/-- The actual kernel-compiled original source inhabits executable checker soundness. -/
theorem checked_ranked_driver_witness : ∃ result,Stock.lower function = .ok result ∧
    Backend.Stock.Scalar.Domain function ∧ Backend.Stock.ConditionalCfg.rankedCheck function result.code = true := by
  obtain ⟨result,lowered,domain⟩ := ranked_domain_witness
  exact ⟨result,lowered,domain,by simp [Backend.Stock.ConditionalCfg.rankedCheck,ranked_input_checks,lowered]⟩
end Backend.Stock.Proof.ConditionalValues.RankedFixture

namespace Backend.Stock.Proof.ConditionalValues.RankedFixture
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
/-- Actual instruction-zero ABI execution follows both choices through the
new tail class, with different source return values and real compiled code. -/
theorem ranked_machine_return_witness (X : ExtSem) (branch : Bool) :
    ∃ result ρ0,Stock.lower function = .ok result ∧
      RunOkABI function result.code (csem (fun _ => False) ⟨0,0⟩ X) (fun _ _ _ => True)
        (initial (if branch then 1 else 0)).slots
        ⟨0,0,ρ0,Arm.write_base_gpr 0#5 (if branch then 1 else 0) Arm.ArmState.default⟩
        (.returned [⟨.i64,if branch then 1 else 2⟩] Clif.Mem.empty) := by
  obtain ⟨result,run,domain⟩ := ranked_domain_witness
  have entered : Clif.enterFunc function [⟨.i64,if branch then 1 else 0⟩] Clif.Mem.empty =
      .ok (initial (if branch then 1 else 0),Clif.Mem.empty) := by cases branch <;> rfl
  have returned : Clif.runLoop Clif.Env.empty {funcs := []} 4
      ⟨initial (if branch then 1 else 0),[],Clif.Mem.empty⟩ =
      .returned [⟨.i64,if branch then 1 else 2⟩] Clif.Mem.empty := by cases branch <;> rfl
  let initialWorld := Arm.write_base_gpr 0#5 (if branch then 1 else 0) Arm.ArmState.default
  have arguments : ArgsAtEntry (fun _ => False) function.sig [⟨.i64,if branch then 1 else 0⟩] initialWorld := by
    intro loc value member
    change (loc,value) ∈ [(.reg (.x 0),⟨.i64,if branch then 1 else 0⟩)] at member
    have same := List.mem_singleton.mp member
    cases same
    simp only [VHolds,regVal,initialWorld,Arm.r,Arm.read_base_gpr,Arm.write_base_gpr,
      Arm.read_store,Arm.write_store,rnum]
    cases branch <;> rfl
  have memorySem : MemRefines (fun _ => False) 0 (fun _ => none) (csem (fun _ => False) ⟨0,0⟩ X) :=
    memRefines_csem (fun _ => False) ⟨0,0⟩ X rfl (fun _ _ h => by cases h)
  have stable : MRStable (fun _ => False) (fun _ _ _ => True) := by intro _ _ _ _ _ _; trivial
  obtain ⟨ρ0,semantics⟩ := domain.returns run (SourceEntry.of_enterFunc entered) returned
    (refines_csem (fun _ => False) ⟨0,0⟩ X) (driverSem_csem (fun _ => False) ⟨0,0⟩ X)
    memorySem stable trivial arguments
  exact ⟨result,ρ0,run,semantics⟩
end Backend.Stock.Proof.ConditionalValues.RankedFixture
