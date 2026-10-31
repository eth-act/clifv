import FV.Backend.Proof.StockMemoryInput
import FV.Backend.Proof.StockMemoryNopJumpSpec
import FV.Backend.Proof.LowerDecide
import FV.E2E.RegLevelDriverSem

namespace Backend.Stock.Memory.CapturedFixture
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

def function : Clif.Function := { LoadFixture.function with
  name := "_RNxC13h_dyn_generic12H3GPtIT8Zs5B"
  blocks := [{id := 0,params := [(0,.i64)],body := [⟨[],.nop⟩],term := .jump ⟨1,[]⟩},
    {id := 1,body := [⟨[],.nop⟩,⟨[2],.load .load .i32 LoadFixture.flags 0 0⟩],term := .ret [2]}] }

private def original : Ctx × Array (Nat × Nat) × LState :=
  (Backend.buildCtx function).toOption.getD (sinkCtx,#[],default)
private theorem original_build : Backend.buildCtx function = .ok original := rfl

theorem scope : LowerScope function := lowerScope_of rfl

private theorem pointer_available : 0 ∈ (availIn function original.1).getD 1 [] := by
  have good : FixOk function original.1 id (fun tl x => tl = 1 ∧ x = 0) := by
    constructor
    · intro tl x pair
      obtain ⟨rfl,rfl⟩ := pair
      exact ⟨by decide,by decide,by decide +kernel,by decide,by decide,by decide⟩
    · intro tl x pair p predecessor
      obtain ⟨rfl,rfl⟩ := pair
      cases p with
      | zero => exact Or.inl (by simp [parsOf,function])
      | succ p => cases p <;> simp [succIdx,succIds,dests,function] at predecessor
    · intro tl x pair y member
      obtain ⟨rfl,rfl⟩ := pair
      change y ∈ ([] : List Nat) at member
      cases member
  exact inFix_greatest good ⟨rfl,rfl⟩

/-- Original SSA and dominance include the inherited pointer after both NOPs. -/
theorem dominated : Dominated function := by
  constructor
  · change ([0,2] : List Nat).Nodup
    decide +kernel
  · intro ctx ranges st build bi b found
    have context : ctx = original.1 := congrArg Prod.fst (Except.ok.inj (build.symm.trans original_build))
    subst ctx
    have bound : bi < 2 := by have h := lt_of_getElem? found; simpa [function] using h
    have cases : bi = 0 ∨ bi = 1 := by omega
    rcases cases with rfl | rfl
    · simp [function] at found
      subst b
      constructor
      · intro j stm present
        cases j with
        | zero =>
          simp [function] at present
          subst stm
          intro x member
          simp [Driver.instArgs] at member
        | succ j => simp [function] at present
      · intro x member
        simp [abiTerm,Driver.termArgs,sretRet,sigRets,function] at member
    · simp [function] at found
      subst b
      constructor
      · intro j stm present
        cases j with
        | zero =>
          simp [function] at present
          subst stm
          intro x member
          simp [Driver.instArgs] at member
        | succ j =>
          cases j with
          | zero =>
            simp [function] at present
            subst stm
            intro x member
            have equal : x = 0 := List.mem_singleton.mp member
            subst x
            have member := pointer_available
            simpa [availOf,function,defsBefore,defsFrom] using member
          | succ j => simp [function] at present
      · intro x member
        have equal : x = 2 := by simpa [abiTerm,Driver.termArgs,sretRet,sigRets,function,LoadFixture.function] using member
        subst x
        simp [availOf,function,defsBefore,defsFrom]
  · intro ctx ranges st build tl x available notLocal y member
    cases tl with
    | zero =>
      have fixed := (inFix_fixOk (f := function) (ctx := ctx) (gn := id)).cand 0 x available
      omega
    | succ tl =>
      cases tl with
      | zero => change y ∉ ([] : List Nat); simp
      | succ tl => simp [parsOf,function]

-- Fixed non-vacuity witness; no generic correctness theorem uses this check.
private theorem lowered_entry : (match Stock.lower function with
    | .error _ => false
    | .ok result => decide (result.order.nodes[0]? = some (.original 0))) = true := by native_decide

/-- The actual Stock driver accepts the nonempty captured shape. -/
theorem lowered : (Stock.lower function).isOk = true := by
  have checked := lowered_entry
  cases run : Stock.lower function with
  | error error => rw [run] at checked; cases checked
  | ok result => rfl

theorem entry_tag {result : Result} (run : Stock.lower function = .ok result) :
    result.order.nodes[0]? = some (.original 0) := by
  simpa only [run,decide_eq_true_eq] using lowered_entry

/-- The NOP jump contract is inhabited while the successor contains an actual load. -/
theorem nop_jump_witness (X : ExtSem) :
    ∃ result, Stock.lower function = .ok result ∧
      Nonempty (Control.JumpBodySpec function result function.blocks[0]! 0 0 ⟨1,[]⟩
        (csem LoadFixture.relation.F ⟨0,0⟩ X) (LoadFixture.relation.holds function)
        Clif.Env.empty {funcs := []}) := by
  have success := lowered
  cases run : Stock.lower function with
  | error error => rw [run] at success; cases success
  | ok result =>
    refine ⟨result,rfl,?_⟩
    exact Control.stock_lower_nop_jump_body_spec run scope dominated (entry_tag run) rfl
      (by intro stm member; have equal : stm = ⟨[],.nop⟩ := by simpa [function] using member
          subst stm; rfl)
      rfl (driverSem_csem LoadFixture.relation.F ⟨0,0⟩ X) _ _

end Backend.Stock.Memory.CapturedFixture
