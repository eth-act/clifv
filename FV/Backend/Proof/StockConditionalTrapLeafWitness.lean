import FV.Backend.Proof.StockConditionalTrapLeaf
import FV.Backend.Proof.StockScalarCheck

/-! Non-vacuity of the trap-leaf continuations: in a real conditional CFG whose `brif` reaches a
scalar block that ends in `trap`, Stock lowering succeeds, and that leaf supplies both successor
continuations for every machine semantics that meets the usual contracts. -/

namespace Backend.Stock.Proof.ConditionalValues.TrapLeafFixture
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false

/-- Entry `brif` to a block that ends in `trap` and to a return block. -/
def function : Clif.Function := {
  name := "conditional_trap_leaf"
  sig := { params := [⟨.i64,.none,.normal⟩], returns := [⟨.i64,.none,.normal⟩] }
  blocks := [
    { id := 0, params := [(0,.i64)], body := [], term := .brif 0 ⟨1,[]⟩ ⟨2,[]⟩ },
    { id := 1, params := [], body := [⟨[3],.binary .imul .i64 0 0⟩], term := .trap (.user 7) },
    { id := 2, params := [], body := [⟨[1],.binary .iadd .i64 0 0⟩], term := .ret [1] }] }

private def checks : Bool :=
  lowerScopeB function && dominatedB function &&
  function.blocks.all (fun b => b.body.all Scalar.maskMixedBodyEligible) &&
  match Stock.lower function with
  | .error _ => false
  | .ok result => decide (result.order.nodes[2]? = some (.original 1))

-- witness: native_decide (the fixed function's input checks and its lowering only)
private theorem checks_true : checks = true := by native_decide

theorem trap_leaf_witness : ∃ (result : Result) (b : Clif.Block),
    Stock.lower function = .ok result ∧ function.block? 1 = some b ∧ b.term = .trap (.user 7) ∧
    (∀ {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}, Refines F isem → DriverSem isem →
      ∀ {MR : MemRelT}, MRStable F MR → ∀ (env : Clif.Env) (cp : Clif.Program) (code : Clif.TrapCode),
        Nonempty (SuccessorTrap function result 0 ⟨1,[]⟩ isem MR env cp code)) ∧
    (∀ (isem : Backend.Proof.Sem) (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program)
      (vals : List Clif.Val) (cm : Clif.Mem),
        Nonempty (SuccessorReturn function result 0 ⟨1,[]⟩ isem MR env cp vals cm)) := by
  have h := checks_true
  unfold checks at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨scope,dominated⟩,bodies⟩,lowered⟩ := h
  have family : ∀ b ∈ function.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst := by
    intro b member stm present
    exact Scalar.maskMixedBodyEligible_sound
      (List.all_eq_true.mp (List.all_eq_true.mp bodies b member) stm present)
  cases run : Stock.lower function with
  | error message => rw [run] at lowered; cases lowered
  | ok result =>
    rw [run] at lowered
    have tag : result.order.nodes[2]? = some (.original 1) := of_decide_eq_true lowered
    have lookup : blockIdx? function 1 = some 1 := by decide
    have found : function.block? 1 = some function.blocks[1]! := by decide
    have source : function.blocks[1]? = some function.blocks[1]! := by decide
    refine ⟨result,_,rfl,found,rfl,?_,?_⟩
    · intro F isem refines driver MR stable env cp code
      exact SuccessorTrap.of_trap_block run (lowerScope_of scope) (dominated_of dominated) family
        refines driver stable lookup found source tag rfl (by decide) (by decide)
    · intro isem MR env cp vals cm
      exact SuccessorReturn.of_trap_block run family lookup found source tag rfl (by decide)

end Backend.Stock.Proof.ConditionalValues.TrapLeafFixture
