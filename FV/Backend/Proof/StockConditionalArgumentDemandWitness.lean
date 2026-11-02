import FV.Backend.Proof.StockConditionalArgumentDemand
import FV.Backend.Proof.StockConditionalGuardedWitness

namespace Backend.Stock.Proof.ConditionalValues.ArgumentDemandWitness
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

private abbrev function := ConditionalCalls.sourceFunction

/-- A real conditional passes the entry parameter to both successors. The derived lemmas
show that this argument is demanded after the body and that the actual guarded entry frame
holds its value; no argument fact is constructed by hand. -/
theorem argument_values_witness (X : ExtSem) (word : BitVec 64) :
    ∃ result,∃ (spec : ConditionalBodySpec function result function.blocks[0]! 0 0 7
      ⟨1,[7]⟩ ⟨2,[7]⟩ (csem (fun _ => False) ⟨0,0⟩ X)
      (fun _ _ _ => True) Clif.Env.empty {funcs := []}),
      ∃ (fr : Clif.Frame) (regs : Nat → CV),Stock.lower function = .ok result ∧
      Clif.enterFunc function [⟨.i64,word⟩] Clif.Mem.empty = .ok (fr,Clif.Mem.empty) ∧
      Demanded spec.term.output.state 7 ∧
      ValuesHeld (fun x => x ∈ ([7] : List Nat)) result.ctx fr
        (fun key => regs (aliasNum result.final.alias key)) := by
  obtain ⟨result,spec,_,_,_,regs,_,_,run,scope,dominated,entered,_,_,before,_,_⟩ :=
    GuardedWitness.executable_parameter_branch_witness X word
  have ordered : blockOrder function =
      .ok ⟨#[.original 0,.original 2,.original 1],#[#[2,1],#[],#[]]⟩ := by cbv
  have orderEq := Except.ok.inj ((stock_lower_order run).symm.trans ordered)
  have successors : result.order.successors[0]! = #[2,1] := by rw [orderEq]; rfl
  have firstTag : result.order.nodes[2]? = some (.original 1) := by rw [orderEq]; rfl
  have secondTag : result.order.nodes[1]? = some (.original 2) := by rw [orderEq]; rfl
  exact ⟨result,spec,_,regs,run,entered,
    spec.arguments_demanded run scope rfl successors firstTag secondTag
      (Or.inl (List.mem_singleton_self 7)),
    spec.argument_values run scope dominated rfl successors firstTag secondTag before (Or.inl rfl)⟩

end Backend.Stock.Proof.ConditionalValues.ArgumentDemandWitness
