import FV.Backend.Proof.StockPolicy
import FV.Backend.Proof.LowerDecide

namespace Backend.Stock.Proof.ConditionalValues.EmptyFixture
open Backend.Proof Backend.Proof.Driver Backend.Proof.Driver.Fix
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000

def function : Clif.Function := {
  name := "stock_conditional_empty_arguments"
  sig := {params := [⟨.i64,.none,.normal⟩],returns := [⟨.i64,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(7,.i64)],term := .brif 7 ⟨1,[]⟩ ⟨2,[]⟩},
    {id := 1,body := [⟨[31],.iconst .i64 1⟩],term := .ret [31]},
    {id := 2,body := [⟨[47],.iconst .i64 2⟩],term := .ret [47]}] }
def initial : Clif.Frame := {
  func := function,regs := Clif.Regs.empty.set 7 ⟨.i64,1⟩,slots := [],
  body := [],term := .brif 7 ⟨1,[]⟩ ⟨2,[]⟩ }
private theorem lower_success : (Stock.lower function).isOk = true := by decide +kernel
private theorem scope : LowerScope function := lowerScope_of rfl
private def original : Ctx × Array (Nat × Nat) × LState :=
  (Backend.buildCtx function).toOption.getD (sinkCtx,#[],default)
private theorem original_build : Backend.buildCtx function = .ok original := rfl
private theorem dominated : Dominated function := by
  constructor
  · change ([7,31,47] : List Nat).Nodup; decide +kernel
  · intro ctx ranges st build bi b found
    have bound : bi < 3 := by have h := lt_of_getElem? found; simpa [function] using h
    have cases : bi = 0 ∨ bi = 1 ∨ bi = 2 := by omega
    rcases cases with rfl | rfl | rfl
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
  · intro ctx ranges st build tl x available notLocal y member
    have fixed := (inFix_fixOk (f := function) (ctx := ctx) (gn := id)).cand tl x available
    have values : x = 7 ∨ x = 31 ∨ x = 47 := by simpa [valueDefs,function] using fixed.2.2.2.1
    have context : ctx = original.1 := congrArg Prod.fst (Except.ok.inj (build.symm.trans original_build))
    rw [context] at member
    rcases values with rfl | rfl | rfl
    all_goals change y ∈ ([] : List Nat) at member; cases member

/-- Complete original-scope source execution with empty outgoing arguments and
nonempty scalar successor bodies; actual lowering is checked by the kernel. -/
theorem driver_witness : ∃ result,Stock.lower function = .ok result ∧ LowerScope function ∧ Dominated function ∧
    Clif.enterFunc function [⟨.i64,1⟩] Clif.Mem.empty = .ok (initial,Clif.Mem.empty) ∧
    Clif.runLoop Clif.Env.empty {funcs := []} 3 ⟨initial,[],Clif.Mem.empty⟩ =
      .returned [⟨.i64,1⟩] Clif.Mem.empty := by
  have success := lower_success
  cases run : Stock.lower function with
  | error message => rw [run] at success; cases success
  | ok result => exact ⟨result,rfl,scope,dominated,rfl,rfl⟩

end Backend.Stock.Proof.ConditionalValues.EmptyFixture
