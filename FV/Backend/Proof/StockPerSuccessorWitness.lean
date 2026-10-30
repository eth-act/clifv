import FV.Backend.Proof.IselExtern
import FV.Backend.Proof.StockPolicy
import FV.Backend.Proof.LowerDecide

/-! An accepted ordinary branching function exposes the remaining per-successor
consumer migration. Raw Stock keeps the correct vectors in Result.edgeArgs;
legacy VCode.edgeEnv alone cannot represent these nonsynthetic edges. -/
namespace Backend.Stock.Proof.PerSuccessorWitness
open Backend.Proof Backend.Proof.Driver Backend.Proof.Driver.Fix
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private def function : Clif.Function := {
  name := "stock_per_successor_migration"
  sig := {params := [⟨.i64,.none,.normal⟩],returns := [⟨.i64,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(7,.i64)],term := .brif 7 ⟨1,[7]⟩ ⟨2,[7]⟩},
    {id := 1,params := [(31,.i64)],term := .ret [31]}, {id := 2,params := [(47,.i64)],term := .ret [47]}] }
private def original : Ctx × Array (Nat × Nat) × LState :=
  (Backend.buildCtx function).toOption.getD (sinkCtx,#[],default)
private theorem original_build : Backend.buildCtx function = .ok original := rfl
private def first (word : BitVec 64) : Clif.Frame := {
  func := function,regs := Clif.Regs.empty.set 7 ⟨.i64,word⟩,slots := [],body := [],term := .brif 7 ⟨1,[7]⟩ ⟨2,[7]⟩ }
private def after (word : BitVec 64) (index : Nat) : Clif.Frame := {
  first word with regs := (first word).regs.set (if index = 0 then 31 else 47) ⟨.i64,word⟩,term := .ret [if index = 0 then 31 else 47] }
private def Observed : Prop := (Stock.lower function).toOption.map (fun result => decide (
  result.code.blocks.size = 3 ∧ (result.code.blocks[0]!).branchArgs = #[] ∧
  (result.code.blocks[1]!).params.size = 1 ∧ (result.code.blocks[2]!).params.size = 1 ∧
  result.edgeArgs[0]! = #[#[.vreg 192 .int],#[.vreg 192 .int]])) = some true
section Kernel
attribute [local semireducible] Isle.Aarch64.program Stock.runTerm
private theorem observed : Observed := by unfold Observed; decide +kernel
end Kernel
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
      · intro j stm present; simp at present
      · intro x member
        simp [abiTerm,Driver.termArgs,sretRet,sigRets,function] at member
        subst x
        simp [availOf,function,defsBefore,defsFrom]
  · intro ctx ranges st build tl x available notLocal y member
    have fixed := (inFix_fixOk (f := function) (ctx := ctx) (gn := id)).cand tl x available
    have values : x = 7 ∨ x = 31 ∨ x = 47 := by simpa [valueDefs,function] using fixed.2.2.2.1
    have context : ctx = original.1 := congrArg Prod.fst (Except.ok.inj (build.symm.trans original_build))
    rw [context] at member
    rcases values with rfl | rfl | rfl
    all_goals change y ∈ ([] : List Nat) at member; cases member

private theorem absent_edge {vc : VCode} (size : vc.blocks.size = 3)
    (args : vc.blocks[0]!.branchArgs = #[]) {target : Nat} (bound : target < 3)
    (params : vc.blocks[target]!.params.size = 1) (ρ : Nat → CV) : edgeEnv vc 0 target ρ = none := by
  have source : vc.blocks[0]? = some vc.blocks[0]! := by
    have h : 0 < vc.blocks.size := by omega
    simp [getElem!_def,Array.getElem?_eq_getElem h]
  have targetFound : vc.blocks[target]? = some vc.blocks[target]! := by
    have h : target < vc.blocks.size := by omega
    simp [getElem!_def,Array.getElem?_eq_getElem h]
  unfold edgeEnv
  simp [source,targetFound,args,params]

/-- Complete original-scope/dominated lowering preserves both nonempty outgoing
vectors, while legacy VCode.edgeEnv rejects both direct successors for every
machine file. Successful source entry, successor binding and return rule out
excluding these accepted inputs instead of migrating per-successor consumers. -/
theorem stock_per_successor_migration_witness (word : BitVec 64) (ρ : Nat → CV)
    (index : Nat) (bound : index < 2) : ∃ result : Result,
    Stock.lower function = .ok result ∧ LowerScope function ∧ Dominated function ∧
    result.edgeArgs[0]! = #[#[.vreg 192 .int],#[.vreg 192 .int]] ∧
    edgeEnv result.code 0 1 ρ = none ∧ edgeEnv result.code 0 2 ρ = none ∧
    Clif.enterFunc function [⟨.i64,word⟩] Clif.Mem.empty = .ok (first word,Clif.Mem.empty) ∧
    Clif.enterBlock (first word) ⟨1+index,[7]⟩ = .ok (after word index) ∧
    Clif.stepTerm Clif.Env.empty {funcs := []} ⟨after word index,[],Clif.Mem.empty⟩
      (.ret [if index = 0 then 31 else 47]) = .done [⟨.i64,word⟩] Clif.Mem.empty := by
  have actual := observed
  unfold Observed at actual
  cases run : Stock.lower function with
  | error err => simp only [run,Except.toOption,Option.map_none] at actual; cases actual
  | ok result =>
    rw [run] at actual
    simp only [Except.toOption,Option.map_some,Option.some.injEq,decide_eq_true_eq] at actual
    obtain ⟨size,args,params1,params2,vectors⟩ := actual
    have cases : index = 0 ∨ index = 1 := by omega
    refine ⟨result,rfl,lowerScope_of (by decide +kernel),dominated,vectors,
      absent_edge size args (by decide) params1 ρ,absent_edge size args (by decide) params2 ρ,rfl,?_,?_⟩
    · rcases cases with rfl | rfl <;> rfl
    · rcases cases with rfl | rfl <;> rfl
end Backend.Stock.Proof.PerSuccessorWitness
