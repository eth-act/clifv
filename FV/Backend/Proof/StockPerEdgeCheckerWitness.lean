import FV.Backend.Proof.PerEdgeRegallocLemmas
import FV.Backend.Proof.RegallocCSem
import FV.Backend.Proof.StockPerSuccessorWitness
namespace Backend.Stock.Proof.PerEdgeCheckerWitness
open Backend.Proof Backend.Proof.Driver
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private def function : Clif.Function := {
  name := "stock_per_successor_migration"
  sig := {params := [⟨.i64,.none,.normal⟩],returns := [⟨.i64,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(7,.i64)],term := .brif 7 ⟨1,[7]⟩ ⟨2,[7]⟩},
    {id := 1,params := [(31,.i64)],term := .ret [31]}, {id := 2,params := [(47,.i64)],term := .ret [47]}] }
private def allocated : RFunc := { spillSlots := 0,saved := [],blocks := #[
  #[.op 0 #[.reg (.x 0)],.op 1 #[.reg (.x 0)]],
  #[.op 0 #[.reg (.x 0)]],#[.op 0 #[.reg (.x 0)]]] }
private def checker (result : Result) : CheckCtx := ⟨result.code,#[#[2,1],#[],#[]],allocated,128⟩
private def before : AState := AState.define (Array.replicate 128 []) (.reg (.x 0)) (.vreg 192)
private def after (index : Nat) : AState := before.parCopy [if index = 0 then 193 else 194] [192]
private def memory (word : CV) : Loc → CV := upd (fun _ => 0) (.reg (.x 0)) word
private def registers (word : CV) : Nat → CV := upd (fun _ => 0) 192 word
local instance : DecidableEq (Except String Unit) := fun a b =>
  match a,b with
  | .ok (),.ok () => isTrue rfl
  | .error a,.error b =>
    if h : a = b then isTrue (congrArg Except.error h)
    else isFalse (fun eq => h (Except.error.inj eq))
  | .ok (),.error _ => isFalse (fun h => by cases h)
  | .error _,.ok () => isFalse (fun h => by cases h)

private def Observed : Prop := (Stock.lower function).toOption.map (fun (result : Result) => decide (
  checkAllocAt result.code result.edgeArgs allocated = .ok () ∧
  checkAlloc result.code allocated = .error "edge 0 → 2: 0 arguments for 1 parameters" ∧
  result.code.blocks.size = 3 ∧ result.edgeArgs[0]? = some #[#[Reg.vreg 192 .int],#[Reg.vreg 192 .int]] ∧
  (result.code.blocks[1]!).params = #[.vreg 194 .int] ∧ (result.code.blocks[2]!).params = #[.vreg 193 .int] ∧
  (result.code.blocks[0]!).insts = #[.args [(.vreg 192 .int,.x 0)],.condBr 2 1 (.notZero (.vreg 192 .int) .size64)])) = some true
section Kernel
attribute [local semireducible] Isle.Aarch64.program Stock.runTerm
private theorem observed : Observed := by unfold Observed; decide +kernel
end Kernel

/-- The complete original-scope/dominated Stock conditional and real physical
operand assignments are accepted by the new checker. Its final verifier checks
every indexed edge; the legacy checker rejects these same allocated blocks. -/
theorem stock_per_edge_checker_witness : ∃ result : Result,
    Stock.lower function = .ok result ∧ LowerScope function ∧ Dominated function ∧
    checkAllocAt result.code result.edgeArgs allocated = .ok () ∧
    checkAlloc result.code allocated = .error "edge 0 → 2: 0 arguments for 1 parameters" ∧
    ∃ succs preds ins,result.code.cfg = .ok (succs,preds) ∧
      ∃ a0,ins[0]? = some (some a0) ∧ a0.le (entryState 128) = true ∧
      ∀ b,b < result.code.blocks.size → ∃ a out,ins[b]? = some (some a) ∧
        (⟨result.code,succs,allocated,128⟩ : CheckCtx).runBlock b a = .ok out ∧
        PerEdge.EdgesOk ⟨result.code,succs,allocated,128⟩ result.edgeArgs ins b out := by
  obtain ⟨result,run,scope,dominated,_⟩ := PerSuccessorWitness.stock_per_successor_migration_witness
    0 (fun _ => 0) 0 (by decide)
  change Stock.lower function = .ok result at run
  change LowerScope function at scope
  change Dominated function at dominated
  have actual := observed
  unfold Observed at actual
  rw [run] at actual
  simp only [Except.toOption,Option.map_some,Option.some.injEq,decide_eq_true_eq] at actual
  obtain ⟨accepted,rejected,_⟩ := actual
  obtain ⟨succs,preds,ins,cfg,_,_,verified⟩ := PerEdge.checkAlloc_ok accepted
  obtain ⟨⟨a0,entry,le⟩,blocks⟩ := PerEdge.verify_ok verified
  exact ⟨result,run,scope,dominated,accepted,rejected,succs,preds,ins,cfg,a0,entry,le,
    fun b bound => PerEdge.verifyBlock_ok (blocks b bound)⟩

private theorem before_inv (word : CV) : Inv (fun _ value => value) before (memory word) (registers word) (fun _ => 0) := by
  have empty : Inv (fun (_ : Reg) (value : CV) => value) (Array.replicate 128 [])
      (fun _ => 0) (fun _ => 0) (fun _ => 0) := by
    intro location symbol member
    cases found : location.index <;> simp [AState.get,found,Array.getD] at member
  exact Inv_define (.reg (.x 0)) 192 word empty
private theorem copied_member (index : Nat) (bound : index < 2) :
    Sym.vreg (if index = 0 then 193 else 194) ∈ (after index).get (.reg (.x 0)) := by
  have positions : index = 0 ∨ index = 1 := by omega
  rcases positions with rfl | rfl <;> decide +kernel
private theorem copy_run {result : Result} (size : result.code.blocks.size = 3)
    (row : result.edgeArgs[0]? = some #[#[Reg.vreg 192 .int],#[Reg.vreg 192 .int]])
    (params1 : (result.code.blocks[1]!).params = #[.vreg 194 .int])
    (params2 : (result.code.blocks[2]!).params = #[.vreg 193 .int])
    (index : Nat) (bound : index < 2) :
    (checker result).edgeCopyAt result.edgeArgs 0 (2-index) index before = .ok (after index) := by
  have h0 : 0 < result.code.blocks.size := by omega
  have ht : 2-index < result.code.blocks.size := by omega
  have source : result.code.blocks[0]? = some result.code.blocks[0]! := by
    simp [getElem!_def,Array.getElem?_eq_getElem h0]
  have target : result.code.blocks[2-index]? = some result.code.blocks[2-index]! := by
    simp [getElem!_def,Array.getElem?_eq_getElem ht]
  have positions : index = 0 ∨ index = 1 := by omega
  unfold CheckCtx.edgeCopyAt
  dsimp only [checker]
  rw [source,target]
  rcases positions with rfl | rfl <;> simp [row,params1,params2,ensure,vregNum,after,List.mapM_cons]
/-- For the complete accepted Stock conditional, either real indexed checker
edge preserves a nonempty symbolic/concrete invariant over arbitrary values.
The successor parameter is actually present and holds the copied input value. -/
theorem stock_per_edge_checker_value_witness (word : CV) (index : Nat) (bound : index < 2) :
    ∃ (result : Result) (ρ' : Nat → CV),Stock.lower function = .ok result ∧
      LowerScope function ∧ Dominated function ∧ checkAllocAt result.code result.edgeArgs allocated = .ok () ∧
      (checker result).edgeAt result.edgeArgs 0 (2-index) index before = .ok (after index) ∧
      edgeEnvAt result.code result.edgeArgs 0 (2-index) index (registers word) = some ρ' ∧
      Inv (fun _ value => value) (after index) (memory word) ρ' (fun _ => 0) ∧
      Sym.vreg (if index = 0 then 193 else 194) ∈ (after index).get (.reg (.x 0)) ∧
      ρ' (if index = 0 then 193 else 194) = word := by
  obtain ⟨result,run,scope,dominated,accepted,_⟩ := stock_per_edge_checker_witness
  have actual := observed
  unfold Observed at actual
  rw [run] at actual
  simp only [Except.toOption,Option.map_some,Option.some.injEq,decide_eq_true_eq] at actual
  obtain ⟨_,_,size,row,params1,params2,code⟩ := actual
  have copy := copy_run size row params1 params2 index bound
  have source : result.code.blocks[0]? = some result.code.blocks[0]! := by
    have h : 0 < result.code.blocks.size := by omega
    simp [getElem!_def,Array.getElem?_eq_getElem h]
  have forget : (checker result).edgeForget 0 (2-index) before = before := by
    simp [checker,CheckCtx.edgeForget,source,code,MInst.normalDead]
  have edge : (checker result).edgeAt result.edgeArgs 0 (2-index) index before = .ok (after index) := by
    simpa only [CheckCtx.edgeAt,forget] using copy
  have inv : Inv (fun _ value => value) ((checker result).edgeForget 0 (2-index) before)
      (memory word) (registers word) (fun _ => 0) := by simpa only [forget] using before_inv word
  obtain ⟨ρ',environment,preserved⟩ := PerEdge.edge_ok edge inv
  have member := copied_member index bound
  have value := preserved (.reg (.x 0)) (.vreg (if index = 0 then 193 else 194)) member
  change memory word (.reg (.x 0)) = ρ' (if index = 0 then 193 else 194) at value
  simp only [memory,upd,ite_true] at value
  exact ⟨result,ρ',run,scope,dominated,accepted,edge,environment,preserved,member,value.symm⟩
end Backend.Stock.Proof.PerEdgeCheckerWitness

