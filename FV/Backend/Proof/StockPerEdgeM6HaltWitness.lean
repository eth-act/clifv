import FV.Backend.Proof.PerEdgeRegallocSound
import FV.Backend.Proof.RegallocCSem
import FV.Backend.Proof.StockTermContractWitness
namespace Backend.Stock.Proof.PerEdgeM6HaltWitness
open Backend.Proof Backend.Proof.Driver
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private def function : Clif.Function := {
  name := "stock_trap_abi_contract",sig := {callConv := some .systemV}
  blocks := [{id := 0,term := .trap (.user 9)}] }
private def allocated : RFunc := {spillSlots := 0,saved := [],blocks := #[#[.op 0 #[]]]}
local instance : DecidableEq (Except String Unit) := fun a b =>
  match a,b with
  | .ok (),.ok () => isTrue rfl
  | .error a,.error b =>
    if h : a = b then isTrue (congrArg Except.error h)
    else isFalse (fun eq => h (Except.error.inj eq))
  | .ok (),.error _ => isFalse (fun h => by cases h)
  | .error _,.ok () => isFalse (fun h => by cases h)
private def Observed : Prop := (Stock.lower function).toOption.map (fun (result : Result) => decide (
  checkAllocAt result.code result.edgeArgs allocated = .ok () ∧ result.code.blocks.size = 1 ∧
  (result.code.blocks[0]!).insts = #[.udf (.user 9)])) = some true
section Kernel
attribute [local semireducible] Isle.Aarch64.program Stock.runTerm
private theorem observed : Observed := by unfold Observed; decide +kernel
end Kernel
/-- Complete Stock trap and physical operand assignment inhabit concrete csem
halt simulation from function entry, including the actual original source trap. -/
theorem stock_per_edge_m6_halt_witness : ∃ result : Result,
    Stock.lower function = .ok result ∧ LowerScope function ∧
    checkAllocAt result.code result.edgeArgs allocated = .ok () ∧
    Clif.step Clif.Env.empty {funcs := []}
      ⟨{func := function,regs := fun _ => none,slots := [],body := [],term := .trap (.user 9)},[],Clif.Mem.empty⟩ =
        .trapped (.user 9) ∧
    ∀ (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) (w : Arm.ArmState)
        (m : Loc → CV) (ρ : Nat → CV),
      Star (MStep result.code (csem F ctx X) ckeep allocated)
        (MConf.init allocated m w) (.halt w) ∧
      Star (VStepAt result.code result.edgeArgs (csem F ctx X)) (VConf.init ρ w) (.halt w) := by
  obtain ⟨result,run,scope,_,source,_⟩ := TermContractWitness.stock_trap_term_contract_witness
  change Stock.lower function = .ok result at run
  change LowerScope function at scope
  have actual := observed
  unfold Observed at actual
  rw [run] at actual
  simp only [Except.toOption,Option.map_some,Option.some.injEq,decide_eq_true_eq] at actual
  obtain ⟨accepted,size,code⟩ := actual
  refine ⟨result,run,scope,accepted,source,?_⟩
  intro F ctx X w m ρ
  have placed : result.code.blocks[0]? = some result.code.blocks[0]! := by
    have bound : 0 < result.code.blocks.size := by omega
    simp [getElem!_def,Array.getElem?_eq_getElem bound]
  have step : MStep result.code (csem F ctx X) ckeep allocated
      (MConf.init allocated m w) (.halt w) := by
    change MStep result.code (csem F ctx X) ckeep allocated (.run ⟨0,[.op 0 #[]],m,w⟩) (.halt w)
    refine MStep.op (k := 0) (allocs := #[]) (i := .udf (.user 9)) (ops := #[])
        (outs := []) (outs' := []) (m2 := m) placed (by rw [code]; rfl) rfl rfl
      (by rfl) (by simp) (HavocOuts.refl _ _ _) ⟨fun _ _ => by simp [writeM],fun _ h => by cases h⟩ ?_
    simp [writeM]
    exact MNext.halt
  have execution := Star.single step
  exact ⟨execution,PerEdge.checkAlloc_halt (sem := csem F ctx X) (keep := ckeep) accepted ρ execution⟩
end Backend.Stock.Proof.PerEdgeM6HaltWitness
