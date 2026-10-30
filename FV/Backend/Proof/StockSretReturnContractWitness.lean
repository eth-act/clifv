import FV.Backend.Proof.StockAliasSemantics
import FV.Backend.Proof.LowerDecide
import FV.Backend.Proof.StockBodyScanOrigin

/-! Record the actual implicit struct-return ABI boundary before transporting
legacy return semantics. Stock's x8 pin does not satisfy the legacy fixed x0..
list, even under the original source conditions. No runtime code is changed. -/
namespace Backend.Stock.Proof.SretReturnContractWitness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitBranch scanBlock
private def function : Clif.Function := {
  name := "stock_sret_return_contract"
  sig := {params := [⟨.i64,.none,.sret⟩],returns := [],callConv := some .systemV}
  blocks := [{id := 0,params := [(7,.i64)],body := [],term := .ret []}] }
private def frame : Clif.Frame := {
  func := function,regs := fun x => if x = 7 then some ⟨.i64,100⟩ else none,
  slots := [],body := [],term := .ret [] }
private def Observed : Prop := (Stock.lower function).toOption.map (fun result =>
  decide (aliasNum result.final.alias 192 = 192) &&
  decide (result.ctx.valueReg? 7 = some (.vreg 192 .int)) &&
  result.blockScans.toList.any (fun event => event.block == 0 &&
    decide (event.output.code = #[.rets [(.vreg 192 .int,.x 8)]]))) = some true
section Kernel
attribute [local semireducible] Isle.Aarch64.program Stock.runTerm
private theorem observed : Observed := by unfold Observed; decide +kernel
end Kernel
private theorem scope : LowerScope function := lowerScope_of (by decide +kernel)
private theorem dominated : Dominated function := by
  constructor
  · change ([7] : List Nat).Nodup; decide +kernel
  · intro ctx ranges st build bi b found
    cases bi with
    | zero =>
      simp [function] at found
      subst b
      constructor
      · intro j stm statement; simp at statement
      · intro x member
        change x ∈ [7] at member
        have equal := List.mem_singleton.mp member
        subst x
        simp [availOf,function,defsBefore,defsFrom]
    | succ bi => simp [function] at found
  · intro ctx ranges st build tl x available notLocal y member
    have bound := (inFix_fixOk (f := function) (ctx := ctx) (gn := id)).cand tl x available
    have length : function.blocks.length = 1 := rfl
    omega

/-- Complete original-scope lowering returns its implicit struct pointer in x8.
The original source returns no explicit values. Its real resolved return code
runs, but its pin list differs from the legacy `LowerTermOk` x0.. requirement. -/
theorem stock_sret_return_pin_contract_witness :
    ∃ (result : Result) (event : BlockScanEvent) (b : Clif.Block) (term : ScanRecord) (body : BlockScan),
      Stock.lower function = .ok result ∧ LowerScope function ∧ Dominated function ∧
      sigAbiOk function.sig = true ∧ abiTerm function (.ret []) = .ret [7] ∧
      event ∈ result.blockScans.toList ∧ SourceBodySplit function event b term body ∧
      result.ctx.valueReg? 7 = some (.vreg 192 .int) ∧ aliasNum result.final.alias 192 = 192 ∧
      event.output.code = #[.rets [(.vreg 192 .int,.x 8)]] ∧
      (([(.vreg 192 .int,.x 8)] : List (Reg × Reg)).map (·.2) ≠
        (List.range 1).map Reg.x) ∧
      Clif.step Clif.Env.empty {funcs := []} ⟨frame,[],Clif.Mem.empty⟩ = .done [] Clif.Mem.empty ∧
      ∀ ρ world,seqRun ispec (event.output.code.toList.map
        (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ world =
        some (.stop 0 (.rets [(.vreg 192 .int,.x 8)]) #[⟨192,.int,.use,.early,.fixed (.x 8)⟩]
          ρ world [] world .ret) := by
  have actual := observed
  unfold Observed at actual
  cases run : Stock.lower function with
  | error err => simp only [run,Except.toOption,Option.map_none] at actual; cases actual
  | ok result =>
    rw [run] at actual
    simp only [Except.toOption,Option.map_some,Option.some.injEq,Bool.and_eq_true,decide_eq_true_eq,
      List.any_eq_true,beq_iff_eq,and_assoc] at actual
    obtain ⟨alias,mapped,event,events,blockIndex,code⟩ := actual
    obtain ⟨b,term,body,split⟩ := stock_lower_body_scan_split run scope events
    refine ⟨result,event,b,term,body,rfl,scope,dominated,rfl,rfl,events,split,mapped,alias,code,
      (by decide +kernel),rfl,?_⟩
    intro ρ world
    rw [code]
    change seqRun ispec [(.rets [(.vreg 192 .int,.x 8)] : MInst).mapRegs
      (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))] ρ world = _
    simp only [List.map_cons,List.map_nil,MInst.mapRegs,resolve_vreg]
    change seqRun ispec [.rets [(.vreg (aliasNum result.final.alias 192) .int,.x 8)]] ρ world = _
    rw [alias]
    rfl
end Backend.Stock.Proof.SretReturnContractWitness
