module

public import FV.Backend.Proof.StockOriginalEntryPrelude
public import FV.Backend.Proof.StockCfgReturnBlock
public import FV.Backend.Proof.StockReturnScanShape

@[expose] public section

namespace Backend.Stock.Proof.ParameterCfg
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- Original entry frame fields, independent of the entry's terminator. -/
theorem entry_frame_parts {f : Clif.Function} {b : Clif.Block}
    (source : f.blocks[0]? = some b) {args : List Clif.Val} {fr : Clif.Frame}
    (entered : SourceEntry f args fr) : fr.func = f ∧ fr.body = b.body ∧ fr.term = b.term := by
  obtain ⟨entry,regs,found,types,paramTypes,set,frame⟩ := entered
  have actual : f.blocks[0]? = some entry := by
    simpa only [Clif.Function.entry?,List.head?_eq_getElem?] using found
  cases Option.some.inj (actual.symm.trans source)
  exact ⟨congrArg Clif.Frame.func frame,congrArg Clif.Frame.body frame,congrArg Clif.Frame.term frame⟩

/-- The actual mandatory return makes the generic entry prelude applicable. -/
theorem return_entry_prelude {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} {xs : List Nat} (ret : b.term = .ret xs) {isem : Backend.Proof.Sem} {MR : MemRelT}
    {env : Clif.Env} {cp : Clif.Program} (spec : CfgReturn.ReturnBlockSpec f result b 0 0 isem MR env cp)
    {args : List Clif.Val} {cm : Clif.Mem} {fr : Clif.Frame} (entered : SourceEntry f args fr)
    (driver : DriverSem isem) {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms isem) (stable : MRStable F MR)
    {w : Arm.ArmState} (memory : MR fr.slots cm w) (arguments : ArgsAtEntry F f.sig args w) :
    ∃ ρ' w',Star (VStepAt result.code result.edgeArgs isem)
      (.run ⟨0,0,entrySeed spec.core.scan.ctx fr,w⟩) (.run ⟨0,spec.preludeCode.size,ρ',w'⟩) ∧
      GuardedScanRel f result spec.core.scan.ctx spec.core.scan.block MR spec.core.scan.output.state
        (0,fr,cm) ρ' w' ∧
      ValuesHeld (fun _ => True) spec.core.scan.ctx fr (fun key => ρ' (aliasNum result.final.alias key)) ∧ SameWorld F w' w := by
  have block : f.blocks[0]? = some b := by simpa only [spec.atBlock] using spec.split.block
  obtain ⟨rs,ps,last,pins⟩ := stock_lower_return_scan_last run scope spec.events spec.split.block ret
  have nonempty : 0 < spec.core.code.size := by
    rw [CfgReturn.stock_return_core_code ret spec.coreRun]
    apply Nat.pos_of_ne_zero
    intro zero
    have empty := Array.eq_empty_of_size_eq_zero zero
    rw [empty] at last
    cases last
  let entry : Control.EntryCoreSpec f result b := {
    ranges := spec.ranges
    params := spec.params
    core := spec.core
    raw := spec.raw
    preludeCode := spec.preludeCode
    build := spec.build
    sizes := spec.sizes
    assembled := spec.assembled
    events := spec.events
    block := block
    rawCode := spec.rawCode
    placed := spec.placed
    nonempty := nonempty }
  exact Control.original_entry_prelude run scope dominated entry entered driver memorySem stable memory arguments

end Backend.Stock.Proof.ParameterCfg
