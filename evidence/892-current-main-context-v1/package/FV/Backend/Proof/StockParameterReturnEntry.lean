import FV.Backend.Proof.StockEdgeCode
import FV.Backend.Proof.StockParameterReturnPrelude
import FV.Backend.Proof.StockCfgReturnBlockAt
import FV.Backend.Proof.StockCfgReturnTrapAt
import FV.Backend.Proof.StockJumpEntryPrelude

namespace Backend.Stock.Proof.ParameterCfg
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

theorem parameter_return_entry_frame {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {entry : Clif.Block} {xs : List Nat} (source : f.blocks[0]? = some entry) (ret : entry.term = .ret xs)
    {env : Clif.Env} {cp : Clif.Program} {args : List Clif.Val} {cm : Clif.Mem} {fr : Clif.Frame}
    (entered : SourceEntry f args fr) {fuel : Nat} {vals : List Clif.Val} {outMem : Clif.Mem}
    (returned : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .returned vals outMem)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem) (driver : DriverSem isem)
    {sb : Nat} {syms : String → Option Nat} (memorySem : MemRefines F sb syms isem)
    {MR : MemRelT} (stable : MRStable F MR) {w0 : Arm.ArmState}
    (memory : MR fr.slots cm w0) (arguments : ArgsAtEntry F f.sig args w0) :
    ∃ ρ0,RunOkABIAt f result.code result.edgeArgs isem MR fr.slots ⟨0,0,ρ0,w0⟩ (.returned vals outMem) := by
  have tag := stock_blockOrder_entry (stock_lower_order run) scope.nonempty
  obtain ⟨spec⟩ := CfgReturn.stock_lower_return_block_spec run scope dominated abi family tag source ret refines driver stable env cp
  obtain ⟨func,remaining,atTerm⟩ := entry_frame_parts source entered
  obtain ⟨ρ,w,path,guarded,values,sameWorld⟩ := return_entry_prelude run scope dominated ret spec
    entered driver memorySem stable memory arguments
  have finished := CfgReturnAt.return_block_returns_at run scope dominated abi family ret refines driver stable spec
    func rfl remaining atTerm
    (by simpa only [spec.atBlock] using Control.source_defined_entry_frame dominated result.ctx entered) returned guarded
  exact ⟨entrySeed spec.core.scan.ctx fr,RunOkABIAt.prefix path finished⟩

theorem parameter_return_entry_trap_frame {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {entry : Clif.Block} {xs : List Nat} (source : f.blocks[0]? = some entry) (ret : entry.term = .ret xs)
    {env : Clif.Env} {cp : Clif.Program} {args : List Clif.Val} {cm : Clif.Mem} {fr : Clif.Frame}
    (entered : SourceEntry f args fr) {fuel : Nat} {code : Clif.TrapCode}
    (trapped : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .trapped code)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem) (driver : DriverSem isem)
    {sb : Nat} {syms : String → Option Nat} (memorySem : MemRefines F sb syms isem)
    {MR : MemRelT} (stable : MRStable F MR) {w0 : Arm.ArmState}
    (memory : MR fr.slots cm w0) (arguments : ArgsAtEntry F f.sig args w0) :
    ∃ ρ0,RunOkABIAt f result.code result.edgeArgs isem MR fr.slots ⟨0,0,ρ0,w0⟩ (.trapped code) := by
  have tag := stock_blockOrder_entry (stock_lower_order run) scope.nonempty
  obtain ⟨spec⟩ := CfgReturn.stock_lower_return_block_spec run scope dominated abi family tag source ret refines driver stable env cp
  obtain ⟨func,remaining,atTerm⟩ := entry_frame_parts source entered
  obtain ⟨ρ,w,path,guarded,values,sameWorld⟩ := return_entry_prelude run scope dominated ret spec
    entered driver memorySem stable memory arguments
  have finished := CfgReturnAt.return_block_traps_at run scope dominated family ret refines driver stable spec
    rfl remaining atTerm trapped guarded
  exact ⟨entrySeed spec.core.scan.ctx fr,RunOkABIAt.prefix path finished⟩
end Backend.Stock.Proof.ParameterCfg
