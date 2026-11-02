import FV.Backend.Proof.StockCfgReturnBlockAt
import FV.Backend.Proof.StockConditionalReturnAt
import FV.Backend.Proof.StockConditionalTrapAt
import FV.Backend.Proof.StockCfgReturnTrapAt

namespace Backend.Stock.Proof.ConditionalValues
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- An actual nonentry scalar return block supplies a conditional return
continuation, using the existing return-core and ABI proofs. -/
theorem SuccessorReturn.of_return_block {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program} {vals : List Clif.Val} {cm : Clif.Mem} {label : Nat} {bc : Clif.BlockCall} {tl targetLabel : Nat} {b : Clif.Block} {xs : List Nat}
    (lookup : blockIdx? f bc.block = some tl) (found : f.block? bc.block = some b)
    (source : f.blocks[tl]? = some b)
    (tag : result.order.nodes[targetLabel]? = some (.original tl))
    (ret : b.term = .ret xs) (nonentry : tl ≠ 0) (forward : label < targetLabel) :
    Nonempty (SuccessorReturn f result label bc isem MR env cp vals cm) := by
  obtain ⟨spec⟩ := CfgReturn.stock_lower_return_block_spec run scope dominated abi family tag source ret
    refines driver stable env cp
  refine ⟨{
    index := tl
    targetLabel := targetLabel
    block := b
    event := spec.core.scan
    lookup := lookup
    found := found
    tag := tag
    member := spec.events
    atBlock := spec.atBlock
    forward := forward
    returns := ?_ }⟩
  intro fuel s ρ w func callers remaining atTerm defined returned held
  have finished := CfgReturnAt.return_block_returns_at run scope dominated abi family ret
    refines driver stable spec func callers remaining atTerm (by simpa only [spec.atBlock] using defined) returned held
  simpa only [spec.noPrelude nonentry] using finished

/-- The same actual return block supplies the first-trap continuation. -/
theorem SuccessorTrap.of_return_block {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program} {trapCode : Clif.TrapCode} {label : Nat} {bc : Clif.BlockCall} {tl targetLabel : Nat} {b : Clif.Block} {xs : List Nat}
    (lookup : blockIdx? f bc.block = some tl) (found : f.block? bc.block = some b)
    (source : f.blocks[tl]? = some b)
    (tag : result.order.nodes[targetLabel]? = some (.original tl))
    (ret : b.term = .ret xs) (nonentry : tl ≠ 0) (forward : label < targetLabel) :
    Nonempty (SuccessorTrap f result label bc isem MR env cp trapCode) := by
  obtain ⟨spec⟩ := CfgReturn.stock_lower_return_block_spec run scope dominated abi family tag source ret
    refines driver stable env cp
  refine ⟨{
    index := tl
    targetLabel := targetLabel
    block := b
    event := spec.core.scan
    lookup := lookup
    found := found
    tag := tag
    member := spec.events
    atBlock := spec.atBlock
    forward := forward
    traps := ?_ }⟩
  intro fuel s ρ w func callers remaining atTerm defined returned held
  have finished := CfgReturnAt.return_block_traps_at run scope dominated family ret
    refines driver stable spec callers remaining atTerm returned held
  simpa only [spec.noPrelude nonentry] using finished


end Backend.Stock.Proof.ConditionalValues
