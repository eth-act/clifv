import FV.Backend.Proof.StockConditionalReturnAt
import FV.Backend.Proof.StockConditionalTrapAt
import FV.Backend.Proof.StockForwardTrap

namespace Backend.Stock.Proof.ConditionalValues
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.ForwardSource
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- A conditional successor can continue through arbitrarily many ranked jump/return blocks. -/
theorem SuccessorReturn.of_ranked_tail {f : Clif.Function} {result : Result} {rank : Nat → Nat}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) (ranked : Ranked f rank) (terms : NonentryJumpReturnBlocks f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program} {vals : List Clif.Val} {cm : Clif.Mem}
    {label : Nat} {bc : Clif.BlockCall} {tl targetLabel : Nat} {b : Clif.Block}
    (lookup : blockIdx? f bc.block = some tl) (found : f.block? bc.block = some b)
    (source : f.blocks[tl]? = some b)
    (tag : result.order.nodes[targetLabel]? = some (.original tl))
    (nonentry : tl ≠ 0) (forward : label < targetLabel) :
    Nonempty (SuccessorReturn f result label bc isem MR env cp vals cm) := by
  obtain ⟨event,member,atBlock,returns⟩ := nonentry_returns_of_termsAt run scope dominated abi ranked terms family
    refines driver stable env cp tag source nonentry
  refine ⟨{
    index := tl
    targetLabel := targetLabel
    block := b
    event := event
    lookup := lookup
    found := found
    tag := tag
    member := member
    atBlock := atBlock
    forward := forward
    returns := ?_ }⟩
  intro fuel s ρ w func callers remaining atTerm defined terminal held
  exact returns fuel s vals cm ρ w func callers remaining atTerm defined terminal held

/-- A conditional successor can continue through arbitrarily many ranked jump/return blocks. -/
theorem SuccessorTrap.of_ranked_tail {f : Clif.Function} {result : Result} {rank : Nat → Nat}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) (ranked : Ranked f rank) (terms : NonentryJumpReturnBlocks f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program} {trapCode : Clif.TrapCode}
    {label : Nat} {bc : Clif.BlockCall} {tl targetLabel : Nat} {b : Clif.Block}
    (lookup : blockIdx? f bc.block = some tl) (found : f.block? bc.block = some b)
    (source : f.blocks[tl]? = some b)
    (tag : result.order.nodes[targetLabel]? = some (.original tl))
    (nonentry : tl ≠ 0) (forward : label < targetLabel) :
    Nonempty (SuccessorTrap f result label bc isem MR env cp trapCode) := by
  obtain ⟨event,member,atBlock,traps⟩ := nonentry_traps_of_termsAt run scope dominated abi ranked terms family
    refines driver stable env cp tag source nonentry
  refine ⟨{
    index := tl
    targetLabel := targetLabel
    block := b
    event := event
    lookup := lookup
    found := found
    tag := tag
    member := member
    atBlock := atBlock
    forward := forward
    traps := ?_ }⟩
  intro fuel s ρ w func callers remaining atTerm defined terminal held
  exact traps fuel s trapCode ρ w func callers remaining atTerm defined terminal held

end Backend.Stock.Proof.ConditionalValues
