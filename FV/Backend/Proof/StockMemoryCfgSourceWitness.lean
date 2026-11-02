import FV.Backend.Proof.StockMemoryCfgClass
import FV.Backend.Proof.StockMemoryCapturedFixture

namespace Backend.Stock.MemoryCfg
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.Stock.Memory
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- Existing source proofs positively inhabit the new memory CFG class. -/
theorem captured_source_class : TwoBlockClass CapturedFixture.function := by
  refine ⟨CapturedFixture.scope,CapturedFixture.dominated,rfl,rfl,?_,?_⟩
  · intro loc member
    change loc ∈ [ArgLoc.reg (.x 0)] at member
    exact ⟨.x 0,List.mem_singleton.mp member⟩
  · exact ⟨CapturedFixture.function.blocks[0]!,CapturedFixture.function.blocks[1]!,0,2,
      LoadFixture.flags,rfl,rfl,rfl,rfl,rfl,by simp [CapturedFixture.function],rfl⟩

-- Executable acceptance regression; this command adds no proof axiom.
#guard Backend.Stock.MemoryCfg.sourceOk CapturedFixture.function

end Backend.Stock.MemoryCfg
