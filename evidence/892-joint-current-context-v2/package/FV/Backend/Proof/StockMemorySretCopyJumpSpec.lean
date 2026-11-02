import FV.Clif.MemTrap
import FV.Backend.Proof.StockMemoryOrdinaryJumpSpec
import FV.Backend.Proof.StockMemorySretCopyBody

namespace Backend.Stock.Memory.SretCopy
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Original copy syntax supplies its actual memory-capable jump contract. -/
theorem captured_sret_copy_jump_spec {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {label bi : Nat} {b : Clif.Block} {bc : Clif.BlockCall}
    (tag : result.order.nodes[label]? = some (.original bi)) (block : f.blocks[bi]? = some b)
    {i0 i8 j0 j8 base destination low high : Nat} {lf0 lf8 sf0 sf8 : Clif.MemFlags}
    (loadLow : b.body[i0]? = some ⟨[low],.load .load .i64 lf0 base 0⟩)
    (loadHigh : b.body[i8]? = some ⟨[high],.load .load .i64 lf8 base 8⟩)
    (storeLow : b.body[j0]? = some ⟨[],.store .store .i64 sf0 low destination 0⟩)
    (storeHigh : b.body[j8]? = some ⟨[],.store .store .i64 sf8 high destination 8⟩)
    (lowEarlier : i0 < j0) (highEarlier : i8 < j8)
    (shape : ∀ j stm,b.body[j]? = some stm → j = i0 ∨ j = i8 ∨ j = j0 ∨ j = j8 ∨ stm.inst = .nop)
    {pi : Nat} {pb : Clif.Block} (parameterBlock : f.blocks[pi]? = some pb)
    (baseParameter : base ∈ pb.params.map (·.1))
    (destinationParameter : destination ∈ pb.params.map (·.1))
    (jump : b.term = .jump bc)
    (loadLowNotrap : lf0.trapCode = none) (loadHighNotrap : lf8.trapCode = none)
    (storeLowNotrap : sf0.trapCode = none) (storeHighNotrap : sf8.trapCode = none)
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat} {isem : Backend.Proof.Sem}
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    (memorySem : MemRefines F sb syms isem) (memoryOk : MemRelOk F sb syms f MR)
    (env : Clif.Env) (cp : Clif.Program) :
    Nonempty (Control.JumpBodySpec f result b label bi bc isem MR env cp) := by
  have family : ∀ stm ∈ b.body,OrdinaryBody.OrdinaryInst stm.inst := by
    intro stm member
    obtain ⟨j,found⟩ := List.mem_iff_getElem?.mp member
    rcases shape j stm found with selected | selected | selected | selected | nop
    · subst j
      have same := Option.some.inj (found.symm.trans loadLow)
      subst stm
      simp [OrdinaryBody.OrdinaryInst]
    · subst j
      have same := Option.some.inj (found.symm.trans loadHigh)
      subst stm
      simp [OrdinaryBody.OrdinaryInst]
    · subst j
      have same := Option.some.inj (found.symm.trans storeLow)
      subst stm
      simp [OrdinaryBody.OrdinaryInst]
    · subst j
      have same := Option.some.inj (found.symm.trans storeHigh)
      subst stm
      simp [OrdinaryBody.OrdinaryInst]
    · simp [OrdinaryBody.OrdinaryInst,nop]
  have notrap : ∀ stm ∈ b.body,∀ fr cm code,instOutcome env cp fr cm stm.inst ≠ .trap code := by
    intro stm member fr cm code
    obtain ⟨j,found⟩ := List.mem_iff_getElem?.mp member
    rcases shape j stm found with selected | selected | selected | selected | nop
    · subst j
      have same := Option.some.inj (found.symm.trans loadLow)
      subst stm
      change Clif.evalInst fr cm (.load .load .i64 lf0 base 0) ≠ .trap code
      exact Clif.evalInst_notrap rfl loadLowNotrap code
    · subst j
      have same := Option.some.inj (found.symm.trans loadHigh)
      subst stm
      change Clif.evalInst fr cm (.load .load .i64 lf8 base 8) ≠ .trap code
      exact Clif.evalInst_notrap rfl loadHighNotrap code
    · subst j
      have same := Option.some.inj (found.symm.trans storeLow)
      subst stm
      change Clif.evalInst fr cm (.store .store .i64 sf0 low destination 0) ≠ .trap code
      exact Clif.evalInst_notrap rfl storeLowNotrap code
    · subst j
      have same := Option.some.inj (found.symm.trans storeHigh)
      subst stm
      change Clif.evalInst fr cm (.store .store .i64 sf8 high destination 8) ≠ .trap code
      exact Clif.evalInst_notrap rfl storeHighNotrap code
    · rw [nop]
      intro impossible
      cases impossible
  exact Control.stock_lower_ordinary_notrap_jump_body_spec run scope dominated tag block family jump
    driver env cp notrap (fun event events found => captured_sret_copy_body run scope dominated events found
      loadLow loadHigh storeLow storeHigh lowEarlier highEarlier shape parameterBlock baseParameter destinationParameter
      stable memorySem memoryOk (env := env) (cp := cp))

end Backend.Stock.Memory.SretCopy
