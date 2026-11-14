import FV.Backend.StockMemoryCheck

/-! The emitted instructions of the sinking load/extension class. Its atomic source
(rule 810) emits one acquiring load, which the plain memory whitelist `effectsOnly`
does not admit. -/
namespace Backend.Stock.Memory
set_option autoImplicit false

/-- Sinking-class emitted instructions: ABI copies, loads, acquiring loads and returns. -/
def sinkEffectInstruction : MInst → Bool
  | .args .. | .load .. | .loadAcquire .. | .rets .. => true
  | _ => false

/-- Every emitted instruction of the actual code is a sinking-class instruction. -/
def sinkEffectsOnly (vc : VCode) : Bool :=
  vc.blocks.toList.all (fun b => b.insts.toList.all sinkEffectInstruction)

end Backend.Stock.Memory
