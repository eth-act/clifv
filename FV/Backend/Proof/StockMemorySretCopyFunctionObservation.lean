import FV.Backend.Proof.StockMemorySretCopyFunction
import FV.Backend.Proof.StockLinearCfgCompatibility

namespace Backend.Stock.Memory.SretCopy
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false

/-- Preserve the existing function observation after proving both actual machine edges. -/
theorem sret_copy_return_function {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) {entry middle target : Clif.Block}
    {first second : Clif.BlockCall} {xs : List Nat}
    (blocks : f.blocks = [entry,middle,target])
    (firstJump : entry.term = .jump first) (secondJump : middle.term = .jump second)
    (ret : target.term = .ret xs)
    (firstDestination : first.block = middle.id) (secondDestination : second.block = target.id)
    (entryMiddle : entry.id ≠ middle.id) (entryTarget : entry.id ≠ target.id)
    (middleTarget : middle.id ≠ target.id)
    (entryNops : ∀ stm ∈ entry.body,stm.inst = .nop)
    (targetNops : ∀ stm ∈ target.body,stm.inst = .nop)
    {i0 i8 j0 j8 base destination low high : Nat} {lf0 lf8 sf0 sf8 : Clif.MemFlags}
    (loadLow : middle.body[i0]? = some ⟨[low],.load .load .i64 lf0 base 0⟩)
    (loadHigh : middle.body[i8]? = some ⟨[high],.load .load .i64 lf8 base 8⟩)
    (storeLow : middle.body[j0]? = some ⟨[],.store .store .i64 sf0 low destination 0⟩)
    (storeHigh : middle.body[j8]? = some ⟨[],.store .store .i64 sf8 high destination 8⟩)
    (lowEarlier : i0 < j0) (highEarlier : i8 < j8)
    (shape : ∀ j stm,middle.body[j]? = some stm → j = i0 ∨ j = i8 ∨ j = j0 ∨ j = j8 ∨ stm.inst = .nop)
    (baseParameter : base ∈ entry.params.map (·.1))
    (destinationParameter : destination ∈ entry.params.map (·.1))
    (loadLowNotrap : lf0.trapCode = none) (loadHighNotrap : lf8.trapCode = none)
    (storeLowNotrap : sf0.trapCode = none) (storeHighNotrap : sf8.trapCode = none)
    {env : Clif.Env} {cp : Clif.Program} {args : List Clif.Val} {cm : Clif.Mem} {fr : Clif.Frame}
    (entered : SourceEntry f args fr)
    {fuel : Nat} {vals : List Clif.Val} {outMem : Clif.Mem}
    (returned : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .returned vals outMem)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms isem) {MR : MemRelT} (stable : MRStable F MR)
    (memoryOk : MemRelOk F sb syms f MR)
    {w0 : Arm.ArmState} (memory : MR fr.slots cm w0) (arguments : ArgsAtEntry F f.sig args w0) :
    ∃ ρ0,RunOkABI f result.code isem MR fr.slots ⟨0,0,ρ0,w0⟩ (.returned vals outMem) := by
  obtain ⟨ρ,executed⟩ := sret_copy_return_frame run scope dominated abi
    blocks firstJump secondJump ret firstDestination secondDestination entryMiddle entryTarget middleTarget
    entryNops targetNops loadLow loadHigh storeLow storeHigh lowEarlier highEarlier shape
    baseParameter destinationParameter loadLowNotrap loadHighNotrap storeLowNotrap storeHighNotrap
    entered returned refines driver memorySem stable memoryOk memory arguments
  exact ⟨ρ,RunOkABIAt.legacyCompatible
    (LinearCfg.legacy_compatible run scope blocks firstJump secondJump ret firstDestination secondDestination
      entryMiddle entryTarget middleTarget) executed⟩

end Backend.Stock.Memory.SretCopy
