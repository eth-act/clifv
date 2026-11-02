import FV.Clif.MemTrap
import FV.Backend.Proof.StockMemoryContract
import FV.Backend.Proof.StockMemoryAccessTrap

/-! Draft: no kernel command ran for this module.
The old explicit-trap domain and its existing source conditions stay unchanged. -/
namespace Backend.Stock.Proof.MemoryFaults
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- An additive source contract separates explicit traps from access boundaries. -/
structure DomainWithAccessTraps (f : Clif.Function) : Prop where
  scope : LowerScope f
  dominated : Dominated f
  abi : sigAbiOk f.sig = true
  ordinary : (sigRets f.sig).any (·.purpose == .sret) = false
  returns : ∀ {result : Stock.Result} (run : Stock.lower f = .ok result)
    {args : List Clif.Val} {cm : Clif.Mem} {fr : Clif.Frame}
    (entered : SourceEntry f args fr)
    {env : Clif.Env} {cp : Clif.Program} {fuel : Nat} {vals : List Clif.Val} {mem : Clif.Mem}
    (returned : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .returned vals mem)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms isem) {MR : MemRelT} (stable : MRStable F MR)
    (memoryOk : MemRelOk F sb syms f MR)
    {w : Arm.ArmState} (memory : MR fr.slots cm w)
    (arguments : ArgsAtEntry F f.sig args w),
    ∃ ρ, RunOkABI f result.code isem MR fr.slots ⟨0,0,ρ,w⟩ (.returned vals mem)
  traps : ∀ {result : Stock.Result} (run : Stock.lower f = .ok result)
    {args : List Clif.Val} {cm : Clif.Mem} {fr : Clif.Frame}
    (entered : SourceEntry f args fr)
    {env : Clif.Env} {cp : Clif.Program} {fuel : Nat} {code : Clif.TrapCode}
    (trapped : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .trapped code)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms isem) {MR : MemRelT} (stable : MRStable F MR)
    (memoryOk : MemRelOk F sb syms f MR)
    {w : Arm.ArmState} (memory : MR fr.slots cm w)
    (arguments : ArgsAtEntry F f.sig args w),
    ∀ (Q : Nat → Nat → Prop),
      (∀ s a n,Reach env cp ⟨fr,[],cm⟩ s → Clif.MemTrapAt env cp s code a n → Q a n) →
      ∃ ρ,VTrapFrom result.code isem ⟨0,0,ρ,w⟩ code ∨
        VAccessTrapFrom sb result.code isem ⟨0,0,ρ,w⟩ code (sourceAddrPred Q)

/-- Retain every existing memory-domain theorem through the explicit-trap branch. -/
theorem domainWithAccessTraps_of_domain {f : Clif.Function} (old : Backend.Stock.Memory.Domain f) :
    DomainWithAccessTraps f := by
  refine ⟨old.scope,old.dominated,old.abi,old.ordinary,?_,?_⟩
  · exact old.returns
  · intro result run args cm fr entered env cp fuel code trapped F isem refines driver
      sb syms memorySem MR stable memoryOk w memory arguments Q allFaults
    obtain ⟨ρ,executed⟩ := old.traps run entered trapped refines driver memorySem stable
      memoryOk memory arguments
    exact ⟨ρ,.inl executed⟩

end Backend.Stock.Proof.MemoryFaults
