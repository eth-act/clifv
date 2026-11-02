import FV.Backend.Proof.StockScalarDomainAt

/-! The scalar production domain stated over one emitted code. Both the legacy domain (for
the actual lowered code) and the per-successor domain (for the actual split code) give it,
so a consumer of `CodeDomain` serves routes that publish either code. -/

namespace Backend.Stock.Scalar
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false

/-- `Domain` over the emitted code `vc` instead of the actual Stock lowering. -/
structure CodeDomain (f : Clif.Function) (vc : VCode) : Prop where
  scope : LowerScope f
  dominated : Dominated f
  abi : sigAbiOk f.sig = true
  ordinary : (sigRets f.sig).any (·.purpose == .sret) = false
  returns : ∀ {args : List Clif.Val} {cm : Clif.Mem} {fr : Clif.Frame}
    (entered : SourceEntry f args fr)
    {env : Clif.Env} {cp : Clif.Program} {fuel : Nat} {vals : List Clif.Val} {mem : Clif.Mem}
    (returned : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .returned vals mem)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms isem) {MR : MemRelT} (stable : MRStable F MR)
    {w : Arm.ArmState} (memory : MR fr.slots cm w)
    (arguments : ArgsAtEntry F f.sig args w),
    ∃ ρ,RunOkABI f vc isem MR fr.slots ⟨0,0,ρ,w⟩ (.returned vals mem)
  traps : ∀ {args : List Clif.Val} {cm : Clif.Mem} {fr : Clif.Frame}
    (entered : SourceEntry f args fr)
    {env : Clif.Env} {cp : Clif.Program} {fuel : Nat} {code : Clif.TrapCode}
    (trapped : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .trapped code)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms isem) {MR : MemRelT} (stable : MRStable F MR)
    {w : Arm.ArmState} (memory : MR fr.slots cm w)
    (arguments : ArgsAtEntry F f.sig args w),
    ∃ ρ,VTrapFrom vc isem ⟨0,0,ρ,w⟩ code

/-- The legacy domain covers the actual lowered code. -/
theorem Domain.code {f : Clif.Function} (domain : Domain f) {result : Stock.Result}
    (run : Stock.lower f = .ok result) : CodeDomain f result.code :=
  ⟨domain.scope,domain.dominated,domain.abi,domain.ordinary,
    fun {_ _ _} entered {_ _ _ _ _} returned {_ _} refines driver {_ _} memorySem {_} stable {_} memory arguments =>
      domain.returns run entered returned refines driver memorySem stable memory arguments,
    fun {_ _ _} entered {_ _ _ _} trapped {_ _} refines driver {_ _} memorySem {_} stable {_} memory arguments =>
      domain.traps run entered trapped refines driver memorySem stable memory arguments⟩

/-- The per-successor domain covers the actual split code. -/
theorem DomainAt.code {f : Clif.Function} (domain : DomainAt f) {result : Stock.Result}
    (run : Stock.lower f = .ok result) {split : EdgeVCode}
    (splitRun : splitEdgesChecked result.code result.edgeArgs = .ok split) : CodeDomain f split.code :=
  ⟨domain.scope,domain.dominated,domain.abi,domain.ordinary,
    fun {_ _ _} entered {_ _ _ _ _} returned {_ _} refines driver {_ _} memorySem {_} stable {_} memory arguments =>
      domain.split_returns run splitRun entered returned refines driver memorySem stable memory arguments,
    fun {_ _ _} entered {_ _ _ _} trapped {_ _} refines driver {_ _} memorySem {_} stable {_} memory arguments =>
      domain.split_traps run splitRun entered trapped refines driver memorySem stable memory arguments⟩

end Backend.Stock.Scalar
