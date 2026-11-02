import FV.Backend.Proof.StockScalarContract
import FV.Backend.Proof.EdgeSplitSound

/-! The per-successor form of the scalar production domain. Its observations use the actual
code together with its actual per-successor vectors (`result.edgeArgs`). After a successful
edge split, they are the legacy observations of the split code. -/

namespace Backend.Stock.Scalar
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false

/-- `Domain` over the actual per-successor vectors of the lowered code. -/
structure DomainAt (f : Clif.Function) : Prop where
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
    {w : Arm.ArmState} (memory : MR fr.slots cm w)
    (arguments : ArgsAtEntry F f.sig args w),
    ∃ ρ,RunOkABIAt f result.code result.edgeArgs isem MR fr.slots ⟨0,0,ρ,w⟩ (.returned vals mem)
  traps : ∀ {result : Stock.Result} (run : Stock.lower f = .ok result)
    {args : List Clif.Val} {cm : Clif.Mem} {fr : Clif.Frame}
    (entered : SourceEntry f args fr)
    {env : Clif.Env} {cp : Clif.Program} {fuel : Nat} {code : Clif.TrapCode}
    (trapped : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .trapped code)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms isem) {MR : MemRelT} (stable : MRStable F MR)
    {w : Arm.ArmState} (memory : MR fr.slots cm w)
    (arguments : ArgsAtEntry F f.sig args w),
    ∃ ρ,PerEdgePrep.VTrapFromAt result.code result.edgeArgs isem ⟨0,0,ρ,w⟩ code

/-- Returns of the per-successor domain are legacy returns of the split code. -/
theorem DomainAt.split_returns {f : Clif.Function} (domain : DomainAt f)
    {result : Stock.Result} (run : Stock.lower f = .ok result) {split : EdgeVCode}
    (splitRun : splitEdgesChecked result.code result.edgeArgs = .ok split)
    {args : List Clif.Val} {cm : Clif.Mem} {fr : Clif.Frame}
    (entered : SourceEntry f args fr)
    {env : Clif.Env} {cp : Clif.Program} {fuel : Nat} {vals : List Clif.Val} {mem : Clif.Mem}
    (returned : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .returned vals mem)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms isem) {MR : MemRelT} (stable : MRStable F MR)
    {w : Arm.ArmState} (memory : MR fr.slots cm w)
    (arguments : ArgsAtEntry F f.sig args w) :
    ∃ ρ,RunOkABI f split.code isem MR fr.slots ⟨0,0,ρ,w⟩ (.returned vals mem) := by
  obtain ⟨ρ,source⟩ := domain.returns run entered returned refines driver memorySem stable memory arguments
  exact ⟨ρ,RunOkABIAt.split driver.toDriverSemG splitRun source⟩

/-- Traps of the per-successor domain are legacy traps of the split code. -/
theorem DomainAt.split_traps {f : Clif.Function} (domain : DomainAt f)
    {result : Stock.Result} (run : Stock.lower f = .ok result) {split : EdgeVCode}
    (splitRun : splitEdgesChecked result.code result.edgeArgs = .ok split)
    {args : List Clif.Val} {cm : Clif.Mem} {fr : Clif.Frame}
    (entered : SourceEntry f args fr)
    {env : Clif.Env} {cp : Clif.Program} {fuel : Nat} {code : Clif.TrapCode}
    (trapped : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .trapped code)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms isem) {MR : MemRelT} (stable : MRStable F MR)
    {w : Arm.ArmState} (memory : MR fr.slots cm w)
    (arguments : ArgsAtEntry F f.sig args w) :
    ∃ ρ,VTrapFrom split.code isem ⟨0,0,ρ,w⟩ code := by
  obtain ⟨ρ,source⟩ := domain.traps run entered trapped refines driver memorySem stable memory arguments
  exact ⟨ρ,RunOkABIAt.split (f := f) (MR := MR) (slots := fr.slots) (o := .trapped code)
    driver.toDriverSemG splitRun source⟩

end Backend.Stock.Scalar
