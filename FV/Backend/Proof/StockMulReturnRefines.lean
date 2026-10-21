import FV.Backend.Proof.StockMulBodyRefines
import FV.Backend.Proof.StockPureReturnRefines

namespace Backend.Stock.Proof.MulBody
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192

/-- Original ABI entry through an arbitrary mixed multiply body to Stock's
actual return. Reuses shared entry/placement/source/return simulation; all
selection, record bindings and guarded source steps are derived internally. -/
theorem actual_mul_entry_return_refines_frame {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) {b : Clif.Block} (blocks : f.blocks = [b])
    (family : ∀ stm ∈ b.body, Family stm.inst)
    {xs : List Nat} (ret : b.term = .ret xs)
    {args : List Clif.Val} {cm : Clif.Mem} {fr : Clif.Frame}
    (entered : SourceEntry f args fr)
    {env : Clif.Env} {cp : Clif.Program} {fuel : Nat} {vals : List Clif.Val} {mem : Clif.Mem}
    (returned : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .returned vals mem)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms isem) {MR : MemRelT} (stable : MRStable F MR)
    {w : Arm.ArmState} (memory : MR fr.slots cm w)
    (arguments : ArgsAtEntry F f.sig args w) :
    ∃ ρ, RunOkABI f result.code isem MR fr.slots ⟨0,0,ρ,w⟩ (.returned vals mem) := by
  exact PureBody.actual_pure_entry_return_refines_frame run scope dominated abi blocks
    (fun stm member => family_pure (family stm member)) ret entered returned refines driver memorySem stable
    (fun event events => actual_mul_body_refines run scope dominated blocks family events refines driver stable)
    memory arguments

end Backend.Stock.Proof.MulBody
