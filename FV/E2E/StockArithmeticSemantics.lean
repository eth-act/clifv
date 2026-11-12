import FV.Backend.Proof.StockArithmeticEntryRefines
import FV.Backend.Proof.StockPreparedSemantics
import FV.E2E.Statement
import FV.E2E.RegLevelCorrect
import FV.E2E.RegLevelDriverSem
import FV.Backend.Proof.MemRefines
import FV.Backend.Proof.RefinesCSem

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false

/-- The existing production entry contract supplies source bindings with its
original stack-slot addresses. No executable allocation premise is added. -/
theorem ClifEntry.stockSourceEntry {f : Clif.Function} {args : List Clif.Val} {cs : Clif.State}
    (entry : ClifEntry f args cs) : SourceEntry f args cs.frame := by
  obtain ⟨b,block,body,term,types,set⟩ := entry.entry
  refine ⟨b,cs.frame.regs,block,?_,types.symm,set,?_⟩
  · simpa only [Clif.AbiParam.tys] using entry.sig
  · have func := entry.func
    cases frame : cs.frame <;> simp_all

/-- Actual arithmetic lowering composes with actual validated preparation on
the existing source entry domain, including arbitrary related slot addresses. -/
theorem stock_arithmetic_prepared_return {f : Clif.Function} {result : Stock.Result}
    (lowered : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) {b : Clif.Block} (blocks : f.blocks = [b])
    (family : ∀ stm ∈ b.body, ∃ subtract : Bool, ∃ ty x y,
      stm.inst = .binary (if subtract then .isub else .iadd) ty x y)
    {xs : List Nat} (ret : b.term = .ret xs) {vcp : VCode}
    (prepared : prepCheck result.code vcp = true)
    {args : List Clif.Val} {cs : Clif.State} (entry : ClifEntry f args cs)
    {env : Clif.Env} {cp : Clif.Program} {fuel : Nat} {vals : List Clif.Val} {cm : Clif.Mem}
    (returned : Clif.runLoop env cp fuel cs = .returned vals cm)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms isem) {MR : MemRelT} (stable : MRStable F MR)
    {w : Arm.ArmState} (memory : MR cs.frame.slots cs.mem w)
    (arguments : ArgsAtEntry F f.sig args w) :
    ∃ ρ, RunOkABI f vcp isem MR cs.frame.slots ⟨0,0,ρ,w⟩ (.returned vals cm) := by
  have state : (⟨cs.frame,[],cs.mem⟩ : Clif.State) = cs := by
    have callers := entry.callers
    cases cs
    cases callers
    rfl
  obtain ⟨ρ,source⟩ := ArithmeticBody.actual_arithmetic_entry_return_refines_frame lowered scope dominated
    abi blocks family ret entry.stockSourceEntry (by rwa [state]) refines driver memorySem stable memory arguments
  exact ⟨ρ,source.prepared driver prepared⟩

/-- Direct composition with the universal-initial-file machine consumer.
The chosen virtual file stays internal; the legacy lowerCheck contract is not
used for the Stock output. The ABI-aware result retains implicit return pins. -/
theorem stock_arithmetic_machine_return {f : Clif.Function} {result : Stock.Result}
    (lowered : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) {b : Clif.Block} (blocks : f.blocks = [b])
    (family : ∀ stm ∈ b.body, ∃ subtract : Bool, ∃ ty x y,
      stm.inst = .binary (if subtract then .isub else .iadd) ty x y)
    {xs : List Nat} (ret : b.term = .ret xs) {vcp : VCode}
    (prepared : prepCheck result.code vcp = true)
    {af : AFunc} {fb : FnBin} {sem : Arm.ArmState → Backend.Proof.Sem}
    {F : Arm.ArmState → BitVec 64 → Prop} {K : Nat} {astep : Arm.ArmState → Arm.ArmState}
    (machine : RegLevelCorrect sem F K astep vcp af fb)
    {base ra : BitVec 64} {s w : Arm.ArmState} (activation : AbiEntry fb base ra s)
    (stack : StackAvail K af s) (bodyEntry : BodyEntry af s w)
    {args : List Clif.Val} {cs : Clif.State} (entry : ClifEntry f args cs)
    {env : Clif.Env} {cp : Clif.Program} {fuel : Nat} {vals : List Clif.Val} {cm : Clif.Mem}
    (returned : Clif.runLoop env cp fuel cs = .returned vals cm)
    (refines : Refines (F s) (sem s)) (driver : DriverSem (sem s))
    {sb : Nat} {syms : String → Option Nat} (memorySem : MemRefines (F s) sb syms (sem s))
    {MR : MemRelT} (stable : MRStable (F s) MR) (memory : MR cs.frame.slots cs.mem w)
    (arguments : ArgsAtEntry (F s) f.sig args w) :
    ∃ (n : Nat) (us : List (Reg × Reg)) (outs : List CV) (world : Arm.ArmState) (cm0 : Clif.Mem),
      ArmRet ra s (runX astep n s) ∧ ReturnABI f us ∧ us.length = outs.length ∧ PrefixHold vals outs ∧
      (∀ (j : Nat) (v p : Reg) (x : CV), us[j]? = some (v,p) → outs[j]? = some x → regVal (runX astep n s) p = x) ∧
      (∀ a, ¬ F s a → (runX astep n s).mem a = world.mem a) ∧
      MR cs.frame.slots cm0 world ∧ cm = (cm0.free (cs.frame.slots.map (·.2))).leave := by
  obtain ⟨ρ,us,outs,world,cm0,reached,pins,arity,values,mem,freed⟩ :=
    stock_arithmetic_prepared_return lowered scope dominated abi blocks family ret prepared entry
      returned refines driver memorySem stable memory arguments
  obtain ⟨n,finished,registers,memEq⟩ := (machine base ra s activation stack w bodyEntry ρ).1
    us outs world reached
  exact ⟨n,us,outs,world,cm0,finished,pins.abi,arity,values,registers,memEq,mem,freed⟩

/-- The actual checked allocator, physical lowering, emission and layout
instantiate the direct Stock consumer. No legacy lowering verdict or supplied
machine simulation is required. -/
theorem backend_correct_stock_arithmetic_return {f : Clif.Function} {result : Stock.Result}
    (lowered : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) {b : Clif.Block} (blocks : f.blocks = [b])
    (family : ∀ stm ∈ b.body, ∃ subtract : Bool, ∃ ty x y,
      stm.inst = .binary (if subtract then .isub else .iadd) ty x y)
    {xs : List Nat} (ret : b.term = .ret xs) {vcp : VCode}
    (prepared : prepCheck result.code vcp = true)
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin} {k : Nat}
    (checked : checkAlloc vcp rf = .ok ()) (allocated : lowerRFunc vcp rf = .ok af)
    (emitted : emitFunc k af = .ok fa) (layout : fa.layout = .ok fb)
    {X : ExtSem} {H : ArmHooks} {K : Nat}
    (covered : FormsCovered ⟨fa.k,af.slotBase⟩ vcp)
    (callees : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (tries : vcp.hasTryCall = true → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (tls : vcp.hasTls = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    {base ra : BitVec 64} {s w : Arm.ArmState} (activation : AbiEntry fb base ra s)
    (stack : StackAvail K af s) (bodyEntry : BodyEntry af s w)
    {args : List Clif.Val} {cs : Clif.State} (entry : ClifEntry f args cs)
    {env : Clif.Env} {cp : Clif.Program} {fuel : Nat} {vals : List Clif.Val} {cm : Clif.Mem}
    (returned : Clif.runLoop env cp fuel cs = .returned vals cm)
    {syms : String → Option Nat} (symbols : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    {MR : MemRelT}
    (stable : MRStable (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) MR)
    (memory : MR cs.frame.slots cs.mem w)
    (arguments : ArgsAtEntry (frameW K (RAFrame.compute vcp rf).intBase
      (RAFrame.compute vcp rf).size af s) f.sig args w) :
    ∃ (n : Nat) (us : List (Reg × Reg)) (outs : List CV) (world : Arm.ArmState) (cm0 : Clif.Mem),
      ArmRet ra s (runX (ArmStepX X H fa) n s) ∧ ReturnABI f us ∧ us.length = outs.length ∧
      PrefixHold vals outs ∧
      (∀ (j : Nat) (v p : Reg) (x : CV), us[j]? = some (v,p) → outs[j]? = some x →
        regVal (runX (ArmStepX X H fa) n s) p = x) ∧
      (∀ a, ¬ frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s a →
        (runX (ArmStepX X H fa) n s).mem a = world.mem a) ∧
      MR cs.frame.slots cm0 world ∧ cm = (cm0.free (cs.frame.slots.map (·.2))).leave := by
  let F := frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af
  have memSem : MemRefines (F s) af.slotBase syms (csem (F s) ⟨fa.k,af.slotBase⟩ X) :=
    memRefines_csem (F s) ⟨fa.k,af.slotBase⟩ X rfl symbols
  exact stock_arithmetic_machine_return lowered scope dominated abi blocks family ret prepared
    (regLevelCorrect_backend checked allocated emitted layout covered callees tries tls)
    activation stack bodyEntry entry returned
    (refines_csem (F s) ⟨fa.k,af.slotBase⟩ X) (driverSem_csem (F s) ⟨fa.k,af.slotBase⟩ X)
    memSem stable memory arguments

end E2E
