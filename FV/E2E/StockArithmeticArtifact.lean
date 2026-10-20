import FV.E2E.StockArithmeticSemantics
import FV.E2E.Main
import FV.Backend.Proof.StockArithmeticNoTrap

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false

/-- Actual Stock data through the existing checked preparation/allocation and
physical emission stages. The old CompiledProduction contract is retained. -/
structure CompiledStockArithmetic (f : Clif.Function) (k : Nat) (result : Stock.Result)
    (vcp : VCode) (rf : RFunc) (af : AFunc) (fa : FnAsm) (fb : FnBin) : Prop where
  lower : Stock.lower f = .ok result
  prepare : Backend.prepare result.code = .ok vcp
  prepOk : prepCheck result.code vcp = true
  check : checkAlloc vcp rf = .ok ()
  alloc : lowerRFunc vcp rf = .ok af
  emit : emitFunc k af = .ok fa
  layout : fa.layout = .ok fb

/-- Direct correctness of the actual Stock artifact for ordinary arithmetic
functions, on the existing production source-entry and machine-entry domain.
All outcomes are covered: arithmetic has no source traps, and stuck/outOfFuel
retain the original refinement convention. -/
theorem backend_correct_stock_arithmetic {f : Clif.Function} {result : Stock.Result}
    {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin} {k : Nat}
    (compiled : CompiledStockArithmetic f k result vcp rf af fa fb)
    (scope : LowerScope f) (dominated : Dominated f) (abi : sigAbiOk f.sig = true)
    {b : Clif.Block} (blocks : f.blocks = [b])
    (family : ∀ stm ∈ b.body, ∃ subtract : Bool, ∃ ty x y,
      stm.inst = .binary (if subtract then .isub else .iadd) ty x y)
    {xs : List Nat} (ret : b.term = .ret xs)
    (ordinary : (sigRets f.sig).any (·.purpose == .sret) = false)
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
    {env : Clif.Env} {cp : Clif.Program} {syms : String → Option Nat}
    (symbols : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (memory : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase
      (RAFrame.compute vcp rf).size af s,syms,af.slotBase,(RAFrame.compute vcp rf).intBase⟩
        f cs.frame.slots cs.mem w)
    (arguments : ArgsAtEntry (frameW K (RAFrame.compute vcp rf).intBase
      (RAFrame.compute vcp rf).size af s) f.sig args w) (fuel : Nat) :
    ArmRefines fb base ra (ArmStepX X H fa) s (Clif.runLoop env cp fuel cs) := by
  let Γ : Rel := ⟨frameW K (RAFrame.compute vcp rf).intBase
    (RAFrame.compute vcp rf).size af s,syms,af.slotBase,(RAFrame.compute vcp rf).intBase⟩
  cases outcome : Clif.runLoop env cp fuel cs with
  | returned vals cm =>
    obtain ⟨n,us,outs,world,cm0,finished,pins,arity,values,registers,memEq,mem,freed⟩ :=
      backend_correct_stock_arithmetic_return compiled.lower scope dominated abi blocks family ret
        compiled.prepOk compiled.check compiled.alloc compiled.emit compiled.layout covered callees tries tls
        activation stack bodyEntry entry outcome symbols (mrStable_holds Γ f) memory arguments
    have hmem : MemRel (Γ.F) syms cm world := by
      rw [freed]
      exact memRel_leave (memRel_free mem.1 _)
    refine ⟨n,finished,?_,memAgree_of hmem memEq⟩
    intro j v found
    have bound : j < vals.length := (List.getElem?_eq_some_iff.mp found).1
    have outputBound : j < outs.length := by have := values.1; omega
    have pinBound : j < us.length := by omega
    have atOutput : outs[j]? = some outs[j] := List.getElem?_eq_getElem outputBound
    have physical := registers j us[j].1 us[j].2 outs[j]
      (List.getElem?_eq_getElem pinBound) atOutput
    have locations := pins.ordinary ordinary
    have atPin := congrArg (fun ps => ps[j]?) locations
    simp only [List.getElem?_map,List.getElem?_range pinBound,
      List.getElem?_eq_getElem pinBound,Option.map_some] at atPin
    have pin : us[j].2 = Reg.x j := Option.some.inj atPin
    rw [pin,regVal_x] at physical
    show VHolds v (ofX (xreg j (runX (ArmStepX X H fa) n s)))
    rw [physical]
    exact values.2 j v outs[j] found atOutput
  | trapped code =>
    obtain ⟨b',found,body,terminal,_,_⟩ := entry.entry
    have same : b' = b := by
      have equal : some b = some b' := by
        simpa only [Clif.Function.entry?,blocks,List.head?_cons] using found
      exact Option.some.inj equal.symm
    subst b'
    exact False.elim (ArithmeticBody.arithmetic_source_notrap fuel cs entry.callers
      (fun stm member => family stm (by rwa [body] at member)) (terminal.trans ret) code outcome)
  | stuck message => trivial
  | outOfFuel => trivial

end E2E
