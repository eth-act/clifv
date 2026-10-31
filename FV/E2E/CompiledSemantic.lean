import FV.E2E.CompiledProduction
import FV.E2E.StockArithmeticWorldX
import FV.E2E.StockMixedWorldX
import FV.E2E.StockLogicalWorldX
import FV.E2E.StockScalarWorldX
import FV.E2E.StockMemoryWorldX
import FV.E2E.StockMemoryCfgWorldX

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Additive artifact contract for actual Stock semantics. Legacy production
contracts and their lowerCheck consequences retain their original meaning. -/
inductive CompiledSemantic (f : Clif.Function) (k : Nat) (vc vcp : VCode)
    (rf : RFunc) (af : AFunc) (fa : FnAsm) (fb : FnBin) : Prop where
  | compatible : CompiledProduction f k vc vcp rf af fa fb →
      CompiledSemantic f k vc vcp rf af fa fb
  | arithmetic {cleanup : Bool} {result : Stock.Result} :
      Stock.Arithmetic.Domain f → result.code = vc →
      CompiledStockArithmeticStage f cleanup k result vcp rf af fa fb →
      CompiledSemantic f k vc vcp rf af fa fb
  | mixed {cleanup : Bool} {result : Stock.Result} :
      Stock.Mixed.Domain f → result.code = vc →
      CompiledStockArithmeticStage f cleanup k result vcp rf af fa fb →
      CompiledSemantic f k vc vcp rf af fa fb
  | logical {cleanup : Bool} {result : Stock.Result} :
      Stock.Logical.Domain f → result.code = vc →
      CompiledStockArithmeticStage f cleanup k result vcp rf af fa fb →
      CompiledSemantic f k vc vcp rf af fa fb

  | scalar {cleanup : Bool} {result : Stock.Result} :
      Stock.Scalar.Domain f → result.code = vc →
      CompiledStockArithmeticStage f cleanup k result vcp rf af fa fb →
      CompiledSemantic f k vc vcp rf af fa fb

  | memory {cleanup : Bool} {result : Stock.Result} :
      Stock.Memory.Domain f → result.code = vc →
      CompiledStockArithmeticStage f cleanup k result vcp rf af fa fb →
      CompiledSemantic f k vc vcp rf af fa fb

  | memoryCfg {cleanup : Bool} {result : Stock.Result} :
      Stock.MemoryCfg.TwoBlockClass f → result.code = vc → Stock.MemoryCfg.effectsOnly vc = true →
      CompiledStockArithmeticStage f cleanup k result vcp rf af fa fb →
      CompiledSemantic f k vc vcp rf af fa fb

namespace CompiledSemantic
variable {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
  {af : AFunc} {fa : FnAsm} {fb : FnBin}

/-- Executable checker facts construct the semantic artifact. This does not
assert the old lowerCheck verdict for a raw Stock artifact. -/
theorem of_checks {cleanup : Bool} (lower : Stock.Arithmetic.check f vc = true)
    (prepared : Backend.prepare (Stock.Arithmetic.stage cleanup vc) = .ok vcp)
    (prepOk : prepCheck (Stock.Arithmetic.stage cleanup vc) vcp = true)
    (check : Backend.checkAlloc vcp rf = .ok ()) (alloc : lowerRFunc vcp rf = .ok af)
    (emit : emitFunc k af = .ok fa) (layout : fa.layout = .ok fb) :
    CompiledSemantic f k vc vcp rf af fa fb := by
  rcases Stock.Arithmetic.check_sound lower with legacy | ⟨result,domain,run,equal,_⟩
  · apply CompiledSemantic.compatible
    cases cleanup with
    | false =>
      exact .stock ⟨⟨legacy,prepared,prepOk,allocChecked_of_checkAlloc check,alloc,emit,layout⟩,check⟩
    | true =>
      exact .stockCleanup ⟨⟨legacy,prepared,prepOk,allocChecked_of_checkAlloc check,alloc,emit,layout⟩,check⟩
  · exact .arithmetic domain equal ⟨run,by rwa [equal],by rwa [equal],check,alloc,emit,layout⟩

theorem check (hc : CompiledSemantic f k vc vcp rf af fa fb) : Backend.checkAlloc vcp rf = .ok () := by
  cases hc with
  | compatible h => exact h.check
  | arithmetic _ _ h => exact h.check
  | mixed _ _ h => exact h.check

  | logical _ _ h => exact h.check

  | scalar _ _ h => exact h.check
  | memory _ _ h => exact h.check
  | memoryCfg _ _ _ h => exact h.check

theorem alloc (hc : CompiledSemantic f k vc vcp rf af fa fb) : lowerRFunc vcp rf = .ok af := by
  cases hc with
  | compatible h => exact h.alloc
  | arithmetic _ _ h => exact h.alloc
  | mixed _ _ h => exact h.alloc

  | logical _ _ h => exact h.alloc

  | scalar _ _ h => exact h.alloc
  | memory _ _ h => exact h.alloc
  | memoryCfg _ _ _ h => exact h.alloc

theorem emit (hc : CompiledSemantic f k vc vcp rf af fa fb) : emitFunc k af = .ok fa := by
  cases hc with
  | compatible h => exact h.emit
  | arithmetic _ _ h => exact h.emit
  | mixed _ _ h => exact h.emit

  | logical _ _ h => exact h.emit

  | scalar _ _ h => exact h.emit
  | memory _ _ h => exact h.emit
  | memoryCfg _ _ _ h => exact h.emit

theorem layout (hc : CompiledSemantic f k vc vcp rf af fa fb) : fa.layout = .ok fb := by
  cases hc with
  | compatible h => exact h.layout
  | arithmetic _ _ h => exact h.layout
  | mixed _ _ h => exact h.layout

  | logical _ _ h => exact h.layout

  | scalar _ _ h => exact h.layout
  | memory _ _ h => exact h.layout
  | memoryCfg _ _ _ h => exact h.layout

end CompiledSemantic

/-- Dispatch the linked per-state consumer using the checked artifact's actual
semantic provenance. All original activation and source conditions are kept. -/
theorem backend_correct_worldX_semantic {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledSemantic f k vc vcp rf af fa fb)
    {X : ExtSem} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    (∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        us.map (·.2) = (List.range us.length).map Reg.x ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧ vc.RetsSite us ∧
        ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
          ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (ArmStepX X H fa) n s) ∧
            PostTrace fa af base (ArmStepX X H fa) s n ∧
            ∀ i < n, actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
              (runX (ArmStepX X H fa) i s)) ∧
    (∀ c', Clif.runLoop env p fuel cs = .trapped c' →
      ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
        ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
        ∃ n, TrapAt fb base c' (runX (ArmStepX X H fa) n s) ∧
          (∀ i < n, actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
            (runX (ArmStepX X H fa) i s)) ∧
          ∀ m, Arm.r .ERR (runX (ArmStepX X H fa) (n + m + 1) s) ≠ .None) := by
  cases hc with
  | compatible h =>
    exact backend_correct_worldX_production hsub h hcov hX hXI hsym hslot hcs hrel hargs htr fuel
  | arithmetic domain equal h =>
    subst vc
    exact backend_correct_worldX_stock_arithmetic domain h hcov hsym hslot hcs hrel hargs fuel
  | mixed domain equal h =>
    subst vc
    exact backend_correct_worldX_stock_mixed domain h hcov hsym hslot hcs hrel hargs fuel

  | logical domain equal h =>
    subst vc
    exact backend_correct_worldX_stock_logical domain h hcov hsym hslot hcs hrel hargs fuel

  | scalar domain equal h =>
    subst vc
    exact backend_correct_worldX_stock_scalar domain h hcov hsym hslot hcs hrel hargs fuel

  | memory domain equal h =>
    subst vc
    exact backend_correct_worldX_stock_memory domain h hcov hsym hslot hcs hrel hargs fuel

  | memoryCfg family equal effects h =>
    subst vc
    exact backend_correct_worldX_stock_memory_cfg family effects h hcov hsym hslot hcs hrel hargs fuel

end E2E
