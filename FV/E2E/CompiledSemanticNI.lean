import FV.E2E.StockMemoryExtLoadNI
import FV.Backend.Proof.StockMemoryExtLoadCheck
import FV.E2E.StockMemoryIntegerNI
import FV.Backend.Proof.StockMemoryIntegerCheck
import FV.E2E.StockMemoryCfgNI
import FV.Backend.Proof.StockMemoryCfgClass
import FV.Backend.Proof.StockParameterCheck
import FV.Backend.Proof.StockConditionalRankedCheck
import FV.E2E.StockCfgNI
import FV.Backend.Proof.StockTwoBlockCheck
import FV.Backend.Proof.StockTwoBlockEntryCheck
import FV.Backend.Proof.StockLinearCfgCheck
import FV.Backend.Proof.StockConditionalCheck
import FV.Backend.Proof.StockForwardCheck
import FV.E2E.CompiledSemantic
import FV.E2E.StockArithmeticNI
import FV.E2E.StockMixedNI
import FV.E2E.StockLogicalNI
import FV.E2E.StockScalarNI
import FV.E2E.StockDivNI
import FV.Backend.SemanticNICheck
import FV.Backend.Proof.StockMemoryCheck
import FV.E2E.StockMemoryNI

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Fully paired semantic artifact. The executable checker derives the raw
Stock read boundary while all old production artifacts retain their contracts. -/
inductive CompiledSemanticNI (f : Clif.Function) (k : Nat) (vc vcp : VCode)
    (rf : RFunc) (af : AFunc) (fa : FnAsm) (fb : FnBin) : Prop where
  | compatible : CompiledProduction f k vc vcp rf af fa fb →
      CompiledSemanticNI f k vc vcp rf af fa fb
  | arithmetic {cleanup : Bool} {result : Stock.Result} :
      Stock.Arithmetic.Domain f → result.code = vc → ABIReadOnly.check f.sig vc = true →
      CompiledStockArithmeticStage f cleanup k result vcp rf af fa fb →
      CompiledSemanticNI f k vc vcp rf af fa fb
  | mixed {cleanup : Bool} {result : Stock.Result} :
      Stock.Mixed.Domain f → result.code = vc → ABIReadFlags.check f.sig vc = true →
      CompiledStockArithmeticStage f cleanup k result vcp rf af fa fb →
      CompiledSemanticNI f k vc vcp rf af fa fb
  | logical {cleanup : Bool} {result : Stock.Result} :
      Stock.Logical.Domain f → result.code = vc → ABIReadFlags.check f.sig vc = true →
      CompiledStockArithmeticStage f cleanup k result vcp rf af fa fb →
      CompiledSemanticNI f k vc vcp rf af fa fb

  | scalar {cleanup : Bool} {result : Stock.Result} :
      Stock.Scalar.Domain f → result.code = vc → ABIReadScalar.check f.sig vc = true →
      CompiledStockArithmeticStage f cleanup k result vcp rf af fa fb →
      CompiledSemanticNI f k vc vcp rf af fa fb
  | scalarDiv {cleanup : Bool} {result : Stock.Result} :
      Stock.Scalar.Domain f → result.code = vc → ABIReadDiv.check f.sig vc = true →
      CompiledStockArithmeticStage f cleanup k result vcp rf af fa fb →
      CompiledSemanticNI f k vc vcp rf af fa fb

  | cfg {cleanup : Bool} {result : Stock.Result} :
      Stock.Scalar.Domain f → result.code = vc → ABIReadCfg.check f.sig vc = true →
      CompiledStockArithmeticStage f cleanup k result vcp rf af fa fb →
      CompiledSemanticNI f k vc vcp rf af fa fb

  | memory {cleanup : Bool} {result : Stock.Result} :
      Stock.Memory.SingleClass f → result.code = vc → Stock.Memory.effectsOnly vc = true →
      CompiledStockArithmeticStage f cleanup k result vcp rf af fa fb →
      CompiledSemanticNI f k vc vcp rf af fa fb

  | memoryCfg {cleanup : Bool} {result : Stock.Result} :
      Stock.MemoryCfg.TwoBlockClass f → result.code = vc → Stock.MemoryCfg.effectsOnly vc = true →
      CompiledStockArithmeticStage f cleanup k result vcp rf af fa fb →
      CompiledSemanticNI f k vc vcp rf af fa fb

  | memoryUnsigned {width : Stock.Memory.IntegerRoots.Width} {cleanup : Bool} {result : Stock.Result} :
      Stock.Memory.IntegerRoots.SingleClass width f → result.code = vc → Stock.Memory.effectsOnly vc = true →
      CompiledStockArithmeticStage f cleanup k result vcp rf af fa fb →
      CompiledSemanticNI f k vc vcp rf af fa fb

  | memoryExtending {kind : Stock.Memory.ExtendedRoots.Kind} {ty : Clif.Ty}
      {cleanup : Bool} {result : Stock.Result} :
      Stock.Memory.ExtendedRoots.SingleClass kind ty f → result.code = vc → Stock.Memory.effectsOnly vc = true →
      CompiledStockArithmeticStage f cleanup k result vcp rf af fa fb →
      CompiledSemanticNI f k vc vcp rf af fa fb

namespace CompiledSemanticNI
variable {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
  {af : AFunc} {fa : FnAsm} {fb : FnBin}

/-- Forgetting paired execution retains the published semantic contract. -/
theorem toSemantic (hc : CompiledSemanticNI f k vc vcp rf af fa fb) :
    CompiledSemantic f k vc vcp rf af fa fb := by
  cases hc with
  | compatible h => exact .compatible h
  | arithmetic domain equal _ h => exact .arithmetic domain equal h
  | mixed domain equal _ h => exact .mixed domain equal h

  | logical domain equal _ h => exact .logical domain equal h

  | scalar domain equal _ h => exact .scalar domain equal h
  | scalarDiv domain equal _ h => exact .scalar domain equal h
  | cfg domain equal _ h => exact .scalar domain equal h
  | memory family equal _ h => exact .memory family.domain equal h
  | memoryCfg family equal effects h => exact .memoryCfg family equal effects h
  | @memoryUnsigned width cleanup result family equal effects h =>
    exact .memory (Stock.Memory.IntegerRoots.SingleClass.domain width family) equal h
  | @memoryExtending kind ty cleanup result family equal effects h =>
    exact .memory (Stock.Memory.ExtendedRoots.SingleClass.domain kind ty family) equal h

/-- All new semantic and paired premises come from executable checks and actual
pipeline observations, rather than new accepted-source assumptions. (`prepared`/`prepOk` are
about the routes' stage `Stock.Arithmetic.stageF`, formerly `Stock.Arithmetic.stage`: the routes
now run Cranelift's skip of unused instructions, `cleanupStage`.) -/
theorem of_checks {cleanup : Bool} (lower : SemanticNI.check f vc = true)
    (prepared : Backend.prepare (Stock.Arithmetic.stageF cleanup f vc) = .ok vcp)
    (prepOk : prepCheck (Stock.Arithmetic.stageF cleanup f vc) vcp = true)
    (check : Backend.checkAlloc vcp rf = .ok ()) (alloc : lowerRFunc vcp rf = .ok af)
    (emit : emitFunc k af = .ok fa) (layout : fa.layout = .ok fb) :
    CompiledSemanticNI f k vc vcp rf af fa fb := by
  have retained (legacy : lowerCheck f vc = true) : CompiledProduction f k vc vcp rf af fa fb := by
    cases cleanup with
    | false =>
      exact .stock ⟨⟨legacy,prepared,prepOk,allocChecked_of_checkAlloc check,alloc,emit,layout⟩,check⟩
    | true =>
      exact .stockCleanup ⟨⟨legacy,prepared,prepOk,allocChecked_of_checkAlloc check,alloc,emit,layout⟩,check⟩
  rcases Bool.eq_false_or_eq_true (lowerCheck f vc) with hl | hl
  · exact .compatible (retained hl)
  rw [Stock.Arithmetic.stageF_of_lowerCheck_false hl] at prepared prepOk
  simp only [SemanticNI.check,Bool.or_eq_true,Bool.and_eq_true] at lower
  rcases lower with legacy | ((((((((((((((⟨semantic,reads⟩ | ⟨semantic,reads⟩) | ⟨semantic,reads⟩) | ⟨semantic,reads⟩) | ⟨semantic,reads⟩) | ⟨semantic,reads⟩) | ⟨semantic,reads⟩) | ⟨semantic,reads⟩) | ⟨semantic,reads⟩) | ⟨semantic,reads⟩) | ⟨semantic,reads⟩) | memory) | memoryCfg) | memoryUnsigned) | memoryExtending)
  · exact .compatible (retained legacy)
  · rcases Stock.Arithmetic.check_sound semantic with legacy | ⟨result,domain,run,equal,_⟩
    · exact .compatible (retained legacy)
    · exact .arithmetic domain equal reads
        ⟨run,by rwa [equal],by rwa [equal],check,alloc,emit,layout⟩
  · obtain ⟨result,domain,run,equal,_⟩ := Stock.Mixed.check_sound semantic
    exact .mixed domain equal reads
      ⟨run,by rwa [equal],by rwa [equal],check,alloc,emit,layout⟩
  · obtain ⟨result,domain,run,equal,_⟩ := Stock.Logical.check_sound semantic
    exact .logical domain equal reads
      ⟨run,by rwa [equal],by rwa [equal],check,alloc,emit,layout⟩
  · obtain ⟨result,domain,run,equal,_⟩ := Stock.Scalar.check_sound semantic
    rcases reads with old | divided
    · exact .scalar domain equal old
        ⟨run,by rwa [equal],by rwa [equal],check,alloc,emit,layout⟩
    · exact .scalarDiv domain equal divided
        ⟨run,by rwa [equal],by rwa [equal],check,alloc,emit,layout⟩

  · obtain ⟨result,domain,run,equal⟩ := Stock.TwoBlock.check_sound semantic
    exact .cfg domain equal reads
      ⟨run,by rwa [equal],by rwa [equal],check,alloc,emit,layout⟩

  · obtain ⟨result,domain,run,equal⟩ := Stock.TwoBlock.Entry.check_sound semantic
    exact .cfg domain equal reads
      ⟨run,by rwa [equal],by rwa [equal],check,alloc,emit,layout⟩

  · obtain ⟨result,domain,run,equal⟩ := Stock.LinearCfg.check_sound semantic
    exact .cfg domain equal reads
      ⟨run,by rwa [equal],by rwa [equal],check,alloc,emit,layout⟩

  · obtain ⟨result,domain,run,equal⟩ := Stock.ForwardCfg.check_sound semantic
    exact .cfg domain equal reads
      ⟨run,by rwa [equal],by rwa [equal],check,alloc,emit,layout⟩

  · obtain ⟨result,domain,run,equal⟩ := Stock.ConditionalCfg.check_sound semantic
    exact .cfg domain equal reads
      ⟨run,by rwa [equal],by rwa [equal],check,alloc,emit,layout⟩

  · obtain ⟨result,domain,run,equal⟩ := Stock.ConditionalCfg.ranked_check_sound semantic
    exact .cfg domain equal reads
      ⟨run,by rwa [equal],by rwa [equal],check,alloc,emit,layout⟩

  · obtain ⟨result,domain,run,equal⟩ := Stock.ParameterCfg.check_sound semantic
    exact .cfg domain equal reads
      ⟨run,by rwa [equal],by rwa [equal],check,alloc,emit,layout⟩

  · obtain ⟨result,family,run,equal,effects⟩ := Stock.Memory.check_sound memory
    exact .memory family equal effects
      ⟨run,by rwa [equal],by rwa [equal],check,alloc,emit,layout⟩

  · obtain ⟨result,family,run,equal,effects⟩ := Stock.MemoryCfg.check_sound memoryCfg
    exact .memoryCfg family equal effects
      ⟨run,by rwa [equal],by rwa [equal],check,alloc,emit,layout⟩

  · obtain ⟨width,result,family,run,equal,effects⟩ := Stock.MemoryUnsigned.check_sound memoryUnsigned
    exact .memoryUnsigned (width := width) family equal effects
      ⟨run,by rwa [equal],by rwa [equal],check,alloc,emit,layout⟩
  · obtain ⟨kind,ty,result,family,run,equal,effects⟩ := Stock.MemoryExtending.check_sound memoryExtending
    exact .memoryExtending (kind := kind) (ty := ty) family equal effects
      ⟨run,by rwa [equal],by rwa [equal],check,alloc,emit,layout⟩

end CompiledSemanticNI

/-- The complete paired linker consumer follows the actual checked artifact,
retaining the old external, source, ABI and activation interfaces. -/
theorem backend_correct_world_niX_semantic {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledSemanticNI f k vc vcp rf af fa fb)
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
    ∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        us.map (·.2) = (List.range us.length).map Reg.x ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧ vc.RetsSite us ∧
        (∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
          ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (ArmStepX X H fa) n s) ∧
            PostTrace fa af base (ArmStepX X H fa) s n ∧
            ∀ i < n, actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
              (runX (ArmStepX X H fa) i s)) ∧
        (XNI F syms (f.externs.map (·.2)) (indSigs f) c
          (CallLg env (f.externs.map (·.2)) (indSigs f)) X → XTls F X →
        ∀ (D : BitVec 64 → Prop) (w₀' : Arm.ArmState),
          RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀' →
          SameWorld (fun b => F b ∨ D b) w₀ w₀' →
          (∀ r v, (ArgLoc.reg r, v) ∈ (locsOf f.sig).zip args → regVal w₀' r = regVal w₀ r) →
          (∀ off v, (ArgLoc.stack off, v) ∈ (locsOf f.sig).zip args → ∀ k < v.ty.bytes,
            w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
              w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k)) →
          ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
            ActEntry vcp rf af fa fb K F G X H base ra s w₀' →
            ∃ n, ActRet ra (fun a => F a ∨ D a) G us outs w s (runX (ArmStepX X H fa) n s) ∧
              PostTrace fa af base (ArmStepX X H fa) s n ∧
              ∀ i < n, actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
                (runX (ArmStepX X H fa) i s)) := by
  cases hc with
  | compatible h =>
    exact backend_correct_world_niX_production hsub h hcov hX hXI hsym hslot hcs hrel hargs htr fuel
  | arithmetic domain equal reads h =>
    subst vc
    intro vals cm returned
    obtain ⟨us,outs,w,pins,arity,values,memory,site,base,paired⟩ :=
      backend_correct_world_niX_stock_arithmetic domain reads h hcov hsym hslot hcs hrel hargs
        fuel vals cm returned
    exact ⟨us,outs,w,pins,arity,values,memory,site,base,fun _ _ => paired⟩
  | mixed domain equal reads h =>
    subst vc
    intro vals cm returned
    obtain ⟨us,outs,w,pins,arity,values,memory,site,base,paired⟩ :=
      backend_correct_world_niX_stock_mixed domain reads h hcov hsym hslot hcs hrel hargs
        fuel vals cm returned
    exact ⟨us,outs,w,pins,arity,values,memory,site,base,fun _ _ => paired⟩

  | logical domain equal reads h =>
    subst vc
    intro vals cm returned
    obtain ⟨us,outs,w,pins,arity,values,memory,site,base,paired⟩ :=
      backend_correct_world_niX_stock_logical domain reads h hcov hsym hslot hcs hrel hargs
        fuel vals cm returned
    exact ⟨us,outs,w,pins,arity,values,memory,site,base,fun _ _ => paired⟩

  | scalar domain equal reads h =>
    subst vc
    intro vals cm returned
    obtain ⟨us,outs,w,pins,arity,values,memory,site,base,paired⟩ :=
      backend_correct_world_niX_stock_scalar domain reads h hcov hsym hslot hcs hrel hargs
        fuel vals cm returned
    exact ⟨us,outs,w,pins,arity,values,memory,site,base,fun _ _ => paired⟩
  | scalarDiv domain equal reads h =>
    subst vc
    intro vals cm returned
    obtain ⟨us,outs,w,pins,arity,values,memory,site,base,paired⟩ :=
      backend_correct_world_niX_stock_div domain reads h hcov hsym hslot hcs hrel hargs
        fuel vals cm returned
    exact ⟨us,outs,w,pins,arity,values,memory,site,base,fun _ _ => paired⟩
  | cfg domain equal reads h =>
    subst vc
    intro vals cm returned
    obtain ⟨us,outs,w,pins,arity,values,memory,site,base,paired⟩ :=
      backend_correct_world_niX_stock_cfg domain reads h hcov hsym hslot hcs hrel hargs
        fuel vals cm returned
    exact ⟨us,outs,w,pins,arity,values,memory,site,base,fun _ _ => paired⟩

  | memory family equal effects h =>
    subst vc
    classical
    by_cases tls : XTls F X
    · intro vals cm returned
      obtain ⟨us,outs,w,pins,arity,values,memory,site,base,paired⟩ :=
        backend_correct_world_niX_stock_memory family effects h hcov hsym hslot tls hcs hrel hargs
          fuel vals cm returned
      exact ⟨us,outs,w,pins,arity,values,memory,site,base,fun _ _ => paired⟩
    · intro vals cm returned
      obtain ⟨us,outs,w,pins,arity,values,memory,site,base⟩ :=
        (backend_correct_worldX_stock_memory family.domain h hcov hsym hslot hcs hrel hargs fuel).1 vals cm returned
      exact ⟨us,outs,w,pins,arity,values,memory,site,base,fun _ positive => False.elim (tls positive)⟩

  | memoryCfg family equal effects h =>
    subst vc
    classical
    by_cases tls : XTls F X
    · intro vals cm returned
      obtain ⟨us,outs,w,pins,arity,values,memory,site,base,paired⟩ :=
        backend_correct_world_niX_stock_memory_cfg family effects h hcov hsym hslot tls hcs hrel hargs
          fuel vals cm returned
      exact ⟨us,outs,w,pins,arity,values,memory,site,base,fun _ _ => paired⟩
    · intro vals cm returned
      obtain ⟨us,outs,w,pins,arity,values,memory,site,base⟩ :=
        (backend_correct_worldX_stock_memory_cfg family effects h hcov hsym hslot hcs hrel hargs fuel).1 vals cm returned
      exact ⟨us,outs,w,pins,arity,values,memory,site,base,fun _ positive => False.elim (tls positive)⟩

  | @memoryUnsigned width cleanup result family equal effects h =>
    subst vc
    classical
    by_cases tls : XTls F X
    · intro vals cm returned
      obtain ⟨us,outs,w,pins,arity,values,memory,site,base,paired⟩ :=
        backend_correct_world_niX_stock_integer_memory family effects h hcov hsym hslot tls hcs hrel hargs
          fuel vals cm returned
      exact ⟨us,outs,w,pins,arity,values,memory,site,base,fun _ _ => paired⟩
    · intro vals cm returned
      obtain ⟨us,outs,w,pins,arity,values,memory,site,base⟩ :=
        (backend_correct_worldX_stock_memory (Stock.Memory.IntegerRoots.SingleClass.domain width family) h hcov hsym hslot hcs hrel hargs fuel).1 vals cm returned
      exact ⟨us,outs,w,pins,arity,values,memory,site,base,fun _ positive => False.elim (tls positive)⟩
  | @memoryExtending kind ty cleanup result family equal effects h =>
    subst vc
    classical
    by_cases tls : XTls F X
    · intro vals cm returned
      obtain ⟨us,outs,w,pins,arity,values,memory,site,base,paired⟩ :=
        backend_correct_world_niX_stock_extending_memory family effects h hcov hsym hslot tls hcs hrel hargs
          fuel vals cm returned
      exact ⟨us,outs,w,pins,arity,values,memory,site,base,fun _ _ => paired⟩
    · intro vals cm returned
      obtain ⟨us,outs,w,pins,arity,values,memory,site,base⟩ :=
        (backend_correct_worldX_stock_memory (Stock.Memory.ExtendedRoots.SingleClass.domain kind ty family) h hcov hsym hslot hcs hrel hargs fuel).1 vals cm returned
      exact ⟨us,outs,w,pins,arity,values,memory,site,base,fun _ positive => False.elim (tls positive)⟩

end E2E
