import FV.E2E.DeadCleanupPipeline
import FV.E2E.LowerDirect

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver Backend.Proof.Prep Backend.DeadCleanup

/-- The cleanup pipeline needs the same source conditions as the legacy one,
without a new lowering or preparation validator premise. -/
theorem CompiledCleanup.of_lower {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
    {af : AFunc} {fa : FnAsm} {fb : FnBin} (hd : Dominated f) (hs : LowerScope f)
    (hl : lowerFunction f = .ok vc) (hp : Backend.prepare (prune vc) = .ok vcp)
    (hch : checkAlloc vcp rf = .ok ()) (ha : lowerRFunc vcp rf = .ok af)
    (he : emitFunc k af = .ok fa) (hla : fa.layout = .ok fb) :
    CompiledCleanup f k vc vcp rf af fa fb :=
  ⟨hl, lowerCheck_complete hd hs hl, hp,
    prepCheck_complete hp (prune_prepDomain (prepDomain_of_lower hs hl hs.nonempty)),
    hch, ha, he, hla⟩

theorem CompiledCleanup.of_lowerB {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
    {af : AFunc} {fa : FnAsm} {fb : FnBin} (hd : dominatedB f = true)
    (hs : lowerScopeB f = true) (hl : lowerFunction f = .ok vc)
    (hp : Backend.prepare (prune vc) = .ok vcp) (hch : checkAlloc vcp rf = .ok ())
    (ha : lowerRFunc vcp rf = .ok af) (he : emitFunc k af = .ok fa) (hla : fa.layout = .ok fb) :
    CompiledCleanup f k vc vcp rf af fa fb :=
  CompiledCleanup.of_lower (dominated_of hd) (lowerScope_of hs) hl hp hch ha he hla

theorem CompiledCleanupA.of_lowerB {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
    {af : AFunc} {fa : FnAsm} {fb : FnBin} (hd : dominatedB f = true)
    (hs : lowerScopeB f = true) (hl : lowerFunction f = .ok vc)
    (hp : Backend.prepare (prune vc) = .ok vcp) (hch : AllocChecked vcp rf)
    (ha : lowerRFunc vcp rf = .ok af) (he : emitFunc k af = .ok fa) (hla : fa.layout = .ok fb) :
    CompiledCleanupA f k vc vcp rf af fa fb :=
  ⟨hl, lowerCheck_complete (dominated_of hd) (lowerScope_of hs) hl, hp,
    prepCheck_complete hp (prune_prepDomain
      (prepDomain_of_lower (lowerScope_of hs) hl (lowerScope_of hs).nonempty)),
    hch, ha, he, hla⟩

end E2E
