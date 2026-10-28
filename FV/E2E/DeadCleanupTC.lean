import FV.E2E.DeadCleanupT
import FV.E2E.FinalTC
import FV.Backend.Proof.DriverCheckC

/-!
# The dead-cleanup chain with typed `try_call`s (S11e6, #419)

`DeadCleanupT.lean`'s structures for the scope with typed direct `try_call`s: `CompiledCleanupTC`
(`CompiledCleanupT` with `lowerCheckTC`, exactly as `CompiledTC` (`E2E/FinalTC.lean`) relates to
`CompiledT`), `CompiledCleanupATC` (`CompiledCleanupAT` with `lowerCheckTC`), and the integer
`.toA`-style helper `CompiledCleanupTC.toA` plus the outgoing-area bound
`outgoing_le_intBaseCleanupATC`.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

/-- `CompiledCleanup` with the typed-`try_call` lowering validator (`CompiledCleanupT` with
`lowerCheckTC`). -/
structure CompiledCleanupTC (f : Clif.Function) (k : Nat) (vc vcp : VCode) (rf : RFunc)
    (af : AFunc) (fa : FnAsm) (fb : FnBin) : Prop where
  lower : lowerFunction f = .ok vc
  lowerOk : lowerCheckTC f vc = true
  prepare : prepare (Backend.DeadCleanup.prune vc) = .ok vcp
  prepOk : prepCheck (Backend.DeadCleanup.prune vc) vcp = true
  check : checkAlloc vcp rf = .ok ()
  alloc : lowerRFunc vcp rf = .ok af
  emit : emitFunc k af = .ok fa
  layout : fa.layout = .ok fb

/-- `CompiledCleanupATC`: `CompiledCleanupTC` with an `AllocChecked` allocation. -/
structure CompiledCleanupATC (f : Clif.Function) (k : Nat) (vc vcp : VCode) (rf : RFunc)
    (af : AFunc) (fa : FnAsm) (fb : FnBin) : Prop where
  lower : lowerFunction f = .ok vc
  lowerOk : lowerCheckTC f vc = true
  prepare : prepare (Backend.DeadCleanup.prune vc) = .ok vcp
  prepOk : prepCheck (Backend.DeadCleanup.prune vc) vcp = true
  check : AllocChecked vcp rf
  alloc : lowerRFunc vcp rf = .ok af
  emit : emitFunc k af = .ok fa
  layout : fa.layout = .ok fb

theorem CompiledCleanupTC.toA {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
    {af : AFunc} {fa : FnAsm} {fb : FnBin} (hc : CompiledCleanupTC f k vc vcp rf af fa fb) :
    CompiledCleanupATC f k vc vcp rf af fa fb :=
  ⟨hc.lower, hc.lowerOk, hc.prepare, hc.prepOk, allocChecked_of_checkAlloc hc.check, hc.alloc,
    hc.emit, hc.layout⟩

theorem outgoing_le_intBaseCleanupATC {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hc : CompiledCleanupATC f k vc vcp rf af fa fb) :
    vc.outgoing ≤ (RAFrame.compute vcp rf).intBase := by
  simp only [RAFrame.compute]
  rw [outgoing_of_prepCheck hc.prepOk, prune_outgoing]
  exact le_alignTo _ 16 (by decide)

end E2E
