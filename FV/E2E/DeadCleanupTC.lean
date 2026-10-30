import FV.E2E.Final
import FV.Backend.Proof.DeadCleanupPrepare
import FV.Backend.Proof.DriverCheckC
import FV.Backend.Proof.DriverCheckTCF

/-!
# The dead-cleanup chain with typed `try_call`s (S11e6, #419)

`DeadCleanupT.lean`'s structures for the scope with typed direct `try_call`s: `CompiledCleanupTC`
(`CompiledCleanupT` with `lowerCheckTC`, exactly as `CompiledTC` (`E2E/FinalTC.lean`) relates to
`CompiledT`), `CompiledCleanupATC` (`CompiledCleanupAT` with `lowerCheckTC`), and the integer
`.toA`-style helper `CompiledCleanupTC.toA` plus the outgoing-area bound
`outgoing_le_intBaseCleanupATC`.

S11f (#35): the same for the scope with the proven float operations (`Compile.functionETCF`,
validator `lowerCheckTCF`, as `CompiledTCF` (`E2E/FinalTCF.lean`) relates to `CompiledTC`):
`CompiledCleanupTCF`, `CompiledCleanupATCF`, `CompiledCleanupTC.toTCF`, `CompiledCleanupTCF.toA`,
`outgoing_le_intBaseCleanupATCF`.
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

/-- `CompiledCleanup` with the lowering validator of the scope with the proven float operations
(`CompiledCleanupTC` with `lowerCheckTCF`, S11f). -/
structure CompiledCleanupTCF (f : Clif.Function) (k : Nat) (vc vcp : VCode) (rf : RFunc)
    (af : AFunc) (fa : FnAsm) (fb : FnBin) : Prop where
  lower : lowerFunction f = .ok vc
  lowerOk : lowerCheckTCF f vc = true
  prepare : prepare (Backend.DeadCleanup.prune vc) = .ok vcp
  prepOk : prepCheck (Backend.DeadCleanup.prune vc) vcp = true
  check : checkAlloc vcp rf = .ok ()
  alloc : lowerRFunc vcp rf = .ok af
  emit : emitFunc k af = .ok fa
  layout : fa.layout = .ok fb

/-- `CompiledCleanupATCF`: `CompiledCleanupTCF` with an `AllocChecked` allocation. -/
structure CompiledCleanupATCF (f : Clif.Function) (k : Nat) (vc vcp : VCode) (rf : RFunc)
    (af : AFunc) (fa : FnAsm) (fb : FnBin) : Prop where
  lower : lowerFunction f = .ok vc
  lowerOk : lowerCheckTCF f vc = true
  prepare : prepare (Backend.DeadCleanup.prune vc) = .ok vcp
  prepOk : prepCheck (Backend.DeadCleanup.prune vc) vcp = true
  check : AllocChecked vcp rf
  alloc : lowerRFunc vcp rf = .ok af
  emit : emitFunc k af = .ok fa
  layout : fa.layout = .ok fb

/-- `lowerCheckTC`'s acceptance is `lowerCheckTCF`'s. -/
theorem CompiledCleanupTC.toTCF {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
    {af : AFunc} {fa : FnAsm} {fb : FnBin} (hc : CompiledCleanupTC f k vc vcp rf af fa fb) :
    CompiledCleanupTCF f k vc vcp rf af fa fb :=
  ⟨hc.lower, lowerCheckTCF_of_lowerCheckTC hc.lowerOk, hc.prepare, hc.prepOk, hc.check, hc.alloc,
    hc.emit, hc.layout⟩

theorem CompiledCleanupTCF.toA {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
    {af : AFunc} {fa : FnAsm} {fb : FnBin} (hc : CompiledCleanupTCF f k vc vcp rf af fa fb) :
    CompiledCleanupATCF f k vc vcp rf af fa fb :=
  ⟨hc.lower, hc.lowerOk, hc.prepare, hc.prepOk, allocChecked_of_checkAlloc hc.check, hc.alloc,
    hc.emit, hc.layout⟩

theorem outgoing_le_intBaseCleanupATCF {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hc : CompiledCleanupATCF f k vc vcp rf af fa fb) :
    vc.outgoing ≤ (RAFrame.compute vcp rf).intBase := by
  simp only [RAFrame.compute]
  rw [outgoing_of_prepCheck hc.prepOk, prune_outgoing]
  exact le_alignTo _ 16 (by decide)

end E2E
