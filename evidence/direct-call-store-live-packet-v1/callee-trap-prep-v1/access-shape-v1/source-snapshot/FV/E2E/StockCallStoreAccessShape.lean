import FV.E2E.StockCallStoreLayout
import FV.E2E.StockCallStoreNoTry
import FV.Backend.Proof.StockMemoryAccessShapeCheck
import FV.Backend.Proof.RelocProvEmit

namespace Backend.Stock.CallStore
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof E2E MemoryFaults Backend.DeadCleanup
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- Both integer parameters use registers, including the existing sret placement rule. -/
theorem no_stack_read_two_i64 {sig : Clif.Signature}
    (types : sig.params.map (·.ty) = [.i64,.i64]) (offset : Int) (bytes : Nat) :
    Backend.ABIReadOnly.stackRead sig offset bytes = false := by
  obtain ⟨params,returns,convention⟩ := sig
  cases params with
  | nil => cases types
  | cons first rest =>
    cases rest with
    | nil => cases types
    | cons second rest =>
      have fields : first.ty = .i64 ∧ second.ty = .i64 ∧ rest = [] := by
        simpa only [List.map_cons,List.cons.injEq,List.map_eq_nil_iff,and_assoc] using types
      obtain ⟨firstType,secondType,rfl⟩ := fields
      obtain ⟨firstTy,firstExt,firstPurpose⟩ := first
      obtain ⟨secondTy,secondExt,secondPurpose⟩ := second
      dsimp only at firstType secondType
      subst firstTy secondTy
      cases firstPurpose <;> cases secondPurpose <;>
        simp [Backend.ABIReadOnly.stackRead,locsOf,sigArgLocs,sigArgs,paramLocs,
          argLocsC,argLocStep,sretLocStep,tyClass,Clif.Ty.bytes,Clif.Ty.width,
          pure,Except.pure,bind,Except.bind]

end Backend.Stock.CallStore
