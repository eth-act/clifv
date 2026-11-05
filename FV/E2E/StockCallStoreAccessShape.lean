import FV.E2E.StockCallStoreLayout
import FV.E2E.StockCallStoreNoTry
import FV.Backend.Proof.StockMemoryAccessShapeCheck
import FV.Backend.Proof.RelocProvEmit

namespace Backend.Stock.CallStore
open Backend Backend.Proof Backend.Proof.RelocProv Backend.Proof.Driver Backend.Stock.Proof E2E MemoryFaults Backend.DeadCleanup
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- Both integer parameters use registers, including the existing sret placement rule. -/
theorem no_stack_read_two_i64 {sig : Clif.Signature}
    (types : sig.params.map (·.ty) = [.i64,.i64]) (offset : Int) (bytes : Nat) :
    Backend.ABIReadOnly.stackRead sig offset bytes = false := by
  obtain ⟨params,returns,convention⟩ := sig
  cases params with
  | nil => simp at types
  | cons first rest =>
    cases rest with
    | nil => simp at types
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

private theorem readOnly_shape {sig : Clif.Signature} {b pc : Nat} {inst : MInst}
    (noStack : ∀ offset bytes,Backend.ABIReadOnly.stackRead sig offset bytes = false)
    (checked : Backend.ABIReadOnly.instruction sig b pc inst = true) :
    ordinaryAccessShapeB inst = true := by
  rcases ABIReadOnly.instruction_cases checked with pure | ⟨pairs,rfl,_⟩ |
      ⟨op,key,offset,flags,rfl,no128,read⟩ | ⟨pairs,rfl⟩
  · cases inst <;> first | rfl | simp [pureForm] at pure
  · rfl
  · rw [noStack] at read
    cases read
  · rfl

/-- Every checked source artifact has the required memory form, without another admission guard. -/
theorem instruction_access_shape {sig : Clif.Signature} {b pc : Nat} {inst : MInst}
    (noStack : ∀ offset bytes,Backend.ABIReadOnly.stackRead sig offset bytes = false)
    (checked : instruction sig b pc inst = true) : ordinaryAccessShapeB inst = true := by
  unfold instruction at checked
  split at checked
  · rename_i info eq
    rfl
  · rename_i value address flags eq
    rfl
  · exact readOnly_shape noStack checked

/-- The complete raw code derives its access shapes from existing class checks. -/
theorem Layout.raw_access_shapes {f : Clif.Function} {result : Stock.Result} (layout : Layout f result) :
    AllInsts (fun inst => ordinaryAccessShapeB inst = true) result.code := by
  obtain ⟨blocks,parameters,body,term,params,rest⟩ := layout.source_fields
  intro block member inst present
  obtain ⟨b,placed⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨j,located⟩ := List.mem_iff_getElem?.mp present
  have accepted := checked_instruction layout.reads (by simpa using placed) (by simpa using located)
  exact instruction_access_shape (no_stack_read_two_i64 params) accepted

private theorem access_shape_retarget {inst changed : MInst} {labels : List Label}
    (retarget : inst.setTargets labels = some changed) (shape : ordinaryAccessShapeB inst = true) :
    ordinaryAccessShapeB changed = true := by
  cases inst <;> simp only [MInst.setTargets] at retarget <;>
    repeat' first | split at retarget | cases retarget | rfl

/-- Both production stages retain the source-derived shapes through the actual preparation. -/
theorem Layout.prepared_access_shapes {f : Clif.Function} {result : Stock.Result} (layout : Layout f result)
    {cleanup : Bool} {prepared : VCode}
    (run : prepare (Stock.Arithmetic.stage cleanup result.code) = .ok prepared) :
    ∀ (b : Nat) (block : VBlock) (j : Nat) (inst : MInst),
      prepared.blocks[b]? = some block → block.insts[j]? = some inst →
      ∀ sb uses world code address bytes,AccessAt sb inst uses world code address bytes → OrdinaryAccessShape inst := by
  have original := layout.raw_access_shapes
  have staged : AllInsts (fun inst => ordinaryAccessShapeB inst = true)
      (Stock.Arithmetic.stage cleanup result.code) := by
    cases cleanup with
    | false => exact original
    | true => exact prune_insts original
  have retained := prepare_allInsts (fun _ => rfl) (fun _ _ _ => access_shape_retarget) run staged
  intro b block j inst placed located sb uses world code address bytes access
  exact ordinaryAccessShape_of_check (retained block
    (List.mem_of_getElem? (by simpa using placed)) inst
    (List.mem_of_getElem? (by simpa using located))) access

end Backend.Stock.CallStore
