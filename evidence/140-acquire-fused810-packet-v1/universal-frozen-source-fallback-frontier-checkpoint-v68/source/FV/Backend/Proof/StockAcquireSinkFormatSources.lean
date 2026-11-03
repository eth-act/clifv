import FV.Backend.Proof.StockAcquireReadFormats
import FV.Backend.Proof.StockNoLoadSource

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp
set_option autoImplicit false
set_option Elab.async false

/-- This source-data property describes the two generated sink formats internally. -/
def SinkFormatSources (f : Clif.Function) (ctx : Ctx) : Prop :=
  ∀ (slot : Nat) (info : IInfo),ctx.insts[slot]? = some info → ∀ fmt fields,
    fmt = 16 ∨ fmt = 17 → (Backend.sem ctx).unData 152 info.data = some (fmt,fields) →
    ∃ inst,info.clif = some inst ∧ instData f inst = .ok info.data ∧
      ((∃ op ty flags pointer offset,inst = .load op ty flags pointer offset) ∨
       (∃ ty flags pointer,inst = .atomicLoad ty flags pointer) ∨
       (∃ ty flags value,inst = .bitcast ty flags value))

private theorem decoded_shape {ctx : Ctx} {tag : Nat} {value : V} {fields : List V}
    (decoded : (Backend.sem ctx).unData 152 value = some (tag,fields)) : value = .data 152 tag fields := by
  cases value <;> try cases decoded
  rename_i actualTy actualTag actualFields
  change (if actualTy == 152 then some (actualTag,actualFields) else none) = some (tag,fields) at decoded
  split at decoded
  · rename_i same
    have typeEq : actualTy = 152 := by simpa only [beq_iff_eq] using same
    subst actualTy
    cases Option.some.inj decoded
    rfl
  · cases decoded

/-- Successful actual construction derives source existence and source kinds for every sink-format slot. -/
theorem buildCtx_sink_format_sources {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {state : State}
    (built : Stock.buildCtx f = .ok (ctx,ranges,state)) : SinkFormatSources f ctx := by
  obtain ⟨original,base,run,spec,view⟩ := buildCtx_source built
  intro slot info found fmt fields format decoded
  have member : info ∈ original.insts.toList := by
    rw [← view.insts]
    exact Array.mem_toList_iff.mpr (Array.mem_of_getElem? found)
  rcases spec.insts info member with rfl | ⟨block,present,stm,statement,rfl⟩
  · change none = some (fmt,fields) at decoded
    cases decoded
  · change (Backend.sem ctx).unData 152 (dataOf f stm) = some (fmt,fields) at decoded
    unfold dataOf at decoded
    cases encoded : instData f stm.inst with
    | error message =>
      simp only [encoded] at decoded
      change none = some (fmt,fields) at decoded
      cases decoded
    | ok data =>
      simp only [encoded] at decoded
      have shape := decoded_shape decoded
      have kinds := instData_read_format (encoded.trans (congrArg Except.ok shape)) format
      refine ⟨stm.inst,rfl,?_,kinds⟩
      change instData f stm.inst = .ok (dataOf f stm)
      simp only [dataOf,encoded]

end Backend.Stock.Proof.Acquire810
