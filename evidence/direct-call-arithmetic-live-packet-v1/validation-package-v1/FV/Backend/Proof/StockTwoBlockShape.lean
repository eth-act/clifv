import FV.Backend.Lowering.Stock
import FV.Backend.Proof.LowerCertBase
import FV.Backend.Proof.RegallocInstsFP

namespace Backend.Stock.Proof.TwoBlock
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- Internally derived entry coverage for a two-block class: each inherited
successor value is either an entry parameter or a forwarded definition. -/
theorem successor_entry_coverage {f : Clif.Function} {entry target : Clif.Block}
    (blocks : f.blocks = [entry,target]) {ctx : Ctx} {bc : Clif.BlockCall}
    (forwarded : ∀ stm ∈ entry.body,∀ x ∈ stm.results,x ∈ bc.args)
    {x : Nat} (available : x ∈ availOf f (availIn f ctx) 1 0)
    (notParam : x ∉ target.params.map (·.1)) :
    x ∈ entry.params.map (·.1) ∨ x ∈ bc.args := by
  have block : f.blocks[1]? = some target := by rw [blocks]; rfl
  obtain ⟨present,noLater⟩ := (mem_av block).mp available
  rcases present with parameter | incoming | ⟨j,stm,earlier,_,_⟩
  · exact False.elim (notParam parameter)
  · have defined := ((inFix_fixOk (f := f) (ctx := ctx) (gn := id)).cand 1 x incoming).2.2.2.1
    simp only [valueDefs,blocks,List.flatMap_cons,List.flatMap_nil,List.append_nil,
      List.mem_append] at defined
    rcases defined with (parameter | result) | parameter | result
    · exact .inl parameter
    · obtain ⟨stm,member,defined⟩ := List.mem_flatMap.mp result
      exact .inr (forwarded stm member x defined)
    · exact False.elim (notParam parameter)
    · obtain ⟨stm,member,defined⟩ := List.mem_flatMap.mp result
      obtain ⟨j,bound,rfl⟩ := List.getElem_of_mem member
      exact False.elim (noLater ⟨j,target.body[j],Nat.zero_le _,List.getElem?_eq_getElem bound,defined⟩)
  · omega

/-- The actual order of a direct two-block jump/return function. Bodies and
value identities remain arbitrary; the graph follows from source structure. -/
theorem block_order {f : Clif.Function} {entry target : Clif.Block} {bc : Clif.BlockCall}
    {xs : List Nat} (blocks : f.blocks = [entry,target])
    (jump : entry.term = .jump bc) (ret : target.term = .ret xs)
    (destination : bc.block = target.id) (different : entry.id ≠ target.id) :
    blockOrder f = .ok ⟨#[.original 0,.original 1],#[#[1],#[]]⟩ := by
  have traversal : rpo #[#[1],#[]] = #[0,1] := by decide +kernel
  simp [blockOrder,blocks,jump,ret,destination,different,Ne.symm different,destinations,
    List.findIdx?_cons,traversal]
  rfl


end Backend.Stock.Proof.TwoBlock
