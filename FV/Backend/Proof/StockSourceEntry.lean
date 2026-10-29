module

public import FV.Backend.Proof.StockSourceDefined

@[expose] public section

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Backend.Proof.Driver.Fix
set_option autoImplicit false
set_option Elab.async false

/-- The original source entry bindings, independently of the allocation of
explicit stack slots. Both executable entry and the production ClifEntry
contract provide these facts; no machine-value certificate is included. -/
def SourceEntry (f : Clif.Function) (args : List Clif.Val) (fr : Clif.Frame) : Prop :=
  ∃ b regs, f.entry? = some b ∧ args.map (·.ty) = Clif.AbiParam.tys f.sig.params ∧
    args.map (·.ty) = b.params.map (·.2) ∧
    Clif.Regs.empty.setMany (b.params.map (·.1)) args = some regs ∧
    fr = ⟨f,regs,fr.slots,b.body,b.term⟩

theorem SourceEntry.of_enterFunc {f : Clif.Function} {args : List Clif.Val}
    {cm0 cm : Clif.Mem} {fr : Clif.Frame}
    (entered : Clif.enterFunc f args cm0 = .ok (fr,cm)) : SourceEntry f args fr := by
  obtain ⟨b,regs,entry,types,paramTypes,set,_,frame⟩ := Opt.enterFunc_ok entered
  exact ⟨b,regs,entry,types,paramTypes,set,frame⟩

/-- Entry definedness uses the existing bindings, not the address choice made
by executable enterSlots. -/
theorem source_defined_entry_frame {f : Clif.Function} (dominated : Dominated f) (ctx : Ctx)
    {args : List Clif.Val} {fr : Clif.Frame} (entered : SourceEntry f args fr) :
    SourceDefinedAt f ctx 0 0 fr := by
  obtain ⟨b,regs,entry,types,paramTypes,set,frame⟩ := entered
  simp only [Clif.Function.entry?,List.head?_eq_getElem?] at entry
  have nodup : (b.params.map (·.1)).Nodup :=
    (List.nodup_append.mp (block_nodup dominated.ssa entry)).1
  intro x available
  obtain ⟨present,_⟩ := (mem_av entry).mp available
  rcases present with parameter | incoming | ⟨j,stm,earlier,_,_⟩
  · obtain ⟨_,v,_,_,value⟩ := setMany_mem set nodup x parameter
    refine ⟨v,?_⟩
    rw [frame]
    exact value
  · have bound := (inFix_fixOk (f := f) (ctx := ctx) (gn := id)).cand 0 x incoming
    omega
  · omega

end Backend.Stock.Proof
