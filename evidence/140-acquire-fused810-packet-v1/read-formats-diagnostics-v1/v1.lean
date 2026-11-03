import FV.Backend.Proof.StockAcquireSourceRead

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Isle
set_option autoImplicit false
set_option Elab.async false

/-- The two generated sink formats encode original reads, not stores or source calls. -/
theorem instData_read_format {f : Clif.Function} {inst : Clif.Inst} {fmt : Nat} {fields : List V}
    (encoded : instData f inst = .ok (.data 152 fmt fields)) (format : fmt = 16 ∨ fmt = 17) :
    (∃ op ty flags pointer offset,inst = .load op ty flags pointer offset) ∨
      (∃ ty flags pointer,inst = .atomicLoad ty flags pointer) := by
  rcases instData_names encoded with ⟨rest,shape⟩ | ⟨ty,imm,equal,float,rest,shape | shape⟩
  · have names := (mkVariant_eq_data shape.symm).1
    rcases format with rfl | rfl
    · rw [mem_variantNames_Load] at names
      cases inst <;> simp only [instNames] at names
      all_goals first | (simp at names; done) | (exact Or.inl ⟨_,_,_,_,_,rfl⟩)
    · rw [atom_vn_LoadNoOffset] at names
      cases inst <;> simp only [instNames] at names
      all_goals first | (simp at names; done) | (exact Or.inr ⟨_,_,_,rfl⟩)
  · rcases format with rfl | rfl <;> cases shape
  · rcases format with rfl | rfl <;> cases shape

end Backend.Stock.Proof.Acquire810
