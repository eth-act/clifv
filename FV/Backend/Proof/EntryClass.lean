import FV.Backend.Isel

/-!
# The entry block's parameter classes (S11e5 Stage C, slice 5)

`lowerFunction` pairs the entry block's parameters with `sigArgLocs f.sig` by position: a
parameter's vreg has the class of its block-parameter type, its location the class of the
signature's parameter type. The CLIF verifier makes the two types equal; `Compile.functionET`
does not check it, so the typed control-form facts take it as a premise, decided on the input
by `entryClassOkB` (`entryClassOk_of`).
-/

namespace Backend.Proof

open Backend

/-- **The entry block's parameters have the register classes of the signature's parameters**,
position by position. -/
def EntryClassOk (f : Clif.Function) : Prop :=
  ∀ B0, f.blocks.head? = some B0 → ∀ (i : Nat) (x : Clif.ValueId) (t : Clif.Ty) (sp : Clif.AbiParam),
    B0.params[i]? = some (x, t) → f.sig.params[i]? = some sp → tyClass t = tyClass sp.ty

/-- `EntryClassOk`, decided. -/
def entryClassOkB (f : Clif.Function) : Bool :=
  match f.blocks with
  | [] => true
  | B0 :: _ => (B0.params.zip f.sig.params).all fun q => decide (tyClass q.1.2 = tyClass q.2.ty)

/-- `entryClassOkB` decides `EntryClassOk`. -/
theorem entryClassOk_of {f : Clif.Function} (h : entryClassOkB f = true) : EntryClassOk f := by
  intro B0 hB i x t sp hb hs
  unfold entryClassOkB at h
  cases hf : f.blocks with
  | nil => rw [hf] at hB; cases hB
  | cons B bs =>
    rw [hf] at hB h
    simp only [List.head?_cons, Option.some.injEq] at hB
    subst hB
    have hz : (B.params.zip f.sig.params)[i]? = some ((x, t), sp) := by
      rw [List.getElem?_zip_eq_some]; exact ⟨hb, hs⟩
    have := List.all_eq_true.mp h _ (List.mem_of_getElem? hz)
    simpa using this

end Backend.Proof
