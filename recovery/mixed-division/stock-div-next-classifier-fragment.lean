namespace Backend.Stock.Scalar
set_option autoImplicit false
set_option Elab.async false

/-- Previously proved scalar syntax before one final returned division.
The old single-division and pure-body classifiers remain unchanged. -/
def mixedDivEligible (b : Clif.Block) : Bool :=
  match b.body.reverse,b.term with
  | ⟨[z],.div _ ty _ _⟩ :: front,.ret [z'] =>
      z == z' && (ty == .i32 || ty == .i64) && front.all highmulBodyEligible
  | _,_ => false

/-- The classifier derives source shape and every prefix family internally. -/
theorem mixedDivEligible_sound {b : Clif.Block} (checked : mixedDivEligible b = true) :
    ∃ (front : List Clif.Stmt) (stm : Clif.Stmt) (op : Clif.DivOp) (ty : Clif.Ty) (x y z : Nat),
      b.body = front ++ [stm] ∧
      (∀ item ∈ front,Proof.HighMulBody.Family item.inst) ∧
      stm.inst = .div op ty x y ∧ stm.results = [z] ∧ b.term = .ret [z] := by
  unfold mixedDivEligible at checked
  split at checked
  next z op ty x y front z' body ret =>
    simp only [Bool.and_eq_true] at checked
    have equal : z = z' := beq_iff_eq.mp checked.1.1
    subst z'
    refine ⟨front.reverse,⟨[z],.div op ty x y⟩,op,ty,x,y,z,?_,?_,rfl,rfl,ret⟩
    · have reversed := congrArg List.reverse body
      simpa only [List.reverse_reverse,List.reverse_cons,List.reverse_nil,List.nil_append] using reversed
    · intro item member
      exact highmulBodyEligible_sound (List.all_eq_true.mp checked.2 item (List.mem_reverse.mp member))
  next => cases checked
end Backend.Stock.Scalar
#print axioms Backend.Stock.Scalar.mixedDivEligible_sound
