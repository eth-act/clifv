import FV.Backend.ABIReadOnly
import FV.E2E.RegLevelPush

namespace E2E.ABIReadOnly
open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup
set_option autoImplicit false
set_option Elab.async false

/-- The executable instruction check supplies its full finite read-only shape. -/
theorem instruction_cases {sig : Clif.Signature} {b k : Nat} {i : MInst}
    (checked : Backend.ABIReadOnly.instruction sig b k i = true) :
    pureForm i = true ∨
    (∃ pairs, i = .args pairs ∧ b = 0 ∧ k = 0 ∧
      pairs.all (fun p => Backend.ABIReadOnly.registerRead sig p.2) = true) ∨
    (∃ op key off fl, i = .load op (.vreg key .int) (.fpOffset off) fl ∧
      op ≠ .fpuLoad128 ∧ Backend.ABIReadOnly.stackRead sig off op.bytes = true) ∨
    (∃ pairs, i = .rets pairs) := by
  unfold Backend.ABIReadOnly.instruction at checked
  split at checked
  · exact .inl (pureForm_of_pureNoFlags (by assumption))
  · rename_i hp
    clear hp
    right
    cases i with
    | args pairs =>
      simp only [Bool.and_eq_true,beq_iff_eq] at checked
      exact .inl ⟨pairs,rfl,checked.1.1,checked.1.2,checked.2⟩
    | rets pairs => exact .inr (.inr ⟨pairs,rfl⟩)
    | load op rd am fl =>
      right; left
      cases rd <;> try cases checked
      case vreg key cls =>
        cases cls <;> try cases checked
        case int =>
          cases am <;> try cases checked
          case fpOffset off =>
            simp only [Bool.and_eq_true,bne_iff_ne] at checked
            exact ⟨op,key,off,fl,rfl,checked⟩
    | _ => cases checked

private theorem zip_parameter_value {locs : List ArgLoc} {params : List Clif.AbiParam}
    {args : List Clif.Val} (types : args.map (·.ty) = params.map (·.ty)) :
    ∀ loc p, (loc,p) ∈ locs.zip params →
      ∃ v, (loc,v) ∈ locs.zip args ∧ v.ty = p.ty := by
  induction locs generalizing params args with
  | nil => simp
  | cons loc locs ih =>
    cases params with
    | nil => simp
    | cons p params =>
      cases args with
      | nil => cases types
      | cons v args =>
        simp only [List.map_cons,List.cons.injEq] at types
        intro loc' p' member
        simp only [List.zip_cons_cons,List.mem_cons] at member
        rcases member with equal | member
        · cases equal
          exact ⟨v,by simp,types.1⟩
        · obtain ⟨v',found,same⟩ := ih types.2 loc' p' member
          exact ⟨v',List.mem_cons_of_mem _ found,same⟩

/-- A declared register read is one of the original ABI argument pairs, without
requiring the parameter to be used by any source statement. -/
theorem registerRead_argument {sig : Clif.Signature} {args : List Clif.Val}
    (types : args.map (·.ty) = sig.params.map (·.ty)) {pin : Reg}
    (checked : Backend.ABIReadOnly.registerRead sig pin = true) :
    ∃ v, (.reg pin,v) ∈ (locsOf sig).zip args := by
  obtain ⟨row,member,located⟩ := List.any_eq_true.mp checked
  have loc : row.1 = .reg pin := by
    cases loc : row.1 with
    | stack off => simp [loc] at located
    | reg r =>
      have same : r = pin := by simpa only [loc,beq_iff_eq] using located
      rw [same]
  obtain ⟨v,found,_⟩ := zip_parameter_value types row.1 row.2 member
  exact ⟨v,by rwa [loc] at found⟩

/-- Every checked stack load is bounded by one original ABI stack argument. -/
theorem stackRead_argument {sig : Clif.Signature} {args : List Clif.Val}
    (types : args.map (·.ty) = sig.params.map (·.ty)) {off : Int} {bytes : Nat}
    (checked : Backend.ABIReadOnly.stackRead sig off bytes = true) :
    ∃ (slot : Nat) (v : Clif.Val), (.stack slot,v) ∈ (locsOf sig).zip args ∧
      off = 16 + (slot : Int) ∧ bytes ≤ v.ty.bytes := by
  obtain ⟨row,member,checked⟩ := List.any_eq_true.mp checked
  obtain ⟨loc,p⟩ := row
  cases loc with
  | reg r => cases checked
  | stack slot =>
    simp only [Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at checked
    obtain ⟨v,found,same⟩ := zip_parameter_value types (.stack slot) p member
    exact ⟨slot,v,found,checked.1,by simpa only [same] using checked.2⟩

end E2E.ABIReadOnly
