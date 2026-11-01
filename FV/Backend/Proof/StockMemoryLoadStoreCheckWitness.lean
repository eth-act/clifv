import FV.Backend.Proof.StockMemoryLoadStoreFixture
import FV.Backend.Proof.StockMemoryLoadStoreCheck

namespace Backend.Stock.Memory.LoadStore.Fixture
open Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

private def widths : List IntegerRoots.Width := [.w8,.w16,.w32,.w64]
private def kinds : List StoreRoots.Kind := [.plain8,.plain16,.plain32,.plain64,.narrow8,.narrow16,.narrow32]

private def observed (width : IntegerRoots.Width) (kind : StoreRoots.Kind) (distinct : Bool) : Bool :=
  match Stock.lower (function width kind distinct) with
  | .error _ => false
  | .ok result => Backend.Stock.MemoryLoadStore.check (function width kind distinct) result.code

private def matrix : Bool := widths.all fun width => kinds.all fun kind =>
  [false,true].all fun distinct => observed width kind distinct

private theorem matrix_checked : matrix = true := by native_decide

/-- Every complete fixture lowers successfully and passes the actual artifact checker. -/
theorem complete_checked_function_witness (width : IntegerRoots.Width) (kind : StoreRoots.Kind)
    (distinct : Bool) : ∃ result : Result,
      Stock.lower (function width kind distinct) = .ok result ∧
      Backend.Stock.MemoryLoadStore.check (function width kind distinct) result.code = true := by
  have widthMember : width ∈ widths := by cases width <;> simp [widths]
  have kindMember : kind ∈ kinds := by cases kind <;> simp [kinds]
  have boolMember : distinct ∈ [false,true] := by cases distinct <;> simp
  have checked := List.all_eq_true.mp
    (List.all_eq_true.mp (List.all_eq_true.mp matrix_checked width widthMember) kind kindMember)
    distinct boolMember
  unfold observed at checked
  cases run : Stock.lower (function width kind distinct) with
  | error message => simp only [run,Bool.false_eq_true] at checked
  | ok result =>
    rw [run] at checked
    exact ⟨result,rfl,checked⟩

end Backend.Stock.Memory.LoadStore.Fixture
