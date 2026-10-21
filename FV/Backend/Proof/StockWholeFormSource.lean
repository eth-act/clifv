import FV.Backend.Proof.StockEmissionCoverageFixture

namespace Backend.Stock.Proof.Coverage.WholeFormsFixture
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.PerEdgePrep Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000

def params : List (Nat × Clif.Ty) := (List.range 9).map (fun n => (n,.i64))
def entryFunction : Clif.Function := {
  name := "stock_whole_forms_register_and_stack_entry"
  sig := {
    params := (List.range 9).map (fun _ => ⟨.i64,.none,.normal⟩)
    returns := [⟨.i64,.none,.normal⟩,⟨.i64,.none,.normal⟩]
    callConv := some .systemV }
  blocks := [{id := 0,params,term := .ret [0,8]}] }

def isArgs : MInst → Bool | .args _ => true | _ => false
def isFrameLoad : MInst → Bool | .load _ _ (.fpOffset _) _ => true | _ => false
theorem source_scope : LowerScope entryFunction := by
  apply lowerScope_of
  decide +kernel

theorem source_arity : ArityOk entryFunction := arityOk_of (by decide +kernel)

theorem source_dominated : Dominated entryFunction := by
  constructor
  · decide +kernel
  · intro ctx ranges st build bi b found
    have bounded : bi < 1 := by have h := lt_of_getElem? found; simpa [entryFunction] using h
    have same : bi = 0 := by omega
    subst bi
    simp [entryFunction] at found
    subst b
    constructor
    · intro j stm atStmt
      simp at atStmt
    · intro x member
      change x ∈ Driver.termArgs (abiTerm entryFunction (.ret [0,8])) at member
      rw [show abiTerm entryFunction (.ret [0,8]) = .ret [0,8] from rfl] at member
      change x ∈ ([0,8] : List Nat) at member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl <;> simp [availOf,entryFunction,params,defsBefore,defsFrom]
  · intro ctx ranges st build tl x available notLocal y member
    have fixed := (inFix_fixOk (f := entryFunction) (ctx := ctx) (gn := id)).cand tl x available
    have small : tl < 1 := by simpa [entryFunction] using fixed.2.1
    omega

end Backend.Stock.Proof.Coverage.WholeFormsFixture
