import FV.Backend.Proof.StockAliasClassInputs
import FV.Backend.Proof.StockEmissionCoverageFixture

namespace Backend.Stock.Proof.TryAliasFixture
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.PerEdgePrep Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

def signature : Clif.Signature := {
  returns := [⟨.i8,.none,.normal⟩],callConv := some .systemV }
def table : Clif.ExnTable := {sig := 0,normal := ⟨1,[.ret 0,.val 0]⟩}
def function : Clif.Function := {
  name := "stock_helper_alias_complete_try_pipeline"
  sig := signature
  sigDecls := [(0,signature)]
  externs := [(0,{name := "callee",sig := signature})]
  blocks := [
    {id := 0,body := [⟨[0],.iconst .i8 9⟩],term := .tryCall 0 [] table},
    {id := 1,params := [(1,.i8),(2,.i8)],term := .ret [2]}] }

theorem source_scope : LowerScope function := lowerScope_of (by decide +kernel)
theorem source_arity : ArityOk function := arityOk_of (by decide +kernel)

private def original : Ctx × Array (Nat × Nat) × LState :=
  (Backend.buildCtx function).toOption.getD (sinkCtx,#[],default)
private theorem original_build : Backend.buildCtx function = .ok original := rfl

theorem source_dominated : Dominated function := by
  constructor
  · decide +kernel
  · intro ctx ranges st build bi b found
    have bound : bi < 2 := by have h := lt_of_getElem? found; simpa [function] using h
    have choices : bi = 0 ∨ bi = 1 := by omega
    rcases choices with rfl | rfl
    · simp [function] at found
      subst b
      constructor
      · intro j stm atStmt x member
        have zero : j = 0 := by have h := lt_of_getElem? atStmt; simp at h; omega
        subst j
        cases atStmt
        cases member
      · intro x member
        have zero : x = 0 := by simpa [abiTerm,Driver.termArgs,function,table,signature,sretRet,sigRets,Clif.ExnTable.vals,Clif.TryDest.vals] using member
        subst x
        simp [availOf,function,defsBefore,defsFrom]
    · simp [function] at found
      subst b
      constructor
      · intro j stm atStmt; simp at atStmt
      · intro x member
        have two : x = 2 := by simpa [abiTerm,Driver.termArgs,function,signature,sretRet,sigRets] using member
        subst x
        simp [availOf,function,defsBefore,defsFrom]
  · intro ctx ranges st build tl x available notLocal y member
    have context : ctx = original.1 := congrArg Prod.fst (Except.ok.inj (build.symm.trans original_build))
    rw [context] at member
    have fixed := (inFix_fixOk (f := function) (ctx := ctx) (gn := id)).cand tl x available
    have values : x = 0 ∨ x = 1 ∨ x = 2 := by simpa [valueDefs,function] using fixed.2.2.2.1
    rcases values with rfl | rfl | rfl
    all_goals change y ∈ ([] : List Nat) at member; cases member

end Backend.Stock.Proof.TryAliasFixture
