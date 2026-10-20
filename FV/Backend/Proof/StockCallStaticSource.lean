import FV.Backend.Proof.StockCallAbiStatic
import FV.Backend.Proof.StockClassesWitness
namespace Backend.Stock.Proof.CallStaticFixture
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.PerEdgePrep Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm Stock.lower

def count (indirect implicit : Bool) : Nat := if implicit then 1 else if indirect then 2 else 9
def signature (indirect implicit : Bool) : Clif.Signature := {
  params := if implicit then [⟨.i64,.none,.sret⟩] else List.replicate (count indirect implicit) ⟨.i64,.none,.normal⟩
  returns := if implicit then [] else [⟨.i64,.none,.normal⟩,⟨.i64,.none,.normal⟩]
  callConv := some .systemV }
def arguments (indirect implicit : Bool) : List Nat :=
  if implicit then [0] else if indirect then [0,1] else [0,1,2,3,4,5,6,7,8]
def numbers (indirect implicit : Bool) : List Nat := (arguments indirect implicit).map (192+·)
def calleeName : String := "stock_call_static_callee"
def callStatement (indirect implicit : Bool) : Clif.Stmt :=
  ⟨if implicit then [] else [40,41],if indirect then .callIndirect 0 80 (arguments indirect implicit)
    else .call 0 (arguments indirect implicit)⟩
def function (indirect implicit : Bool) : Clif.Function := {
  name := "stock_call_static_complete"
  sig := signature indirect implicit
  sigDecls := [(0,signature indirect implicit)]
  externs := [(0,{name := calleeName,sig := signature indirect implicit,colocated := true})]
  blocks := [{
    id := 0
    params := (arguments indirect implicit).map (fun n => (n,.i64))
    body := (if indirect then [⟨[80],.iconst .i64 4096⟩] else []) ++ [callStatement indirect implicit]
    term := .ret (if implicit then [] else [40,41])}] }
private theorem source_dominated (indirect implicit : Bool) : Dominated (function indirect implicit) := by
  constructor
  · cases indirect <;> cases implicit <;> decide +kernel
  · intro ctx ranges st build bi b found
    cases bi with
    | zero =>
      simp only [function,List.getElem?_cons_zero,Option.some.injEq] at found
      subst b
      constructor
      · intro j stm statement x member
        cases indirect <;> cases implicit
        all_goals rcases j with _ | (_ | j)
        all_goals simp [function,callStatement] at statement
        all_goals subst stm
        all_goals simp [Driver.instArgs,arguments,count] at member
        all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals simp [availOf,function,callStatement,signature,arguments,count,defsBefore,defsFrom]
      · intro x member
        cases indirect <;> cases implicit
        all_goals simp [abiTerm,Driver.termArgs,function,callStatement,signature,sretRet,sigRets,arguments,count] at member
        all_goals rcases member with rfl | rfl
        all_goals simp [availOf,function,callStatement,signature,arguments,count,defsBefore,defsFrom]
    | succ bi => simp [function] at found
  · intro ctx ranges st build tl x incoming notLocal y member
    have bound := (inFix_fixOk (f := function indirect implicit) (ctx := ctx) (gn := id)).cand tl x incoming
    have length : (function indirect implicit).blocks.length = 1 := rfl
    omega

/-- Real direct/indirect ordinary/sret sources retain all original input
conditions. The ordinary direct call has nine arguments and stack traffic. -/
theorem source_conditions (indirect implicit : Bool) :
    LowerScope (function indirect implicit) ∧ Dominated (function indirect implicit) ∧
    ArityOk (function indirect implicit) ∧ sigAbiOk (signature indirect implicit) = true := by
  constructor
  · cases indirect <;> cases implicit <;> apply lowerScope_of <;> decide +kernel
  constructor
  · exact source_dominated indirect implicit
  constructor
  · cases indirect <;> cases implicit <;> apply arityOk_of <;> decide +kernel
  · cases indirect <;> cases implicit <;> decide +kernel
end Backend.Stock.Proof.CallStaticFixture
