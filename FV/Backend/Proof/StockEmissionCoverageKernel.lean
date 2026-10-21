import FV.Backend.Proof.StockEmissionStatic
import FV.Backend.Proof.PerEdgeAllocDriverSound
import FV.Backend.Proof.LowerDecide
import FV.Backend.Proof.SpillArity

namespace Backend.Stock.Proof.EmissionCoverageFixture
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.PerEdgePrep
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000

def function (branch : Bool) : Clif.Function := if branch then {
  name := "stock_emission_branch_coverage"
  sig := {params := [⟨.i64,.none,.normal⟩,⟨.i64,.none,.normal⟩],returns := [⟨.i64,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(7,.i64),(13,.i64)],body := [⟨[17],.icmp .eq .i64 7 13⟩],term := .brif 17 ⟨1,[7]⟩ ⟨2,[7]⟩},
    {id := 1,params := [(31,.i64)],term := .ret [31]}, {id := 2,params := [(47,.i64)],term := .ret [47]}] }
  else {name := "stock_emission_statement_coverage"
        sig := {returns := [⟨.i64,.none,.normal⟩],callConv := some .systemV}
        blocks := [{id := 0,body := [⟨[7],.iconst .i64 9⟩],term := .ret [7]}]}

def rootCtx (branch : Bool) (ctx : Ctx) : Ctx := if branch then
  Driver.termCtx ctx 1 ((Backend.termData (.brif 17 ⟨1,[7]⟩ ⟨2,[7]⟩)).toOption.getD (.op .unit)) else ctx

def rootName (branch : Bool) : String := if branch then "lower_branch" else "lower"
def rootArgs (branch : Bool) : List Backend.V := if branch then [.inst 1,.labels [2,1]] else [.inst 0]

structure Data where
  result : Result
  prepared : EdgeVCode
  rf : RFunc
  af : AFunc
  out : Backend.V
  after : State
  trace : List Isle.RuleId

def pipeline (branch : Bool) : Except String Data := do
  let result ← Stock.lower (function branch)
  let prepared ← prepareAt result.code result.edgeArgs
  let rf ← allocResultAt prepared.code prepared.edges (.error "force emission-coverage fallback")
  let af ← lowerRFunc prepared.code rf
  let (out,after,trace) ← Stock.runTerm (rootCtx branch result.ctx) (rootName branch) (rootArgs branch) result.initial
  let some out := out | throw "missing named output"
  pure ⟨result,prepared,rf,af,out,after,trace⟩

def Observed (branch : Bool) : Prop := (pipeline branch).toOption.map
  (fun q => decide (q.result.initial.base.emitted = #[] ∧ q.after.base.emitted.any (fun i => !i.isCtl) = true)) = some true
section Kernel
theorem emission_observed (branch : Bool) : Observed branch := by
  cases branch <;> unfold Observed pipeline <;> decide +kernel
end Kernel


end Backend.Stock.Proof.EmissionCoverageFixture
