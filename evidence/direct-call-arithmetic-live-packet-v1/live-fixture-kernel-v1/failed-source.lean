import FV.E2E.StockLiveCallLayout
import FV.Backend.LinearScan

namespace E2E.LiveCallFixture
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def signature : Clif.Signature := {
  params := [⟨.i64,.none,.normal⟩],returns := [⟨.i64,.none,.normal⟩],callConv := some .systemV }
def callee : Clif.Function := {
  name := "stock_clobber_add",sig := signature
  blocks := [{id := 0,params := [(101,.i64)],
    body := [⟨[109],.iconst .i64 13⟩,⟨[121],.binary .iadd .i64 101 109⟩],term := .ret [121]}] }
def caller : Clif.Function := {
  name := "stock_live_call_add",sig := signature
  externs := [(0,{name := callee.name,sig := signature,colocated := true})]
  blocks := [{id := 0,params := [(7,.i64)],
    body := [⟨[31],.call 0 [7]⟩,⟨[79],.binary .iadd .i64 31 7⟩],term := .ret [79]}] }

def compileCaller (cleanup : Bool) : Except String RFunc := do
  let result ← Stock.lower caller
  if !Stock.LiveCall.check caller result.code then throw "live-call class rejected"
  let prepared ← prepare (Stock.Arithmetic.stage cleanup result.code)
  let allocated ← leanAlloc prepared
  let _ ← checkAlloc prepared allocated
  pure allocated

private def metadataB (cleanup : Bool) (result : Stock.Result) : Bool :=
  Stock.LiveCall.check caller result.code &&
  decide (result.ctx.valueReg? 7 = some (.vreg 192 .int)) &&
  decide (result.ctx.valueReg? 31 = some (.vreg 193 .int)) &&
  decide (result.ctx.valueReg? 79 = some (.vreg 194 .int)) &&
  decide (aliasNum result.final.alias 192 = 192) &&
  decide (aliasNum result.final.alias 193 = 196) &&
  decide (aliasNum result.final.alias 194 = 195) &&
  (compileCaller cleanup).toOption.any (fun allocated => decide (allocated.saved = [.x 19]))
private def observed (cleanup : Bool) : Bool := (Stock.lower caller).toOption.any (metadataB cleanup)
attribute [local irreducible] observed
-- witness: native_decide (actual source, retained maps, checked allocation, and the x19 save only)
private theorem observed_true (cleanup : Bool) : observed cleanup = true := by
  cases cleanup <;> native_decide

private theorem of_any {α : Type} {action : Except String α} {predicate : α → Bool}
    (positive : action.toOption.any predicate = true) : ∃ value,action = .ok value ∧ predicate value = true := by
  cases action with
  | error message => cases positive
  | ok value => exact ⟨value,rfl,positive⟩

/-- The original live parameter has a distinct retained location and an actual saved physical register. -/
-- witness: native_decide (fixed compiler metadata only)
theorem actual_retained_and_saved (cleanup : Bool) :
    ∃ (result : Stock.Result) (allocated : RFunc),Stock.lower caller = .ok result ∧
      Stock.LiveCall.check caller result.code = true ∧
      result.ctx.valueReg? 7 = some (.vreg 192 .int) ∧
      result.ctx.valueReg? 31 = some (.vreg 193 .int) ∧
      result.ctx.valueReg? 79 = some (.vreg 194 .int) ∧
      aliasNum result.final.alias 192 = 192 ∧ aliasNum result.final.alias 193 = 196 ∧
      aliasNum result.final.alias 194 = 195 ∧
      compileCaller cleanup = .ok allocated ∧ allocated.saved = [.x 19] := by
  have positive := observed_true cleanup
  unfold observed at positive
  obtain ⟨result,lowered,metadata⟩ := of_any positive
  simp only [metadataB,Bool.and_eq_true,decide_eq_true_eq,and_assoc] at metadata
  obtain ⟨admitted,live,called,sum,liveAlias,calledAlias,sumAlias,allocation⟩ := metadata
  obtain ⟨allocated,compiled,saved⟩ := of_any allocation
  exact ⟨result,allocated,lowered,admitted,live,called,sum,liveAlias,calledAlias,sumAlias,compiled,
    of_decide_eq_true saved⟩

end E2E.LiveCallFixture
