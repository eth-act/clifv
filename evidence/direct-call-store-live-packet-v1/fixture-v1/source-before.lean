import FV.Backend.Lowering.StockArithmetic
import FV.Backend.Proof.StockCallStoreResult
import FV.Backend.LinearScan
import FV.Clif.Parse

namespace E2E.CallStoreFixture
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def calleeSignature : Clif.Signature := {
  params := [⟨.i64,.none,.normal⟩],returns := [⟨.i64,.none,.normal⟩],callConv := some .systemV }
def callerSignature : Clif.Signature := {calleeSignature with params := [⟨.i64,.none,.normal⟩,⟨.i64,.none,.normal⟩]}
def callee : Clif.Function := {
  name := "stock_store_clobber",sig := calleeSignature
  blocks := [{id := 0,params := [(101,.i64)],body := [⟨[109],.iconst .i64 13⟩,⟨[121],.binary .iadd .i64 101 109⟩],term := .ret [121]}] }
def caller : Clif.Function := {
  name := "stock_call_store_live",sig := callerSignature
  externs := [(0,{name := callee.name,sig := calleeSignature,colocated := true})]
  blocks := [{id := 0,params := [(7,.i64),(11,.i64)],
    body := [⟨[31],.call 0 [11]⟩,⟨[],.store .store .i64 {} 31 7 8⟩],term := .ret [31]}] }

def callerText : String := "function %stock_call_store_live(i64, i64) -> i64 system_v {\n    fn0 = colocated %stock_store_clobber(i64) -> i64 system_v\nblock0(v7: i64, v11: i64):\n    v31 = call fn0(v11)\n    store v31, v7+8\n    return v31\n}\n"
def calleeText : String := "function %stock_store_clobber(i64) -> i64 system_v {\nblock0(v101: i64):\n    v109 = iconst.i64 13\n    v121 = iadd v101, v109\n    return v121\n}\n"

-- witness: native_decide (the fixed source parser input only)
theorem original_source_exact :
    ((Clif.parseFile callerText).funcs[0]?).bind (fun parsed => parsed.func.toOption) = some caller ∧
    ((Clif.parseFile calleeText).funcs[0]?).bind (fun parsed => parsed.func.toOption) = some callee := by
  native_decide

def compileCaller (cleanup : Bool) : Except String RFunc := do
  let result ← Stock.lower caller
  let prepared ← prepare (Stock.Arithmetic.stage cleanup result.code)
  let allocated ← leanAlloc prepared
  let _ ← checkAlloc prepared allocated
  pure allocated

private def allocatedB (allocated : RFunc) : Bool :=
  decide (allocated.saved = [.x 19]) && allocated.blocks.toList.any (fun block =>
    block.toList.any (fun item => decide (item = .op 2 #[.reg (.x 0),.reg (.x 19)])))
private def metadataB (cleanup : Bool) (result : Stock.Result) : Bool :=
  decide (result.ctx.valueReg? 7 = some (.vreg 192 .int)) &&
  decide (result.ctx.valueReg? 11 = some (.vreg 193 .int)) &&
  decide (result.ctx.valueReg? 31 = some (.vreg 194 .int)) &&
  decide (aliasNum result.final.alias 192 = 192) &&
  decide (aliasNum result.final.alias 194 = 195) &&
  (compileCaller cleanup).toOption.any allocatedB
private def observed (cleanup : Bool) : Bool := (Stock.lower caller).toOption.any (metadataB cleanup)
attribute [local irreducible] observed
-- witness: native_decide (fixed source, retained aliases, checked allocation, and pointer-save metadata only)
private theorem observed_true (cleanup : Bool) : observed cleanup = true := by
  cases cleanup <;> native_decide

private theorem of_any {α : Type} {action : Except String α} {predicate : α → Bool}
    (positive : action.toOption.any predicate = true) : ∃ value,action = .ok value ∧ predicate value = true := by
  cases action with
  | error message => cases positive
  | ok value => exact ⟨value,rfl,positive⟩

/-- Both real allocations retain the original pointer in x19 and store the actual x0 call result. -/
-- witness: native_decide (fixed retained compiler and allocation metadata only)
theorem actual_retained_and_saved (cleanup : Bool) :
    ∃ (result : Stock.Result) (allocated : RFunc),Stock.lower caller = .ok result ∧
      result.ctx.valueReg? 7 = some (.vreg 192 .int) ∧
      result.ctx.valueReg? 11 = some (.vreg 193 .int) ∧
      result.ctx.valueReg? 31 = some (.vreg 194 .int) ∧
      aliasNum result.final.alias 192 = 192 ∧ aliasNum result.final.alias 194 = 195 ∧
      compileCaller cleanup = .ok allocated ∧ allocated.saved = [.x 19] ∧
      ∃ block,block ∈ allocated.blocks.toList ∧ .op 2 #[.reg (.x 0),.reg (.x 19)] ∈ block.toList := by
  have positive := observed_true cleanup
  unfold observed at positive
  obtain ⟨result,lowered,metadata⟩ := of_any positive
  simp only [metadataB,Bool.and_eq_true,decide_eq_true_eq,and_assoc] at metadata
  obtain ⟨pointer,argument,value,pointerAlias,resultAlias,allocation⟩ := metadata
  obtain ⟨allocated,compiled,saved⟩ := of_any allocation
  simp only [allocatedB,Bool.and_eq_true,decide_eq_true_eq,List.any_eq_true] at saved
  obtain ⟨saved,block,member,item,present,equal⟩ := saved
  subst item
  exact ⟨result,allocated,lowered,pointer,argument,value,pointerAlias,resultAlias,compiled,saved,
    block,member,present⟩

end E2E.CallStoreFixture
