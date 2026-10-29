module

public import FV.Backend.Proof.StockHighMulSourceValues

@[expose] public section

namespace Backend.Stock.Proof.ScalarHighMul.Witness.RunData
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
def function (signed : Bool) (ty : Clif.Ty) : Clif.Function := {
  name := "stock_highmul_values"
  sig := {params := [⟨ty,.none,.normal⟩,⟨ty,.none,.normal⟩],returns := [⟨ty,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(7,ty),(31,ty)],body :=
    [⟨[100],.binary (if signed then .smulhi else .umulhi) ty 7 31⟩],term := .ret [100]}] }
def built (signed : Bool) (ty : Clif.Ty) : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx (function signed ty)).toOption.getD (sinkCtx,#[],sinkState)
def demand : Array Nat := (Array.replicate 101 0).modify 7 (·+1) |>.modify 31 (·+1) |>.modify 100 (·+1)
def sourceKey (info : IInfo) := (info.clif,info.results)
def ctxKey (ctx : Ctx) := (ctx.insts.map sourceKey,ctx.valTy,ctx.valDef,ctx.valReg)

section Runs
attribute [local semireducible] Isle.Aarch64.program Stock.runTerm
theorem observed (signed : Bool) (ty : Clif.Ty) (supported : ty = .i8 ∨ ty = .i16 ∨ ty = .i32 ∨ ty = .i64) :
    (Stock.lower (function signed ty)).toOption.map (fun result =>
      decide (aliasNum result.final.alias 192 = 192) && decide (aliasNum result.final.alias 193 = 193) && result.blockScans.toList.any (fun event =>
        decide (ctxKey event.ctx = ctxKey (built signed ty).1) && event.output.records.any (fun record =>
          record.inst == (0 : Nat) && decide (record.output.state.demand = demand) &&
          record.output.step.any (fun step => step.decision == .emitted && decide (step.rules.getLast? = some (highmulRule signed ty.width).id))))) = some true := by
  cases signed <;> rcases supported with rfl | rfl | rfl | rfl <;> decide +kernel
end Runs
end Backend.Stock.Proof.ScalarHighMul.Witness.RunData
