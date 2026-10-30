import FV.Backend.Proof.StockAliasSemantics

namespace Backend.Stock.Proof.ReturnFixture
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
structure Case where
  sret : Bool
  ty : Clif.Ty
  width : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64
  pointer : sret = true → ty = .i64
  int : ty.isInt = true

def explicitXs (p : Case) : List Nat := if p.sret then [] else [7,31]
def abiXs (p : Case) : List Nat := if p.sret then [7] else [7,31]
def registers (p : Case) : List Reg := if p.sret then [.vreg 192 .int] else [.vreg 192 .int,.vreg 193 .int]
def pins (p : Case) : List Reg := if p.sret then [.x 8] else [.x 0,.x 1]
def function (p : Case) : Clif.Function := {
  name := "stock_return_source_driver"
  sig := {params := if p.sret then [⟨p.ty,.none,.sret⟩] else [⟨p.ty,.none,.normal⟩,⟨p.ty,.none,.normal⟩], returns := if p.sret then [] else [⟨p.ty,.none,.normal⟩,⟨p.ty,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := if p.sret then [(7,p.ty)] else [(7,p.ty),(31,p.ty)],body := [],term := .ret (explicitXs p)}] }
def afterReturn (p : Case) (st : State) : State := {(abiXs p).foldl State.mark st with
  base := ((abiXs p).foldl State.mark st).base.emit (.rets ((registers p).zip (pins p)))}
def Observed (p : Case) : Prop := (Stock.lower (function p)).toOption.map (fun result =>
  decide (aliasNum result.final.alias 192 = 192) && decide (aliasNum result.final.alias 193 = 193) &&
  result.blockScans.toList.any (fun event => event.block == 0 &&
    decide (event.ctx.valueReg? 7 = some (.vreg 192 .int)) && decide (event.ctx.defInst? 7 = none) &&
    (if p.sret then true else decide (event.ctx.valueReg? 31 = some (.vreg 193 .int) ∧ event.ctx.defInst? 31 = none)) &&
    event.output.records.any (fun record => record.inst == 0 && record.output.step.any (fun step => step.decision == .emitted) &&
      decide (record.output.emitted = #[.rets ((registers p).zip (pins p))]) &&
      decide (record.output.state = afterReturn p (scanState record.input record.inst))))) = some true
private def normal (ty : Clif.Ty) (width : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64)
    (int : ty.isInt = true := by decide) : Case := ⟨false,ty,width,(by intro h; cases h),int⟩
private def implicitPointer : Case := ⟨true,.i64,by simp [Clif.Ty.width],fun _ => rfl,rfl⟩
section Kernel
attribute [local semireducible] Isle.Aarch64.program Stock.runTerm
private theorem normal8 : Observed (normal .i8 (by simp [Clif.Ty.width])) := by unfold Observed; decide +kernel
private theorem normal16 : Observed (normal .i16 (by simp [Clif.Ty.width])) := by unfold Observed; decide +kernel
private theorem normal32 : Observed (normal .i32 (by simp [Clif.Ty.width])) := by unfold Observed; decide +kernel
private theorem normal64 : Observed (normal .i64 (by simp [Clif.Ty.width])) := by unfold Observed; decide +kernel
private theorem pointer64 : Observed implicitPointer := by unfold Observed; decide +kernel
end Kernel
/-- Complete original drivers retain the actual ABI return record, its exact
full helper state, source maps and final aliases at every scalar width, plus
the implicit64-bit struct-return case. -/
theorem stock_return_driver_observed (p : Case) : Observed p := by
  rcases p with ⟨sret,ty,width,pointer,int⟩
  cases sret with
  | true =>
    have same := pointer rfl
    subst ty
    exact pointer64
  | false =>
    cases ty
    all_goals first
      | exact normal8
      | exact normal16
      | exact normal32
      | exact normal64
      | (simp at int; done)
      | (simp [Clif.Ty.width] at width; done)
end Backend.Stock.Proof.ReturnFixture
