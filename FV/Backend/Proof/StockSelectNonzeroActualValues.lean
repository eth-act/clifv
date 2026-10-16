import FV.Backend.Proof.StockSelectNonzero8Values
import FV.Backend.Proof.StockSelectNonzero16Values
import FV.Backend.Proof.StockSelectNonzeroWideValues
namespace Backend.Stock.Proof.ScalarSelect
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
/-- Every scalar original nonzero condition and actual659 select computes the
original selected source value. Width cases are internal; the retained caller
derives the source availability separation needed by the16-bit scratch case. -/
theorem stock_select_nonzero_actual_source_values {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {cty ty : Clif.Ty}
    (conditionWidth : cty.width = 8 ∨ cty.width = 16 ∨ cty.width = 32 ∨ cty.width = 64)
    (width : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64)
    {fr : Clif.Frame} (dfg : DFGCons ctx fr) {c x y : Nat} {test : BitVec cty.width} {u v : BitVec ty.width}
    (getC : fr.getAs c cty = .ok test) (getX : fr.getAs x ty = .ok u) (getY : fr.getAs y ty = .ok v)
    (typed : ctx.valueType? c = some (.int cty.width))
    {emitFuel selectFuel : Nat} (enoughEmit : 220 ≤ emitFuel) (enoughSelect : 319 ≤ selectFuel)
    {st middle next : State} {tr emitterTrace trace : Array RuleId} {condition out : V}
    (empty : st.base.emitted = #[])
    (emitter : ApplyInternal program (Stock.sem ctx) {} emitFuel 123 651 [.value c]
      (st,tr) condition (middle,emitterTrace))
    {consumerStart : Array RuleId}
    (consumer : ApplyInternal program (Stock.sem ctx) {} selectFuel 22 659
      [.ty (.int ty.width),condition,.value x,.value y] (middle,consumerStart) out (next,trace))
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ value r,ctx.valueReg? value = some r → value < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun key => ρ (aliasNum aliases key)))
    (outsideX : ∀ key,ctx.valueReg? x = some (.vreg key .int) →
      aliasNum aliases key < st.base.nextVreg ∨ next.base.nextVreg ≤ aliasNum aliases key)
    (outsideY : ∀ key,ctx.valueReg? y = some (.vreg key .int) →
      aliasNum aliases key < st.base.nextVreg ∨ next.base.nextVreg ≤ aliasNum aliases key) :
    ∃ d code,out = .regs [.vreg d .int] ∧ st.base.nextVreg ≤ d ∧ d < next.base.nextVreg ∧
      Frag st.base next.base code ∧
      ∀ world,Runs F isem (code.map (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world
        (fun final _ => VHolds ⟨ty,if test != 0 then u else v⟩ (final d) ∧
          ∀ k,k < st.base.nextVreg ∨ next.base.nextVreg ≤ k → final k = ρ k) := by
  cases cty
  case i8 =>
    obtain ⟨key,nx,ny,d,_,_,_,output,lower,upper,fragment,execution⟩ := stock_select_nonzero8_source_values inv width
      getC getX getY typed enoughEmit enoughSelect emitter consumer refines bounded extent held
    refine ⟨d,_,output,lower,upper,fragment,fun world => (execution world).imp ?_⟩
    intro final _ _ pair
    exact ⟨pair.1,fun k h => pair.2 k (by rcases h with h | h <;> omega)⟩
  case i16 =>
    obtain ⟨key,nx,ny,_,_,_,output,frontier,fragment,execution⟩ := stock_select_nonzero16_source_values inv width dfg
      getC getX getY typed enoughEmit enoughSelect empty emitter consumer refines bounded extent held outsideX outsideY
    exact ⟨st.base.nextVreg+1,_,output,by omega,by omega,fragment,execution⟩
  case i32 =>
    obtain ⟨key,nx,ny,d,_,_,_,output,lower,upper,fragment,execution⟩ := stock_select_nonzero_wide_source_values inv false width
      getC getX getY typed enoughEmit enoughSelect emitter consumer refines bounded extent held
    refine ⟨d,_,output,lower,upper,fragment,fun world => (execution world).imp ?_⟩
    intro final _ _ pair
    exact ⟨pair.1,fun k h => pair.2 k (by rcases h with h | h <;> omega)⟩
  case i64 =>
    obtain ⟨key,nx,ny,d,_,_,_,output,lower,upper,fragment,execution⟩ := stock_select_nonzero_wide_source_values inv true width
      getC getX getY typed enoughEmit enoughSelect emitter consumer refines bounded extent held
    refine ⟨d,_,output,lower,upper,fragment,fun world => (execution world).imp ?_⟩
    intro final _ _ pair
    exact ⟨pair.1,fun k h => pair.2 k (by rcases h with h | h <;> omega)⟩
  case i128 => simp [Clif.Ty.width] at conditionWidth
end Backend.Stock.Proof.ScalarSelect
