import FV.Backend.Proof.StockExtendValues
import FV.Backend.Proof.IselCmpDivRoot
namespace Backend.Stock.Proof.ScalarDiv
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
private theorem ext_location {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {x to : Nat} {pass : List CTy} {sg : Bool} {st next : State} {out : V} {d : Nat}
    (shape : ScalarShift.MappedExtOut ctx x sg to pass st next out)
    (output : out = .reg (.vreg d .int)) :
    ctx.valueReg? x = some (.vreg d .int) ∨ st.base.nextVreg ≤ d ∧ d < next.base.nextVreg := by
  obtain ⟨t,typed,safe,rx,mapped,form⟩ := shape
  obtain ⟨nx,rfl⟩ := inv.valueReg x rx mapped
  rcases form with ⟨_,equal,rfl⟩ | ⟨_,_,equal,rfl⟩
  · rw [equal] at output; cases output; exact Or.inl mapped
  · change out = .reg (.vreg st.base.nextVreg .int) at equal
    rw [equal] at output; cases output
    right
    simp only [State.mark,LState.fresh,LState.emit]
    omega
def DividendValueOut (F : BitVec 64 → Prop) (isem : Backend.Proof.Sem) (ctx : Ctx) (x : Nat) (sg : Bool)
    (ty : Clif.Ty) (u : BitVec ty.width) (st next : State) (out : V)
    (aliases : Array (Option Nat)) (ρ : Nat → CV) : Prop :=
  ∃ ms d ρ',out = .reg (.vreg d .int) ∧ Frag st.base next.base ms ∧
    (ctx.valueReg? x = some (.vreg d .int) ∨ st.base.nextVreg ≤ d ∧ d < next.base.nextVreg) ∧
    PRun F isem (ms.map (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ ρ' ∧
    DivOpnd sg u (ρ' (aliasNum aliases d)) ∧
    ∀ k,k < st.base.nextVreg ∨ next.base.nextVreg ≤ k → ρ' k = ρ k
/-- Actual signed/unsigned dividend widening derives original division operands
and complete fresh-write preservation, through original source getters and final
aliases. The wide/narrow relation follows the source rule's canonical type match. -/
theorem stock_div_extended_dividend_values {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (sg wide : Bool) {n x : Nat} (enough : 60 ≤ n) {fr : Clif.Frame} (dfg : DFGCons ctx fr)
    {ty : Clif.Ty} {u : BitVec ty.width} (get : fr.getAs x ty = .ok u)
    (width : if wide then ty.width = 64 else ty.width ≤ 32)
    {st next : State} {out : V} {tr trace : Array RuleId} {aliases : Array (Option Nat)} {ρ : Nat → CV}
    (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ x r,ctx.valueReg? x = some r → x < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun k => ρ (aliasNum aliases k)))
    (run : ApplyInternal p (Stock.sem ctx) {} n 27 (ScalarShift.extTerm sg wide) [.value x] (st,tr) out (next,trace)) :
    DividendValueOut F isem ctx x sg ty u st next out aliases ρ := by
  have shape : ScalarShift.MappedExtOut ctx x sg (ScalarShift.extTarget wide) (ScalarShift.extPass wide) st next out := by
    cases wide <;> cases sg
    · exact ScalarShift.stock_zext32_out hp rfl enough run
    · exact ScalarShift.stock_sext32_out hp rfl enough run
    · exact ScalarShift.stock_zext64_out hp rfl enough run
    · exact ScalarShift.stock_sext64_out hp rfl enough run
  obtain ⟨ms,d,ρ',output,emitted,mono,defs,execution,value,kept⟩ :=
    ScalarShift.stock_ext_helper_values hp inv refines sg wide enough dfg get bounded extent held run
  have operand : DivOpnd sg u (ρ' (aliasNum aliases d)) := by
    cases wide
    · simp only [Bool.false_eq_true,ite_false] at width
      unfold DivOpnd
      simp only [width,ite_true]
      exact value.2 (by simp [ScalarShift.extTarget]; omega)
    · simp only [ite_true] at width
      exact divOpnd_of_vholds64 width value.1
  exact ⟨ms,d,ρ',output,⟨emitted,mono,defs⟩,ext_location inv shape output,execution,operand,kept⟩
/-- The actual64-bit unsigned dividend register request derives the original
operand and empty fragment, preserving the complete machine register file. -/
theorem stock_div_plain_dividend_values {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} {fr : Clif.Frame} {x : Nat}
    {u : BitVec 64} (get : fr.getAs x .i64 = .ok u)
    {st next : State} {out : V} {aliases : Array (Option Nat)} {ρ : Nat → CV}
    (extent : ∀ x r,ctx.valueReg? x = some r → x < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun k => ρ (aliasNum aliases k)))
    (run : Stock.externCtor ctx T.put_in_reg [.value x] st = .ok (out,next)) :
    DividendValueOut F isem ctx x false .i64 u st next out aliases ρ := by
  obtain ⟨safe,r,mapped,rfl,rfl⟩ := (stock_put_in_reg_iff ctx st x out next).mp run
  obtain ⟨d,rfl⟩ := inv.valueReg x r mapped
  have needed : Demanded (st.mark x) x := by
    rw [Demanded,(mark_demand st x (extent x _ mapped)).1]
    omega
  have operand : DivOpnd false u (ρ (aliasNum aliases d)) :=
    divOpnd_of_vholds64 rfl (held.read needed (getAs_ok get) mapped)
  exact ⟨[],d,ρ,rfl,⟨by simp [State.mark],Nat.le_refl _,by simp⟩,Or.inl mapped,
    prun_nil _,operand,fun _ _ => rfl⟩
end Backend.Stock.Proof.ScalarDiv
