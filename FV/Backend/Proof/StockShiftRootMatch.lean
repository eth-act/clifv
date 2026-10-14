import FV.Backend.Proof.StockShiftRootValues
import FV.Backend.Proof.StockSelectionReceipts
namespace Backend.Stock.Proof.ScalarShift
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private theorem sem_extract (ctx : Ctx) (t : Term) (v : V) (st : State) :
    (Stock.sem ctx).extract t v st = Backend.externExtract ctx t v st.base := rfl
private theorem sem_unData (ctx : Ctx) (t : Nat) (v : V) :
    (Stock.sem ctx).unData t v = (Backend.sem ctx).unData t v := rfl
private theorem sem_eq (ctx : Ctx) (a b : V) : (Stock.sem ctx).eq a b = (a == b) := rfl
private theorem sem_prim_type (ctx : Ctx) (name : String) :
    (Stock.sem ctx).prim 14 name = (CTy.ofName? name).map V.ty := rfl
section Data
attribute [local semireducible] Isle.Aarch64.program
private theorem source_data {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    (kind : Kind) {i x y : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.binary kind.cop ty x y)) :
    IW ty.width ∧ info.data = .data 152 2 [.data 151 kind.opcode [],.values [x,y]] ∧
      info.resTys.head? = some (.int ty.width) := by
  have accepted := inv.instE i info _ source clif
  have supported : eTy ty = true := by
    cases kind <;> simpa [Kind.cop,Compile.instE,Compile.binaryE,Compile.tyE,eTy] using accepted
  have raw := inv.data i info _ source clif
  obtain ⟨types,result,typed,len⟩ := inv.resTys i info _ source clif
  simp only [Clif.Inst.resultTypes] at result
  cases result
  refine ⟨?_,?_,by rw [typed]; simp [ofClif_int_width]⟩
  · cases ty <;> simp [eTy,Clif.Ty.width,IW] at supported ⊢
  · have expected : instData f (.binary kind.cop ty x y) = .ok (.data 152 2 [.data 151 kind.opcode [],.values [x,y]]) := by
      cases kind <;> simp only [Kind.cop,Kind.opcode,instData,binaryOpcode,supported,ite_true] <;> rfl
    exact Except.ok.inj (raw.symm.trans expected)
end Data

/-- Actual source facts determine all six scalar root matches, including
rejection of the other width case, with unchanged complete state and trace. -/
theorem stock_shift_root_match {p : Program} (hp : Data p) (ctx : Ctx) (kind : Kind) (wide : Bool)
    {i x y w : Nat} {info : IInfo} (source : ctx.insts[i]? = some info)
    (type : info.resTys.head? = some (.int w))
    (data : info.data = .data 152 2 [.data 151 kind.opcode [],.values [x,y]])
    (st : State) (tr : Array RuleId) (m : Nat) :
    (matchRule p (Stock.sem ctx) {} (m+10) (kind.rule wide) [.inst i]).run (st,tr) =
      .ok ((if (if wide then w = 64 else w ≤ 32) then some (rootEnv wide w x y) else none),st,tr) := by
  have extraction := ext_inst_data_value ctx st.base source
  rw [data,type,Option.getD_some] at extraction
  have values := ext_value_array_2 ctx st.base x y
  have fits := ext_fits_in_32 ctx st.base w
  cases wide
  · by_cases small : w ≤ 32
    all_goals simp only [small,ite_true,ite_false] at fits ⊢
    all_goals cases hp
    all_goals cases kind <;> isel_eval [*,Kind.rule,Kind.opcode,rootEnv,rule_lower_1545,rule_lower_1638,rule_lower_1695,sem_extract,sem_unData]
  · by_cases large : w = 64
    · subst w
      cases hp
      cases kind <;> isel_eval [*,Kind.rule,Kind.opcode,rootEnv,rule_lower_1549,rule_lower_1642,rule_lower_1699,sem_extract,sem_unData,sem_eq,sem_prim_type]
    · have different : (V.ty (.int w) == V.ty (.int 64)) = false := by simp [large]
      cases hp
      cases kind <;> isel_eval [*,Kind.rule,Kind.opcode,rootEnv,rule_lower_1549,rule_lower_1642,rule_lower_1699,sem_extract,sem_unData,sem_eq,sem_prim_type]

/-- Every actual selected scalar shift root derives its width gate and
canonical environment internally from original mapped source data. -/
theorem stock_shift_selected_root_values {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem) (kind : Kind) (wide : Bool)
    {i x y : Nat} {info : IInfo} {ty : Clif.Ty} (source : ctx.insts[i]? = some info)
    (clif : info.clif = some (.binary kind.cop ty x y))
    {fr : Clif.Frame} (dfg : DFGCons ctx fr) {u : BitVec ty.width} {amount : Clif.Val}
    (getX : fr.getAs x ty = .ok u) (getY : fr.regs y = some amount)
    {st next : State} {out : V} {rules : List RuleId} (selected : LowerSelection ctx i st out next rules)
    (chosen : selected.rule = kind.rule wide) {aliases : Array (Option Nat)} {ρ : Nat → CV}
    (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ x r,ctx.valueReg? x = some r → x < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun z => ρ (aliasNum aliases z)))
    (outsideX : ∀ a,ctx.valueReg? x = some (.vreg a .int) → aliasNum aliases a < st.base.nextVreg ∨ next.base.nextVreg ≤ aliasNum aliases a)
    (outsideY : ∀ a,ctx.valueReg? y = some (.vreg a .int) → aliasNum aliases a < st.base.nextVreg ∨ next.base.nextVreg ≤ aliasNum aliases a) :
    ShiftRootValueOut F isem kind ty u amount st next out aliases ρ := by
  obtain ⟨width,data,type⟩ := source_data inv kind source clif
  have enough := selected.fuelBound
  have count : (program.rulesOf T.lower.id).length = 517 := by rw [show T.lower.id = 686 from rfl,data_program.r686]; rfl
  obtain ⟨m,fuelEq⟩ : ∃ m,selected.matchFuel = m+10 := ⟨selected.matchFuel-10,by omega⟩
  have matched := selected.matchedRun
  rw [chosen,fuelEq,stock_shift_root_match data_program ctx kind wide source type data st #[] m] at matched
  by_cases gate : (if wide then ty.width = 64 else ty.width ≤ 32)
  · rw [if_pos gate] at matched
    simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at matched
    obtain ⟨envEq,stateEq,traceEq⟩ := matched
    have rhs := selected.rhsRun
    rw [chosen,← envEq,← stateEq,← traceEq] at rhs
    exact stock_shift_root_values inv refines kind wide width gate dfg getX getY bounded extent held outsideX outsideY rhs
  · rw [if_neg gate] at matched
    cases matched
end Backend.Stock.Proof.ScalarShift
