import FV.Backend.Proof.StockMulRhs
import FV.Backend.Proof.StockMulSemantics
import FV.Backend.Proof.StockSelectionReceipts
namespace Backend.Stock.Proof.ScalarMul
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private theorem stock_sem_extract (ctx : Ctx) (t : Term) (v : V) (st : State) :
    (Stock.sem ctx).extract t v st = Backend.externExtract ctx t v st.base := rfl
private theorem stock_sem_unData (ctx : Ctx) (ty t k : Nat) (fs : List V) :
    (Stock.sem ctx).unData ty (.data t k fs) = if t = ty then some (k,fs) else none := Backend.Proof.sem_unData ctx ty t k fs
section Data
attribute [local semireducible] Isle.Aarch64.program
theorem stock_mul_data {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i x y : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info)
    (clif : info.clif = some (.binary .imul ty x y)) :
    ty.width ≤ 64 ∧ info.data = .data 152 2 [.data 151 77 [], .values [x,y]] ∧
      info.resTys.head? = some (.int ty.width) := by
  have supported := inv.instE i info _ source clif
  have he : eTy ty = true := by
    simpa [Compile.instE,Compile.binaryE,Compile.tyE,eTy] using supported
  have data := inv.data i info _ source clif
  obtain ⟨types, result, typed, len⟩ := inv.resTys i info _ source clif
  simp only [Clif.Inst.resultTypes] at result
  cases result
  refine ⟨eTy_width he, ?_, ?_⟩
  · have shape : instData f (.binary .imul ty x y) =
        .ok (.data 152 2 [.data 151 77 [], .values [x,y]]) := by
      simp only [instData,show binaryOpcode .imul = some "Imul" from rfl,he,ite_true]
      rfl
    exact Except.ok.inj (data.symm.trans shape)
  · rw [typed]; simp [ofClif_int_width (isInt_of_eTy he)]

end Data
/-- The actual Stock multiplication root matches the original instruction data and retains
all scheduling fields; mapping source values to dense registers does not affect matching. -/
theorem stock_mul_match {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    {i x y w : Nat} {info : IInfo} (source : ctx.insts[i]? = some info)
    (type : info.resTys.head? = some (.int w)) (width : w ≤ 64)
    (data : info.data = .data 152 2 [.data 151 77 [], .values [x, y]])
    (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) cfg (n + 2) rule_lower_871 [.inst i]).run (st, tr) =
      .ok (some (env3 (.ty (.int w)) (.value x) (.value y)), st, tr) := by
  have extraction := ext_inst_data_value ctx st.base source
  rw [data, type, Option.getD_some] at extraction
  cases hp
  isel_eval [*, rule_lower_871, stock_sem_extract, stock_sem_unData,
    ext_ty_int_ref_scalar_64_extract ctx st.base width, ext_value_array_2]

private theorem marked (st : State) (x : Nat) (bound : x < st.demand.size) : Demanded (st.mark x) x := by
  rw [Demanded,(mark_demand st x bound).1]
  omega
private theorem twice_marked (st : State) (x y : Nat) (bx : x < st.demand.size) (by_ : y < st.demand.size) :
    Demanded ((st.mark x).mark y) x ∧ Demanded ((st.mark x).mark y) y := by
  have afterBound : y < (st.mark x).demand.size := by rw [(mark_demand st x bx).2.2]; exact by_
  exact ⟨(demanded_mark_iff (st.mark x) y x afterBound).mpr (Or.inr (marked st x bx)),
    marked (st.mark x) y afterBound⟩

/-- The actual selected multiplication root supplies its typed match, requests
and fresh output internally, and computes the original source multiplication. -/
theorem stock_mul_selected_root_values {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {i x y : Nat} {ty : Clif.Ty} {info : IInfo}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.binary .imul ty x y))
    {fr : Clif.Frame} {u v : BitVec ty.width} (sourceX : fr.getAs x ty = .ok u) (sourceY : fr.getAs y ty = .ok v)
    {st next : State} {out : V} {trace : List RuleId} (selected : LowerSelection ctx i st out next trace)
    (chosen : selected.rule = rule_lower_871) {aliases : Array (Option Nat)} {ρ : Nat → CV}
    (bounded : aliases.size ≤ st.base.nextVreg) (extent : ∀ x r,ctx.valueReg? x = some r → x < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun k => ρ (aliasNum aliases k))) :
    ∃ (mi : MInst) (ρ' : Nat → CV), out = .regsVec [[.vreg st.base.nextVreg .int]] ∧
      next.base = (st.base.fresh .int).2.emit mi ∧
      PRun F isem [mi.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1))] ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.binary .imul u v⟩ (ρ' st.base.nextVreg) ∧
      ∀ n,n ≠ st.base.nextVreg → ρ' n = ρ n := by
  obtain ⟨width,data,type⟩ := stock_mul_data inv source clif
  have fuelBound := selected.fuelBound
  have count : (program.rulesOf T.lower.id).length ≤ 999987 := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]; decide +kernel
  have enough : 2 ≤ selected.matchFuel := by omega
  obtain ⟨m,fuelEq⟩ : ∃ m,selected.matchFuel = m+2 := ⟨selected.matchFuel-2,by omega⟩
  have matched := selected.matchedRun
  rw [chosen,fuelEq,stock_mul_match data_program ctx source type width data st #[] m] at matched
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at matched
  obtain ⟨envEq,stateEq,traceEq⟩ := matched
  have rhs := selected.rhsRun
  rw [chosen,← envEq,← stateEq,← traceEq] at rhs
  obtain ⟨safeX,safeY,rx,ry,mx,my,output,state⟩ := stock_mul_rhs_observed data_program ctx rfl width (n := 999959) rhs
  obtain ⟨nx,rfl⟩ := inv.valueReg x rx mx
  obtain ⟨ny,rfl⟩ := inv.valueReg y ry my
  have needed : Demanded next x ∧ Demanded next y := by
    rw [state]
    exact twice_marked st x y (extent x _ mx) (extent y _ my)
  have operands : ValuesHeld (fun z => z = x ∨ z = y) ctx fr (fun k => ρ (aliasNum aliases k)) := by
    apply held.mono
    intro z either
    rcases either with rfl | rfl
    · exact needed.1
    · exact needed.2
  obtain ⟨ρ',execution,value,kept⟩ := stock_mul_resolved refines width bounded mx my operands sourceX sourceY
  exact ⟨.aluRRRR .mAdd (szOf ty.width) (.vreg st.base.nextVreg .int) (.vreg nx .int) (.vreg ny .int) .xzr,
    ρ',output,congrArg State.base state,execution,value,kept⟩

end Backend.Stock.Proof.ScalarMul
