import FV.Backend.Proof.StockMulFusedSemantics
import FV.Backend.Proof.StockMulFusedMatch
namespace Backend.Stock.Proof.ScalarMul.Fused
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private theorem marked (st : State) (x : Nat) (bound : x < st.demand.size) : Demanded (st.mark x) x := by
  rw [Demanded,(mark_demand st x bound).1]
  omega
private theorem three_marked (st : State) (a b x : Nat)
    (ba : a < st.demand.size) (bb : b < st.demand.size) (bx : x < st.demand.size) :
    Demanded (((st.mark a).mark b).mark x) a ∧
      Demanded (((st.mark a).mark b).mark x) b ∧ Demanded (((st.mark a).mark b).mark x) x := by
  have bb' : b < (st.mark a).demand.size := by simpa only [State.mark,Array.size_modify] using bb
  have bx' : x < ((st.mark a).mark b).demand.size := by simpa only [State.mark,Array.size_modify] using bx
  have aFirst := (demanded_mark_iff (st.mark a) b a bb').mpr (Or.inr (marked st a ba))
  exact ⟨(demanded_mark_iff ((st.mark a).mark b) x a bx').mpr (Or.inr aFirst),
    (demanded_mark_iff ((st.mark a).mark b) x b bx').mpr (Or.inr (marked (st.mark a) b bb')),
    marked ((st.mark a).mark b) x bx'⟩

/-- Actual selected multiply-add/subtract roots establish the original binary
source result. Hidden multiplication values come from restricted source DFG,
while every machine operand and its demand comes from the successful RHS. -/
theorem stock_mul_fused_selected_root_values {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (fusion : Fusion) {i x z : Nat} {ty : Clif.Ty} {info : IInfo}
    (source : ctx.insts[i]? = some info)
    (clif : info.clif = some (.binary fusion.cop ty (if fusion.left then z else x) (if fusion.left then x else z)))
    {fr : Clif.Frame} (dfg : DFGCons ctx fr) {t product : BitVec ty.width}
    (sourceX : fr.getAs x ty = .ok t) (sourceZ : fr.getAs z ty = .ok product)
    {st next : State} {out : V} {trace : List RuleId} (selected : LowerSelection ctx i st out next trace)
    (chosen : selected.rule = fusion.rule) {aliases : Array (Option Nat)} {ρ : Nat → CV}
    (bounded : aliases.size ≤ st.base.nextVreg) (extent : ∀ x r,ctx.valueReg? x = some r → x < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun k => ρ (aliasNum aliases k))) :
    ∃ (mi : MInst) (ρ' : Nat → CV), out = .regsVec [[.vreg st.base.nextVreg .int]] ∧
      next.base = (st.base.fresh .int).2.emit mi ∧
      PRun F isem [mi.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1))] ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.binary fusion.cop (if fusion.left then product else t) (if fusion.left then t else product)⟩
        (ρ' st.base.nextVreg) ∧ ∀ n,n ≠ st.base.nextVreg → ρ' n = ρ n := by
  have fuelBound := selected.fuelBound
  have count : (program.rulesOf T.lower.id).length ≤ 999987 := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]; decide +kernel
  have enough : 10 ≤ selected.matchFuel := by omega
  obtain ⟨m,fuelEq⟩ : ∃ m,selected.matchFuel = m+10 := ⟨selected.matchFuel-10,by omega⟩
  have matched := selected.matchedRun
  rw [chosen,fuelEq] at matched
  obtain ⟨width,a,b,u,v,envEq,stateEq,getA,getB,productValue⟩ :=
    stock_mul_fused_match_receipts data_program inv fusion source clif dfg sourceZ matched
  have rhs := selected.rhsRun
  rw [chosen,envEq,stateEq] at rhs
  obtain ⟨safeA,safeB,safeX,ra,rb,rx,ma,mb,mx,output,state⟩ :=
    stock_mul_fused_rhs_observed data_program ctx fusion width (n := 999959) rhs
  obtain ⟨na,rfl⟩ := inv.valueReg a ra ma
  obtain ⟨nb,rfl⟩ := inv.valueReg b rb mb
  obtain ⟨nx,rfl⟩ := inv.valueReg x rx mx
  have needed : Demanded next a ∧ Demanded next b ∧ Demanded next x := by
    rw [state]
    exact three_marked st a b x (extent a _ ma) (extent b _ mb) (extent x _ mx)
  have operands : ValuesHeld (fun z => z = a ∨ z = b ∨ z = x) ctx fr (fun k => ρ (aliasNum aliases k)) := by
    apply held.mono
    intro z either
    rcases either with rfl | rfl | rfl
    · exact needed.1
    · exact needed.2.1
    · exact needed.2.2
  obtain ⟨ρ',execution,value,kept⟩ := stock_mul_fused_resolved refines fusion width bounded ma mb mx operands getA getB sourceX
  have original : (if fusion.subtract then t-u*v else t+u*v) =
      Clif.Sem.binary fusion.cop (if fusion.left then product else t) (if fusion.left then t else product) := by
    rw [productValue]
    cases fusion <;> simp [Fusion.cop,Fusion.subtract,Fusion.left,Clif.Sem.binary,Clif.Sem.iadd,Clif.Sem.isub,Clif.Sem.imul,BitVec.add_comm]
  rw [original] at value
  exact ⟨.aluRRRR fusion.op (szOf ty.width) (.vreg st.base.nextVreg .int) (.vreg na .int) (.vreg nb .int) (.vreg nx .int),
    ρ',output,congrArg State.base state,execution,value,kept⟩
end Backend.Stock.Proof.ScalarMul.Fused
