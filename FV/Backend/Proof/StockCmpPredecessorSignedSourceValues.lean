import FV.Backend.Proof.StockCmpPredecessorSignedEmission
import FV.Backend.Proof.StockDivConstantSource
import FV.Backend.Proof.IselCmpDivRoot
import FV.Backend.Proof.IselFamALUA
import FV.Backend.Proof.StockCmpConditionValues
import FV.Backend.Proof.StockDemandMono
namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
private theorem operand_of_value {ty : Clif.Ty} (width : ty.width = 32 ∨ ty.width = 64)
    {u : BitVec ty.width} {A : CV} (sg : Bool) (held : VHolds ⟨ty,u⟩ A) : DivOpnd sg u A := by
  cases ty <;> simp only [Clif.Ty.width] at width
  all_goals try (omega)
  all_goals first
    | exact divOpnd_of_vholds64 rfl held
    | change BitVec 32 at u
      change A.setWidth 32 = u at held
      have signed : u.signExtend 32 = u := BitVec.signExtend_eq u
      have unsigned : u.setWidth 32 = u := BitVec.setWidth_eq u
      change (lo64 A).setWidth 32 = (if sg then u.signExtend 32 else u.setWidth 32)
      rw [signed,unsigned,ite_self]
      change (A.setWidth 64).setWidth 32 = u
      rw [BitVec.setWidth_setWidth_of_le A (by decide)]
      exact held
/-- The immediate producer is tied to the original defining constant through
restricted DFG consistency; that constant need not occupy a machine register. -/
theorem stock_cmp_predecessor_signed_condition_source_values {p : Program} (hp : Data p)
    {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx) 
    {ty : Clif.Ty} (width : ty.width = 32 ∨ ty.width = 64)
    {fr : Clif.Frame} (dfg : DFGCons ctx fr) {x y j : Nat} {info : IInfo} {i : Int}
    {u v : BitVec ty.width} (getX : fr.getAs x ty = .ok u) (getY : fr.getAs y ty = .ok v)
    (defined : ctx.defInst? y = some j) (found : ctx.insts[j]? = some info)
    (data : info.data = .data 152 35 [.data 151 57 [],.int i])
    {imm : Imm12} (encoded : Imm12.ofNat? (u64 (i-1)) = some imm)
    (odd : u64 i % 2 = 1)
    {st middle next : State} {tr emitTrace conditionStart trace : Array RuleId}
    {n fuel : Nat} {condition out : V} (enough : 119 ≤ fuel)
    (emitter : (evalExpr p (Stock.sem ctx) {} (n+100) rule_inst_5160.rhs
      #[some (.ty (.int (szOf ty.width).bits)),some (.value x),some (.int i),some (.op (.imm12 imm))]).run
      (st,tr) = .ok (some condition,middle,emitTrace))
    (conditionCall : ApplyInternal p (Stock.sem ctx) {} fuel 27 715 [condition]
      (middle,conditionStart) out (next,trace))
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ z r,ctx.valueReg? z = some r → z < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun key => ρ (aliasNum aliases key))) :
    ∃ nx d,ctx.valueReg? x = some (.vreg nx .int) ∧ out = .reg (.vreg d .int) ∧
      st.base.nextVreg ≤ d ∧ d < next.base.nextVreg ∧
      Frag st.base next.base [.aluRRImm12 .subS (szOf ty.width) .xzr (.vreg nx .int) imm,
        .cset (.vreg d .int) (condOf .sgt)] ∧
      ∀ world,Runs F isem ([MInst.aluRRImm12 .subS (szOf ty.width) .xzr (.vreg nx .int) imm,
        .cset (.vreg d .int) (condOf .sgt)].map
        (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world (fun ρ' _ =>
          VHolds ⟨.i8,Clif.Sem.bool8 (Clif.Sem.intcc .sge u v)⟩ (ρ' d) ∧ ∀ k,k ≠ d → ρ' k = ρ k) := by
  obtain ⟨_,constant⟩ := ScalarDiv.stock_div_constant_source_value inv dfg getY defined found data
  obtain ⟨literal,validImm⟩ := imm12_ofNat_value encoded (u64_lt (i-1))
  have originalLiteral : u64 i = v.toNat := by
    rw [constant]
    exact u64_imm64OfIconst (ty := ty) (c := v) (by omega)
  have word : BitVec.ofInt ty.width i = v := by
    rw [← ofNat_u64_le (w := ty.width) (by omega),originalLiteral,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  have encodedWord : BitVec.ofNat ty.width imm.value = v-1 := by
    rw [literal,ofNat_u64_le (w := ty.width) (by omega),show i-1=i+(-1) from by omega,BitVec.ofInt_add,word]
    simp [BitVec.ofInt_neg,BitVec.sub_eq_add_neg]
  have oddV : v.toNat % 2 = 1 := by rw [← originalLiteral]; exact odd
  have nonzero : v ≠ 0 := by
    intro zero; rw [zero] at oddV; cases oddV
  have notMinimum : v ≠ BitVec.intMin ty.width := by
    have even : (BitVec.intMin ty.width).toNat % 2 = 0 := by
      rcases width with h | h <;> rw [h] <;> decide +kernel
    intro minimum; rw [minimum,even] at oddV; cases oddV
  obtain ⟨safeX,rx,mapX,producer,finish⟩ := stock_cmp_predecessor_signed_rhs_observed hp ctx rfl (szOf ty.width) emitter
  obtain ⟨nx,rfl⟩ := inv.valueReg x rx mapX
  have conditionDemand := stock_apply_demand_mono conditionCall
  have neededX : Demanded next x := by
    have marked := (mark_demand st x (extent x _ mapX)).1
    have done := conditionDemand x
    rw [finish] at done
    unfold Demanded
    omega
  have inputX := operand_of_value width (signedCC .sgt) (held.read neededX (getAs_ok getX) mapX)
  have truth : condOn (condOf .sgt).bits
      (cmpFlags (opnd (szOf ty.width) (ρ (aliasNum aliases nx)))
        (BitVec.ofNat (szOf ty.width).bits imm.value)) = Clif.Sem.intcc .sge u v := by
    cases ty <;> simp only [Clif.Ty.width] at width
    all_goals try omega
    all_goals simp only [Clif.Ty.width] at *
    all_goals first
      | change BitVec 32 at u v
        change (lo64 (ρ (aliasNum aliases nx))).setWidth 32 =
          (if signedCC .sgt then u.signExtend 32 else u.setWidth 32) at inputX
        simp only [BitVec.signExtend_eq,BitVec.setWidth_eq,ite_self] at inputX
        change condOn (condOf .sgt).bits (cmpFlags
          ((lo64 (ρ (aliasNum aliases nx))).setWidth 32) (BitVec.ofNat 32 imm.value)) = _
        rw [encodedWord,inputX]
        exact stock_cmp_signed_predecessor (Or.inl rfl) u v notMinimum
      | change BitVec 64 at u v
        change lo64 (ρ (aliasNum aliases nx)) = u.setWidth 64 at inputX
        simp only [BitVec.setWidth_eq] at inputX
        change condOn (condOf .sgt).bits (cmpFlags
          ((lo64 (ρ (aliasNum aliases nx))).setWidth 64) (BitVec.ofNat 64 imm.value)) = _
        rw [encodedWord,inputX,BitVec.setWidth_eq]
        exact stock_cmp_signed_predecessor (Or.inr rfl) u v notMinimum
  have flags := setsFlags_cmpImm (szOf ty.width) nx validImm (fun key => ρ (aliasNum aliases key))
  rw [producer] at conditionCall
  have decoded : MInst.ofV (.data 58 4 [.data 59 10 [],
      .data 93 (if szOf ty.width = .size32 then 0 else 1) [],.reg .xzr,.reg (.vreg nx .int),.op (.imm12 imm)]) =
      some (.aluRRImm12 .subS (szOf ty.width) .xzr (.vreg nx .int) imm) := by
    cases szOf ty.width <;> rfl
  have boundedMiddle : aliases.size ≤ middle.base.nextVreg := by rw [finish]; exact bounded
  obtain ⟨d,output,lower,upper,fragment,execution⟩ := stock_cmp_flag_condition_values hp ctx rfl enough decoded
    (condOf_ne_al .sgt) rfl conditionCall refines boundedMiddle flags truth
  refine ⟨nx,d,mapX,output,?_,upper,?_,execution⟩
  · rw [finish] at lower; exact lower
  · rw [finish] at fragment; exact fragment
end Backend.Stock.Proof.ScalarCmp
