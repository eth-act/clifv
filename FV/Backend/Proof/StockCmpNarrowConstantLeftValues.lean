import FV.Backend.Proof.StockCmpNarrowConstantLeftSelection
import FV.Backend.Proof.StockCmpNarrowSourceValues
namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
/-- Actual652 selection and715 execution compute the original narrow source
predicate, deriving the emitter RHS rather than requiring a caller certificate. -/
theorem stock_cmp_narrow_constant_left_emitter_source_values {p : Program} (hp : Data p)
    {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx) (half : Bool) (cc : Clif.IntCC)
    {ty : Clif.Ty} (sourceTy : ty = if half then .i16 else .i8)
    {fr : Clif.Frame} {x y : Nat} {u v : BitVec ty.width}
    (getX : fr.getAs x ty = .ok u) (getY : fr.getAs y ty = .ok v)
    (typeX : ctx.valueType? x = some (.int (if half then 16 else 8)))
    (typeY : ctx.valueType? y = some (.int (if half then 16 else 8)))
    {constantJ : Nat} {constantInfo : IInfo} {literal : Int}
    (defined : ctx.defInst? x = some constantJ) (constantFound : ctx.insts[constantJ]? = some constantInfo)
    (data : constantInfo.data = .data 152 35 [.data 151 57 [],.int literal]) (nonzero : u64 literal ≠ 0)
    (notConstantY : NonConstantSource ctx y)
    {st middle next : State} {tr emitTrace conditionStart trace : Array RuleId}
    {emitFuel fuel : Nat} {condition out : V} (enoughEmit : 200 ≤ emitFuel) (enough : 119 ≤ fuel)
    (emitter : ApplyInternal p (Stock.sem ctx) {} emitFuel 123 652 [.data 145 (ccIdx cc) [],.value x,.value y]
      (st,tr) condition (middle,emitTrace))
    (conditionCall : ApplyInternal p (Stock.sem ctx) {} fuel 27 715 [condition]
      (middle,conditionStart) out (next,trace))
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ z r,ctx.valueReg? z = some r → z < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun key => ρ (aliasNum aliases key)))
    (separatedY : ∀ r,ctx.valueReg? y = some (.vreg r .int) → aliasNum aliases r ≠ st.base.nextVreg) :
    ∃ nx ny d,ctx.valueReg? x = some (.vreg nx .int) ∧ ctx.valueReg? y = some (.vreg ny .int) ∧
      out = .reg (.vreg d .int) ∧ st.base.nextVreg ≤ d ∧ d < next.base.nextVreg ∧
      Frag st.base next.base [MInst.extend (.vreg st.base.nextVreg .int) (.vreg nx .int)
        (signedCC cc) ty.width 32,
        .aluRRRExtend .subS .size32 .xzr (.vreg st.base.nextVreg .int) (.vreg ny .int)
          (if signedCC cc then (if half then ExtendOp.sxth else .sxtb) else (if half then ExtendOp.uxth else .uxtb)),
        .cset (.vreg d .int) (condOf cc)] ∧
      ∀ world,Runs F isem ([MInst.extend (.vreg st.base.nextVreg .int) (.vreg nx .int)
        (signedCC cc) ty.width 32,
        .aluRRRExtend .subS .size32 .xzr (.vreg st.base.nextVreg .int) (.vreg ny .int)
          (if signedCC cc then (if half then ExtendOp.sxth else .sxtb) else (if half then ExtendOp.uxth else .uxtb)),
        .cset (.vreg d .int) (condOf cc)].map
          (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world (fun ρ' _ =>
            VHolds ⟨.i8,Clif.Sem.bool8 (Clif.Sem.intcc cc u v)⟩ (ρ' d) ∧
            ∀ k,k < st.base.nextVreg ∨ next.base.nextVreg ≤ k → ρ' k = ρ k) := by
  obtain ⟨rhsTrace,rhs,traceEq⟩ := stock_cmp_narrow_constant_left_emitter_selected hp ctx inv cc half
    enoughEmit typeX typeY defined constantFound data nonzero notConstantY emitter
  obtain ⟨n,equal⟩ : ∃ n,emitFuel=n+160 := ⟨emitFuel-160,by omega⟩
  rw [equal] at rhs
  exact stock_cmp_narrow_condition_source_values hp inv half cc sourceTy getX getY typeX enough
    rhs conditionCall refines bounded extent held separatedY
end Backend.Stock.Proof.ScalarCmp
