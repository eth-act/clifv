import FV.Backend.Proof.StockCmpNarrowImmediateSourceValues
import FV.Backend.Proof.StockCmpNarrowImmediateSelection
namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
/-- Actual652 first-match and715 execution compute the original unsigned
narrow constant comparison with the emitter RHS derived internally. -/
theorem stock_cmp_narrow_immediate_emitter_source_values {p : Program} (hp : Data p)
    {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx) (half : Bool) (cc : Clif.IntCC)
    {ty : Clif.Ty} (sourceTy : ty = if half then .i16 else .i8)
    (unsigned : signedCC cc = false)
    {fr : Clif.Frame} (dfg : DFGCons ctx fr) {x y j : Nat} {info : IInfo} {literal : Int} {u v : BitVec ty.width}
    (getX : fr.getAs x ty = .ok u) (getY : fr.getAs y ty = .ok v)
    (defined : ctx.defInst? y = some j) (found : ctx.insts[j]? = some info)
    (data : info.data = .data 152 35 [.data 151 57 [],.int literal])
    {imm : Imm12} (encoded : Imm12.ofNat? (u64 literal) = some imm)
    (typeX : ctx.valueType? x = some (.int (if half then 16 else 8)))
    (notConstantX : NonConstantSource ctx x) (nonzero : u64 literal ≠ 0)
    {st middle next : State} {tr emitTrace conditionStart trace : Array RuleId}
    {emitFuel fuel : Nat} {condition out : V} (enoughEmit : 200 ≤ emitFuel) (enough : 119 ≤ fuel)
    (emitter : ApplyInternal p (Stock.sem ctx) {} emitFuel 123 652 [.data 145 (ccIdx cc) [],.value x,.value y]
      (st,tr) condition (middle,emitTrace))
    (conditionCall : ApplyInternal p (Stock.sem ctx) {} fuel 27 715 [condition]
      (middle,conditionStart) out (next,trace))
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ z r,ctx.valueReg? z = some r → z < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun key => ρ (aliasNum aliases key))) :
    ∃ nx d,ctx.valueReg? x = some (.vreg nx .int) ∧
      out = .reg (.vreg d .int) ∧ st.base.nextVreg ≤ d ∧ d < next.base.nextVreg ∧
      Frag st.base next.base [MInst.extend (.vreg st.base.nextVreg .int) (.vreg nx .int)
        false ty.width 32,
        .aluRRImm12 .subS .size32 .xzr (.vreg st.base.nextVreg .int) imm,
        .cset (.vreg d .int) (condOf cc)] ∧
      ∀ world,Runs F isem ([MInst.extend (.vreg st.base.nextVreg .int) (.vreg nx .int)
        false ty.width 32,
        .aluRRImm12 .subS .size32 .xzr (.vreg st.base.nextVreg .int) imm,
        .cset (.vreg d .int) (condOf cc)].map
          (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world (fun ρ' _ =>
            VHolds ⟨.i8,Clif.Sem.bool8 (Clif.Sem.intcc cc u v)⟩ (ρ' d) ∧
            ∀ k,k < st.base.nextVreg ∨ next.base.nextVreg ≤ k → ρ' k = ρ k) := by
  obtain ⟨rhsTrace,rhs,_⟩ := stock_cmp_narrow_immediate_emitter_selected hp ctx inv cc half enoughEmit unsigned
    typeX notConstantX defined found data nonzero encoded emitter
  obtain ⟨n,equal⟩ : ∃ n,emitFuel=n+160 := ⟨emitFuel-160,by omega⟩
  rw [equal] at rhs
  exact stock_cmp_narrow_immediate_condition_source_values hp inv half cc sourceTy unsigned dfg getX getY
    defined found data encoded typeX enough rhs conditionCall refines bounded extent held
end Backend.Stock.Proof.ScalarCmp
