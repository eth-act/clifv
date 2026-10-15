import FV.Backend.Proof.StockCmpPredecessorUnsignedSelection
import FV.Backend.Proof.StockCmpPredecessorUnsignedSourceValues
namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
/-- Actual emitter652 and condition715 compute the original constant comparison;
the real immediate RHS is derived from selection rather than supplied by callers. -/
theorem stock_cmp_predecessor_unsigned_emitter_source_values {p : Program} (hp : Data p)
    {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {ty : Clif.Ty} (width : ty.width = 32 ∨ ty.width = 64)
    {fr : Clif.Frame} (dfg : DFGCons ctx fr) {x y j : Nat} {info : IInfo} {i : Int}
    {u v : BitVec ty.width} (getX : fr.getAs x ty = .ok u) (getY : fr.getAs y ty = .ok v)
    (defined : ctx.defInst? y = some j) (found : ctx.insts[j]? = some info)
    (data : info.data = .data 152 35 [.data 151 57 [],.int i])
    {imm : Imm12} (encoded : Imm12.ofNat? (u64 (i-1)) = some imm)
    (odd : u64 i % 2 = 1)
    (nonencodable : Imm12.ofNat? (u64 i) = none)
    (typeX : ctx.valueType? x = some (.int (szOf ty.width).bits))
    {st middle next : State} {tr emitTrace conditionStart trace : Array RuleId}
    {emitFuel fuel : Nat} {condition out : V} (enoughEmit : 200 ≤ emitFuel) (enough : 119 ≤ fuel)
    (emitter : ApplyInternal p (Stock.sem ctx) {} emitFuel 123 652 [.data 145 (ccIdx .uge) [],.value x,.value y]
      (st,tr) condition (middle,emitTrace))
    (conditionCall : ApplyInternal p (Stock.sem ctx) {} fuel 27 715 [condition]
      (middle,conditionStart) out (next,trace))
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ z r,ctx.valueReg? z = some r → z < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun key => ρ (aliasNum aliases key))) :
    ∃ nx d,ctx.valueReg? x = some (.vreg nx .int) ∧ out = .reg (.vreg d .int) ∧
      st.base.nextVreg ≤ d ∧ d < next.base.nextVreg ∧
      Frag st.base next.base [.aluRRImm12 .subS (szOf ty.width) .xzr (.vreg nx .int) imm,
        .cset (.vreg d .int) (condOf .ugt)] ∧
      ∀ world,Runs F isem ([MInst.aluRRImm12 .subS (szOf ty.width) .xzr (.vreg nx .int) imm,
        .cset (.vreg d .int) (condOf .ugt)].map
        (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world (fun ρ' _ =>
          VHolds ⟨.i8,Clif.Sem.bool8 (Clif.Sem.intcc .uge u v)⟩ (ρ' d) ∧ ∀ k,k ≠ d → ρ' k = ρ k) := by
  obtain ⟨rhsTrace,rhs,traceEq⟩ := stock_cmp_predecessor_unsigned_emitter_selected hp ctx (szOf ty.width)
    enoughEmit typeX defined found data odd encoded nonencodable emitter
  obtain ⟨n,fuelEq⟩ : ∃ n,emitFuel=n+100 := ⟨emitFuel-100,by omega⟩
  rw [fuelEq] at rhs
  obtain ⟨safe,rx,mapped,producer,finish⟩ := stock_cmp_predecessor_unsigned_rhs_observed hp ctx rfl (szOf ty.width) rhs
  have raw := stock_cmp_predecessor_unsigned_rhs hp ctx (cfg := {}) rfl (szOf ty.width) st tr n x i rx imm mapped safe
  rw [← producer,← finish] at raw
  exact stock_cmp_predecessor_unsigned_condition_source_values hp inv width dfg getX getY defined found data encoded odd enough
    raw conditionCall refines bounded extent held
end Backend.Stock.Proof.ScalarCmp
