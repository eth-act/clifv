module

public import FV.Backend.Proof.StockCmpNonencodableSelection
public import FV.Backend.Proof.StockCmpRegisterTraceValues

@[expose] public section

namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
/-- Actual successful emitter652 selection and condition715 execution compute
the original nonconstant comparison. No caller-chosen emitter RHS is required,
and the real emitted-rule trace prefix is retained. -/
theorem stock_cmp_nonencodable_emitter_source_values {p : Program} (hp : Data p)
    {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx) (cc : Clif.IntCC)
    {ty : Clif.Ty} (width : ty.width = 32 ∨ ty.width = 64)
    {fr : Clif.Frame} {x y : Nat} {u v : BitVec ty.width}
    (getX : fr.getAs x ty = .ok u) (getY : fr.getAs y ty = .ok v)
    (typeX : ctx.valueType? x = some (.int (szOf ty.width).bits))
    (typeY : ctx.valueType? y = some (.int (szOf ty.width).bits))
    (notConstantX : NonConstantSource ctx x) {constantJ : Nat} {constantInfo : IInfo} {literal : Int}
    (defined : ctx.defInst? y = some constantJ) (constantFound : ctx.insts[constantJ]? = some constantInfo)
    (data : constantInfo.data = .data 152 35 [.data 151 57 [],.int literal]) (nonzero : u64 literal ≠ 0)
    (ordinaryNone : Imm12.ofNat? (u64 literal) = none)
    (predecessorNone : Imm12.ofNat? (u64 (literal-1)) = none)
    {st middle next : State} {tr emitTrace trace : Array RuleId} {emitFuel conditionFuel : Nat} {condition out : V}
    (enoughEmit : 200 ≤ emitFuel) (enoughCondition : 119 ≤ conditionFuel)
    (emitter : ApplyInternal p (Stock.sem ctx) {} emitFuel 123 652 [.data 145 (ccIdx cc) [],.value x,.value y]
      (st,tr) condition (middle,emitTrace))
    (conditionCall : ApplyInternal p (Stock.sem ctx) {} conditionFuel 27 715 [condition]
      (middle,emitTrace) out (next,trace))
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ z r,ctx.valueReg? z = some r → z < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun key => ρ (aliasNum aliases key))) :
    ∃ nx ny d,ctx.valueReg? x = some (.vreg nx .int) ∧ ctx.valueReg? y = some (.vreg ny .int) ∧
      out = .reg (.vreg d .int) ∧ st.base.nextVreg ≤ d ∧ d < next.base.nextVreg ∧
      Frag st.base next.base [.aluRRR .subS (szOf ty.width) .xzr (.vreg nx .int) (.vreg ny .int),
        .cset (.vreg d .int) (condOf cc)] ∧
      ∀ world,Runs F isem ([MInst.aluRRR .subS (szOf ty.width) .xzr (.vreg nx .int) (.vreg ny .int),
        .cset (.vreg d .int) (condOf cc)].map
        (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world (fun ρ' _ =>
          VHolds ⟨.i8,Clif.Sem.bool8 (Clif.Sem.intcc cc u v)⟩ (ρ' d) ∧ ∀ k,k ≠ d → ρ' k = ρ k) := by
  obtain ⟨rhsTrace,rhs,traceEq⟩ := stock_cmp_nonencodable_emitter_selected hp ctx inv cc (szOf ty.width)
    enoughEmit typeX typeY notConstantX defined constantFound data nonzero ordinaryNone predecessorNone emitter
  obtain ⟨n,fuelEq⟩ : ∃ n,emitFuel=n+100 := ⟨emitFuel-100,by omega⟩
  rw [fuelEq] at rhs
  exact stock_cmp_register_condition_source_values_any_trace hp inv cc width getX getY enoughCondition
    rhs conditionCall refines bounded extent held
end Backend.Stock.Proof.ScalarCmp
