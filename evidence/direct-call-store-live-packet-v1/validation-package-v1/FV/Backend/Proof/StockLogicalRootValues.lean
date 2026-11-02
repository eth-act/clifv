import FV.Backend.Proof.StockDemandMono
import FV.Backend.Proof.StockLogicalHelper
import FV.Backend.Proof.StockLogicalValues

namespace Backend.Stock.Proof.LogicalSelected
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.LogicalSemantics
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program

def Kind.op : Kind → ALUOp
  | .band => .and | .bor => .orr | .bxor => .eor
private theorem kindTag (kind : Kind) : ALUOp.ofIdx? kind.tag = some kind.op := by cases kind <;> rfl
private theorem kindPair (kind : Kind) : LogicPair kind.op kind.cop := by
  cases kind <;> simp [Kind.op,Kind.cop,LogicPair]
private theorem stock_sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem valueReg (ctx : Ctx) (st : State) (r : Reg) :
    (Stock.sem ctx).ctor T.value_reg [.reg r] st = .ok (.regs [r],st) := by
  rw [stock_sem_ctor]
  rw [stock_ctor_baseOnly ctx T.value_reg _ st (by decide)]
  rfl
private theorem outputReg (ctx : Ctx) (st : State) (r : Reg) :
    (Stock.sem ctx).ctor T.output [.regs [r]] st = .ok (.regsVec [[r]],st) := by
  rw [stock_sem_ctor]
  rw [stock_ctor_baseOnly ctx T.output _ st (by decide)]
  rfl
private theorem output_run {p : Program} (hp : Data p) (ctx : Ctx) (st : State) (tr : Array RuleId)
    (n : Nat) (r : Reg) :
    (applyTerm p (Stock.sem ctx) {} (n + 10) 25 172 [.reg r]).run (st,tr) =
      .ok (some (.regsVec [[r]]),st,tr.push rule_prelude_lower_105.id) := by
  have a := valueReg ctx st r
  have b := outputReg ctx st r
  rw [stock_sem_ctor] at a b
  cases hp
  isel_eval [*,rule_prelude_lower_105,stock_sem_ctor]

/-- The actual typed logical root RHS inherits the helper's original-value and
fresh-only execution semantics, including its actual output wrapper. -/
theorem stock_logical_root_values {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (kind : Kind) {ty : Clif.Ty} (width : ty.width ≤ 64) {fr : Clif.Frame} (dfg : DFGCons ctx fr)
    {x y : Nat} {u v : BitVec ty.width} (sourceX : fr.getAs x ty = .ok u) (sourceY : fr.getAs y ty = .ok v)
    {st next : State} {out : V} {rhsTrace : Array RuleId} {aliases : Array (Option Nat)} {ρ : Nat → CV}
    (bounded : aliases.size ≤ st.base.nextVreg) (extent : ∀ x r, ctx.valueReg? x = some r → x < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun z => ρ (aliasNum aliases z)))
    (rhs : (evalExpr program (Stock.sem ctx) {} 999999 kind.rule.rhs
      (env3 (.ty (.int ty.width)) (.value x) (.value y))).run (st,#[]) = .ok (some out,next,rhsTrace)) :
    ∃ (mi : MInst) (ρ' : Nat → CV), out = .regsVec [[.vreg st.base.nextVreg .int]] ∧
      next.base = (st.base.fresh .int).2.emit mi ∧
      PRun F isem [mi.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size + 1))] ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.binary kind.cop u v⟩ (ρ' st.base.nextVreg) ∧
      ∀ n, n ≠ st.base.nextVreg → ρ' n = ρ n := by
  obtain ⟨a,middle,helperTrace,helper,output⟩ := stock_logical_rhs_helper kind rhs
  have mono := stock_apply_demand_mono output
  have helperHeld : ValuesHeld (Demanded middle) ctx fr (fun z => ρ (aliasNum aliases z)) := by
    apply held.mono
    intro x needed
    unfold Demanded at needed ⊢
    have grows := mono x
    omega
  obtain ⟨mi,ρ',outEq,base,execution,value,kept⟩ := stock_logical_helper_values data_program inv refines
    (kindTag kind) (kindPair kind) width dfg sourceX sourceY bounded extent helperHeld (n := 999936) helper
  rw [outEq] at output
  rw [output_run data_program ctx middle helperTrace 999988 (.vreg st.base.nextVreg .int)] at output
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at output
  obtain ⟨outputEq,stateEq,traceEq⟩ := output
  exact ⟨mi,ρ',outputEq.symm,by rw [← stateEq]; exact base,execution,value,kept⟩

end Backend.Stock.Proof.LogicalSelected
