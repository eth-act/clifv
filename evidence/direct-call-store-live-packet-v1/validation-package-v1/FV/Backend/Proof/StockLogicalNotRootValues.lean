import FV.Backend.Proof.StockDemandMono
import FV.Backend.Proof.StockLogicalSelected
import FV.Backend.Proof.StockLogicalNotValues

namespace Backend.Stock.Proof.LogicalNot
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.LogicalSelected
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program

def notTag : Kind → Nat
  | .band => 6 | .bor => 3 | .bxor => 8
def notALU : Kind → ALUOp
  | .band => .andNot | .bor => .orrNot | .bxor => .eorNot
def notRule (kind : Kind) (left : Bool) : Rule :=
  match kind,left with
  | .band,false => rule_lower_1429 | .band,true => rule_lower_1431
  | .bor,false => rule_lower_1466 | .bor,true => rule_lower_1468
  | .bxor,false => rule_lower_1534 | .bxor,true => rule_lower_1536
private def notTerm : Kind → Nat
  | .band => 1968 | .bor => 1965 | .bxor => 1970
private def args (kind : Kind) (left : Bool) : List Expr :=
  [.term 59 (notTerm kind) [],.var 14 0,.var 15 (if left then 2 else 1),.var 15 (if left then 1 else 2)]
def rootEnv (left : Bool) (w x y : Nat) : Isle.Interp.Env V :=
  if left then env3 (.ty (.int w)) (.value y) (.value x) else env3 (.ty (.int w)) (.value x) (.value y)
private theorem root_rhs (kind : Kind) (left : Bool) :
    ((notRule kind) left).rhs = .term 25 172 [.term 27 566 (args kind left)] := by
  cases kind <;> cases left <;> rfl
private theorem arguments {p : Program} (hp : Data p) (ctx : Ctx) (kind : Kind) (left : Bool)
    (w x y : Nat) (st : State) (tr : Array RuleId) (n : Nat) :
    (evalArgs p (Stock.sem ctx) {} (n+5) (args kind left) (rootEnv left w x y)).run (st,tr) =
      .ok (some [.data 59 (notTag kind) [],.ty (.int w),.value x,.value y],st,tr) := by
  cases hp
  cases kind <;> cases left <;> isel_eval [*,args,rootEnv,notTerm,notTag] <;> rfl

/-- All six mirrored logical-NOT RHSs expose the actual term566 call and output
wrapper with complete intermediate state and trace. -/
theorem stock_not_rhs_helper {ctx : Ctx} (kind : Kind) (left : Bool) {w x y : Nat}
    {st next : State} {tr rhsTrace : Array RuleId} {out : V}
    (rhs : (evalExpr program (Stock.sem ctx) {} 999999 ((notRule kind) left).rhs
      (rootEnv left w x y)).run (st,tr) = .ok (some out,next,rhsTrace)) :
    ∃ (a : V) (middle : State) (helperTrace : Array RuleId),
      (applyTerm program (Stock.sem ctx) {} 999996 27 566
        [.data 59 (notTag kind) [],.ty (.int w),.value x,.value y]).run (st,tr) = .ok (some a,middle,helperTrace) ∧
      (applyTerm program (Stock.sem ctx) {} 999998 25 172 [a]).run (middle,helperTrace) = .ok (some out,next,rhsTrace) := by
  rw [root_rhs] at rhs
  obtain ⟨vs,s1,a,s2,values,helper,output⟩ := rhs_output_inv (n := 999996) rhs
  rw [arguments data_program ctx kind left w x y st tr 999991] at values
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at values
  obtain ⟨rfl,rfl,rfl⟩ := values
  exact ⟨a,s2.1,s2.2,helper,output⟩

private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem value_reg (ctx : Ctx) (st : State) (r : Reg) :
    (Stock.sem ctx).ctor T.value_reg [.reg r] st = .ok (.regs [r],st) := by
  rw [sem_ctor,stock_ctor_baseOnly ctx T.value_reg _ st (by decide)]
  rfl
private theorem output_reg (ctx : Ctx) (st : State) (r : Reg) :
    (Stock.sem ctx).ctor T.output [.regs [r]] st = .ok (.regsVec [[r]],st) := by
  rw [sem_ctor,stock_ctor_baseOnly ctx T.output _ st (by decide)]
  rfl
private theorem output_run {p : Program} (hp : Data p) (ctx : Ctx) (st : State) (tr : Array RuleId)
    (n : Nat) (r : Reg) :
    (applyTerm p (Stock.sem ctx) {} (n+10) 25 172 [.reg r]).run (st,tr) =
      .ok (some (.regsVec [[r]]),st,tr.push rule_prelude_lower_105.id) := by
  have a := value_reg ctx st r
  have b := output_reg ctx st r
  rw [sem_ctor] at a b
  cases hp
  isel_eval [*,rule_prelude_lower_105,sem_ctor]
private theorem tag (kind : Kind) : ALUOp.ofIdx? (notTag kind) = some (notALU kind) := by cases kind <;> rfl
private theorem operation (kind : Kind) : NotOp (notALU kind) := by cases kind <;> simp [notALU,NotOp]

/-- Actual typed mirrored NOT roots inherit all three helper selections' mapped
value and fresh-only execution semantics, including the real output wrapper. -/
theorem stock_not_root_values {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (kind : Kind) (left : Bool) {ty : Clif.Ty} (width : ty.width ≤ 64)
    {fr : Clif.Frame} (dfg : DFGCons ctx fr) {x y : Nat} {u v : BitVec ty.width}
    (sourceX : fr.getAs x ty = .ok u) (sourceY : fr.getAs y ty = .ok v)
    {st next : State} {out : V} {rhsTrace : Array RuleId} {aliases : Array (Option Nat)} {ρ : Nat → CV}
    (bounded : aliases.size ≤ st.base.nextVreg) (extent : ∀ x r,ctx.valueReg? x = some r → x < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun z => ρ (aliasNum aliases z)))
    (rhs : (evalExpr program (Stock.sem ctx) {} 999999 ((notRule kind) left).rhs
      (rootEnv left ty.width x y)).run (st,#[]) = .ok (some out,next,rhsTrace)) :
    ∃ (mi : MInst) (ρ' : Nat → CV), out = .regsVec [[.vreg st.base.nextVreg .int]] ∧
      next.base = (st.base.fresh .int).2.emit mi ∧
      PRun F isem [mi.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1))] ρ ρ' ∧
      VHolds ⟨ty,notOpVal (notALU kind) u v⟩ (ρ' st.base.nextVreg) ∧
      ∀ n,n ≠ st.base.nextVreg → ρ' n = ρ n := by
  obtain ⟨a,middle,helperTrace,helper,output⟩ := stock_not_rhs_helper kind left rhs
  have mono := stock_apply_demand_mono output
  have helperHeld : ValuesHeld (Demanded middle) ctx fr (fun z => ρ (aliasNum aliases z)) := by
    apply held.mono
    intro x needed
    unfold Demanded at needed ⊢
    have grows := mono x
    omega
  obtain ⟨mi,ρ',outEq,base,execution,value,kept⟩ := stock_not_helper_values data_program inv refines
    (tag kind) (operation kind) width dfg sourceX sourceY bounded extent helperHeld (n := 999936) helper
  rw [outEq] at output
  rw [output_run data_program ctx middle helperTrace 999988 (.vreg st.base.nextVreg .int)] at output
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at output
  obtain ⟨outputEq,stateEq,traceEq⟩ := output
  exact ⟨mi,ρ',outputEq.symm,by rw [← stateEq]; exact base,execution,value,kept⟩

end Backend.Stock.Proof.LogicalNot
