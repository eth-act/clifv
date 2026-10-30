import FV.Backend.Proof.StockExtendValues
namespace Backend.Stock.Proof.ScalarShift
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
inductive Kind where
  | lsl | lsr | asr
  deriving DecidableEq
def Kind.op : Kind → ALUOp
  | .lsl => .lsl | .lsr => .lsr | .asr => .asr
def Kind.tag : Kind → Nat
  | .lsl => 18 | .lsr => 16 | .asr => 17
def Kind.cop : Kind → Clif.BinaryOp
  | .lsl => .ishl | .lsr => .ushr | .asr => .sshr
def Kind.opcode : Kind → Nat
  | .lsl => 103 | .lsr => 104 | .asr => 105
def Kind.rule (kind : Kind) (wide : Bool) : Rule :=
  match kind,wide with
  | .lsl,false => rule_lower_1545 | .lsl,true => rule_lower_1549
  | .lsr,false => rule_lower_1638 | .lsr,true => rule_lower_1642
  | .asr,false => rule_lower_1695 | .asr,true => rule_lower_1699
def rootEnv (wide : Bool) (w x y : Nat) : Isle.Interp.Env V :=
  if wide then env2 (.value x) (.value y) else env3 (.ty (.int w)) (.value x) (.value y)
def PrepRun (ctx : Ctx) (kind : Kind) (wide : Bool) (x : Nat) (st middle : State)
    (tr prepTrace : Array RuleId) (prepared : V) : Prop :=
  match kind with
  | .lsl => Stock.externCtor ctx T.put_in_reg [.value x] st = .ok (prepared,middle) ∧ prepTrace = tr
  | .lsr => ApplyInternal program (Stock.sem ctx) {} 999991 27 (extTerm false wide) [.value x] (st,tr) prepared (middle,prepTrace)
  | .asr => ApplyInternal program (Stock.sem ctx) {} 999991 27 (extTerm true wide) [.value x] (st,tr) prepared (middle,prepTrace)
private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem sem_prim_type (ctx : Ctx) (name : String) :
    (Stock.sem ctx).prim 14 name = (CTy.ofName? name).map V.ty := rfl
private theorem sem_mkData (ctx : Ctx) (t k : Nat) (vs : List V) :
    (Stock.sem ctx).mkData t k vs = .data t k vs := rfl

/-- The real RHS of each scalar shift root exposes operand preparation, the
actual do_shift call and output wrapper with complete states and traces. -/
theorem stock_shift_rhs_receipts (kind : Kind) (wide : Bool) {ctx : Ctx} {w x y : Nat}
    {st next : State} {tr trace : Array RuleId} {out : V}
    (rhs : (evalExpr program (Stock.sem ctx) {} 999999 (kind.rule wide).rhs (rootEnv wide w x y)).run
      (st,tr) = .ok (some out,next,trace)) :
    ∃ (prepared result : V) (middle after : State) (prepTrace shiftTrace : Array RuleId),
      PrepRun ctx kind wide x st middle tr prepTrace prepared ∧
      ApplyInternal program (Stock.sem ctx) {} 999995 27 703
        [.data 59 kind.tag [],.ty (.int (if wide then 64 else w)),prepared,.value y]
        (middle,prepTrace) result (after,shiftTrace) ∧
      (applyTerm program (Stock.sem ctx) {} 999998 25 172 [result]).run (after,shiftTrace) =
        .ok (some out,next,trace) := by
  have hp := data_program
  cases hp
  cases kind <;> cases wide
  all_goals
    isel_inv [*,Kind.rule,Kind.tag,rootEnv,rule_lower_1545,rule_lower_1549,rule_lower_1638,
      rule_lower_1642,rule_lower_1695,rule_lower_1699,sem_ctor,sem_prim_type,sem_mkData] at rhs
    all_goals isel_destruct <;> subst_vars
    all_goals first
      | (rename_i result shifted prepared middle outputCall shiftCall prepCall
         refine ⟨prepared,result,middle,shifted.1,tr,⟨prepCall,rfl⟩,shifted.2,shiftCall,?_⟩
         simpa only [data_program.t172,pure,Except.pure,term_172_kind,true_and] using outputCall)
      | (rename_i result shifted prepared middle outputCall shiftCall prepCall
         refine ⟨prepared,result,middle.1,shifted.1,middle.2,prepCall,shifted.2,shiftCall,?_⟩
         simpa only [data_program.t172,pure,Except.pure,term_172_kind,true_and] using outputCall)
end Backend.Stock.Proof.ScalarShift
