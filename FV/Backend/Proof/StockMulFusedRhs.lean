import FV.Backend.Proof.StockMulHelper
import FV.Backend.Proof.StockRequestSuccess
namespace Backend.Stock.Proof.ScalarMul.Fused
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.ScalarMul
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
inductive Fusion where
  | addRight | addLeft | subRight
  deriving DecidableEq
def Fusion.rule : Fusion → Rule
  | .addRight => rule_lower_125 | .addLeft => rule_lower_128 | .subRight => rule_lower_132
def Fusion.left : Fusion → Bool
  | .addLeft => true | _ => false
def Fusion.subtract : Fusion → Bool
  | .subRight => true | _ => false
def Fusion.cop (fusion : Fusion) : Clif.BinaryOp := if fusion.subtract then .isub else .iadd
def Fusion.op (fusion : Fusion) : ALUOp3 := if fusion.subtract then .mSub else .mAdd
def rootEnv (fusion : Fusion) (w x a b : Nat) : Isle.Interp.Env V :=
  if fusion.left then env4 (.ty (.int w)) (.value a) (.value b) (.value x)
  else env4 (.ty (.int w)) (.value x) (.value a) (.value b)
private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem output_run {p : Program} (hp : Data p) (ctx : Ctx) (st : State) (tr : Array RuleId)
    (n : Nat) (r : Reg) :
    (applyTerm p (Stock.sem ctx) {} (n+10) 25 172 [.reg r]).run (st,tr) =
      .ok (some (.regsVec [[r]]),st,tr.push rule_prelude_lower_105.id) := by
  have value : ∀ q,Stock.externCtor ctx T.value_reg [.reg r] q = .ok (.regs [r],q) := by
    intro q; rw [stock_ctor_baseOnly ctx T.value_reg _ q (by decide)]; rfl
  have output : ∀ q,Stock.externCtor ctx T.output [.regs [r]] q = .ok (.regsVec [[r]],q) := by
    intro q; rw [stock_ctor_baseOnly ctx T.output _ q (by decide)]; rfl
  cases hp
  isel_eval [*,rule_prelude_lower_105,sem_ctor]

/-- Actual fused multiply-add/subtract RHSs account for all three guarded
requests, scheduling fields and the single fresh machine instruction. -/
theorem stock_mul_fused_rhs_run {p : Program} (hp : Data p) (ctx : Ctx) (fusion : Fusion)
    {x a b w : Nat} {rx ra rb : Reg} (mx : ctx.valueReg? x = some rx)
    (ma : ctx.valueReg? a = some ra) (mb : ctx.valueReg? b = some rb) (width : w ≤ 64)
    (st : State) (safeX : DemandAllowed ctx st x) (safeA : DemandAllowed ctx st a) (safeB : DemandAllowed ctx st b)
    (tr : Array RuleId) (n : Nat) :
    ∃ trace,(evalExpr p (Stock.sem ctx) {} (n+40) fusion.rule.rhs (rootEnv fusion w x a b)).run (st,tr) =
      .ok (some (.regsVec [[(st.base.fresh .int).1]]),
        {((st.mark a).mark b).mark x with base := (st.base.fresh .int).2.emit (.aluRRRR fusion.op (szOf w) (st.base.fresh .int).1 ra rb rx)},trace) := by
  have requestA := stock_put_in_reg ctx st a ra ma safeA
  have requestB := stock_put_in_reg ctx (st.mark a) b rb mb safeB
  have requestX := stock_put_in_reg ctx ((st.mark a).mark b) x rx mx safeX
  have add := fun q trace fuel => stock_madd_helper hp ctx (cfg := {}) rfl width q trace fuel ra rb rx
  have sub := fun q trace fuel => stock_msub_helper hp ctx (cfg := {}) rfl width q trace fuel ra rb rx
  have output := fun q trace fuel r => output_run hp ctx q trace fuel r
  cases hp
  cases fusion with
  | addRight =>
    refine Exists.intro ?traceR ?proofR
    case proofR =>
      isel_eval [*,Fusion.rule,Fusion.op,Fusion.subtract,Fusion.left,rootEnv,rule_lower_125,rule_lower_128,rule_lower_132,sem_ctor]
      rfl
  | addLeft =>
    refine Exists.intro ?traceL ?proofL
    case proofL =>
      isel_eval [*,Fusion.rule,Fusion.op,Fusion.subtract,Fusion.left,rootEnv,rule_lower_125,rule_lower_128,rule_lower_132,sem_ctor]
      rfl
  | subRight =>
    refine Exists.intro ?traceS ?proofS
    case proofS =>
      isel_eval [*,Fusion.rule,Fusion.op,Fusion.subtract,Fusion.left,rootEnv,rule_lower_125,rule_lower_128,rule_lower_132,sem_ctor]
      rfl

private theorem requests {p : Program} (hp : Data p) (ctx : Ctx) (fusion : Fusion)
    {x a b w n : Nat} {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n+40) fusion.rule.rhs (rootEnv fusion w x a b)).run
      (st,tr) = .ok (some out,next,trace)) :
    DemandAllowed ctx st a ∧ DemandAllowed ctx st b ∧ DemandAllowed ctx st x ∧
      ∃ ra rb rx,ctx.valueReg? a = some ra ∧ ctx.valueReg? b = some rb ∧ ctx.valueReg? x = some rx := by
  cases callA : Stock.externCtor ctx T.put_in_reg [.value a] st with
  | fail =>
    have denied : (evalExpr p (Stock.sem ctx) {} (n+40) fusion.rule.rhs (rootEnv fusion w x a b)).run (st,tr) ≠ .ok (some out,next,trace) := by
      cases hp
      cases fusion <;> isel_eval [*,Fusion.rule,Fusion.left,rootEnv,rule_lower_125,rule_lower_128,rule_lower_132,sem_ctor]
      all_goals intro impossible; cases impossible
    exact False.elim (denied run)
  | unmodeled err =>
    have denied : (evalExpr p (Stock.sem ctx) {} (n+40) fusion.rule.rhs (rootEnv fusion w x a b)).run (st,tr) ≠ .ok (some out,next,trace) := by
      cases hp
      cases fusion <;> isel_eval [*,Fusion.rule,Fusion.left,rootEnv,rule_lower_125,rule_lower_128,rule_lower_132,sem_ctor]
      all_goals intro impossible; cases impossible
    exact False.elim (denied run)
  | ok pair =>
    obtain ⟨vA,sA⟩ := pair
    obtain ⟨safeA,rA,mA,rfl,rfl⟩ := (stock_put_in_reg_iff ctx st a vA sA).mp callA
    cases callB : Stock.externCtor ctx T.put_in_reg [.value b] (st.mark a) with
    | fail =>
      have denied : (evalExpr p (Stock.sem ctx) {} (n+40) fusion.rule.rhs (rootEnv fusion w x a b)).run (st,tr) ≠ .ok (some out,next,trace) := by
        cases hp
        cases fusion <;> isel_eval [*,Fusion.rule,Fusion.left,rootEnv,rule_lower_125,rule_lower_128,rule_lower_132,sem_ctor]
        all_goals intro impossible; cases impossible
      exact False.elim (denied run)
    | unmodeled err =>
      have denied : (evalExpr p (Stock.sem ctx) {} (n+40) fusion.rule.rhs (rootEnv fusion w x a b)).run (st,tr) ≠ .ok (some out,next,trace) := by
        cases hp
        cases fusion <;> isel_eval [*,Fusion.rule,Fusion.left,rootEnv,rule_lower_125,rule_lower_128,rule_lower_132,sem_ctor]
        all_goals intro impossible; cases impossible
      exact False.elim (denied run)
    | ok pair =>
      obtain ⟨vB,sB⟩ := pair
      obtain ⟨safeB,rB,mB,rfl,rfl⟩ := (stock_put_in_reg_iff ctx (st.mark a) b vB sB).mp callB
      cases callX : Stock.externCtor ctx T.put_in_reg [.value x] ((st.mark a).mark b) with
      | fail =>
        have denied : (evalExpr p (Stock.sem ctx) {} (n+40) fusion.rule.rhs (rootEnv fusion w x a b)).run (st,tr) ≠ .ok (some out,next,trace) := by
          cases hp
          cases fusion <;> isel_eval [*,Fusion.rule,Fusion.left,rootEnv,rule_lower_125,rule_lower_128,rule_lower_132,sem_ctor]
          all_goals intro impossible; cases impossible
        exact False.elim (denied run)
      | unmodeled err =>
        have denied : (evalExpr p (Stock.sem ctx) {} (n+40) fusion.rule.rhs (rootEnv fusion w x a b)).run (st,tr) ≠ .ok (some out,next,trace) := by
          cases hp
          cases fusion <;> isel_eval [*,Fusion.rule,Fusion.left,rootEnv,rule_lower_125,rule_lower_128,rule_lower_132,sem_ctor]
          all_goals intro impossible; cases impossible
        exact False.elim (denied run)
      | ok pair =>
        obtain ⟨vX,sX⟩ := pair
        obtain ⟨safeX,rX,mX,rfl,rfl⟩ := (stock_put_in_reg_iff ctx ((st.mark a).mark b) x vX sX).mp callX
        exact ⟨safeA,safeB,safeX,rA,rB,rX,mA,mB,mX⟩

/-- Successful fused RHS execution derives the requests and exact complete
state, so guarded mapped operands are not separate caller certificates. -/
theorem stock_mul_fused_rhs_observed {p : Program} (hp : Data p) (ctx : Ctx) (fusion : Fusion)
    {x a b w n : Nat} (width : w ≤ 64) {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n+40) fusion.rule.rhs (rootEnv fusion w x a b)).run
      (st,tr) = .ok (some out,next,trace)) :
    DemandAllowed ctx st a ∧ DemandAllowed ctx st b ∧ DemandAllowed ctx st x ∧
      ∃ ra rb rx,ctx.valueReg? a = some ra ∧ ctx.valueReg? b = some rb ∧ ctx.valueReg? x = some rx ∧
        out = .regsVec [[(st.base.fresh .int).1]] ∧
        next = {((st.mark a).mark b).mark x with base := (st.base.fresh .int).2.emit (.aluRRRR fusion.op (szOf w) (st.base.fresh .int).1 ra rb rx)} := by
  obtain ⟨safeA,safeB,safeX,ra,rb,rx,ma,mb,mx⟩ := requests hp ctx fusion run
  obtain ⟨trace',expected⟩ := stock_mul_fused_rhs_run hp ctx fusion mx ma mb width st safeX safeA safeB tr n
  have same := Except.ok.inj (run.symm.trans expected)
  have outputEq := Option.some.inj (congrArg Prod.fst same)
  have stateEq := congrArg (fun q => q.2.1) same
  exact ⟨safeA,safeB,safeX,ra,rb,rx,ma,mb,mx,outputEq,stateEq⟩
end Backend.Stock.Proof.ScalarMul.Fused
