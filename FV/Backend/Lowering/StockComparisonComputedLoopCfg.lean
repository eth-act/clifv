import FV.Backend.Lowering.StockComparisonLoopCfg

/-! The loop class with comparisons of computed values (#140, CB-8).

`ComparisonLoopCfg` admits an `icmp` condition whose first operand is a parameter. A loop
header often compares a computed value, for example `icmp eq (iadd i, -1), n`. Here an `icmp`
condition may also compare two values of one wide type that are not results of an `iconst`:
parameters of any block, or results of other statements of any block. The aarch64 lowering then
selects the register comparison `subs xzr, x, y` (`emit_icmp` rule 5128): its other rules look
through an operand only when it is an `iconst`. The other conditions are those of
`ComparisonLoopCfg`. -/

namespace Backend.Stock.ComparisonComputedLoopCfg
open Backend.Proof.Driver
set_option autoImplicit false

/-- The result types of `stm`'s instruction, or `[]`. -/
def resultTypesOf (f : Clif.Function) (stm : Clif.Stmt) : List Clif.Ty :=
  (stm.inst.resultTypes (fun r => (f.extern? r).map (·.sig)) (f.sigDecls.lookup ·)).getD []

/-- `stm` is not an `iconst`, and it defines `x` as a result of type `ty`. -/
def computedResult (f : Clif.Function) (x : Nat) (ty : Clif.Ty) (stm : Clif.Stmt) : Bool :=
  (match stm.inst with
    | .iconst .. => false
    | _ => true) && (stm.results.zip (resultTypesOf f stm)).contains (x,ty)

/-- `x` is a value of type `ty` that is not a result of an `iconst`: a parameter of some block,
or a result of another statement of some block. -/
def computedOf (f : Clif.Function) (x : Nat) (ty : Clif.Ty) : Bool :=
  ComparisonLoopCfg.parameterOf f x ty || ComparisonLoopCfg.statementOf f (computedResult f x ty)

/-- `stm` defines `condition` by an `icmp` in one of the forms of `ComparisonLoopCfg`, or by an
`icmp cc _ x y` where `x` and `y` are computed values of one wide type. -/
def comparisonEligible (f : Clif.Function) (condition : Nat) (stm : Clif.Stmt) : Bool :=
  ComparisonLoopCfg.comparisonEligible f condition stm ||
  (stm.results.contains condition && match stm.inst with
    | .icmp _ _ x y => (computedOf f x .i32 && computedOf f y .i32) || (computedOf f x .i64 && computedOf f y .i64)
    | _ => false)

/-- A `brif` condition of block `b`: a wide parameter of any block, or a result of an eligible
comparison in the body of `b`. -/
def conditionEligible (f : Clif.Function) (b : Clif.Block) (c : Nat) : Bool :=
  ParameterCfg.parameterEligible f c || b.body.any (comparisonEligible f c)

/-- `ComparisonLoopCfg.controlEligible` with `conditionEligible` for the `brif` condition of
block `b`. -/
def controlEligible (f : Clif.Function) (b : Clif.Block) : Clif.Terminator → Bool
  | .jump bc => ParameterLoopCfg.targetNonentry f bc
  | .ret _ => true
  | .brif c yes no => conditionEligible f b c && yes.args.isEmpty && no.args.isEmpty &&
    ParameterLoopCfg.targetNonentry f yes && ParameterLoopCfg.targetNonentry f no
  | _ => false

/-- As `controlEligible`, and a nonentry block may also end in `trap`. -/
def controlLeafEligible (f : Clif.Function) (bi : Nat) (b : Clif.Block) : Clif.Terminator → Bool
  | .trap _ => bi != 0
  | term => controlEligible f b term

/-- `ComparisonLoopCfg.sourceLeafEligible` with comparisons of computed values. -/
def sourceLeafEligible (f : Clif.Function) : Bool :=
  f.blocks.zipIdx.all (fun (b,bi) => controlLeafEligible f bi b b.term) &&
  f.blocks.all (fun b => b.body.all Scalar.maskMixedBodyEligible) &&
  f.sig.params.all Scalar.narrowAbiEligible && f.sig.returns.all Scalar.narrowAbiEligible

def sourceOk (f : Clif.Function) : Bool :=
  sourceLeafEligible f && lowerScopeB f && dominatedB f && sigAbiOk f.sig

def check (f : Clif.Function) (vc : VCode) : Bool :=
  sourceOk f && match Stock.lower f with
  | .error _ => false
  | .ok result => decide (result.code = vc)

end Backend.Stock.ComparisonComputedLoopCfg
