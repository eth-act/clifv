import FV.Backend.Lowering.StockComparisonArgsLoopCfg
import FV.Backend.Lowering.StockComparisonComputedLoopCfg

/-! The loop class with comparisons of computed values and block arguments (#140, CB-9).

`ComparisonComputedLoopCfg` (CB-8) admits a comparison of two computed values, but its `brif`
successors take no arguments. `ComparisonArgsLoopCfg` (T7b-9) admits block arguments, but the first
`icmp` operand must be a parameter. Real loops do both. For example, the loop of
`runtests/fibonacci.clif` counts down with `v14 = iadd v10, v24`, branches on
`icmp eq v14, (iconst 0)`, and passes block arguments on both edges.

Here a `brif` condition is a wide parameter, a same-block `icmp` in one of the forms of
`ComparisonComputedLoopCfg.conditionEligible`, or a same-block `icmp eq|ne x, y` where `y` is a
result of `iconst 0` and `x` is a computed wide value: a parameter, or a result of a statement
that is not an `iconst` and, for `eq`, not a `band`. The aarch64 lowering then selects the zero
rule of `emit_icmp` (5170 for `eq`, 5172 for `ne`) and `is_nonzero x`, which is one
`cbz`/`cbnz` on `x`. A `band` result is excluded for `eq` because of the `tbz` rule of
`lower_branch`. The successors may take block arguments through original or critical-edge
successors. Every edge enters an existing nonentry block, so back edges and self loops are
selected.

The checker publishes the edge split of the actual Stock lowering, as
`ComparisonArgsLoopCfg.check`. -/

namespace Backend.Stock.ComparisonComputedArgsLoopCfg
open Backend.Proof.Driver
set_option autoImplicit false

/-- `stm` is not an `iconst`, is not a `band` unless `cc` is `ne`, and defines `x` as a result of
type `ty`. -/
def zeroResult (f : Clif.Function) (cc : Clif.IntCC) (x : Nat) (ty : Clif.Ty) (stm : Clif.Stmt) : Bool :=
  (match stm.inst with
    | .iconst .. => false
    | .binary .band .. => cc == .ne
    | _ => true) && (stm.results.zip (ComparisonComputedLoopCfg.resultTypesOf f stm)).contains (x,ty)

/-- `x` is a value of type `ty` that is a parameter of some block, or a `zeroResult` of a
statement of some block. -/
def zeroOperandOf (f : Clif.Function) (cc : Clif.IntCC) (x : Nat) (ty : Clif.Ty) : Bool :=
  ComparisonLoopCfg.parameterOf f x ty || ComparisonLoopCfg.statementOf f (zeroResult f cc x ty)

/-- `stm` defines `condition` by an `icmp eq|ne x, y` where `x` is a `zeroOperandOf` value of one
wide type and `y` is a result of `iconst 0`. -/
def zeroEligible (f : Clif.Function) (condition : Nat) (stm : Clif.Stmt) : Bool :=
  stm.results.contains condition && match stm.inst with
    | .icmp cc _ x y => (cc == .eq || cc == .ne) &&
      (zeroOperandOf f cc x .i32 || zeroOperandOf f cc x .i64) &&
      ComparisonLoopCfg.statementOf f (ComparisonZeroCfg.constantEligible y)
    | _ => false

/-- A `brif` condition of block `b`: a condition of `ComparisonComputedLoopCfg`, or a result of a
zero comparison of a computed value in the body of `b`. -/
def conditionEligible (f : Clif.Function) (b : Clif.Block) (c : Nat) : Bool :=
  ComparisonComputedLoopCfg.conditionEligible f b c || b.body.any (zeroEligible f c)

/-- `ComparisonArgsLoopCfg.controlEligible` with `conditionEligible` for the `brif` condition of
block `b`: jumps with any arguments, returns, and branches with any arguments, each target an
existing nonentry block. -/
def controlEligible (f : Clif.Function) (b : Clif.Block) : Clif.Terminator → Bool
  | .jump bc => ParameterLoopCfg.targetNonentry f bc
  | .ret _ => true
  | .brif c yes no => conditionEligible f b c &&
    ParameterLoopCfg.targetNonentry f yes && ParameterLoopCfg.targetNonentry f no
  | _ => false

/-- As `controlEligible`, and a nonentry block may also end in `trap`. -/
def controlLeafEligible (f : Clif.Function) (bi : Nat) (b : Clif.Block) : Clif.Terminator → Bool
  | .trap _ => bi != 0
  | term => controlEligible f b term

/-- `ComparisonArgsLoopCfg.sourceLeafEligible` with the conditions of `conditionEligible`. Bodies
and ABI are as there. -/
def sourceLeafEligible (f : Clif.Function) : Bool :=
  f.blocks.zipIdx.all (fun (b,bi) => controlLeafEligible f bi b b.term) &&
  f.blocks.all (fun b => b.body.all Scalar.maskMixedBodyEligible) &&
  f.sig.params.all Scalar.narrowAbiEligible && f.sig.returns.all Scalar.narrowAbiEligible

def sourceOk (f : Clif.Function) : Bool :=
  sourceLeafEligible f && lowerScopeB f && dominatedB f && sigAbiOk f.sig

/-- The published code is the actual edge split of the actual Stock lowering. -/
def check (f : Clif.Function) (vc : VCode) : Bool :=
  sourceOk f && match Stock.lower f with
  | .error _ => false
  | .ok result => match splitEdgesChecked result.code result.edgeArgs with
    | .ok split => decide (split.code = vc)
    | .error _ => false

end Backend.Stock.ComparisonComputedArgsLoopCfg
