import FV.Backend.Lowering.StockParameterArgsLoopCfg
import FV.Backend.Lowering.StockComparisonLoopCfg

/-! The loop class whose comparison branches pass block arguments (#140, T7b-9).

`ComparisonLoopCfg` (T7b-7) admits comparison conditions, but its `brif` successors take no
arguments. `ParameterArgsLoopCfg` (T7b-8) admits `brif` arguments, but only on a wide-parameter
condition. Real loops do both: `egraph/licm.clif:f` branches on `icmp eq v2, v5` and passes the
next counter back to its own header, `brif v6, block2(v4), block1(v8)`. Here a `brif` condition
is a wide parameter or a same-block `icmp` in one of the three forms of `ComparisonLoopCfg`
(`ComparisonLoopCfg.conditionEligible`), and its successors may take block arguments through
original or critical-edge successors. Every edge enters an existing nonentry block, so back
edges and self loops are selected.

The checker publishes the edge split of the actual Stock lowering, as `ParameterArgsLoopCfg.check`. -/

namespace Backend.Stock.ComparisonArgsLoopCfg
open Backend.Proof.Driver
set_option autoImplicit false

/-- `ParameterArgsLoopCfg.controlEligible` with `ComparisonLoopCfg.conditionEligible` for the
`brif` condition of block `b`: jumps with any arguments, returns, and branches on a wide parameter
or on a comparison in `b`, with any arguments, each target an existing nonentry block. -/
def controlEligible (f : Clif.Function) (b : Clif.Block) : Clif.Terminator → Bool
  | .jump bc => ParameterLoopCfg.targetNonentry f bc
  | .ret _ => true
  | .brif c yes no => ComparisonLoopCfg.conditionEligible f b c &&
    ParameterLoopCfg.targetNonentry f yes && ParameterLoopCfg.targetNonentry f no
  | _ => false

/-- As `controlEligible`, and a nonentry block may also end in `trap`. -/
def controlLeafEligible (f : Clif.Function) (bi : Nat) (b : Clif.Block) : Clif.Terminator → Bool
  | .trap _ => bi != 0
  | term => controlEligible f b term

/-- `ParameterArgsLoopCfg.sourceLeafEligible` with comparison conditions, or
`ComparisonLoopCfg.sourceLeafEligible` with block arguments on branches. Bodies and ABI are as in
both. -/
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

end Backend.Stock.ComparisonArgsLoopCfg
