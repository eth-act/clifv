import FV.Backend.Lowering.StockParameterLoopCfg
import FV.Backend.Lowering.StockParameterAnyArgsCfg

/-! The loop class whose parameter branches pass block arguments (#140, T7b-8).

`ParameterLoopCfg` admits loops, but its `brif` successors take no arguments. Real loops pass
loop-carried values on `brif` edges, for example a self loop `brif v, block1(args...), block2(...)`.
`ParameterArgsCfg.anySourceLeafEligible` admits `brif` arguments through original or critical-edge
successors, but only in a ranked forward CFG. Here both restrictions are dropped: every edge enters
an existing nonentry block (`ParameterLoopCfg.targetNonentry`), so back edges and self loops are
selected, and parameter branches may pass block arguments. A `brif` condition is a wide parameter;
comparison conditions (`ComparisonLoopCfg`) are not part of this class.

The checker publishes the edge split of the actual Stock lowering, as `ParameterArgsCfg.anyCheck`. -/

namespace Backend.Stock.ParameterArgsLoopCfg
open Backend.Proof.Driver
set_option autoImplicit false

/-- `ParameterLoopCfg.controlEligible` where a parameter branch may pass block arguments:
jumps with any arguments, returns, and wide-parameter branches with any arguments, each target an
existing nonentry block. -/
def controlEligible (f : Clif.Function) : Clif.Terminator → Bool
  | .jump bc => ParameterLoopCfg.targetNonentry f bc
  | .ret _ => true
  | .brif c yes no => ParameterCfg.parameterEligible f c &&
    ParameterLoopCfg.targetNonentry f yes && ParameterLoopCfg.targetNonentry f no
  | _ => false

/-- As `controlEligible`, and a nonentry block may also end in `trap`. -/
def controlLeafEligible (f : Clif.Function) (bi : Nat) : Clif.Terminator → Bool
  | .trap _ => bi != 0
  | term => controlEligible f term

/-- `ParameterArgsCfg.anySourceLeafEligible` without the forward rank, or
`ParameterLoopCfg.sourceLeafEligible` with block arguments on parameter branches. Bodies and ABI
are as in both. -/
def sourceLeafEligible (f : Clif.Function) : Bool :=
  f.blocks.zipIdx.all (fun (b,bi) => controlLeafEligible f bi b.term) &&
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

end Backend.Stock.ParameterArgsLoopCfg
