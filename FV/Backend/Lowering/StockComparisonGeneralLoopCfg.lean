import FV.Backend.Lowering.StockComparisonComputedArgsLoopCfg

/-! The legacy loop class with all six comparison condition forms (#140, CB-10).

`ComparisonComputedLoopCfg` (CB-8) admits a `brif` on a wide parameter or on a same-block `icmp`
in four forms: two parameters of one wide type (CB-4), a wide parameter with an encodable 12-bit
`iconst` (CB-7) or with `iconst 0` for `eq`/`ne` (CB-7d), and two computed values of one wide type
(CB-8). `ComparisonComputedArgsLoopCfg` (CB-9) adds the zero and 12-bit immediate forms with a
computed first operand, but it admits `brif` block arguments and publishes split code.

Here a `brif` condition is any condition of `ComparisonComputedArgsLoopCfg.conditionEligible`, and
its successors take no arguments, as in `ComparisonComputedLoopCfg`. Every edge enters an existing
nonentry block, so back edges and self loops are selected. Jumps may pass any arguments. The
checker publishes the unsplit code of the actual Stock lowering, so the class keeps the legacy
single-vector interface (`Scalar.Domain`). -/

namespace Backend.Stock.ComparisonGeneralLoopCfg
open Backend.Proof.Driver
set_option autoImplicit false

/-- `ComparisonComputedLoopCfg.controlEligible` with the six condition forms of
`ComparisonComputedArgsLoopCfg.conditionEligible` for the `brif` condition of block `b`: jumps
with any arguments, returns, and branches with empty arguments, each target an existing nonentry
block. -/
def controlEligible (f : Clif.Function) (b : Clif.Block) : Clif.Terminator → Bool
  | .jump bc => ParameterLoopCfg.targetNonentry f bc
  | .ret _ => true
  | .brif c yes no => ComparisonComputedArgsLoopCfg.conditionEligible f b c && yes.args.isEmpty &&
    no.args.isEmpty && ParameterLoopCfg.targetNonentry f yes && ParameterLoopCfg.targetNonentry f no
  | _ => false

/-- As `controlEligible`, and a nonentry block may also end in `trap`. -/
def controlLeafEligible (f : Clif.Function) (bi : Nat) (b : Clif.Block) : Clif.Terminator → Bool
  | .trap _ => bi != 0
  | term => controlEligible f b term

/-- `ComparisonComputedLoopCfg.sourceLeafEligible` with the conditions of
`ComparisonComputedArgsLoopCfg.conditionEligible`. Bodies and ABI are as there. -/
def sourceLeafEligible (f : Clif.Function) : Bool :=
  f.blocks.zipIdx.all (fun (b,bi) => controlLeafEligible f bi b b.term) &&
  f.blocks.all (fun b => b.body.all Scalar.maskMixedBodyEligible) &&
  f.sig.params.all Scalar.narrowAbiEligible && f.sig.returns.all Scalar.narrowAbiEligible

def sourceOk (f : Clif.Function) : Bool :=
  sourceLeafEligible f && lowerScopeB f && dominatedB f && sigAbiOk f.sig

/-- The published code is the unsplit code of the actual Stock lowering. -/
def check (f : Clif.Function) (vc : VCode) : Bool :=
  sourceOk f && match Stock.lower f with
  | .error _ => false
  | .ok result => decide (result.code = vc)

end Backend.Stock.ComparisonGeneralLoopCfg
