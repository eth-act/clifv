import FV.Backend.Lowering.StockGeneralArgsLoopCfg6

/-! The legacy loop class with `br_table` terminators (#140, CB-14c).

`GeneralLoopCfg5` (CB-13) with the `br_table` terminators of `GeneralArgsLoopCfg6.tableEligible`
whose default and table entries take no block arguments. Jumps may pass any arguments; `brif`
successors take none. The checker publishes the unsplit code of the actual Stock lowering, so the
class keeps the legacy single-vector interface (`Scalar.Domain`). -/

namespace Backend.Stock.GeneralLoopCfg6
open Backend.Proof.Driver
set_option autoImplicit false

/-- `GeneralLoopCfg5.controlEligible` with the `br_table` terminators of
`GeneralArgsLoopCfg6.tableEligible` whose successors take no arguments. -/
def controlEligible (f : Clif.Function) (b : Clif.Block) : Clif.Terminator → Bool
  | .brTable x dc tbl => GeneralArgsLoopCfg6.tableEligible f x dc tbl && (dc :: tbl).all (·.args.isEmpty)
  | term => GeneralLoopCfg5.controlEligible f b term

/-- As `controlEligible`, and a nonentry block may also end in `trap`. -/
def controlLeafEligible (f : Clif.Function) (bi : Nat) (b : Clif.Block) : Clif.Terminator → Bool
  | .trap _ => bi != 0
  | term => controlEligible f b term

/-- `GeneralLoopCfg5.sourceLeafEligible` with the terminators of `controlLeafEligible`. -/
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

end Backend.Stock.GeneralLoopCfg6
