import FV.Backend.Lowering.StockGeneralLoopCfg5

/-! The loop class with `br_table` terminators, with block arguments (#140, CB-14c).

`GeneralArgsLoopCfg5` (CB-13) admits jumps, returns, `brif` on its conditions and nonentry traps.
Here a block may also end in `br_table x, dc, [tbl]` (`tableEligible`) when

* the index `x` is declared with type `i32` (a parameter or a result of a statement); the table
  rule passes an `i32` index to `put_in_reg_zext32` unchanged, so no definition is looked through;
* the table has fewer than 4096 entries, so the bound check is `subs wzr, ridx, #n` with an
  immediate (rule 5450);
* the default and every table entry enter an existing nonentry block.

The successors may take block arguments. The checker publishes the edge split of the actual Stock
lowering. -/

namespace Backend.Stock.GeneralArgsLoopCfg6
open Backend.Proof.Driver
set_option autoImplicit false

/-- A `br_table x, dc, [tbl]` of the class: an `i32` index, fewer than 4096 table entries, and
every target an existing nonentry block. -/
def tableEligible (f : Clif.Function) (x : Nat) (dc : Clif.BlockCall) (tbl : List Clif.BlockCall) : Bool :=
  GeneralArgsLoopCfg5.declaredOf f x .i32 && decide (tbl.length < 4096) &&
    (dc :: tbl).all (ParameterLoopCfg.targetNonentry f)

/-- `GeneralArgsLoopCfg5.controlEligible` with `br_table` terminators of `tableEligible`. -/
def controlEligible (f : Clif.Function) (b : Clif.Block) : Clif.Terminator → Bool
  | .brTable x dc tbl => tableEligible f x dc tbl
  | term => GeneralArgsLoopCfg5.controlEligible f b term

/-- As `controlEligible`, and a nonentry block may also end in `trap`. -/
def controlLeafEligible (f : Clif.Function) (bi : Nat) (b : Clif.Block) : Clif.Terminator → Bool
  | .trap _ => bi != 0
  | term => controlEligible f b term

/-- `GeneralArgsLoopCfg5.sourceLeafEligible` with the terminators of `controlLeafEligible`. Bodies
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

end Backend.Stock.GeneralArgsLoopCfg6
