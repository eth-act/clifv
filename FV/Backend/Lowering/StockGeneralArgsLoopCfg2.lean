import FV.Backend.Lowering.StockComparisonComputedArgsLoopCfg

/-! The loop class with plain computed conditions and block arguments (#140, CB-11).

`ComparisonComputedArgsLoopCfg` (CB-9) admits a `brif` on a wide parameter or on an `icmp` in six
forms. Real loops also branch on a computed value that is not a comparison, for example
`v3 = iadd v1, v2; brif v3, ...`, or on a `clz`, `ctz`, `ineg`, `bmask` or `ireduce` result.

The aarch64 lowering of `brif c` selects `lower_brif` (3231), `is_nonzero_cmp` (650) and
`is_nonzero` (4977 for `i32`, 4979 for `i64`): one `cbnz` on the register of `c`. Only three rules
look through the definition of `c` first: `tbnz` (3251, `c` is a `band` with a one-bit constant
mask), `tbz` (3257, `c` is an `icmp eq` of a `band` with zero) and the comparison rule of
`is_nonzero_cmp` (4966, `c` is an `icmp` or a `uextend` of one). So here a `brif` condition may
also be a plain condition: a result of type `i32` or `i64` of a statement of any block that is not
an `icmp`, a `band` or a `uextend` (`plainEligible`).

The successors may take block arguments through original or critical-edge successors. Every edge
enters an existing nonentry block, so back edges and self loops are selected. The checker publishes
the edge split of the actual Stock lowering, as `ComparisonComputedArgsLoopCfg.check`. -/

namespace Backend.Stock.GeneralArgsLoopCfg2
open Backend.Proof.Driver
set_option autoImplicit false

/-- No lowering rule of a `brif` condition looks through a result of this instruction: it is not
an `icmp`, a `band` or a `uextend`. -/
def plainInst : Clif.Inst → Bool
  | .icmp .. => false
  | .binary .band .. => false
  | .extend .uextend .. => false
  | _ => true

/-- `stm` has a `plainInst` instruction, and it defines `c` as a result of type `ty`. -/
def plainResult (f : Clif.Function) (c : Nat) (ty : Clif.Ty) (stm : Clif.Stmt) : Bool :=
  plainInst stm.inst && (stm.results.zip (ComparisonComputedLoopCfg.resultTypesOf f stm)).contains (c,ty)

/-- `c` is a plain condition: a `plainResult` of type `i32` or `i64` of a statement of some
block. -/
def plainEligible (f : Clif.Function) (c : Nat) : Bool :=
  ComparisonLoopCfg.statementOf f (plainResult f c .i32) || ComparisonLoopCfg.statementOf f (plainResult f c .i64)

/-- A `brif` condition of block `b`: a condition of `ComparisonComputedArgsLoopCfg`, or a plain
condition. -/
def conditionEligible (f : Clif.Function) (b : Clif.Block) (c : Nat) : Bool :=
  ComparisonComputedArgsLoopCfg.conditionEligible f b c || plainEligible f c

/-- `ComparisonComputedArgsLoopCfg.controlEligible` with `conditionEligible`: jumps with any
arguments, returns, and branches with any arguments, each target an existing nonentry block. -/
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

/-- `ComparisonComputedArgsLoopCfg.sourceLeafEligible` with the conditions of `conditionEligible`.
Bodies and ABI are as there. -/
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

end Backend.Stock.GeneralArgsLoopCfg2
