import FV.Backend.Lowering.StockGeneralLoopCfg2

/-! The loop class with plain `i8` conditions and block arguments (#140, CB-12).

`GeneralArgsLoopCfg2` (CB-11) admits a `brif` on an `i32` or `i64` condition: a parameter, an
`icmp` in six forms, or a plain computed value. Real functions also branch on an `i8` value, for
example a parameter `v0: i8` or the `i8` result of an `iadd` or an `iconst`.

The aarch64 lowering of `brif c` for an `i8` condition `c` selects `lower_brif` (3231),
`is_nonzero_cmp` (650) and rule 4988 of `is_nonzero`: `tst w, #0xff` and `b.ne`. As for a wide
condition, only the `tbnz` and `tbz` rules (3251, 3257) and the comparison rule of
`is_nonzero_cmp` (4966) look through the definition of `c` first, so the plain result kinds are
those of `GeneralArgsLoopCfg2.plainInst`. Here a `brif` condition may also be a narrow condition:
an `i8` parameter of a block, or an `i8` result of a statement that is not an `icmp`, a `band`
or a `uextend` (`narrowEligible`).

The successors may take block arguments, and every edge enters an existing nonentry block, as in
`GeneralArgsLoopCfg2`. The checker publishes the edge split of the actual Stock lowering. -/

namespace Backend.Stock.GeneralArgsLoopCfg3
open Backend.Proof.Driver
set_option autoImplicit false

/-- `c` is an `i8` parameter of some block. -/
def narrowParameterEligible (f : Clif.Function) (c : Nat) : Bool :=
  f.blocks.any fun b => b.params.any fun (value,ty) => value == c && ty == .i8

/-- `c` is a narrow condition: an `i8` parameter of some block, or a
`GeneralArgsLoopCfg2.plainResult` of type `i8` of a statement of some block. -/
def narrowEligible (f : Clif.Function) (c : Nat) : Bool :=
  narrowParameterEligible f c || ComparisonLoopCfg.statementOf f (GeneralArgsLoopCfg2.plainResult f c .i8)

/-- A `brif` condition of block `b`: a condition of `GeneralArgsLoopCfg2`, or a narrow
condition. -/
def conditionEligible (f : Clif.Function) (b : Clif.Block) (c : Nat) : Bool :=
  GeneralArgsLoopCfg2.conditionEligible f b c || narrowEligible f c

/-- `GeneralArgsLoopCfg2.controlEligible` with `conditionEligible`: jumps with any arguments,
returns, and branches with any arguments, each target an existing nonentry block. -/
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

/-- `GeneralArgsLoopCfg2.sourceLeafEligible` with the conditions of `conditionEligible`. Bodies
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

end Backend.Stock.GeneralArgsLoopCfg3
