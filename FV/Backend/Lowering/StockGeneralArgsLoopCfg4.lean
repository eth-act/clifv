import FV.Backend.Lowering.StockGeneralLoopCfg3

/-! The loop class with plain `i16` conditions and block arguments (#140, CB-12b).

`GeneralArgsLoopCfg3` (CB-12) admits a `brif` on a condition of `GeneralArgsLoopCfg2` (an `i32`
or `i64` parameter, an `icmp` in six forms, or a plain computed value) or on a plain `i8`
condition. Real functions also branch on an `i16` value, for example a parameter `v0: i16` or the
`i16` result of an `iadd` or an `iconst`.

The aarch64 lowering of `brif c` for an `i16` condition `c` selects `lower_brif` (3231),
`is_nonzero_cmp` (650) and rule 4977 of `is_nonzero`: `uxth t, w` into a fresh temporary `t` and
`cbnz t`. As for the other conditions, only the `tbnz` and `tbz` rules (3251, 3257) and the
comparison rule of `is_nonzero_cmp` (4966) look through the definition of `c` first, so the plain
result kinds are those of `GeneralArgsLoopCfg2.plainInst`. Here a `brif` condition may also be an
`i16` condition: an `i16` parameter of a block, or an `i16` result of a statement that is not an
`icmp`, a `band` or a `uextend` (`narrow16Eligible`).

The successors may take block arguments, and every edge enters an existing nonentry block, as in
`GeneralArgsLoopCfg3`. The checker publishes the edge split of the actual Stock lowering. -/

namespace Backend.Stock.GeneralArgsLoopCfg4
open Backend.Proof.Driver
set_option autoImplicit false

/-- `c` is an `i16` parameter of some block. -/
def narrow16ParameterEligible (f : Clif.Function) (c : Nat) : Bool :=
  f.blocks.any fun b => b.params.any fun (value,ty) => value == c && ty == .i16

/-- `c` is an `i16` condition: an `i16` parameter of some block, or a
`GeneralArgsLoopCfg2.plainResult` of type `i16` of a statement of some block. -/
def narrow16Eligible (f : Clif.Function) (c : Nat) : Bool :=
  narrow16ParameterEligible f c || ComparisonLoopCfg.statementOf f (GeneralArgsLoopCfg2.plainResult f c .i16)

/-- A `brif` condition of block `b`: a condition of `GeneralArgsLoopCfg3`, or an `i16`
condition. -/
def conditionEligible (f : Clif.Function) (b : Clif.Block) (c : Nat) : Bool :=
  GeneralArgsLoopCfg3.conditionEligible f b c || narrow16Eligible f c

/-- `GeneralArgsLoopCfg3.controlEligible` with `conditionEligible`: jumps with any arguments,
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

/-- `GeneralArgsLoopCfg3.sourceLeafEligible` with the conditions of `conditionEligible`. Bodies
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

end Backend.Stock.GeneralArgsLoopCfg4
