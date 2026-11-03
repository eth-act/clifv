import FV.Backend.Lowering.StockGeneralLoopCfg6

/-! The loop class with plain `band` conditions, with block arguments (#140, CB-15).

`GeneralArgsLoopCfg6` (CB-14c) admits a `brif` on a condition of `GeneralArgsLoopCfg5`. A `band`
condition is there only the one-bit test of the `tbnz` rule 3251. Here a `brif` condition may also
be a plain `band` (`plainBandEligible`): an `i32` or `i64` result of `band x k` whose mask `k` is
not a one-bit mask of `x` (`nonTestMask`), that is,

* `k` is a block parameter, or
* `k` is a result of a statement that is not an `iconst`, or
* `k` is a result of `iconst n` and `n` does not have exactly one set bit below the width of a
  declared type of `x`.

Rule 3251 does not match such a condition, so ordinary `brif` (3231) lowers it to the `and` of the
body and one `cbnz`. The other terminators are those of `GeneralArgsLoopCfg6`. The checker
publishes the edge split of the actual Stock lowering. -/

namespace Backend.Stock.GeneralArgsLoopCfg7
open Backend.Proof.Driver
set_option autoImplicit false

/-- `k` is not a one-bit mask of `x`: a block parameter, a result of a statement that is not an
`iconst`, or a result of an `iconst` whose value does not have exactly one set bit below the width
of a declared type of `x`. -/
def nonTestMask (f : Clif.Function) (x k : Nat) : Bool :=
  (f.blocks.any fun b => b.params.any fun (value,_) => value == k) ||
    ComparisonLoopCfg.statementOf f fun stm => stm.results.contains k && match stm.inst with
      | .iconst ty imm => GeneralArgsLoopCfg5.intTypes.any fun tx =>
        GeneralArgsLoopCfg5.declaredOf f x tx &&
          (GeneralArgsLoopCfg5.singleBit tx.width ((u64 (imm64OfIconst ty imm) : Nat) : Int)).isNone
      | _ => true

/-- `stm` defines `c` as an `i32` or `i64` result of `band x k` with `k` not a one-bit mask of
`x`. -/
def plainBandStatement (f : Clif.Function) (c : Nat) (stm : Clif.Stmt) : Bool :=
  match stm.inst with
  | .binary .band _ x k =>
    [Clif.Ty.i32,.i64].any (fun ty => (stm.results.zip (ComparisonComputedLoopCfg.resultTypesOf f stm)).contains (c,ty)) &&
      nonTestMask f x k
  | _ => false

/-- `c` is a plain `band`. -/
def plainBandEligible (f : Clif.Function) (c : Nat) : Bool :=
  ComparisonLoopCfg.statementOf f (plainBandStatement f c)

/-- A `brif` condition of block `b`: a condition of `GeneralArgsLoopCfg5`, or a plain `band`. -/
def conditionEligible (f : Clif.Function) (b : Clif.Block) (c : Nat) : Bool :=
  GeneralArgsLoopCfg5.conditionEligible f b c || plainBandEligible f c

/-- `GeneralArgsLoopCfg6.controlEligible` with `conditionEligible`: branches with any arguments,
each target an existing nonentry block; the other terminators as there. -/
def controlEligible (f : Clif.Function) (b : Clif.Block) : Clif.Terminator → Bool
  | .brif c yes no => conditionEligible f b c &&
    ParameterLoopCfg.targetNonentry f yes && ParameterLoopCfg.targetNonentry f no
  | term => GeneralArgsLoopCfg6.controlEligible f b term

/-- As `controlEligible`, and a nonentry block may also end in `trap`. -/
def controlLeafEligible (f : Clif.Function) (bi : Nat) (b : Clif.Block) : Clif.Terminator → Bool
  | .trap _ => bi != 0
  | term => controlEligible f b term

/-- `GeneralArgsLoopCfg6.sourceLeafEligible` with the terminators of `controlLeafEligible`. Bodies
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

end Backend.Stock.GeneralArgsLoopCfg7
