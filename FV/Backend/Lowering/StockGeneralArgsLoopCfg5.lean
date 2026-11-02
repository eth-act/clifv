import FV.Backend.Lowering.StockGeneralLoopCfg4

/-! The loop class with one-bit tests and zero extensions as conditions, with block arguments
(#140, CB-13).

`GeneralArgsLoopCfg4` (CB-12b) admits a `brif` on a parameter, a comparison in six forms, or a
plain wide, `i8` or `i16` value; a plain value is not an `icmp`, a `band` or a `uextend`, because
three lowering rules look through such a definition. Here a `brif` condition may also be

* a one-bit test `band x k` with `k = iconst n` and `n` one set bit below the width of `x`
  (`testBitEligible`), lowered by `tbnz x, #bit` (rule 3251);
* a zero test `icmp eq (band x k) 0` of such a mask (`testBitZeroEligible`), lowered by
  `tbz x, #bit` (rule 3257);
* a zero extension `uextend (icmp cc x, y)` of a comparison of two wide parameters of one width
  (`uextComparisonEligible`), lowered by `subs` and `b.cond` through the `maybe_uextend` look-through
  of `is_nonzero_cmp` (rule 4966);
* a plain zero extension: an `i16`, `i32` or `i64` result of `uextend x` where `x` is a parameter or
  a result of a statement that is not an `icmp` (`uextPlainEligible`), lowered as a plain value.

The successors may take block arguments, and every edge enters an existing nonentry block, as in
`GeneralArgsLoopCfg4`. The checker publishes the edge split of the actual Stock lowering. -/

namespace Backend.Stock.GeneralArgsLoopCfg5
open Backend.Proof.Driver
set_option autoImplicit false

/-- `x` is declared with type `ty`: a parameter of type `ty` of some block, or a result of type `ty`
of a statement of some block. -/
def declaredOf (f : Clif.Function) (x : Nat) (ty : Clif.Ty) : Bool :=
  ComparisonLoopCfg.parameterOf f x ty ||
    ComparisonLoopCfg.statementOf f fun stm =>
      (stm.results.zip (ComparisonComputedLoopCfg.resultTypesOf f stm)).contains (x,ty)

/-- The single set bit of `n` below `width`, as `test_and_compare_bit_const` computes it. -/
def singleBit (width : Nat) (n : Int) : Option Nat :=
  match (List.range 64).filter ((u64 n).testBit ·) with
  | [bit] => if bit < width then some bit else none
  | _ => none

/-- The integer types of the source. -/
def intTypes : List Clif.Ty := [.i8,.i16,.i32,.i64]

/-- `stm` defines `k` by an `iconst` whose value has one set bit below the width of a declared
type of `x`. -/
def maskEligible (f : Clif.Function) (x k : Nat) (stm : Clif.Stmt) : Bool :=
  stm.results.contains k && match stm.inst with
    | .iconst ty imm => intTypes.any fun tx =>
      declaredOf f x tx && (singleBit tx.width ((u64 (imm64OfIconst ty imm) : Nat) : Int)).isSome
    | _ => false

/-- `stm` defines `c` by a one-bit test `band x k`. -/
def testBitStatement (f : Clif.Function) (c : Nat) (stm : Clif.Stmt) : Bool :=
  stm.results.contains c && match stm.inst with
    | .binary .band _ x k => ComparisonLoopCfg.statementOf f (maskEligible f x k)
    | _ => false

/-- `c` is a one-bit test: a result of `band x k` with `k` a one-bit mask of `x`. -/
def testBitEligible (f : Clif.Function) (c : Nat) : Bool :=
  ComparisonLoopCfg.statementOf f (testBitStatement f c)

/-- `stm` defines `c` by a zero test `icmp eq y z` of a one-bit test `y`, with `z = iconst 0`. -/
def testBitZeroStatement (f : Clif.Function) (c : Nat) (stm : Clif.Stmt) : Bool :=
  stm.results.contains c && match stm.inst with
    | .icmp .eq _ y z => testBitEligible f y && ComparisonLoopCfg.statementOf f (ComparisonZeroCfg.constantEligible z)
    | _ => false

/-- `c` is a zero test of a one-bit mask. -/
def testBitZeroEligible (f : Clif.Function) (c : Nat) : Bool :=
  ComparisonLoopCfg.statementOf f (testBitZeroStatement f c)

/-- `stm` defines `z` by a comparison of two parameters of one wide type. -/
def wideComparisonStatement (f : Clif.Function) (z : Nat) (stm : Clif.Stmt) : Bool :=
  stm.results.contains z && match stm.inst with
    | .icmp _ _ x y =>
      (ComparisonLoopCfg.parameterOf f x .i32 && ComparisonLoopCfg.parameterOf f y .i32) ||
        (ComparisonLoopCfg.parameterOf f x .i64 && ComparisonLoopCfg.parameterOf f y .i64)
    | _ => false

/-- `stm` defines `c` by `uextend z` of such a comparison. -/
def uextComparisonStatement (f : Clif.Function) (c : Nat) (stm : Clif.Stmt) : Bool :=
  stm.results.contains c && match stm.inst with
    | .extend .uextend _ z => ComparisonLoopCfg.statementOf f (wideComparisonStatement f z)
    | _ => false

/-- `c` is a zero extension of a comparison of two wide parameters of one width. -/
def uextComparisonEligible (f : Clif.Function) (c : Nat) : Bool :=
  ComparisonLoopCfg.statementOf f (uextComparisonStatement f c)

/-- `x` is a parameter of some block, or a result of a statement that is not an `icmp`. -/
def nonComparisonOperand (f : Clif.Function) (x : Nat) : Bool :=
  (f.blocks.any fun b => b.params.any fun (value,_) => value == x) ||
    ComparisonLoopCfg.statementOf f fun stm => stm.results.contains x && match stm.inst with
      | .icmp .. => false
      | _ => true

/-- `stm` defines `c` as an `i16`, `i32` or `i64` result of `uextend x` with `x` not a comparison. -/
def uextPlainStatement (f : Clif.Function) (c : Nat) (stm : Clif.Stmt) : Bool :=
  match stm.inst with
  | .extend .uextend _ x =>
    [Clif.Ty.i16,.i32,.i64].any (fun ty => (stm.results.zip (ComparisonComputedLoopCfg.resultTypesOf f stm)).contains (c,ty)) &&
      nonComparisonOperand f x
  | _ => false

/-- `c` is a plain zero extension. -/
def uextPlainEligible (f : Clif.Function) (c : Nat) : Bool :=
  ComparisonLoopCfg.statementOf f (uextPlainStatement f c)

/-- A `brif` condition of block `b`: a condition of `GeneralArgsLoopCfg4`, a one-bit test, a zero
test of a one-bit mask, a zero extension of a wide comparison, or a plain zero extension. -/
def conditionEligible (f : Clif.Function) (b : Clif.Block) (c : Nat) : Bool :=
  GeneralArgsLoopCfg4.conditionEligible f b c || testBitEligible f c || testBitZeroEligible f c ||
    uextComparisonEligible f c || uextPlainEligible f c

/-- `GeneralArgsLoopCfg4.controlEligible` with `conditionEligible`: jumps with any arguments,
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

/-- `GeneralArgsLoopCfg4.sourceLeafEligible` with the conditions of `conditionEligible`. Bodies
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

end Backend.Stock.GeneralArgsLoopCfg5
