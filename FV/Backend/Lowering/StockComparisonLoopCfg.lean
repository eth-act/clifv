import FV.Backend.Lowering.StockParameterLoopCfg
import FV.Backend.Lowering.StockComparisonImmCfg
import FV.Backend.Lowering.StockComparisonZeroCfg

/-! The loop class with comparison conditions (#140, T7b-7).

`ParameterLoopCfg` admits a `brif` only on a wide parameter. A typical `while (i < n)` loop
branches on `icmp slt i, n` in its header, so here a `brif` condition may also be a result of an
`icmp` in the branching block, in one of the forms of the comparison cores: two parameters of
one wide type (`ComparisonCfg`), a wide parameter and an encodable 12-bit `iconst`
(`ComparisonImmCfg`), or `eq`/`ne` of a wide parameter with `iconst 0` (`ComparisonZeroCfg`).
The operands may be parameters of any block, and the constant may be defined in any block. The
other conditions are those of `ParameterLoopCfg`. -/

namespace Backend.Stock.ComparisonLoopCfg
open Backend.Proof.Driver
set_option autoImplicit false

/-- `x` is a parameter of type `ty` of some block. -/
def parameterOf (f : Clif.Function) (x : Nat) (ty : Clif.Ty) : Bool :=
  f.blocks.any fun b => b.params.contains (x,ty)

/-- Some block has a statement that `eligible` accepts. -/
def statementOf (f : Clif.Function) (eligible : Clif.Stmt → Bool) : Bool :=
  f.blocks.any fun b => b.body.any eligible

/-- `stm` defines `condition` by an `icmp cc _ x y` in one of the forms of the comparison cores:
`x` and `y` are parameters of one wide type; or `x` is a wide parameter and `y` is a result of an
encodable 12-bit `iconst`, nonzero for `eq`/`ne`; or `cc` is `eq` or `ne`, `x` is a wide
parameter, and `y` is a result of `iconst 0`. -/
def comparisonEligible (f : Clif.Function) (condition : Nat) (stm : Clif.Stmt) : Bool :=
  stm.results.contains condition && match stm.inst with
    | .icmp cc _ x y =>
      (parameterOf f x .i32 && parameterOf f y .i32) || (parameterOf f x .i64 && parameterOf f y .i64) ||
      ((parameterOf f x .i32 || parameterOf f x .i64) &&
        (statementOf f (ComparisonImmCfg.constantEligible cc y) ||
          ((cc == .eq || cc == .ne) && statementOf f (ComparisonZeroCfg.constantEligible y))))
    | _ => false

/-- A `brif` condition of block `b`: a wide parameter of any block, or a result of an eligible
comparison in the body of `b`. -/
def conditionEligible (f : Clif.Function) (b : Clif.Block) (c : Nat) : Bool :=
  ParameterCfg.parameterEligible f c || b.body.any (comparisonEligible f c)

/-- `ParameterLoopCfg.controlEligible` with `conditionEligible` for the `brif` condition of
block `b`. -/
def controlEligible (f : Clif.Function) (b : Clif.Block) : Clif.Terminator → Bool
  | .jump bc => ParameterLoopCfg.targetNonentry f bc
  | .ret _ => true
  | .brif c yes no => conditionEligible f b c && yes.args.isEmpty && no.args.isEmpty &&
    ParameterLoopCfg.targetNonentry f yes && ParameterLoopCfg.targetNonentry f no
  | _ => false

/-- As `controlEligible`, and a nonentry block may also end in `trap`. -/
def controlLeafEligible (f : Clif.Function) (bi : Nat) (b : Clif.Block) : Clif.Terminator → Bool
  | .trap _ => bi != 0
  | term => controlEligible f b term

/-- `ParameterLoopCfg.sourceLeafEligible` with comparison conditions. -/
def sourceLeafEligible (f : Clif.Function) : Bool :=
  f.blocks.zipIdx.all (fun (b,bi) => controlLeafEligible f bi b b.term) &&
  f.blocks.all (fun b => b.body.all Scalar.maskMixedBodyEligible) &&
  f.sig.params.all Scalar.narrowAbiEligible && f.sig.returns.all Scalar.narrowAbiEligible

def sourceOk (f : Clif.Function) : Bool :=
  sourceLeafEligible f && lowerScopeB f && dominatedB f && sigAbiOk f.sig

def check (f : Clif.Function) (vc : VCode) : Bool :=
  sourceOk f && match Stock.lower f with
  | .error _ => false
  | .ok result => decide (result.code = vc)

end Backend.Stock.ComparisonLoopCfg
