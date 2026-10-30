import FV.Backend.Lowering.StockScalar
import FV.Backend.StockArithmeticCheck

namespace Backend.Stock.ParameterCfg
open Backend.Proof.Driver
set_option autoImplicit false

/-- A condition is an original wide parameter, including inherited block parameters. -/
def parameterEligible (f : Clif.Function) (c : Nat) : Bool :=
  f.blocks.any fun b => b.params.any fun (value,ty) =>
    value == c && (ty == .i32 || ty == .i64)

def targetAfter (f : Clif.Function) (bi : Nat) (bc : Clif.BlockCall) : Bool :=
  match f.blocks.findIdx? (·.id == bc.block) with
  | some target => decide (bi < target)
  | none => false

/-- Original source ranking; conditional copies stay empty, ordinary jump copies remain arbitrary. -/
def controlEligible (f : Clif.Function) (bi : Nat) : Clif.Terminator → Bool
  | .jump bc => targetAfter f bi bc
  | .ret _ => true
  | .brif c yes no => parameterEligible f c && yes.args.isEmpty && no.args.isEmpty &&
    targetAfter f bi yes && targetAfter f bi no
  | _ => false

def sourceEligible (f : Clif.Function) : Bool :=
  f.blocks.zipIdx.all (fun (b,bi) => controlEligible f bi b.term) &&
  f.blocks.all (fun b => b.body.all Scalar.maskMixedBodyEligible) &&
  f.sig.params.all Scalar.narrowAbiEligible && f.sig.returns.all Scalar.narrowAbiEligible

def hasNonentryConditional (f : Clif.Function) : Bool :=
  f.blocks.drop 1 |>.any fun b => match b.term with | .brif .. => true | _ => false

def sourceOk (f : Clif.Function) : Bool :=
  sourceEligible f && lowerScopeB f && dominatedB f && sigAbiOk f.sig

def check (f : Clif.Function) (vc : VCode) : Bool :=
  sourceOk f && match Stock.lower f with
  | .error _ => false
  | .ok result => decide (result.code = vc)
end Backend.Stock.ParameterCfg
