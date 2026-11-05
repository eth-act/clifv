import FV.Backend.Lowering.StockConditionalCfg

namespace Backend.Stock.ComparisonZeroCfg
set_option autoImplicit false

/-- `stm` defines `y` by an `iconst` of zero. -/
def constantEligible (y : Nat) (stm : Clif.Stmt) : Bool :=
  stm.results.contains y && match stm.inst with
    | .iconst _ k => k == 0
    | _ => false

/-- `stm` defines `condition` by an `icmp eq` or `icmp ne` of a wide entry
parameter (`.i32` or `.i64`) with a value that the entry body defines by
`iconst 0`. Stock lowers the branch on it to one `cbz` (`eq`) or `cbnz`
(`ne`) on the parameter. -/
def zeroEligible (entry : Clif.Block) (condition : Nat) (stm : Clif.Stmt) : Bool :=
  stm.results.contains condition && match stm.inst with
    | .icmp cc _ x y =>
      (cc == .eq || cc == .ne) &&
      (entry.params.contains (x,.i32) || entry.params.contains (x,.i64)) &&
        entry.body.any (constantEligible y)
    | _ => false

/-- Branches on a direct entry `eq`/`ne` comparison of an entry parameter
with zero into return or trap blocks. Every nonentry block has no
parameters, and both targets carry no arguments, preserving the existing
legacy edge-copy interface. -/
def leafEligible (f : Clif.Function) : Bool :=
  match f.blocks with
  | entry :: rest => match entry.term with
    | .brif condition yes no =>
      entry.body.any (zeroEligible entry condition) &&
      ConditionalCfg.targetEligible f yes && ConditionalCfg.targetEligible f no &&
      rest.all (fun b => b.params.isEmpty && match b.term with | .ret _ | .trap _ => true | _ => false) &&
      f.blocks.all (fun b => b.body.all Scalar.maskMixedBodyEligible) &&
      f.sig.params.all Scalar.narrowAbiEligible && f.sig.returns.all Scalar.narrowAbiEligible
    | _ => false
  | _ => false

def sourceOk (f : Clif.Function) : Bool :=
  leafEligible f && Backend.Proof.Driver.lowerScopeB f &&
    Backend.Proof.Driver.dominatedB f && Backend.sigAbiOk f.sig

def check (f : Clif.Function) (vc : VCode) : Bool :=
  sourceOk f && match Stock.lower f with
  | .error _ => false
  | .ok result => decide (result.code = vc)

end Backend.Stock.ComparisonZeroCfg
