import FV.Backend.Lowering.StockParameterCfg

namespace Backend.Stock.ParameterLoopCfg
open Backend.Proof.Driver
set_option autoImplicit false

/-- A destination is an existing nonentry block. Unlike `ParameterCfg.targetAfter`, it may
precede or equal its source block, so back edges and self loops are selected. -/
def targetNonentry (f : Clif.Function) (bc : Clif.BlockCall) : Bool :=
  match f.blocks.findIdx? (·.id == bc.block) with
  | some target => decide (0 < target)
  | none => false

/-- `ParameterCfg.controlEligible` with `targetNonentry` in place of the forward rank:
jumps with any arguments, returns, and wide-parameter branches with empty arguments. -/
def controlEligible (f : Clif.Function) : Clif.Terminator → Bool
  | .jump bc => targetNonentry f bc
  | .ret _ => true
  | .brif c yes no => ParameterCfg.parameterEligible f c && yes.args.isEmpty && no.args.isEmpty &&
    targetNonentry f yes && targetNonentry f no
  | _ => false

/-- As `controlEligible`, and a nonentry block may also end in `trap`. -/
def controlLeafEligible (f : Clif.Function) (bi : Nat) : Clif.Terminator → Bool
  | .trap _ => bi != 0
  | term => controlEligible f term

/-- `ParameterCfg.sourceLeafEligible` without the forward rank: every edge enters a nonentry
block, so the selected CFGs may contain loops. Bodies and ABI are as in `ParameterCfg`.
The loop structure is not restricted further; the composition proofs (#140, T7b-5) may need
an extra structural condition, for example reducibility or a condition on back-edge arguments. -/
def sourceLeafEligible (f : Clif.Function) : Bool :=
  f.blocks.zipIdx.all (fun (b,bi) => controlLeafEligible f bi b.term) &&
  f.blocks.all (fun b => b.body.all Scalar.maskMixedBodyEligible) &&
  f.sig.params.all Scalar.narrowAbiEligible && f.sig.returns.all Scalar.narrowAbiEligible

def sourceOk (f : Clif.Function) : Bool :=
  sourceLeafEligible f && lowerScopeB f && dominatedB f && sigAbiOk f.sig

def check (f : Clif.Function) (vc : VCode) : Bool :=
  sourceOk f && match Stock.lower f with
  | .error _ => false
  | .ok result => decide (result.code = vc)
end Backend.Stock.ParameterLoopCfg
