import FV.Backend.StockArithmeticCheck
import FV.Backend.DeadCleanup

namespace Backend.Stock.Memory
open Backend.Proof.Driver
set_option autoImplicit false

/-- Original source syntax of the first memory delivery class. -/
def eligible (f : Clif.Function) : Bool :=
  match f.blocks with
  | [b] => match b.body with
    | [⟨[z],.load .load .i32 flags x 0⟩] => match b.term with
      | .ret [ret] => z == ret && (b.params.map (·.1)).contains x && flags.trapCode.isNone
      | _ => false
    | _ => false
  | _ => false

def registerEntry (sig : Clif.Signature) : Bool :=
  (locsOf sig).all fun loc => match loc with | .reg _ => true | .stack _ => false

def sourceOk (f : Clif.Function) : Bool :=
  eligible f && lowerScopeB f && dominatedB f && sigAbiOk f.sig &&
    !(sigRets f.sig).any (·.purpose == .sret) && registerEntry f.sig

/-- First-class emitted instructions: ABI copies, loads and returns. -/
def effectInstruction : MInst → Bool
  | .args .. | .load .. | .rets .. => true
  | _ => false

/-- Actual emitted effects retain concrete semantics under value realization. -/
def effectsOnly (vc : VCode) : Bool :=
  vc.blocks.toList.all (fun b => b.insts.toList.all (effectInstruction))

def check (f : Clif.Function) (vc : VCode) : Bool :=
  sourceOk f && match Stock.lower f with
  | .error _ => false
  | .ok result => decide (result.code = vc) && effectsOnly vc

end Backend.Stock.Memory
