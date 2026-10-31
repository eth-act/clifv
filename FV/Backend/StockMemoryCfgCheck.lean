import FV.Backend.StockMemoryCheck

namespace Backend.Stock.MemoryCfg
open Backend.Proof.Driver
set_option autoImplicit false

/-- The captured source shape uses one entry NOP and one inherited-pointer load. -/
def eligible (f : Clif.Function) : Bool :=
  match f.blocks with
  | [entry,target] => match entry.body,target.body,entry.term,target.term with
    | [⟨[],.nop⟩],[⟨[],.nop⟩,⟨[z],.load .load .i32 flags x 0⟩],.jump ⟨dst,[]⟩,.ret [ret] =>
      dst == target.id && z == ret && (entry.params.map (·.1)).contains x && flags.trapCode.isNone
    | _,_,_,_ => false
  | _ => false

def sourceOk (f : Clif.Function) : Bool :=
  eligible f && lowerScopeB f && dominatedB f && sigAbiOk f.sig &&
    !(sigRets f.sig).any (·.purpose == .sret) && Memory.registerEntry f.sig

/-- The additive CFG whitelist also permits the actual direct jump. -/
def effectInstruction : MInst → Bool
  | .args .. | .load .. | .rets .. | .jump .. => true
  | _ => false

def effectsOnly (vc : VCode) : Bool :=
  vc.blocks.toList.all (fun b => b.insts.toList.all effectInstruction)

def check (f : Clif.Function) (vc : VCode) : Bool :=
  sourceOk f && match Stock.lower f with
  | .error _ => false
  | .ok result => decide (result.code = vc) && effectsOnly vc

end Backend.Stock.MemoryCfg
