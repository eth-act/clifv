import FV.Backend.StockMemoryStoreCheck

namespace Backend.Stock.MemoryStoreCfg

/-- The CFG adapter retains the store whitelist and permits direct jumps. -/
def effectInstruction : MInst → Bool
  | .jump .. => true
  | i => Memory.Store.effectInstruction i

def effectsOnly (vc : VCode) : Bool :=
  vc.blocks.toList.all (fun b => b.insts.toList.all effectInstruction)

open Backend.Proof.Driver
set_option autoImplicit false

/-- Select one original store and require every other statement to be a NOP. -/
def candidate (entry target : Clif.Block) (pair : Clif.Stmt × Nat) : Bool :=
  match pair.1 with
  | ⟨[],.store op ty flags value pointer 0⟩ =>
    (entry.params.map (·.1)).contains pointer &&
      entry.params.any (fun q => q.1 == value && MemoryStore.scalarParameter q.2) &&
      flags.trapCode.isNone &&
      target.body.zipIdx.all (fun q => q.2 == pair.2 || decide (q.1.inst = .nop))
  | _ => false

/-- Read the complete CFG shape from original source syntax. -/
def eligible (f : Clif.Function) : Bool :=
  match f.blocks with
  | [entry,target] => match entry.term,target.term with
    | .jump ⟨dst,[]⟩,.ret [] => dst == target.id &&
      entry.body.all (fun stm => decide (stm.inst = .nop)) &&
      target.body.zipIdx.any (candidate entry target)
    | _,_ => false
  | _ => false

def sourceOk (f : Clif.Function) : Bool :=
  eligible f && lowerScopeB f && dominatedB f && sigAbiOk f.sig &&
    !(sigRets f.sig).any (·.purpose == .sret) && Memory.registerEntry f.sig

def check (f : Clif.Function) (vc : VCode) : Bool :=
  sourceOk f && match Stock.lower f with
  | .error _ => false
  | .ok result => decide (result.code = vc) && effectsOnly vc

end Backend.Stock.MemoryStoreCfg
