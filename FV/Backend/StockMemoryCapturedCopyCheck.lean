import FV.Backend.StockMemoryStoreCfgCheck

namespace Backend.Stock.MemoryCapturedCopy
open Backend.Proof.Driver
set_option autoImplicit false

/-- Keep the original positions while selecting ordinary instructions. -/
def nonNops (b : Clif.Block) : List (Clif.Stmt × Nat) :=
  b.body.zipIdx.filter (fun pair => decide (pair.1.inst ≠ .nop))

/-- Select the original load/load/store CFG, including inherited base parameters and NOPs. -/
def eligible (f : Clif.Function) : Bool :=
  match f.blocks with
  | [entry,target] => match entry.term,target.term,nonNops target with
    | .jump ⟨dst,[]⟩,.ret [],
        [(⟨[value],.load .load .i64 vf base 8⟩,iv),
         (⟨[pointer],.load .load .i64 pf otherBase 0⟩,ip),
         (⟨[],.store .store .i64 sf stored destination 0⟩,is)] =>
      dst == target.id && base == otherBase && value == stored && pointer == destination &&
        decide (iv < is) && decide (ip < is) &&
        (entry.params.map (·.1)).contains base && vf.trapCode.isNone &&
        pf.trapCode.isNone && sf.trapCode.isNone &&
        entry.body.all (fun stm => decide (stm.inst = .nop))
    | _,_,_ => false
  | _ => false

def sourceOk (f : Clif.Function) : Bool :=
  eligible f && lowerScopeB f && dominatedB f && sigAbiOk f.sig &&
    !(sigRets f.sig).any (·.purpose == .sret) && Memory.registerEntry f.sig

/-- Bind the source-only class to the actual Stock artifact and existing CFG effects. -/
def check (f : Clif.Function) (vc : VCode) : Bool :=
  sourceOk f && match Stock.lower f with
  | .error _ => false
  | .ok result => decide (result.code = vc) && MemoryStoreCfg.effectsOnly vc

end Backend.Stock.MemoryCapturedCopy
