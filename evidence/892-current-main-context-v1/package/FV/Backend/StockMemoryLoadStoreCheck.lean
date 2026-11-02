import FV.Backend.StockMemoryStoreCheck

namespace Backend.Stock.MemoryLoadStore
open Backend.Proof.Driver
set_option autoImplicit false

/-- Select original mixed load/store syntax before any actual lowering attempt. -/
def eligible (f : Clif.Function) : Bool :=
  match f.blocks with
  | [b] => match b.body with
    | [⟨[z],.load .load loadTy loadFlags loadPointer 0⟩,
        ⟨[],.store op ty storeFlags value storePointer 0⟩] => match b.term with
      | .ret [returned] => z == returned && MemoryStore.scalarParameter loadTy &&
          (b.params.map (·.1)).contains loadPointer && (b.params.map (·.1)).contains storePointer &&
          b.params.any (fun q => q.1 == value && MemoryStore.scalarParameter q.2) &&
          loadFlags.trapCode.isNone && storeFlags.trapCode.isNone
      | _ => false
    | _ => false
  | _ => false

def sourceOk (f : Clif.Function) : Bool :=
  eligible f && lowerScopeB f && dominatedB f && sigAbiOk f.sig &&
    !(sigRets f.sig).any (·.purpose == .sret) && Memory.registerEntry f.sig

/-- Bind original source selection to the actual Stock artifact and existing effect policy. -/
def check (f : Clif.Function) (vc : VCode) : Bool :=
  sourceOk f && match Stock.lower f with
  | .error _ => false
  | .ok result => decide (result.code = vc) && Memory.Store.effectsOnly vc

end Backend.Stock.MemoryLoadStore
