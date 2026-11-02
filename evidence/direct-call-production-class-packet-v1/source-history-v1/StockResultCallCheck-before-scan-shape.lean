import FV.Backend.StockVoidCallCheck
import FV.Backend.ABIReadOnly

namespace Backend.Stock.ResultCall
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false

structure SourceData where
  block : Clif.Block
  fn : Clif.FnRef
  args : List Nat
  ext : Clif.ExtFunc
  bytes : List Nat
  result : Nat
  returned : Clif.AbiParam

def sourceData? (f : Clif.Function) : Option SourceData := do
  let [block] := f.blocks | none
  let [⟨[result],.call fn args⟩] := block.body | none
  let ext ← f.extern? fn
  let [returned] := ext.sig.returns | none
  let bytes ← (sigParamBytes ext.sig).toOption
  pure ⟨block,fn,args,ext,bytes,result,returned⟩

/-- This selects a source class; it adds no caller proof premise. -/
def sourceB (f : Clif.Function) (data : SourceData) : Bool :=
  decide (f.blocks = [data.block]) &&
  decide (data.block.body = [⟨[data.result],.call data.fn data.args⟩]) &&
  decide (data.block.term = .ret [data.result]) &&
  decide (f.sig.returns = [data.returned]) && decide (data.ext.sig.returns = [data.returned]) &&
  decide (data.returned.ty = .i64) && decide (f.extern? data.fn = some data.ext) &&
  decide (sigParamBytes data.ext.sig = .ok data.bytes) && decide (data.bytes.length ≤ 8) &&
  decide (returnPins f 1 = some [.x 0])

def resolvedReg? (result : Stock.Result) (source : Nat) : Option Reg := do
  let reg ← result.ctx.valueReg? source
  pure (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1) reg)

/-- Check the same actual definition, alias destination, argument pins and return use. -/
def codeB (data : SourceData) (result : Stock.Result) : Bool :=
  match resolvedReg? result data.result,result.code.blocks[0]? with
  | some destination,some block =>
    match block.insts.toList.reverse with
    | .rets returns :: .call info :: _ =>
      decide (result.code.blocks.size = 1) && destination.isVirtual &&
      decide (destination.cls = .int) && decide (info.dest = .sym data.ext.name) &&
      decide (info.defs = [(.x 0,destination)]) && decide (returns = [(destination,.x 0)]) &&
      match data.args.mapM (resolvedReg? result) with
      | none => false
      | some arguments => decide (info.uses = arguments.zip (regLocs data.ext.sig))
    | _ => false
  | _,_ => false

/-- Retained records expose the source binder before final alias resolution. -/
def scanB (data : SourceData) (result : Stock.Result) (event : Stock.BlockScanEvent) : Bool :=
  if event.block == 0 then
    match event.ctx.valueReg? data.result,event.output.code.toList with
    | some sourceReg,[.call info,.rets returns] =>
      match info.defs with
      | [(.x 0,destination)] =>
        decide (info.dest = .sym data.ext.name) &&
        decide (returns = [(sourceReg,.x 0)]) &&
        decide (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1) sourceReg =
          Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1) destination) &&
        match data.args.mapM event.ctx.valueReg? with
        | none => false
        | some arguments => decide (info.uses = arguments.zip (regLocs data.ext.sig))
      | _ => false
    | _,_ => false
  else true

def instruction (sig : Clif.Signature) (block pc : Nat) (i : MInst) : Bool :=
  match i with
  | .call _ => true
  | _ => Backend.ABIReadOnly.instruction sig block pc i

def codeCheck (sig : Clif.Signature) (vc : VCode) : Bool :=
  vc.blocks.toList.zipIdx.all fun (block,b) =>
    block.insts.toList.zipIdx.all fun (i,k) => instruction sig b k i

/-- The runtime check reads original source and actual Stock artifacts only. -/
def check (f : Clif.Function) (vc : VCode) : Bool :=
  match sourceData? f with
  | none => false
  | some data => sourceB f data && lowerScopeB f && dominatedB f && sigAbiOk f.sig &&
      match Stock.lower f with
      | .error _ => false
      | .ok result => decide (result.code = vc) && codeB data result &&
          result.blockScans.toList.all (scanB data result) && codeCheck f.sig vc &&
          result.edgeArgs.all (fun row => row.all (·.isEmpty))

end Backend.Stock.ResultCall
