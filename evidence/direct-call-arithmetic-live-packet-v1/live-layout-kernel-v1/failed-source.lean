import FV.Backend.StockResultCallCheck

namespace Backend.Stock.LiveCall
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false

structure SourceData where
  block : Clif.Block
  fn : Clif.FnRef
  ext : Clif.ExtFunc
  live : Nat
  called : Nat
  sum : Nat
  returned : Clif.AbiParam

def sourceData? (f : Clif.Function) : Option SourceData := do
  let [block] := f.blocks | none
  let [(live,.i64)] := block.params | none
  let [⟨[called],.call fn [argument]⟩,⟨[sum],.binary .iadd .i64 left right⟩] := block.body | none
  if argument != live || left != called || right != live then none else do
    let ext ← f.extern? fn
    let [returned] := ext.sig.returns | none
    pure ⟨block,fn,ext,live,called,sum,returned⟩

def sourceB (f : Clif.Function) (data : SourceData) : Bool :=
  decide (f.blocks = [data.block]) && decide (data.block.params = [(data.live,.i64)]) &&
  decide (data.block.body = [⟨[data.called],.call data.fn [data.live]⟩,
    ⟨[data.sum],.binary .iadd .i64 data.called data.live⟩]) &&
  decide (data.block.term = .ret [data.sum]) && decide (f.sig.params.map (·.ty) = [.i64]) &&
  decide (f.sig.returns.map (·.ty) = [.i64]) && decide (data.ext.sig.params.map (·.ty) = [.i64]) &&
  decide (data.ext.sig.returns = [data.returned]) && decide (data.returned.ty = .i64) &&
  decide (f.extern? data.fn = some data.ext) && decide (returnPins f 1 = some [.x 0]) &&
  decide (data.live ≠ data.called) && decide (data.sum ≠ data.called) && decide (data.sum ≠ data.live)

structure ScanData where
  live : Nat
  calledRoot : Nat
  calledDestination : Nat
  sumRoot : Nat
  sumDestination : Nat

def scanData? (data : SourceData) (event : Stock.BlockScanEvent) : Option ScanData := do
  let some (.vreg live .int) := event.ctx.valueReg? data.live | none
  let some (.vreg calledRoot .int) := event.ctx.valueReg? data.called | none
  let some (.vreg sumRoot .int) := event.ctx.valueReg? data.sum | none
  let [.call info,.aluRRR .add .size64 (.vreg sumDestination .int) _ _,.rets _] :=
    event.output.code.toList | none
  let [(.x 0,.vreg calledDestination .int)] := info.defs | none
  pure ⟨live,calledRoot,calledDestination,sumRoot,sumDestination⟩

def scanFactsB (data : SourceData) (result : Stock.Result) (event : Stock.BlockScanEvent)
    (scan : ScanData) : Bool :=
  decide (event.ctx.valueReg? data.live = some (.vreg scan.live .int)) &&
  decide (event.ctx.valueReg? data.called = some (.vreg scan.calledRoot .int)) &&
  decide (event.ctx.valueReg? data.sum = some (.vreg scan.sumRoot .int)) &&
  decide (event.output.code = #[
    .call ⟨.sym data.ext.name,retPairs [(scan.live,.x 0)],callDefs [(.x 0,scan.calledDestination)]⟩,
    .aluRRR .add .size64 (.vreg scan.sumDestination .int) (.vreg scan.calledRoot .int) (.vreg scan.live .int),
    .rets (retPairs [(scan.sumRoot,.x 0)])]) &&
  decide (aliasNum result.final.alias scan.calledRoot = aliasNum result.final.alias scan.calledDestination) &&
  decide (aliasNum result.final.alias scan.sumRoot = aliasNum result.final.alias scan.sumDestination) &&
  decide (aliasNum result.final.alias scan.live ≠ aliasNum result.final.alias scan.calledDestination)

def scanB (data : SourceData) (result : Stock.Result) (event : Stock.BlockScanEvent) : Bool :=
  if event.block == 0 then
    (scanData? data event).any (scanFactsB data result event)
  else true

def instruction (sig : Clif.Signature) (block pc : Nat) (inst : MInst) : Bool :=
  match inst with
  | .call _ | .aluRRR .add .size64 _ _ _ => true
  | _ => Backend.ABIReadOnly.instruction sig block pc inst

def codeCheck (sig : Clif.Signature) (vc : VCode) : Bool :=
  vc.blocks.toList.zipIdx.all fun (block,b) =>
    block.insts.toList.zipIdx.all fun (inst,pc) => instruction sig b pc inst

def check (f : Clif.Function) (vc : VCode) : Bool :=
  match sourceData? f with
  | none => false
  | some data => sourceB f data && lowerScopeB f && dominatedB f && sigAbiOk f.sig &&
    match Stock.lower f with
    | .error _ => false
    | .ok result => decide (result.code = vc) &&
      result.blockScans.toList.all (scanB data result) && codeCheck f.sig vc &&
      result.edgeArgs.all (fun row => row.all (·.isEmpty))

end Backend.Stock.LiveCall
