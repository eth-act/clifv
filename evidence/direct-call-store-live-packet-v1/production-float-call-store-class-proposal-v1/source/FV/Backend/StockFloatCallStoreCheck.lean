import FV.Backend.StockLiveCallCheck

namespace Backend.Stock.FloatCallStore
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false

structure SourceData where
  block : Clif.Block
  fn : Clif.FnRef
  ext : Clif.ExtFunc
  pointer : Nat
  argument : Nat
  called : Nat
  flags : Clif.MemFlags
  returned : Clif.AbiParam

def sourceData? (f : Clif.Function) : Option SourceData := do
  let [block] := f.blocks | none
  let [(pointer,.i64),(argument,.f64)] := block.params | none
  let [⟨[called],.call fn [actualArgument]⟩,⟨[],.store .store .f64 flags value actualPointer 8⟩] := block.body | none
  if actualArgument != argument || value != called || actualPointer != pointer then none else do
    let ext ← f.extern? fn
    let [returned] := ext.sig.returns | none
    pure ⟨block,fn,ext,pointer,argument,called,flags,returned⟩

def sourceB (f : Clif.Function) (data : SourceData) : Bool :=
  decide (f.blocks = [data.block]) &&
  decide (data.block.params = [(data.pointer,.i64),(data.argument,.f64)]) &&
  decide (data.block.body = [⟨[data.called],.call data.fn [data.argument]⟩,
    ⟨[],.store .store .f64 data.flags data.called data.pointer 8⟩]) &&
  decide (data.block.term = .ret [data.called]) &&
  decide (f.sig.params.map (·.ty) = [.i64,.f64]) && decide (f.sig.returns.map (·.ty) = [.f64]) &&
  decide (data.ext.sig.params.map (·.ty) = [.f64]) &&
  decide (data.ext.sig.returns = [data.returned]) && decide (data.returned.ty = .f64) &&
  decide (f.extern? data.fn = some data.ext) && decide (returnPins f 1 = some [.v 0]) &&
  decide (data.pointer ≠ data.called) && decide (data.argument ≠ data.called) &&
  decide (data.pointer ≠ data.argument) && decide (data.flags = {}) &&
  decide ((sigParamBytes data.ext.sig).toOption = some [8])

structure ScanData where
  pointer : Nat
  argument : Nat
  calledRoot : Nat
  calledDestination : Nat

def scanData? (data : SourceData) (event : Stock.BlockScanEvent) : Option ScanData := do
  let some (.vreg pointer .int) := event.ctx.valueReg? data.pointer | none
  let some (.vreg argument .float) := event.ctx.valueReg? data.argument | none
  let some (.vreg calledRoot .float) := event.ctx.valueReg? data.called | none
  let [.call info,.fpuStore .size64 _ _ _,.rets _] := event.output.code.toList | none
  let [(.v 0,.vreg calledDestination .float)] := info.defs | none
  pure ⟨pointer,argument,calledRoot,calledDestination⟩

def scanFactsB (data : SourceData) (result : Stock.Result) (event : Stock.BlockScanEvent)
    (scan : ScanData) : Bool :=
  decide (event.ctx.valueReg? data.pointer = some (.vreg scan.pointer .int)) &&
  decide (event.ctx.valueReg? data.argument = some (.vreg scan.argument .float)) &&
  decide (event.ctx.valueReg? data.called = some (.vreg scan.calledRoot .float)) &&
  decide (event.output.code = #[
    .call ⟨.sym data.ext.name,[(.vreg scan.argument .float,.v 0)],[(.v 0,.vreg scan.calledDestination .float)]⟩,
    .fpuStore .size64 (.vreg scan.calledRoot .float) (.unsignedOffset (.vreg scan.pointer .int) 8) data.flags,
    .rets [(.vreg scan.calledRoot .float,.v 0)]]) &&
  decide (aliasNum result.final.alias scan.calledRoot = aliasNum result.final.alias scan.calledDestination) &&
  decide (aliasNum result.final.alias scan.pointer ≠ aliasNum result.final.alias scan.calledDestination)

def scanB (data : SourceData) (result : Stock.Result) (event : Stock.BlockScanEvent) : Bool :=
  if event.block == 0 then (scanData? data event).any (scanFactsB data result event) else true

def instruction (sig : Clif.Signature) (block pc : Nat) (inst : MInst) : Bool :=
  match inst with
  | .call _ => true
  | .fpuStore .size64 (.vreg _ .float) (.unsignedOffset (.vreg _ .int) 8) flags => decide (flags = {})
  | _ => Backend.ABIReadOnly.instruction sig block pc inst

def codeCheck (sig : Clif.Signature) (vc : VCode) : Bool :=
  vc.blocks.toList.zipIdx.all fun (block,b) =>
    LiveCall.prefixReads sig b 0 block.insts.toList &&
      block.insts.toList.zipIdx.all (fun (inst,pc) => instruction sig b pc inst)

/-- Admission reads source and compiler artifacts only; it never asks for a heap or call outcome. -/
def check (f : Clif.Function) (vc : VCode) : Bool :=
  match sourceData? f with
  | none => false
  | some data => sourceB f data && lowerScopeB f && dominatedB f && sigAbiOk f.sig &&
    match Stock.lower f with
    | .error _ => false
    | .ok result => decide (result.code = vc) && result.blockScans.toList.all (scanB data result) &&
      codeCheck f.sig vc && result.edgeArgs.all (fun row => row.all (·.isEmpty))

end Backend.Stock.FloatCallStore
