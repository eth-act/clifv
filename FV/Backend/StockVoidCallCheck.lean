import FV.Backend.StockArithmeticCheck
import FV.Backend.Proof.StockReturnABI
import FV.Backend.Proof.IselCtlTerm

namespace Backend.Stock.VoidCall
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false

/-- Read a source register through the actual context map, never its numeric source identifier. -/
def sourceKey (ctx : Ctx) (x : Nat) : Nat :=
  match ctx.valueReg? x with
  | some (.vreg key .int) => key
  | _ => 0

local instance : DecidableEq (Except String (List Nat)) := fun a b =>
  match a,b with
  | .ok x,.ok y => if h : x = y then isTrue (congrArg Except.ok h)
      else isFalse (fun eq => h (Except.ok.inj eq))
  | .error x,.error y => if h : x = y then isTrue (congrArg Except.error h)
      else isFalse (fun eq => h (Except.error.inj eq))
  | .ok _,.error _ => isFalse (by intro eq; cases eq)
  | .error _,.ok _ => isFalse (by intro eq; cases eq)

structure SourceData where
  block : Clif.Block
  fn : Clif.FnRef
  args : List Nat
  ext : Clif.ExtFunc
  bytes : List Nat

def sourceData? (f : Clif.Function) : Option SourceData :=
  match f.blocks with
  | [block] => match block.body with
    | [⟨[],.call fn args⟩] => do
      let ext ← f.extern? fn
      let bytes ← (sigParamBytes ext.sig).toOption
      pure ⟨block,fn,args,ext,bytes⟩
    | _ => none
  | _ => none

/-- Check the original source and ABI. No execution certificate is an input. -/
def sourceB (f : Clif.Function) (data : SourceData) : Bool :=
  decide (f.blocks = [data.block]) && decide (data.block.body = [⟨[],.call data.fn data.args⟩]) &&
  decide (data.block.term = .ret []) && decide (f.sig.returns = []) &&
  decide (data.ext.sig.returns = []) && decide (f.extern? data.fn = some data.ext) &&
  decide (sigParamBytes data.ext.sig = .ok data.bytes) && decide (data.bytes.length ≤ 8) &&
  decide (returnPins f 0 = some [])

def callUses (uses : List (Reg × Reg)) : List (Nat × Reg) :=
  uses.map fun pair => ((match pair.1 with | .vreg key .int => key | _ => 0),pair.2)

/-- Check actual retained call metadata against original source argument mappings. -/
def scanB (data : SourceData) (event : Stock.BlockScanEvent) : Bool :=
  if event.block == 0 then
    match event.output.code.toList with
    | [.call info,.rets []] =>
      decide (info.dest = .sym data.ext.name) && info.defs.isEmpty &&
        decide (info.uses = retPairs (callUses info.uses)) &&
        decide ((callUses info.uses).map (·.1) = data.args.map (sourceKey event.ctx))
    | _ => false
  else true

def codeB (data : SourceData) (result : Stock.Result) : Bool := result.blockScans.toList.all (scanB data)


/-- Bind the source and record checks to the actual unchanged Stock output. -/
def check (f : Clif.Function) (vc : VCode) : Bool :=
  match sourceData? f with
  | none => false
  | some data => sourceB f data && lowerScopeB f && dominatedB f && sigAbiOk f.sig &&
      match Stock.lower f with
      | .error _ => false
      | .ok result => decide (result.code = vc) && codeB data result &&
          result.edgeArgs.all (fun row => row.all (·.isEmpty))

end Backend.Stock.VoidCall
