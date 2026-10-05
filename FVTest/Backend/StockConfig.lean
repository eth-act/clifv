import FV.Backend
import Lean.Data.Json

/-!
Explicit, fail-closed stock-filetest configuration adapter. This is an experimental
driver, NOT an extension of the existing end-to-end compiler theorem. The original
compiler and its proofs retain their fixed configuration. No machine bytes are masked
or rewritten by the comparison harness.
-/
namespace StockConfig
open Backend Lean

structure Config where
  request : Json
  pic : Bool
  preserveFramePointers : Bool
  unwind : Bool

-- At opt_level=none the stock egraph/alias-analysis pass is not run. Spectre policy
-- settings apply to explicit guard instructions, which the existing lowerer either
-- implements or rejects; they do not invent additional heap/table inputs.
def fixedFlags : List (String × String) := [
  ("regalloc_algorithm", "backtracking"), ("opt_level", "none"),
  ("tls_model", "none"), ("stack_switch_model", "none"),
  ("libcall_call_conv", "isa_default"), ("probestack_size_log2", "12"),
  ("probestack_strategy", "outline"), ("bb_padding_log2_minus_one", "0"),
  ("log2_min_function_alignment", "0"), ("regalloc_checker", "false"),
  ("regalloc_verbose_logs", "false"), ("enable_alias_analysis", "true"),
  ("enable_verifier", "true"), ("use_colocated_libcalls", "false"),
  ("enable_nan_canonicalization", "false"), ("enable_pinned_reg", "false"),
  ("enable_llvm_abi_extensions", "false"), ("enable_multi_ret_implicit_sret", "false"),
  ("machine_code_cfg_info", "true"), ("enable_probestack", "false"),
  ("enable_heap_access_spectre_mitigation", "true"),
  ("enable_table_access_spectre_mitigation", "true"),
  ("enable_incremental_compilation_cache_checks", "false"),
  ("enable_compact_unwind_abi", "false")]

def boolFlags : List String := ["is_pic", "preserve_frame_pointers", "unwind_info"]
def isaFlags : List String := ["has_lse", "has_pauth", "has_fp16", "has_dotprod",
  "has_i8mm", "sign_return_address_all", "sign_return_address",
  "sign_return_address_with_bkey", "use_bti", "use_csdb"]

def flagRows (j : Json) (key : String) : Except String (List (String × String)) := do
  let rows ← (← j.getObjVal? key).getArr?
  let values ← rows.toList.mapM fun row => do
    pure (← row.getObjValAs? String "name", ← row.getObjValAs? String "value")
  if (values.map (·.1)).eraseDups.length != values.length then
    throw s!"duplicate {key}"
  pure values

def checkNames (rows : List (String × String)) (names : List String) : Except String Unit := do
  for (name, _) in rows do
    if !names.contains name then throw s!"unknown setting {name}"
  for name in names do
    if (rows.lookup name).isNone then throw s!"missing setting {name}"

def parse (j : Json) : Except String Config := do
  let schema ← j.getObjValAs? Nat "schema"
  if schema != 1 then throw "unsupported stock configuration schema"
  let target ← j.getObjValAs? String "target"
  if !(["aarch64", "aarch64-unknown-unknown", "aarch64-unknown-unknown-elf", "aarch64-unknown-linux-gnu"].contains target) then
    throw s!"unsupported target {target} (only AArch64 generic/Linux ABI is audited)"
  let shared ← flagRows j "flags"
  checkNames shared (fixedFlags.map (·.1) ++ boolFlags)
  for (name, expected) in fixedFlags do
    let actual := (shared.lookup name).getD ""
    if actual != expected then throw s!"unsupported setting {name}={actual}; implemented policy is {expected}"
  let isa ← flagRows j "isa_flags"
  checkNames isa isaFlags
  for (name, value) in isa do
    if value != "false" then throw s!"unsupported ISA setting {name}={value}"
  let boolean (name : String) : Except String Bool := do
    match shared.lookup name with
    | some "true" => pure true
    | some "false" => pure false
    | _ => throw s!"invalid boolean {name}"
  let pic ← boolean "is_pic"
  let preserveFramePointers ← boolean "preserve_frame_pointers"
  let unwind ← boolean "unwind_info"
  pure { request := j, pic, preserveFramePointers, unwind }

def touchesFrame (m : MInst) : Bool :=
  (m.uses ++ m.defs).any (fun r => r == .x 29 || r == .x 30) ||
  match m with
  | .call .. | .tryCall .. | .elfTlsGetAddr .. => true
  | .load _ _ (.fpOffset _) _ | .store _ _ (.fpOffset _) _ | .loadAddr _ (.fpOffset _)
  | .load _ _ (.incomingArg _) _ | .store _ _ (.incomingArg _) _
  | .loadAddr _ (.incomingArg _) => true
  | _ => false

def frameRequired (af : AFunc) : Bool :=
  af.frameSize != 0 || af.slotBase != 0 || af.blocks.any fun (_, code) =>
    code.any fun | .inst m => touchesFrame m | _ => false

def configure (c : Config) (vc : VCode) (af : AFunc) : Except String AFunc := do
  if !c.pic && vc.blocks.any (fun b => b.insts.any (fun i => i matches .loadExtNameGot ..)) then
    throw "stock configuration unsupported for this function: is_pic=false requires a non-PIC far-symbol lowering that Lean does not implement"
  if vc.hasTls then
    throw "stock configuration unsupported for this function: tls_model=none cannot use Lean's fixed TLSDESC lowering"
  -- Incoming stack arguments require a frame even when allocation drops their
  -- unused loads. Consult pre-allocation VCode as well as the allocated body.
  let required := frameRequired af || vc.blocks.any (fun b => b.insts.any touchesFrame)
  pure { af with frame := c.preserveFramePointers || required }

def allocate (c : Config) (a : Allocator) (vcs : Array VCode) : IO (Array (Except String AFunc)) := do
  let results ← a.run vcs
  pure ((vcs.zip results).map fun (vc, result) => result.bind (configure c vc))

def receipt (request : Json) (error : Option String) : Json :=
  Json.mkObj [("schema", toJson (1 : Nat)), ("request", request),
    ("configuration_accepted", toJson error.isNone), ("error", toJson error),
    ("proof_scope", toJson "experimental stock-configured driver; not covered by backend_correct"),
    ("policy", toJson "exact requested flags; unsupported flags rejected; PIC=false far symbols and tls_model=none TLS rejected per function; optional leaf frame omitted before emission; no binary normalization")]

end StockConfig
