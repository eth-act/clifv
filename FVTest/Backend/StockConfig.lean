import FV.Backend
import Lean.Data.Json

/-!
Explicit, fail-closed stock-filetest configuration adapter. This is an experimental
driver, NOT an extension of the existing end-to-end compiler theorem. The original
compiler and its proofs retain their fixed configuration. No machine bytes are masked
or rewritten by the comparison harness.

A stock setting the backend does not implement is accepted only where it cannot change the
code of the function being compiled. Each other function is rejected for that setting
(`configure`). Cranelift references are to wasmtime v49.0.1 (`cranelift/codegen/src`).
-/
namespace StockConfig
open Backend Lean

structure Config where
  request : Json
  pic : Bool
  preserveFramePointers : Bool
  unwind : Bool
  /-- `has_lse`: stock lowers `atomic_cas` and most `atomic_rmw` operations to LSE instructions. -/
  lse : Bool
  /-- `use_csdb`: stock adds `csdb` to `select_spectre_guard` and to the `br_table` sequence. -/
  csdb : Bool
  signReturnAddress : Bool
  signReturnAddressAll : Bool

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
  ("machine_code_cfg_info", "true"), ("enable_probestack", "false"),
  ("enable_heap_access_spectre_mitigation", "true"),
  ("enable_table_access_spectre_mitigation", "true"),
  ("enable_incremental_compilation_cache_checks", "false"),
  ("enable_compact_unwind_abi", "false")]

/-- Shared settings accepted with either value, because no function Lean compiles can observe
them:
* `enable_llvm_abi_extensions`: on AArch64 it only permits `f128` parameters of `apple_aarch64`
  signatures (`isa/aarch64/abi.rs:231`). Lean has no float types (`Clif.Ty`) and lowers only
  `system_v`/`fast` signatures (`Backend.aapcsConv`).
* `enable_multi_ret_implicit_sret`: it only matters when the returns of a signature do not fit
  in the return registers (`isa/aarch64/abi.rs:382`, `machinst/abi.rs:936`). Lean rejects each
  function, call and `try_call` with more than 8 returns (`Backend.retRegs`). -/
def inertFlags : List String := ["enable_llvm_abi_extensions", "enable_multi_ret_implicit_sret"]

def boolFlags : List String := ["is_pic", "preserve_frame_pointers", "unwind_info"]
def isaFlags : List String := ["has_lse", "has_pauth", "has_fp16", "has_dotprod",
  "has_i8mm", "sign_return_address_all", "sign_return_address",
  "sign_return_address_with_bkey", "use_bti", "use_csdb"]

/-- ISA settings rejected for the whole request when `true`: `use_bti` puts `bti c` at the
entry of each function that is not signed (`isa/aarch64/abi.rs:638`), and Lean does not emit it.
The other ISA settings are accepted:
* `has_fp16`, `has_dotprod`, `has_i8mm`: only float and vector lowering rules read them
  (`isa/aarch64/inst.isle:2892,2942,4222,4250`, `isa/aarch64/lower.isle:402,419`). Lean's CLIF
  subset has integer types only (`Clif.Ty`), so no function Lean compiles can observe them.
* `has_lse`, `use_csdb`, `sign_return_address`, `sign_return_address_all`,
  `sign_return_address_with_bkey`, `has_pauth`: per function, in `configure`. -/
def rejectedIsaFlags : List String := ["use_bti"]

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

def boolean (rows : List (String × String)) (name : String) : Except String Bool :=
  match rows.lookup name with
  | some "true" => pure true
  | some "false" => pure false
  | _ => throw s!"invalid boolean {name}"

def parse (j : Json) : Except String Config := do
  let schema ← j.getObjValAs? Nat "schema"
  if schema != 1 then throw "unsupported stock configuration schema"
  let target ← j.getObjValAs? String "target"
  if !(["aarch64", "aarch64-unknown-unknown", "aarch64-unknown-unknown-elf", "aarch64-unknown-linux-gnu"].contains target) then
    throw s!"unsupported target {target} (only AArch64 generic/Linux ABI is audited)"
  let shared ← flagRows j "flags"
  checkNames shared (fixedFlags.map (·.1) ++ inertFlags ++ boolFlags)
  for (name, expected) in fixedFlags do
    let actual := (shared.lookup name).getD ""
    if actual != expected then throw s!"unsupported setting {name}={actual}; implemented policy is {expected}"
  for name in inertFlags do
    discard <| boolean shared name
  let isa ← flagRows j "isa_flags"
  checkNames isa isaFlags
  for (name, value) in isa do
    if (← boolean isa name) && rejectedIsaFlags.contains name then
      throw s!"unsupported ISA setting {name}={value}"
  pure { request := j, pic := ← boolean shared "is_pic",
         preserveFramePointers := ← boolean shared "preserve_frame_pointers",
         unwind := ← boolean shared "unwind_info", lse := ← boolean isa "has_lse",
         csdb := ← boolean isa "use_csdb",
         signReturnAddress := ← boolean isa "sign_return_address",
         signReturnAddressAll := ← boolean isa "sign_return_address_all" }

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

/-- An `atomic_rmw` with an LSE form, or an `atomic_cas`: with `has_lse` stock lowers these to
LSE instructions, not to the LL/SC loops Lean emits (`isa/aarch64/lower.isle:2328-2388`).
`nand` and `xchg` have no LSE rule. -/
def usesLse (f : Clif.Function) : Bool :=
  f.blocks.any fun b => b.body.any fun s => match s.inst with
    | .atomicRmw op .. => op != .nand && op != .xchg
    | .atomicCas .. => true
    | _ => false

/-- `select_spectre_guard` or `br_table`: with `use_csdb` stock adds a `csdb` after the guard's
`csel` (`isa/aarch64/lower.isle:2274`), and to the jump-table sequence under the fixed
`enable_table_access_spectre_mitigation=true` (`isa/aarch64/inst/emit.rs:3276`). Lean does not
lower `select_spectre_guard` today; the check keeps the policy closed if it starts to. -/
def usesCsdb (f : Clif.Function) : Bool :=
  f.blocks.any fun b =>
    b.body.any (fun s => s.inst matches .selectSpectreGuard ..) || b.term matches .brTable ..

/-- The per-function part of the settings policy. `fs` is the function's CLIF before and after
`i128` legalisation. Each error is a setting rejection (`allocate` records it). -/
def configure (c : Config) (fs : List Clif.Function) (vc : VCode) (af : AFunc) :
    Except String AFunc := do
  if fs.isEmpty then throw s!"no CLIF function {vc.name} to check the settings against"
  if !c.pic && vc.blocks.any (fun b => b.insts.any (fun i => i matches .loadExtNameGot ..)) then
    throw "is_pic=false requires a non-PIC far-symbol lowering that Lean does not implement"
  if vc.hasTls then
    throw "tls_model=none cannot use Lean's fixed TLSDESC lowering"
  if c.lse && fs.any usesLse then
    throw "has_lse=true changes the lowering of this function's atomic_rmw/atomic_cas; Lean does not implement LSE atomics"
  if c.csdb && fs.any usesCsdb then
    throw "use_csdb=true adds csdb to this function's select_spectre_guard/br_table; Lean does not implement it"
  -- Incoming stack arguments require a frame even when allocation drops their
  -- unused loads. Consult pre-allocation VCode as well as the allocated body.
  let required := frameRequired af || vc.blocks.any (fun b => b.insts.any touchesFrame)
  let frame := c.preserveFramePointers || required
  -- Stock signs the return address if and only if the function sets up a frame or
  -- `sign_return_address_all` is set (`select_api_key`, `isa/aarch64/abi.rs:1365`). The key
  -- (`sign_return_address_with_bkey`) and `has_pauth` (`is_hint`, `isa/aarch64/abi.rs:736`)
  -- only change that signing. The other uses need instructions Lean rejects: `return_call`
  -- (`isa/aarch64/lower/isle.rs:129-162`, `isa/aarch64/inst/emit.rs:3775`) and
  -- `get_return_address` (`isa/aarch64/inst.isle:4577`).
  if c.signReturnAddress && (frame || c.signReturnAddressAll) then
    throw "sign_return_address=true signs this function's return address; Lean does not implement pointer authentication"
  pure { af with frame }

/-- The start of the `unsupported` reason of a function that `configure` rejects. -/
def rejectionPrefix : String := "stock configuration unsupported for this function: "

/-- Allocate, then apply `configure`. `clif name` is the CLIF of function `name`. Each rejection
is recorded in `rejected` as (name, reason), for the receipt. -/
def allocate (c : Config) (clif : String → List Clif.Function)
    (rejected : IO.Ref (Array (String × String))) (a : Allocator) (vcs : Array VCode) :
    IO (Array (Except String AFunc)) := do
  let results ← a.run vcs
  (vcs.zip results).mapM fun (vc, result) => do
    match result with
    | .error e => pure (.error e)
    | .ok af =>
      match configure c (clif vc.name) vc af with
      | .ok af => pure (.ok af)
      | .error why =>
        rejected.modify (·.push (vc.name, why))
        pure (.error (rejectionPrefix ++ why))

/-- The configuration receipt. `functionRejections` is written after compilation: the
functions that `configure` rejected, by name, with the reason. -/
def receipt (request : Json) (error : Option String)
    (functionRejections : Option (List (String × String)) := none) : Json :=
  Json.mkObj ([("schema", toJson (1 : Nat)), ("request", request),
    ("configuration_accepted", toJson error.isNone), ("error", toJson error),
    ("proof_scope", toJson "experimental stock-configured driver; not covered by backend_correct"),
    ("policy", toJson "exact requested flags; a setting Lean does not implement is accepted only for functions whose code it cannot change (enable_llvm_abi_extensions, enable_multi_ret_implicit_sret, has_fp16, has_dotprod, has_i8mm: all functions; has_lse: no LSE atomic; use_csdb: no select_spectre_guard or br_table; sign_return_address, sign_return_address_with_bkey, has_pauth: unsigned functions); use_bti and other unsupported settings rejected for the whole request; is_pic=false far symbols and tls_model=none TLS rejected per function; per-function rejections listed in function_rejections; optional leaf frame omitted before emission; no binary normalization")] ++
    match functionRejections with
    | some rs => [("function_rejections", Json.mkObj (rs.map fun (n, why) => (n, toJson why)))]
    | none => [])

end StockConfig
