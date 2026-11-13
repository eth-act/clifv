import FV.Backend
import FV.Backend.RegallocPerEdgeDriver
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
  | .loadAddr _ (.incomingArg _) | .fpuLoad _ _ (.fpOffset _) _ | .fpuStore _ _ (.fpOffset _) _
  | .fpuLoad _ _ (.incomingArg _) _ | .fpuStore _ _ (.incomingArg _) _ => true
  | _ => false

/-- Incoming stack-argument loads from `sp`, as stock addresses them (`AMode::IncomingArg`;
`mem_finalize` in `isa/aarch64/inst/emit.rs`: `sp` plus the setup, clobber, fixed-frame and
outgoing areas). The lowering loads an incoming stack argument from `fp + 16 + off`
(`fpOffset`). In the body of a function with a frame, `fp = sp + frameSize` (`prologueLines`;
the body keeps `sp`), so `fpOffset o` addresses `sp + frameSize + o`. Stock's other
`FPOffset` (`get_return_address`, offset 8) stays. -/
def argLoadsFromSp (af : AFunc) : AFunc :=
  let fromSp : AMode → AMode
    | .fpOffset o => if o ≥ 16 then .spOffset (af.frameSize + o) else .fpOffset o
    | m => m
  { af with blocks := af.blocks.map fun (l, code) => (l, code.map fun
      | .inst (.load op r m fl) => .inst (.load op r (fromSp m) fl)
      | .inst (.fpuLoad sz r m fl) => .inst (.fpuLoad sz r (fromSp m) fl)
      | a => a) }

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

/-- The per-function checks of the settings policy, shared by `configure` (stock-configured
driver) and `admit` (proved settings mode). `fs` is the function's CLIF before and after `i128`
legalisation. Each error is a setting rejection. The result is stock's frame decision: whether
stock sets up a frame for this function (`preserve_frame_pointers`, or a frame the function
needs). It changes no code. -/
def checkFunction (c : Config) (fs : List Clif.Function) (vc : VCode) (af : AFunc) :
    Except String Bool := do
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
  pure frame

/-- The per-function part of the settings policy of the stock-configured driver:
`checkFunction`, then the frame as stock decides it, and stack-argument loads from `sp` (both
unproved). -/
def configure (c : Config) (fs : List Clif.Function) (vc : VCode) (af : AFunc) :
    Except String AFunc := do
  let frame ← checkFunction c fs vc af
  pure (if frame then argLoadsFromSp { af with frame } else { af with frame })

/-- The start of the `unsupported` reason of a function that `configure` rejects. -/
def rejectionPrefix : String := "stock configuration unsupported for this function: "

/-- **Proved settings mode** (`lean-backend --settings`): the per-function admission. The
function is compiled by the proved compiler unchanged (`af` is returned as allocated: no
`configure`, no `argLoadsFromSp`, no `dropDeadNotrapLoads`, no native `i128`). Its output is
claimed for the settings only where the proved compiler implements the settings for it: `checkFunction` passes, and the
compiled function has a frame exactly when stock sets one up (the proved compiler always sets
one up today, so a frameless leaf under `preserve_frame_pointers=false` is rejected). -/
def admit (c : Config) (fs : List Clif.Function) (vc : VCode) (af : AFunc) :
    Except String AFunc := do
  let frame ← checkFunction c fs vc af
  if frame != af.frame then
    throw (if frame then "stock sets up a frame for this function; the compiled function has none"
      else "preserve_frame_pointers=false: stock omits this function's frame; the proved compiler sets one up")
  pure af

/-- `admit` on each allocation of `run`, which it returns unchanged. Each rejection is recorded
in `rejected` as (name, reason): the function stays compiled, so that its callers in the file
are compiled as without the option (their code does not depend on the callee's frame), and its
own output is not claimed for these settings (the receipt's `setting_rejection`). -/
def admitWith (c : Config) (clif : String → List Clif.Function)
    (rejected : IO.Ref (Array (String × String)))
    (run : Array VCode → IO (Array (Except String AFunc))) (vcs : Array VCode) :
    IO (Array (Except String AFunc)) := do
  let results ← run vcs
  for (vc, result) in vcs.zip results do
    if let .ok af := result then
      if let .error why := admit c (clif vc.name) vc af then
        rejected.modify (·.push (vc.name, why))
  pure results

/-! ## Unused `notrap` loads (#970)

Stock does not lower a `load` whose flags are `notrap` when none of its results is used
(`must_lower_even_if_unused`, `inst_predicates.rs:113`, wasmtime v49.0.1; the filetest
`isa/aarch64/dead-notrap-load.clif`). Lean's lowering emits it, and neither cleanup stage drops it
(`Proof.Driver.skippable` and `DeadCleanup.pureForm` exclude loads). `dropDeadNotrapLoads` drops
such loads in this stock-configured driver only. It is NOT proved: like `argLoadsFromSp`, it is
outside `backend_correct`, and every function of this mode is reported unverified. The default
mode and `cargo fv` do not run it: cg_clif's Cranelift 0.136.1, the reference of `cargo fv`, keeps
these loads (#970, #588).

The CLIF justification is `Clif.evalInst_notrap_load` (`FV/Clif/NotrapLoad.lean`): a `notrap` load
reads without changing the memory, or it is stuck; it never traps. So a source run either continues
past the load with the same memory (its value is unused) or is stuck, which the backend theorems
do not constrain (`E2E.ArmRefines`). A load that can trap is never dropped. -/

/-- The loads `dropDeadNotrapLoads` may drop: an integer, float or `i128`-pair load whose flags are
`notrap` (so not a trapping load), whose defs and register uses are all virtual, and whose address
mode has no writeback (`sp` pre/post-index) and is not an ABI access (`fpOffset`/`incomingArg`: the
incoming stack arguments, `Backend.stackArgLoad`; `spOffset`). Atomic loads (`ldar`,
`MInst.loadAcquire`) are other instructions and are never dropped. -/
def notrapLoad (m : MInst) : Bool :=
  m.defs.all Reg.isVirtual && m.uses.all Reg.isVirtual && match m with
    | .load _ _ am fl | .fpuLoad _ _ am fl => fl.notrap && plain am
    | .loadP64 _ _ _ _ fl => fl.notrap
    | _ => false
where plain : AMode → Bool
  | .spPostIndexed _ | .spPreIndexed _ | .fpOffset _ | .incomingArg _ | .spOffset _ => false
  | _ => true

/-- `DeadCleanup.discard`, and a `notrapLoad` with no clobbers whose defs are all dead. -/
def dropDiscard (m : MInst) (live : List Nat) : Bool :=
  DeadCleanup.discard m live ||
    (notrapLoad m && m.clobbers.isEmpty && !(DeadCleanup.defs m).isEmpty &&
      (DeadCleanup.defs m).all (fun n => !live.contains n))

/-- `DeadCleanup.scan` with `dropDiscard`: backwards; a dropped instruction's inputs do not
become live. -/
def dropScan (nregs : Nat) : List MInst → List Nat → List MInst × List Nat
  | [], live => ([], live)
  | m :: ms, exit =>
    let (kept, live) := dropScan nregs ms exit
    if dropDiscard m live then (kept, live)
    else (m :: kept, DeadCleanup.uses nregs m ++
      live.filter (fun n => !(DeadCleanup.defs m).contains n))

/-- One pass over every block (`DeadCleanup.clean` with `dropScan`). -/
def dropPass (vc : VCode) : VCode :=
  { vc with blocks := vc.blocks.mapIdx fun i b =>
      { b with insts :=
          (dropScan vc.classes.size b.insts.toList (DeadCleanup.exitLive vc i b)).1.toArray } }

def instCount (vc : VCode) : Nat := vc.blocks.foldl (fun n b => n + b.insts.size) 0

def notrapLoadCount (vc : VCode) : Nat :=
  vc.blocks.foldl (fun n b => n + (b.insts.filter notrapLoad).size) 0

/-- **Drop the unused `notrap` loads** (unproved, stock-configured driver only; see above).
`dropPass` until nothing changes: `DeadCleanup.exitLive` counts the reads of a dropped load, so a
chain of loads, and the producers of a dropped load's address, go one per pass. The result is used
only if it drops a `notrapLoad`; otherwise (and for an invalid CFG) `vc` is unchanged. -/
def dropDeadNotrapLoads (vc : VCode) : VCode :=
  if notrapLoadCount vc == 0 then vc else
  match vc.cfg with
  | .error _ => vc
  | .ok _ =>
    let out := go (instCount vc + 1) vc
    if notrapLoadCount out < notrapLoadCount vc then out else vc
where go : Nat → VCode → VCode
  | 0, vc => vc
  | n + 1, vc =>
    let vc' := dropPass vc
    if instCount vc' == instCount vc then vc else go n vc'

/-- Drop the unused `notrap` loads (`dropDeadNotrapLoads`, unproved), allocate, then apply
`configure`, which decides the frame from the VCode before the drop. `clif name` is the CLIF of
function `name`. Each rejection is recorded in `rejected` as (name, reason), for the receipt. -/
def allocateWith (c : Config) (clif : String → List Clif.Function)
    (rejected : IO.Ref (Array (String × String)))
    (run : Array VCode → IO (Array (Except String AFunc))) (vcs : Array VCode) :
    IO (Array (Except String AFunc)) := do
  let results ← run (vcs.map dropDeadNotrapLoads)
  (vcs.zip results).mapM fun (vc, result) => do
    match result with
    | .error e => pure (.error e)
    | .ok af =>
      match configure c (clif vc.name) vc af with
      | .ok af => pure (.ok af)
      | .error why =>
        rejected.modify (·.push (vc.name, why))
        pure (.error (rejectionPrefix ++ why))

/-- Retain the original allocator entry point for existing comparison consumers. -/
def allocate (c : Config) (clif : String → List Clif.Function)
    (rejected : IO.Ref (Array (String × String))) (a : Allocator) (vcs : Array VCode) :
    IO (Array (Except String AFunc)) :=
  allocateWith c clif rejected a.run vcs

/-- Allocate Stock code together with its actual per-successor vectors. -/
def allocateAt (c : Config) (clif : String → List Clif.Function)
    (rejected : IO.Ref (Array (String × String))) (a : Allocator) (vcs : Array EdgeVCode) :
    IO (Array (Except String AFunc)) := do
  let results ← a.runAt vcs
  (vcs.zip results).mapM fun (vc, result) => do
    match result with
    | .error e => pure (.error e)
    | .ok af =>
      match configure c (clif vc.code.name) vc.code af with
      | .ok af => pure (.ok af)
      | .error why =>
        rejected.modify (·.push (vc.code.name, why))
        pure (.error (rejectionPrefix ++ why))

/-- The configuration receipt. `functionRejections` is written after compilation: the
functions that `configure` rejected, by name, with the reason. -/
def receipt (request : Json) (error : Option String)
    (functionRejections : Option (List (String × String)) := none)
    (deadCleanup : Bool := false) : Json :=
  Json.mkObj ([("schema", toJson (1 : Nat)), ("request", request),
    ("dead_instruction_cleanup", toJson deadCleanup),
    ("configuration_accepted", toJson error.isNone), ("error", toJson error),
    ("proof_scope", toJson "experimental stock-configured driver; not covered by backend_correct"),
    ("policy", toJson "exact requested flags; a setting Lean does not implement is accepted only for functions whose code it cannot change (enable_llvm_abi_extensions, enable_multi_ret_implicit_sret, has_fp16, has_dotprod, has_i8mm: all functions; has_lse: no LSE atomic; use_csdb: no select_spectre_guard or br_table; sign_return_address, sign_return_address_with_bkey, has_pauth: unsigned functions); use_bti and other unsupported settings rejected for the whole request; is_pic=false far symbols and tls_model=none TLS rejected per function; per-function rejections listed in function_rejections; optional leaf frame omitted before emission; no binary normalization")] ++
    match functionRejections with
    | some rs => [("function_rejections", Json.mkObj (rs.map fun (n, why) => (n, toJson why)))]
    | none => [])

/-- The receipt of the proved settings mode (`lean-backend --settings`). `functions` gives, per
function of the file, whether it was compiled, why not (`setting_rejection`: `admit`;
`unsupported`), and whether `backend_correct` covers it (`unverified`, `unvalidated`: why not). -/
def settingsReceipt (request : Json) (error : Option String)
    (functions : List (String × Json)) (deadCleanup : Bool) : Json :=
  Json.mkObj [("schema", toJson (1 : Nat)), ("request", request),
    ("mode", toJson "proved"), ("dead_instruction_cleanup", toJson deadCleanup),
    ("configuration_accepted", toJson error.isNone), ("error", toJson error),
    ("proof_scope", toJson "the proved compiler, unchanged: per function, backend_correct covers it iff backend_correct is true"),
    ("policy", toJson "exact requested flags, as --stock-config; a function is compiled only where the proved compiler implements the settings for it (StockConfig.admit: the checks of configure, and a frame exactly where stock sets one up); no configure, argLoadsFromSp, dropDeadNotrapLoads or native i128 lowering; no binary normalization"),
    ("functions", Json.mkObj functions)]

end StockConfig
