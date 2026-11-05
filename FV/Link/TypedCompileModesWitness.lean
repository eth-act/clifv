import FV.Link.TypedCompileSourceModes
import FV.E2E.ProductionBoundaryWitness
import FV.Backend.Lowering.StockVoidCallNI
namespace Link.TypedCompilerModesWitness
open Backend E2E E2E.LinkCheck E2E.Elf E2E.BinCheck
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace Raw
def fn0 : FnInput where
  clif := "set regalloc_algorithm=backtracking\nset opt_level=none\nset tls_model=elf_gd\nset stack_switch_model=none\nset libcall_call_conv=isa_default\nset probestack_size_log2=12\nset probestack_strategy=inline\nset bb_padding_log2_minus_one=0\nset log2_min_function_alignment=0\nset regalloc_checker=0\nset regalloc_verbose_logs=0\nset enable_alias_analysis=1\nset enable_verifier=0\nset is_pic=1\nset use_colocated_libcalls=0\nset enable_nan_canonicalization=0\nset enable_pinned_reg=0\nset enable_llvm_abi_extensions=1\nset enable_multi_ret_implicit_sret=0\nset unwind_info=1\nset preserve_frame_pointers=1\nset machine_code_cfg_info=0\nset enable_probestack=1\nset enable_heap_access_spectre_mitigation=1\nset enable_table_access_spectre_mitigation=1\nset enable_incremental_compilation_cache_checks=0\nset enable_compact_unwind_abi=0\ntarget aarch64 has_lse=0 has_pauth=0 has_fp16=0 has_dotprod=0 has_i8mm=0 sign_return_address_all=0 sign_return_address=0 sign_return_address_with_bkey=0 use_bti=0 use_csdb=0\n\nfunction %_RNxC7fv_demo11HawPMC3YC2b(i64 sret, i64) system_v {\nblock0(v0: i64, v1: i64):\n    nop\n    jump block1\n\nblock1:\n    nop\n    v2 = load.i64 notrap v1\n    v3 = load.i64 notrap v1+8\n    store.i64 notrap v2, v0\n    store.i64 notrap v3, v0+8\n    jump block2\n\nblock2:\n    nop\n    return\n}\n"
  ra := "{\"functions\": [{\"name\": \"_RNxC7fv_demo11HawPMC3YC2b\", \"ok\": true, \"num_spillslots\": 0, \"allocs\": [[\"x8\", \"x0\"], [], [\"x9\", \"x0\"], [\"x10\", \"x0\"], [\"x9\", \"x8\"], [\"x10\", \"x8\"], [], [\"x0\"]], \"edits\": [{\"inst\": 7, \"pos\": \"before\", \"from\": \"x8\", \"to\": \"x0\"}], \"checker\": \"ok\"}]}\n"

/-- `sret_caller` -/
def fn1 : FnInput where
  clif := "\nfunction %sret_caller(i64, i64) system_v {\n    fn0 = colocated %_RNxC7fv_demo11HawPMC3YC2b(i64 sret, i64) system_v\n\nblock0(v0: i64, v1: i64):\n    call fn0(v0, v1)\n    return\n}\n"
  ra := "{\"functions\": [{\"name\": \"sret_caller\", \"ok\": true, \"num_spillslots\": 0, \"allocs\": [[\"x0\", \"x1\"], [\"x8\", \"x0\", \"x0\"], []], \"edits\": [{\"inst\": 1, \"pos\": \"before\", \"from\": \"x0\", \"to\": \"x8\"}, {\"inst\": 1, \"pos\": \"before\", \"from\": \"x1\", \"to\": \"x0\"}], \"checker\": \"ok\"}]}\n"

/-- `float_leaf` -/
def fn2 : FnInput where
  clif := "\nfunction %float_leaf(f64) -> f64 {\nblock0(v0: f64):\n    return v0\n}\n"
  ra := "{\"functions\": [{\"name\": \"float_leaf\", \"ok\": true, \"num_spillslots\": 0, \"allocs\": [[\"v0\"], [\"v0\"]], \"edits\": [], \"checker\": \"ok\"}]}\n"

/-- Slice 0 of the functions. -/
def slice0 : List FnInput := [fn0, fn1, fn2]

/-- The crate's input. -/
def input : LinkInput where
  funcs := slice0
  addrs := [
    ("_RNxC7fv_demo11HawPMC3YC2b", 2097504),
    ("sret_caller", 2097544),
    ("float_leaf", 2097576)]
  syms := [
    ]
  raStar := 8
  D := 16

/-- Fixed production callback and the original preparation-mode flag. -/
def compilerInput : SemanticStackBound.CompilerInput where
  toLinkInput := input
  cleanup := false
  lower := (Backend.Stock.VoidCall.NI.lowerWithRoutes [("_RNxC7fv_demo11HawPMC3YC2b", 0), ("sret_caller", 0)])

abbrev actualLower := compilerInput.lower

abbrev actualStage := compilerInput.stage
abbrev actualResults := compilerInput.results

/-- The data objects the program reaches (`cargo fv link-proof`'s `; data:` lines). -/

def initial : Link.LinkSpec := {
  funcs := input.funcs
  names := []
  sizes := []
  outside := []
  symNames := input.syms.map (·.1)
  R := 0x200160 }
def spec : Link.LinkSpec := initial.placedProductionWith actualLower false
def file0 : ByteArray := match Link.Ld.assemble (ProductionBoundaryWitness.plan spec) with
  | .ok image => image.write
  | .error _ => ByteArray.empty
def file : ByteArray := getOk (TypedCompilerWith.attempt actualLower spec file0 false)
-- witness: native_decide (actual full captured program, float leaf, and allocator answers)
theorem compiler_success : TypedCompilerWith.attempt actualLower spec file0 false = .ok file := by
  native_decide
end Raw

namespace Cleanup
def fn0 : FnInput where
  clif := "set regalloc_algorithm=backtracking\nset opt_level=none\nset tls_model=elf_gd\nset stack_switch_model=none\nset libcall_call_conv=isa_default\nset probestack_size_log2=12\nset probestack_strategy=inline\nset bb_padding_log2_minus_one=0\nset log2_min_function_alignment=0\nset regalloc_checker=0\nset regalloc_verbose_logs=0\nset enable_alias_analysis=1\nset enable_verifier=0\nset is_pic=1\nset use_colocated_libcalls=0\nset enable_nan_canonicalization=0\nset enable_pinned_reg=0\nset enable_llvm_abi_extensions=1\nset enable_multi_ret_implicit_sret=0\nset unwind_info=1\nset preserve_frame_pointers=1\nset machine_code_cfg_info=0\nset enable_probestack=1\nset enable_heap_access_spectre_mitigation=1\nset enable_table_access_spectre_mitigation=1\nset enable_incremental_compilation_cache_checks=0\nset enable_compact_unwind_abi=0\ntarget aarch64 has_lse=0 has_pauth=0 has_fp16=0 has_dotprod=0 has_i8mm=0 sign_return_address_all=0 sign_return_address=0 sign_return_address_with_bkey=0 use_bti=0 use_csdb=0\n\nfunction %_RNxC7fv_demo11HawPMC3YC2b(i64 sret, i64) system_v {\nblock0(v0: i64, v1: i64):\n    nop\n    jump block1\n\nblock1:\n    nop\n    v2 = load.i64 notrap v1\n    v3 = load.i64 notrap v1+8\n    store.i64 notrap v2, v0\n    store.i64 notrap v3, v0+8\n    jump block2\n\nblock2:\n    nop\n    return\n}\n"
  ra := "{\"functions\": [{\"name\": \"_RNxC7fv_demo11HawPMC3YC2b\", \"ok\": true, \"num_spillslots\": 0, \"allocs\": [[\"x8\", \"x0\"], [], [\"x9\", \"x0\"], [\"x10\", \"x0\"], [\"x9\", \"x8\"], [\"x10\", \"x8\"], [], [\"x0\"]], \"edits\": [{\"inst\": 7, \"pos\": \"before\", \"from\": \"x8\", \"to\": \"x0\"}], \"checker\": \"ok\"}]}\n"

/-- `sret_caller` -/
def fn1 : FnInput where
  clif := "\nfunction %sret_caller(i64, i64) system_v {\n    fn0 = colocated %_RNxC7fv_demo11HawPMC3YC2b(i64 sret, i64) system_v\n\nblock0(v0: i64, v1: i64):\n    call fn0(v0, v1)\n    return\n}\n"
  ra := "{\"functions\": [{\"name\": \"sret_caller\", \"ok\": true, \"num_spillslots\": 0, \"allocs\": [[\"x0\", \"x1\"], [\"x8\", \"x0\", \"x0\"], []], \"edits\": [{\"inst\": 1, \"pos\": \"before\", \"from\": \"x0\", \"to\": \"x8\"}, {\"inst\": 1, \"pos\": \"before\", \"from\": \"x1\", \"to\": \"x0\"}], \"checker\": \"ok\"}]}\n"

/-- `float_leaf` -/
def fn2 : FnInput where
  clif := "\nfunction %float_leaf(f64) -> f64 {\nblock0(v0: f64):\n    return v0\n}\n"
  ra := "{\"functions\": [{\"name\": \"float_leaf\", \"ok\": true, \"num_spillslots\": 0, \"allocs\": [[\"v0\"], [\"v0\"]], \"edits\": [], \"checker\": \"ok\"}]}\n"

/-- Slice 0 of the functions. -/
def slice0 : List FnInput := [fn0, fn1, fn2]

/-- The crate's input. -/
def input : LinkInput where
  funcs := slice0
  addrs := [
    ("_RNxC7fv_demo11HawPMC3YC2b", 2097504),
    ("sret_caller", 2097544),
    ("float_leaf", 2097576)]
  syms := [
    ]
  raStar := 8
  D := 16

/-- Fixed production callback and the original preparation-mode flag. -/
def compilerInput : SemanticStackBound.CompilerInput where
  toLinkInput := input
  cleanup := true
  lower := (Backend.Stock.VoidCall.NI.lowerWithRoutes [("_RNxC7fv_demo11HawPMC3YC2b", 0), ("sret_caller", 0)])

abbrev actualLower := compilerInput.lower

abbrev actualStage := compilerInput.stage
abbrev actualResults := compilerInput.results

/-- The data objects the program reaches (`cargo fv link-proof`'s `; data:` lines). -/

def initial : Link.LinkSpec := {
  funcs := input.funcs
  names := []
  sizes := []
  outside := []
  symNames := input.syms.map (·.1)
  R := 0x200160 }
def spec : Link.LinkSpec := initial.placedProductionWith actualLower true
def file0 : ByteArray := match Link.Ld.assemble (ProductionBoundaryWitness.plan spec) with
  | .ok image => image.write
  | .error _ => ByteArray.empty
def file : ByteArray := getOk (TypedCompilerWith.attempt actualLower spec file0 true)
-- witness: native_decide (actual full captured program, float leaf, and allocator answers)
theorem compiler_success : TypedCompilerWith.attempt actualLower spec file0 true = .ok file := by
  native_decide
end Cleanup

end Link.TypedCompilerModesWitness
