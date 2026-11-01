import FV.E2E.PreparedReturnPinProgram
import FV.E2E.ProductionPipelineWith
import FV.E2E.LinkReturnPinGood
import FV.E2E.CompiledSemanticReturnPinsWitness

namespace E2E.PreparedReturnPinSretWitness
open Backend Backend.Proof Backend.Proof.Driver LinkCheck
open Backend.Stock.Memory.StoreRoots.ComputedFixture (function)
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

-- Original source SHA256: c4851e2c711ae5323f1f8edb3b7e7b35b788294dfd42368221cbdd6bd917996e
private def capturedSource : String := "set regalloc_algorithm=backtracking\nset opt_level=none\nset tls_model=elf_gd\nset stack_switch_model=none\nset libcall_call_conv=isa_default\nset probestack_size_log2=12\nset probestack_strategy=inline\nset bb_padding_log2_minus_one=0\nset log2_min_function_alignment=0\nset regalloc_checker=0\nset regalloc_verbose_logs=0\nset enable_alias_analysis=1\nset enable_verifier=0\nset is_pic=1\nset use_colocated_libcalls=0\nset enable_nan_canonicalization=0\nset enable_pinned_reg=0\nset enable_llvm_abi_extensions=1\nset enable_multi_ret_implicit_sret=0\nset unwind_info=1\nset preserve_frame_pointers=1\nset machine_code_cfg_info=0\nset enable_probestack=1\nset enable_heap_access_spectre_mitigation=1\nset enable_table_access_spectre_mitigation=1\nset enable_incremental_compilation_cache_checks=0\nset enable_compact_unwind_abi=0\ntarget aarch64 has_lse=0 has_pauth=0 has_fp16=0 has_dotprod=0 has_i8mm=0 sign_return_address_all=0 sign_return_address=0 sign_return_address_with_bkey=0 use_bti=0 use_csdb=0\n\nfunction %_RNxC7fv_demo11HawPMC3YC2b(i64 sret, i64) system_v {\nblock0(v0: i64, v1: i64):\n    nop\n    jump block1\n\nblock1:\n    nop\n    v2 = load.i64 notrap v1\n    v3 = load.i64 notrap v1+8\n    store.i64 notrap v2, v0\n    store.i64 notrap v3, v0+8\n    jump block2\n\nblock2:\n    nop\n    return\n}\n"

def input : LinkInput := {
  funcs := [{clif := capturedSource,ra := "null"}],
  addrs := [("_RNxC7fv_demo11HawPMC3YC2b",4096)],syms := [],raStar := 8192,D := 4096,fallback := true }
def outputs (cleanup : Bool) : Res := input.resultsProductionWith Stock.MemorySretCopy.lowerValidated cleanup
private def checks (cleanup : Bool) : Bool :=
  okRReturnPins (productionStage cleanup) input (outputs cleanup) &&
  (progOf (outputs cleanup)).funcs.all (fun g => !hasTls g) &&
  decide (input.funcs[0]!.func = function) &&
  !SemanticNI.check function (artOf (outputs cleanup) function).vc &&
  (match Stock.MemorySretCopy.lowerValidated function with
    | .error _ => false
    | .ok vc => decide ((artOf (outputs cleanup) function).vc = vc))

-- witness: native_decide (the two fixed complete pipelines only)
attribute [local irreducible] checks
private theorem checks_true : checks false = true ∧ checks true = true := by
  have both : (checks false && checks true) = true := by native_decide
  exact Bool.and_eq_true_iff.mp both

private theorem checked (cleanup : Bool) :
    okRReturnPins (productionStage cleanup) input (outputs cleanup) = true ∧
      (progOf (outputs cleanup)).funcs.all (fun g => !hasTls g) = true := by
  have h : checks cleanup = true := by
    cases cleanup with
    | false => exact checks_true.1
    | true => exact checks_true.2
  simp only [checks,Bool.and_eq_true,and_assoc] at h
  exact ⟨h.1,h.2.1⟩

def world (cleanup : Bool) : BitVec 64 → Prop :=
  (ofRes input (outputs cleanup) closedBase (fun _ => False)).Img

def system (cleanup : Bool) : LinkSys := ofRes input (outputs cleanup) closedBase (world cleanup)

private theorem base_ok (cleanup : Bool) : BaseOk (system cleanup) :=
  baseOk_closedR fun g member => by
    simpa only [Bool.not_eq_true'] using List.all_eq_true.mp (checked cleanup).2 g member

/-- The original source, including its complete settings header, supplies the actual function. -/
theorem original_source_witness : input.funcs[0]!.func = function := by
  have h := checks_true.1
  simp only [checks,Bool.and_eq_true,and_assoc] at h
  exact of_decide_eq_true h.2.2.1

/-- The complete ABI-aware contract is jointly inhabited by the unchanged sret capture. -/
theorem system_ok (cleanup : Bool) : (system cleanup).OkSemanticReturnPins :=
  semanticPreparedReturnPinsResults_sound (productionStage cleanup) (productionStage_cases cleanup)
    (input.resultsProductionWith_prepared Stock.MemorySretCopy.lowerValidated cleanup)
    (checked cleanup).1 (base_ok cleanup) (fun _ h => h)

/-- The actual compiled sret artifact uses the Stock ABI branch rather than the old branch. -/
theorem selected_stock_abi (cleanup : Bool) :
    ReturnPinMode.checked function ((system cleanup).A function).vc = .stockABI := by
  have h : checks cleanup = true := by
    cases cleanup with
    | false => exact checks_true.1
    | true => exact checks_true.2
  simp only [checks,Bool.and_eq_true,and_assoc] at h
  have old : SemanticNI.check function ((system cleanup).A function).vc = false :=
    by simpa only [Bool.not_eq_true',system,ofRes] using h.2.2.2.1
  simp only [ReturnPinMode.checked,old,Bool.false_eq_true,↓reduceIte]

/-- The source occurs in the actual linked program table in both cleanup modes. -/
theorem entry_present (cleanup : Bool) : function ∈ (system cleanup).P.funcs := by
  change function ∈ [input.funcs[0]!.func]
  rw [original_source_witness]
  exact List.mem_singleton_self _

/-- The actual sret program retains the original program statement for every valid base and world. -/
theorem program_correct (cleanup : Bool) : CrateStmtReturnPins input (outputs cleanup) function.name :=
  preparedReturnPins_correct (productionStage cleanup) (productionStage_cases cleanup)
    (input.resultsProductionWith_prepared Stock.MemorySretCopy.lowerValidated cleanup)
    (checked cleanup).1 _

end E2E.PreparedReturnPinSretWitness
