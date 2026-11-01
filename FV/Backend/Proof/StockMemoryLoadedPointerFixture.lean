import FV.Backend.Proof.StockMemoryComputedStoreRecordSpec
import FV.Clif.Parse
import FV.Backend.Proof.LowerDecide

namespace Backend.Stock.Memory.IntegerRoots.LoadedPointerFixture
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

-- Original source SHA256: 9d39c7307e7fc9b4c3f334692726fae11926683d31f27ea49d032d46e99e70ce
private def capturedText : String := "set regalloc_algorithm=backtracking\nset opt_level=none\nset tls_model=elf_gd\nset stack_switch_model=none\nset libcall_call_conv=isa_default\nset probestack_size_log2=12\nset probestack_strategy=inline\nset bb_padding_log2_minus_one=0\nset log2_min_function_alignment=0\nset regalloc_checker=0\nset regalloc_verbose_logs=0\nset enable_alias_analysis=1\nset enable_verifier=0\nset is_pic=1\nset use_colocated_libcalls=0\nset enable_nan_canonicalization=0\nset enable_pinned_reg=0\nset enable_llvm_abi_extensions=1\nset enable_multi_ret_implicit_sret=0\nset unwind_info=1\nset preserve_frame_pointers=1\nset machine_code_cfg_info=0\nset enable_probestack=1\nset enable_heap_access_spectre_mitigation=1\nset enable_table_access_spectre_mitigation=1\nset enable_incremental_compilation_cache_checks=0\nset enable_compact_unwind_abi=0\ntarget aarch64 has_lse=0 has_pauth=0 has_fp16=0 has_dotprod=0 has_i8mm=0 sign_return_address_all=0 sign_return_address=0 sign_return_address_with_bkey=0 use_bti=0 use_csdb=0\n\nfunction %_RNxC7fv_demo12HezxnGHZarII(i64) system_v {\nblock0(v0: i64):\n    nop\n    jump block1\n\nblock1:\n    nop\n    v2 = load.i64 notrap v0+8\n    v3 = load.i64 notrap v0\n    store.i64 notrap v2, v3\n    return\n}\n"

def function : Clif.Function :=
  ((Clif.parseFile capturedText).funcs.head?.bind (fun parsed => parsed.func.toOption)).getD
    {name := "unparsed_captured_input",sig := {},blocks := []}
private def flags : Clif.MemFlags := {trapCode := none}
private def observed : Option Bool :=
  (Stock.buildCtx function).toOption.map fun built =>
    lowerScopeB function && dominatedB function &&
    decide (built.1.defInst? 3 = some 4) &&
    decide (built.1.valueReg? 3 = some (.vreg 194 .int)) &&
    decide (built.2.2.sunk[4]! = false) &&
    (built.1.insts[4]?).any fun info =>
      decide (info.data = .data 152 16 [.data 151 29 [],.value 0,.op (.memFlags flags),.int 0]) &&
      decide (info.resTys.head? = some (.int 64))
private theorem observed_true : observed = some true := by native_decide

/-- The unchanged captured function supplies an actual loaded-pointer context and sink guard. -/
theorem captured_loaded_pointer_context_witness :
    ∃ (ctx : Ctx) (ranges : Array (Nat × Nat)) (st : State) (info : IInfo),
      Stock.buildCtx function = .ok (ctx,ranges,st) ∧ LowerScope function ∧ Dominated function ∧
      ctx.defInst? 3 = some 4 ∧ ctx.valueReg? 3 = some (.vreg 194 .int) ∧
      ctx.insts[4]? = some info ∧
      info.data = .data 152 16 [.data 151 29 [],.value 0,.op (.memFlags flags),.int 0] ∧
      info.resTys.head? = some (.int 64) ∧ DemandAllowed ctx st 3 := by
  have actual := observed_true
  unfold observed at actual
  cases build : Stock.buildCtx function with
  | error message => simp only [build,Except.toOption,Option.map_none] at actual; cases actual
  | ok built =>
    simp only [build,Except.toOption,Option.map_some,Option.some.injEq] at actual
    obtain ⟨scopeB,domB,defined,mapped,sunk,info,source,data,type⟩ :=
      (by simpa only [Option.any_eq_true,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using actual :
        lowerScopeB function = true ∧ dominatedB function = true ∧
        built.1.defInst? 3 = some 4 ∧ built.1.valueReg? 3 = some (.vreg 194 .int) ∧
        built.2.2.sunk[4]! = false ∧ ∃ info,built.1.insts[4]? = some info ∧
          info.data = .data 152 16 [.data 151 29 [],.value 0,.op (.memFlags flags),.int 0] ∧
          info.resTys.head? = some (.int 64))
    refine ⟨built.1,built.2.1,built.2.2,info,rfl,lowerScope_of scopeB,dominated_of domB,
      defined,mapped,source,data,type,?_⟩
    intro i equal
    have same : i = 4 := Option.some.inj (equal.symm.trans defined)
    subst i
    exact sunk

end Backend.Stock.Memory.IntegerRoots.LoadedPointerFixture
