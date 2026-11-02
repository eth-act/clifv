import FV.Backend.Proof.StockMemoryComputedStoreRecordSpec
import FV.Clif.Parse
import FV.Backend.Proof.LowerDecide

namespace Backend.Stock.Memory.StoreRoots.ComputedFixture
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

-- Original source SHA256: c4851e2c711ae5323f1f8edb3b7e7b35b788294dfd42368221cbdd6bd917996e
private def capturedText : String := "set regalloc_algorithm=backtracking\nset opt_level=none\nset tls_model=elf_gd\nset stack_switch_model=none\nset libcall_call_conv=isa_default\nset probestack_size_log2=12\nset probestack_strategy=inline\nset bb_padding_log2_minus_one=0\nset log2_min_function_alignment=0\nset regalloc_checker=0\nset regalloc_verbose_logs=0\nset enable_alias_analysis=1\nset enable_verifier=0\nset is_pic=1\nset use_colocated_libcalls=0\nset enable_nan_canonicalization=0\nset enable_pinned_reg=0\nset enable_llvm_abi_extensions=1\nset enable_multi_ret_implicit_sret=0\nset unwind_info=1\nset preserve_frame_pointers=1\nset machine_code_cfg_info=0\nset enable_probestack=1\nset enable_heap_access_spectre_mitigation=1\nset enable_table_access_spectre_mitigation=1\nset enable_incremental_compilation_cache_checks=0\nset enable_compact_unwind_abi=0\ntarget aarch64 has_lse=0 has_pauth=0 has_fp16=0 has_dotprod=0 has_i8mm=0 sign_return_address_all=0 sign_return_address=0 sign_return_address_with_bkey=0 use_bti=0 use_csdb=0\n\nfunction %_RNxC7fv_demo11HawPMC3YC2b(i64 sret, i64) system_v {\nblock0(v0: i64, v1: i64):\n    nop\n    jump block1\n\nblock1:\n    nop\n    v2 = load.i64 notrap v1\n    v3 = load.i64 notrap v1+8\n    store.i64 notrap v2, v0\n    store.i64 notrap v3, v0+8\n    jump block2\n\nblock2:\n    nop\n    return\n}\n"

def function : Clif.Function :=
  ((Clif.parseFile capturedText).funcs.head?.bind (fun parsed => parsed.func.toOption)).getD
    {name := "unparsed_captured_input",sig := {},blocks := []}
private def bodyBlock : Clif.Block := function.blocks[1]!
private def entryBlock : Clif.Block := function.blocks[0]!
private def flags : Clif.MemFlags := {trapCode := none}

private def observed : Option Bool :=
  (Stock.lower function).toOption.map fun result =>
    lowerScopeB function && dominatedB function &&
    decide (function.name = "_RNxC7fv_demo11HawPMC3YC2b") &&
    decide ((function.sig.params[0]?).map (fun q => q.purpose) = some .sret) &&
    result.blockScans.toList.any fun event =>
      decide (function.blocks[event.block]? = some bodyBlock) &&
      decide (bodyBlock.body[1]? = some ⟨[2],.load .load .i64 flags 1 0⟩) &&
      decide (bodyBlock.body[3]? = some ⟨[],.store .store .i64 flags 2 0 0⟩) &&
      decide (function.blocks[0]? = some entryBlock) &&
      decide (0 ∈ entryBlock.params.map (·.1)) &&
      decide (event.ctx.defInst? 2 = some 3) &&
      (event.ctx.insts[3]?).any fun info => info.clif.isSome &&
        decide (info.results[0]? = some 2) && decide (info.resTys[0]? = some (.int 64))

private theorem observed_true : observed = some true := by native_decide

/-- The unchanged captured sret function inhabits both computed-value contracts.
Its first stored value comes from a load instruction,not a parameter. -/
theorem captured_computed_store_record_witness :
    ∃ (f : Clif.Function) (result : Result) (event : BlockScanEvent) (b : Clif.Block),
      f = function ∧ f.name = "_RNxC7fv_demo11HawPMC3YC2b" ∧
      (f.sig.params[0]?).map (fun q => q.purpose) = some .sret ∧
      Stock.lower f = .ok result ∧ event ∈ result.blockScans.toList ∧
      f.blocks[event.block]? = some b ∧
      b.body[1]? = some ⟨[2],.load .load .i64 flags 1 0⟩ ∧
      b.body[3]? = some ⟨[],.store .store .i64 flags 2 0 0⟩ ∧
      event.ctx.defInst? 2 = some 3 ∧
      event.ctx.valueType? 2 = some (.int 64) ∧
      Nonempty (RetainedStoreReturnSpec .plain64 .i64 f result event b 3 2 0 flags) := by
  have actual := observed_true
  unfold observed at actual
  cases run : Stock.lower function with
  | error message => simp only [run,Except.toOption,Option.map_none] at actual; cases actual
  | ok result =>
    simp only [run,Except.toOption,Option.map_some,Option.some.injEq] at actual
    obtain ⟨scopeB,domB,name,sret,event,events,block,loadStatement,statement,parameterBlock,parameter,
      computed,info,source,hasClif,resultAt,typeAt⟩ :=
      (by simpa only [List.any_eq_true,Option.any_eq_true,Bool.and_eq_true,
          decide_eq_true_eq,and_assoc] using actual :
        lowerScopeB function = true ∧ dominatedB function = true ∧
        function.name = "_RNxC7fv_demo11HawPMC3YC2b" ∧
        (function.sig.params[0]?).map (fun q => q.purpose) = some .sret ∧
        ∃ event ∈ result.blockScans.toList,
          function.blocks[event.block]? = some bodyBlock ∧
          bodyBlock.body[1]? = some ⟨[2],.load .load .i64 flags 1 0⟩ ∧
          bodyBlock.body[3]? = some ⟨[],.store .store .i64 flags 2 0 0⟩ ∧
          function.blocks[0]? = some entryBlock ∧ 0 ∈ entryBlock.params.map (·.1) ∧
          event.ctx.defInst? 2 = some 3 ∧
          ∃ info,event.ctx.insts[3]? = some info ∧ info.clif.isSome = true ∧
            info.results[0]? = some 2 ∧ info.resTys[0]? = some (.int 64))
    obtain ⟨inst,clif⟩ := Option.isSome_iff_exists.mp hasClif
    have valueType := stock_lower_source_result_type run (lowerScope_of scopeB)
      (dominated_of domB) events source clif resultAt typeAt
    have spec := stock_mixed_store_record_spec_of_value_type .plain64 .i64 run
      (lowerScope_of scopeB) (dominated_of domB) events block statement parameterBlock parameter
      valueType (by intro h; rfl)
    exact ⟨function,result,event,bodyBlock,rfl,name,sret,run,events,block,loadStatement,statement,computed,valueType,spec⟩

end Backend.Stock.Memory.StoreRoots.ComputedFixture
