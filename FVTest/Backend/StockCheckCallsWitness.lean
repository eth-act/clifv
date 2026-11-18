import FV.Backend.StockCheckCalls
import FV.Backend.LinearScan
import FV.Opt.Legalize128Pass
import FV.Opt.ConstPhiSelect
import FV.E2E.CompiledSemanticReturnPins

/-! # Witness: the Stock path's theorem instantiated from the driver's own run (#1101)

Two real functions `lean-backend` compiles for the survey crate `a_arith`
(`crate-proofs/Crates/AArith/Input.lean`, `fn0` and `fn1`: `core::num::<impl i32>::saturating_add`
and `core::num::<impl u8>::overflowing_sub`, the CLIF `cargo fv` handed `lean-backend`, one
function per file). `run` is `lean-backend`'s driver as `FVTest/Backend/Main.lean` calls it without
`--opt` (the `i128` legalisation, constant-phi removal, `compileFileReturnPinWhen` enabled, dead
cleanup) with the Lean allocator (`--regalloc lean`, `allocateLeanAnswers`), in `Id`.

`witness` instantiates `E2E.CompiledSemanticReturnPins.of_checks_calls` with **no assumed
`SemanticABI.checkCalls`**: it comes from `Backend.lowerForAllocationVoidCallABI_callsRoute` (the
complete per-function chain, `lowerCheckedVoidCallABI` → … → `lowerChecked`) for the code
`lowerForAllocationVoidCallABI f (verifyOf …) true` whose emitted text the run printed for the
function, and `Backend.compileFileReturnPinWhen_checkCalls` holds of the run (its premises all
satisfied). The facts about the run and the compiled objects (`facts`) are decided by
`native_decide` (a witness, not a compiler theorem). -/

namespace FVTest.Backend.StockCheckCallsWitness
open _root_.Backend _root_.Backend.Proof.Driver E2E
set_option autoImplicit false

/-- `__fv_3bbe099e5f3d__RNvMs0_NtCsazjiGSRkgVH_4core3numl14saturating_add` -/
def src0 : String := "set regalloc_algorithm=backtracking\nset opt_level=none\nset tls_model=elf_gd\nset stack_switch_model=none\nset libcall_call_conv=isa_default\nset probestack_size_log2=12\nset probestack_strategy=inline\nset bb_padding_log2_minus_one=0\nset log2_min_function_alignment=0\nset regalloc_checker=0\nset regalloc_verbose_logs=0\nset enable_alias_analysis=1\nset enable_verifier=0\nset is_pic=1\nset use_colocated_libcalls=0\nset enable_nan_canonicalization=0\nset enable_pinned_reg=0\nset enable_llvm_abi_extensions=1\nset enable_multi_ret_implicit_sret=0\nset unwind_info=1\nset preserve_frame_pointers=1\nset machine_code_cfg_info=0\nset enable_probestack=1\nset enable_heap_access_spectre_mitigation=1\nset enable_table_access_spectre_mitigation=1\nset enable_incremental_compilation_cache_checks=0\nset enable_compact_unwind_abi=0\ntarget aarch64 has_lse=0 has_pauth=0 has_fp16=0 has_dotprod=0 has_i8mm=0 sign_return_address_all=0 sign_return_address=0 sign_return_address_with_bkey=0 use_bti=0 use_csdb=0\n\nfunction %__fv_3bbe099e5f3d__RNvMs0_NtCsazjiGSRkgVH_4core3numl14saturating_add(i32, i32) -> i32 system_v {\nblock0(v0: i32, v1: i32):\n    nop\n    jump block1\n\nblock1:\n    nop\n    v4 = iconst.i32 -2147483648\n    v5 = iconst.i32 2147483647\n    v6 = iadd.i32 v0, v1\n    v7 = iconst.i32 0\n    v8 = icmp.i32 slt v1, v7\n    v9 = icmp.i32 slt v6, v0\n    v10 = bxor.i8 v8, v9\n    v11 = iconst.i32 0\n    v12 = icmp.i32 sge v1, v11\n    v13 = select.i32 v12, v5, v4\n    v14 = select.i32 v10, v13, v6\n    jump block2\n\nblock2:\n    nop\n    return v14\n}\n"

/-- `__fv_3bbe099e5f3d__RNvMs4_NtCsazjiGSRkgVH_4core3numh15overflowing_sub` -/
def src1 : String := "set regalloc_algorithm=backtracking\nset opt_level=none\nset tls_model=elf_gd\nset stack_switch_model=none\nset libcall_call_conv=isa_default\nset probestack_size_log2=12\nset probestack_strategy=inline\nset bb_padding_log2_minus_one=0\nset log2_min_function_alignment=0\nset regalloc_checker=0\nset regalloc_verbose_logs=0\nset enable_alias_analysis=1\nset enable_verifier=0\nset is_pic=1\nset use_colocated_libcalls=0\nset enable_nan_canonicalization=0\nset enable_pinned_reg=0\nset enable_llvm_abi_extensions=1\nset enable_multi_ret_implicit_sret=0\nset unwind_info=1\nset preserve_frame_pointers=1\nset machine_code_cfg_info=0\nset enable_probestack=1\nset enable_heap_access_spectre_mitigation=1\nset enable_table_access_spectre_mitigation=1\nset enable_incremental_compilation_cache_checks=0\nset enable_compact_unwind_abi=0\ntarget aarch64 has_lse=0 has_pauth=0 has_fp16=0 has_dotprod=0 has_i8mm=0 sign_return_address_all=0 sign_return_address=0 sign_return_address_with_bkey=0 use_bti=0 use_csdb=0\n\nfunction %__fv_3bbe099e5f3d__RNvMs4_NtCsazjiGSRkgVH_4core3numh15overflowing_sub(i8, i8) -> i8, i8 uext system_v {\nblock0(v0: i8, v1: i8):\n    nop\n    jump block1\n\nblock1:\n    nop\n    v4 = isub.i8 v0, v1\n    v5 = icmp.i8 ugt v4, v0\n    return v4, v5\n}\n"

/-- `lean-backend --regalloc lean`'s allocator. -/
def alloc (vcs : Array VCode) : Id (Array (Except String AFunc)) := pure (allocateLeanAnswers vcs).1

/-- `lean-backend`'s file before the driver (no `--opt`): the `i128` legalisation, then
constant-phi removal. -/
def legal (src : String) : Opt.Legalize128.Legalized := Opt.Legalize128.parsedFile128 (Clif.parseFile src)
def file (src : String) : Clif.ParsedFile := Opt.ConstPhi.selectFile (Link.clifHeader src) (legal src).file
def pre (src : String) : List (String × String) := (legal src).unverified

/-- The driver's run. -/
def run (src : String) : FileAsm := Id.run (compileFileReturnPinWhen true alloc (file src) (pre src) true)

/-- The first function of a file. -/
def first : List Clif.ParsedFunction → Clif.ParsedFunction
  | q :: _ => q
  | [] => ⟨"", .ok default, 0⟩

/-- The file's function and the objects of its compilation. -/
def p (src : String) : Clif.ParsedFunction := first (file src).funcs
def f (src : String) : Clif.Function := (p src).func.toOption.get!
def code (src : String) : VCode :=
  (lowerForAllocationVoidCallABI (f src) (verifyOf (pre src) (p src).name (f src)) true).toOption.get!
def vcp (src : String) : VCode := (prepare (code src)).toOption.get!
def rf (src : String) : RFunc := (leanAlloc (vcp src)).toOption.get!
def af (src : String) : AFunc := (lowerRFunc (vcp src) (rf src)).toOption.get!
def fa (src : String) : FnAsm := (emitFunc 0 (af src)).toOption.get!
def fb (src : String) : FnBin := (fa src).layout.toOption.get!

/-- What `native_decide` evaluates: one function, of subset E, validated by the driver (`verifyOf`); the run reports it compiled and
neither unverified nor unvalidated and printed exactly `fa`'s text for it; the lowering, `prepare`
with `prepCheck`, the Lean allocation with `checkAlloc`, `lowerRFunc`, `emitFunc`, layout. -/
def facts (src : String) : Bool :=
  (file src).funcs.length == 1 && (p src).func.isOk && Compile.functionE (f src) &&
  verifyOf (pre src) (p src).name (f src) &&
  (run src).funcs.any (·.name == (p src).name) && !(run src).unverified.any (·.1 == (p src).name) &&
  !(run src).unvalidated.any (·.1 == (p src).name) &&
  (run src).funcs.any (fun b => b.name == (p src).name && b.text == (fa src).text) &&
  (lowerForAllocationVoidCallABI (f src) (verifyOf (pre src) (p src).name (f src)) true).isOk &&
  (prepare (code src)).isOk && prepCheck (code src) (vcp src) && (leanAlloc (vcp src)).isOk &&
  (checkAlloc (vcp src) (rf src)).isOk && (lowerRFunc (vcp src) (rf src)).isOk &&
  (emitFunc 0 (af src)).isOk && (fa src).layout.isOk

theorem facts0 : facts src0 = true := by native_decide
theorem facts1 : facts src1 = true := by native_decide

theorem ok_of_isOk {ε α : Type} [Inhabited α] {x : Except ε α} (h : x.isOk = true) :
    x = .ok x.toOption.get! := by
  cases x with
  | error e => cases h
  | ok a => rfl

theorem mem_first {l : List Clif.ParsedFunction} (h : (l.length == 1) = true) : first l ∈ l := by
  cases l with
  | nil => cases h
  | cons a l => exact List.mem_cons_self

/-- **The Stock path's theorem from the run, with no assumed `checkCalls`**: the run satisfies
every premise of `compileFileReturnPinWhen_checkCalls`; it printed `fa`'s text for the function; and
the artifact of `E2E.backend_correct_world_niX_semantic_return_pins` exists for the objects `fa` is
built from, its `SemanticABI.checkCalls` premise given by `lowerForAllocationVoidCallABI_callsRoute`
for the code the driver's validated lowering produced. -/
def Witness (src : String) : Prop :=
  (∃ L, CallsRoute L ∧
    RunsReturn.Ret (compileFileWithLowering L VCode.rulesFired alloc (file src) (pre src) true) (run src) ∧
    ∀ c, L (f src) (verifyOf (pre src) (p src).name (f src)) true = .ok c →
      verifyOf (pre src) (p src).name (f src) = true ∧
      ∃ vc, SemanticABI.checkCalls (f src) vc = true ∧ c = Stock.Arithmetic.stageF true (f src) vc) ∧
  (run src).funcs.any (fun b => b.name == (p src).name && b.text == (fa src).text) = true ∧
  ∃ vc, SemanticABI.checkCalls (f src) vc = true ∧
    code src = Stock.Arithmetic.stageF true (f src) vc ∧
    CompiledSemanticReturnPins (f src) 0 vc (vcp src) (rf src) (af src) (fa src) (fb src)
      (ReturnPinMode.checked (f src) vc)

theorem witness (src : String) (h : facts src = true) : Witness src := by
  unfold Witness
  simp only [facts, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨one, isOk⟩, hE⟩, von⟩, compiled⟩, verified⟩, validated⟩, same⟩, lowered⟩, prepared⟩,
    prepOk⟩, allocated⟩, checked⟩, physical⟩, emitted⟩, laid⟩ := h
  have hf : (p src).func = .ok (f src) := ok_of_isOk isOk
  refine ⟨compileFileReturnPinWhen_checkCalls (m := Id) (alloc := alloc) true (fa := run src) rfl
    (mem_first one) hf hE compiled verified validated, same, ?_⟩
  have hcode : lowerForAllocationVoidCallABI (f src) (verifyOf (pre src) (p src).name (f src)) true =
      .ok (code src) := ok_of_isOk lowered
  rw [von] at hcode
  obtain ⟨vc, calls, stage⟩ := lowerForAllocationVoidCallABI_callsRoute hE hcode
  have prep : prepare (code src) = .ok (vcp src) := ok_of_isOk prepared
  rw [stage] at prep prepOk
  exact ⟨vc, calls, stage, CompiledSemanticReturnPins.of_checks_calls calls prep prepOk
    (ok_of_isOk checked) (ok_of_isOk physical) (ok_of_isOk emitted) (ok_of_isOk laid)⟩

/-- `core::num::<impl i32>::saturating_add`. -/
theorem witness0 : Witness src0 := witness src0 facts0
/-- `core::num::<impl u8>::overflowing_sub`. -/
theorem witness1 : Witness src1 := witness src1 facts1

end FVTest.Backend.StockCheckCallsWitness
