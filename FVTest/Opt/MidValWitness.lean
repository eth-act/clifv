import FV.Front.Raw
import FV.Opt.Proof.MidValProg

/-! # The mid-end validator's soundness on a real pair (#1119)

A pair of the measured release crates (memchr 2.8.3, `_RNxC6memchr12H1xhfOL3Wdwp`,
`arch::aarch64::neon::memchr::One::find_raw_impl`): cg_clif's unoptimised dump and Cranelift's
optimised function (`FVTest/Opt/midval/real_memchr.{unopt,opt}.clif`, the dumps with the
comment lines that `Front.readDump` does not read removed). Cranelift forwarded two stored
values to later loads (one across a block boundary, one into the next block), merged three
`stack_addr`s, and removed copies. The certificate is the one `Opt.MidVal.emit` produces; the
re-check `checkCert` is decided (`native_decide`, witness), and the soundness theorem gives
`FunSimMU` and the program refinement (`validated_refines`) for it, with no premise assumed. -/

namespace Opt.MidVal.RealWitness

open Clif

/-- Decode one function of a dump text, as `midval-check` does. -/
def decode (s : String) : Option Function :=
  (do
    let d ← Front.readDump s
    let ρ ← Front.unitTable [d]
    Front.decodeFn ρ d).toOption

def fText : String := "set regalloc_algorithm=backtracking\nset opt_level=speed_and_size\nset tls_model=elf_gd\nset stack_switch_model=none\nset libcall_call_conv=isa_default\nset probestack_size_log2=12\nset probestack_strategy=inline\nset bb_padding_log2_minus_one=0\nset log2_min_function_alignment=0\nset regalloc_checker=0\nset regalloc_verbose_logs=0\nset enable_alias_analysis=1\nset enable_verifier=0\nset is_pic=1\nset use_colocated_libcalls=0\nset enable_nan_canonicalization=0\nset enable_pinned_reg=0\nset enable_llvm_abi_extensions=1\nset enable_multi_ret_implicit_sret=0\nset unwind_info=1\nset preserve_frame_pointers=1\nset machine_code_cfg_info=0\nset enable_probestack=1\nset enable_heap_access_spectre_mitigation=1\nset enable_table_access_spectre_mitigation=1\nset enable_incremental_compilation_cache_checks=0\nset enable_compact_unwind_abi=0\ntarget aarch64 has_lse=0 has_pauth=0 has_fp16=0 has_dotprod=0 has_i8mm=0 sign_return_address_all=0 sign_return_address=0 sign_return_address_with_bkey=0 use_bti=0 use_csdb=0\n\n; symbol _RNxC6memchr12H1xhfOL3Wdwp\nfunction u0:22(i64, i64, i64) -> i64, i64 system_v {\n; symbol _RNxC6memchr12H1xhfOL3Wdwp\n\n\n\n    ss0 = explicit_slot 16, align = 8\n    ss1 = explicit_slot 8, align = 8\n    sig0 = (i64, i64, i64) -> i64, i64 system_v\n    fn0 = colocated u0:89 sig0\n\n                                block0(v0: i64, v1: i64, v2: i64):\n                                    v6 -> v1\n                                    v7 -> v2\n                                    nop\n                                    v3 = stack_addr.i64 ss1\n                                    store notrap v0, v3\n                                    jump block1\n\n                                block1:\n                                    nop\n@0000                               v4 = stack_addr.i64 ss1\n@0000                               v5 = load.i64 notrap v4\n@0000                               nop\n@0000                               v8, v9 = call fn0(v5, v6, v7)\n@0000                               v10 = stack_addr.i64 ss0\n@0000                               store notrap v8, v10\n@0000                               v11 = stack_addr.i64 ss0+8\n@0000                               store notrap v9, v11\n@0000                               jump block2\n\n                                block2:\n@0000                               nop\n@0002                               v12 = stack_addr.i64 ss0\n@0002                               v13 = load.i64 notrap v12\n@0002                               v14 = stack_addr.i64 ss0+8\n@0002                               v15 = load.i64 notrap v14\n@0002                               return v13, v15\n}\n\n; clifv-extnames 1\n; userextname0 = u0:89\n; decl u0:22 func local \"_RNxC6memchr12H1xhfOL3Wdwp\"\n; decl u0:89 func local \"_RNxC6memchr12HilWSXQyxMcb\"\n; end clifv-extnames\n"

def gText : String := "set regalloc_algorithm=backtracking\nset opt_level=speed_and_size\nset tls_model=elf_gd\nset stack_switch_model=none\nset libcall_call_conv=isa_default\nset probestack_size_log2=12\nset probestack_strategy=inline\nset bb_padding_log2_minus_one=0\nset log2_min_function_alignment=0\nset regalloc_checker=0\nset regalloc_verbose_logs=0\nset enable_alias_analysis=1\nset enable_verifier=0\nset is_pic=1\nset use_colocated_libcalls=0\nset enable_nan_canonicalization=0\nset enable_pinned_reg=0\nset enable_llvm_abi_extensions=1\nset enable_multi_ret_implicit_sret=0\nset unwind_info=1\nset preserve_frame_pointers=1\nset machine_code_cfg_info=0\nset enable_probestack=1\nset enable_heap_access_spectre_mitigation=1\nset enable_table_access_spectre_mitigation=1\nset enable_incremental_compilation_cache_checks=0\nset enable_compact_unwind_abi=0\ntarget aarch64 has_lse=0 has_pauth=0 has_fp16=0 has_dotprod=0 has_i8mm=0 sign_return_address_all=0 sign_return_address=0 sign_return_address_with_bkey=0 use_bti=0 use_csdb=0\n\n; symbol _RNxC6memchr12H1xhfOL3Wdwp\nfunction u0:22(i64, i64, i64) -> i64, i64 system_v {\n; symbol _RNxC6memchr12H1xhfOL3Wdwp\n\n\n\n    ss0 = explicit_slot 16, align = 8\n    ss1 = explicit_slot 8, align = 8\n    sig0 = (i64, i64, i64) -> i64, i64 system_v\n    fn0 = colocated u0:89 sig0\n\n                                block0(v0: i64, v1: i64, v2: i64):\n                                    nop\n                                    v3 = stack_addr.i64 ss1\n                                    store notrap v0, v3\n                                    jump block1\n\n                                block1:\n@0000                               v8, v9 = call fn0(v0, v1, v2)\n@0000                               v10 = stack_addr.i64 ss0\n@0000                               store notrap v8, v10\n@0000                               v11 = stack_addr.i64 ss0+8\n@0000                               store notrap v9, v11\n@0000                               jump block2\n\n                                block2:\n@0002                               v13 = load.i64 notrap v10\n@0002                               return v13, v9\n}\n\n; clifv-extnames 1\n; userextname0 = u0:89\n; decl u0:22 func local \"_RNxC6memchr12H1xhfOL3Wdwp\"\n; decl u0:89 func local \"_RNxC6memchr12HilWSXQyxMcb\"\n; end clifv-extnames\n"

/-- The pair and the certificate `emit` gives for it (after constant-phi removal of `f`). -/
def pair : Option (Function × Function × Cert) := do
  let f ← decode fText
  let g ← decode gText
  let cert ← (emit (ConstPhi.run f) g).toOption
  pure (f, g, cert)

/-- The re-check accepts (decided). -/
theorem pair_checked :
    (pair.map fun p => checkCert (ConstPhi.run p.1) p.2.1 p.2.2) = some true := by
  native_decide

theorem pair_some : ∃ f g cert, pair = some (f, g, cert) ∧
    checkCert (ConstPhi.run f) g cert = true := by
  have h := pair_checked
  cases hp : pair with
  | none => rw [hp] at h; cases h
  | some p =>
    obtain ⟨f, g, cert⟩ := p
    rw [hp] at h
    exact ⟨f, g, cert, rfl, by simpa using h⟩

/-- **Soundness on the real pair**: the optimised function simulates the unoptimised one. -/
theorem real_simMU : ∃ f g, (pair.map fun p => (p.1, p.2.1)) = some (f, g) ∧ FunSimMU f g := by
  obtain ⟨f, g, cert, hp, hc⟩ := pair_some
  exact ⟨f, g, by rw [hp]; rfl, checked_simMU hc⟩

/-- **The program corollary on the real pair**: the one-function programs refine. -/
theorem real_refines : ∃ f g, (pair.map fun p => (p.1, p.2.1)) = some (f, g) ∧
    ∀ (syms : String → Option Nat) (env : XEnv), EnvKeepsSymbolsX env →
      ∀ n (xs xs' : XState), SRU syms xs xs' →
        ∃ n', XOutcomeRefines (Clif.runLoopX env { funcs := [f] } n xs)
          (Clif.runLoopX env { funcs := [g] } n' xs') := by
  obtain ⟨f, g, cert, hp, hc⟩ := pair_some
  exact ⟨f, g, by rw [hp]; rfl, fun syms env hE =>
    validated_refines (p := { funcs := [f] }) (q := { funcs := [g] }) hE
      (.checked cert hc .nil)⟩

end Opt.MidVal.RealWitness
