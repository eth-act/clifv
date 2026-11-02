import FV.Backend.Proof.IselAtomicMemTI
import FV.Backend.Proof.IselMemRootsMemTI
import FV.Backend.Proof.IselMemFuncAddrMemTI
import FV.Backend.Proof.IselTlsMemTI

/-!
# M4 memory family over typed contexts (S11e5 Stage C, slice 7)

`memRulesCorrectRTI_program`: every integer memory root of `lower` (a memory root that is not a
float memory root) is correct under `MemRefinesR Rd` on the subset-E instructions of a typed
context (`MemRulesCorrectRTI`, `CtxT`). The dispatch is `memRulesCorrectR_program`'s with each
rule's `…TI` theorem; the float roots are `MemRulesCorrectRT`'s (`memRulesCorrectRT_program`).
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

/-- **The integer memory roots over typed contexts** (`MemRulesCorrectRTI`). -/
theorem memRulesCorrectRTI_program : MemRulesCorrectRTI program := by
  intro Rd F sb syms isem MR env cp hR hMR hM r hr hmem hfm
  have hsub : r ∈ (program.rulesOf TId.lower).filter memRootRule := List.mem_filter.2 ⟨hr, hmem⟩
  rw [lower_memRoot_filter] at hsub
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hsub
  rcases hsub with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact uextend_atomic_load_okTI data_program
  · exact uextend_load_okTI data_program
  · exact sextend_load_okTI data_program
  · exact atomic_load_okTI data_program hMR hM
  · exact atomic_store_okTI data_program hMR hM
  · exact atomic_rmw_add_okTI data_program hMR hM
  · exact atomic_rmw_sub_okTI data_program hMR hM
  · exact atomic_rmw_and_okTI data_program hMR hM
  · exact atomic_rmw_nand_okTI data_program hMR hM
  · exact atomic_rmw_or_okTI data_program hMR hM
  · exact atomic_rmw_xor_okTI data_program hMR hM
  · exact atomic_rmw_smin_okTI data_program hMR hM
  · exact atomic_rmw_smax_okTI data_program hMR hM
  · exact atomic_rmw_umin_okTI data_program hMR hM
  · exact atomic_rmw_umax_okTI data_program hMR hM
  · exact atomic_rmw_xchg_okTI data_program hMR hM
  · exact atomic_cas_okTI data_program hMR hM
  · exact func_addr_okTI data_program faData_program hR hMR hM
  · exact symbol_value_okTI data_program hR hMR hM
  · exact load_i8_okTI data_program hR hMR hM
  · exact load_i16_okTI data_program hR hMR hM
  · exact load_i32_okTI data_program hR hMR hM
  · exact load_i64_okTI data_program hR hMR hM
  · exact uload8_okTI data_program hR hMR hM
  · exact sload8_okTI data_program hR hMR hM
  · exact uload16_okTI data_program hR hMR hM
  · exact sload16_okTI data_program hR hMR hM
  · exact uload32_okTI data_program hR hMR hM
  · exact sload32_okTI data_program hR hMR hM
  · exact store_i8_okTI data_program hR hMR hM
  · exact store_i16_okTI data_program hR hMR hM
  · exact store_i32_okTI data_program hR hMR hM
  · exact store_i64_okTI data_program hR hMR hM
  · exact istore8_okTI data_program hR hMR hM
  · exact istore16_okTI data_program hR hMR hM
  · exact istore32_okTI data_program hR hMR hM
  · exact stack_addr_okTI data_program hMR hM
  · exact tls_value_okTI data_program hMR hM
  · exact tls_value_macho_okTI data_program
  · exact absurd hfm (by decide)
  · exact absurd hfm (by decide)
  · exact absurd hfm (by decide)
  · exact absurd hfm (by decide)

end Backend.Proof
