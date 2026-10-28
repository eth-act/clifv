import Crates.TlsFrozen.BinaryExecWitness
import FV.E2E.ExecTlsProven

/-! # Non-vacuity of the hook-free binary theorem (T1)

`E2E.ExecBytes.binary_correct_exec_proven_tls` on the call of `Crates.TlsFrozen.BinaryExecWitness`
(`a_arith`'s `wrapping_add` with `2` and `3`): every premise holds together — the base
environment `leBase I closedBase file` satisfies `BaseOk` (`baseOk_closedLe`, with or without
`tls_value`), the closed base's outside-call hook meets `HooksSim`'s call clause, and the loader
contract `TlsLoader` holds (the entry's thread pointer is `closedBase.tp = 0`; the closed base's
outside-call hook keeps it; the program has no TLSDESC relocation). The theorem gives the
hook-free machine's return to the caller with `5` in x0.

The call is the 2026-10-04 one, frozen in `Crates.TlsFrozen` (#709): the hook-free theory
(`FV/E2E/ExecTls*.lean`) is stated for the `LinkInput.resultsT` compiler, which the shipped routed
compiler no longer emits; porting it to the semantic compiler is open.
-/

namespace Crates.BinaryExecTlsWitness

open E2E E2E.LinkCheck E2E.Binary E2E.BinCheck E2E.ExecBytes Backend Backend.Proof
open Crates.TlsFrozen.BinaryWitness Crates.TlsFrozen.BinaryExecWitness

/-- The witness program has no TLSDESC relocation. -/
theorem noTlsReloc : (tabOf I.results).all (fun e =>
    e.2.fb.relocs.all fun rl => rl.type != .tlsDescAdrPage21) = true := by native_decide

theorem tlsLoader (file : ByteArray) : TlsLoader I closedBase file (r (memOf file)) where
  tp := by
    simp only [r, Arm.r_of_w_different (by decide : Arm.StateField.TPIDR ≠ .PC),
      Arm.r_of_w_different (by decide : Arm.StateField.TPIDR ≠ .GPR 30#5),
      Arm.r_of_w_different (by decide : Arm.StateField.TPIDR ≠ .GPR 31#5),
      Arm.r_of_w_different (by decide : Arm.StateField.TPIDR ≠ .GPR 0#5),
      Arm.r_of_w_different (by decide : Arm.StateField.TPIDR ≠ .GPR 1#5), r_setMem]
    with_unfolding_all rfl
  call d s := by
    show Arm.r .TPIDR (Arm.w .PC (Arm.r .PC s + 4) s) = _
    exact Arm.r_of_w_different (by simp)
  addr g hg rl hrl ht := by
    have hm := tab_mem (okB_names Crates.TlsFrozen.AArithAbort.okB_input) hg
    have := List.all_eq_true.1 (List.all_eq_true.1 noTlsReloc _ hm) rl hrl
    rw [ht] at this
    exact absurd this (by decide)

theorem hooksCall (d : Option String) {m e : Arm.ArmState} (h : Sim I m e) :
    Sim I (closedBase.hooks.call d m) (closedBase.hooks.call d e) := by
  show Sim I (Arm.w .PC (Arm.r .PC m + 4) m) (Arm.w .PC (Arm.r .PC e + 4) e)
  rw [h.1 .PC]
  exact sim_w h _ _

/-- **Non-vacuity of `binary_correct_exec_proven_tls`** (T1): its premises hold together on the
`a_arith` call, and the hook-free executable machine returns to the caller with `5` in x0. -/
theorem binary_correct_exec_proven_tls_witness :
    (∃ file, Elf.Agrees file Crates.TlsFrozen.AArithAbort.exAll) ∧
    ∀ file, Elf.Agrees file Crates.TlsFrozen.AArithAbort.exAll →
      ∃ k, ArmRet ra0 (r (memOf file)) (runX (stepT I closedBase file) k (r (memOf file))) ∧
        XHolds ⟨.i32, 5#32⟩ (xreg 0 (runX (stepT I closedBase file) k (r (memOf file)))) := by
  refine ⟨⟨_, agrees_fileOf⟩, fun file hfile => ?_⟩
  obtain ⟨hX, hoc, hcr, htr, -, -⟩ := binary_correct_exec_witness.2 file hfile
  have h := binary_correct_exec_proven_tls Crates.TlsFrozen.AArithAbort.okB_input codeMap_ok
    (Crates.TlsFrozen.AArithAbort.bin_ok file hfile) (gotB_sound gotB_true hfile) closedBase
    baseOk_closedLe (fun d _ _ h => hooksCall d h) facts.1 acyclic M hX hoc
    (outsideAvoids file) hcr htr (tlsLoader file)
  rw [show Clif.runLoop closedBase.env (prog I) (M + 1) cs = run from rfl, run_eq, x30_r] at h
  obtain ⟨k, hret, hx, -⟩ := h
  exact ⟨k, hret, hx 0 _ rfl⟩

end Crates.BinaryExecTlsWitness
