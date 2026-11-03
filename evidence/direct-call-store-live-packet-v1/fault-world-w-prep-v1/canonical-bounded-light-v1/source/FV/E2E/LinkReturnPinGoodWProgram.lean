import FV.E2E.LinkReturnPinGoodW
import FV.E2E.LinkReturnPinProgram

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver
namespace LinkSys
variable (L : LinkSys) {modes : Clif.Function → ReturnPinMode}
variable {κ : Nat → Clif.Function → Nat}
set_option autoImplicit false
set_option Elab.async false

theorem thmGW_of_return_pins (hL : L.OkReturnPins modes) (providers : ∀ g ∈ L.P.funcs, ∃ returns, WorldReturnTraceProvider L.P.bare g (L.A g).vc (L.A g).vcp (L.A g).rf (L.A g).af (L.A g).fa (L.A g).fb returns) [L.CrunOk] (hκ : L.Budget κ) {M : Nat} (ih : 0 < M → L.ThmReturnPins modes κ (M - 1))
    (ihG : 0 < M → L.ThmGW κ (M - 1)) : L.ThmGW κ M := by
  intro g hg F vals cs w₀ fuel rvals cm' hWE hrun
  have hc := hL.compiled g hg
  have hI : Clif.LInv (L.P.only g) cs := runInv_entry (by simp [Clif.Program.only]) hWE.clif
  have hJ : L.ActInv g (spv w₀) cs := ⟨hI, hWE.clif.callers, hWE.place⟩
  have hrun' : Clif.runLoop (L.envOf M g (spv w₀)) L.P.bare fuel cs = .returned rvals cm' := by
    rw [L.runLoop_envOf_return_pins hL hg fuel cs hJ]; exact hrun
  obtain ⟨returns,provider⟩ := providers g hg
  have h := provider.run
    (X := L.XMode modes κ M g F) (syms := L.syms)
    (env := L.envOf M g (spv w₀)) (K := κ M g) (F := F) (c := spv w₀) (hL.covered g hg)
    (L.xCallsOk_return_pins hL hκ ih hg hWE.img hWE.room hWE.dead hWE.align)
    (L.xCallsIndOk_return_pins hL hκ ih hg hWE.img hWE.room hWE.dead hWE.align)
    (fun n b hn => hL.symOk n b hn) rfl hWE.clif hWE.rel hWE.args
    (trapsExplicit_of_returned hrun') fuel
  obtain ⟨_us, _outs, _wf, -, -, -, -, -, hall, hni⟩ := h rvals cm' hrun'
  have hAE : ∀ G ra s w₀', L.MachEntry κ M g F G ra s w₀' →
      ActEntry (L.A g).vcp (L.A g).rf (L.A g).af (L.A g).fa (L.A g).fb (κ M g) F G (L.XMode modes κ M g F)
        (L.hooks M) (L.A g).base ra s w₀' := fun G ra s w₀' hME =>
    ⟨hME.abi, hME.stack, hME.gfree, hME.hF, L.calleeOk_return_pins hL hκ ih hg hME,
      fun _ => L.calleeTryOk_return_pins hL hκ ih hg hME,
      fun ht => L.tlsOk_hooks_mode (hL.baseTls g hg (hasTls_of_vcode_return_pins hc ht) F (κ M g)), hME.body⟩
  refine ⟨fun G ra s hME => ?_, fun hN D w₀' hrel' hsw hreg hstk G ra s hME => ?_⟩
  · obtain ⟨n, hret, -, hgood⟩ := hall (L.hooks M) G (L.A g).base ra s (hAE G ra s w₀ hME)
    exact L.runGood_of_traceW_return_pins hL ihG hg hME hgood fun k hno _ =>
      Nat.lt_of_not_le fun hle => hno n hle (L.retL_of_actRet hME.abi hret)
  · obtain ⟨n, hret, -, hgood⟩ := hni (L.xni_return_pins hL hN ih hg hWE.img (spv w₀)) (L.xTls_return_pins hL hN) D w₀'
      hrel' hsw hreg hstk (L.hooks M) G (L.A g).base ra s (hAE G ra s w₀' hME)
    exact L.runGood_of_traceW_return_pins hL ihG hg hME hgood fun k hno _ =>
      Nat.lt_of_not_le fun hle => hno n hle (L.retL_of_actRet hME.abi hret)

/-- **The per-state part of the linking statement at every depth.** -/
theorem thmGW_return_pins (hL : L.OkReturnPins modes) (providers : ∀ g ∈ L.P.funcs, ∃ returns, WorldReturnTraceProvider L.P.bare g (L.A g).vc (L.A g).vcp (L.A g).rf (L.A g).af (L.A g).fa (L.A g).fb returns) [L.CrunOk] (hκ : L.Budget κ) : ∀ M, L.ThmGW κ M
  | 0 => L.thmGW_of_return_pins hL providers hκ (fun h => absurd h (Nat.lt_irrefl 0)) fun h => absurd h (Nat.lt_irrefl 0)
  | M + 1 => L.thmGW_of_return_pins hL providers hκ (fun _ => L.thm_return_pins hL hκ M) fun _ => thmGW_return_pins hL providers hκ M


end LinkSys
end E2E
