import FV.E2E.LinkArmUOs
import FV.E2E.LinkArmUX
import FV.E2E.WorldUnwind

/-!
# The linking statement with unwinding at every depth (S10f, #233)

`LinkSys.thm_of`/`thm` (`FV/E2E/LinkArm.lean`) for the linked machine with unwinding, without
non-interference (`¬ NeedNI`): the linking statement with unwinding at depth `M` (`ThmU`) from the
one at depth `M - 1`, by the per-function world theorem with unwinding
(`backend_correct_world_pipelineU`) for the activation's environment `envOfX`, external semantics
`XU` and raising callees `XRU`, its machine-side activations' callee contracts (`calleeOkU`,
`calleeTryOkU`, `calleeUnwOkU`, TLS) and the tables the unwinder reads (`Art.tables`).
-/

namespace E2E

open Backend Backend.Proof

namespace LinkSysU

variable (L : LinkSysU)
variable {κ : Nat → Clif.Function → Nat}

theorem tlsOk_hooksU {F F' : BitVec 64 → Prop} {K M : Nat} {g : Clif.Function}
    (h : TlsOk F K L.Xb L.Hb) : TlsOk F K (L.XU κ M g F') (L.hooksU M) := by
  cases M <;> exact ⟨h.pc, h.seq, h.flags⟩

/-- **The induction step with unwinding** (`thm_of`'s counterpart, without non-interference):
the linking statement with unwinding at depth `M` from the one at depth `M - 1`. -/
theorem thm_ofU (hL : L.Ok) (hU : L.OkU) [L.CrunOkX] (hκ : L.Budget κ) (hN : ¬ L.NeedNI)
    {M : Nat} (ih : 0 < M → L.ThmU κ (M - 1)) : L.ThmU κ M := by
  intro g hg F vals cs w₀ fuel hWE
  have hc := hL.compiled g hg
  have hI : Clif.LInv (L.P.only g) cs := runInv_entry (by simp [Clif.Program.only]) hWE.clif
  have hJ : L.ActInvX g (spv w₀) cs.toX :=
    ⟨⟨hI, by simp [Clif.XState.Aligned, Clif.State.toX]⟩, hWE.clif.callers, hWE.place⟩
  have hrunEq := fun n => L.runLoopX_envOfX hL hU (M := M) hg n cs.toX hJ
  obtain ⟨lsda, hsites⟩ := hU.sites g hg
  obtain ⟨rows, hrows⟩ := hU.rows g hg
  obtain ⟨hlsda, hcie, hfde⟩ := Art.tables_eq hsites hrows
  have pipe := fun (htr : TrapsExplicitX (L.envOfX M g (spv w₀)) L.P.bare cs) =>
    backend_correct_world_pipelineU_any (hL.subset g hg) hc (hU.lowerU g hg)
      (X := L.XU κ M g F) (XR := L.XRU κ M g F) (syms := L.syms)
      (env := L.envOfX M g (spv w₀)) (K := κ M g) (F := F) (c := spv w₀) (hL.covered g hg)
      (L.xCallsOkU hL hU hκ ih hg hWE.img hWE.room hWE.dead hWE.align)
      (L.xCallsIndOkU hL hU hκ ih hg hWE.img hWE.room hWE.dead hWE.align)
      (L.xRaiseOkU hL hU hκ ih hg hWE.img hWE.room hWE.dead hWE.align)
      (L.xRaiseIndOkU hL hU hκ ih hg hWE.img hWE.room hWE.dead hWE.align)
      (fun d uses w hx => L.XU_excl hU.baseExcl d uses w hx)
      (fun n b hn => hL.symOk n b hn) rfl (T := (L.A g).tables) hsites hlsda hrows hcie hfde
      (hU.pads g hg) (hU.saved g hg) hWE.clif hWE.rel hWE.args htr fuel
  have hAE : ∀ G ra s, L.MachEntry κ M g F G ra s w₀ →
      ActEntryU (L.A g).vcp (L.A g).rf (L.A g).af (L.A g).fa (L.A g).fb (κ M g) F G
        (L.XU κ M g F) (L.hooksU M) (L.XRU κ M g F) (L.UU M) (L.A g).base ra s w₀ :=
    fun G ra s hME =>
      { abi := hME.abi, stack := hME.stack, gfree := hME.gfree, hF := hME.hF,
        calls := L.calleeOkU hL hU hκ ih hg hME,
        tries := fun _ => L.calleeTryOkU hL hU hκ ih hg hME,
        tls := fun ht =>
          L.tlsOk_hooksU (hL.baseTls g hg (hasTls_of_vcode_pipeline hc ht) F (κ M g)),
        body := hME.body,
        unw := L.calleeUnwOkU hL hU hκ ih hg hME }
  refine ⟨fun rvals cm' hrun => ?_, fun htrX c hrun G ra s hME => ?_, fun e cm' hrun => ?_⟩
  · have hrun' : Clif.runLoopX (L.envOfX M g (spv w₀)) L.P.bare fuel cs.toX = .returned rvals cm' :=
      (hrunEq fuel).trans hrun
    obtain ⟨us, outs, wf, hus, hlen, hhold, hmem, hrs, hall⟩ :=
      (pipe (Clif.trapsExplicitX_of_ended (.inl ⟨_, _, hrun'⟩))).1 rvals cm' hrun'
    exact ⟨us, outs, wf, hus, hlen, hhold, hmem, hrs,
      fun G ra s hME => hall (L.hooksU M) (L.UU M) G (L.A g).base ra s (hAE G ra s hME),
      fun hNI => absurd hNI hN⟩
  · exact (pipe (L.trapsExplicitX_envOfX hL hU hg hJ htrX)).2.1 c ((hrunEq fuel).trans hrun)
      (L.hooksU M) (L.UU M) G (L.A g).base ra s (hAE G ra s hME)
  · have hrun' : Clif.runLoopX (L.envOfX M g (spv w₀)) L.P.bare fuel cs.toX = .unwound e cm' :=
      (hrunEq fuel).trans hrun
    obtain ⟨obj, wf, hex, hmem, hall⟩ :=
      (pipe (Clif.trapsExplicitX_of_ended (.inr ⟨_, _, hrun'⟩))).2.2 e cm' hrun'
    exact ⟨obj, wf, hex, hmem,
      fun G ra s hME => hall (L.hooksU M) (L.UU M) G (L.A g).base ra s (hAE G ra s hME),
      fun hNI => absurd hNI hN⟩

/-- **The linking statement with unwinding at every depth** (without non-interference). -/
theorem thmU (hL : L.Ok) (hU : L.OkU) [L.CrunOkX] (hκ : L.Budget κ) (hN : ¬ L.NeedNI) :
    ∀ M, L.ThmU κ M
  | 0 => L.thm_ofU hL hU hκ hN fun h => absurd h (Nat.lt_irrefl 0)
  | M + 1 => L.thm_ofU hL hU hκ hN fun _ => thmU hL hU hκ hN M

end LinkSysU

end E2E
