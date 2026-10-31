import FV.E2E.LinkArmUIndNI
import FV.E2E.LinkArmUGood

/-!
# The linking statement with unwinding, with the per-state facts of every activation (S10g, #404)

`thm_ofU`/`thmU` and `thm_ofUN`/`thmUN` (`FV/E2E/LinkArmUInd.lean`, `FV/E2E/LinkArmUIndNI.lean`)
for `ThmGU`: every machine-side activation that realises a CLIF outcome also has the per-state
facts of its run with unwinding and of the activations nested through its calls (`RunGoodLU`).
The induction step instantiates the per-function world theorem with the per-state trace
(`backend_correct_world_pipelineUG`, `backend_correct_world_ni_pipelineUG`) and turns the trace
into `RunGoodLU` (`runGood_of_traceU`, the nested activations from the statement one level down).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

namespace LinkSysU

variable (L : LinkSysU)
variable {κ : Nat → Clif.Function → Nat}

/-- **The induction step with unwinding, with the per-state facts** (`thm_ofU` for `ThmGU`). -/
theorem thm_ofGU (hL : L.Ok) (hU : L.OkU) [L.CrunOkX] (hκ : L.Budget κ) (hN : ¬ L.NeedNI)
    {M : Nat} (ih : 0 < M → L.ThmGU κ (M - 1)) : L.ThmGU κ M := by
  have ih' : 0 < M → L.ThmU κ (M - 1) := fun h => ThmUQ.toThmU L (ih h)
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
    backend_correct_world_pipelineUG (hL.subset g hg) hc (hU.lowerU g hg)
      (X := L.XU κ M g F) (XR := L.XRU κ M g F) (syms := L.syms)
      (env := L.envOfX M g (spv w₀)) (K := κ M g) (F := F) (c := spv w₀) (hL.covered g hg)
      (L.xCallsOkU hL hU hκ ih' hg hWE.img hWE.room hWE.dead hWE.align)
      (L.xCallsIndOkU hL hU hκ ih' hg hWE.img hWE.room hWE.dead hWE.align)
      (L.xRaiseOkU hL hU hκ ih' hg hWE.img hWE.room hWE.dead hWE.align)
      (L.xRaiseIndOkU hL hU hκ ih' hg hWE.img hWE.room hWE.dead hWE.align)
      (fun d uses w hx => L.XU_excl hU.baseExcl d uses w hx)
      (fun n b hn => hL.symOk n b hn) rfl (T := (L.A g).tables) hsites hlsda hrows hcie hfde
      (hU.pads g hg) (hU.last g hg) (hU.saved g hg) hWE.clif hWE.rel hWE.args htr fuel
  have hAE : ∀ G ra s, L.MachEntry κ M g F G ra s w₀ →
      ActEntryU (L.A g).vcp (L.A g).rf (L.A g).af (L.A g).fa (L.A g).fb (κ M g) F G
        (L.XU κ M g F) (L.hooksU M) (L.XRU κ M g F) (L.UU M) (L.A g).base ra s w₀ :=
    fun G ra s hME =>
      { abi := hME.abi, stack := hME.stack, gfree := hME.gfree, hF := hME.hF,
        calls := L.calleeOkU hL hU hκ ih' hg hME,
        tries := fun _ => L.calleeTryOkU hL hU hκ ih' hg hME,
        tls := fun ht =>
          L.tlsOk_hooksU (hL.baseTls g hg (hasTls_of_vcode_pipeline hc ht) F (κ M g)),
        body := hME.body,
        unw := L.calleeUnwOkU hL hU hκ ih' hg hME }
  refine ⟨fun rvals cm' hrun => ?_, fun htrX c hrun G ra s hME => ?_, fun e cm' hrun => ?_⟩
  · have hrun' : Clif.runLoopX (L.envOfX M g (spv w₀)) L.P.bare fuel cs.toX = .returned rvals cm' :=
      (hrunEq fuel).trans hrun
    obtain ⟨us, outs, wf, hus, hlen, hhold, hmem, hrs, hall⟩ :=
      (pipe (Clif.trapsExplicitX_of_ended (.inl ⟨_, _, hrun'⟩))).1 rvals cm' hrun'
    refine ⟨us, outs, wf, hus, hlen, hhold, hmem, hrs, fun G ra s hME => ?_,
      fun hNI => absurd hNI hN⟩
    obtain ⟨n, hret, hpt, hnu, htr⟩ := hall (L.hooksU M) (L.UU M) G (L.A g).base ra s (hAE G ra s hME)
    exact ⟨n, hret, hpt, hnu, L.runGood_of_traceU hL hU hκ ih hg hME htr fun k hno _ =>
      Nat.lt_of_not_le fun hle => hno n hle (L.retU_of_actRet hME.abi hret)⟩
  · obtain ⟨n, htrap, htr, hst⟩ := (pipe (L.trapsExplicitX_envOfX hL hU hg hJ htrX)).2.1 c
      ((hrunEq fuel).trans hrun) (L.hooksU M) (L.UU M) G (L.A g).base ra s (hAE G ra s hME)
    refine ⟨n, htrap, L.runGood_of_traceU hL hU hκ ih hg hME htr fun k _ hk => ?_⟩
    refine Nat.lt_of_not_le fun hle => hst (k - n) ?_
    rw [show n + (k - n) + 1 = k + 1 by omega]
    exact hk
  · have hrun' : Clif.runLoopX (L.envOfX M g (spv w₀)) L.P.bare fuel cs.toX = .unwound e cm' :=
      (hrunEq fuel).trans hrun
    obtain ⟨obj, wf, hex, hmem, hall⟩ :=
      (pipe (Clif.trapsExplicitX_of_ended (.inr ⟨_, _, hrun'⟩))).2.2 e cm' hrun'
    refine ⟨obj, wf, hex, hmem, fun G ra s hME => ?_, fun hNI => absurd hNI hN⟩
    obtain ⟨n, hu, hpt, hn0, hx, htr⟩ :=
      hall (L.hooksU M) (L.UU M) G (L.A g).base ra s (hAE G ra s hME)
    exact ⟨n, hu, hpt, hn0, hx, L.runGood_of_traceU hL hU hκ ih hg hME htr fun k hno _ =>
      Nat.lt_of_not_le fun hle => hno n hle (L.retU_of_actUnw hME.abi hu)⟩

/-- **The linking statement with unwinding at every depth, with the per-state facts**
(without non-interference). -/
theorem thmGU (hL : L.Ok) (hU : L.OkU) [L.CrunOkX] (hκ : L.Budget κ) (hN : ¬ L.NeedNI) :
    ∀ M, L.ThmGU κ M
  | 0 => L.thm_ofGU hL hU hκ hN fun h => absurd h (Nat.lt_irrefl 0)
  | M + 1 => L.thm_ofGU hL hU hκ hN fun _ => thmGU hL hU hκ hN M

/-- **The induction step with unwinding and non-interference, with the per-state facts**
(`thm_ofUN` for `ThmGU`). -/
theorem thm_ofUNG (hL : L.Ok) (hU : L.OkU) (hNI : L.OkUNI) [L.CrunOkX] (hκ : L.Budget κ)
    {M : Nat} (ih : 0 < M → L.ThmGU κ (M - 1)) : L.ThmGU κ M := by
  have ih' : 0 < M → L.ThmU κ (M - 1) := fun h => ThmUQ.toThmU L (ih h)
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
    backend_correct_world_ni_pipelineUG (hL.subset g hg) hc (hU.lowerU g hg)
      (X := L.XU κ M g F) (XR := L.XRU κ M g F) (syms := L.syms)
      (env := L.envOfX M g (spv w₀)) (K := κ M g) (F := F) (c := spv w₀) (hL.covered g hg)
      (L.xCallsOkU hL hU hκ ih' hg hWE.img hWE.room hWE.dead hWE.align)
      (L.xCallsIndOkU hL hU hκ ih' hg hWE.img hWE.room hWE.dead hWE.align)
      (L.xRaiseOkU hL hU hκ ih' hg hWE.img hWE.room hWE.dead hWE.align)
      (L.xRaiseIndOkU hL hU hκ ih' hg hWE.img hWE.room hWE.dead hWE.align)
      (fun d uses w hx => L.XU_excl hU.baseExcl d uses w hx)
      (fun n b hn => hL.symOk n b hn) rfl (T := (L.A g).tables) hsites hlsda hrows hcie hfde
      (hU.pads g hg) (hU.last g hg) (hU.saved g hg) hWE.clif hWE.rel hWE.args htr fuel
  have hAE : ∀ G ra s w₀', L.MachEntry κ M g F G ra s w₀' →
      ActEntryU (L.A g).vcp (L.A g).rf (L.A g).af (L.A g).fa (L.A g).fb (κ M g) F G
        (L.XU κ M g F) (L.hooksU M) (L.XRU κ M g F) (L.UU M) (L.A g).base ra s w₀' :=
    fun G ra s w₀' hME =>
      { abi := hME.abi, stack := hME.stack, gfree := hME.gfree, hF := hME.hF,
        calls := L.calleeOkU hL hU hκ ih' hg hME,
        tries := fun _ => L.calleeTryOkU hL hU hκ ih' hg hME,
        tls := fun ht =>
          L.tlsOk_hooksU (hL.baseTls g hg (hasTls_of_vcode_pipeline hc ht) F (κ M g)),
        body := hME.body,
        unw := L.calleeUnwOkU hL hU hκ ih' hg hME }
  refine ⟨fun rvals cm' hrun => ?_, fun htrX c hrun G ra s hME => ?_, fun e cm' hrun => ?_⟩
  · have hrun' : Clif.runLoopX (L.envOfX M g (spv w₀)) L.P.bare fuel cs.toX = .returned rvals cm' :=
      (hrunEq fuel).trans hrun
    obtain ⟨us, outs, wf, hus, hlen, hhold, hmem, hrs, hall, hni⟩ :=
      (pipe (Clif.trapsExplicitX_of_ended (.inl ⟨_, _, hrun'⟩))).1 rvals cm' hrun'
    refine ⟨us, outs, wf, hus, hlen, hhold, hmem, hrs, fun G ra s hME => ?_,
      fun hN D w₀' hrel' hsw hreg hstk G ra s hME => ?_⟩
    · obtain ⟨n, hret, hpt, hnu, htr⟩ :=
        hall (L.hooksU M) (L.UU M) G (L.A g).base ra s (hAE G ra s w₀ hME)
      exact ⟨n, hret, hpt, hnu, L.runGood_of_traceU hL hU hκ ih hg hME htr fun k hno _ =>
        Nat.lt_of_not_le fun hle => hno n hle (L.retU_of_actRet hME.abi hret)⟩
    · obtain ⟨n, hret, hpt, hnu, htr⟩ :=
        hni (L.xniU hL hU hN hκ ih' hg hWE.img (spv w₀)) (L.xTlsU hL hN)
          (L.xrniU hL hU hNI hN hκ ih' hg hWE.img (spv w₀)) D w₀' hrel' hsw hreg hstk (L.hooksU M)
          (L.UU M) G (L.A g).base ra s (hAE G ra s w₀' hME)
      exact ⟨n, hret, hpt, hnu, L.runGood_of_traceU hL hU hκ ih hg hME htr fun k hno _ =>
        Nat.lt_of_not_le fun hle => hno n hle (L.retU_of_actRet hME.abi hret)⟩
  · obtain ⟨n, htrap, htr, hst⟩ := (pipe (L.trapsExplicitX_envOfX hL hU hg hJ htrX)).2.1 c
      ((hrunEq fuel).trans hrun) (L.hooksU M) (L.UU M) G (L.A g).base ra s (hAE G ra s w₀ hME)
    refine ⟨n, htrap, L.runGood_of_traceU hL hU hκ ih hg hME htr fun k _ hk => ?_⟩
    refine Nat.lt_of_not_le fun hle => hst (k - n) ?_
    rw [show n + (k - n) + 1 = k + 1 by omega]
    exact hk
  · have hrun' : Clif.runLoopX (L.envOfX M g (spv w₀)) L.P.bare fuel cs.toX = .unwound e cm' :=
      (hrunEq fuel).trans hrun
    obtain ⟨obj, wf, hex, hmem, hall, hni⟩ :=
      (pipe (Clif.trapsExplicitX_of_ended (.inr ⟨_, _, hrun'⟩))).2.2 e cm' hrun'
    refine ⟨obj, wf, hex, hmem, fun G ra s hME => ?_,
      fun hN D w₀' hrel' hsw hreg hstk G ra s hME => ?_⟩
    · obtain ⟨n, hu, hpt, hn0, hx, htr⟩ :=
        hall (L.hooksU M) (L.UU M) G (L.A g).base ra s (hAE G ra s w₀ hME)
      exact ⟨n, hu, hpt, hn0, hx, L.runGood_of_traceU hL hU hκ ih hg hME htr fun k hno _ =>
        Nat.lt_of_not_le fun hle => hno n hle (L.retU_of_actUnw hME.abi hu)⟩
    · obtain ⟨n, hu, hpt, hn0, hx, htr⟩ :=
        hni (L.xniU hL hU hN hκ ih' hg hWE.img (spv w₀)) (L.xTlsU hL hN)
          (L.xrniU hL hU hNI hN hκ ih' hg hWE.img (spv w₀)) D w₀' hrel' hsw hreg hstk (L.hooksU M)
          (L.UU M) G (L.A g).base ra s (hAE G ra s w₀' hME)
      exact ⟨n, hu, hpt, hn0, hx, L.runGood_of_traceU hL hU hκ ih hg hME htr fun k hno _ =>
        Nat.lt_of_not_le fun hle => hno n hle (L.retU_of_actUnw hME.abi hu)⟩

/-- **The linking statement with unwinding at every depth, with the per-state facts**, with
non-interference. -/
theorem thmUNG (hL : L.Ok) (hU : L.OkU) (hNI : L.OkUNI) [L.CrunOkX] (hκ : L.Budget κ) :
    ∀ M, L.ThmGU κ M
  | 0 => L.thm_ofUNG hL hU hNI hκ fun h => absurd h (Nat.lt_irrefl 0)
  | M + 1 => L.thm_ofUNG hL hU hNI hκ fun _ => thmUNG hL hU hNI hκ M

end LinkSysU

end E2E
