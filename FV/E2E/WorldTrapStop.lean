import FV.E2E.WorldTrapCall

/-!
# The per-function world theorem with callee traps, with the stopping state (S9c, #376)

`backend_correct_world_cleanup_trapcall` (`FV/E2E/WorldTrapCall.lean`) with the facts the
linked-program induction needs at the state where the activation stops: its `sp` is the body's
and its program the function's, a trap site's run errs from the step after it on, and the
earlier states form a `PostTrace`.

* `trap_udf_stop`, `trap_trapIf_stop`: `trap_udf` and `trap_trapIf` with the trap site's `sp` and
  program;
* `regLevel_trapStop_core`: `regLevel_trapCall_core` with the trace, the stuck run after a trap
  site, and the `sp` and program of the stopping state;
* `regLevel_trapStop_world`, **`backend_correct_world_cleanup_trapstop`**: the same for
  `regLevel_trapCall_world` and `backend_correct_world_cleanup_trapcall`;
* `postTrace_of_actGoodX`: `PostTrace` from the trace predicate `actGoodX`.
-/

namespace Backend.Proof

open Backend E2E Backend.DeadCleanup

/-- **`udf` on the machine, with the stopping state**: `trap_udf` and the trap site's `sp` (the
body's) and program (the function's). -/
theorem trap_udf_stop {R : RL} (hR : R.Wf) {s : Arm.ArmState} {b k : Nat} {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩)) {vb : VBlock} {code : Clif.TrapCode}
    (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some (.udf code)) :
    TrapAt R.fb R.base code s ∧ (∀ m, Arm.r .ERR (iterN R.step (m + 1) s) ≠ .None) ∧
      spOf s = R.spB ∧ s.program = R.fb.program R.base := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, hst⟩ := q_op hq hvb hi
  obtain ⟨h1, h2⟩ := trap_udf hR hq hvb hi
  exact ⟨h1, h2, hst.sp, hst.prog⟩

/-- **A taken `trapIf` on the machine, with the stopping state**: `trap_trapIf` and the trap
site's `sp` (the body's) and program (the function's). -/
theorem trap_trapIf_stop {R : RL} (hR : R.Wf) {s : Arm.ArmState} {b k : Nat} {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩)) {vb : VBlock} {kk : CondBrKind}
    {code : Clif.TrapCode} (hvb : R.vc.blocks[b]? = some vb)
    (hi : vb.insts[k]? = some (.trapIf kk code)) {ops : Array Operand}
    (hops : (MInst.trapIf kk code).operands = .ok ops)
    (hholds : kk.holds (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w = true) :
    ∃ n, TrapAt R.fb R.base code (iterN R.step n s) ∧ (∀ i < n, R.GoodX (iterN R.step i s)) ∧
      (∀ m, Arm.r .ERR (iterN R.step (n + m + 1) s) ≠ .None) ∧
      spOf (iterN R.step n s) = R.spB ∧ (iterN R.step n s).program = R.fb.program R.base := by
  have hck := (lowerRFunc_ok hR.alloc).2.2
  obtain ⟨j0, items, pre, regs, i', c1, c2, ls1, ls2, ps1, psm, ps2, T, cc, wh, ops', rfl, hit, hsplit,
    hasg, hc1', hops', hstat, hchk', hc2, h1, h2, htr, hdrop, hpc, hst⟩ := q_op hq hvb hi
  rw [hops] at hops'; cases hops'
  have hkk : ∀ r sz, kk = .zero r sz ∨ kk = .notZero r sz → r.isVregInt = true := by
    intro r sz hr
    have := ctlCheck_inst hck hvb hi
    rcases hr with rfl | rfl <;> simpa [ctlInstOk] using this
  obtain ⟨k', rfl, hkr⟩ := kind_alloc hkk (mk := fun k => MInst.trapIf k code) rfl
    (fun f => rfl) (fun f => rfl) hops hstat hasg m
  obtain rfl : c1 = [.inst (.trapIf k' code)] := by
    rcases hc1' with ⟨h, -, -⟩ | ⟨_, h, -⟩ | ⟨_, h, -⟩
    · exact h
    · cases h
    · cases h
  have hl1 := codeLinesE_single h1
  simp only [MInst.lines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hl1
  obtain ⟨rfl, hpsm⟩ := hl1
  -- the branch (relaxed or not) to the trap label is taken
  have hZ : ∀ n, (ls2 ++ nxtOf R.af b)[1]? ≠ some (.label (.trap n)) := by
    intro n e
    have hm := List.mem_of_getElem? e
    rcases List.mem_append.1 hm with hm | hm
    · exact codeLinesE_noTrap _ _ _ _ h2 _ hm n rfl
    · simp only [nxtOf] at hm
      split at hm <;> simp at hm
  have hdrop' : R.L.drop j0 = relaxLine R.far (.ins (k'.insn (.trap ps1.traps.size)) none) ++
      (relaxLines R.far (ftList (ls2 ++ nxtOf R.af b)) ++ T) := by
    rw [hdrop, List.singleton_append, ftList_kind_trap k' ps1.traps.size _ hZ, relaxLines_cons,
      List.append_assoc]
  have hform : (∃ c, k'.insn (.trap ps1.traps.size) = .bcond c (.trap ps1.traps.size)) ∨
      (∃ nz w r, k'.insn (.trap ps1.traps.size) = .cbz nz w r (.trap ps1.traps.size)) ∨
      (∃ nz r bit, k'.insn (.trap ps1.traps.size) = .tbz nz r bit (.trap ps1.traps.size)) := by
    cases k' <;> simp [CondBrKind.insn]
  obtain ⟨nst, jl, hnst, hjt, -, -, -, hgx⟩ := reach_rcbX hR hdrop' hform (by simp) true
    (fun env a ha => by rw [kind_brCond hst hkr _ ha, hholds])
    (fun hct env a ha => by rw [kind_brCond_inv hst hkr _ _ hct ha, hholds])
    (by rw [hst.prog]) hpc hst.err hst.sp
  have hjl := hjt rfl
  -- the trap section entry of this trap
  have hpre : psm.traps.toList <+: R.psF.traps.toList :=
    (codeLinesE_traps h2).trans htr
  have hn : R.psF.traps.toList[ps1.traps.size]? = some (.trap ps1.traps.size, code) := by
    obtain ⟨t, ht⟩ := hpre
    rw [← ht, ← hpsm]
    simp
  obtain ⟨body, psF', hb, hL, -⟩ := emit_block hR.emit
  rw [relaxLines_append, relaxLines_trapLines, List.append_assoc,
    show emitFar ⟨R.fa.k, R.af.slotBase⟩ R.af = R.far from rfl] at hL
  obtain ⟨body', hb'⟩ := hR.psF
  have hk : R.ctx = ⟨R.fa.k, R.af.slotBase⟩ := rfl
  rw [hk, hb] at hb'
  simp only [Except.ok.injEq, Prod.mk.injEq] at hb'
  obtain ⟨-, rfl⟩ := hb'
  obtain ⟨hlab, hudf⟩ := trapLines_get_append _ _ _ _ hn
  have hlab' : R.L[(relaxLines R.far (ftList body)).length + 2 * ps1.traps.size]? = some (.label (.trap ps1.traps.size)) := by
    simp only [RL.L, hL]; rw [List.getElem?_append_right (by omega)]; simpa using hlab
  have hudf' : R.L[(relaxLines R.far (ftList body)).length + 2 * ps1.traps.size + 1]? =
      some (.ins (.udf 0xc11f) (some code)) := by
    simp only [RL.L, hL]; rw [List.getElem?_append_right (by omega)]
    simpa [Nat.add_assoc] using hudf
  -- the branch reaches the label's offset, which is the trap site's
  have hoff : R.pcOf jl = R.pcOf ((relaxLines R.far (ftList body)).length + 2 * ps1.traps.size + 1) := by
    have e1 := labelOffsets_label hR.lm hjl
    have e2 := labelOffsets_label hR.lm hlab'
    simp only [RL.pcOf]
    rw [lineOffset_succ _ _ _ hlab']
    simp only [RL.L] at e1 e2 ⊢
    rw [e1] at e2
    simp only [Option.some.injEq] at e2
    rw [e2]; simp [Line.size]
  have hpcF : Arm.r .PC (iterN R.step nst s) =
      R.pcOf ((relaxLines R.far (ftList body)).length + 2 * ps1.traps.size + 1) := by
    rw [hnst, Arm.r_of_w_same, hoff]
  have herrF : Arm.r .ERR (iterN R.step nst s) = .None := by
    rw [hnst, Arm.r_of_w_different (by simp)]; exact hst.err
  have hprogF : (iterN R.step nst s).program = R.fb.program R.base := by
    rw [hnst, Arm.w_program, hst.prog]
  have hspF : spOf (iterN R.step nst s) = R.spB := by
    simp only [spOf]
    rw [hnst, Arm.r_of_w_different (by simp)]; exact hst.sp
  refine ⟨nst, trapAt_line hR hudf' hpcF herrF, hgx, fun m => ?_, hspF, hprogF⟩
  rw [show nst + m + 1 = nst + (m + 1) by omega, iterN_add]
  exact RL.udf_stuck hR hudf' hpcF hprogF herrF m

/-- **The register level of the explicit and the callee traps, with the stopping state**
(`regLevel_trapCall_core` strengthened): an explicit trap of the VCode run is a trap site of the
machine run after which every state errs, an exceptional end a callee-trap state; in both cases
every earlier state is `GoodX` and the stopping state has the body's `sp` and the function's
program. -/
theorem regLevel_trapStop_core {R : RL} (hR : R.Wf) {ra : BitVec 64}
    (hent : AbiCall R.fb R.base ra R.s0) {cc : CheckCtx} {ins : Array (Option AState)}
    {a0 : AState} (hcheck : CheckedAt R.vc R.rf cc ins a0) {semU : Sem}
    {XT : Option String → List CV → Arm.ArmState → Prop}
    (hgot : GotSem R.gv R.X semU)
    (hRz : Realizes R.vc R.rf semU ckeep R.step (QA R) R.GoodX)
    (hhalt : ∀ i uses w outs w', trapCode? i ≠ none → semU i uses w = some (outs, w', .halt) →
      csem R.F R.ctx R.X i uses w = some (outs, w', .halt))
    {w₀ : Arm.ArmState} (hbe : BodyEntryW R.F R.vc.EntryArg R.af R.s0 w₀)
    (ρsel : (Loc → CV) → Nat → CV)
    (hsel : ∀ m₀ : Loc → CV, Inv ckeep a0 m₀ (ρsel m₀) (fun r => m₀ (.reg r))) :
    ∃ m₀ : Loc → CV,
    (∀ c, VTraps R.vc semU (ρsel m₀) w₀ c →
      ∃ n, TrapAt R.fb R.base c (E2E.runX R.step n R.s0) ∧
        (∀ i < n, R.GoodX (E2E.runX R.step i R.s0)) ∧
        (∀ m, Arm.r .ERR (E2E.runX R.step (n + m + 1) R.s0) ≠ .None) ∧
        spOf (E2E.runX R.step n R.s0) = R.spB ∧
        (E2E.runX R.step n R.s0).program = R.fb.program R.base) ∧
    (∀ obj w', VUnwinds R.vc semU (xrT XT) (ρsel m₀) w₀ obj w' →
      ∃ n, R.CallTrapPre XT (E2E.runX R.step n R.s0) ∧
        (∀ i < n, R.GoodX (E2E.runX R.step i R.s0)) ∧
        spOf (E2E.runX R.step n R.s0) = R.spB ∧
        (E2E.runX R.step n R.s0).program = R.fb.program R.base) := by
  obtain ⟨n0, ht0, hq0, hA0, -⟩ := q_init hR hent hbe
  obtain ⟨hSim, hinit, -⟩ := checkedAt_sound_match (sem := semU) (keep := ckeep) hcheck
    (locVal R.fr (iterN R.step n0 R.s0)) (ρsel (locVal R.fr (iterN R.step n0 R.s0))) w₀ (hsel _)
  have hfin : ∀ n1 n2 n3, E2E.runX R.step (n0 + n1 + n2 + n3) R.s0 =
      iterN R.step n3 (iterN R.step n2 (iterN R.step n1 (iterN R.step n0 R.s0))) := by
    intro n1 n2 n3
    rw [runX_eq]
    simp only [iterN_add]
  refine ⟨locVal R.fr (iterN R.step n0 R.s0), fun c htr => ?_, fun obj w' hu => ?_⟩
  · -- an explicit trap
    obtain ⟨b, k, ρ, w, vb, i, ops, outs, w', hstar, hvb, hi, hops, hsem, htc⟩ := htr
    obtain ⟨n1, c1, hq1, hr1, ht1⟩ := forward hSim hRz hstar hinit (.inl ⟨hq0, hA0⟩)
    obtain ⟨hnil, hform⟩ :=
      csem_halt (hhalt _ _ _ _ _ (by rw [htc]; exact Option.some_ne_none _) hsem)
    subst hnil
    have hdefs : ops.toList.filter Operand.isDef = [] := by
      rcases hform with ⟨cd, rfl⟩ | ⟨kk, cd, rfl, -⟩
      · rw [udf_ops hops]; rfl
      · exact trapIf_nodefs hops
    have h1 : VStep R.vc semU (.run ⟨b, k, ρ, w⟩) (.halt w') :=
      VStep.step hvb hi hops hsem (by rw [hdefs]; rfl) VNext.halt
    obtain ⟨n2, c', c'', hq2, hr2, hms, hr3, ht2⟩ :=
      forward_last hSim hRz h1 _ c1 _ (Nat.le_refl _) hr1 hq1
    cases c'' with
    | run s' => obtain ⟨_, e⟩ := hSim.run hr3; cases e
    | ret vs m' w'' => cases hSim.ret hr3
    | halt w'' =>
      cases hms with
      | op hvb' hi' hops' hsz hsem2 hlen2 hho hcl hn =>
        obtain ⟨hb', hk', hw'⟩ := hSim.at_op hr2
        simp only at hb' hk' hw'
        subst hb' hk' hw'
        rw [hvb] at hvb'; cases hvb'
        rw [hi] at hi'; cases hi'
        have hnr : ∀ us, i ≠ .rets us := by
          intro us h
          rcases hform with ⟨cd, rfl⟩ | ⟨kk, cd, rfl, -⟩ <;> cases h
        have hq2 := (qa_op hq2 hvb hi hnr).1
        rcases hform with ⟨cd, rfl⟩ | ⟨kk, cd, rfl, -⟩
        · simp only [trapCode?, Option.some.injEq] at htc
          subst htc
          obtain ⟨htrap, hstuck, hsp, hprog⟩ := trap_udf_stop hR hq2 hvb hi
          refine ⟨n0 + n1 + n2 + 0, by rw [hfin]; exact htrap, fun i hi => ?_, fun m => ?_,
            by rw [hfin]; exact hsp, by rw [hfin]; exact hprog⟩
          · rw [runX_eq]
            exact trace_add ht0 (trace_add ht1 ht2) i (by omega)
          · rw [show n0 + n1 + n2 + 0 + m + 1 = n0 + n1 + n2 + (m + 1) by omega, hfin]
            exact hstuck m
        · cases hn with
          | halt =>
          obtain ⟨-, hform2⟩ := csem_halt (hhalt _ _ _ _ _ (by simp [trapCode?]) hsem2)
          rcases hform2 with ⟨_, e⟩ | ⟨kk', cd', e, hholds⟩
          · cases e
          · cases e
            simp only [trapCode?, Option.some.injEq] at htc
            subst htc
            obtain ⟨n3, htrap, hgx3, hstuck, hsp, hprog⟩ :=
              trap_trapIf_stop hR hq2 hvb hi hops' hholds
            refine ⟨n0 + n1 + n2 + n3, by rw [hfin]; exact htrap, fun i hi => ?_, fun m => ?_,
              by rw [hfin]; exact hsp, by rw [hfin]; exact hprog⟩
            · rw [runX_eq]
              exact trace_add ht0 (trace_add ht1 (trace_add ht2 hgx3)) i (by omega)
            · rw [show n0 + n1 + n2 + n3 + m + 1 = n0 + n1 + n2 + (n3 + m + 1) by omega, hfin]
              exact hstuck m
  · -- an exceptional end: a `call` whose callee traps
    obtain ⟨b, k, ρ, w1, vb, info, ops, outs, hstar, hvb, hi, hops, hraise, hsem, hlen⟩ := hu
    obtain ⟨n1, c1, hq1, hr1, ht1⟩ := forward hSim hRz hstar hinit (.inl ⟨hq0, hA0⟩)
    have h1 : VStep R.vc semU (.run ⟨b, k, ρ, w1⟩) (.halt w') :=
      VStep.step hvb hi hops hsem hlen VNext.halt
    obtain ⟨n2, c', c'', hq2, hr2, hms, hr3, ht2⟩ :=
      forward_last hSim hRz h1 _ c1 _ (Nat.le_refl _) hr1 hq1
    obtain ⟨u, hu⟩ : ∃ u, iterN R.step n2 (iterN R.step n1 (iterN R.step n0 R.s0)) = u :=
      ⟨_, rfl⟩
    rw [hu] at hq2
    cases hms with
    | move => obtain ⟨_, e⟩ := hSim.run hr3; cases e
    | @op b' k' allocs its m w2 vb' i2 ops2 outs2 outs2' w2' ctl m2 c3 hvb' hi' hops' hsz hsem2
        hlen2 hho hcl hn =>
      obtain ⟨hb', hk', hw'⟩ := hSim.at_op hr2
      simp only at hb' hk' hw'
      subst hb' hk' hw'
      rw [hvb] at hvb'; cases hvb'
      rw [hi] at hi'; cases hi'
      rw [hops] at hops'; cases hops'
      -- the allocated code reads the VCode's uses: the same trapping callee
      have hU0 := matchRun_uses hcheck hr2 (MStep.op hvb hi hops hsz hsem2 hlen2 hho hcl hn) hvb hi
        hops
      have hq2 := (qa_op hq2 hvb hi (fun us h => by cases h)).1
      obtain ⟨j0, items, pre, regs, i', cA, cB, ls1, ls2, ps1, psm, ps2, T', cc', wh, ops'', hal, hit,
        hsplit, hasg, hc1', hops'', hstat, hchk', hcode2, h1', h2', htr', hdrop, hpc, hst⟩ :=
        q_op hq2 hvb hi
      rw [hops] at hops''; cases hops''
      subst hal
      have hm' : ∀ r, r.allocatable = true → m (.reg r) = regVal u r := fun r hr =>
        hst.store (.reg r) (fun r' e => by cases e; exact hr) trivial
      have hraise' : (xrT XT).raise (callDest info) (useVals ops regs u) w1 = some (obj, w') := by
        rw [← useVals_of_store hstat hm', hU0]
        exact hraise
      have hgg : gotGuard R.gv R.X info (useVals ops regs u) := by
        rw [← useVals_of_store hstat hm', hU0]
        exact (hgot _ _ _ _).1 hsem
      have hcpc := callAt_of_q hq2 hvb hi call_hcall regs i' rfl hasg
      have hrun : E2E.runX R.step (n0 + n1 + n2) R.s0 = u := by
        rw [← hu, runX_eq]
        simp only [iterN_add]
      refine ⟨n0 + n1 + n2, ?_, fun i hi => ?_, by rw [hrun]; exact hst.sp,
        by rw [hrun]; exact hst.prog⟩
      · rw [hrun]
        exact ⟨info, ⟨b, vb, k, hvb, hi⟩, by rw [hst.sp]; exact RL.K_le hR,
          fun a ha => by rw [hst.sp] at ha; exact RL.below_F ha, hst.gkeep, cc', wh, ops, regs,
          i', w1, hops, hstat, hasg, hcpc, hst.world, hst.align, hst.err, hgg,
          (xrT_some hraise').1⟩
      · rw [runX_eq]
        exact trace_add ht0 (trace_add ht1 ht2) i (by omega)

end Backend.Proof

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

/-- `PostTrace` from the trace predicate `actGoodX` of an activation's run. -/
theorem postTrace_of_actGoodX {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    {base : BitVec 64} {s : Arm.ArmState} {X : ExtSem} {H : ArmHooks} {K : Nat}
    {G : BitVec 64 → Prop} {gv : Nat → String → Prop} {n : Nat}
    (h : ∀ i < n, actGoodX vcp rf af fa fb base s X H K G gv (runX (ArmStepX X H fa) i s)) :
    PostTrace fa af base (ArmStepX X H fa) s n := by
  intro i _ hi hpc
  exact (h i hi).good.resolve_left fun h => h hpc

/-- **The register level of the explicit and the callee traps for an activation inside a
linked program, with the stopping state** (`regLevel_trapCall_world` strengthened): at a trap
site every later state errs; at a trap site and at a callee-trap state every earlier state is
`GoodX` (`actGoodX`), `sp` is the body's and the program the function's. -/
theorem regLevel_trapStop_world {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin} {k : Nat} (hcheck : checkAlloc vcp rf = .ok ())
    (halloc : lowerRFunc vcp rf = .ok af) (hemit : emitFunc k af = .ok fa)
    (hlayout : fa.layout = .ok fb) {X : ExtSem} {H : ArmHooks} {K : Nat}
    {F G : BitVec 64 → Prop} (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hnt : vcp.hasTryCall = false) (XT : Option String → List CV → Arm.ArmState → Prop)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState}
    (he : ActEntry vcp rf af fa fb K F G X H base ra s w₀) (ρ₀ : Nat → CV) :
    (∀ c, VTraps vcp (valueSemVU (GotV vcp) F ⟨fa.k, af.slotBase⟩ X (xrT XT)) ρ₀ w₀ c →
      ∃ n, TrapAt fb base c (runX (ArmStepX X H fa) n s) ∧
        (∀ i < n, actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
          (runX (ArmStepX X H fa) i s)) ∧
        (∀ m, Arm.r .ERR (runX (ArmStepX X H fa) (n + m + 1) s) ≠ .None) ∧
        spv (runX (ArmStepX X H fa) n s) = spv s - BitVec.ofNat 64 (frameDrop af) ∧
        (runX (ArmStepX X H fa) n s).program = fb.program base) ∧
    (∀ obj w', VUnwinds vcp (valueSemVU (GotV vcp) F ⟨fa.k, af.slotBase⟩ X (xrT XT)) (xrT XT)
        ρ₀ w₀ obj w' →
      ∃ n, CallTrapAt vcp F K G s fa base X (GotV vcp) XT (runX (ArmStepX X H fa) n s) ∧
        (∀ i < n, actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
          (runX (ArmStepX X H fa) i s)) ∧
        spv (runX (ArmStepX X H fa) n s) = spv s - BitVec.ofNat 64 (frameDrop af) ∧
        (runX (ArmStepX X H fa) n s).program = fb.program base) := by
  obtain ⟨cc, ins, hcA⟩ := checked_of_checkAlloc hcheck
  obtain ⟨a0, hat, hle⟩ := hcA.at
  obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hlayout
  obtain ⟨body, psF, hb, -, hk⟩ := emitFunc_ok hemit
  subst hk
  let R : RL := ⟨vcp, rf, af, fa, fb, lm, base, s, X, H, psF, K, G, GotV vcp⟩
  have hR : R.Wf := ⟨⟨cc, ins, a0, hat, entryOk_of_le hle⟩, halloc, hemit, hlayout, hlm,
    by show 4 * fb.words.size ≤ 2 ^ 64; have := he.abi.fits; omega, he.stack, ⟨body, hb⟩,
    he.abi.program, he.gfree⟩
  have hF : R.F = F := he.hF
  have hreal := realizes_value_all hR (by rw [hF]; exact he.calls)
    (fun h => by rw [show R.vc = vcp from rfl, hnt] at h; cases h)
    (by rw [hF]; exact he.tls) hcov
  have hRz := realizes_trapT (semU := valueSemVU R.gv R.F R.ctx R.X (xrT XT)) hreal
    (fun _ _ _ h => valueSemVU_noRaise h)
    (fun _ _ _ _ _ _ h hr => by rw [valueSemVU_call_raise h hr]) hnt
  have hbe' : BodyEntryW R.F R.vc.EntryArg R.af R.s0 w₀ := by
    rw [hF]; exact he.body
  obtain ⟨_, h1, h2⟩ := regLevel_trapStop_core (XT := XT) hR he.abi hat
    (gotSem_valueSemVU _ _ _ _ _) hRz (fun _ _ _ _ _ ht h => valueSemVU_halt_trap ht h) hbe'
    (fun _ => ρ₀) (fun _ => Inv_mono hle Inv_entryState)
  have e1 : valueSemVU R.gv R.F R.ctx R.X (xrT XT) =
      valueSemVU (GotV vcp) F ⟨fa.k, af.slotBase⟩ X (xrT XT) := by
    rw [hF]; rfl
  refine ⟨fun c htr => ?_, fun obj w' hu => ?_⟩
  · rw [← e1] at htr
    obtain ⟨n, htrap, ht, hstuck, hsp, hprog⟩ := h1 c htr
    exact ⟨n, htrap, fun i hi => (ht i hi).act, hstuck, hsp, hprog⟩
  · rw [← e1] at hu
    obtain ⟨n, hct, ht, hsp, hprog⟩ := h2 obj w' hu
    refine ⟨n, ?_, fun i hi => (ht i hi).act, hsp, hprog⟩
    have hct' : CallTrapAt R.vc R.F R.K R.G R.s0 R.fa R.base R.X R.gv XT
        (runX R.step n R.s0) := hct
    rw [hF] at hct'
    exact hct'

/-- **The per-function world theorem with callee traps, with the stopping state**
(`backend_correct_world_cleanup_trapcall` strengthened): every activation (`ActEntry`) of a
function whose run traps with `tc` under `TrapsExplicitC` stops at a state with the body's `sp`
and the function's program, every earlier state `GoodX` (`actGoodX`), which is a trap site of
`f` with `tc` after which every state errs, or a callee-trap state (`CallTrapAt` with the GOT
pins `GotV vcp` and the trapping callees `TrapCallSem … tc`). -/
theorem backend_correct_world_cleanup_trapstop {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledCleanup f k vc vcp rf af fa fb)
    (hlU : lowerCheckU f vc = true)
    (hp : p.funcs = []) (hft : ∀ B ∈ f.blocks, B.term.isTry = false)
    {X : ExtSem} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXT : XTrapsOk env (f.externs.map (·.2)) (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : TrapsExplicitC env p cs) {fuel : Nat} {tc : Clif.TrapCode}
    (hrun : Clif.runLoop env p fuel cs = .trapped tc) :
    ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
      ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
      ∃ n, (∀ i < n, actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
          (runX (ArmStepX X H fa) i s)) ∧
        spv (runX (ArmStepX X H fa) n s) = spv s - BitVec.ofNat 64 (frameDrop af) ∧
        (runX (ArmStepX X H fa) n s).program = fb.program base ∧
        ((TrapAt fb base tc (runX (ArmStepX X H fa) n s) ∧
            ∀ m, Arm.r .ERR (runX (ArmStepX X H fa) (n + m + 1) s) ≠ .None) ∨
          CallTrapAt vcp F K G s fa base X (GotV vcp)
            (TrapCallSem env (f.externs.map (·.2)) (indSigs f)
              (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X tc)
            (runX (ArmStepX X H fa) n s)) := by
  obtain ⟨htrX, hout⟩ := trapEnv_of_trapped env tc hp hft (noTail_of_subset hsub) hcs htr hrun
  let XT := TrapCallSem env (f.externs.map (·.2)) (indSigs f)
    (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X tc
  have hnt : vcp.hasTryCall = false :=
    noTryCall_of_prepCheck hc.prepOk (prune_noTryCall (noTryCall_of_check hc.lowerOk hft))
  have hexcl : ∀ d uses w, X.call d uses w ≠ none → (xrT XT).raise d uses w = none :=
    fun _ _ _ hne => xrT_none fun h => hne h.1
  have hI := iselSimU_relW_cleanup hsub hc hlU (xCallsOk_trapEnv (c := tc) hX)
    (xCallsIndOk_trapEnv (c := tc) hXI) (xRaiseOk_trapEnv hXT) (xRaiseIndOk_trapEnv hXT) hexcl
    hsym hslot (fun _ => 0) hcs hrel hargs htrX fuel
  have hP := prepareCorrectU_cleanup (driverSem_valueSemU F ⟨fa.k, af.slotBase⟩ X (xrT XT))
    (fun _ _ _ _ _ _ hp he => valueSemU_pure hp he) (valueSemU_cmpOverwrite _ _ _ _) hc.prepOk
    (xrT XT)
  intro H G base ra s he
  obtain ⟨hR1, hR2⟩ := regLevel_trapStop_world hc.check hc.alloc hc.emit hc.layout hcov hnt XT he
    (fun _ => 0)
  rcases hout with h | ⟨e, m, h⟩
  · obtain ⟨n, hn, ht, hstuck, hsp, hprog⟩ := hR1 tc
      (vTraps_gotV_gen (gotPair_valueU _ _ _) ((hP.1 _ _).2 tc (hI.2.1 tc h)))
    exact ⟨n, ht, hsp, hprog, .inl ⟨hn, hstuck⟩⟩
  · obtain ⟨obj, w, hv, -, -⟩ := hI.2.2 e m h
    obtain ⟨n, hct, ht, hsp, hprog⟩ :=
      hR2 obj w (vUnwinds_gotV_gen (gotPair_valueU _ _ _) (hP.2 _ _ _ _ hv))
    exact ⟨n, ht, hsp, hprog, .inr hct⟩

end E2E
