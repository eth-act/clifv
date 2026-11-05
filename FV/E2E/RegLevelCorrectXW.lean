import FV.E2E.RegLevelCorrect
import FV.E2E.RegLevelCorrectW
import FV.E2E.RegLevelFrameW
import FV.E2E.RegLevelGotoW
import FV.E2E.RegLevelWrites

/-!
# The register-level theorem with the per-state facts of the run and the writes (A3, #412, slice F8b)

`regLevelCorrect_world_atXW` and `regLevelCorrect_worldXW`: `regLevelCorrect_world_atX` and
`regLevelCorrect_worldX` with `actGoodXW` (`RL.GoodXW`: every state of the run before its return
or trap state has, besides the per-state facts `GoodX`, the writes fact `RL.WritesAt`, whose
memory writes avoid the kept addresses `G`), from `realizes_allW`. Also `trap_trapIfW`,
`trap_trapIf` with the writes.
-/

namespace Backend.Proof

open Backend E2E

/-- The taken branch of a `trapIf` reaches the trap section's `udf` site with the code
(the continuation shared by the mid-block and last-instruction cases). -/
private theorem trapIf_reachW {R : RL} (hR : R.Wf) {s : Arm.ArmState} {m : Loc → CV}
    {w : Arm.ArmState} {kk k' : CondBrKind} {code : Clif.TrapCode} {n j0 : Nat} {T : List Line}
    {us : List CV} (hst : StRel R s m w) (hkr : KindRel m kk k' us)
    (hholds : kk.holds us w = true)
    (hdrop : R.L.drop j0 = relaxLine R.far (.ins (k'.insn (.trap n)) none) ++ T)
    (hpc : Arm.r .PC s = R.pcOf j0)
    (hn : R.psF.traps[n]? = some (.trap n, code)) :
    ∃ nst jl, iterN R.step nst s = Arm.w .PC (R.pcOf jl) s ∧
      TrapAt R.fb R.base code (iterN R.step nst s) ∧ (∀ i < nst, R.GoodXW (iterN R.step i s)) ∧
      ∀ mm, Arm.r .ERR (iterN R.step (nst + mm + 1) s) ≠ .None := by
  have hbc : (∃ c, k'.insn (.trap n) = .bcond c (.trap n)) ∨
      (∃ nz wv r, k'.insn (.trap n) = .cbz nz wv r (.trap n)) ∨
      (∃ nz r bit, k'.insn (.trap n) = .tbz nz r bit (.trap n)) := by
    cases k' <;> simp [CondBrKind.insn]
  obtain ⟨nst, jl, hnst, hjt, -, -, -, hgx⟩ := reach_rcbXW hR hdrop hbc (by simp) true
    (fun env a ha => by rw [kind_brCond hst hkr _ ha, hholds])
    (fun hct env a ha => by rw [kind_brCond_inv hst hkr _ _ hct ha, hholds])
    (by rw [hst.prog]) hpc hst.err hst.sp
  have hjl := hjt rfl
  -- the final lines: the body's segments' relaxation and the trap section
  obtain ⟨p, hp, hL0, -⟩ := emit_seg hR.emit
  obtain ⟨p2, hplan, hps⟩ := hR.psF
  rw [hplan] at hp
  simp only [Except.ok.injEq] at hp
  subst hp
  have hL : R.L = relaxLines R.far (segLines p2.segs p2.outs) ++ trapLines R.psF := by
    show R.fa.lines.toList = _
    rw [hL0, show (emitFar ⟨R.fa.k, R.af.slotBase⟩ R.af) = R.far from rfl, Plan.lines,
      relaxLines_append, relaxLines_trapLines, hps]
  obtain ⟨hlab, hudf⟩ := trapLines_get R.psF n (.trap n, code) hn
  have hlab' : R.L[(relaxLines R.far (segLines p2.segs p2.outs)).length + 2 * n]? =
      some (.label (.trap n)) := by
    rw [hL, List.getElem?_append_right (by omega)]
    simpa using hlab
  have hudf' : R.L[(relaxLines R.far (segLines p2.segs p2.outs)).length + 2 * n + 1]? =
      some (.ins (.udf 0xc11f) (some code)) := by
    rw [hL, List.getElem?_append_right (by omega)]
    simpa [Nat.add_assoc] using hudf
  -- the branch reaches the label's offset, which is the trap site's
  have hoff : R.pcOf jl = R.pcOf ((relaxLines R.far (segLines p2.segs p2.outs)).length + 2 * n + 1) := by
    have e1 := labelOffsets_label hR.lm hjl
    have e2 := labelOffsets_label hR.lm hlab'
    simp only [RL.pcOf]
    rw [lineOffset_succ _ _ _ hlab']
    simp only [RL.L] at e1 e2 ⊢
    rw [e1] at e2
    simp only [Option.some.injEq] at e2
    rw [e2]; simp [Line.size]
  have hpcF : Arm.r .PC (iterN R.step nst s) =
      R.pcOf ((relaxLines R.far (segLines p2.segs p2.outs)).length + 2 * n + 1) := by
    rw [hnst, Arm.r_of_w_same, hoff]
  have herrF : Arm.r .ERR (iterN R.step nst s) = .None := by
    rw [hnst, Arm.r_of_w_different (by simp)]; exact hst.err
  have hprogF : (iterN R.step nst s).program = R.fb.program R.base := by
    rw [hnst, Arm.w_program, hst.prog]
  refine ⟨nst, jl, hnst, trapAt_line hR hudf' hpcF herrF, hgx, fun mm => ?_⟩
  rw [show nst + mm + 1 = nst + (mm + 1) by omega, iterN_add]
  exact RL.udf_stuck hR hudf' hpcF hprogF herrF mm

/-- **A taken `trapIf` on the machine** with the writes (`trap_trapIf` with `RL.GoodXW`): one
branch to the deferred trap label, whose next line is the trap site; every state before it has
`GoodX` and the writes `RL.WritesAt`. -/
theorem trap_trapIfW {R : RL} (hR : R.Wf) {s : Arm.ArmState} {b k : Nat} {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩)) {vb : VBlock} {kk : CondBrKind}
    {code : Clif.TrapCode} (hvb : R.vc.blocks[b]? = some vb)
    (hi : vb.insts[k]? = some (.trapIf kk code)) {ops : Array Operand}
    (hops : (MInst.trapIf kk code).operands = .ok ops)
    (hholds : kk.holds (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w = true) :
    ∃ n, TrapAt R.fb R.base code (iterN R.step n s) ∧ (∀ i < n, R.GoodXW (iterN R.step i s)) ∧
      ∀ m, Arm.r .ERR (iterN R.step (n + m + 1) s) ≠ .None := by
  have hck := (lowerRFunc_ok hR.alloc).2.2
  rcases Q.cases hq with hqs | ⟨vbf, allocsf, regsf, if_, xf, bx, hvbf, he, hits, half, hins,
    hasgf, hsuccf, itx, hitx, hqx⟩
  rotate_left
  · -- a forwarding block: its `jump` takes no machine step, but a `trapIf`'s assigned form
    -- is no `jump`
    rw [hvb] at hvbf
    cases hvbf
    simp only [RItem.op.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    subst hits
    have hi1 := hi
    rw [hins] at hi1
    simp only [List.getElem?_toArray, List.getElem?_cons_zero, Option.some.injEq] at hi1
    subst hi1
    have htg := (assign_shape hasgf).1
    simp [MInst.targets] at htg
  rcases Nat.lt_or_ge (k + 1) vb.insts.size with hkl | hkge
  · -- not the block's last instruction
    obtain ⟨j0, items, pre, regs, i', c1, c2, X', ls1, ps1, psm, psm', ps2, x, cc, wh, ops'',
      rfl, -, -, hasg, hc1', hops', hstat, -, -, h1, hX2, hT2, htr, hdrop, hpc, hst, -, -⟩ :=
      q_op hR hq hvb hi hkl
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
    have hdrop' : R.L.drop j0 = relaxLine R.far (.ins (k'.insn (.trap ps1.traps.size)) none) ++
        (relaxLines R.far (X' ++ x.2.1) ++ R.L.drop (rix R.far (planLines R.fa.k R.af) x.2.2)) := by
      rw [hdrop, relaxLines_cons, relaxLines_nil, List.append_assoc, List.nil_append]
    have hpre : psm.traps.toList <+: R.psF.traps.toList :=
      (codeLinesE_traps hX2).trans ((codeLinesE_traps hT2).trans htr)
    have hnL : R.psF.traps.toList[ps1.traps.size]? = some (.trap ps1.traps.size, code) := by
      obtain ⟨t, ht⟩ := hpre
      rw [← ht, ← hpsm]
      simp
    have hn : R.psF.traps[ps1.traps.size]? = some (.trap ps1.traps.size, code) := by
      simpa using hnL
    obtain ⟨nst, -, -, hTrap, hgx, hstuck⟩ := trapIf_reachW hR hst hkr hholds hdrop' hpc hn
    exact ⟨nst, hTrap, hgx, hstuck⟩
  · -- the block's last instruction
    have hk1 : k + 1 = vb.insts.size := by
      have hks : k < vb.insts.size := (Array.getElem?_eq_some_iff.1 hi).1
      omega
    obtain ⟨_, vb0, _, _, code0, _, _, _, _, _, hvb0, -, -, hchk0, hcode, -⟩ := id hqs
    rw [hvb] at hvb0; cases hvb0
    obtain rfl : its = [] := hchk0.tail_nil hk1
    obtain ⟨j0, vb0, items, pre, c1, X, ps1, psm, ps2, x, hvb0, hit, hsplit, hchk, hc1, hX, hT,
      htr, hdrop, hpc, hst, hterm⟩ := qs_term hR hqs
    rw [hvb] at hvb0; cases hvb0
    obtain ⟨regs, i0, i', rfl, hi0, hasg, hc1'⟩ := itemCode_op hc1
    rw [hi] at hi0; cases hi0
    obtain ⟨cc, wh, i2, ops2, hi2, hops2, hstat, -⟩ := op_checked hchk
    rw [hi] at hi2; cases hi2
    rw [hops] at hops2; cases hops2
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
    have hX' : codeLinesE R.ctx R.af [] ps1 = .ok (X, psm) := by
      simpa [List.dropLast_singleton] using hX
    have hXe : codeLinesE R.ctx R.af [] ps1 = .ok ([], ps1) := by simp [codeLinesE]
    rw [hXe] at hX'
    simp only [Except.ok.injEq, Prod.mk.injEq] at hX'
    obtain ⟨hX0, hpsm0⟩ := hX'
    subst hX0
    subst hpsm0
    have hT' : codeLinesE R.ctx R.af [.inst (.trapIf k' code)] ps1 = .ok (x.1.term, ps2) := by
      simpa using hT
    have hl1 := codeLinesE_single hT'
    simp only [MInst.lines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hl1
    obtain ⟨hxe, hpsm⟩ := hl1
    have hxterm : x.1.term = [.ins (k'.insn (.trap ps1.traps.size)) none] := by
      first | exact hxe.symm | exact hxe
    -- the emitted `trapIf` line is kept (its target is the trap label, no block label)
    obtain ⟨hlenO, hLO⟩ := termOk_kept (by simp) (by simp) (by simp) (by simp) hterm
    have hx21L : x.2.1.length = 1 := by rw [hlenO]; simp [hxterm]
    obtain ⟨y, hy⟩ : ∃ y, x.2.1[0]? = some y := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hx21 : x.2.1 = [y] := by
      cases h21 : x.2.1 with
      | nil => rw [h21] at hx21L; simp at hx21L
      | cons a as =>
        have hAs : as = [] := by
          rw [h21] at hx21L
          rw [List.length_cons] at hx21L
          exact List.eq_nil_of_length_eq_zero (by omega)
        rw [h21, hAs] at hy
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hy
        rw [hAs, hy]
    have hx0 : x.1.term[0]? = some (.ins (k'.insn (.trap ps1.traps.size)) none) := by
      rw [hxterm]; simp
    rcases hLO 0 _ _ hx0 hy with ⟨hyl, -⟩ | ⟨lb, l2, hxt, -, -, -⟩
    · subst hyl
      have hdrop' : R.L.drop j0 = relaxLine R.far (.ins (k'.insn (.trap ps1.traps.size)) none) ++
          R.L.drop (rix R.far (planLines R.fa.k R.af) x.2.2) := by
        rw [hdrop, List.nil_append, hx21, relaxLines_cons, relaxLines_nil, List.append_assoc,
          List.nil_append]
      have hpre : ps2.traps.toList <+: R.psF.traps.toList := htr
      have hnL : R.psF.traps.toList[ps1.traps.size]? = some (.trap ps1.traps.size, code) := by
        obtain ⟨t, ht⟩ := hpre
        rw [← ht, ← hpsm]
        simp
      have hn : R.psF.traps[ps1.traps.size]? = some (.trap ps1.traps.size, code) := by
        simpa using hnL
      obtain ⟨nst, -, -, hTrap, hgx, hstuck⟩ := trapIf_reachW hR hst hkr hholds hdrop' hpc hn
      exact ⟨nst, hTrap, hgx, hstuck⟩
    · cases k' <;> simp [Line.target?, CondBrKind.insn] at hxt

/-- `regLevelCorrect_world_atX` with the writes. -/
theorem regLevelCorrect_world_atXW {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin} {k : Nat} {cc : CheckCtx} {ins : Array (Option AState)}
    {a0 : AState} (hcheck : CheckedAt vcp rf cc ins a0) (hok : EntryOk a0) (halloc : lowerRFunc vcp rf = .ok af)
    (hemit : emitFunc k af = .ok fa) (hlayout : fa.layout = .ok fb) {X : ExtSem} {H : ArmHooks}
    {K : Nat} {G : BitVec 64 → Prop} {gv : Nat → String → Prop}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    {base ra : BitVec 64} {s : Arm.ArmState} (hent : AbiCall fb base ra s)
    (hres : StackAvail K af s) (hG : ∀ a, G a → ¬ StackBelow (frameDrop af + K) (spv s) a)
    (hC : CalleeOkG (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K G s
      (CallAt fa base) X H vcp.CallSite gv)
    (hCT : vcp.hasTryCall = true → CalleeTryOkG (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K G s
      (CallAt fa base) X H vcp.TrySite gv)
    (hTls : vcp.hasTls = true → TlsOk (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K X H)
    {w₀ : Arm.ArmState} (hbe : BodyEntryW (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) vcp.EntryArg af s w₀)
    (ρsel : (Loc → CV) → Nat → CV)
    (hsel : ∀ m₀ : Loc → CV, Inv ckeep a0 m₀ (ρsel m₀) (fun r => m₀ (.reg r))) :
    ∃ m₀ : Loc → CV,
    (∀ us vals w, VReturns vcp (csemV gv (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) ⟨fa.k, af.slotBase⟩ X) (ρsel m₀) w₀ us vals w →
      ∃ n, (ArmRet ra s (E2E.runX (ArmStepX X H fa) n s) ∧
        (∀ (j : Nat) v p x, us[j]? = some (v, p) → vals[j]? = some x →
          regVal (E2E.runX (ArmStepX X H fa) n s) p = x) ∧
        (∀ a, ¬ (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) a → (E2E.runX (ArmStepX X H fa) n s).mem a = w.mem a) ∧
        (∀ f, ¬ Masked f → f ≠ .GPR 29#5 → f ≠ .GPR 31#5 →
          Arm.r f (E2E.runX (ArmStepX X H fa) n s) = Arm.r f w) ∧
        (∀ a, G a → (E2E.runX (ArmStepX X H fa) n s).mem a = s.mem a) ∧
        (E2E.runX (ArmStepX X H fa) n s).program = s.program ∧
        (∀ i, 0 < i → i < n → PostCall fa base (Arm.r .PC (E2E.runX (ArmStepX X H fa) i s)) →
          spv (E2E.runX (ArmStepX X H fa) i s) = spv s - BitVec.ofNat 64 (frameDrop af))) ∧
        ∀ i < n, actGoodXW vcp rf af fa fb base s X H K G gv (E2E.runX (ArmStepX X H fa) i s)) ∧
    (∀ c, VTraps vcp (csemV gv (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) ⟨fa.k, af.slotBase⟩ X) (ρsel m₀) w₀ c →
      ∃ n, TrapAt fb base c (E2E.runX (ArmStepX X H fa) n s) ∧
        (∀ i < n, actGoodXW vcp rf af fa fb base s X H K G gv (E2E.runX (ArmStepX X H fa) i s)) ∧
        ∀ m, Arm.r .ERR (E2E.runX (ArmStepX X H fa) (n + m + 1) s) ≠ .None) := by
  obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hlayout
  obtain ⟨p, hp, -, hk⟩ := emitFunc_ok hemit
  subst hk
  let R : RL := ⟨vcp, rf, af, fa, fb, lm, base, s, X, H, p.ps, K, G, gv⟩
  have hR : R.Wf := ⟨⟨cc, ins, a0, hcheck, hok⟩, halloc, hemit, hlayout, hlm, by show 4 * fb.words.size ≤ 2 ^ 64; have := hent.fits; omega, hres,
    ⟨p, hp, rfl⟩, hent.program, hG⟩
  have hck := (lowerRFunc_ok hR.alloc).2.2
  obtain ⟨n0, ht0, hq0, hA0, hf0⟩ := q_initW hR hent hbe
  obtain ⟨Rl, hSim, hinit, hkeep⟩ :=
    checkedAt_sound R.vc R.rf R.sem ckeep hcheck (locVal R.fr (iterN R.step n0 s))
      (ρsel (locVal R.fr (iterN R.step n0 s))) w₀ (hsel _)
  have hRz := realizes_allW hR hC hCT hTls hcov
  -- the states of the run: `GoodXW`, from the entry's run (`q_initW`) and the realised items
  have hmk : ∀ (n1 n23 : Nat), (∀ i < n1 + n23, R.GoodXW (iterN R.step i (iterN R.step n0 s))) →
      ∀ i < n0 + (n1 + n23), actGoodXW vcp rf af fa fb base s X H K G gv
        (E2E.runX (ArmStepX X H fa) i s) := by
    intro n1 n23 hb i hi
    rw [runX_eq]
    exact (trace_add ht0 hb i hi).act
  refine ⟨locVal R.fr (iterN R.step n0 s), fun us vals w hret => ?_, fun c htr => ?_⟩
  · -- a return
    obtain ⟨b, k, ρ, w₁, vb, ops, outs, hstar, hvb, hi, hops, hvals, hsem⟩ := hret
    obtain ⟨n1, c1, hq1, hr1, ht1⟩ := forward hSim hRz hstar hinit (.inl ⟨hq0, hA0⟩)
    obtain ⟨ns, rfl⟩ := ctlCheck_rets hck hvb hi
    rw [operands_retsC] at hops
    cases hops
    have hsem' := hsem
    simp only [csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem'
    obtain ⟨rfl, rfl, -⟩ := hsem'
    have h1 : VStep R.vc R.sem (.run ⟨b, k, ρ, w₁⟩) (.ret vals w₁) := by
      rw [hvals]
      refine VStep.step hvb hi (operands_retsC ns) (by rw [hvals] at hsem; exact hsem) ?_ (VNext.ret rfl)
      rw [List.toList_toArray, filter_isDef_retOpsC]; rfl
    obtain ⟨n2, c', c'', hq2, hr2, hms, hr3, ht2⟩ :=
      forward_last hSim hRz h1 _ c1 _ (Nat.le_refl _) hr1 hq1
    have hfin : ∀ n3, E2E.runX (ArmStepX X H fa) (n0 + n1 + n2 + n3) s =
        iterN R.step n3 (iterN R.step n2 (iterN R.step n1 (iterN R.step n0 s))) := by
      intro n3; rw [runX_eq]; simp only [iterN_add]; rfl
    cases c'' with
    | run s' => obtain ⟨_, e⟩ := hSim.run hr3; cases e
    | halt w'' => cases hSim.halt hr3
    | ret uses m' w'' =>
      have hks := hkeep hr3
      cases hms with
      | op hvb' hi' hops' hsz hsem2 hlen2 hho hcl hn =>
        obtain ⟨hb', hk', hw'⟩ := hSim.at_op hr2
        simp only at hb' hk' hw'
        subst hb' hk' hw'
        rw [hvb] at hvb'; cases hvb'
        rw [hi] at hi'; cases hi'
        rw [operands_retsC] at hops'; cases hops'
        have hsem3 := hsem2
        simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem3
        obtain ⟨rfl, rfl, rfl⟩ := hsem3
        cases hn with
        | ret _ =>
        rw [rets_store hlen2 rfl hho hcl] at hks
        obtain ⟨mt, hq2'⟩ := qa_q hq2
        have hst := q_stRel hq2'
        obtain ⟨n3, ht3, hpc, herr, hsp, hx29, hregs, hsaved, hmem, hfld, hprogF, hvalsM⟩ :=
          ret_machineW hR hent hq2 hvb hi
        -- every state of the run before the return is `GoodXW`
        have htr : ∀ i < n0 + n1 + n2 + n3, R.GoodXW (E2E.runX (ArmStepX X H fa) i s) := by
          intro i hi
          rw [runX_eq]
          exact trace_add ht0 (trace_add ht1 (trace_add ht2 ht3)) i (by omega)
        have hm0 : ∀ r, locVal R.fr (iterN R.step n0 s) (.reg r) = regVal (iterN R.step n0 s) r :=
          fun _ => rfl
        refine ⟨n0 + n1 + n2 + n3, ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, fun i hi0 hi hpcall => ?_⟩,
          fun i hi => (htr i hi).act⟩
        rotate_right
        · exact (htr i hi).1.good.resolve_left (fun h => h hpcall)
        all_goals rw [hfin]
        · exact hpc
        · exact herr
        · exact hsp
        · intro n hn
          simp only [calleeSavedX, List.mem_map, List.mem_range] at hn
          obtain ⟨a, ha, rfl⟩ := hn
          by_cases h29 : a = 10
          · subst h29; exact hx29
          obtain ⟨hcs, hal⟩ := calleeSaved_x (n := 19 + a) (by omega) (by omega)
          by_cases hsv : Reg.x (19 + a) ∈ R.af.saves
          · exact hsaved _ hsv
          have k1 := hks _ hcs
          simp only [ckeep, hm0] at k1
          have hne : ∀ q, q < 32 → q ≠ 19 + a →
              Arm.StateField.GPR (rnum (19 + a)) ≠ .GPR (BitVec.ofNat 5 q) :=
            fun q h1 h2 e => rnum_ne (a := 19 + a) (b := q) (by omega) h1 (Ne.symm h2)
              (Arm.StateField.GPR.inj e)
          have k2 := hregs _ hal hsv
          simp only [regVal] at k1 k2
          rw [hf0 _ (by simp) (hne 29 (by omega) (by omega)) (hne 31 (by omega) (by omega))
            (hne 16 (by omega) (by omega))] at k1
          exact setWidth128_inj (k2.trans k1)
        · intro n h8 h16
          obtain ⟨hcs, hal⟩ := calleeSaved_v h8 h16
          by_cases hsv : Reg.v n ∈ R.af.saves
          · exact hsaved _ hsv
          have k1 := hks _ hcs
          simp only [ckeep, hm0] at k1
          have k2 := hregs _ hal hsv
          simp only [regVal] at k1 k2
          rw [hf0 _ (by simp) (by simp) (by simp) (by simp)] at k1
          show (Arm.r (.SFP (rnum n)) _).setWidth 64 = (Arm.r (.SFP (rnum n)) s).setWidth 64
          rw [k2]
          exact setWidth128_inj k1
        · intro j v p x hj hx
          have e1 := hSim.ret hr3
          simp only [VConf.ret.injEq] at e1
          rw [e1.1] at hx
          exact hvalsM _ (operands_retsC ns) j v p x hj hx
        · intro a ha
          rw [hmem]
          exact hst.world.2.1 a ha
        · intro f hf h29 h31
          rw [hfld f hf h29 h31]
          exact hst.world.1 f hf
        · intro a ha
          rw [hmem]
          exact hst.gkeep a ha
        · rw [hprogF, hst.prog]
          exact hent.program.symm
  · -- a trap
    obtain ⟨b, k, ρ, w, vb, i, ops, outs, w', hstar, hvb, hi, hops, hsem, htc⟩ := htr
    obtain ⟨n1, c1, hq1, hr1, ht1⟩ := forward hSim hRz hstar hinit (.inl ⟨hq0, hA0⟩)
    obtain ⟨hnil, hform⟩ := csem_halt (csemV_sub hsem)
    subst hnil
    have hdefs : ops.toList.filter Operand.isDef = [] := by
      rcases hform with ⟨cd, rfl⟩ | ⟨kk, cd, rfl, -⟩
      · rw [udf_ops hops]; rfl
      · exact trapIf_nodefs hops
    have h1 : VStep R.vc R.sem (.run ⟨b, k, ρ, w⟩) (.halt w') :=
      VStep.step hvb hi hops hsem (by rw [hdefs]; rfl) VNext.halt
    obtain ⟨n2, c', c'', hq2, hr2, hms, hr3, ht2⟩ :=
      forward_last hSim hRz h1 _ c1 _ (Nat.le_refl _) hr1 hq1
    have hfin : ∀ n3, E2E.runX (ArmStepX X H fa) (n0 + n1 + n2 + n3) s =
        iterN R.step n3 (iterN R.step n2 (iterN R.step n1 (iterN R.step n0 s))) := by
      intro n3; rw [runX_eq]; simp only [iterN_add]; rfl
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
          obtain ⟨htrap, hstuck⟩ := trap_udf hR hq2 hvb hi
          refine ⟨n0 + n1 + n2 + 0, by rw [hfin]; exact htrap,
            fun i hi => hmk n1 (n2 + 0)
              (trace_add ht1 (trace_add ht2 fun _ h => absurd h (Nat.not_lt_zero _))) i (by omega),
            fun m => ?_⟩
          rw [show n0 + n1 + n2 + 0 + m + 1 = n0 + n1 + n2 + (m + 1) by omega, hfin]
          exact hstuck m
        · cases hn with
          | halt =>
          obtain ⟨-, hform2⟩ := csem_halt (csemV_sub hsem2)
          rcases hform2 with ⟨_, e⟩ | ⟨kk', cd', e, hholds⟩
          · cases e
          · cases e
            simp only [trapCode?, Option.some.injEq] at htc
            subst htc
            obtain ⟨n3, htrap, ht3, hstuck⟩ := trap_trapIfW hR hq2 hvb hi hops' hholds
            refine ⟨n0 + n1 + n2 + n3, by rw [hfin]; exact htrap,
              fun i hi => hmk n1 (n2 + n3) (trace_add ht1 (trace_add ht2 ht3)) i (by omega),
              fun m => ?_⟩
            rw [show n0 + n1 + n2 + n3 + m + 1 = n0 + n1 + n2 + (n3 + m + 1) by omega, hfin]
            exact hstuck m

/-- `regLevelCorrect_worldX` with the writes. -/
theorem regLevelCorrect_worldXW {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin} {k : Nat} (hcheck : checkAlloc vcp rf = .ok ()) (halloc : lowerRFunc vcp rf = .ok af)
    (hemit : emitFunc k af = .ok fa) (hlayout : fa.layout = .ok fb) {X : ExtSem} {H : ArmHooks}
    {K : Nat} {G : BitVec 64 → Prop} {gv : Nat → String → Prop}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    {base ra : BitVec 64} {s : Arm.ArmState} (hent : AbiCall fb base ra s)
    (hres : StackAvail K af s) (hG : ∀ a, G a → ¬ StackBelow (frameDrop af + K) (spv s) a)
    (hC : CalleeOkG (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K G s
      (CallAt fa base) X H vcp.CallSite gv)
    (hCT : vcp.hasTryCall = true → CalleeTryOkG (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K G s
      (CallAt fa base) X H vcp.TrySite gv)
    (hTls : vcp.hasTls = true → TlsOk (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K X H)
    {w₀ : Arm.ArmState} (hbe : BodyEntryW (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) vcp.EntryArg af s w₀) (ρ₀ : Nat → CV) :
    (∀ us vals w, VReturns vcp (csemV gv (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) ⟨fa.k, af.slotBase⟩ X) ρ₀ w₀ us vals w →
      ∃ n, (ArmRet ra s (E2E.runX (ArmStepX X H fa) n s) ∧
        (∀ (j : Nat) v p x, us[j]? = some (v, p) → vals[j]? = some x →
          regVal (E2E.runX (ArmStepX X H fa) n s) p = x) ∧
        (∀ a, ¬ (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) a → (E2E.runX (ArmStepX X H fa) n s).mem a = w.mem a) ∧
        (∀ f, ¬ Masked f → f ≠ .GPR 29#5 → f ≠ .GPR 31#5 →
          Arm.r f (E2E.runX (ArmStepX X H fa) n s) = Arm.r f w) ∧
        (∀ a, G a → (E2E.runX (ArmStepX X H fa) n s).mem a = s.mem a) ∧
        (E2E.runX (ArmStepX X H fa) n s).program = s.program ∧
        ∀ i, 0 < i → i < n → PostCall fa base (Arm.r .PC (E2E.runX (ArmStepX X H fa) i s)) →
          spv (E2E.runX (ArmStepX X H fa) i s) = spv s - BitVec.ofNat 64 (frameDrop af)) ∧
        ∀ i < n, actGoodXW vcp rf af fa fb base s X H K G gv (E2E.runX (ArmStepX X H fa) i s)) ∧
    (∀ c, VTraps vcp (csemV gv (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) ⟨fa.k, af.slotBase⟩ X) ρ₀ w₀ c →
      ∃ n, TrapAt fb base c (E2E.runX (ArmStepX X H fa) n s) ∧
        (∀ i < n, actGoodXW vcp rf af fa fb base s X H K G gv (E2E.runX (ArmStepX X H fa) i s)) ∧
        ∀ m, Arm.r .ERR (E2E.runX (ArmStepX X H fa) (n + m + 1) s) ≠ .None) := by
  obtain ⟨cc, ins, hc⟩ := checked_of_checkAlloc hcheck
  obtain ⟨a0, hat, hle⟩ := hc.at
  obtain ⟨_, h⟩ := regLevelCorrect_world_atXW hat (entryOk_of_le hle) halloc hemit hlayout hcov hent
    hres hG hC hCT hTls hbe (fun _ => ρ₀) (fun _ => Inv_mono hle Inv_entryState)
  exact h

end Backend.Proof