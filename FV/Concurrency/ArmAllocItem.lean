import FV.Concurrency.VCodeThread
import FV.E2E.RegLevelOp

/-!
# The register-level relation with interference: patches and items (T2h, #311, layer 4b)

The per-item lemmas of layer 4b reuse the register-level simulation relation `Backend.Proof.Q`
(`FV/E2E/RegLevelSim.lean`). With interference, the Arm thread and the allocated code read the
environment's bytes; both sides patch their memory with the same read events
(`VCodeThread.patch`), outside the frame addresses `R.F`:

* `q_patch`: **`Q` survives patching both sides with events that avoid `R.F`** (the store reads
  the frame, which the patch leaves; the worlds agree outside `R.F` before and after);
* `realizes_op_lines`: `realizes_op_next` with the item's lines, their position and the
  machine's state after them exposed (the single-core facts the event-level lemmas need).
-/

namespace Concurrency.ArmAllocThread

open Arm ArmFoot ArmThread ArmInstFoot VCodeThread Backend Backend.Proof

/-! ## Patching memories outside the frame -/

theorem writeM_pt : ∀ (n : Nat) (a : BitVec 64) (v : BitVec (n * 8)) {m m' : Memory} {x : BitVec 64},
    m x = m' x → ArmFoot.writeM n a v m x = ArmFoot.writeM n a v m' x
  | 0, _, _, _, _, _, h => h
  | n + 1, a, v, m, m', x, h => by
    simp only [ArmFoot.writeM]
    apply writeM_pt
    simp only [write_store]
    split <;> simp_all

theorem applyR_pt : ∀ (E : List Ev) {m m' : Memory} {x : BitVec 64},
    m x = m' x → applyR E m x = applyR E m' x
  | [], _, _, _, h => h
  | e :: E, m, m', x, h => by
    simp only [applyR]
    apply applyR_pt
    split
    · exact writeM_pt _ _ _ h
    · exact h

theorem applyR_avoid {F : BitVec 64 → Prop} : ∀ {E : List Ev}, (∀ e ∈ E, Avoids F e.n e.addr) →
    ∀ (m : Memory) {x : BitVec 64}, F x → applyR E m x = m x
  | [], _, _, _, _ => rfl
  | e :: E, h, m, x, hx => by
    simp only [applyR]
    rw [applyR_avoid (fun e' he' => h e' (List.mem_cons_of_mem _ he')) _ hx]
    split
    · exact writeM_apply_out _ _ _ _ _ fun k hk e' => h e List.mem_cons_self k hk (e' ▸ hx)
    · rfl

/-- Patching keeps the world outside `F`. -/
theorem sameWorld_patch {F : BitVec 64 → Prop} {s w : ArmState} (h : SameWorld F s w)
    (E : List Ev) : SameWorld F (patch E s) (patch E w) :=
  ⟨fun f hf => by simp only [patch, r_setMem]; exact h.1 f hf,
    fun a ha => by simp only [patch, setMem_mem]; exact applyR_pt E (h.2.1 a ha),
    by simp only [patch, setMem_program]; exact h.2.2⟩

theorem read_mem_bytes_patch {F : BitVec 64 → Prop} {E : List Ev} (hE : ∀ e ∈ E, Avoids F e.n e.addr)
    {s : ArmState} {n : Nat} {a : BitVec 64} (ha : ∀ k < n, F (a + BitVec.ofNat 64 k)) :
    Arm.read_mem_bytes n a (patch E s) = Arm.read_mem_bytes n a s :=
  read_mem_bytes_congr _ _ fun k hk => by
    simp only [patch, setMem_mem]; exact applyR_avoid hE _ (ha k hk)

/-- **The store relation survives patching both sides** with events avoiding `R.F`. -/
theorem stRel_patch {R : RL} (hR : R.Wf) {s w : ArmState} {m : Loc → CV} (h : StRel R s m w)
    {E : List Ev} (hE : ∀ e ∈ E, Avoids R.F e.n e.addr) : StRel R (patch E s) m (patch E w) := by
  have hK : FrameKeep R.FK s (patch E s) :=
    ⟨by simp [patch, spOf, r_setMem], fun a ha => by
      simp only [patch, setMem_mem]; exact applyR_avoid hE _ (RL.FK_F ha), by simp [patch, r_setMem]⟩
  refine ⟨fun l hl hL => ?_, sameWorld_patch h.world E, by rw [patch, r_setMem]; exact h.err,
    by rw [patch, setMem_program]; exact h.prog, by have := h.sp; simp only [spOf, patch, r_setMem] at this ⊢; exact this,
    ?_, fun hframe => ?_, ?_, fun a ha => ?_, fun hf => ?_⟩
  · rw [h.store l hl hL]
    cases l with
    | reg r => simp [locVal, patch, regVal_setMem]
    | stack k c => exact (locVal_frame_keep (R.frameOkK hR) h.sp hK hL (fun r e => by cases e)).symm
    | save r => exact (locVal_frame_keep (R.frameOkK hR) h.sp hK hL (fun r e => by cases e)).symm
  · simpa [Arm.CheckSPAlignment, Arm.read_gpr, patch, r_setMem] using h.align
  · rw [← h.fplr hframe]
    exact read_mem_bytes_congr _ _ fun k hk => hK.2.1 _ (fplr_inF hR hframe k hk)
  · exact code_keep hR.prog0 h.code fun a ha => hK.2.1 a (.inl (.inr (.inr ha)))
  · show (patch E s).mem a = R.s0.mem a
    rw [hK.2.1 a (.inr ha)]; exact h.gkeep a ha
  · exact hK.2.2.trans (h.fp hf)

/-- **`Q` survives patching both sides** with events avoiding `R.F`. -/
theorem q_patch {R : RL} (hR : R.Wf) {s : ArmState} {b : Nat} {its : List RItem} {m : Loc → CV}
    {w : ArmState} (hq : Q R s (.run ⟨b, its, m, w⟩)) {E : List Ev}
    (hE : ∀ e ∈ E, Avoids R.F e.n e.addr) : Q R (patch E s) (.run ⟨b, its, m, patch E w⟩) := by
  obtain ⟨j, vb, items, pre, code, ls, ps1, ps2, T, hvb, hit, hsplit, hchk, hcode, hls, htr, hdrop,
    hpc, hst⟩ := hq
  exact ⟨j, vb, items, pre, code, ls, ps1, ps2, T, hvb, hit, hsplit, hchk, hcode, hls, htr, hdrop,
    by rw [patch, r_setMem]; exact hpc, stRel_patch hR hst hE⟩

/-! ## Straight-line items with their lines -/

/-- **`realizes_op_next` with the lines exposed**: from `Q` at a straight-line instruction item
whose `MStep` continues, the item's allocated instruction `i'` has lines `ls1` at line `j` (the
pc), unhooked and plain, which run to `s'`, and `Q` holds at `s'` with the configuration of a
`MStep` of the item. -/
theorem realizes_op_lines {R : RL} (hR : R.Wf) {s : ArmState} {b k : Nat} {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : ArmState}
    (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩))
    {vb : VBlock} {i : MInst} {ops : Array Operand} {outs : List CV} {w' : ArmState}
    (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some i) (hops : i.operands = .ok ops)
    (hsz : allocs.size = ops.size)
    (hsem : R.sem i (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w =
      some (outs, w', .next))
    (hlen : outs.length = ((ops.zip allocs).toList.filter (·.1.isDef)).length)
    (hk : k + 1 < vb.insts.size)
    (hOS : ∀ env, OperandsSound R.F (execMInst R.ctx env) (csem R.F R.ctx R.X) i)
    (hL : ∀ regs i', i.assign regs = .ok i' →
      LinesOk R.ctx i' ∧ (∀ ds, i' ≠ .args ds) ∧ (∀ us, i' ≠ .rets us))
    (hW' : Arm.r .ERR w' = .None ∧ w'.program = w.program) :
    ∃ (j : Nat) (regs : Array Reg) (i' : MInst) (ls1 T : List Line) (s' : ArmState)
      (c'' : MConf CV ArmState),
      allocs = regs.map Loc.reg ∧ i.assign regs = .ok i' ∧ (∀ ps, i'.lines R.ctx ps = .ok (ls1, ps)) ∧
      (∀ ln ∈ ls1, ∃ x t, ln = .ins x t ∧ x.hooked = false) ∧ R.L.drop j = ls1 ++ T ∧
      Arm.r .PC s = R.pcOf j ∧ execLines (R.envOf j) ls1 s = some s' ∧
      InterOk (R.envOf j) ls1 s ∧ (∃ m' w'', c'' = .run ⟨b, its, m', w''⟩) ∧
      MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c'' ∧ Q R s' c'' := by
  have hOS' : ∀ env, OperandsSoundCtlAtI R.F R.FK
      (fun i' => ∃ regs, allocs = regs.map Loc.reg ∧ i.assign regs = .ok i') (execMInst R.ctx env)
      R.sem i .next s := fun env => (((hOS env).at (fun _ => RL.FK_F) s).toI _).v R.gv
  obtain ⟨j, vb0, items, pre, code, ls, ps1, ps2, T, hvb0, hit, hsplit, hchk, hcode, hls, htr, hdrop,
    hpc, hst⟩ := hq
  rw [hvb] at hvb0
  cases hvb0
  obtain ⟨c1, c2, hc1, hc2, rfl⟩ := itemsCode_cons hcode
  obtain ⟨regs, i0, i', rfl, hi0, hasg, hc1'⟩ := itemCode_op hc1
  rw [hi] at hi0
  cases hi0
  obtain ⟨c, wh, i2, ops2, hi2, hops2, hstat, hchk'⟩ := op_checked hchk
  rw [hi] at hi2
  cases hi2
  rw [hops] at hops2
  cases hops2
  have hm : ∀ r, r.allocatable = true → m (.reg r) = regVal s r := fun r hr =>
    hst.store (.reg r) (fun r' e => by cases e; exact hr) trivial
  obtain ⟨s', m2, hex, hW, hK, hc2', hr2, hl2⟩ := operandsSound_stepI (hOS' (R.envOf j)) hops hstat
    hasg ⟨regs, rfl, hasg⟩ hm hst.world hst.align hst.err hsem hlen
  obtain ⟨⟨ls1, hl1, hins, hpl, hint⟩, hna, hnr⟩ := hL regs i' hasg
  rcases hc1' with ⟨rfl, -, -⟩ | ⟨ds, rfl, -⟩ | ⟨us, rfl, -⟩
  rotate_left
  · exact absurd rfl (hna ds)
  · exact absurd rfl (hnr us)
  obtain ⟨ls1', ls2, psm, h1, h2, rfl⟩ := codeLinesE_append _ _ _ _ _ hls
  have h1' : codeLinesE R.ctx R.af [AInst.inst i'] ps1 = .ok (ls1, ps1) := by
    simp [codeLinesE, ainstLines, hl1 ps1, bind, Except.bind, pure, Except.pure]
  rw [h1'] at h1
  simp only [Except.ok.injEq, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  have hZ : ∀ n, (ls2 ++ nxtOf R.af b)[1]? ≠ some (.label (.trap n)) := by
    intro n e
    have hm := List.mem_of_getElem? e
    rcases List.mem_append.1 hm with hm | hm
    · exact codeLinesE_noTrap _ _ _ _ h2 _ hm n rfl
    · simp only [nxtOf] at hm
      split at hm <;> simp at hm
  have hdrop' : R.L.drop j = ls1 ++ (relaxLines R.far (ftList (ls2 ++ nxtOf R.af b)) ++ T) := by
    rw [hdrop, List.append_assoc, ftR_plain_append _ _ _ hpl hZ, List.append_assoc]
  have hrun : execLines (R.envOf j) ls1 s = some s' := by
    simp only [execMInst, hl1] at hex; exact hex
  have hins' : ∀ ln ∈ ls1, ∃ i t, ln = .ins i t := fun ln h => by
    obtain ⟨i, t, e, -⟩ := hins ln h; exact ⟨i, t, e⟩
  have hpc' : Arm.r .PC s' = R.pcOf (j + ls1.length) := by
    rw [execLines_pc hrun, hpc]
    simp only [RL.pcOf, RL.L]
    rw [lineOffset_drop_ins (by simpa [RL.L] using hdrop') hins', BitVec.add_assoc]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_add]
  refine ⟨j, regs, i', ls1, _, s', _, rfl, hasg, hl1, hins, hdrop', hpc, hrun,
    hint _ _ _ hst.err hrun, ⟨_, _, rfl⟩,
    MStep.op hvb hi hops hsz hsem hlen (HavocOuts.refl _ _ _) hc2' (MNext.next hk), ?_⟩
  have hfr := R.frameOkK hR
  refine ⟨j + ls1.length, vb, items, pre ++ [.op k (regs.map Loc.reg)], c2, ls2, ps1, ps2, T, hvb,
    hit, by rw [hsplit]; simp, hchk', hc2, h2, htr, ?_, hpc', ?_⟩
  · rw [← List.drop_drop, hdrop', List.drop_left]
  · have hsp' : spOf s' = R.spB := hK.1.trans hst.sp
    have herr' : Arm.r .ERR s' = .None := by
      rw [hW.1 .ERR (by simp [Masked]), hW'.1]
    refine ⟨fun l hl hL => ?_, hW, herr', ?_, hsp', align_of_sp (by rw [hsp', hst.sp]) hst.align,
      fun hframe => ?_, code_keep hR.prog0 hst.code fun a ha => hK.2.1 a (.inl (.inr (.inr ha))),
      fun a ha => (hK.2.1 a (.inr ha)).trans (hst.gkeep a ha), fun hf => hK.2.2.trans (hst.fp hf)⟩
    · cases l with
      | reg r => exact hr2 r (hl r rfl)
      | stack k' c =>
        rw [hl2 _ (fun r h => by cases h), hst.store _ hl hL,
          locVal_frame_keep hfr hst.sp hK hL (fun r h => by cases h)]
      | save r =>
        rw [hl2 _ (fun r h => by cases h), hst.store _ hl hL,
          locVal_frame_keep hfr hst.sp hK hL (fun r h => by cases h)]
    · rw [hW.2.2, hW'.2, ← hst.world.2.2, hst.prog]
    · rw [← hst.fplr hframe]
      exact read_mem_bytes_congr _ _ (fun k hk => hK.2.1 _ (fplr_inF hR hframe k hk))

end Concurrency.ArmAllocThread
