import FV.E2E.RegLevelFrame
import FV.E2E.RegLevelGoodXN

/-!
# The prologue and the return on the machine with no call state (SEM1 #537, step 2k)

`RegLevelFrame`'s `iterN_steps`, `q_init`, `ret_machine` with `RL.GoodXN`
(docs/plans/uninit.md §5.5): the prologue, epilogue and `ret` lines are unhooked, so no state of
those runs is a call state.
-/

namespace Backend.Proof

open Backend E2E

/-- Straight-line lines at line `j` of the final code run as machine steps. -/
theorem iterN_stepsN {R : RL} (hR : R.Wf) {ls T : List Line} {j : Nat} {s s' : Arm.ArmState}
    (hdrop : R.L.drop j = ls ++ T)
    (hins : ∀ ln ∈ ls, ∃ x, ln = .ins x none ∧ x.hooked = false)
    (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j)
    (herr : Arm.r .ERR s = .None) (h : StepsOk (R.envOf j) ls s s') :
    iterN R.step ls.length s = s' ∧ Arm.r .PC s' = R.pcOf (j + ls.length) ∧
      (∀ i, 0 < i → i ≤ ls.length → R.Good (iterN R.step i s)) ∧
      ((∀ i t, Line.ins i t ∈ ls → i.tlsTail = false) → R.Good s →
        LinesReads (R.envOf j) ls s R.ReadOk → ∀ i < ls.length, R.GoodXN (iterN R.step i s)) := by
  have hat : ∀ k ln, ls[k]? = some ln → R.fa.lines.toList[j + k]? = some ln := by
    intro k ln hk
    have := congrArg (·[k]?) hdrop
    simp only [List.getElem?_drop, RL.L] at this
    rw [this, List.getElem?_append_left (List.getElem?_eq_some_iff.1 hk).1]
    exact hk
  have hins' : ∀ ln ∈ ls, ∃ i t, ln = .ins i t := fun ln h => by
    obtain ⟨x, e, -⟩ := hins ln h; exact ⟨x, none, e⟩
  have hhook : ∀ i t, Line.ins i t ∈ ls → i.hooked = false := fun i t hm => by
    obtain ⟨x, e, hh⟩ := hins _ hm; cases e; exact hh
  have hrun := h.exec
  refine ⟨iterN_execLines hR.layout hR.lm hR.fit ls j s s' hat hhook
      hprog (by rw [hpc]; rfl) herr (stepsOk_interOk h herr) hrun, ?_,
    R.good_execLines hR hat hhook hprog hpc herr (stepsOk_interOk h herr) hrun,
    fun htail h0 hrd => RL.goodXN_execLinesG hR hat hhook htail hprog hpc herr h0
      (stepsOk_interOk h herr) hrun hrd⟩
  rw [execLines_pc hrun, hpc]
  simp only [RL.pcOf, RL.L]
  rw [lineOffset_drop_ins (by simpa [RL.L] using hdrop) hins', BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add]

/-- `iterN_proRun` with `RL.GoodXN` (#581): the prologue's lines are unhooked, so no state of its
run is a call state. -/
theorem iterN_proRunN {R : RL} (hR : R.Wf) {saves : List Reg} {size : Nat} {calls : Bool}
    {T : List Line} {j : Nat} {s s' : Arm.ArmState}
    (hdrop : R.L.drop j = prologueLines saves size calls ++ T)
    (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j)
    (herr : Arm.r .ERR s = .None) (h : ProRun (R.envOf j) saves size calls s s') :
    iterN R.step (prologueSteps saves size calls) s = s' ∧
      Arm.r .PC s' = R.pcOf (j + (prologueLines saves size calls).length) ∧
      (∀ i, 0 < i → i ≤ prologueSteps saves size calls → R.Good (iterN R.step i s)) ∧
      (R.Good s → ∀ i < prologueSteps saves size calls, R.GoodXN (iterN R.step i s)) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := iterN_proRun hR hdrop hprog hpc herr h
  refine ⟨h1, h2, h3, fun h0 i hi => ⟨h4 h0 i hi, ?_⟩⟩
  obtain ⟨k, hk, e⟩ := h5 i hi
  obtain ⟨x, ex, hx, -⟩ := prologueLines_ins _ _ _ (List.getElem_mem hk)
  refine RL.noCallAt_of_line hR (j := j + k) ?_ e hx
  have := congrArg (·[k]?) hdrop
  simp only [List.getElem?_drop] at this
  rw [this, List.getElem?_append_left hk, List.getElem?_eq_getElem hk, ex]

/-- **After the prologue**: the machine is at the entry configuration of the allocated code
(store = the machine's locations, world = any body-entry world `w₀`), `AInv` holds, and every
field but the pc, x16, x17, x29, `sp` and the flags is as at entry. (#581: x17 and the flags
are new exceptions: Cranelift's stack-probe loop sets them.) -/
theorem q_initN {R : RL} (hR : R.Wf) {ra : BitVec 64} (hent : AbiCall R.fb R.base ra R.s0)
    {w₀ : Arm.ArmState} (hbe : BodyEntryW R.F R.vc.EntryArg R.af R.s0 w₀) :
    ∃ n, (∀ i < n, R.GoodXN (iterN R.step i R.s0)) ∧
      Q R (iterN R.step n R.s0) (MConf.init R.rf (locVal R.fr (iterN R.step n R.s0)) w₀) ∧
      AInv R (MConf.init R.rf (locVal R.fr (iterN R.step n R.s0)) w₀) ∧
      ∀ f, f ≠ .PC → f ≠ .GPR 29#5 → f ≠ .GPR 31#5 → f ≠ .GPR 16#5 → f ≠ .GPR 17#5 →
        (∀ fl, f ≠ .FLAG fl) → Arm.r f (iterN R.step n R.s0) = Arm.r f R.s0 := by
  obtain ⟨hframe, hfs, -, hsv, -, hcb, -, -, hdrop0⟩ := RL.frame_facts hR
  have hst0 := hR.stack.frame
  have hsp0 := (spv R.s0).isLt
  have hs : R.af.frameSize < 2 ^ 64 := by have := hst0.1; omega
  obtain ⟨vb, items, code, ls, ps1, ps2, T, hvb, hit, hcode, hls, htr, hj0, hdrop⟩ := entry_block hR
  obtain ⟨s', hsteps, hsp', hfp', ho', hfl', hm', -, -⟩ :=
    prologue_ok (calls := R.af.isCaller) (R.envOf 1) hs hsv (by rw [hfs]; exact hcb) R.s0 hent.spAligned
  have hpc1 : Arm.r .PC R.s0 = R.pcOf 1 := by
    rw [hent.pc]
    simp only [RL.pcOf, RL.L] at hj0 ⊢
    rw [lineOffset_succ _ _ _ hj0]
    simp [lineOffset, Line.size]
  obtain ⟨hiter, hpc', -, hgx⟩ := iterN_proRunN hR hdrop hent.program hpc1 hent.err hsteps
  obtain ⟨herr', hprog'⟩ := hsteps.err
  refine ⟨prologueSteps R.af.saves R.af.frameSize R.af.isCaller,
    hgx (.inl (by rw [hent.pc]; exact RL.not_postCall_base hR hent.fits)), ?_⟩
  have hsP : R.sP = s' := hiter
  rw [hiter]
  have hspB : spOf s' = R.spB := by
    rw [hsp', RL.spB, hdrop0, ← hfs]; exact sp_sub16 _ _
  have htopB : R.topB.toNat = (spv R.s0).toNat - R.topN := by
    simp only [RL.topB, RL.topN]
    have := hst0.1
    rw [BitVec.toNat_sub_of_le] <;>
      simp only [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 16 + clobberBytes R.af.saves < 2 ^ 64 by omega)]
    omega
  have hk64 : ∀ k < R.topN, (R.topB + BitVec.ofNat 64 k).toNat = (spv R.s0).toNat - R.topN + k := by
    intro k hk
    simp only [RL.topN] at hk
    have := hst0.1
    have hkl : k < 2 ^ 64 := by rw [hfs] at this; omega
    rw [BitVec.toNat_add, htopB, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) hkl]
    simp only [RL.topN]
    rw [hfs] at this
    omega
  -- the frame top (and the bytes the stack probes zeroed)
  have hslot : ∀ a, (∀ k < R.topN, a ≠ R.topB + BitVec.ofNat 64 k) → s'.mem a = probeMem R.af R.s0 a :=
    fun a ha => by
      rw [hm' a ha]
      show _ = (if probeHit R.af (spv R.s0) a then 0#8 else R.s0.mem a)
      rw [show probeHit R.af (spv R.s0) a =
        probeHitN (probeCount (probeTotal R.af.frameSize R.af.isCaller)) (spOf R.s0) a by
          simp only [probeHit, hframe, Bool.true_and]; rfl]
  have hmemF : ∀ a, ¬ R.F a → s'.mem a = w₀.mem a := by
    intro a ha
    rw [hslot a (fun k hk e => ha (e ▸ RL.FK_F (fplr_inF hR hframe k hk))), hbe.mem a ha]
  have hcode' : ∀ a, CodeAddr R.s0 a → s'.mem a = R.s0.mem a := by
    intro a ha
    rw [← probeMem_of_not (probeHit_noCode hR.stack ha)]
    apply hslot
    intro k hk e
    have h2 := hst0.2 a ha
    rw [e] at h2
    have hk' := hk64 k hk
    have := hst0.1
    simp only [RL.topN] at hk hk'
    have hin : (spv R.s0 - BitVec.ofNat 64 (R.af.frameSize + 16)).toNat =
        (spv R.s0).toNat - (R.af.frameSize + 16) := by
      have hm : (R.af.frameSize + 16) % 2 ^ 64 = R.af.frameSize + 16 := Nat.mod_eq_of_lt (by omega)
      rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat, hm]; omega),
        BitVec.toNat_ofNat, hm]
    rw [BitVec.toNat_sub, hk', hin] at h2
    have e2 : (2 ^ 64 - ((spv R.s0).toNat - (R.af.frameSize + 16)) +
        ((spv R.s0).toNat - (16 + clobberBytes R.af.saves) + k)) % 2 ^ 64 =
        (spv R.s0).toNat - (16 + clobberBytes R.af.saves) + k -
          ((spv R.s0).toNat - (R.af.frameSize + 16)) := by
      rw [show 2 ^ 64 - ((spv R.s0).toNat - (R.af.frameSize + 16)) +
          ((spv R.s0).toNat - (16 + clobberBytes R.af.saves) + k) =
        ((spv R.s0).toNat - (16 + clobberBytes R.af.saves) + k -
          ((spv R.s0).toNat - (R.af.frameSize + 16))) + 2 ^ 64 by rw [hfs] at this ⊢; omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by rw [hfs] at this ⊢; omega)]
    rw [e2] at h2
    rw [hfs] at this h2
    omega
  have hfield : ∀ f, f ≠ .PC → f ≠ .GPR 29#5 → f ≠ .GPR 31#5 → f ≠ .GPR 16#5 → f ≠ .GPR 17#5 →
      (∀ fl, f ≠ .FLAG fl) → Arm.r f s' = Arm.r f R.s0 := ho'
  -- the kept addresses are not the frame top
  have hgk : ∀ a, R.G a → s'.mem a = R.s0.mem a := by
    intro a ha
    rw [← probeMem_of_not (hR.gprobe a ha)]
    apply hslot
    intro k hk e
    apply hR.gfree a ha
    rw [e, hdrop0]
    have := hst0.1
    have hk' := hk64 k hk
    simp only [RL.topN] at hk hk'
    simp only [StackBelow, hk']
    rw [hfs] at this
    constructor <;> omega
  refine ⟨?_, ?_, hfield⟩
  · have hitems : R.rf.blocks[0]! = items := by simp [getElem!_def, hit]
    simp only [MConf.init, hitems]
    refine ⟨1 + (prologueLines R.af.saves R.af.frameSize R.af.isCaller).length, vb, items, [], code, ls, ps1, ps2, T, hvb,
      hit, rfl, itemsChecked_block hR hvb hit, hcode, hls, htr, ?_, hpc', ?_⟩
    · rw [← List.drop_drop, hdrop, List.drop_left]
    · refine ⟨fun l _ _ => rfl, ⟨fun f hf => ?_, hmemF, ?_⟩, by rw [herr', hent.err], by rw [hprog', hent.program],
        hspB, ?_, fun _ => ?_, code_keep hR.prog0 hent.code hcode', hgk, fun _ => hfp'⟩
      · by_cases hfl : ∃ fl, f = .FLAG fl
        · obtain ⟨fl, rfl⟩ := hfl
          rw [hfl' fl, hbe.other _ hf (by simp) (by simp)]
          simp [probeR, probeFlag, hframe]
        have hfl : ∀ fl, f ≠ .FLAG fl := fun fl e => hfl ⟨fl, e⟩
        by_cases h29 : f = .GPR 29#5
        · subst h29
          have := hbe.fp
          simp only [hframe, ite_true, xreg] at this hfp'
          rw [hfp', this]; rfl
        by_cases h31 : f = .GPR 31#5
        · subst h31
          have := hbe.sp
          simp only [spv] at this
          rw [this]; exact hspB
        have h16 : f ≠ .GPR 16#5 := by rintro rfl; exact hf (by simp [Masked])
        have h17 : f ≠ .GPR 17#5 := by rintro rfl; exact hf (by simp [Masked])
        have hpc : f ≠ .PC := by rintro rfl; exact hf trivial
        rw [hfield f hpc h29 h31 h16 h17 hfl, hbe.other f hf h29 h31, probeR_of_ne hfl]
      · rw [hprog', hbe.program]
      · rw [checkSP_iff, hspB]
        simp only [RL.spB, hdrop0]
        have := hst0.1
        have ha := hent.spAligned
        rw [hfs] at this
        have hm : (R.fr.total + 16) % 2 ^ 64 = R.fr.total + 16 := Nat.mod_eq_of_lt (by omega)
        rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat, hm]; simp only [spv] at *; omega),
          BitVec.toNat_ofNat, hm]
        have : R.fr.total % 16 = 0 := (RL.frame_facts hR).2.2.2.2.2.2.1
        simp only [spv, spOf] at *
        omega
      · simp only [RL.topImg, hsP]
  · intro _ _ r hr
    show regVal s' r = regVal w₀ r
    rw [hbe.args r hr]
    obtain ⟨vb', ds, hvb', hi', v, hv⟩ := hr
    have hr := ((ctlCheck_args (lowerRFunc_ok hR.alloc).2.2 hvb' hi').2.2 _ hv).2
    cases r with
    | x n =>
      simp only [Reg.isArgReg, decide_eq_true_eq] at hr
      have hne : ∀ m, 8 < m → m < 32 → Arm.StateField.GPR (rnum n) ≠ .GPR (BitVec.ofNat 5 m) :=
        fun m h1 h2 e => rnum_ne (a := n) (b := m) (by omega) h2 (by omega) (Arm.StateField.GPR.inj e)
      simp only [regVal]
      rw [hfield _ (by simp) (hne 29 (by omega) (by omega)) (hne 31 (by omega) (by omega))
        (hne 16 (by omega) (by omega)) (hne 17 (by omega) (by omega)) (by simp)]
    | v n =>
      simp only [regVal]
      rw [hfield _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)]
    | _ => simp [Reg.isArgReg] at hr


/-- **The return on the machine** (Cranelift's epilogue): from `QA` at a `Rets` item, the
epilogue and `ret` reach the return address with `sp` and x29 as at entry, the memory as at the
item, the allocatable registers but the saved ones as in the store, each saved register's low 64
bits (its slot) as at entry, and the returned values in their fixed registers. -/
theorem ret_machineN {R : RL} (hR : R.Wf) {ra : BitVec 64} (hent : AbiCall R.fb R.base ra R.s0)
    {s : Arm.ArmState} {b k : Nat} {allocs : Array Loc} {its : List RItem} {m : Loc → CV}
    {w : Arm.ArmState} (hqa : QA R s (.run ⟨b, .op k allocs :: its, m, w⟩)) {vb : VBlock}
    {us : List (Reg × Reg)} (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some (.rets us)) :
    ∃ n, (∀ i < n, R.GoodXN (iterN R.step i s)) ∧
      Arm.r .PC (iterN R.step n s) = ra ∧ Arm.r .ERR (iterN R.step n s) = .None ∧
      spv (iterN R.step n s) = spv R.s0 ∧ xreg 29 (iterN R.step n s) = xreg 29 R.s0 ∧
      (∀ r, r.allocatable = true → r ∉ R.af.saves → regVal (iterN R.step n s) r = m (.reg r)) ∧
      (∀ r ∈ R.af.saves, slotVal (iterN R.step n s) r = slotVal R.s0 r) ∧
      (iterN R.step n s).mem = s.mem ∧
      (∀ f, ¬ Masked f → f ≠ .GPR 29#5 → f ≠ .GPR 31#5 → Arm.r f (iterN R.step n s) = Arm.r f s) ∧
      (iterN R.step n s).program = s.program ∧
      ∀ ops, (MInst.rets us).operands = .ok ops → ∀ (j : Nat) (v p : Reg) (x : CV), us[j]? = some (v, p) →
        ((((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)))[j]? = some x →
        regVal (iterN R.step n s) p = x := by
  have hframe := lowerRFunc_frame hR.alloc
  have hck := (lowerRFunc_ok hR.alloc).2.2
  obtain ⟨-, hfs, hsav, hsv, -, hcb, -, -, -⟩ := RL.frame_facts hR
  have hst0 := hR.stack.frame
  have hsp0 := (spv R.s0).isLt
  have hs : R.af.frameSize < 2 ^ 64 := by have := hst0.1; omega
  have hcb' : clobberBytes R.af.saves ≤ R.af.frameSize := by rw [hfs]; exact hcb
  -- the machine's store `mt`: `m` but at the restored registers `D`
  obtain ⟨mt, D, hq, hmD, hDs⟩ : ∃ (mt : Loc → CV) (D : List Reg), Q R s (.run ⟨b, .op k allocs :: its, mt, w⟩) ∧
      (∀ l, (∀ r ∈ D, l ≠ .reg r) → m l = mt l) ∧ ∀ r ∈ D, r ∈ R.af.saves := by
    unfold QA at hqa
    rcases hqa with ⟨hq, -⟩ | h
    · refine ⟨m, [], hq, fun _ _ => rfl, ?_⟩
      simp
    · simp only [RetTail, TailOk] at h
      obtain ⟨mt, D, hq, hm, _, _, _, _, _, _, -, -, -, htl⟩ := h
      exact ⟨mt, D, hq, hm, fun r hr => by rw [hsav]; exact (retTailOk_prefix htl).subset hr⟩
  obtain ⟨j0, items, pre, regs, i', c1, c2, ls1, ls2, ps1, psm, ps2, T, cc, wh, ops, rfl, hit, hsplit,
    hasg, hc1', hops, hstat, hchk', hc2, h1, h2, htr, hdrop, hpc, hst⟩ := q_op hq hvb hi
  obtain ⟨us', rfl⟩ := assign_rets hasg
  obtain rfl : c1 = [.epilogueRet] := by
    rcases hc1' with ⟨-, -, h⟩ | ⟨_, h, -⟩ | ⟨_, -, h⟩
    · exact absurd rfl (h us')
    · cases h
    · exact h
  simp only [codeLinesE, ainstLines, hframe, ite_true, bind, Except.bind, pure, Except.pure,
    List.append_nil, Except.ok.injEq, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  rw [epilogueLines_epi] at hdrop
  have hpl : ∀ ln ∈ epiLines R.af.saves R.af.frameSize ++ [Line.ins .ret none], ln.plain = true := by
    intro ln hln
    rcases List.mem_append.1 hln with hln | hln
    · obtain ⟨_, _, _, hp, -⟩ := epiLines_ins _ _ ln hln; exact hp
    · simp only [List.mem_singleton] at hln; subst hln; rfl
  rw [ftR_plain_append _ _ _ hpl (noTrap_next h2)] at hdrop
  have hdrop' : R.L.drop j0 = epiLines R.af.saves R.af.frameSize ++
      (.ins .ret none :: (relaxLines R.far (ftList (ls2 ++ nxtOf R.af b)) ++ T)) := by
    rw [hdrop]; simp
  -- `sp + size - clobberBytes` is the bottom of the clobber area, `sp + size` the fp/lr slot
  have hdrop0 : frameDrop R.af = R.af.frameSize + 16 := by simp [frameDrop, hframe]
  have hslot : spOf s + BitVec.ofNat 64 R.af.frameSize = spv R.s0 - 16#64 := by
    rw [hst.sp, RL.spB, hdrop0, BitVec.ofNat_add]; bv_omega
  have hB : spOf s + BitVec.ofNat 64 (R.af.frameSize - clobberBytes R.af.saves) = R.topB := by
    obtain ⟨d, hd⟩ : ∃ d, R.af.frameSize = d + clobberBytes R.af.saves :=
      ⟨_, (Nat.sub_add_cancel hcb').symm⟩
    rw [hst.sp, RL.spB, RL.topB, RL.topN, hdrop0, hd, Nat.add_sub_cancel,
      show d + clobberBytes R.af.saves + 16 = d + (16 + clobberBytes R.af.saves) by omega,
      BitVec.ofNat_add, BitVec.ofNat_add]
    bv_omega
  have htopcb : R.topB + BitVec.ofNat 64 (clobberBytes R.af.saves) = spv R.s0 - 16#64 := by
    rw [RL.topB, RL.topN, BitVec.ofNat_add]; bv_omega
  have hal : (spOf s + BitVec.ofNat 64 (R.af.frameSize - clobberBytes R.af.saves)).toNat % 16 = 0 := by
    rw [hB]
    have := hent.spAligned
    have := clobberBytes_mod R.af.saves
    have h16 : 16 + clobberBytes R.af.saves ≤ (spv R.s0).toNat := by have := hst0.1; omega
    have hm : (16 + clobberBytes R.af.saves) % 2 ^ 64 = 16 + clobberBytes R.af.saves :=
      Nat.mod_eq_of_lt (by omega)
    simp only [RL.topB, RL.topN]
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat, hm]; exact h16),
      BitVec.toNat_ofNat, hm]
    omega
  obtain ⟨s1, hsteps, hsp1, hx29, hx30, ho1, hm1, hpop⟩ :=
    epilogue_ok (R.envOf j0) hs hsv hcb' s hal
  -- the reads: the clobber area and fp/lr, no kept address
  have hrdE : LinesReads (R.envOf j0) (epiLines R.af.saves R.af.frameSize) s R.ReadOk :=
    epilogue_reads (R.envOf j0) hs hsv hcb' s hal fun k hk => by
      rw [hB]; exact .inl (RL.top_notG hR k (by simp only [RL.topN]; omega))
  obtain ⟨hiter, hpc1, hgood, hgx⟩ := iterN_stepsN hR hdrop'
    (fun ln h => by obtain ⟨x, e, hh, -, -⟩ := epiLines_ins _ _ ln h; exact ⟨x, e, hh⟩)
    hst.prog hpc hst.err hsteps
  obtain ⟨herr1, hprog1⟩ := hsteps.err
  -- the `ret`
  have hj : R.fa.lines.toList[j0 + (epiLines R.af.saves R.af.frameSize).length]? =
      some (Line.ins .ret none) := by
    have := congrArg (·[(epiLines R.af.saves R.af.frameSize).length]?) hdrop'
    simpa [List.getElem?_drop, RL.L] using this
  obtain ⟨a, ha, hstep⟩ := armStepX_ins (X := R.X) (H := R.H) hR.layout hR.lm hR.fit hj rfl
    (by rw [hprog1, hst.prog]) hpc1 (by rw [herr1, hst.err])
  obtain ⟨a', ha', he'⟩ := exec_ret ⟨lineOffset R.fa.lines.toList
    (j0 + (epiLines R.af.saves R.af.frameSize).length), (R.lm[·]?)⟩ s1
  rw [ha] at ha'; cases ha'
  have hfin : iterN R.step ((epiLines R.af.saves R.af.frameSize).length + 1) s =
      Arm.w .PC (xreg 30 s1) s1 := by
    rw [iterN_one_succ, hiter]; exact hstep.trans he'
  -- the top of the frame as the prologue left it
  have hbytes := read_mem_bytes_bytes R.topN R.topB s R.sP (hst.fplr hframe)
  obtain ⟨sP, -, hsP, hP16, hPsl⟩ := RL.sP_steps hR hent
  rw [hsP] at hbytes
  have hfplr : Arm.read_mem_bytes 16 (spOf s + BitVec.ofNat 64 R.af.frameSize) s =
      xreg 30 R.s0 ++ xreg 29 R.s0 := by
    rw [hslot, ← htopcb, read_sub (n := 16) (o := clobberBytes R.af.saves) hbytes
      (by simp only [RL.topN]; omega), htopcb]
    exact hP16
  have hpopS : ∀ r ∈ R.af.saves, slotVal s1 r = slotVal R.s0 r := by
    intro r hr
    have hv := hpop r hr
    rw [hB, read_sub (n := 8) (o := clobberOff R.af.saves r) hbytes
      (by have := clobberOff_le hsv hr; simp only [RL.topN]; omega), hPsl r hr] at hv
    refine slotVal_of_popVal ?_ hv
    rcases calleeSaved_cases (hsv.1 r hr) with ⟨n, rfl, -⟩ | ⟨n, rfl, -⟩
    · exact .inl ⟨n, rfl⟩
    · exact .inr ⟨n, rfl⟩
  have hregs : ∀ r, r.allocatable = true → r ∉ R.af.saves →
      regVal (Arm.w .PC (xreg 30 s1) s1) r = regVal s r := by
    intro r hr hns
    rw [regVal_w (by rcases allocatable_cases hr with ⟨n, rfl, _⟩ | ⟨n, rfl, _⟩ <;> simp [Reg.field])]
    have hfs' : ∀ f, r.field = some f → ∀ r' ∈ R.af.saves, r'.field ≠ some f :=
      fun f hf r' hr' => field_ne_of_ne hr (hsv.1 r' hr') (fun e => hns (e ▸ hr')) f hf
    rcases allocatable_cases hr with ⟨n, rfl, hn⟩ | ⟨n, rfl, hn⟩
    · have hne : ∀ q, q < 32 → q ≠ n → Arm.StateField.GPR (rnum n) ≠ .GPR (BitVec.ofNat 5 q) :=
        fun q h1 h2 e => rnum_ne (a := n) (b := q) (by omega) h1 (Ne.symm h2) (Arm.StateField.GPR.inj e)
      simp only [regVal]
      rw [ho1 _ (by simp) (hne 29 (by omega) (by omega)) (hne 30 (by omega) (by omega))
        (hne 31 (by omega) (by omega)) (hne 16 (by omega) (by omega)) (hfs' _ rfl)]
    · simp only [regVal]
      rw [ho1 _ (by simp) (by simp) (by simp) (by simp) (by simp) (hfs' _ rfl)]
  refine ⟨(epiLines R.af.saves R.af.frameSize).length + 1, fun i hi => ?_, ?_⟩
  · rcases Nat.lt_or_ge i (epiLines R.af.saves R.af.frameSize).length with hi1 | hi1
    · refine hgx (fun x t h => ?_) (RL.good_of_sp hst.sp) hrdE i hi1
      obtain ⟨_, e, -, -, ht⟩ := epiLines_ins _ _ _ h
      cases e; exact ht
    · obtain rfl : i = (epiLines R.af.saves R.af.frameSize).length := by omega
      rw [hiter]
      refine RL.goodXN_ofIns hR hj hpc1 rfl rfl ?_ (by rw [herr1, hst.err]) (by rw [hprog1, hst.prog])
        (by
          rw [show R.step s1 = Arm.w .PC (xreg 30 s1) s1 from hstep.trans he']
          exact RL.nextOk_ret (by
            rw [Arm.r_of_w_same, hx30, hfplr, BitVec.extractLsb'_append_eq_left]))
        (RL.readsAt_noLoad hR hj hpc1 rfl)
      rw [← hiter]
      exact hgood _ (by simp only [epiLines, List.length_append, List.length_cons, List.length_nil]; omega)
        (Nat.le_refl _)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hfin]
  · rw [Arm.r_of_w_same, hx30, hfplr, BitVec.extractLsb'_append_eq_left, hent.lr]
  · rw [Arm.r_of_w_different (by simp), herr1, hst.err]
  · simp only [spv]
    rw [Arm.r_of_w_different (by simp)]
    show spOf s1 = spv R.s0
    rw [hsp1, hslot, BitVec.sub_add_cancel]
  · simp only [xreg]
    rw [Arm.r_of_w_different (by simp)]
    have := hx29
    simp only [xreg] at this
    rw [this, hfplr, BitVec.extractLsb'_append_eq_right]
    rfl
  · intro r hr hns
    rw [hregs r hr hns, hmD (.reg r) (fun r' hr' e => hns (by cases e; exact hDs _ hr')),
      hst.store (.reg r) (fun r' e => by cases e; exact hr) trivial]
    rfl
  · intro r hr
    rw [slotVal_w_pc]; exact hpopS r hr
  · rw [Arm.ArmState.mem_w_eq_mem, hm1]
  · intro f hf h29 h31
    have hpc : f ≠ .PC := by rintro rfl; exact hf trivial
    rw [Arm.r_of_w_different hpc]
    exact ho1 f hpc h29 (by rintro rfl; exact hf (by simp [Masked])) h31
      (by rintro rfl; exact hf (by simp [Masked]))
      (fun r' hr' e => hf (masked_of_calleeSaved (hsv.1 r' hr') e))
  · rw [Arm.w_program, hprog1]
  · intro ops' hops' j v p x hj hx
    have hpS : p ∉ R.af.saves := fun hp =>
      ctlCheck_rets_regs hck hvb hi _ (List.mem_of_getElem? hj) (hsv.1 p hp)
    obtain ⟨ns, rfl⟩ := ctlCheck_rets hck hvb hi
    rw [operands_retsC] at hops' hops
    cases hops'
    cases hops
    obtain ⟨hsz, hloc, -, -⟩ := checkStatic_facts hstat
    obtain ⟨rfl, q, hq, hq2⟩ := rets_usesC (fun q hq r hr => (hloc q hq).2 r hr) hsz j v p x hj hx
    have hal : p.allocatable = true := by
      have := (hloc q hq).1
      rw [hq2] at this
      simp only [CheckCtx.locOk, Bool.and_eq_true] at this
      exact this.2
    rw [hregs p hal hpS, hmD (.reg p) (fun r' hr' e => hpS (by cases e; exact hDs _ hr')),
      hst.store (.reg p) (fun r e => by cases e; exact hal) trivial]
    rfl
end Backend.Proof
