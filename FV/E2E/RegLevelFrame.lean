import FV.Backend.Proof.IselCtlTerm
import FV.E2E.RegLevelPush
import FV.E2E.RegLevelNext

/-!
# Prologue and epilogue on the machine (M6)
-/

namespace Backend.Proof

open Backend E2E


/-! ## Machine facts about the frame lines -/

theorem movkLines_mem {n : Nat} : ∀ {ks : List (Nat × Nat)} {ln : Line}, ln ∈ movkLines n ks →
    ∃ c i, ln = .ins (.movk true (.x n) ⟨c, i⟩) none
  | [], _, h => by simp [movkLines] at h
  | (c, i) :: ks, ln, h => by
    simp only [movkLines, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨c, i, rfl⟩
    · exact movkLines_mem h

/-- The frame lines are plain, unhooked instruction lines. -/
theorem spAdjLines_ins (sub : Bool) (size : Nat) :
    ∀ ln ∈ spAdjLines sub size, ∃ x, ln = .ins x none ∧ x.hooked = false ∧ ln.plain = true := by
  intro ln hln
  unfold spAdjLines at hln
  split at hln
  · simp at hln
  · split at hln
    · simp only [List.mem_singleton] at hln
      subst hln; exact ⟨_, rfl, rfl, by cases sub <;> rfl⟩
    · rw [List.mem_append, loadConst64_eq] at hln
      rcases hln with hln | hln
      · simp only [List.mem_cons] at hln
        rcases hln with rfl | hln
        · exact ⟨_, rfl, rfl, rfl⟩
        · obtain ⟨c, i, rfl⟩ := movkLines_mem hln
          exact ⟨_, rfl, rfl, rfl⟩
      · simp only [List.mem_singleton] at hln
        subst hln; exact ⟨_, rfl, rfl, by cases sub <;> rfl⟩


/-- The `sp` adjustment holds no instruction of the TLS tail. -/
theorem spAdjLines_tail (sub : Bool) (size : Nat) :
    ∀ i t, Line.ins i t ∈ spAdjLines sub size → i.tlsTail = false := by
  intro i t hln
  unfold spAdjLines at hln
  split at hln
  · simp at hln
  · split at hln
    · simp only [List.mem_singleton, Line.ins.injEq] at hln
      obtain ⟨rfl, -⟩ := hln; cases sub <;> rfl
    · rw [List.mem_append] at hln
      rcases hln with hln | hln
      · simpa [Line.tailFree] using loadConst64_tailFree _ _ _ hln
      · simp only [List.mem_singleton, Line.ins.injEq] at hln
        obtain ⟨rfl, -⟩ := hln; cases sub <;> rfl

theorem pushLines_ins (int : Bool) (rs : List Reg) :
    ∀ ln ∈ pushLines int rs, ∃ x, ln = .ins x none ∧ x.hooked = false ∧ ln.plain = true ∧
      x.loads = false ∧ x.tlsTail = false := by
  intro ln h
  obtain ⟨x, rfl, r, r', hx⟩ := pushLines_mem h
  rcases hx with rfl | rfl | rfl | rfl <;> exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩

theorem popLines_ins (int : Bool) (rs : List Reg) :
    ∀ ln ∈ popLines int rs, ∃ x, ln = .ins x none ∧ x.hooked = false ∧ ln.plain = true ∧
      x.tlsTail = false := by
  intro ln h
  obtain ⟨x, rfl, r, r', hx⟩ := popLines_mem h
  rcases hx with rfl | rfl | rfl | rfl <;> exact ⟨_, rfl, rfl, rfl, rfl⟩

/-- The stack probes are plain, unhooked instruction lines without loads (#581). -/
theorem probeLines_ins (total : Nat) :
    ∀ ln ∈ probeLines total, ∃ x, ln = .ins x none ∧ x.hooked = false ∧ ln.plain = true ∧
      x.loads = false ∧ x.tlsTail = false := by
  intro ln h
  rcases probeLines_mem h with rfl | rfl | ⟨_, rfl⟩ <;> exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩

theorem prologueLines_ins {calls : Bool} (saves : List Reg) (size : Nat) :
    ∀ ln ∈ prologueLines saves size calls, ∃ x, ln = .ins x none ∧ x.hooked = false ∧ ln.plain = true := by
  intro ln hln
  rw [prologueLines_eq] at hln
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hln
  rcases hln with (rfl | rfl) | h | h | h | h
  · exact ⟨_, rfl, rfl, rfl⟩
  · exact ⟨_, rfl, rfl, rfl⟩
  · obtain ⟨x, e, h1, h2, -⟩ := probeLines_ins _ _ h; exact ⟨x, e, h1, h2⟩
  · obtain ⟨x, e, h1, h2, -⟩ := pushLines_ins _ _ _ h; exact ⟨x, e, h1, h2⟩
  · obtain ⟨x, e, h1, h2, -⟩ := pushLines_ins _ _ _ h; exact ⟨x, e, h1, h2⟩
  · exact spAdjLines_ins true _ _ h

theorem prologueLines_noLoads {calls : Bool} (saves : List Reg) (size : Nat) :
    ∀ i t, Line.ins i t ∈ prologueLines saves size calls → i.loads = false := by
  intro i t hln
  rw [prologueLines_eq] at hln
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hln
  rcases hln with (h | h) | h | h | h | h
  · simp only [Line.ins.injEq] at h; obtain ⟨rfl, -⟩ := h; rfl
  · simp only [Line.ins.injEq] at h; obtain ⟨rfl, -⟩ := h; rfl
  · obtain ⟨x, e, -, -, hl, -⟩ := probeLines_ins _ _ h; cases e; exact hl
  · obtain ⟨x, e, -, -, hl, -⟩ := pushLines_ins _ _ _ h; cases e; exact hl
  · obtain ⟨x, e, -, -, hl, -⟩ := pushLines_ins _ _ _ h; cases e; exact hl
  · exact spAdjLines_noLoads true _ i t h

theorem prologueLines_tail {calls : Bool} (saves : List Reg) (size : Nat) :
    ∀ i t, Line.ins i t ∈ prologueLines saves size calls → i.tlsTail = false := by
  intro i t hln
  rw [prologueLines_eq] at hln
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hln
  rcases hln with (h | h) | h | h | h | h
  · simp only [Line.ins.injEq] at h; obtain ⟨rfl, -⟩ := h; rfl
  · simp only [Line.ins.injEq] at h; obtain ⟨rfl, -⟩ := h; rfl
  · obtain ⟨x, e, -, -, -, ht⟩ := probeLines_ins _ _ h; cases e; exact ht
  · obtain ⟨x, e, -, -, -, ht⟩ := pushLines_ins _ _ _ h; cases e; exact ht
  · obtain ⟨x, e, -, -, -, ht⟩ := pushLines_ins _ _ _ h; cases e; exact ht
  · exact spAdjLines_tail true _ i t h

/-- The epilogue's lines before the `ret`. -/
def epiLines (saves : List Reg) (size : Nat) : List Line :=
  spAdjLines false (size - clobberBytes saves) ++ (popLines false (savesFloat saves) ++
    (popLines true (savesInt saves) ++ [.ins (.ldp Reg.fp Reg.lr (.spPostIndexed 16))]))

theorem epiLines_ins (saves : List Reg) (size : Nat) :
    ∀ ln ∈ epiLines saves size, ∃ x, ln = .ins x none ∧ x.hooked = false ∧ ln.plain = true ∧
      x.tlsTail = false := by
  intro ln hln
  simp only [epiLines, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hln
  rcases hln with h | h | h | rfl
  · obtain ⟨x, e, h1, h2⟩ := spAdjLines_ins false _ _ h
    exact ⟨x, e, h1, h2, by subst e; exact spAdjLines_tail false _ x none h⟩
  · exact popLines_ins _ _ _ h
  · exact popLines_ins _ _ _ h
  · exact ⟨_, rfl, rfl, rfl, rfl⟩

theorem stepsOk_interOk {env : Env} {ls : List Line} {s s' : Arm.ArmState} (h : StepsOk env ls s s')
    (herr : Arm.r .ERR s = .None) : InterOk env ls s := by
  intro k _ _ s1 h1
  obtain ⟨s2, h2⟩ := StepsOk.take k h
  rw [h2.exec] at h1
  cases h1
  obtain ⟨e1, e2⟩ := h2.err
  exact ⟨e1.trans herr, e2⟩

/-- Straight-line lines at line `j` of the final code run as machine steps. -/
theorem iterN_steps {R : RL} (hR : R.Wf) {ls T : List Line} {j : Nat} {s s' : Arm.ArmState}
    (hdrop : R.L.drop j = ls ++ T)
    (hins : ∀ ln ∈ ls, ∃ x, ln = .ins x none ∧ x.hooked = false)
    (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j)
    (herr : Arm.r .ERR s = .None) (h : StepsOk (R.envOf j) ls s s') :
    iterN R.step ls.length s = s' ∧ Arm.r .PC s' = R.pcOf (j + ls.length) ∧
      (∀ i, 0 < i → i ≤ ls.length → R.Good (iterN R.step i s)) ∧
      ((∀ i t, Line.ins i t ∈ ls → i.tlsTail = false) → R.Good s →
        LinesReads (R.envOf j) ls s R.ReadOk → ∀ i < ls.length, R.GoodX (iterN R.step i s)) := by
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
    fun htail h0 hrd => R.goodX_execLinesG hR hat hhook htail hprog hpc herr h0
      (stepsOk_interOk h herr) hrun hrd⟩
  rw [execLines_pc hrun, hpc]
  simp only [RL.pcOf, RL.L]
  rw [lineOffset_drop_ins (by simpa [RL.L] using hdrop) hins', BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add]

/-- **The entry address is no return address of a call of the function**: `base + off + 4 =
base` only if the code fills the address space (`AbiCall.fits`), but the frame below the entry
`sp` holds no code (`StackAvail`). -/
theorem RL.not_postCall_base {R : RL} (hR : R.Wf)
    (hfits : R.base.toNat + 4 * R.fb.words.size ≤ 2 ^ 64) : ¬ PostCall R.fa R.base R.base := by
  rintro ⟨q, ⟨j', i', t', hj', -, rfl⟩, he⟩
  have hsum := layout_sum hR.layout
  have hl2 := lineOffset_le_size R.fa.lines.toList (j' + 1)
  have hs2 := lineOffset_succ R.fa.lines.toList j' _ hj'
  simp only [Line.size] at hs2
  rw [BitVec.add_assoc] at he
  have he' : R.base + (BitVec.ofNat 64 (lineOffset R.fa.lines.toList j') + 4#64) = R.base + 0#64 := by
    rw [BitVec.add_zero]; exact he.symm
  have he2 := congrArg BitVec.toNat ((BitVec.add_right_inj _).mp he')
  have h4 : (4 : BitVec 64).toNat = 4 := rfl
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, h4] at he2
  have hfull : lineOffset R.fa.lines.toList j' + 4 = 2 ^ 64 := by
    rw [hs2, hsum] at hl2
    rw [Nat.mod_eq_of_lt (a := lineOffset R.fa.lines.toList j') (by omega)] at he2
    omega
  have hb0 : R.base = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [hs2, hsum] at hl2
    simp only [BitVec.toNat_ofNat]
    omega
  -- every address is a code address, the bottom of the frame too
  have hroom := hR.stack.frame
  let a := spv R.s0 - BitVec.ofNat 64 (R.af.frameSize + 16)
  have hk : a.toNat / 4 < R.fb.words.size := by
    rw [hs2, hsum] at hl2
    have := a.isLt
    omega
  have hc := codeAddr_word hR.prog0 (Array.getElem?_eq_getElem hk) (i := a.toNat % 4) (by omega)
  have ha : R.base + BitVec.ofNat 64 (4 * (a.toNat / 4)) + BitVec.ofNat 64 (a.toNat % 4) = a := by
    rw [hb0]
    apply BitVec.eq_of_toNat_eq
    have := a.isLt
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [ha] at hc
  have := hroom.2 a hc
  simp only [a, BitVec.sub_self, BitVec.toNat_ofNat] at this
  omega

/-! ## The prologue on the machine: `Q` at the entry configuration -/

theorem noTrap_next {R : RL} {c2 : List AInst} {psm ps2 : PState} {ls2 : List Line} {b : Nat}
    (h2 : codeLinesE R.ctx R.af c2 psm = .ok (ls2, ps2)) :
    ∀ n, (ls2 ++ nxtOf R.af b)[1]? ≠ some (.label (.trap n)) := by
  intro n e
  have hm := List.mem_of_getElem? e
  rcases List.mem_append.1 hm with hm | hm
  · exact codeLinesE_noTrap _ _ _ _ h2 _ hm n rfl
  · simp only [nxtOf] at hm
    split at hm <;> simp at hm

/-- The entry block in the final lines: its label at line 0, then the prologue, then the
`fallthrough` of its items' lines. -/
theorem entry_block {R : RL} (hR : R.Wf) :
    ∃ vb items code ls ps1 ps2 T, R.vc.blocks[0]? = some vb ∧ R.rf.blocks[0]? = some items ∧
      itemsCode R.fr vb items.toList = .ok code ∧ codeLinesE R.ctx R.af code ps1 = .ok (ls, ps2) ∧
      ps2.traps.toList <+: R.psF.traps.toList ∧
      R.L[0]? = some (.label (.block vb.label)) ∧
      R.L.drop 1 = prologueLines R.af.saves R.af.frameSize R.af.isCaller ++ (relaxLines R.far (ftList (ls ++ nxtOf R.af 0)) ++ T) := by
  obtain ⟨c, ins, _, hc, -⟩ := hR.check
  have h0 : 0 < R.vc.blocks.size := Nat.pos_of_ne_zero hc.nonempty
  obtain ⟨vb, hvb⟩ : ∃ vb, R.vc.blocks[0]? = some vb := ⟨_, Array.getElem?_eq_getElem h0⟩
  obtain ⟨items, hit⟩ : ∃ items, R.rf.blocks[0]? = some items :=
    ⟨_, Array.getElem?_eq_getElem (by rw [hc.size]; exact h0)⟩
  have hframe := lowerRFunc_frame hR.alloc
  obtain ⟨⟨-, -, -, hbl⟩, -⟩ := lowerRFunc_ok hR.alloc
  obtain ⟨code, hcode, haf⟩ := hbl 0 vb items hvb hit
  obtain ⟨body, psF, hb, -, hblk⟩ := emit_block hR.emit
  obtain ⟨body', hb'⟩ := hR.psF
  have hk : R.ctx = ⟨R.fa.k, R.af.slotBase⟩ := rfl
  rw [hk, hb] at hb'
  simp only [Except.ok.injEq, Prod.mk.injEq] at hb'
  obtain ⟨-, rfl⟩ := hb'
  obtain ⟨j0, lsA, ps1, ps2, T, hj0, hdrop, hls, htr, hj⟩ := hblk 0 _ _ haf
  rw [show emitFar ⟨R.fa.k, R.af.slotBase⟩ R.af = R.far from rfl] at hdrop
  obtain rfl := hj rfl
  simp only [ite_true] at hls
  obtain ⟨ls1, ls2, psm, h1, h2, rfl⟩ := codeLinesE_append _ _ _ _ _ hls
  simp only [codeLinesE, ainstLines, hframe, ite_true, bind, Except.bind, pure, Except.pure,
    List.append_nil, Except.ok.injEq, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  refine ⟨vb, items, code, ls2, ps1, ps2, T, hvb, hit, hcode, h2, htr, hj0, ?_⟩
  show List.drop (0 + 1) R.fa.lines.toList = _
  rw [hdrop, List.append_assoc, ftR_plain_append _ _ _
    (fun ln h => by obtain ⟨_, _, _, hp⟩ := prologueLines_ins _ _ ln h; exact hp) (noTrap_next h2), List.append_assoc]

theorem sp_sub16 (x : BitVec 64) (n : Nat) :
    x - 16#64 - BitVec.ofNat 64 n = x - BitVec.ofNat 64 (n + 16) := by
  rw [BitVec.ofNat_add]; bv_omega

/-- **After the prologue**: the machine is at the entry configuration of the allocated code
(store = the machine's locations, world = any body-entry world `w₀`), `AInv` holds, and every
field but the pc, x16, x29 and `sp` is as at entry. -/
theorem q_init {R : RL} (hR : R.Wf) {ra : BitVec 64} (hent : AbiCall R.fb R.base ra R.s0)
    {w₀ : Arm.ArmState} (hbe : BodyEntryW R.F R.vc.EntryArg R.af R.s0 w₀) :
    ∃ n, (∀ i < n, R.GoodX (iterN R.step i R.s0)) ∧
      Q R (iterN R.step n R.s0) (MConf.init R.rf (locVal R.fr (iterN R.step n R.s0)) w₀) ∧
      AInv R (MConf.init R.rf (locVal R.fr (iterN R.step n R.s0)) w₀) ∧
      ∀ f, f ≠ .PC → f ≠ .GPR 29#5 → f ≠ .GPR 31#5 → f ≠ .GPR 16#5 →
        Arm.r f (iterN R.step n R.s0) = Arm.r f R.s0 := by
  obtain ⟨hframe, hfs, -, hsv, -, hcb, -, -, hdrop0⟩ := RL.frame_facts hR
  have hst0 := hR.stack.frame
  have hsp0 := (spv R.s0).isLt
  have hs : R.af.frameSize < 2 ^ 64 := by have := hst0.1; omega
  obtain ⟨vb, items, code, ls, ps1, ps2, T, hvb, hit, hcode, hls, htr, hj0, hdrop⟩ := entry_block hR
  obtain ⟨s', hsteps, hsp', hfp', ho', hm', -, -⟩ :=
    prologue_ok (calls := R.af.isCaller) (R.envOf 1) hs hsv (by rw [hfs]; exact hcb) R.s0 hent.spAligned
  have hpc1 : Arm.r .PC R.s0 = R.pcOf 1 := by
    rw [hent.pc]
    simp only [RL.pcOf, RL.L] at hj0 ⊢
    rw [lineOffset_succ _ _ _ hj0]
    simp [lineOffset, Line.size]
  obtain ⟨hiter, hpc', -, hgx⟩ := iterN_steps hR hdrop
    (fun ln h => by obtain ⟨x, e, hh, -⟩ := prologueLines_ins _ _ ln h; exact ⟨x, e, hh⟩)
    hent.program hpc1 hent.err hsteps
  obtain ⟨herr', hprog'⟩ := hsteps.err
  refine ⟨(prologueLines R.af.saves R.af.frameSize R.af.isCaller).length,
    hgx (prologueLines_tail _ _) (.inl (by rw [hent.pc]; exact RL.not_postCall_base hR hent.fits))
      (linesReads_noLoads (prologueLines_noLoads _ _)), ?_⟩
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
  have hfield : ∀ f, f ≠ .PC → f ≠ .GPR 29#5 → f ≠ .GPR 31#5 → f ≠ .GPR 16#5 →
      Arm.r f s' = Arm.r f R.s0 := ho'
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
      · by_cases h29 : f = .GPR 29#5
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
        have hpc : f ≠ .PC := by rintro rfl; exact hf trivial
        rw [hfield f hpc h29 h31 h16, hbe.other f hf h29 h31]
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
        (hne 16 (by omega) (by omega))]
    | v n =>
      simp only [regVal]
      rw [hfield _ (by simp) (by simp) (by simp) (by simp)]
    | _ => simp [Reg.isArgReg] at hr

/-! ## The return on the machine -/

/-- The register of an accepted `Args`/`Rets` pair is an argument register (x0–x8, v0–v7), so
no callee-saved one. -/
theorem argPairOk_not_calleeSaved {q : Reg × Reg} (h : argPairOk q = true) : q.2 ∉ calleeSaved := by
  intro hc
  have h' : q.2.isArgReg = true ∨ q.2.isFpArgReg = true := by
    simp only [argPairOk, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with ⟨-, h⟩ | ⟨-, h⟩
    · exact .inl h
    · exact .inr h
  rcases calleeSaved_cases hc with ⟨n, he, h1, h2⟩ | ⟨n, he, h1, h2⟩ <;> rw [he] at h' <;>
    simp [Reg.isArgReg, Reg.isFpArgReg] at h' <;> omega

theorem ctlCheck_rets {vc : VCode} {rf : RFunc} (h : ctlCheck vc rf = true) {b k : Nat}
    {vb : VBlock} {us : List (Reg × Reg)} (hvb : vc.blocks[b]? = some vb)
    (hi : vb.insts[k]? = some (.rets us)) : ∃ ns, us = argPairsC ns := by
  have h2 := ctlCheck_inst h hvb hi
  simp only [ctlInstOk, List.all_eq_true] at h2
  obtain ⟨ns, rfl, -⟩ := argPairsC_of (fun p hp => (argPairOk_facts (h2 p hp)).1)
  exact ⟨ns, rfl⟩

/-- The registers a `Rets` returns in are no callee-saved ones. -/
theorem ctlCheck_rets_regs {vc : VCode} {rf : RFunc} (h : ctlCheck vc rf = true) {b k : Nat}
    {vb : VBlock} {us : List (Reg × Reg)} (hvb : vc.blocks[b]? = some vb)
    (hi : vb.insts[k]? = some (.rets us)) : ∀ q ∈ us, q.2 ∉ calleeSaved := by
  have h2 := ctlCheck_inst h hvb hi
  simp only [ctlInstOk, List.all_eq_true] at h2
  exact fun q hq => argPairOk_not_calleeSaved (h2 q hq)

theorem assign_rets {us : List (Reg × Reg)} {regs : Array Reg} {i' : MInst}
    (h : (MInst.rets us).assign regs = .ok i') : ∃ us', i' = .rets us' := by
  unfold MInst.assign at h
  simp only [MInst.visitOperands, StateT.run_bind, StateT.run_pure] at h
  generalize StateT.run _ 0 = X at h
  cases X with
  | error e => cases h
  | ok v =>
    simp only [bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    · simp only [Except.ok.injEq] at h
      exact ⟨_, h.symm⟩

/-- The `j`-th use value of a `Rets` (of either class) is the store's value of its `j`-th fixed
register. -/
theorem rets_usesC {ns : List (Nat × RegClass × Reg)} {allocs : Array Loc} {m : Loc → CV}
    (hfix : ∀ p ∈ ((retOpsC ns).toArray.zip allocs).toList, ∀ r, p.1.con = .fixed r → p.2 = .reg r)
    (_hsz : (retOpsC ns).toArray.size = allocs.size) :
    ∀ (j : Nat) (v p : Reg) (x : CV), (argPairsC ns)[j]? = some (v, p) →
      ((((retOpsC ns).toArray.zip allocs).toList.filter (·.1.isUse)).map (m ·.2))[j]? = some x →
      x = m (.reg p) ∧ ∃ q ∈ ((retOpsC ns).toArray.zip allocs).toList, q.2 = .reg p := by
  intro j v p x hj hx
  have hu : ((retOpsC ns).toArray.zip allocs).toList.filter (·.1.isUse) =
      ((retOpsC ns).toArray.zip allocs).toList := by
    rw [List.filter_eq_self]
    intro q hq
    have := (List.of_mem_zip (by simpa using hq)).1
    simp only [retOpsC, List.mem_map] at this
    obtain ⟨_, -, e⟩ := this
    rw [← e]; rfl
  rw [hu] at hx
  simp only [List.getElem?_map, Option.map_eq_some_iff] at hx
  obtain ⟨q, hq, rfl⟩ := hx
  have hq' := hq
  simp only [Array.toList_zip, List.getElem?_zip_eq_some] at hq'
  obtain ⟨h1, -⟩ := hq'
  simp only [argPairsC, retOpsC, List.getElem?_map, Option.map_eq_some_iff] at hj h1
  obtain ⟨q1, hq1, e1⟩ := hj
  obtain ⟨q2, hq2, e2⟩ := h1
  rw [hq1] at hq2; cases hq2
  simp only [Prod.mk.injEq] at e1
  obtain ⟨-, rfl⟩ := e1
  have e3 := hfix q (List.mem_of_getElem? hq) q1.2.2 (by rw [← e2])
  exact ⟨by rw [e3], q, List.mem_of_getElem? hq, e3⟩

theorem retOps_eq_C (ns : List (Nat × Reg)) :
    retOps ns = retOpsC (ns.map fun q => (q.1, RegClass.int, q.2)) := by
  simp [retOps, retOpsC, Function.comp_def]

theorem retPairs_eq_C (ns : List (Nat × Reg)) :
    retPairs ns = argPairsC (ns.map fun q => (q.1, RegClass.int, q.2)) := by
  simp [retPairs, argPairsC, Function.comp_def]

/-- The `j`-th use value of a `Rets` is the store's value of its `j`-th fixed register. -/
theorem rets_uses {ns : List (Nat × Reg)} {allocs : Array Loc} {m : Loc → CV}
    (hfix : ∀ p ∈ ((retOps ns).toArray.zip allocs).toList, ∀ r, p.1.con = .fixed r → p.2 = .reg r)
    (_hsz : (retOps ns).toArray.size = allocs.size) :
    ∀ (j : Nat) (v p : Reg) (x : CV), (retPairs ns)[j]? = some (v, p) →
      ((((retOps ns).toArray.zip allocs).toList.filter (·.1.isUse)).map (m ·.2))[j]? = some x →
      x = m (.reg p) ∧ ∃ q ∈ ((retOps ns).toArray.zip allocs).toList, q.2 = .reg p := by
  rw [retOps_eq_C] at hfix _hsz ⊢
  rw [retPairs_eq_C]
  exact rets_usesC hfix _hsz

theorem iterN_one_succ {S : Type} (f : S → S) (n : Nat) (s : S) :
    iterN f (n + 1) s = f (iterN f n s) := by
  rw [iterN_add]; rfl

/-! ## Return tails: the restores emit no code -/

/-- The remaining items `its` of block `b` are a return tail with the registers `D` restored so
far: moves meeting `retTailOk`, then a `Rets`. -/
def TailOk (R : RL) (b : Nat) (D : List Reg) (its : List RItem) : Prop :=
  ∃ vb pend k a rest us, R.vc.blocks[b]? = some vb ∧ its = pend ++ .op k a :: rest ∧
    vb.insts[k]? = some (.rets us) ∧ retTailOk R.rf.saved D pend = true

/-- **In a return tail**: the restores of the registers `D` ran at the level of the allocated
code only (they emit no code: the epilogue pops the saved registers), so the store `m` is the
machine's store `mt` (related by `Q`) but at the registers of `D`. -/
def RetTail (R : RL) (s : Arm.ArmState) : MConf CV Arm.ArmState → Prop
  | .run ⟨b, its, m, w⟩ => ∃ mt D, Q R s (.run ⟨b, its, mt, w⟩) ∧
      (∀ l, (∀ r ∈ D, l ≠ .reg r) → m l = mt l) ∧ TailOk R b D its
  | _ => False

/-- **The register-level relation with Cranelift's callee saves**: `Q ∧ AInv`, or a return
tail. -/
def QA (R : RL) (s : Arm.ArmState) (c : MConf CV Arm.ArmState) : Prop :=
  (Q R s c ∧ AInv R c) ∨ RetTail R s c

/-- The registers restored so far in a valid return tail are a prefix of the saved ones. -/
theorem retTailOk_prefix {saved : List Reg} :
    ∀ {D : List Reg} {L : List RItem}, retTailOk saved D L = true → D <+: saved
  | D, [], h => by
    simp only [retTailOk, beq_iff_eq] at h
    subst h; exact List.prefix_refl _
  | D, it :: rest, h => by
    unfold retTailOk at h
    split at h
    · rename_i r _ _
      simp only [Bool.and_eq_true] at h
      exact (List.prefix_append D [r]).trans (retTailOk_prefix h.2)
    · simp only [Bool.and_eq_true] at h
      exact retTailOk_prefix h.2

/-! ## The return on the machine -/

theorem clobberOff_le {saves : List Reg} (hsv : SavesOk saves) {r : Reg} (h : r ∈ saves) :
    clobberOff saves r + 8 ≤ clobberBytes saves := by
  rcases saves_mem hsv h with ⟨n, rfl, hg, he⟩ | ⟨n, rfl, hg, he⟩
  · have := (List.getElem?_eq_some_iff.1 hg).1
    rw [he]; simp only [clobberBytes, pushBytes]; omega
  · have := (List.getElem?_eq_some_iff.1 hg).1
    rw [he]; simp only [clobberBytes, pushBytes]; omega

/-- A sub-read of a range on which two states agree. -/
theorem read_sub {s t : Arm.ArmState} {N : Nat} {B : BitVec 64}
    (h : ∀ k < N, s.mem (B + BitVec.ofNat 64 k) = t.mem (B + BitVec.ofNat 64 k)) {n o : Nat}
    (hle : o + n ≤ N) :
    Arm.read_mem_bytes n (B + BitVec.ofNat 64 o) s = Arm.read_mem_bytes n (B + BitVec.ofNat 64 o) t :=
  read_mem_bytes_congr n _ fun k hk => by rw [add_ofNat_add]; exact h _ (by omega)

theorem slotVal_of_popVal {t : Arm.ArmState} {r : Reg} {v : BitVec 64}
    (hr : (∃ n, r = .x n) ∨ ∃ n, r = .v n) (h : PopVal t r v) : slotVal t r = v := by
  rcases hr with ⟨n, rfl⟩ | ⟨n, rfl⟩
  · exact h
  · simp only [PopVal] at h
    simp only [slotVal, h]
    apply BitVec.eq_of_toNat_eq
    have := v.isLt
    simp only [BitVec.toNat_setWidth]
    omega

theorem slotVal_w_pc (v : BitVec 64) (s : Arm.ArmState) (r : Reg) :
    slotVal (Arm.w .PC v s) r = slotVal s r := by
  cases r <;> simp [slotVal, Arm.r_of_w_different]

/-- Distinct registers, one allocatable, one callee-saved, have distinct fields. -/
theorem field_ne_of_ne {r r' : Reg} (hr : r.allocatable = true) (hr' : r' ∈ calleeSaved)
    (hne : r' ≠ r) : ∀ f, r.field = some f → r'.field ≠ some f := by
  intro f hf e
  rcases allocatable_cases hr with ⟨n, rfl, hn⟩ | ⟨n, rfl, hn⟩ <;>
    rcases calleeSaved_cases hr' with ⟨n', rfl, h1, h2⟩ | ⟨n', rfl, h1, h2⟩ <;>
    simp only [Reg.field, Option.some.injEq] at hf e <;> rw [← hf] at e
  · exact rnum_ne (a := n') (b := n) (by omega) (by omega) (fun h => hne (by rw [h]))
      (Arm.StateField.GPR.inj e)
  · cases e
  · cases e
  · exact rnum_ne (a := n') (b := n) (by omega) (by omega) (fun h => hne (by rw [h]))
      (Arm.StateField.SFP.inj e)

/-- The field of a callee-saved register is masked. -/
theorem masked_of_calleeSaved {r : Reg} {f : Arm.StateField} (h : r ∈ calleeSaved)
    (hf : r.field = some f) : Masked f := by
  rcases calleeSaved_cases h with ⟨n, rfl, h1, h2⟩ | ⟨n, rfl, -⟩ <;>
    simp only [Reg.field, Option.some.injEq] at hf <;> subst hf
  · simp only [Masked, rnum_toNat (show n < 32 by omega)]; omega
  · trivial

/-- The prologue's lines from the ABI entry reach `R.sP`. -/
theorem RL.sP_steps {R : RL} (hR : R.Wf) {ra : BitVec 64} (hent : AbiCall R.fb R.base ra R.s0) :
    ∃ s', StepsOk (R.envOf 1) (prologueLines R.af.saves R.af.frameSize R.af.isCaller) R.s0 s' ∧ R.sP = s' ∧
      Arm.read_mem_bytes 16 (spv R.s0 - 16#64) s' = xreg 30 R.s0 ++ xreg 29 R.s0 ∧
      ∀ r ∈ R.af.saves, Arm.read_mem_bytes 8 (R.topB + BitVec.ofNat 64 (clobberOff R.af.saves r)) s' =
        slotVal R.s0 r := by
  obtain ⟨-, hfs, -, hsv, -, hcb, -, -, -⟩ := RL.frame_facts hR
  have hst0 := hR.stack.frame
  have hs : R.af.frameSize < 2 ^ 64 := by have := hst0.1; have := (spv R.s0).isLt; omega
  obtain ⟨vb, items, code, ls, ps1, ps2, T, -, -, -, -, -, hj0, hdrop⟩ := entry_block hR
  obtain ⟨s', hsteps, -, -, -, -, h16, hsl⟩ :=
    prologue_ok (calls := R.af.isCaller) (R.envOf 1) hs hsv (by rw [hfs]; exact hcb) R.s0 hent.spAligned
  have hpc1 : Arm.r .PC R.s0 = R.pcOf 1 := by
    rw [hent.pc]
    simp only [RL.pcOf, RL.L] at hj0 ⊢
    rw [lineOffset_succ _ _ _ hj0]
    simp [lineOffset, Line.size]
  obtain ⟨hiter, -, -, -⟩ := iterN_steps hR hdrop
    (fun ln h => by obtain ⟨x, e, hh, -⟩ := prologueLines_ins _ _ ln h; exact ⟨x, e, hh⟩)
    hent.program hpc1 hent.err hsteps
  exact ⟨s', hsteps, hiter, h16, hsl⟩

/-- The top of the frame (fp/lr and the clobber area) holds no kept address. -/
theorem RL.top_notG {R : RL} (hR : R.Wf) : ∀ k < R.topN, ¬ R.G (R.topB + BitVec.ofNat 64 k) := by
  obtain ⟨-, -, -, -, -, hcb, -, hst', hd⟩ := RL.frame_facts hR
  intro k hk hG
  apply hR.gfree _ hG
  have hsp0 := (spv R.s0).isLt
  simp only [RL.topN] at hk
  have hm : (16 + clobberBytes R.af.saves) % 2 ^ 64 = 16 + clobberBytes R.af.saves :=
    Nat.mod_eq_of_lt (by omega)
  have hk64 : (R.topB + BitVec.ofNat 64 k).toNat =
      (spv R.s0).toNat - (16 + clobberBytes R.af.saves) + k := by
    simp only [RL.topB, RL.topN]
    rw [BitVec.toNat_add, BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat, hm]; omega),
      BitVec.toNat_ofNat, hm, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega)]
    omega
  simp only [StackBelow, hk64, hd]
  constructor <;> omega

/-- **The top of the frame in a state related by `StRel`** (`fplr`): the entry x29 and x30 at
entry sp − 16 and − 8, each saved register's low 64 bits at its slot (`clobberOff` above
`R.topB`), as the prologue pushed them. -/
theorem RL.top_bytes {R : RL} (hR : R.Wf) {ra : BitVec 64} (hent : AbiCall R.fb R.base ra R.s0)
    {s : Arm.ArmState} (hfplr : Arm.read_mem_bytes R.topN R.topB s = R.topImg) :
    Arm.read_mem_bytes 8 (spv R.s0 - 16#64) s = xreg 29 R.s0 ∧
      Arm.read_mem_bytes 8 (spv R.s0 - 16#64 + 8#64) s = xreg 30 R.s0 ∧
      ∀ r ∈ R.af.saves, Arm.read_mem_bytes 8 (R.topB + BitVec.ofNat 64 (clobberOff R.af.saves r)) s =
        slotVal R.s0 r := by
  obtain ⟨-, -, -, hsv, -, -, -, -, -⟩ := RL.frame_facts hR
  have hbytes := read_mem_bytes_bytes R.topN R.topB s R.sP hfplr
  obtain ⟨sP, -, hsP, hP16, hPsl⟩ := RL.sP_steps hR hent
  rw [hsP] at hbytes
  have htopcb : R.topB + BitVec.ofNat 64 (clobberBytes R.af.saves) = spv R.s0 - 16#64 := by
    rw [RL.topB, RL.topN, BitVec.ofNat_add]; bv_omega
  have h16 : Arm.read_mem_bytes 16 (spv R.s0 - 16#64) s = xreg 30 R.s0 ++ xreg 29 R.s0 := by
    rw [← htopcb, read_sub (n := 16) (o := clobberBytes R.af.saves) hbytes
      (by simp only [RL.topN]; omega), htopcb]
    exact hP16
  obtain ⟨h29, h30⟩ := read16_split h16
  refine ⟨h29, h30, fun r hr => ?_⟩
  rw [read_sub (n := 8) (o := clobberOff R.af.saves r) hbytes
    (by have := clobberOff_le hsv hr; simp only [RL.topN]; omega)]
  exact hPsl r hr

theorem epilogueLines_epi (saves : List Reg) (size : Nat) :
    epilogueLines saves size = epiLines saves size ++ [.ins .ret] :=
  epilogueLines_eq saves size

/-- **The return on the machine** (Cranelift's epilogue): from `QA` at a `Rets` item, the
epilogue and `ret` reach the return address with `sp` and x29 as at entry, the memory as at the
item, the allocatable registers but the saved ones as in the store, each saved register's low 64
bits (its slot) as at entry, and the returned values in their fixed registers. -/
theorem ret_machine {R : RL} (hR : R.Wf) {ra : BitVec 64} (hent : AbiCall R.fb R.base ra R.s0)
    {s : Arm.ArmState} {b k : Nat} {allocs : Array Loc} {its : List RItem} {m : Loc → CV}
    {w : Arm.ArmState} (hqa : QA R s (.run ⟨b, .op k allocs :: its, m, w⟩)) {vb : VBlock}
    {us : List (Reg × Reg)} (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some (.rets us)) :
    ∃ n, (∀ i < n, R.GoodX (iterN R.step i s)) ∧
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
  obtain ⟨hiter, hpc1, hgood, hgx⟩ := iterN_steps hR hdrop'
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
      refine RL.goodX_ofIns hR hj hpc1 rfl rfl ?_ (by rw [herr1, hst.err]) (by rw [hprog1, hst.prog])
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

/-! ## Return tails from the callee-save shape (`saveShapeOk`) -/

theorem saveSegsOk_suffix {vb : VBlock} {saved : List Reg} :
    ∀ (A : List RItem) {pend L : List RItem}, saveSegsOk vb saved pend (A ++ L) = true →
      ∃ pend', saveSegsOk vb saved pend' L = true
  | [], pend, _, h => ⟨pend, h⟩
  | .move x y :: A, _, _, h => by
    simp only [List.cons_append, saveSegsOk] at h
    exact saveSegsOk_suffix A h
  | .op k a :: A, _, _, h => by
    simp only [List.cons_append, saveSegsOk, Bool.and_eq_true] at h
    exact saveSegsOk_suffix A h.2

/-- A pending run holding a save or a restore ends in a return tail. -/
theorem saveSegsOk_tail {vb : VBlock} {saved : List Reg} :
    ∀ (L : List RItem) {pend : List RItem}, saveSegsOk vb saved pend L = true →
      pend.all RItem.noSave = false →
      ∃ P k a rest us, L = P ++ .op k a :: rest ∧ vb.insts[k]? = some (.rets us) ∧
        retTailOk saved [] (pend ++ P) = true
  | [], pend, h, hn => by simp only [saveSegsOk] at h; rw [h] at hn; cases hn
  | .move x y :: L, pend, h, hn => by
    simp only [saveSegsOk] at h
    obtain ⟨P, k, a, rest, us, rfl, hk, ht⟩ :=
      saveSegsOk_tail L h (by simp [List.all_append, hn])
    exact ⟨.move x y :: P, k, a, rest, us, rfl, hk, by simpa using ht⟩
  | .op k a :: L, pend, h, hn => by
    simp only [saveSegsOk, Bool.and_eq_true] at h
    obtain ⟨h1, -⟩ := h
    split at h1
    · rename_i us hk
      rw [if_pos rfl] at h1
      exact ⟨[], k, a, L, us, rfl, hk, by simpa using h1⟩
    · rw [if_neg Bool.false_ne_true] at h1
      rw [h1] at hn; cases hn

theorem retTailOk_suffix {saved : List Reg} :
    ∀ (P : List RItem) {D : List Reg} {L : List RItem}, retTailOk saved D (P ++ L) = true →
      ∃ D', retTailOk saved D' L = true
  | [], D, _, h => ⟨D, h⟩
  | it :: P, _, _, h => by
    rw [List.cons_append] at h
    unfold retTailOk at h
    split at h
    · simp only [Bool.and_eq_true] at h; exact retTailOk_suffix P h.2
    · simp only [Bool.and_eq_true] at h; exact retTailOk_suffix P h.2

theorem retTailOk_restore {saved D : List Reg} {r : Reg} {dst : Loc} {L : List RItem}
    (h : retTailOk saved D (.move (.save r) dst :: L) = true) :
    dst = .reg r ∧ retTailOk saved (D ++ [r]) L = true := by
  cases dst with
  | reg r' =>
    by_cases e : r' = r
    · subst e
      simp only [retTailOk, RItem.restoreReg, RItem.isRestore, beq_self_eq_true,
        Bool.and_eq_true] at h
      exact ⟨rfl, h.2⟩
    · have hne : (r' == r) = false := by simpa using e
      simp [retTailOk, RItem.restoreReg, RItem.isRestore, hne, RItem.avoids, Loc.isSave] at h
  | _ => simp [retTailOk, RItem.restoreReg, RItem.isRestore, RItem.avoids, Loc.isSave] at h

theorem RItem.eq_restore {it : RItem} {r : Reg} (h1 : it.restoreReg = some r)
    (h2 : it.isRestore = true) : it = .move (.save r) (.reg r) := by
  cases it with
  | op k a => simp [RItem.restoreReg] at h1
  | move a d =>
    cases a with
    | save r' =>
      simp only [RItem.restoreReg, Option.some.injEq] at h1
      subst h1
      cases d with
      | reg r'' => simp only [RItem.isRestore, beq_iff_eq] at h2; subst h2; rfl
      | _ => simp [RItem.isRestore] at h2
    | _ => simp [RItem.restoreReg] at h1

/-- **A restore starts a return tail**: from `Q` at a move out of a save slot, the move is the
restore of its register `r` (`saveShapeOk`), and the items after it are a return tail with `r`
and the registers restored before it. -/
theorem restore_tail {R : RL} (hR : R.Wf) {s : Arm.ArmState} {b : Nat} {r : Reg} {dst : Loc}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    (hq : Q R s (.run ⟨b, .move (.save r) dst :: its, m, w⟩)) :
    dst = .reg r ∧ ∃ D, TailOk R b (D ++ [r]) its := by
  obtain ⟨hsh, -⟩ := lowerRFunc_saves hR.alloc
  obtain ⟨j, vb, items, pre, code, ls, ps1, ps2, T, hvb, hit, hsplit, -⟩ := hq
  obtain ⟨h0, h1⟩ := saveShapeOk_block hsh hvb hit
  obtain ⟨pend, hseg⟩ : ∃ pend, saveSegsOk vb R.rf.saved pend (.move (.save r) dst :: its) = true := by
    by_cases hb : b = 0
    · obtain ⟨htake, hseg⟩ := h0 hb
      have hlen : R.rf.saved.length ≤ pre.length := by
        apply Classical.byContradiction
        intro hlt
        have hlt' : pre.length < R.rf.saved.length := by omega
        have e := congrArg (·[pre.length]?) htake
        simp only [hsplit, List.getElem?_take, hlt', ite_true, List.getElem?_map] at e
        rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero] at e
        cases hs : R.rf.saved[pre.length]? <;> simp [hs] at e
      rw [hsplit, List.drop_append_of_le_length hlen] at hseg
      exact saveSegsOk_suffix _ hseg
    · have hseg := h1 hb
      rw [hsplit] at hseg
      exact saveSegsOk_suffix _ hseg
  simp only [saveSegsOk] at hseg
  obtain ⟨P, k, a, rest, us, rfl, hk, ht⟩ := saveSegsOk_tail its hseg
    (by simp [List.all_append, RItem.noSave, Loc.isSave])
  rw [List.append_assoc, List.singleton_append] at ht
  obtain ⟨D, hD⟩ := retTailOk_suffix pend ht
  obtain ⟨rfl, hr⟩ := retTailOk_restore hD
  exact ⟨rfl, D, vb, P, k, a, rest, us, hvb, rfl, hk, hr⟩

/-- **`Realizes` for `QA`**: from the realisation under `Q ∧ AInv` of every step but a callee
restore, the realisation of the moves (no restore) under `Q`, and the `Rets` steps' ending the
run. The restores take no machine step (`q_restore`); the moves of a return tail are realised
on the machine's store. -/
theorem realizesQA {R : RL} (hR : R.Wf) {sem : ISem CV Arm.ArmState} {keep : Reg → CV → CV}
    {T : Arm.ArmState → Prop}
    (hstep : ∀ s c c', Q R s c → AInv R c → MStep R.vc sem keep R.rf c c' →
      (∀ b src dst its m w, c = .run ⟨b, .move src dst :: its, m, w⟩ → src.isSave = false) →
      ∃ n c'', MStep R.vc sem keep R.rf c c'' ∧ (Q R (iterN R.step n s) c'' ∧ AInv R c'') ∧
        ∀ i < n, T (iterN R.step i s))
    (hmove : ∀ s b src dst its m w, Q R s (.run ⟨b, .move src dst :: its, m, w⟩) →
      src.isSave = false → ∃ n, Q R (iterN R.step n s) (.run ⟨b, its, upd m dst (m src), w⟩) ∧
        ∀ i < n, T (iterN R.step i s))
    (hrets : ∀ b k a its m w c' vb us, R.vc.blocks[b]? = some vb → vb.insts[k]? = some (.rets us) →
      MStep R.vc sem keep R.rf (.run ⟨b, .op k a :: its, m, w⟩) c' → ∃ vals m' w', c' = .ret vals m' w') :
    Realizes R.vc R.rf sem keep R.step (QA R) T := by
  intro s c c' hqa hm
  have nil : ∀ i < 0, T (iterN R.step i s) := fun _ h => absurd h (Nat.not_lt_zero _)
  rcases hqa with ⟨hq, hA⟩ | hrt
  · by_cases hres : ∃ b r dst its m w, c = .run ⟨b, .move (.save r) dst :: its, m, w⟩
    · obtain ⟨b, r, dst, its, m, w, rfl⟩ := hres
      obtain ⟨rfl, D, htl⟩ := restore_tail hR hq
      cases hm
      refine ⟨0, _, .move, .inr ?_, nil⟩
      simp only [RetTail]
      refine ⟨m, D ++ [r], q_restore rfl hq, fun l hl => ?_, htl⟩
      simp only [upd, hl r (by simp), ite_false]
    · obtain ⟨n, c'', hm', hq', ht⟩ := hstep s c c' hq hA hm fun b src dst its m w e => by
        cases src with
        | save r => exact absurd ⟨b, r, dst, its, m, w, e⟩ hres
        | _ => rfl
      exact ⟨n, c'', hm', .inl hq', ht⟩
  · rcases c with ⟨b, its, m, w⟩ | ⟨vals, m, w⟩ | w
    · simp only [RetTail] at hrt
      obtain ⟨mt, D, hq, hmD, vb, pend, k, a, rest, us, hvb, rfl, hk, htl⟩ := hrt
      rcases pend with _ | ⟨it, pend⟩
      · obtain ⟨vals, m', w', rfl⟩ := hrets b k a rest m w c' vb us hvb hk hm
        exact ⟨0, _, hm, .inl ⟨trivial, trivial⟩, nil⟩
      · simp only [List.cons_append] at hm hq
        unfold retTailOk at htl
        split at htl
        · rename_i r hr1 hr2
          simp only [Bool.and_eq_true] at htl
          obtain rfl := RItem.eq_restore hr1 hr2
          cases hm
          refine ⟨0, _, .move, .inr ?_, nil⟩
          simp only [RetTail]
          refine ⟨mt, D ++ [r], q_restore rfl hq, fun l hl => ?_, vb, pend, k, a, rest, us, hvb, rfl,
            hk, htl.2⟩
          simp only [upd, hl r (by simp), ite_false]
          exact hmD l (fun r' hr' => hl r' (List.mem_append_left _ hr'))
        · simp only [Bool.and_eq_true] at htl
          obtain ⟨hav, htl⟩ := htl
          cases it with
          | op _ _ => simp [RItem.avoids] at hav
          | move x y =>
            simp only [RItem.avoids, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false,
              Bool.or_eq_true, beq_iff_eq, not_or] at hav
            obtain ⟨⟨hx, -⟩, hD⟩ := hav
            cases hm
            obtain ⟨n, hq', ht⟩ := hmove s b x y _ mt w hq hx
            refine ⟨n, _, .move, .inr ?_, ht⟩
            simp only [RetTail]
            refine ⟨upd mt y (mt x), D, hq', fun l hl => ?_, vb, pend, k, a, rest, us, hvb, rfl, hk, htl⟩
            by_cases hly : l = y
            · simp only [upd, hly, ite_true]
              exact hmD x (fun r hr e => (hD r hr).1 e)
            · simp only [upd, hly, ite_false]
              exact hmD l hl
    · simp only [RetTail] at hrt
    · simp only [RetTail] at hrt

/-- `QA` at an item gives `Q` with the machine's store. -/
theorem qa_q {R : RL} {s : Arm.ArmState} {b : Nat} {its : List RItem} {m : Loc → CV}
    {w : Arm.ArmState} (h : QA R s (.run ⟨b, its, m, w⟩)) :
    ∃ mt, Q R s (.run ⟨b, its, mt, w⟩) := by
  rcases h with ⟨hq, -⟩ | h
  · exact ⟨m, hq⟩
  · simp only [RetTail] at h
    obtain ⟨mt, -, hq, -⟩ := h
    exact ⟨mt, hq⟩

/-- `QA` at an instruction other than a `Rets` is `Q ∧ AInv` (a return tail ends at its
`Rets`). -/
theorem qa_op {R : RL} {s : Arm.ArmState} {b k : Nat} {a : Array Loc} {its : List RItem}
    {m : Loc → CV} {w : Arm.ArmState} (h : QA R s (.run ⟨b, .op k a :: its, m, w⟩)) {vb : VBlock}
    {i : MInst} (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some i)
    (hnr : ∀ us, i ≠ .rets us) :
    Q R s (.run ⟨b, .op k a :: its, m, w⟩) ∧ AInv R (.run ⟨b, .op k a :: its, m, w⟩) := by
  rcases h with h | h
  · exact h
  · simp only [RetTail] at h
    obtain ⟨_mt, _D, _hq, _hm, vb', pend, k', a', rest, us, hvb', he, hk', htl⟩ := h
    rcases pend with _ | ⟨it, pend⟩
    · simp only [List.nil_append, List.cons.injEq, RItem.op.injEq] at he
      obtain ⟨⟨rfl, -⟩, -⟩ := he
      rw [hvb] at hvb'; cases hvb'
      rw [hi] at hk'; cases hk'
      exact absurd rfl (hnr us)
    · simp only [List.cons_append, List.cons.injEq] at he
      obtain ⟨rfl, -⟩ := he
      simp [retTailOk, RItem.restoreReg, RItem.isRestore, RItem.avoids] at htl

end Backend.Proof
