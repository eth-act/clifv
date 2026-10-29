module

public import FV.E2E.RegLevelFrame
public import FV.E2E.RegLevelGoodXNR
public import FV.E2E.RegLevelSegAlign

@[expose] public section

/-!
# The prologue and the return on the machine with no call state (SEM1 #537, step 2k)

`RegLevelFrame`'s `iterN_steps`, `q_init`, `ret_machine` with `RL.GoodXNR`
(docs/plans/uninit.md §5.5): the prologue, epilogue and `ret` lines are unhooked, so no state of
those runs is a call state.
-/

namespace Backend.Proof

open Backend E2E

/-- Straight-line lines at line `j` of the final code run as machine steps. -/
theorem iterN_stepsNR {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} {ls T : List Line} {j : Nat}
    {s s' : Arm.ArmState}
    (hdrop : R.L.drop j = ls ++ T)
    (hins : ∀ ln ∈ ls, ∃ x, ln = .ins x none ∧ x.hooked = false)
    (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j)
    (herr : Arm.r .ERR s = .None) (h : StepsOk (R.envOf j) ls s s') :
    iterN R.step ls.length s = s' ∧ Arm.r .PC s' = R.pcOf (j + ls.length) ∧
      (∀ i, 0 < i → i ≤ ls.length → R.Good (iterN R.step i s)) ∧
      ((∀ i t, Line.ins i t ∈ ls → i.tlsTail = false) → R.Good s → ∀ {Pa : BitVec 64 → Prop},
        (∀ a, Pa a → R.ReadOk a) →
        (∀ x t, Line.ins x t ∈ ls → x.loads = true → ∀ a, Pa a → R.ReadInY Y x.ldpFR a) →
        LinesReads (R.envOf j) ls s Pa → ∀ i < ls.length, R.GoodXNY Y (iterN R.step i s)) := by
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
    fun htail h0 _ hok hP hrd => RL.goodXNR_execLinesGP hR hat hhook htail hprog hpc herr h0
      (stepsOk_interOk h herr) hrun hok hP hrd⟩
  rw [execLines_pc hrun, hpc]
  simp only [RL.pcOf, RL.L]
  rw [lineOffset_drop_ins (by simpa [RL.L] using hdrop) hins', BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add]

/-- **After the prologue, at the chosen initial witness**: `q_initNR` with the prologue's length
(a function of the code only) and `QW` at `R.initW`. -/
theorem q_initNA {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} {ra : BitVec 64}
    (hent : AbiCall R.fb R.base ra R.s0)
    {w₀ : Arm.ArmState} (hbe : BodyEntryW R.F R.vc.EntryArg R.af R.s0 w₀) :
    ∃ n, n = (prologueLines R.af.frameSize).length ∧ (∀ i < n, R.GoodXNY Y (iterN R.step i R.s0)) ∧
      QW R (iterN R.step n R.s0) R.initW.1 R.initW.2.1 R.initW.2.2
        (MConf.init R.rf (locVal R.fr (iterN R.step n R.s0)) w₀) ∧
      AInv R (MConf.init R.rf (locVal R.fr (iterN R.step n R.s0)) w₀) ∧
      ∀ f, f ≠ .PC → f ≠ .GPR 29#5 → f ≠ .GPR 31#5 → f ≠ .GPR 16#5 →
        Arm.r f (iterN R.step n R.s0) = Arm.r f R.s0 := by
  have hframe := lowerRFunc_frame hR.alloc
  have hst0 := hR.stack.frame
  have hsp0 := (spv R.s0).isLt
  have hs : R.af.frameSize < 2 ^ 64 := by have := hst0.1; omega
  have hal0 : Arm.CheckSPAlignment R.s0 := (checkSP_iff _).2 hent.spAligned
  obtain ⟨vb, items, code, ls, ps1, ps2, T, hvb, hit, hcode, hls, htr, hj0, hdrop⟩ := entry_block hR
  obtain ⟨s', hsteps, hsp', hfp', ho', hm'⟩ := prologue_ok (R.envOf 1) hs R.s0 hal0
  have hpc1 : Arm.r .PC R.s0 = R.pcOf 1 := by
    rw [hent.pc]
    simp only [RL.pcOf, RL.L] at hj0 ⊢
    rw [lineOffset_succ _ _ _ hj0]
    simp [lineOffset, Line.size]
  obtain ⟨hiter, hpc', -, hgx⟩ := iterN_stepsNR (Y := Y) hR hdrop
    (fun ln h => by obtain ⟨x, e, hh, -⟩ := prologueLines_ins _ ln h; exact ⟨x, e, hh⟩)
    hent.program hpc1 hent.err hsteps
  obtain ⟨herr', hprog'⟩ := hsteps.err
  refine ⟨(prologueLines R.af.frameSize).length, rfl,
    hgx (prologueLines_tail _) (.inl (by rw [hent.pc]; exact RL.not_postCall_base hR hent.fits))
      (Pa := fun _ => False) (fun _ h => h.elim) (fun _ _ _ _ _ h => h.elim)
      (linesReads_noLoads (prologueLines_noLoads _)), ?_⟩
  rw [hiter]
  have hdrop0 : frameDrop R.af = R.af.frameSize + 16 := by simp [frameDrop, hframe]
  have hspB : spOf s' = R.spB := by
    rw [hsp', RL.spB, hdrop0]; exact sp_sub16 _ _
  -- the fp/lr slot
  have hslot : ∀ a, (∀ k < 16, a ≠ spv R.s0 - 16#64 + BitVec.ofNat 64 k) → s'.mem a = R.s0.mem a := by
    intro a ha
    rw [hm', Arm.Memory.write_mem_bytes_eq_mem_write_bytes]
    exact write_bytes_outside 16 _ _ _ ha
  have hmemF : ∀ a, ¬ R.F a → s'.mem a = w₀.mem a := by
    intro a ha
    rw [hslot a (fun k hk e => ha (e ▸ RL.FK_F (fplr_inF hR hframe k hk))), hbe.mem a ha]
  have hcode' : ∀ a, CodeAddr R.s0 a → s'.mem a = R.s0.mem a := by
    intro a ha
    apply hslot
    intro k hk e
    have h2 := hst0.2 a ha
    rw [e] at h2
    have : spv R.s0 - 16#64 + BitVec.ofNat 64 k - (spv R.s0 - BitVec.ofNat 64 (R.af.frameSize + 16)) =
        BitVec.ofNat 64 (R.af.frameSize + k) := by
      apply BitVec.eq_of_toNat_eq
      have := hst0.1
      simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt (a := R.af.frameSize + 16) (by omega),
        Nat.mod_eq_of_lt (a := R.af.frameSize + k) (by omega)]
      simp only [spv] at *
      omega
    rw [this, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h2
    omega
  have hfield : ∀ f, f ≠ .PC → f ≠ .GPR 29#5 → f ≠ .GPR 31#5 → f ≠ .GPR 16#5 →
      Arm.r f s' = Arm.r f R.s0 := ho'
  -- the kept addresses are not the fp/lr slot
  have hgk : ∀ a, R.G a → s'.mem a = R.s0.mem a := by
    intro a ha
    apply hslot
    intro k hk e
    apply hR.gfree a ha
    rw [e, hdrop0]
    have := hst0.1
    have hk64 : (spv R.s0 - 16#64 + BitVec.ofNat 64 k).toNat = (spv R.s0).toNat - 16 + k := by
      simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
      have := (spv R.s0).isLt
      rw [Nat.mod_eq_of_lt (a := k) (by omega)]
      simp only [spv] at *
      omega
    simp only [StackBelow, hk64]
    constructor <;> omega
  refine ⟨?_, ?_, hfield⟩
  · have hitems : R.rf.blocks[0]! = items := by simp [getElem!_def, hit]
    have hIW : R.InitWit (1 + (prologueLines R.af.frameSize).length, ps1, T) :=
      ⟨rfl, fun items' hit' => by
        rw [hit] at hit'; cases hit'
        exact ⟨vb, code, ls, ps2, hvb, itemsChecked_block hR hvb hit, hcode, hls, htr,
          by rw [← List.drop_drop, hdrop, List.drop_left]⟩⟩
    have hW := RL.initW_spec ⟨_, hIW⟩
    obtain ⟨vb', code', ls', ps2', hvb', hchk', hcodeW, hls', htr', hdrop'⟩ := hW.2 items hit
    simp only [MConf.init, hitems]
    refine ⟨vb', items, [], code', ls', ps2', hvb', hit, rfl, hchk', hcodeW, hls', htr', hdrop',
      by rw [hW.1]; exact hpc', ?_⟩
    · refine ⟨fun l _ _ => rfl, ⟨fun f hf => ?_, hmemF, ?_⟩, by rw [herr', hent.err], by rw [hprog', hent.program],
        hspB, ?_, fun _ => ?_, code_keep hR.prog0 hent.code hcode', hgk⟩
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
        have hm : (R.af.frameSize + 16) % 2 ^ 64 = R.af.frameSize + 16 := Nat.mod_eq_of_lt (by omega)
        rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat, hm]; omega),
          BitVec.toNat_ofNat, hm]
        have : R.af.frameSize % 16 = 0 := by
          rw [(lowerRFunc_ok hR.alloc).1.1]; exact alignTo16_mod _
        omega
      · rw [← Arm.read_mem_bytes_of_write_mem_bytes_same (n := 16) (addr := spv R.s0 - 16#64)
          (v := xreg 30 R.s0 ++ xreg 29 R.s0) (s := R.s0) (by decide)]
        exact read_mem_bytes_congr _ _ (fun k _ => by rw [hm']; rfl)
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

/-- **After the prologue**: the machine is at the entry configuration of the allocated code
(store = the machine's locations, world = any body-entry world `w₀`), `AInv` holds, and every
field but the pc, x16, x29 and `sp` is as at entry. -/
theorem q_initNR {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} {ra : BitVec 64}
    (hent : AbiCall R.fb R.base ra R.s0)
    {w₀ : Arm.ArmState} (hbe : BodyEntryW R.F R.vc.EntryArg R.af R.s0 w₀) :
    ∃ n, (∀ i < n, R.GoodXNY Y (iterN R.step i R.s0)) ∧
      Q R (iterN R.step n R.s0) (MConf.init R.rf (locVal R.fr (iterN R.step n R.s0)) w₀) ∧
      AInv R (MConf.init R.rf (locVal R.fr (iterN R.step n R.s0)) w₀) ∧
      ∀ f, f ≠ .PC → f ≠ .GPR 29#5 → f ≠ .GPR 31#5 → f ≠ .GPR 16#5 →
        Arm.r f (iterN R.step n R.s0) = Arm.r f R.s0 :=
  let ⟨n, _, hg, hq, hA, hf⟩ := q_initNA (Y := Y) hR hent hbe
  ⟨n, hg, hq.q, hA, hf⟩

/-- **The number of machine steps of the epilogue and `ret`** (a function of the code only). -/
def RL.retLen (R : RL) : Nat := (spAdjLines false R.af.frameSize).length + 2

/-- **The return on the machine, with its length**: `ret_machineNR`, the run taking exactly
`R.retLen` steps (the epilogue's lines and the `ret`). -/
theorem ret_machineNA {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} {ra : BitVec 64}
    (hent : AbiCall R.fb R.base ra R.s0)
    {s : Arm.ArmState} {b k : Nat} {allocs : Array Loc} {its : List RItem} {m : Loc → CV}
    {w : Arm.ArmState} (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩)) {vb : VBlock}
    {us : List (Reg × Reg)} (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some (.rets us)) :
    ∃ n, n = R.retLen ∧ (∀ i < n, R.GoodXNY Y (iterN R.step i s)) ∧
      Arm.r .PC (iterN R.step n s) = ra ∧ Arm.r .ERR (iterN R.step n s) = .None ∧
      spv (iterN R.step n s) = spv R.s0 ∧ xreg 29 (iterN R.step n s) = xreg 29 R.s0 ∧
      (∀ r, r.allocatable = true → regVal (iterN R.step n s) r = regVal s r) ∧
      (iterN R.step n s).mem = s.mem ∧
      (∀ f, ¬ Masked f → f ≠ .GPR 29#5 → f ≠ .GPR 31#5 → Arm.r f (iterN R.step n s) = Arm.r f s) ∧
      (iterN R.step n s).program = s.program ∧
      ∀ ops, (MInst.rets us).operands = .ok ops → ∀ (j : Nat) (v p : Reg) (x : CV), us[j]? = some (v, p) →
        ((((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)))[j]? = some x →
        regVal (iterN R.step n s) p = x := by
  have hframe := lowerRFunc_frame hR.alloc
  have hck := (lowerRFunc_ok hR.alloc).2.2
  have hst0 := hR.stack.frame
  have hsp0 := (spv R.s0).isLt
  have hs : R.af.frameSize < 2 ^ 64 := by have := hst0.1; omega
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
  rw [epilogueLines_eq] at hdrop
  have hpl : ∀ ln ∈ spAdjLines false R.af.frameSize ++
      [Line.ins (.ldp Reg.fp Reg.lr (.spPostIndexed 16)) none, .ins .ret none], ln.plain = true := by
    intro ln hln
    rcases List.mem_append.1 hln with hln | hln
    · obtain ⟨_, _, _, hp⟩ := spAdjLines_ins false _ ln hln; exact hp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hln
      rcases hln with rfl | rfl <;> rfl
  rw [ftR_plain_append _ _ _ hpl (noTrap_next h2)] at hdrop
  have hdrop' : R.L.drop j0 = (spAdjLines false R.af.frameSize ++
      [Line.ins (.ldp Reg.fp Reg.lr (.spPostIndexed 16)) none]) ++
      (.ins .ret none :: (relaxLines R.far (ftList (ls2 ++ nxtOf R.af b)) ++ T)) := by
    rw [hdrop]; simp
  -- alignment of `sp + size` (= the fp/lr slot)
  have hdrop0 : frameDrop R.af = R.af.frameSize + 16 := by simp [frameDrop, hframe]
  have hslot : spOf s + BitVec.ofNat 64 R.af.frameSize = spv R.s0 - 16#64 := by
    rw [hst.sp, RL.spB, hdrop0, BitVec.ofNat_add]; bv_omega
  have hal : (spOf s + BitVec.ofNat 64 R.af.frameSize).toNat % 16 = 0 := by
    have h16 : 16 ≤ (spv R.s0).toNat := by have := hst0.1; omega
    rw [hslot, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simpa using h16)]
    have := hent.spAligned
    simp; omega
  obtain ⟨s1, hsteps, hsp1, hx29, hx30, ho1, hm1⟩ := epilogue_ok (R.envOf j0) hs s hal
  -- the reads: the `ldp` reads the fp/lr slot, which is not kept
  have hrdE : LinesReads (R.envOf j0) (spAdjLines false R.af.frameSize ++
      [Line.ins (.ldp Reg.fp Reg.lr (.spPostIndexed 16)) none]) s
      (fun a => ∃ k < 16, a = spv R.s0 - 16#64 + BitVec.ofNat 64 k) := by
    refine linesReads_append_last (spAdjLines_noLoads false _) fun s1' hs1' env' a ha p hp k hk => ?_
    obtain ⟨s2, h2, hsp2, -, -⟩ := spAdj_ok (R.envOf j0) false hs s
    rw [h2.exec] at hs1'
    cases hs1'
    rw [memReads_ldp_fplr ha] at hp
    simp only [List.mem_singleton] at hp
    subst hp
    simp only [Bool.false_eq_true, ite_false] at hsp2
    simp only at hk ⊢
    rw [hsp2, hslot]
    exact ⟨k, hk, rfl⟩
  have hokE : ∀ a, (∃ k < 16, a = spv R.s0 - 16#64 + BitVec.ofNat 64 k) → R.ReadOk a := by
    rintro _ ⟨k, hk, rfl⟩
    refine .inl fun hG => hR.gfree _ hG ?_
    rw [hdrop0]
    have := hst0.1
    have hk64 : (spv R.s0 - 16#64 + BitVec.ofNat 64 k).toNat = (spv R.s0).toNat - 16 + k := by
      simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
      have := (spv R.s0).isLt
      rw [Nat.mod_eq_of_lt (a := k) (by omega)]
      simp only [spv] at *
      omega
    simp only [StackBelow, hk64]
    constructor <;> omega
  have hPE : ∀ x t, Line.ins x t ∈ spAdjLines false R.af.frameSize ++
      [Line.ins (.ldp Reg.fp Reg.lr (.spPostIndexed 16)) none] → x.loads = true →
      ∀ a, (∃ k < 16, a = spv R.s0 - 16#64 + BitVec.ofNat 64 k) → R.ReadInY Y x.ldpFR a := by
    rintro x t hm hl _ ⟨k, hk, rfl⟩
    rcases List.mem_append.1 hm with hm | hm
    · rw [spAdjLines_noLoads false _ x t hm] at hl; cases hl
    simp only [List.mem_singleton, Line.ins.injEq] at hm
    obtain ⟨rfl, -⟩ := hm
    refine .inr (.inl ⟨R.af.frameSize + k, by rw [hdrop0]; omega, .inr rfl, ?_⟩)
    have := hst0.1
    have h16 : 16 ≤ (spv R.s0).toNat := by omega
    simp only [RL.spB, hdrop0]
    apply BitVec.eq_of_toNat_eq
    have := (spv R.s0).isLt
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    simp only [spv] at *
    omega
  obtain ⟨hiter, hpc1, hgood, hgx⟩ := iterN_stepsNR (Y := Y) hR hdrop'
    (fun ln h => by
      rcases List.mem_append.1 h with h | h
      · obtain ⟨x, e, hh, -⟩ := spAdjLines_ins false _ ln h; exact ⟨x, e, hh⟩
      · simp only [List.mem_singleton] at h; exact ⟨_, h, rfl⟩)
    hst.prog hpc hst.err hsteps
  obtain ⟨herr1, hprog1⟩ := hsteps.err
  -- the `ret`
  have hj : R.fa.lines.toList[j0 + (spAdjLines false R.af.frameSize ++
      [Line.ins (.ldp Reg.fp Reg.lr (.spPostIndexed 16)) none]).length]? = some (Line.ins .ret none) := by
    have := congrArg (·[(spAdjLines false R.af.frameSize ++
      [Line.ins (.ldp Reg.fp Reg.lr (.spPostIndexed 16)) none]).length]?) hdrop'
    simpa [List.getElem?_drop, RL.L] using this
  obtain ⟨a, ha, hstep⟩ := armStepX_ins (X := R.X) (H := R.H) hR.layout hR.lm hR.fit hj rfl
    (by rw [hprog1, hst.prog]) hpc1 (by rw [herr1, hst.err])
  obtain ⟨a', ha', he'⟩ := exec_ret ⟨lineOffset R.fa.lines.toList (j0 + (spAdjLines false R.af.frameSize ++
      [Line.ins (.ldp Reg.fp Reg.lr (.spPostIndexed 16)) none]).length), (R.lm[·]?)⟩ s1
  rw [ha] at ha'; cases ha'
  have hfin : iterN R.step ((spAdjLines false R.af.frameSize ++
      [Line.ins (.ldp Reg.fp Reg.lr (.spPostIndexed 16)) none]).length + 1) s = Arm.w .PC (xreg 30 s1) s1 := by
    rw [iterN_one_succ, hiter]; exact hstep.trans he'
  have hfplr := hst.fplr hframe
  rw [← hslot] at hfplr
  have hregs : ∀ r, r.allocatable = true → regVal (Arm.w .PC (xreg 30 s1) s1) r = regVal s r := by
    intro r hr
    rw [regVal_w (by rcases allocatable_cases hr with ⟨n, rfl, _⟩ | ⟨n, rfl, _⟩ <;> simp [Reg.field])]
    rcases allocatable_cases hr with ⟨n, rfl, hn⟩ | ⟨n, rfl, hn⟩
    · have hne : ∀ q, q < 32 → q ≠ n → Arm.StateField.GPR (rnum n) ≠ .GPR (BitVec.ofNat 5 q) :=
        fun q h1 h2 e => rnum_ne (a := n) (b := q) (by omega) h1 (Ne.symm h2) (Arm.StateField.GPR.inj e)
      simp only [regVal]
      rw [ho1 _ (by simp) (hne 29 (by omega) (by omega)) (hne 30 (by omega) (by omega))
        (hne 31 (by omega) (by omega)) (hne 16 (by omega) (by omega))]
    · simp only [regVal]
      rw [ho1 _ (by simp) (by simp) (by simp) (by simp) (by simp)]
  refine ⟨(spAdjLines false R.af.frameSize ++
      [Line.ins (.ldp Reg.fp Reg.lr (.spPostIndexed 16)) none]).length + 1,
    by simp [RL.retLen], fun i hi => ?_, ?_⟩
  · rcases Nat.lt_or_ge i (spAdjLines false R.af.frameSize ++
        [Line.ins (.ldp Reg.fp Reg.lr (.spPostIndexed 16)) none]).length with hi1 | hi1
    · refine hgx (fun x t h => ?_) (RL.good_of_sp hst.sp) hokE hPE hrdE i hi1
      rcases List.mem_append.1 h with h | h
      · exact spAdjLines_tail false _ x t h
      · simp only [List.mem_singleton, Line.ins.injEq] at h
        obtain ⟨rfl, -⟩ := h; rfl
    · obtain rfl : i = (spAdjLines false R.af.frameSize ++
          [Line.ins (.ldp Reg.fp Reg.lr (.spPostIndexed 16)) none]).length := by omega
      rw [hiter]
      refine RL.goodXNR_ofIns hR hj hpc1 rfl rfl ?_ (by rw [herr1, hst.err]) (by rw [hprog1, hst.prog])
        (by
          rw [show R.step s1 = Arm.w .PC (xreg 30 s1) s1 from hstep.trans he']
          exact RL.nextOk_ret (by
            rw [Arm.r_of_w_same, hx30, hfplr, BitVec.extractLsb'_append_eq_left]))
        (RL.readsIn_noLoad hR hj hpc1 rfl)
      rw [← hiter]
      exact hgood _ (by simp) (Nat.le_refl _)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hfin]
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
  · exact hregs
  · rw [Arm.ArmState.mem_w_eq_mem, hm1]
  · intro f hf h29 h31
    have hpc : f ≠ .PC := by rintro rfl; exact hf trivial
    rw [Arm.r_of_w_different hpc]
    exact ho1 f hpc h29 (by rintro rfl; exact hf (by simp [Masked])) h31
      (by rintro rfl; exact hf (by simp [Masked]))
  · rw [Arm.w_program, hprog1]
  · intro ops' hops' j v p x hj hx
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
    rw [hregs p hal, hst.store (.reg p) (fun r e => by cases e; exact hal) trivial]
    rfl

/-- **The return on the machine**: from `Q` at a `Rets` item, the epilogue and `ret` reach the
return address with `sp` and x29 as at entry, the allocatable registers and the memory as at
the item, and the returned values in their fixed registers. -/
theorem ret_machineNR {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} {ra : BitVec 64}
    (hent : AbiCall R.fb R.base ra R.s0)
    {s : Arm.ArmState} {b k : Nat} {allocs : Array Loc} {its : List RItem} {m : Loc → CV}
    {w : Arm.ArmState} (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩)) {vb : VBlock}
    {us : List (Reg × Reg)} (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some (.rets us)) :
    ∃ n, (∀ i < n, R.GoodXNY Y (iterN R.step i s)) ∧
      Arm.r .PC (iterN R.step n s) = ra ∧ Arm.r .ERR (iterN R.step n s) = .None ∧
      spv (iterN R.step n s) = spv R.s0 ∧ xreg 29 (iterN R.step n s) = xreg 29 R.s0 ∧
      (∀ r, r.allocatable = true → regVal (iterN R.step n s) r = regVal s r) ∧
      (iterN R.step n s).mem = s.mem ∧
      (∀ f, ¬ Masked f → f ≠ .GPR 29#5 → f ≠ .GPR 31#5 → Arm.r f (iterN R.step n s) = Arm.r f s) ∧
      (iterN R.step n s).program = s.program ∧
      ∀ ops, (MInst.rets us).operands = .ok ops → ∀ (j : Nat) (v p : Reg) (x : CV), us[j]? = some (v, p) →
        ((((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)))[j]? = some x →
        regVal (iterN R.step n s) p = x :=
  let ⟨n, _, h⟩ := ret_machineNA (Y := Y) hR hent hq hvb hi
  ⟨n, h⟩

end Backend.Proof
