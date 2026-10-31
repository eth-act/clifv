import FV.E2E.RegLevelGoodX
import FV.E2E.ExecWrites
import FV.E2E.MoveWrites

/-!
# The writes of the M6 runs (A3, #412, slice F8b)

`RL.WritesAt R u` (next to D2's `RL.ReadsAt`): the memory writes (`MemWrites`) of the unhooked
instruction at the pc avoid the kept addresses `R.G`. With D2 it bounds the whole footprint of
every step of the activation's run (`E2E.ExecBytes.instEvs_cover`): a map that allows every byte
outside `G` for reading and writing, and the function's jump tables for reading, makes no step
fault (`ArmFault`). `RL.GoodXW` is `GoodX` with `WritesAt`; this file has the builders the
realised forms use (`RL.writesAt_of_line`, `RL.writesAt_noStore`, `RL.writesAt_hooked`,
`RL.goodXW_execLinesG`).
-/

namespace Backend.Proof

open Backend E2E

/-- **F8b at `u`**: the memory writes of the unhooked instruction at the pc avoid `G`. -/
def RL.WritesAt (R : RL) (u : Arm.ArmState) : Prop :=
  ∀ j x t, R.L[j]? = some (.ins x t) → Arm.r .PC u = R.pcOf j → x.hooked = false →
    ∀ env a, x.toArmInst env = .ok a → ∀ p ∈ E2E.ExecBytes.MemWrites a u, ∀ k < p.2,
      ¬ R.G (p.1 + BitVec.ofNat 64 k)

/-- **The per-state facts with the writes.** -/
def RL.GoodXW (R : RL) (u : Arm.ArmState) : Prop := R.GoodX u ∧ R.WritesAt u

/-- **The writes at `u` satisfy `P`**: `RL.WritesAt` for any address predicate (`WritesAt` is
`WritesAtP` of the addresses outside `G`). -/
def RL.WritesAtP (R : RL) (P : BitVec 64 → Prop) (u : Arm.ArmState) : Prop :=
  ∀ j x t, R.L[j]? = some (.ins x t) → Arm.r .PC u = R.pcOf j → x.hooked = false →
    ∀ env a, x.toArmInst env = .ok a → ∀ p ∈ E2E.ExecBytes.MemWrites a u, ∀ k < p.2, P (p.1 + BitVec.ofNat 64 k)

theorem RL.writesAt_iff {R : RL} {u : Arm.ArmState} : R.WritesAt u ↔ R.WritesAtP (fun a => ¬ R.G a) u :=
  Iff.rfl

/-- `WritesAtP` at an instruction line from the writes of its instruction. -/
theorem RL.writesAtP_of_line {R : RL} (hR : R.Wf) {P : BitVec 64 → Prop} {u : Arm.ArmState} {j : Nat}
    {x : Insn} {t : Option Clif.TrapCode} (hj : R.L[j]? = some (.ins x t)) (hpc : Arm.r .PC u = R.pcOf j)
    (h : x.hooked = false → ∀ env a, x.toArmInst env = .ok a →
      ∀ p ∈ E2E.ExecBytes.MemWrites a u, ∀ k < p.2, P (p.1 + BitVec.ofNat 64 k)) :
    R.WritesAtP P u := by
  intro j' x' t' hj' hpc' hh
  obtain rfl := RL.pcOf_inj hR hj hj' (hpc.symm.trans hpc')
  rw [hj] at hj'
  cases hj'
  exact h hh

/-- `WritesAt` at an instruction line from the writes of its instruction. -/
theorem RL.writesAt_of_line {R : RL} (hR : R.Wf) {u : Arm.ArmState} {j : Nat} {x : Insn}
    {t : Option Clif.TrapCode} (hj : R.L[j]? = some (.ins x t)) (hpc : Arm.r .PC u = R.pcOf j)
    (h : x.hooked = false → ∀ env a, x.toArmInst env = .ok a →
      ∀ p ∈ E2E.ExecBytes.MemWrites a u, ∀ k < p.2, ¬ R.G (p.1 + BitVec.ofNat 64 k)) :
    R.WritesAt u := by
  intro j' x' t' hj' hpc' hh
  obtain rfl := RL.pcOf_inj hR hj hj' (hpc.symm.trans hpc')
  rw [hj] at hj'
  cases hj'
  exact h hh

/-- `WritesAt` at a line whose instruction is no store. -/
theorem RL.writesAt_noStore {R : RL} (hR : R.Wf) {u : Arm.ArmState} {j : Nat} {x : Insn}
    {t : Option Clif.TrapCode} (hj : R.L[j]? = some (.ins x t)) (hpc : Arm.r .PC u = R.pcOf j)
    (hx : x.stores = false) : R.WritesAt u :=
  RL.writesAt_of_line hR hj hpc fun _ _ a ha p hp => by
    rw [Insn.memWrites_nil hx ha] at hp; cases hp

/-- `WritesAt` at a hooked line. -/
theorem RL.writesAt_hooked {R : RL} (hR : R.Wf) {u : Arm.ArmState} {j : Nat} {x : Insn}
    {t : Option Clif.TrapCode} (hj : R.L[j]? = some (.ins x t)) (hpc : Arm.r .PC u = R.pcOf j)
    (hx : x.hooked = true) : R.WritesAt u :=
  RL.writesAt_of_line hR hj hpc fun h => by rw [hx] at h; cases h

/-- `WritesAt` where the pc is at no instruction line of the activation. -/
theorem RL.writesAt_noLine {R : RL} {u : Arm.ArmState}
    (h : ∀ j x t, R.L[j]? = some (.ins x t) → Arm.r .PC u ≠ R.pcOf j) : R.WritesAt u :=
  fun j x t hj hpc => absurd hpc (h j x t hj)

/-- `WritesAt` at a `GoodX` state whose line holds no store. -/
theorem RL.writesAt_of_goodX {R : RL} (hR : R.Wf) {u : Arm.ArmState} (hg : R.GoodX u)
    (h : ∀ x, R.AtLine u x → x.stores = false) : R.WritesAt u := by
  obtain ⟨x, ⟨j, t, hj, hpc⟩, -⟩ := hg.line
  exact RL.writesAt_noStore hR hj hpc (h x ⟨j, t, hj, hpc⟩)

/-- **The states of a straight-line run with their writes** (`RL.goodX_execLinesG` with the
writes of the lines). -/
theorem RL.goodXW_execLinesG {R : RL} (hR : R.Wf) {ls : List Line} {j : Nat} {s s' : Arm.ArmState}
    (hat : ∀ k ln, ls[k]? = some ln → R.fa.lines.toList[j + k]? = some ln)
    (hhook : ∀ i t, Line.ins i t ∈ ls → i.hooked = false)
    (htail : ∀ i t, Line.ins i t ∈ ls → i.tlsTail = false)
    (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j)
    (herr : Arm.r .ERR s = .None) (h0 : R.Good s) (hinter : InterOk (R.envOf j) ls s)
    (hrun : execLines (R.envOf j) ls s = some s')
    (hrd : LinesReads (R.envOf j) ls s R.ReadOk)
    (hwr : LinesWrites (R.envOf j) ls s fun a => ¬ R.G a) :
    ∀ i < ls.length, R.GoodXW (iterN R.step i s) := by
  intro i hi
  refine ⟨RL.goodX_execLinesG hR hat hhook htail hprog hpc herr h0 hinter hrun hrd i hi, ?_⟩
  have hpcs := iterN_execLines_pc (X := R.X) (H := R.H) hR.layout hR.lm hR.fit ls j s s' hat hhook
    hprog hpc herr hinter hrun
  obtain ⟨ln, hln⟩ : ∃ ln, ls[i]? = some ln := ⟨ls[i], List.getElem?_eq_getElem hi⟩
  have hmem := List.mem_of_getElem? hln
  obtain ⟨x, t, rfl⟩ := execLines_ins hrun _ hmem
  have hj : R.L[j + i]? = some (.ins x t) := hat i _ hln
  have hpci : Arm.r .PC (iterN R.step i s) = R.pcOf (j + i) := hpcs i (by omega)
  have hst : ∃ s1, execLines (R.envOf j) (ls.take i) s = some s1 ∧ iterN R.step i s = s1 := by
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · exact ⟨s, by simp [execLines], rfl⟩
    · obtain ⟨s1, hs1⟩ := execLines_take i hrun
      have hlen : (ls.take i).length = i := by simp; omega
      have hit := iterN_execLines (X := R.X) (H := R.H) hR.layout hR.lm hR.fit (ls.take i) j s s1
        (fun k ln hk => by
          rw [List.getElem?_take] at hk
          split at hk
          · exact hat k ln hk
          · cases hk)
        (fun i' t' hm => hhook i' t' (List.mem_of_mem_take hm)) hprog hpc herr
        (fun k hk0 hk s2 hs2 => hinter k hk0 (by omega) s2 (by
          rwa [List.take_take, Nat.min_eq_left (by omega)] at hs2)) hs1
      rw [hlen] at hit
      exact ⟨s1, hs1, hit⟩
  obtain ⟨s1, hs1, hit1⟩ := hst
  exact RL.writesAt_of_line hR hj hpci fun _ env a ha => by
    rw [hit1]; exact hwr i x t hln s1 hs1 env a ha

/-- **The states of a straight-line run with their writes, for any address predicate**: the
`i`-th state is at line `j + i`, whose instruction's writes satisfy `P` by `LinesWrites`. -/
theorem RL.writesAtP_execLines {R : RL} (hR : R.Wf) {ls : List Line} {j : Nat} {s s' : Arm.ArmState}
    (hat : ∀ k ln, ls[k]? = some ln → R.fa.lines.toList[j + k]? = some ln)
    (hhook : ∀ i t, Line.ins i t ∈ ls → i.hooked = false)
    (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j)
    (herr : Arm.r .ERR s = .None) (hinter : InterOk (R.envOf j) ls s)
    (hrun : execLines (R.envOf j) ls s = some s') {P : BitVec 64 → Prop}
    (hwr : LinesWrites (R.envOf j) ls s P) :
    ∀ i < ls.length, R.WritesAtP P (iterN R.step i s) := by
  intro i hi
  have hpcs := iterN_execLines_pc (X := R.X) (H := R.H) hR.layout hR.lm hR.fit ls j s s' hat hhook
    hprog hpc herr hinter hrun
  obtain ⟨ln, hln⟩ : ∃ ln, ls[i]? = some ln := ⟨ls[i], List.getElem?_eq_getElem hi⟩
  have hmem := List.mem_of_getElem? hln
  obtain ⟨x, t, rfl⟩ := execLines_ins hrun _ hmem
  have hj : R.L[j + i]? = some (.ins x t) := hat i _ hln
  have hpci : Arm.r .PC (iterN R.step i s) = R.pcOf (j + i) := hpcs i (by omega)
  have hst : ∃ s1, execLines (R.envOf j) (ls.take i) s = some s1 ∧ iterN R.step i s = s1 := by
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · exact ⟨s, by simp [execLines], rfl⟩
    · obtain ⟨s1, hs1⟩ := execLines_take i hrun
      have hlen : (ls.take i).length = i := by simp; omega
      have hit := iterN_execLines (X := R.X) (H := R.H) hR.layout hR.lm hR.fit (ls.take i) j s s1
        (fun k ln hk => by
          rw [List.getElem?_take] at hk
          split at hk
          · exact hat k ln hk
          · cases hk)
        (fun i' t' hm => hhook i' t' (List.mem_of_mem_take hm)) hprog hpc herr
        (fun k hk0 hk s2 hs2 => hinter k hk0 (by omega) s2 (by
          rwa [List.take_take, Nat.min_eq_left (by omega)] at hs2)) hs1
      rw [hlen] at hit
      exact ⟨s1, hs1, hit⟩
  obtain ⟨s1, hs1, hit1⟩ := hst
  exact RL.writesAtP_of_line hR hj hpci fun _ env a ha => by
    rw [hit1]; exact hwr i x t hln s1 hs1 env a ha

theorem RL.goodXW_execLines {R : RL} (hR : R.Wf) {ls : List Line} {j : Nat} {s s' : Arm.ArmState}
    (hat : ∀ k ln, ls[k]? = some ln → R.fa.lines.toList[j + k]? = some ln)
    (hhook : ∀ i t, Line.ins i t ∈ ls → i.hooked = false)
    (htail : ∀ i t, Line.ins i t ∈ ls → i.tlsTail = false)
    (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j)
    (herr : Arm.r .ERR s = .None) (hsp : spOf s = R.spB) (hinter : InterOk (R.envOf j) ls s)
    (hrun : execLines (R.envOf j) ls s = some s')
    (hrd : LinesReads (R.envOf j) ls s R.ReadOk)
    (hwr : LinesWrites (R.envOf j) ls s fun a => ¬ R.G a) :
    ∀ i < ls.length, R.GoodXW (iterN R.step i s) :=
  RL.goodXW_execLinesG hR hat hhook htail hprog hpc herr (.inr hsp) hinter hrun hrd hwr

/-! ## Moves -/

/-- **A move on the machine with its writes** (`realizes_move`): the move's lines write only the
frame's slot area, which `G` avoids. -/
theorem realizes_moveW {R : RL} (hR : R.Wf) {s : Arm.ArmState} {b : Nat} {src dst : Loc}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    (hq : Q R s (.run ⟨b, .move src dst :: its, m, w⟩)) (hns : src.isSave = false) :
    ∃ n, Q R (iterN R.step n s) (.run ⟨b, its, upd m dst (m src), w⟩) ∧
      ∀ i < n, R.GoodXW (iterN R.step i s) := by
  by_cases hds : dst.isSave = true
  · exact ⟨0, q_save hds hq, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  obtain ⟨j, vb, items, pre, code, ls, ps1, ps2, T, hvb, hit, hsplit, hchk, hcode, hls, htr, hdrop,
    hpc, hst⟩ := hq
  obtain ⟨⟨c, wh, hcm⟩, hLs, hLd, hT, hchk'⟩ := move_facts hit hsplit hchk hns (by simpa using hds)
  obtain ⟨c1, c2, hc1, hc2, rfl⟩ := itemsCode_cons hcode
  rw [itemCode_move] at hc1
  obtain ⟨ls1, ls2, psm, h1, h2, rfl⟩ := codeLinesE_append _ _ _ _ _ hls
  obtain ⟨hvs, -, is, s', rfl, hmi, hex, hmo⟩ := lower_move (R.frameOk hR) R.ctx hcm
    hLs hLd hT hc1 hst.world hst.sp hst.align
  obtain ⟨ls1', hcl, hlen, hins, hpl, hrun, hint, hprog, herr⟩ :=
    run_oneLines R.ctx R.af is s s' (fun i hi => oneLine_of_moveInst R.ctx (hmi i hi)) hex hst.err
  rw [hcl ps1] at h1
  simp only [Except.ok.injEq, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  -- the lines at `j`
  have hZ : ∀ n, (ls2 ++ nxtOf R.af b)[1]? ≠ some (.label (.trap n)) := by
    intro n e
    have hm := List.mem_of_getElem? e
    rcases List.mem_append.1 hm with hm | hm
    · exact codeLinesE_noTrap _ _ _ _ h2 _ hm n rfl
    · simp only [nxtOf] at hm
      split at hm <;> simp at hm
  have hdrop' : R.L.drop j = ls1' ++ (relaxLines R.far (ftList (ls2 ++ nxtOf R.af b)) ++ T) := by
    rw [hdrop, List.append_assoc, ftR_plain_append _ _ _ hpl hZ, List.append_assoc]
  have hat : ∀ k ln, ls1'[k]? = some ln → R.fa.lines.toList[j + k]? = some ln := by
    intro k ln hk
    have := congrArg (·[k]?) hdrop'
    simp only [List.getElem?_drop, RL.L] at this
    rw [this, List.getElem?_append_left (List.getElem?_eq_some_iff.1 hk).1]
    exact hk
  have hins' : ∀ ln ∈ ls1', ∃ i t, ln = .ins i t := fun ln h => by
    obtain ⟨i, t, e, -⟩ := hins ln h; exact ⟨i, t, e⟩
  have hiter : iterN R.step ls1'.length s = s' :=
    iterN_execLines hR.layout hR.lm hR.fit ls1' j s s' hat
      (fun i t h => by obtain ⟨i', t', e, hh⟩ := hins _ h; cases e; exact hh)
      (by rw [hst.prog]) (by rw [hpc]; rfl) hst.err (hint _) (hrun _)
  -- the move's reads: bytes of the frame's slot area, which `G` avoids
  have hrd : LinesReads (R.envOf j) ls1' s R.ReadOk := by
    obtain ⟨is', e, hrd⟩ := moveInsts_reads (vc := R.vc) (rf := R.rf) R.ctx hcm hLs hLd hT hc1
      hst.align
    obtain rfl := (List.map_inj_right fun _ _ h => AInst.inst.inj h).1 e
    refine (linesReads_of_insts R.ctx R.af is s s'
      (fun i hi => oneLine_of_moveInst R.ctx (hmi i hi)) hex hrd ls1' ps1 ps1 (hcl ps1) _).mono ?_
    rintro a ⟨o, ho, rfl⟩
    exact .inl fun hG => RL.G_not_slot hR hG o ho (by rw [hst.sp])
  -- the move's writes: bytes of the frame's slot area, which `G` avoids
  have hwr : LinesWrites (R.envOf j) ls1' s fun a => ¬ R.G a := by
    obtain ⟨is', e, hwr⟩ := moveInsts_writes (vc := R.vc) (rf := R.rf) R.ctx hcm hLs hLd hT hc1
      hst.align
    obtain rfl := (List.map_inj_right fun _ _ h => AInst.inst.inj h).1 e
    refine (linesWrites_of_insts R.ctx R.af is s s'
      (fun i hi => oneLine_of_moveInst R.ctx (hmi i hi)) hex hwr ls1' ps1 ps1 (hcl ps1) _).mono ?_
    rintro a ⟨o, ho, rfl⟩
    exact fun hG => RL.G_not_slot hR hG o ho (by rw [hst.sp])
  refine ⟨ls1'.length, ⟨j + ls1'.length, vb, items, pre ++ [.move src dst], c2, ls2, ps1, ps2, T, hvb,
    hit, by rw [hsplit]; simp, hchk', hc2, h2, htr, ?_, ?_, ?_⟩, fun i hi => ?_⟩
  rotate_right
  · exact R.goodXW_execLines hR hat
      (fun i t h => by obtain ⟨i', t', e, hh⟩ := hins _ h; cases e; exact hh)
      (codeLinesE_noTlsTail (is.map .inst) ps1 ps1 ls1' (fun n rd tmp h => by
        simp only [List.mem_map] at h
        obtain ⟨a, ha, e⟩ := h
        cases e
        exact (oneLine_of_moveInst R.ctx (hmi _ ha)).not_tls n rd tmp rfl) (hcl ps1))
      (by rw [hst.prog]) hpc hst.err hst.sp (hint _) (hrun _) hrd hwr i hi
  · rw [← List.drop_drop, hdrop', List.drop_left]
  · rw [hiter, execLines_pc (hrun ⟨lineOffset R.fa.lines.toList j, (R.lm[·]?)⟩), hpc]
    simp only [RL.pcOf, RL.L]
    rw [lineOffset_drop_ins (by simpa [RL.L] using hdrop') hins', BitVec.add_assoc]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_add]
  · rw [hiter]
    have hsp' : spOf s' = R.spB := hmo.sp
    have hw' := hmo.world
    refine ⟨move_agree hst.store hvs hLs hmo.store, hw', herr, by rw [hprog, hst.prog], hsp',
      align_of_sp (by rw [hsp', hst.sp]) hst.align, fun hframe => ?_,
      code_frameKeep hR hmo.mem hst.code,
      fun a ha => (hmo.mem a (RL.G_not_slot hR ha)).trans (hst.gkeep a ha),
      fun hf => (xreg29_sw hst.world hw').trans (hst.fp hf)⟩
    rw [← hst.fplr hframe]
    apply read_mem_bytes_congr
    intro k hk
    exact hmo.mem _ (fun o ho => by
      have := fplr_outside hR hframe k hk o ho
      rwa [show R.spB = spOf s by rw [hst.sp]] at this ⊢)

/-! ## No fault -/

/-- **No fault at a state with the per-state facts and the writes**: under a memory map whose
non-writable bytes are kept (in `G`) and whose jump-table bytes are readable, the unhooked
instruction at the pc does not fault (`ArmFault.evsOk`): its reads are outside `G` or jump-table
bytes (D2), its writes outside `G` (`WritesAt`). -/
theorem RL.evsOk_of_goodXW {R : RL} {mp : ArmFault.MemMap} {u : Arm.ArmState}
    (hg : R.GoodXW u) (hG : ∀ a, (mp a).allows .W = false → R.G a)
    (hJT : ∀ j tg bs, R.L[j]? = some (.word tg bs) → ∀ i < 4,
      (mp (R.pcOf j + BitVec.ofNat 64 i)).allows .R = true)
    {j : Nat} {x : Insn} {t : Option Clif.TrapCode} (hj : R.L[j]? = some (.ins x t))
    (hpc : Arm.r .PC u = R.pcOf j) (hx : x.hooked = false) {env : Env} {a : Arm.ArmInst}
    (ha : x.toArmInst env = .ok a) :
    ArmFault.evsOk mp (Concurrency.ArmInstFoot.instEvs a u) = true := by
  refine E2E.ExecBytes.evsOk_of (fun p hp k hk => ?_) (fun p hp k hk => ?_)
  · rcases hg.1.reads j x t hj hpc hx env a ha p hp k hk with hnG | ⟨j', tg, bs, hj', i, hi, he⟩
    · have hw : (mp (p.1 + BitVec.ofNat 64 k)).allows .W = true := by
        cases hc : (mp (p.1 + BitVec.ofNat 64 k)).allows .W
        · exact absurd (hG _ hc) hnG
        · rfl
      revert hw; cases mp (p.1 + BitVec.ofNat 64 k) <;> simp [ArmFault.Perm.allows]
    · rw [he]; exact hJT j' tg bs hj' i hi
  · have := hg.2 j x t hj hpc hx env a ha p hp k hk
    cases hc : (mp (p.1 + BitVec.ofNat 64 k)).allows .W
    · exact absurd (hG _ hc) this
    · rfl

/-! ## The facts of an activation given by its data -/

/-- `RL.GoodXW` of the activation with these data. -/
def actGoodXW (vc : VCode) (rf : RFunc) (af : AFunc) (fa : FnAsm) (fb : FnBin) (base : BitVec 64)
    (s0 : Arm.ArmState) (X : ExtSem) (H : ArmHooks) (K : Nat) (G : BitVec 64 → Prop)
    (gv : Nat → String → Prop) (u : Arm.ArmState) : Prop :=
  RL.GoodXW ⟨vc, rf, af, fa, fb, {}, base, s0, X, H, {}, K, G, gv⟩ u

theorem RL.GoodXW.act {R : RL} {u : Arm.ArmState} (h : R.GoodXW u) :
    actGoodXW R.vc R.rf R.af R.fa R.fb R.base R.s0 R.X R.H R.K R.G R.gv u :=
  ⟨h.1.act, h.2⟩

theorem actGoodXW.toX {vc : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    {base : BitVec 64} {s0 : Arm.ArmState} {X : ExtSem} {H : ArmHooks} {K : Nat}
    {G : BitVec 64 → Prop} {gv : Nat → String → Prop} {u : Arm.ArmState}
    (h : actGoodXW vc rf af fa fb base s0 X H K G gv u) :
    actGoodX vc rf af fa fb base s0 X H K G gv u := h.1

end Backend.Proof
