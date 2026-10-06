import FV.E2E.RegLevelGoodX

/-!
# Straight-line instructions on the machine (M6)

`realizes_op_next`: at an instruction item whose `MStep` continues (`next`), an instruction
with `OperandsSound` whose expansion is plain straight-line code (`LinesOk`) is realised: the
machine runs its lines and reaches `Q` at the next item, with the store `MStep.op` builds.
-/

namespace Backend.Proof

open Backend E2E

/-- The expansion of an allocated instruction: emitter-state independent, unhooked plain
instruction lines whose intermediate states are error-free. -/
def LinesOk (ctx : FnCtx) (i : MInst) : Prop :=
  ∃ ls, (∀ ps, i.lines ctx ps = .ok (ls, ps)) ∧
    (∀ ln ∈ ls, ∃ x t, ln = .ins x t ∧ x.hooked = false) ∧ (∀ ln ∈ ls, ln.plain = true) ∧
    ∀ env s s', Arm.r .ERR s = .None → execLines env ls s = some s' → InterOk env ls s

theorem linesOk_of_oneLine {ctx : FnCtx} {i : MInst} (h : OneLine ctx i) : LinesOk ctx i := by
  obtain ⟨x, t, hl, hx, hp⟩ := h
  refine ⟨[.ins x t], hl, fun ln hln => ?_, fun ln hln => ?_, fun env s s' _ _ k h0 hk => ?_⟩
  · simp only [List.mem_singleton] at hln; exact ⟨x, t, hln, hx⟩
  · simp only [List.mem_singleton] at hln; rw [hln]; exact hp
  · simp at hk; omega

def locReg : Loc → Except String Reg
  | Loc.reg r => pure r
  | l => throw (toString "operand in " ++ toString (repr l))

theorem mapM_locReg : ∀ (L : List Loc) (R : List Reg), L.mapM locReg = .ok R → L = R.map .reg
  | [], R, h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h; subst h; rfl
  | l :: L, R, h => by
    rw [List.mapM_cons] at h
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    rename_i r hr
    split at h
    · cases h
    rename_i rs hrs
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    rw [mapM_locReg L rs hrs]
    cases l <;> simp [locReg, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at hr
    subst hr; rfl

theorem arr_mapM_locReg {allocs : Array Loc} {regs : Array Reg}
    (h : allocs.mapM locReg = .ok regs) : allocs = regs.map .reg := by
  have e := Array.toList_mapM (xs := allocs) (f := locReg)
  rw [h] at e
  simp only [Functor.map, Except.map] at e
  apply Array.toList_inj.1
  rw [Array.toList_map]
  exact mapM_locReg _ _ e.symm

theorem itemCode_op {fr : RAFrame} {vb : VBlock} {k : Nat} {allocs : Array Loc} {c1 : List AInst}
    (h : itemCode fr vb (.op k allocs) = .ok c1) :
    ∃ regs i i', allocs = regs.map Loc.reg ∧ vb.insts[k]? = some i ∧ i.assign regs = .ok i' ∧
      ((c1 = [AInst.inst i'] ∧ (∀ ds, i' ≠ .args ds) ∧ (∀ us, i' ≠ .rets us)) ∨ (∃ ds, i' = .args ds ∧ c1 = []) ∨
        (∃ us, i' = .rets us ∧ c1 = [AInst.epilogueRet])) := by
  unfold itemCode itemStep at h
  dsimp only at h
  simp only [bind, Except.bind, Functor.map, Except.map] at h
  split at h
  · cases h
  rename_i arr harr
  simp only [Except.ok.injEq] at h
  subst h
  split at harr
  · cases harr
  rename_i regs hregs
  split at harr
  · rename_i i hi
    split at harr
    · cases harr
    rename_i i' hi'
    refine ⟨regs, i, i', arr_mapM_locReg (by exact hregs), hi, hi', ?_⟩
    cases i' <;> simp only [pure, Except.pure, Except.ok.injEq] at harr <;> subst harr <;> simp
  · simp [throw, throwThe, MonadExceptOf.throw] at harr


/-- A frame location is kept by a step that keeps the frame (`FrameKeep`). -/
theorem locVal_frame_keep {fr : RAFrame} {D : Loc → Prop} {T : Prop} {sp0 : BitVec 64}
    {F : BitVec 64 → Prop} (hfr : FrameOk fr D T sp0 F) {s s' : Arm.ArmState}
    (hsp : spOf s = sp0) (hK : FrameKeep F s s') {l : Loc} (hD : D l) (hl : ∀ r, l ≠ .reg r) :
    locVal fr s' l = locVal fr s l := by
  cases ho : fr.offset l with
  | error e =>
    cases l with
    | reg r => exact absurd rfl (hl r)
    | stack k c => simp only [locVal, ho]
    | save r => simp only [locVal, ho]
  | ok o =>
    rw [locVal_frame_eq ho, locVal_frame_eq ho, hK.1]
    have hr : ∀ n, n ≤ slotBytes l → Arm.read_mem_bytes n (spOf s + BitVec.ofNat 64 o) s' =
        Arm.read_mem_bytes n (spOf s + BitVec.ofNat 64 o) s := fun n hn =>
      read_mem_bytes_congr n _ (fun k hk => hK.2 _ (by rw [hsp]; exact hfr.inF l o hD ho k (by omega)))
    rcases slotBytes_cases l with h | h
    · rw [if_pos h, if_pos h, hr 8 (by omega)]
    · rw [if_neg (by omega), if_neg (by omega), hr 16 (by omega)]

/-- The fp/lr slot lies in the frame addresses. -/
theorem fplr_inF {R : RL} (hR : R.Wf) (hframe : R.af.frame = true) :
    ∀ k < 16, R.FK (spv R.s0 - 16#64 + BitVec.ofNat 64 k) := by
  obtain ⟨⟨hfs, -⟩, -⟩ := lowerRFunc_ok hR.alloc
  have hst := hR.stack.frame.1
  have hd : frameDrop R.af = R.fr.total + 16 := by
    simp only [frameDrop, hframe, ite_true, hfs, RL.fr]
  intro k hk
  refine .inl ?_
  simp only [frameF, hd]
  rw [hfs] at hst
  simp only [RL.fr] at *
  have hm : (R.fr.total + 16) % 2 ^ 64 = R.fr.total + 16 := Nat.mod_eq_of_lt (by simp [RL.fr]; omega)
  have e : (spv R.s0 - 16#64 + BitVec.ofNat 64 k -
      (spv R.s0 - BitVec.ofNat 64 ((RAFrame.compute R.vc R.rf).total + 16))).toNat =
      (RAFrame.compute R.vc R.rf).total + k := by
    have : spv R.s0 - 16#64 + BitVec.ofNat 64 k - (spv R.s0 - BitVec.ofNat 64 ((RAFrame.compute R.vc R.rf).total + 16))
        = BitVec.ofNat 64 ((RAFrame.compute R.vc R.rf).total + k) := by
      apply BitVec.eq_of_toNat_eq
      have := (spv R.s0).isLt
      simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
      simp only [RL.fr] at hm
      rw [hm, Nat.mod_eq_of_lt (a := k) (by omega)]
      omega
    rw [this, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [e, hfs]
  exact .inr (.inl ⟨by omega, by omega⟩)

/-- The checker's facts at an instruction item. -/
theorem op_checked {R : RL} {vb : VBlock} {k : Nat} {allocs : Array Loc} {its : List RItem}
    (h : ItemsChecked R vb (.op k allocs :: its)) :
    ∃ (c : CheckCtx) (wh : String) (i : MInst) (ops : Array Operand), vb.insts[k]? = some i ∧ i.operands = .ok ops ∧
      c.checkStatic wh ops allocs i.clobbers = .ok () ∧ ItemsChecked R vb its := by
  obtain ⟨c, k0, a, out, hcr, hcv, hrun⟩ := h
  simp only [CheckCtx.runItems, bind, Except.bind] at hrun
  obtain ⟨-, hrun⟩ := Except.seq_ok hrun
  obtain ⟨hk, hrun⟩ := Except.seq_ok hrun
  have hk := ensure_ok hk
  simp only [beq_iff_eq] at hk
  subst hk
  split at hrun
  · cases hrun
  rename_i i hi
  split at hrun
  · cases hrun
  rename_i ops hops
  split at hrun
  · cases hrun
  rename_i a' hso
  exact ⟨c, _, i, ops, hi, hops, (stepOp_ok hso).1, ⟨c, k + 1, a', out, hcr, hcv, hrun⟩⟩

/-- **`GoodX` at an instruction line** from its fields: the `got`/`blr`/`call` obligations only
for the line's own instruction (one instruction at a pc, `RL.atLine_iff`). -/
theorem RL.goodX_line {R : RL} (hR : R.Wf) {u : Arm.ArmState} {j : Nat} {x : Insn}
    {t : Option Clif.TrapCode} (hj : R.L[j]? = some (.ins x t)) (hpc : Arm.r .PC u = R.pcOf j)
    (hx : x.tlsTail = false) (hgood : R.Good u) (herr : Arm.r .ERR u = .None)
    (hprog : u.program = R.fb.program R.base) (hnext : R.NextOk u (R.step u))
    (hgot : ∀ rd rn n, x = .ldrGotLo12 rd rn n → ∀ a, R.G a → u.mem a = R.s0.mem a)
    (hblr : ∀ r, x = .blr r → (R.vc.DestsInt → r ≠ .xzr) ∧ ∀ k w, R.fb.words[k]? = some w →
      Arm.read_mem_bytes 4 (R.base + BitVec.ofNat 64 (4 * k)) u = w)
    (hcall : ((∃ n, x = .bl n) ∨ ∃ r, x = .blr r) → R.CallPre u) (hrd : R.ReadsAt u) : R.GoodX u :=
  ⟨hgood, herr, hprog, ⟨x, ⟨j, t, hj, hpc⟩, hx⟩, hnext,
    fun rd rn n h => hgot rd rn n ((RL.atLine_iff hR hj hpc).1 h).symm,
    fun r h => hblr r ((RL.atLine_iff hR hj hpc).1 h).symm,
    fun x' h hc => hcall (((RL.atLine_iff hR hj hpc).1 h) ▸ hc), hrd⟩

/-- `RL.goodX_line`'s `call` obligation at a line that is no call. -/
theorem not_call_insn {x : Insn} (hx : ∀ n, x ≠ .bl n) (hx' : ∀ r, x ≠ .blr r) {P : Prop} :
    ((∃ n, x = .bl n) ∨ ∃ r, x = .blr r) → P := by
  rintro (⟨n, rfl⟩ | ⟨r, rfl⟩)
  · exact absurd rfl (hx n)
  · exact absurd rfl (hx' r)

/-- Unhooked lines of an allocated instruction hold no instruction of the TLS sequence past its
`ldr` (the TLS sequence starts with a hooked `adrp`). -/
theorem noTlsTail_of_unhooked {c : FnCtx} {m : MInst} {ps ps' : PState} {ls : List Line}
    (h : m.lines c ps = .ok (ls, ps')) (hh : ∀ i t, Line.ins i t ∈ ls → i.hooked = false) :
    ∀ i t, Line.ins i t ∈ ls → i.tlsTail = false := by
  by_cases hm : ∃ n rd tmp, m = .elfTlsGetAddr n rd tmp
  · obtain ⟨n, rd, tmp, rfl⟩ := hm
    simp only [MInst.lines] at h
    split at h
    · cases h
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact absurd (hh _ none (List.mem_cons_self ..)) (by simp [Insn.hooked])
  · exact lines_noTlsTail h fun n rd tmp e => hm ⟨n, rd, tmp, e⟩

/-- The machine runs the lines `ls1` of the allocated instruction `i'`, placed at line `j`, from a
state related to a store and world (`StRel`) and satisfying `pre`, to the state
`exec (R.envOf j) i'` gives, ending at the line after them (in some number of steps: one per
line, or fewer where the machine runs several lines as one hooked step, as for the TLSDESC
sequence of `tls_value`), every state before the end satisfying `GoodX`. -/
def RunsAs (R : RL) (exec : Env → MInst → Arm.ArmState → Option Arm.ArmState) (i' : MInst)
    (ls1 : List Line) (pre : Arm.ArmState → Prop) : Prop :=
  ∀ j T s m w s', R.L.drop j = ls1 ++ T → StRel R s m w → Arm.r .PC s = R.pcOf j → pre s →
    exec (R.envOf j) i' s = some s' →
    ∃ n, iterN R.step n s = s' ∧ Arm.r .PC s' = R.pcOf (j + ls1.length) ∧
      ∀ i < n, R.GoodX (iterN R.step i s)

theorem RunsAs.mono {R : RL} {exec : Env → MInst → Arm.ArmState → Option Arm.ArmState} {i' : MInst}
    {ls1 : List Line} {P Q : Arm.ArmState → Prop} (h : RunsAs R exec i' ls1 Q)
    (hPQ : ∀ u, P u → Q u) : RunsAs R exec i' ls1 P :=
  fun j T s m w s' hd hst hpc hp hex => h j T s m w s' hd hst hpc (hPQ s hp) hex

/-- `operandsSound_step` for the obligation at the allocated instructions `P` (`P i'`). -/
theorem operandsSound_stepI {F FK : BitVec 64 → Prop} {P : MInst → Prop}
    {exec : MInst → Arm.ArmState → Option Arm.ArmState}
    {sem : ISem CV Arm.ArmState} {i : MInst} {ctl : Ctl} {s : Arm.ArmState}
    (hs : OperandsSoundCtlAtI F FK P exec sem i ctl s)
    {c : CheckCtx} {wh : String} {ops : Array Operand} {regs : Array Reg} {i' : MInst}
    (hops : i.operands = .ok ops)
    (hst : c.checkStatic wh ops (regs.map Loc.reg) i.clobbers = .ok ())
    (hasg : i.assign regs = .ok i') (hP : P i') {m : Loc → CV} {w : Arm.ArmState}
    (hm : ∀ r, r.allocatable = true → m (.reg r) = regVal s r) (hw : SameWorld F s w)
    (hal : Arm.CheckSPAlignment s) (herr : Arm.r .ERR s = .None) {outs : List CV} {w' : Arm.ArmState}
    (hsem : sem i (((ops.zip (regs.map Loc.reg)).toList.filter (·.1.isUse)).map (m ·.2)) w =
      some (outs, w', ctl))
    (hlen : outs.length = ((ops.zip (regs.map Loc.reg)).toList.filter (·.1.isDef)).length) :
    ∃ s' m2, exec i' s = some s' ∧ SameWorld F s' w' ∧ FrameKeep FK s s' ∧
      Clobbered ckeep i.clobbers
        (writeM m ((((ops.zip (regs.map Loc.reg)).toList.filter (·.1.isDef)).zip outs).filter
          (·.1.1.isEarly))) m2 ∧
      (∀ r, r.allocatable = true →
        writeM m2 ((((ops.zip (regs.map Loc.reg)).toList.filter (·.1.isDef)).zip outs).filter
          (·.1.1.isLate)) (.reg r) = regVal s' r) ∧
      (∀ l, (∀ r, l ≠ .reg r) →
        writeM m2 ((((ops.zip (regs.map Loc.reg)).toList.filter (·.1.isDef)).zip outs).filter
          (·.1.1.isLate)) l = m l) := by
  rw [useVals_of_store hst hm] at hsem
  obtain ⟨s', hex, hW, hK, hdef, hoth, hcl⟩ :=
    hs c wh ops regs i' w outs w' hops hst hasg hP hw hal herr hsem
  obtain ⟨m2, hc2, hr2, hl2⟩ := operandsSound_post hst hm hlen hdef hoth hcl
  exact ⟨s', m2, hex, hW, hK, hc2, hr2, hl2⟩

/-- **An instruction item that falls through, on the machine** (`MStep.op` with control
`next`), for any execution function `exec` of allocated instructions the machine realises from
states satisfying `Pre` (`RunsAs`, given the checker's static facts of the allocation): given
the operand-view obligation for `exec` at the state (`OperandsSoundCtlAt`, keeping the frame
`R.FK`), the machine reaches `Q` at the next item, every state before it satisfying `GoodX`. -/
theorem realizes_op_coreX {R : RL} (hR : R.Wf) {s : Arm.ArmState} {b k : Nat} {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩))
    {vb : VBlock} {i : MInst} {ops : Array Operand} {outs : List CV} {w' : Arm.ArmState}
    (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some i) (hops : i.operands = .ok ops)
    (hsz : allocs.size = ops.size)
    (hsem : R.sem i (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w =
      some (outs, w', .next))
    (hlen : outs.length = ((ops.zip allocs).toList.filter (·.1.isDef)).length)
    (hk : k + 1 < vb.insts.size)
    {exec : Env → MInst → Arm.ArmState → Option Arm.ArmState}
    (hOS : ∀ env, OperandsSoundCtlAtI R.F R.FK
      (fun i' => ∃ regs, allocs = regs.map Loc.reg ∧ i.assign regs = .ok i') (exec env) R.sem i .next s)
    {Pre : Arm.ArmState → Prop} (hpre : Pre s)
    (hL : ∀ regs i', i.assign regs = .ok i' → allocs = regs.map Loc.reg →
      (∃ env s s', exec env i' s = some s') →
      (∃ (c : CheckCtx) (wh : String), c.checkStatic wh ops (regs.map Loc.reg) i.clobbers = .ok ()) →
      ∃ ls1, (∀ ps, i'.lines R.ctx ps = .ok (ls1, ps)) ∧
      (∀ ln ∈ ls1, ln.plain = true) ∧ (∀ ds, i' ≠ .args ds) ∧ (∀ us, i' ≠ .rets us) ∧
      RunsAs R exec i' ls1 Pre)
    (hW' : Arm.r .ERR w' = .None ∧ w'.program = w.program) :
    ∃ n c'', MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c'' ∧
      Q R (iterN R.step n s) c'' ∧ ∀ i < n, R.GoodX (iterN R.step i s) := by
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
  -- the instruction's effect
  have hm : ∀ r, r.allocatable = true → m (.reg r) = regVal s r := fun r hr =>
    hst.store (.reg r) (fun r' e => by cases e; exact hr) trivial
  obtain ⟨s', m2, hex, hW, hK, hc2', hr2, hl2⟩ := operandsSound_stepI (hOS (R.envOf j)) hops hstat
    hasg ⟨regs, rfl, hasg⟩ hm hst.world hst.align hst.err hsem hlen
  obtain ⟨ls1, hl1, hpl, hna, hnr, hruns⟩ := hL regs i' hasg rfl ⟨_, _, _, hex⟩ ⟨c, wh, hstat⟩
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
  -- the lines at `j`
  have hZ : ∀ n, (ls2 ++ nxtOf R.af b)[1]? ≠ some (.label (.trap n)) := by
    intro n e
    have hm := List.mem_of_getElem? e
    rcases List.mem_append.1 hm with hm | hm
    · exact codeLinesE_noTrap _ _ _ _ h2 _ hm n rfl
    · simp only [nxtOf] at hm
      split at hm <;> simp at hm
  have hdrop' : R.L.drop j = ls1 ++ (relaxLines R.far (ftList (ls2 ++ nxtOf R.af b)) ++ T) := by
    rw [hdrop, List.append_assoc, ftR_plain_append _ _ _ hpl hZ, List.append_assoc]
  obtain ⟨nst, hiter, hpc', hgood⟩ := hruns j _ s m w s' hdrop' hst hpc hpre hex
  refine ⟨nst, _, MStep.op hvb hi hops hsz hsem hlen (HavocOuts.refl _ _ _) hc2' (MNext.next hk), ?_,
    hgood⟩
  have hfr := R.frameOkK hR
  refine ⟨j + ls1.length, vb, items, pre ++ [.op k (regs.map Loc.reg)], c2, ls2, ps1, ps2, T, hvb,
    hit, by rw [hsplit]; simp, hchk', hc2, h2, htr, ?_, ?_, ?_⟩
  · rw [← List.drop_drop, hdrop', List.drop_left]
  · rw [hiter, hpc']
  · rw [hiter]
    have hsp' : spOf s' = R.spB := hK.1.trans hst.sp
    have herr' : Arm.r .ERR s' = .None := by
      rw [hW.1 .ERR (by simp [Masked]), hW'.1]
    refine ⟨fun l hl hL => ?_, hW, herr', ?_, hsp', align_of_sp (by rw [hsp', hst.sp]) hst.align,
      fun hframe => ?_, code_keep hR.prog0 hst.code fun a ha => hK.2 a (.inl (.inr (.inr ha))),
      fun a ha => (hK.2 a (.inr ha)).trans (hst.gkeep a ha)⟩
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
      exact read_mem_bytes_congr _ _ (fun k hk => hK.2 _ (fplr_inF hR hframe k hk))

/-- Straight-line lines (`LinesOk`) run on the machine as `execMInst` runs them. -/
theorem runsAs_of_linesOk {R : RL} (hR : R.Wf) {i' : MInst} {ls1 : List Line}
    (hl1 : ∀ ps, i'.lines R.ctx ps = .ok (ls1, ps))
    (hins : ∀ ln ∈ ls1, ∃ x t, ln = .ins x t ∧ x.hooked = false)
    (hint : ∀ env s s', Arm.r .ERR s = .None → execLines env ls1 s = some s' → InterOk env ls1 s) :
    RunsAs R (fun env => execMInst R.ctx env) i' ls1 fun u => ∀ env, LinesReads env ls1 u R.ReadOk := by
  intro j T s _ _ s' hdrop' hst hpc hrd hex
  have hprog := hst.prog
  have herr := hst.err
  have hat : ∀ k ln, ls1[k]? = some ln → R.fa.lines.toList[j + k]? = some ln := by
    intro k ln hk
    have := congrArg (·[k]?) hdrop'
    simp only [List.getElem?_drop, RL.L] at this
    rw [this, List.getElem?_append_left (List.getElem?_eq_some_iff.1 hk).1]
    exact hk
  have hins' : ∀ ln ∈ ls1, ∃ i t, ln = .ins i t := fun ln h => by
    obtain ⟨i, t, e, -⟩ := hins ln h; exact ⟨i, t, e⟩
  have hrun : execLines (R.envOf j) ls1 s = some s' := by
    simp only [execMInst, hl1] at hex; exact hex
  have hhook : ∀ i t, Line.ins i t ∈ ls1 → i.hooked = false := fun i t h => by
    obtain ⟨i', t', e, hh⟩ := hins _ h; cases e; exact hh
  refine ⟨ls1.length, iterN_execLines hR.layout hR.lm hR.fit ls1 j s s' hat hhook
      hprog (by rw [hpc]; rfl) herr (hint _ _ _ herr hrun) hrun, ?_,
    R.goodX_execLines hR hat hhook (noTlsTail_of_unhooked (hl1 {}) hhook) hprog hpc herr hst.sp
      (hint _ _ _ herr hrun) hrun (hrd _)⟩
  rw [execLines_pc hrun, hpc]
  simp only [RL.pcOf, RL.L]
  rw [lineOffset_drop_ins (by simpa [RL.L] using hdrop') hins', BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add]

/-- **A straight-line instruction on the machine** (`MStep.op` with control `next`): given
`OperandsSound` for the instruction, `LinesOk` for its allocated form and the reads of its
allocated lines (outside the frame addresses whenever `csem` gives a result, `formOk_reads`), the
machine runs its lines and reaches `Q` at the next item, every state before it satisfying `GoodX`. -/
theorem realizes_op_next {R : RL} (hR : R.Wf) {s : Arm.ArmState} {b k : Nat} {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩))
    {vb : VBlock} {i : MInst} {ops : Array Operand} {outs : List CV} {w' : Arm.ArmState}
    (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some i) (hops : i.operands = .ok ops)
    (hsz : allocs.size = ops.size)
    (hsem : R.sem i (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w =
      some (outs, w', .next))
    (hlen : outs.length = ((ops.zip allocs).toList.filter (·.1.isDef)).length)
    (hk : k + 1 < vb.insts.size)
    (hOS : ∀ env, OperandsSound R.F (execMInst R.ctx env) (csem R.F R.ctx R.X) i)
    (hL : ∀ regs i', i.assign regs = .ok i' →
      LinesOk R.ctx i' ∧ (∀ ds, i' ≠ .args ds) ∧ (∀ us, i' ≠ .rets us))
    (hRd : ∀ {regs : Array Reg} {i' : MInst} {ls : List Line} {ps ps' : PState} {u v : Arm.ArmState}
      {r : List CV × Arm.ArmState × Ctl}, AllocOk ops regs → i.assign regs = .ok i' →
      i'.lines R.ctx ps = .ok (ls, ps') → SameWorld R.F u v → Arm.r .ERR v = .None →
      Arm.CheckSPAlignment v → csem R.F R.ctx R.X i (useVals ops regs u) v = some r → ∀ env,
      LinesReads env ls u (fun a => ¬ R.F a))
    (hW' : Arm.r .ERR w' = .None ∧ w'.program = w.program) :
    ∃ n c'', MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c'' ∧
      Q R (iterN R.step n s) c'' ∧ ∀ i < n, R.GoodX (iterN R.step i s) := by
  have hpre : ∀ regs i' ls1, allocs = regs.map Loc.reg → i.assign regs = .ok i' →
      (∀ ps, i'.lines R.ctx ps = .ok (ls1, ps)) → ∀ env, LinesReads env ls1 s R.ReadOk := by
    intro regs i' ls1 hal' hasg hl1 env
    obtain ⟨j, vb0, items, pre, code, ls, ps1, ps2, T, hvb0, hit, hsplit, hchk, hcode, hls, htr, hdrop,
      hpc, hst⟩ := hq
    rw [hvb] at hvb0
    cases hvb0
    obtain ⟨c, wh, i2, ops2, hi2, hops2, hstat, -⟩ := op_checked hchk
    rw [hi] at hi2
    cases hi2
    rw [hops] at hops2
    cases hops2
    subst hal'
    have hm : ∀ r, r.allocatable = true → m (.reg r) = regVal s r := fun r hr =>
      hst.store (.reg r) (fun r' e => by cases e; exact hr) trivial
    rw [useVals_of_store hstat hm] at hsem
    have herrw : Arm.r .ERR w = .None := by
      rw [← hst.world.1 .ERR (by simp [Masked]), hst.err]
    have halw : Arm.CheckSPAlignment w := by
      simpa [Arm.CheckSPAlignment, Arm.read_gpr, (hst.world.1 (.GPR 31#5) (by simp [Masked])).symm]
        using hst.align
    exact (hRd (allocOk_of_checkStatic hstat) hasg (hl1 {}) hst.world herrw halw (R.sem_csem hsem)
      env).mono fun a ha => .inl fun hG => ha (RL.FK_F (.inr hG))
  exact realizes_op_coreX hR hq hvb hi hops hsz hsem hlen hk (exec := fun env => execMInst R.ctx env)
    (fun env => (((hOS env).at (fun _ => RL.FK_F) s).toI _).v R.gv) (Pre := fun u =>
      ∀ regs i' ls1, allocs = regs.map Loc.reg → i.assign regs = .ok i' →
        (∀ ps, i'.lines R.ctx ps = .ok (ls1, ps)) → ∀ env, LinesReads env ls1 u R.ReadOk) hpre
    (fun regs i' hasg hal' _ _ => by
      obtain ⟨⟨ls1, hl1, hins, hpl, hint⟩, hna, hnr⟩ := hL regs i' hasg
      exact ⟨ls1, hl1, hpl, hna, hnr, (runsAs_of_linesOk hR hl1 hins hint).mono
        fun u hu env => hu regs i' ls1 hal' hasg hl1 env⟩) hW'

end Backend.Proof
