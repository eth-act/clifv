import FV.E2E.RegLevelU
import FV.E2E.RegLevelCallSite

/-!
# A raising `try_call` on the machine: the landing pad (S10e, #232)

`realizes_tryCall_raiseU`: from `Q` at a `tryCall` item whose callee raises (`XRaise`), one step
of the machine with unwinding (`Unw.ArmStepU`: the callee raises, the personality reads the
emitted call-site table and installs the first handler's landing pad) reaches `Q` at the entry
of the handler's successor (the landing-pad edge block, whose label line is at the pad's
offset: `pad_label`), the defs of the call holding the payload (x0 = the exception object,
x1 = 0; every other allocatable register as the unwinder restored it, x0/x1 holding nothing
live by `tryUOk`'s `payloadRegOk`): the raising `tryCall` case of `realizes_allU`, for any
semantics with `csemU`'s raising-`tryCall` clause (`TryRaiseSem`), the trace state the
raising-call state (`RLU.RaiseX`).

What it reads about the emitted code and tables:
* `LsdaAt`: the tables the unwinder reads hold the emitted call-site table (`CallSitesOk`);
* `PadsNonzero`: the landing pads of the table are at non-zero offsets (the personality treats
  landing pad 0 as none); decidable check `padsNonzeroB` (`padsNonzero_of_check`);
* `SiteAt`: the call-site bridge: at a call item the pc is at the call line whose return
  offset `callSites` pairs with this call; `siteAt_of_check` from `q_callSite`/
  `q_callSite_last` under the check `lastCallsOk`.
* Non-vacuity: `UTryWitness.checks` (both checks pass on S10c's witness function).
-/

namespace Backend.Proof

open Backend E2E Backend.Proof.UnwindTables

/-- The tables the unwinder reads hold the emitted call-site table of the activation's
function. -/
def LsdaAt (R : RLU) : Prop :=
  ∃ sites, CallSitesOk R.af R.fa sites ∧ R.T.lsda = some (sites.map (·.entry))

/-- Every `try_call` landing pad of the emitted call-site table is at a non-zero offset. -/
def PadsNonzero (af : AFunc) (fa : FnAsm) : Prop :=
  ∀ ti ret e, (some ti, ret) ∈ af.calls.zip (scanLines fa.lines.toList 0 [] []).2 →
    entryFor (scanLines fa.lines.toList 0 [] []).1 (some ti, ret) = some e → e.pad ≠ 0

/-- **The call-site bridge** at the call items of the activation: the pc is at the call line,
whose return offset `callSites` pairs with this call (`none` for a `call`, `some ti` for a
`tryCall`). -/
def SiteAt (R : RL) : Prop :=
  ∀ (s : Arm.ArmState) (b k : Nat) (allocs : Array Loc) (its : List RItem) (m : Loc → CV)
    (w : Arm.ArmState) (vb : VBlock) (i : MInst) (info : CallInfo) (c : Option TryInfo),
    Q R s (.run ⟨b, .op k allocs :: its, m, w⟩) → R.vc.blocks[b]? = some vb →
    vb.insts[k]? = some i → ((i = .call info ∧ c = none) ∨ ∃ ti, i = .tryCall info ti ∧ c = some ti) →
    ∃ j x, R.L[j]? = some (.ins x none) ∧ Arm.r .PC s = R.pcOf j ∧
      ((∃ n, x = .bl n) ∨ ∃ r, x = .blr r) ∧
      (c, lineOffset R.L j + 4) ∈ R.af.calls.zip (scanLines R.fa.lines.toList 0 [] []).2

/-! ## List facts -/

theorem mem_zip_filter_map {α β γ : Type} (P : α → Bool) (g : α → γ) :
    ∀ (L : List (α × β)) (q : (α × β) × γ),
      q ∈ (L.filter (fun p => P p.1)).zip (((L.map Prod.fst).filter P).map g) → q.2 = g q.1.1
  | [], _, h => by simp at h
  | a :: L, q, h => by
    by_cases ha : P a.1 = true
    · simp only [List.filter_cons, ha, ite_true, List.map_cons, List.zip_cons_cons,
        List.mem_cons] at h
      rcases h with rfl | h
      · rfl
      · exact mem_zip_filter_map P g L q h
    · simp only [List.filter_cons, ha, List.map_cons, Bool.false_eq_true, ite_false] at h
      exact mem_zip_filter_map P g L q h

theorem zip_toList_map_fst {α β : Type} (xs : Array α) (ys : Array β) (h : xs.size = ys.size) :
    (xs.zip ys).toList.map Prod.fst = xs.toList := by
  rw [Array.toList_zip, List.map_fst_zip]
  simp [h]

/-! ## Registers after the landing pad's install -/

theorem regVal_x01 {t : Arm.ArmState} {obj : BitVec 64} {r : Reg}
    (ha : r.allocatable = true) (h0 : r ≠ .x 0) (h1 : r ≠ .x 1) :
    regVal (Arm.w (.GPR 1#5) 0 (Arm.w (.GPR 0#5) obj t)) r = regVal t r := by
  rcases allocatable_cases ha with ⟨n, rfl, hn, -⟩ | ⟨n, rfl, hn⟩
  · have hn0 : n ≠ 0 := fun e => h0 (by rw [e])
    have hn1 : n ≠ 1 := fun e => h1 (by rw [e])
    simp only [regVal, rnum]
    rw [Arm.r_of_w_different (by
        simp only [ne_eq, Arm.StateField.GPR.injEq]
        exact Unw.ofNat5_ne (a := n) (b := 1) (by omega) (by omega) hn1),
      Arm.r_of_w_different (by
        simp only [ne_eq, Arm.StateField.GPR.injEq]
        exact Unw.ofNat5_ne (a := n) (b := 0) (by omega) (by omega) hn0)]
  · simp only [regVal]
    rw [Arm.r_of_w_different (by simp), Arm.r_of_w_different (by simp)]

theorem regVal_x01_x0 (t : Arm.ArmState) (obj : BitVec 64) :
    regVal (Arm.w (.GPR 1#5) 0 (Arm.w (.GPR 0#5) obj t)) (.x 0) = ofX obj := by
  simp only [regVal, rnum, ofX]
  rw [Arm.r_of_w_different (by decide), Arm.r_of_w_same]

theorem regVal_x01_x1 (t : Arm.ArmState) (obj : BitVec 64) :
    regVal (Arm.w (.GPR 1#5) 0 (Arm.w (.GPR 0#5) obj t)) (.x 1) = ofX 0 := by
  simp only [regVal, rnum, ofX]
  rw [Arm.r_of_w_same]

theorem frameKeep_x01 {F : BitVec 64 → Prop} {s t : Arm.ArmState} {obj : BitVec 64}
    (h : FrameKeep F s t) :
    FrameKeep F s (Arm.w (.GPR 1#5) 0 (Arm.w (.GPR 0#5) obj t)) := by
  refine ⟨?_, fun a ha => ?_, ?_⟩
  · simp only [spOf]
    rw [Arm.r_of_w_different (by decide), Arm.r_of_w_different (by decide)]
    exact h.1
  · rw [Arm.mem_w_of_mem_eq rfl, Arm.mem_w_of_mem_eq rfl]
    exact h.2.1 a ha
  · rw [Arm.r_of_w_different (by decide), Arm.r_of_w_different (by decide)]
    exact h.2.2

theorem sameWorld_x01 {F : BitVec 64 → Prop} {t w : Arm.ArmState} {obj : BitVec 64}
    (h : SameWorld F t w) :
    SameWorld F (Arm.w (.GPR 1#5) 0 (Arm.w (.GPR 0#5) obj t)) w :=
  SameWorld.w_left (by simp [Masked]) (SameWorld.w_left (by simp [Masked]) h)

theorem err_x01 {t : Arm.ArmState} {obj : BitVec 64} (h : Arm.r .ERR t = .None) :
    Arm.r .ERR (Arm.w (.GPR 1#5) 0 (Arm.w (.GPR 0#5) obj t)) = .None := by
  rw [Arm.r_of_w_different (by simp), Arm.r_of_w_different (by simp)]
  exact h

/-- A fixed def operand's allocated register is its fixed register. -/
theorem def_fixed_reg {cc : CheckCtx} {wh : String} {ops : Array Operand} {regs : Array Reg}
    {clob : List Reg} (hst : cc.checkStatic wh ops (regs.map Loc.reg) clob = .ok ())
    {o : Operand} (ho : o ∈ ops.toList) (hd : o.isDef = true) {r : Reg} (hc : o.con = .fixed r) :
    ∃ p ∈ (ops.zip regs).toList, p.1.isDef = true ∧ p.2 = r := by
  obtain ⟨hsz, hfx, -, -⟩ := checkStatic_facts hst
  simp only [Array.size_map] at hsz
  rw [← zip_toList_map_fst ops regs hsz] at ho
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ho
  refine ⟨p, hp, hd, ?_⟩
  have hp' : (p.1, Loc.reg p.2) ∈ (ops.zip (regs.map Loc.reg)).toList := by
    rw [pairs_regs]; exact List.mem_map_of_mem hp
  have := (hfx _ hp').2 r hc
  simpa using this

/-! ## The landing pad -/

/-- The landing pad the call-site table gives a `try_call` whose first handler is `tag 0`/`tag 1`
of label `l` is the offset of `l`'s label line. -/
theorem pad_label {R : RL} (hR : R.Wf) {ti : TryInfo} {ret : Nat} {e : Unw.CallSiteEntry}
    {h : TryHandler} {hs : List TryHandler} (hti : ti.handlers = h :: hs) {l : Label}
    (hl : h = .tag 0 l ∨ h = .tag 1 l)
    (he : entryFor (scanLines R.fa.lines.toList 0 [] []).1 (some ti, ret) = some e) :
    ∃ jl, R.L[jl]? = some (.label (.block l)) ∧ lineOffset R.L jl = e.pad := by
  have hlk : (scanLines R.fa.lines.toList 0 [] []).1.lookup l = some e.pad := by
    simp only [entryFor, handlersOf, hti, handlerEntry?] at he
    rcases hl with rfl | rfl <;> simp only [TryHandler.label] at he <;>
      cases hk : (scanLines R.fa.lines.toList 0 [] []).1.lookup l <;> simp [hk] at he <;>
      rw [← he]
  exact (labelOffsets_spec hR.lm _ _).mp (scanLines_labelOffsets hR.lm hlk)

/-- **A raising `try_call` on the machine, with the raising-call state's step facts**: the callee
raises, the personality installs the first handler's landing pad, and the machine is at the
landing-pad edge block with the payload in the call's defs, the raising-call state `RaiseXF`
(`RealizesTryRaiseP … R.GoodXUF`), for any semantics with `csemU`'s raising-`tryCall` clause
(`TryRaiseSem`: `R.semU`, `csemU`, the dead-cleanup chain's value semantics). -/
theorem realizes_tryCall_raiseUF {R : RLU} (hR : R.Wf) {semU : Sem}
    (hU : CalleeUnwOkG R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.XR R.U R.vc.CallSite R.gv)
    (hsemT : TryRaiseSem R.XR semU) (hgot : GotSem R.gv R.X semU)
    (hT : LsdaAt R) (hpad : PadsNonzero R.af R.fa) (hsite : SiteAt R.toRL) :
    RealizesTryRaiseP R semU R.GoodXUF := by
  intro s b k allocs its m w vb info ti ops c' obj w2 hq _hA hvb hi hops hraise hm
  obtain ⟨j0, items, pre, regs, i', c1, c2, ls1, ls2, ps1, psm, ps2, T, cc, wh, ops', hal, hit,
    hsplit, hasg, hc1', hops', hstat, hchk', hcode2, h1, h2, htr, hdrop, hpc, hst⟩ := q_op hq hvb hi
  rw [hops] at hops'; cases hops'
  subst hal
  have hm' : ∀ r, r.allocatable = true → m (.reg r) = regVal s r := fun r hr =>
    hst.store (.reg r) (fun r' e => by cases e; exact hr) trivial
  have huses := useVals_of_store hstat hm'
  rw [huses] at hraise
  have hopsC : (MInst.call info).operands = .ok ops := by
    rw [← operands_tryCall_call info ti]; exact hops
  have hsz0 := (checkStatic_facts hstat).1
  simp only [Array.size_map] at hsz0
  cases hm with
  | @op _ _ _ _ _ _ vb' i2 ops2 outs outs' w' ctl m2 _ hvb' hi' hops2 hsz hsem hlen hho hcl hn =>
  rw [hvb] at hvb'; cases hvb'
  rw [hi] at hi'; cases hi'
  rw [hops] at hops2; cases hops2
  have hsem0 := hsem
  rw [huses] at hsem0
  have hgg := (hgot _ _ _ _).2 ti hsem0
  obtain ⟨hok, heq⟩ := hsemT _ _ _ _ _ _ _ hsem0 hraise
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl, rfl⟩ := heq
  simp only [tryUOk, Bool.and_eq_true, Bool.not_eq_true'] at hok
  obtain ⟨⟨⟨⟨hfirst, -⟩, hdefs01⟩, hp0⟩, hp1⟩ := hok
  -- the first handler
  obtain ⟨hd0, hs0, hfirstEq, l, hl⟩ : ∃ h hs, ti.handlers = h :: hs ∧
      ∃ l, h = .tag 0 l ∨ h = .tag 1 l := by
    revert hfirst
    rcases ti.handlers with _ | ⟨h, hs⟩
    · simp [firstHandlerOk]
    · intro hf
      refine ⟨h, hs, rfl, ?_⟩
      rcases h with ⟨_ | _ | n, l⟩ | l <;> simp_all [firstHandlerOk]
  -- the raising callee (the contract)
  have hsite0 : R.vc.CallSite info := ⟨b, vb, k, hvb, .inr ⟨ti, hi⟩⟩
  have hcpc := callAt_of_q hq hvb hi tryCall_hcall regs i' rfl hasg
  have hraiseU := hU.os info (.tryCall info ti) hsite0 (.inr ⟨ti, rfl⟩) s
    (by rw [hst.sp]; exact RL.K_le hR) (fun a ha => by rw [hst.sp] at ha; exact RL.below_F ha)
    hst.gkeep cc wh ops regs i' w hops hstat hasg hcpc hst.world hst.align hst.err hgg
  obtain ⟨t, hUr, hW, hFK, herrt, hprogt, hoth, hkeep⟩ := hraiseU obj _ hraise
  obtain ⟨hstep1, hRX, hdesc, hxzr⟩ := RLU.stepU_q_raiseF hR hq hvb hi (.inr ⟨ti, rfl⟩) hUr
  -- the personality: the first handler's landing pad
  obtain ⟨j, x', hj, hpcj, -, hmem⟩ := hsite s b k _ its m w vb _ info (some ti) hq hvb hi
    (.inr ⟨ti, rfl, rfl⟩)
  obtain ⟨sites, hcs, hlsda⟩ := hT
  obtain ⟨e, he, hpers⟩ := Unw.personality_callSite hcs hmem
  simp only [hpad ti _ e hmem he, ↓reduceIte] at hpers
  have hne : R.fb.words.toList ≠ [] := by
    obtain ⟨_, wd, hw, hk⟩ := FnAsm.layout_word hR.layout hR.lm hj rfl
    intro h
    have : R.fb.words.size = 0 := by simpa using congrArg List.length h
    simp [this] at hk
  have hpb : progBase s = R.base := progBase_eq (by rw [hst.prog]; rfl) hne
  have hfit : lineOffset R.L j + 4 ≤ 2 ^ 64 := by
    have h1' := lineOffset_succ R.L j _ hj
    have h2' := lineOffset_le_size R.L (j + 1)
    have h3' := layout_sum hR.layout
    have h4' := hR.fit
    simp only [Line.size, RL.L] at h1' h2' h3' ⊢
    omega
  have hoff : (Arm.r .PC s + 4 - 1 - progBase s).toNat = lineOffset R.L j + 4 - 1 := by
    rw [hpcj, hpb]
    simp only [RL.pcOf]
    have : R.base + BitVec.ofNat 64 (lineOffset R.L j) + 4 - 1 - R.base =
        BitVec.ofNat 64 (lineOffset R.L j + 3) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat,
        show (4 : BitVec 64).toNat = 4 from rfl, show (1 : BitVec 64).toNat = 1 from rfl]
      have := R.base.isLt
      omega
    rw [this, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  have hstepU : R.stepU s = Arm.w .PC (progBase s + BitVec.ofNat 64 e.pad)
      (Arm.w (.GPR 1#5) 0 (Arm.w (.GPR 0#5) obj t)) := by
    rw [hstep1]
    apply Unw.unwindAt_install
    rw [hlsda, hoff]
    exact hpers
  -- the landing pad's label line
  obtain ⟨jl, hjl, hjlo⟩ := pad_label hR hfirstEq hl he
  -- the successor: the first handler's block
  have hnone : havocFrom (MInst.tryCall info ti) (.goto 0) = none := by
    simp [havocFrom, MInst.keptDefs, MInst.isBranch, MInst.normalDead, hfirstEq]
  obtain rfl := hho.2.1 hnone
  cases hn with
  | @goto _ st items' hk1 hsucc hitems =>
  obtain ⟨c, ins, _, hc, -⟩ := hR.check
  obtain ⟨preds, hcfg⟩ := hc.cfg
  obtain ⟨t0, ts, hback, hss, hlab⟩ := cfg_block hcfg hvb
  have hti : t0 = .tryCall info ti := by
    rw [Array.back?_eq_getElem?, show vb.insts.size - 1 = k by omega, hi] at hback
    cases hback; rfl
  subst hti
  have hsucc' := hsucc
  simp only [succOf, hcfg, hss, Option.bind_some] at hsucc'
  obtain ⟨vs, hvs, hlj⟩ := hlab _ st hsucc'
  have hst0 : st ≠ 0 := ctlCheck_succ ((lowerRFunc_ok hR.alloc).2.2) hsucc
  have hvl : vs.label = l := by
    simp only [MInst.targets, hfirstEq, List.map_cons, List.cons_append,
      List.getElem?_cons_zero, Option.some.injEq] at hlj
    rcases hl with rfl | rfl <;> exact hlj.symm
  -- the machine after the install: the payload registers
  have hFK' : FrameKeep R.FK s (Arm.w (.GPR 1#5) 0 (Arm.w (.GPR 0#5) obj t)) :=
    frameKeep_x01 ⟨hFK.1, fun a ha => hFK.2.1 a ⟨RL.FK_F ha, by rw [hst.sp]; exact RL.FK_not_below hR ha⟩,
      hFK.2.2⟩
  have hlenD : (payloadOuts (.call info) obj).length =
      ((ops.zip regs).toList.filter (·.1.isDef)).length := by
    rw [hlen, pairs_regs, List.filter_map, List.length_map]; rfl
  have hlen' : (payloadOuts (.call info) obj).length =
      ((ops.zip (regs.map Loc.reg)).toList.filter (·.1.isDef)).length := hlen
  -- the defs: x0 := obj, x1 := 0
  have hdcons : ∀ o ∈ ops.toList, o.isDef = true → o.con = .fixed (.x 0) ∨ o.con = .fixed (.x 1) := by
    intro o ho hd
    have hmem : o.con ∈ defCons (.call info) := by
      simp only [defCons, hopsC]
      exact List.mem_map_of_mem (List.mem_filter.mpr ⟨ho, hd⟩)
    have := List.all_eq_true.mp hdefs01 _ hmem
    simpa using this
  have hdef : ∀ p ∈ defRegs ops regs (payloadOuts (.call info) obj),
      regVal (Arm.w (.GPR 1#5) 0 (Arm.w (.GPR 0#5) obj t)) p.1.2 = p.2 := by
    intro p hp
    have hp2 : p.2 = (fun c => if c = .fixed (.x 0) then ofX obj else ofX 0) p.1.1.con := by
      refine mem_zip_filter_map Operand.isDef
        (fun o => if o.con = .fixed (.x 0) then ofX obj else ofX 0) (ops.zip regs).toList p ?_
      rw [zip_toList_map_fst ops regs hsz0]
      simpa [defRegs, payloadOuts, defCons, hopsC, List.map_map, Function.comp_def] using hp
    have hp1 : p.1 ∈ (ops.zip regs).toList ∧ p.1.1.isDef = true := by
      have := List.of_mem_zip hp
      exact List.mem_filter.mp this.1 |>.imp id (by simp)
    have hfx := (checkStatic_facts hstat).2.1 (p.1.1, Loc.reg p.1.2)
      (by rw [pairs_regs]; exact List.mem_map_of_mem hp1.1)
    have ho : p.1.1 ∈ ops.toList := by
      rw [← zip_toList_map_fst ops regs hsz0]; exact List.mem_map_of_mem hp1.1
    rcases hdcons _ ho hp1.2 with hc0 | hc1
    · have := hfx.2 _ hc0
      simp only [Loc.reg.injEq] at this
      rw [this, hp2]
      simp only [hc0, ite_true]
      exact regVal_x01_x0 t obj
    · have := hfx.2 _ hc1
      simp only [Loc.reg.injEq] at this
      rw [this, hp2]
      simp only [hc1, ite_false, Constraint.fixed.injEq, Reg.x.injEq, reduceCtorEq]
      exact regVal_x01_x1 t obj
  -- x0, x1 hold nothing kept live across the call
  have hnot01 : ∀ (r0 : Reg), payloadRegOk info ti r0 = true → ∀ r, r = r0 →
      (∀ p ∈ (ops.zip regs).toList, p.1.isDef = true → p.2 ≠ r) →
      r ∉ (MInst.tryCall info ti).clobbers → False := by
    intro r0 hpr r hr hnd hnc
    subst hr
    simp only [payloadRegOk, Bool.or_eq_true, List.contains_iff_mem] at hpr
    rcases hpr with hpr | hpr
    · exact hnc hpr
    · simp only [defCons, hopsC, List.mem_map, List.mem_filter] at hpr
      obtain ⟨o, ⟨ho, hd⟩, hc⟩ := hpr
      obtain ⟨p, hp, hpd, hpr⟩ := def_fixed_reg hstat ho hd hc
      exact hnd p hp hpd hpr
  obtain ⟨m3, hc3, hr3, hl3⟩ := operandsSound_post (s' := Arm.w (.GPR 1#5) 0 (Arm.w (.GPR 0#5) obj t))
    hstat hm' hlen' hdef
    (fun r ha hnd hnc => by
      rw [regVal_x01 ha (fun e => hnot01 _ hp0 r e hnd hnc) (fun e => hnot01 _ hp1 r e hnd hnc)]
      exact hoth r ha hnd hnc)
    (fun r hr hcs => by
      have ha := calleeSaved_allocatable hcs
      have h0 : r ≠ .x 0 := by rintro rfl; simp [calleeSaved] at hcs <;> omega
      have h1 : r ≠ .x 1 := by rintro rfl; simp [calleeSaved] at hcs <;> omega
      rw [regVal_x01 ha h0 h1]
      exact hkeep r hr hcs)
  have hfr := R.frameOkK hR
  have hsp' : spOf (Arm.w (.GPR 1#5) 0 (Arm.w (.GPR 0#5) obj t)) = R.spB := hFK'.1.trans hst.sp
  have hprog' : (Arm.w (.GPR 1#5) 0 (Arm.w (.GPR 0#5) obj t)).program = R.fb.program R.base := by
    rw [Arm.w_program, Arm.w_program, hprogt, hst.prog]
  have hstr : StRel R.toRL (Arm.w (.GPR 1#5) 0 (Arm.w (.GPR 0#5) obj t))
      (writeM m3 ((((ops.zip (regs.map Loc.reg)).toList.filter (·.1.isDef)).zip
        (payloadOuts (.call info) obj)).filter (·.1.1.isLate))) w' := by
    refine ⟨fun l hl hL => ?_, sameWorld_x01 hW, err_x01 herrt, hprog', hsp',
      align_of_sp (by rw [hsp', hst.sp]) hst.align,
      fun hframe => ?_, code_keep hR.prog0 hst.code fun a ha => hFK'.2.1 a (.inl (.inr (.inr ha))),
      fun a ha => (hFK'.2.1 a (.inr ha)).trans (hst.gkeep a ha), fun hf => hFK'.2.2.trans (hst.fp hf)⟩
    · cases l with
      | reg r => exact hr3 r (hl r rfl)
      | stack k' c =>
        rw [hl3 _ (fun r h => by cases h), hst.store _ hl hL,
          locVal_frame_keep hfr hst.sp hFK' hL (fun r h => by cases h)]
      | save r =>
        rw [hl3 _ (fun r h => by cases h), hst.store _ hl hL,
          locVal_frame_keep hfr hst.sp hFK' hL (fun r h => by cases h)]
    · rw [← hst.fplr hframe]
      exact read_mem_bytes_congr _ _ (fun k hk => hFK'.2.1 _ (fplr_inF hR hframe k hk))
  refine ⟨1, _, MStep.op hvb hi hops hsz hsem hlen (HavocOuts.refl _ _ _) hc3
    (MNext.goto hk1 hsucc hitems), ?_, fun i hi => ?_⟩
  · simp only [iterN]
    rw [hstepU]
    refine q_entry hR hst0 hvs hitems (jl := jl) (by rw [hvl]; exact hjl) ?_ (hstr.pc _)
    rw [Arm.r_of_w_same, hpb]
    simp only [RL.pcOf, hjlo]
  · obtain rfl : i = 0 := by omega
    show R.GoodXUF s
    have hnext : R.NextOk s (R.stepU s) := by
      refine .inr (.inr (.inr ⟨jl, ?_, fun x tt h => by rw [hjl] at h; cases h⟩))
      rw [hstepU, Arm.r_of_w_same, hpb]
      simp only [RL.pcOf]
      rw [lineOffset_succ _ _ _ hjl, hjlo]
      simp [Line.size]
    have hexit : Unw.personality R.T.lsda (Arm.r .PC s + 4 - 1 - progBase s).toNat = .continue →
        ArmRet (xreg 30 R.s0) R.s0 (R.stepU s) ∧ (R.stepU s).program = R.fb.program R.base := by
      intro hc
      rw [hoff, hlsda, hpers] at hc
      cases hc
    have htsp : ∀ x d obj' t', R.AtLine s x →
        ((∃ n, x = .bl n ∧ d = some n) ∨ (∃ r, x = .blr r ∧ d = none)) →
        R.U.raise d s = some (obj', t') → spOf t' = R.spB := by
      intro x d obj' t' hx hd hr'
      obtain rfl := hdesc x d hx hd
      rw [hUr] at hr'
      cases hr'
      exact hFK.1.trans hst.sp
    have htfp : ∀ x d obj' t', R.AtLine s x →
        ((∃ n, x = .bl n ∧ d = some n) ∨ (∃ r, x = .blr r ∧ d = none)) →
        R.U.raise d s = some (obj', t') → xreg 29 t' = spv R.s0 - 16#64 := by
      intro x d obj' t' hx hd hr'
      obtain rfl := hdesc x d hx hd
      rw [hUr] at hr'
      cases hr'
      exact hFK.2.2.trans (hst.fp (lowerRFunc_frame hR.alloc))
    exact .inr ⟨hRX, hnext, hexit, htsp, htfp, fun x hx => ⟨hxzr x hx, hst.code⟩,
      ⟨.tryCall info ti, info, hsite0, .inr ⟨ti, rfl⟩, by rw [hst.sp]; exact RL.K_le hR,
        fun a ha => by rw [hst.sp] at ha; exact RL.below_F ha, hst.gkeep, cc, wh, ops, regs, i', w,
        obj, _, hops, hstat, hasg, hcpc, hst.world, hst.align, hst.err, hgg, hraise⟩⟩

/-- **A raising `try_call` on the machine**: the callee raises, the personality installs the
first handler's landing pad, and the machine is at the landing-pad edge block with the payload in
the call's defs (`RealizesTryRaise`), for any semantics with `csemU`'s raising-`tryCall` clause
(`TryRaiseSem`: `R.semU`, `csemU`, the dead-cleanup chain's value semantics). -/
theorem realizes_tryCall_raiseU {R : RLU} (hR : R.Wf) {semU : Sem}
    (hU : CalleeUnwOkG R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.XR R.U R.vc.CallSite R.gv)
    (hsemT : TryRaiseSem R.XR semU) (hgot : GotSem R.gv R.X semU)
    (hT : LsdaAt R) (hpad : PadsNonzero R.af R.fa) (hsite : SiteAt R.toRL) :
    RealizesTryRaise R semU :=
  (realizes_tryCall_raiseUF hR hU hsemT hgot hT hpad hsite).mono fun _ h => h.goodXU

/-! ## Discharging `SiteAt` and `PadsNonzero` -/

/-- **`SiteAt` from the check of the last block's calls** (`q_callSite`, `q_callSite_last`). -/
theorem siteAt_of_check {R : RL} (hR : R.Wf) (h : lastCallsOk R.af R.fa = true) : SiteAt R := by
  intro s b k allocs its m w vb i info c hq hvb hi hc
  cases hb : R.af.blocks[b + 1]? with
  | none => exact q_callSite_last hR hq hvb hi hc hb h
  | some p => exact q_callSite hR hq hvb hi hc (by rw [hb]; rfl)

/-- The check that the landing pads of the emitted call-site table are at non-zero offsets
(decidable, on `af` and its final code `fa`). -/
def padsNonzeroB (af : AFunc) (fa : FnAsm) : Bool :=
  let r := scanLines fa.lines.toList 0 [] []
  (af.calls.zip r.2).all fun p => match p.1, entryFor r.1 p with
    | some _, some e => e.pad != 0
    | _, _ => true

theorem padsNonzero_of_check {af : AFunc} {fa : FnAsm} (h : padsNonzeroB af fa = true) :
    PadsNonzero af fa := by
  intro ti ret e hm he
  have := List.all_eq_true.mp h _ hm
  simp only [he] at this
  simpa using this

/-! ## Non-vacuity -/

namespace UTryWitness

open Backend.Proof.UnwindTables.Witness in
/-- S10c's witness function (a `try_call` whose catch handler's landing pad is at offset 28)
passes both checks: its call-site bridge (`siteAt_of_check`) and its landing pads
(`padsNonzero_of_check`) are discharged. -/
theorem checks : padsNonzeroB af fa = true ∧ lastCallsOk af fa = true := by decide +kernel

open Backend.Proof.UnwindTables.Witness in
theorem pads : PadsNonzero af fa := padsNonzero_of_check checks.1

open Backend.Proof.UnwindTables.Witness in
/-- The check is not vacuous there: the function's one call is a `try_call` whose entry has
landing pad 28 (32 before #479: Cranelift's frame scheme moves the code 4 bytes earlier). -/
theorem entry :
    af.calls.zip (scanLines fa.lines.toList 0 [] []).2 = [(some ⟨1, [.tag 1 2], false, 0⟩, 16)] ∧
      entryFor (scanLines fa.lines.toList 0 [] []).1 (some ⟨1, [.tag 1 2], false, 0⟩, 16) =
        some ⟨15, 1, 28, 1⟩ := by
  decide +kernel

end UTryWitness

end Backend.Proof
