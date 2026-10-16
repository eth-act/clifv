import FV.E2E.RegLevelU

/-!
# A raising `try_call` on the machine: the landing pad (S10e, #232)

`realizes_tryCall_raiseU`: from `Q` at a `tryCall` item whose callee raises (`XRaise`), one step
of the machine with unwinding (`Unw.ArmStepU`: the callee raises, the personality reads the
emitted call-site table and installs the first handler's landing pad) reaches `Q` at the entry
of the handler's successor (the landing-pad edge block), the defs of the call holding the
payload (x0 = the exception object, x1 = 0): the raising `tryCall` case of `realizes_allU`.

What it reads about the emitted code and tables:
* `LsdaAt`: the tables the unwinder reads hold the emitted call-site table (`CallSitesOk`);
* `PadsNonzero`: the landing pads of the table are at non-zero offsets (the personality treats
  landing pad 0 as none);
* `SiteAt`: the call-site bridge (`q_callSite`): at a call item the pc is at the call line
  whose return offset `callSites` pairs with this call.
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

theorem regVal_w_x01 {t : Arm.ArmState} {obj : BitVec 64} {pc : BitVec 64} {r : Reg}
    (ha : r.allocatable = true) (h0 : r ≠ .x 0) (h1 : r ≠ .x 1) :
    regVal (Arm.w .PC pc (Arm.w (.GPR 1#5) 0 (Arm.w (.GPR 0#5) obj t))) r = regVal t r := by
  rcases allocatable_cases ha with ⟨n, rfl, hn, -⟩ | ⟨n, rfl, hn⟩
  · have hn0 : n ≠ 0 := fun e => h0 (by rw [e])
    have hn1 : n ≠ 1 := fun e => h1 (by rw [e])
    simp only [regVal, rnum]
    rw [Arm.r_of_w_different (by simp),
      Arm.r_of_w_different (by
        simp only [ne_eq, Arm.StateField.GPR.injEq]
        exact Unw.ofNat5_ne (a := n) (b := 1) (by omega) (by omega) hn1),
      Arm.r_of_w_different (by
        simp only [ne_eq, Arm.StateField.GPR.injEq]
        exact Unw.ofNat5_ne (a := n) (b := 0) (by omega) (by omega) hn0)]
  · simp only [regVal]
    rw [Arm.r_of_w_different (by simp), Arm.r_of_w_different (by simp),
      Arm.r_of_w_different (by simp)]

theorem frameKeep_w_x01 {F : BitVec 64 → Prop} {s t : Arm.ArmState} {obj pc : BitVec 64}
    (h : FrameKeep F s t) :
    FrameKeep F s (Arm.w .PC pc (Arm.w (.GPR 1#5) 0 (Arm.w (.GPR 0#5) obj t))) := by
  refine ⟨?_, fun a ha => ?_⟩
  · simp only [spOf]
    rw [Arm.r_of_w_different (by simp), Arm.r_of_w_different (by simp only [ne_eq,
      Arm.StateField.GPR.injEq]; decide), Arm.r_of_w_different (by simp only [ne_eq,
      Arm.StateField.GPR.injEq]; decide)]
    exact h.1
  · rw [Arm.mem_w_of_mem_eq rfl, Arm.mem_w_of_mem_eq rfl, Arm.mem_w_of_mem_eq rfl]
    exact h.2 a ha

theorem sameWorld_w_x01 {F : BitVec 64 → Prop} {t w : Arm.ArmState} {obj pc : BitVec 64}
    (h : SameWorld F t w) :
    SameWorld F (Arm.w .PC pc (Arm.w (.GPR 1#5) 0 (Arm.w (.GPR 0#5) obj t))) w :=
  SameWorld.w_left (by simp [Masked]) (SameWorld.w_left (by simp [Masked]; decide)
    (SameWorld.w_left (by simp [Masked]; decide) h))

/-- **A raising `try_call` on the machine**: the callee raises, the personality installs the
first handler's landing pad, and the machine is at the landing-pad edge block with the payload in
the call's defs (`RealizesTryRaise`). -/
theorem realizes_tryCall_raiseU {R : RLU} (hR : R.Wf)
    (hU : CalleeUnwOkG R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.XR R.U R.vc.CallSite)
    (hT : LsdaAt R) (hpad : PadsNonzero R.af R.fa) (hsite : SiteAt R.toRL) :
    RealizesTryRaise R R.semU := by
  intro s b k allocs its m w vb info ti ops c' obj w2 hq _hA hvb hi hops hraise hm
  have hck := (lowerRFunc_ok hR.alloc).2.2
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
  obtain ⟨hok, heq⟩ := csemVU_try_raise hsem0 hraise
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl, rfl⟩ := heq
  simp only [tryUOk, Bool.and_eq_true, Bool.not_eq_true'] at hok
  obtain ⟨⟨⟨hfirst, hcl0⟩, hdefs01⟩, hx01⟩ := hok
  -- the raising callee (the contract)
  have hsite0 : R.vc.CallSite info := ⟨b, vb, k, hvb, .inr ⟨ti, hi⟩⟩
  have hcpc := callAt_of_q hq hvb hi tryCall_hcall regs i' rfl hasg
  obtain ⟨-, hraiseU⟩ := hU.os info (.tryCall info ti) hsite0 (.inr ⟨ti, rfl⟩) s
    (by rw [hst.sp]; exact RL.K_le hR) (fun a ha => by rw [hst.sp] at ha; exact RL.below_F ha)
    hst.gkeep cc wh ops regs i' w hops hstat hasg hcpc hst.world hst.align hst.err
  obtain ⟨t, hUr, hW, hFK, herrt, hprogt, hoth, hkeep⟩ := hraiseU obj w2 hraise
  -- the call line and the machine's step into the unwinder
  obtain ⟨j1, x, t1, hj1, hx, hpc1⟩ := hcpc
  have hins : insnAt R.fa (progBase s) (Arm.r .PC s) = some x := insnAt_pc hR hj1 hst.prog hpc1
  have hstep1 : R.stepU s = Unw.unwindAt R.T (progBase s) (Arm.r .PC s) obj t := by
    obtain ⟨ic, rfl, -⟩ := (assign_call_tryCall info regs).2 ti i' hasg
    unfold RLU.stepU
    simp only [MInst.callInsn?] at hx
    split at hx
    · rename_i n _
      cases hx
      exact Unw.armStepU_raise hins (.inl ⟨n, rfl, rfl⟩) (hUr _)
    · rename_i r _
      cases hx
      exact Unw.armStepU_raise hins (.inr ⟨r, rfl, rfl⟩) (hUr _)
  -- the personality: the first handler's landing pad
  obtain ⟨j, x', hj, hpcj, -, hmem⟩ := hsite s b k _ its m w vb _ info (some ti) hq hvb hi
    (.inr ⟨ti, rfl, rfl⟩)
  obtain ⟨sites, hcs, hlsda⟩ := hT
  obtain ⟨e, he, hpers⟩ := Unw.personality_callSite hcs hmem
  rw [if_neg (hpad ti _ e hmem he)] at hpers
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
      simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
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
  -- the landing pad's label
  obtain ⟨hd0, hs0, hfirstEq⟩ : ∃ h hs, ti.handlers = h :: hs ∧
      ((∃ l, h = .tag 0 l) ∨ ∃ l, h = .tag 1 l) := by
    revert hfirst
    rcases ti.handlers with _ | ⟨h, hs⟩
    · simp [firstHandlerOk]
    · intro hf
      refine ⟨h, hs, rfl, ?_⟩
      rcases h with ⟨_ | _ | n, l⟩ | l <;> simp_all [firstHandlerOk]
  sorry

end Backend.Proof
