import FV.E2E.BackendTwoRunLF
import FV.E2E.LinkArmDetX
import FV.E2E.LinkArmBaseNIX

/-!
# The return agreement from the machine lock (SEM1 #537, `docs/plans/uninit.md` §5.9)

At the joint invariant at the `rets` item (`backend_twoRunLF`/`LEF`: the JR configurations are at a
`rets`, `RL.RetsAt`) the two states are locked (`StEqOutX (Zc d d')`). The epilogue keeps the lock
(the `sp` adjustment and the clobber pops name no `x30`, and the pops read frame bytes other than
the saved-LR word, outside `Zc`; the frame-record reload reads the saved fp word, a frame byte,
which `Zc` excludes), and the `ret` gives `RetAgreeX`: the bytes below the entry `sp` that `RetAgreeX`
compares are frame bytes but the saved-LR word, or the callees' dead stack, all outside `Zc`.

* `RL.notZc_ret` (the compared bytes are outside `Zc`), `popLines_x30`, `epiA_x30`;
* **`RL.retAgreeX_rets`**: `RetAgreeX (frameDrop + K) (spv s0)` after `retLen` steps.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- **The bytes `RetAgreeX` compares are outside the lock set**: below the entry `sp` by at most
`frameDrop + K`, but the saved-LR word (the 8 bytes just below). -/
theorem RL.notZc_ret {R : RL} (hR : R.Wf) (d d' : MConf CV Arm.ArmState) {a : BitVec 64}
    (h : StackBelow (frameDrop R.af + R.K) (spv R.s0) a) (h8 : ¬ StackBelow 8 (spv R.s0) a) :
    ¬ R.Zc d d' a := by
  rintro ⟨hfr, -, hds, -⟩
  obtain ⟨hB, hK⟩ := spBody_toNat hR.stack
  obtain ⟨h1, h2⟩ := h
  have h3 : a.toNat + 8 < (spv R.s0).toNat := by
    rcases Nat.lt_or_ge (a.toNat + 8) (spv R.s0).toNat with h | h
    · exact h
    · exact absurd ⟨h1, by omega⟩ h8
  have hlt := (spv R.s0).isLt
  by_cases hin : (spv R.s0).toNat ≤ a.toNat + frameDrop R.af
  · apply hfr
    refine ⟨a.toNat - R.spB.toNat, by rw [RL.spB, hB]; omega, .inl (by rw [RL.spB, hB]; omega), ?_⟩
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, RL.spB, hB]
    rw [Nat.mod_eq_of_lt (a := a.toNat - _) (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  · apply hds
    refine ⟨by rw [RL.spB, hB]; omega, by rw [RL.spB, hB]; omega⟩

/-- The pops of registers the pushes handle (no fp/lr) name no `x30`-exempt instruction. -/
theorem popLines_x30 {int : Bool} {rs : List Reg} (hrs : ∀ r ∈ rs, PushReg int r) :
    ∀ x t, Line.ins x t ∈ popLines int rs → x.x30Exempt = false := by
  intro x t hln
  rw [popLines_eq, List.mem_append] at hln
  rcases hln with hln | hln
  · obtain ⟨p, hp, e⟩ := List.mem_map.1 hln
    have hp1 := hrs _ ((pairsOf_mem rs).1 p hp).1
    have hne : p.1 ≠ Reg.fp := by
      intro e1; rw [e1] at hp1; simp [PushReg, Reg.fp] at hp1
    simp only [popLine2, Line.ins.injEq] at e
    obtain ⟨rfl, -⟩ := e
    cases int <;> simp [Insn.x30Exempt, hne]
  · split at hln
    · simp only [List.mem_singleton, Line.ins.injEq] at hln
      obtain ⟨rfl, -⟩ := hln
      cases int <;> simp [Insn.x30Exempt]
    · simp at hln

/-- **The epilogue's lines before the frame-record reload** (`epiPops`: the `sp` adjustment and
the pops) name no `x30`-exempt instruction. -/
theorem epiA_x30 {saves : List Reg} (hsv : SavesOk saves) {size : Nat} :
    ∀ x t, Line.ins x t ∈ epiPops saves size → x.x30Exempt = false := by
  intro x t h
  simp only [epiPops, List.mem_append] at h
  rcases h with h | h | h
  · exact spAdjLines_x30 false _ x t h
  · exact popLines_x30 hsv.float x t h
  · exact popLines_x30 hsv.int x t h

set_option maxHeartbeats 1000000 in
/-- **The return agreement and the lock at the return from the lock at the `rets` item**: from
states locked at `Zc d d'`, the first (`u`) at `QA` of a `rets` configuration, the two runs return
after `retLen` steps in `RetAgreeX (frameDrop + K) (spv s0)`, with the same program and the same
memory outside `Zc d d'`. The epilogue's `sp` adjustment and pops read frame bytes but the
saved-LR word (`ret_machineNA`'s located reads), outside `Zc`; the frame-record reload reads the
saved fp word, outside `Zc`. -/
theorem RL.retLock_rets {R : RL} (hR : R.Wf) {ra : BitVec 64} (hent : AbiCall R.fb R.base ra R.s0)
    (hx30 : R.fa.x30Free R.lm = true) {u u' : Arm.ArmState} {e : MConf CV Arm.ArmState}
    (hqa : QA R u e) (hre : R.RetsAt e) {d d' : MConf CV Arm.ArmState}
    (hl : StEqOutX (R.Zc d d') u' u) :
    RetAgreeX (frameDrop R.af + R.K) (spv R.s0) (iterN R.step R.retLen u')
      (iterN R.step R.retLen u) ∧
    (iterN R.step R.retLen u').program = (iterN R.step R.retLen u).program ∧
    (∀ a, ¬ R.Zc d d' a → (iterN R.step R.retLen u').mem a = (iterN R.step R.retLen u).mem a) ∧
    ∀ i < R.retLen, StEqOutX (R.Zc d d') (iterN R.step i u') (iterN R.step i u) := by
  obtain ⟨b, k, allocs, its, m, w, vb, us, rfl, hvb, hi⟩ := hre
  obtain ⟨n3, hn3, hgx, -⟩ := ret_machineNA (Y := fun _ => True) hR hent hqa hvb hi
  subst hn3
  obtain ⟨mt, hq⟩ := qa_q hqa
  obtain ⟨hframe, hfs, -, hsv, -, hcb, -, -, -⟩ := RL.frame_facts hR
  have hst0 := hR.stack.frame
  have hsp0 := (spv R.s0).isLt
  have hs : R.af.frameSize < 2 ^ 64 := by have := hst0.1; omega
  have hcb' : clobberBytes R.af.saves ≤ R.af.frameSize := by rw [hfs]; exact hcb
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
  -- the epilogue: the `sp` adjustment and the pops (`epiPops`), then the frame-record reload
  have hEA : epiLines R.af.saves R.af.frameSize = epiPops R.af.saves R.af.frameSize ++
      [Line.ins (.ldp Reg.fp Reg.lr (.spPostIndexed 16)) none] := epiLines_pops _ _
  have hdropA : R.L.drop j0 = epiPops R.af.saves R.af.frameSize ++
      (Line.ins (.ldp Reg.fp Reg.lr (.spPostIndexed 16)) none ::
        .ins .ret none :: (relaxLines R.far (ftList (ls2 ++ nxtOf R.af b)) ++ T)) := by
    rw [hdrop', hEA]; simp only [List.append_assoc, List.singleton_append]
  have hdrop0 : frameDrop R.af = R.af.frameSize + 16 := by simp [frameDrop, hframe]
  -- `sp + size - clobberBytes` is the bottom of the clobber area
  have hB : spOf u + BitVec.ofNat 64 (R.af.frameSize - clobberBytes R.af.saves) = R.topB := by
    obtain ⟨d, hd⟩ : ∃ d, R.af.frameSize = d + clobberBytes R.af.saves :=
      ⟨_, (Nat.sub_add_cancel hcb').symm⟩
    rw [hst.sp, RL.spB, RL.topB, RL.topN, hdrop0, hd, Nat.add_sub_cancel,
      show d + clobberBytes R.af.saves + 16 = d + (16 + clobberBytes R.af.saves) by omega,
      BitVec.ofNat_add, BitVec.ofNat_add]
    bv_omega
  have hal : (spOf u + BitVec.ofNat 64 (R.af.frameSize - clobberBytes R.af.saves)).toNat % 16 = 0 := by
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
  obtain ⟨s1, hsteps, -, -, -, -, -, -⟩ := epilogue_ok (R.envOf j0) hs hsv hcb' u hal
  -- the lines and the pcs of the epilogue's states
  have hat : ∀ q ln, (epiLines R.af.saves R.af.frameSize)[q]? = some ln →
      R.fa.lines.toList[j0 + q]? = some ln := by
    intro q ln hq'
    have := congrArg (·[q]?) hdrop'
    simp only [List.getElem?_drop, RL.L] at this
    rw [this, List.getElem?_append_left (List.getElem?_eq_some_iff.1 hq').1]
    exact hq'
  have hins : ∀ ln ∈ epiLines R.af.saves R.af.frameSize, ∃ x, ln = .ins x none ∧ x.hooked = false :=
    fun ln h => let ⟨x, e, hh, _⟩ := epiLines_ins _ _ ln h; ⟨x, e, hh⟩
  have hhook : ∀ i t, Line.ins i t ∈ epiLines R.af.saves R.af.frameSize → i.hooked = false :=
    fun i t h => by obtain ⟨x, e, hh⟩ := hins _ h; cases e; exact hh
  have hpcs := iterN_execLines_pc (X := R.X) (H := R.H) hR.layout hR.lm hR.fit _ j0 u s1 hat hhook
    hst.prog (by rw [hpc]; rfl) hst.err (stepsOk_interOk hsteps hst.err) hsteps.exec
  -- `sp` at the frame-record reload: the `sp` adjustment and the pops run first
  obtain ⟨sc, hcA, hspc⟩ := epiPops_ok (R.envOf j0) hs hsv hcb' u hal
  have hinsA : ∀ ln ∈ epiPops R.af.saves R.af.frameSize, ∃ x, ln = .ins x none ∧ x.hooked = false :=
    fun ln h => hins ln (by rw [hEA]; exact List.mem_append_left _ h)
  have hitA : iterN R.step (epiPops R.af.saves R.af.frameSize).length u = sc :=
    (iterN_steps hR hdropA hinsA hst.prog hpc hst.err hcA).1
  have hspA : spOf sc = spv R.s0 - 16#64 := by
    rw [hspc, hst.sp, RL.spB, hdrop0, BitVec.ofNat_add]; bv_omega
  have hlen : R.retLen = (epiLines R.af.saves R.af.frameSize).length + 1 := rfl
  have hLA : (epiLines R.af.saves R.af.frameSize).length =
      (epiPops R.af.saves R.af.frameSize).length + 1 := by
    rw [hEA, List.length_append, List.length_singleton]
  have hfpw : ∀ q < 8, ¬ R.Zc d d' (spv R.s0 - 16#64 + BitVec.ofNat 64 q) := by
    intro q hq'
    have h16 : 16 ≤ (spv R.s0).toNat := by have := hst0.1; omega
    have e : (spv R.s0 - 16#64 + BitVec.ofNat 64 q).toNat = (spv R.s0).toNat - 16 + q := by
      simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (a := q) (by omega)]
      omega
    refine RL.notZc_ret hR d d' ⟨by rw [e]; omega, by rw [e, hdrop0]; omega⟩
      fun ⟨_, h⟩ => by rw [e] at h; omega
  -- the lock through the epilogue's lines
  have H : ∀ i ≤ (epiLines R.af.saves R.af.frameSize).length,
      StEqOutX (R.Zc d d') (iterN R.step i u') (iterN R.step i u) := by
    intro i hi
    induction i with
    | zero => exact hl
    | succ i ih =>
      have hi' : i < (epiLines R.af.saves R.af.frameSize).length := by omega
      have hlk := ih (by omega)
      obtain ⟨ln, hln⟩ : ∃ ln, (epiLines R.af.saves R.af.frameSize)[i]? = some ln :=
        ⟨_, List.getElem?_eq_getElem hi'⟩
      obtain ⟨x, rfl, hhx⟩ := hins _ (List.mem_of_getElem? hln)
      have hgi := hgx i (by rw [hlen]; omega)
      have hg := hgi.1.1
      have hj := hat i _ hln
      have hpci := hpcs i (by omega)
      have ht : OnLine R.fa R.fb R.lm R.base (iterN R.step i u) x :=
        ⟨hR.layout, hR.lm, hR.fit, hg.prog, hg.err, ⟨j0 + i, none, hj, hpci⟩⟩
      have e1 : iterN R.step (i + 1) u' = R.step (iterN R.step i u') := by rw [iterN_add]; rfl
      have e2 : iterN R.step (i + 1) u = R.step (iterN R.step i u) := by rw [iterN_add]; rfl
      rw [e1, e2]
      rw [hEA] at hln
      rcases Nat.lt_or_ge i (epiPops R.af.saves R.af.frameSize).length with hia | hia
      · have hmem : Line.ins x none ∈ epiPops R.af.saves R.af.frameSize := by
          rw [List.getElem?_append_left hia] at hln
          exact List.mem_of_getElem? hln
        have hxe : x.x30Exempt = false := epiA_x30 hsv x none hmem
        have hld : x.ldpFR = false := by
          cases hl2 : x.ldpFR with
          | false => rfl
          | true =>
            exfalso
            have e : x = .ldp .fp .lr (.spPostIndexed 16) := by simpa [Insn.ldpFR] using hl2
            subst e
            simp [Insn.x30Exempt] at hxe
        refine stEqOutX_line_free (X := R.X) (H := R.H) ht hx30 hxe hlk ?_
          (fun _ _ hb => by obtain ⟨_, _, _, rfl⟩ := hb; simp [Insn.hooked] at hhx)
        apply readsAvoid_stepiEvs
        intro a ha ev hev hdir k' hk'
        obtain ⟨a', ha', hd⟩ := decodeAt_ofLine ht.layout ht.lm ht.fit ht.prog hj hpci
        rw [hd, Option.some.injEq] at ha
        subst ha
        have hcov := (ExecBytes.instEvs_cover hev).1 hdir
        have hr := hgi.2 (j0 + i) x none hj hpci hhx a'
          (by refine (congrArg (x.toArmInst ·) ?_).trans ha'; exact RL.envL_of_lm ht.lm (j0 + i))
          (ev.addr, ev.n) hcov k' hk'
        rw [hld] at hr
        exact RL.notZc_of_readInY hr fun _ _ => trivial
      · obtain rfl : i = (epiPops R.af.saves R.af.frameSize).length := by omega
        rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at hln
        simp only [List.getElem?_cons_zero, Option.some.injEq, Line.ins.injEq] at hln
        obtain ⟨rfl, -⟩ := hln
        refine stEqOutX_line_ldpFR (X := R.X) (H := R.H) ht hlk fun q hq' => ?_
        have hsp : Arm.read_gpr 64 31 (iterN R.step (epiPops R.af.saves R.af.frameSize).length u) =
            spv R.s0 - 16#64 := by
          rw [hitA]
          exact hspA
        rw [hsp]
        exact hfpw q hq'
  -- the `ret`
  have hlk := H _ (Nat.le_refl _)
  have hg := (hgx (epiLines R.af.saves R.af.frameSize).length (by rw [hlen]; omega)).1.1
  have hj : R.fa.lines.toList[j0 + (epiLines R.af.saves R.af.frameSize).length]? =
      some (Line.ins .ret none) := by
    have := congrArg (·[(epiLines R.af.saves R.af.frameSize).length]?) hdrop'
    simpa [List.getElem?_drop, RL.L] using this
  have ht : OnLine R.fa R.fb R.lm R.base
      (iterN R.step (epiLines R.af.saves R.af.frameSize).length u) .ret :=
    ⟨hR.layout, hR.lm, hR.fit, hg.prog, hg.err, ⟨_, none, hj, hpcs _ (Nat.le_refl _)⟩⟩
  have e1 : iterN R.step R.retLen u' =
      R.step (iterN R.step (epiLines R.af.saves R.af.frameSize).length u') := by
    rw [hlen, iterN_add]; rfl
  have e2 : iterN R.step R.retLen u =
      R.step (iterN R.step (epiLines R.af.saves R.af.frameSize).length u) := by
    rw [hlen, iterN_add]; rfl
  rw [e1, e2]
  obtain ⟨hr, hp, hm⟩ := retAgree_line_ret (X := R.X) (H := R.H) ht hlk
  exact ⟨⟨hr, fun a ha h8 => hm a (RL.notZc_ret hR d d' ha h8)⟩, hp, hm,
    fun i hi => H i (by rw [hlen] at hi; omega)⟩

/-- **The return agreement from the lock at the `rets` item** (module doc): from states locked at
`Zc d d'`, the first (`u`) at `QA` of a `rets` configuration, the two runs return after `retLen`
steps in `RetAgreeX (frameDrop + K) (spv s0)`. -/
theorem RL.retAgreeX_rets {R : RL} (hR : R.Wf) {ra : BitVec 64} (hent : AbiCall R.fb R.base ra R.s0)
    (hx30 : R.fa.x30Free R.lm = true) {u u' : Arm.ArmState} {e : MConf CV Arm.ArmState}
    (hqa : QA R u e) (hre : R.RetsAt e) {d d' : MConf CV Arm.ArmState}
    (hl : StEqOutX (R.Zc d d') u' u) :
    RetAgreeX (frameDrop R.af + R.K) (spv R.s0) (iterN R.step R.retLen u')
      (iterN R.step R.retLen u) :=
  (RL.retLock_rets hR hent hx30 hqa hre hl).1

/-- **A base call keeps the lock** (`HookNIX`, #704) when the lock set is inside the exterior:
the worlds of the two configurations differ only on `F` (the lock set is `F` or the difference
set, less the frame, the tables and the dead stack). -/
theorem stEqOutX_call_of_hookNIX {R : RL} {Hb : ArmHooks} {BD : Option String → Prop}
    (hN : HookNIX Hb BD R.F) {c c' : MConf CV Arm.ArmState}
    (hW : ∀ a, MConf.WDiff c c' a → R.F a) {d : Option String} (hd : BD d) {u u' : Arm.ArmState}
    (h : StEqOutX (R.Zc c c') u u') : StEqOutX (R.Zc c c') (Hb.call d u) (Hb.call d u') :=
  hN.1 d hd _ u u' h fun _ ⟨_, _, _, hz⟩ => hz.elim id (hW _)

/-- **A TLS hook keeps the lock** (`HookNIX`, #704), as `stEqOutX_call_of_hookNIX`. -/
theorem stEqOutX_tls_of_hookNIX {R : RL} {Hb : ArmHooks} {BD : Option String → Prop}
    (hN : HookNIX Hb BD R.F) {c c' : MConf CV Arm.ArmState}
    (hW : ∀ a, MConf.WDiff c c' a → R.F a) (n : String) (r : Reg) {u u' : Arm.ArmState}
    (h : StEqOutX (R.Zc c c') u u') : StEqOutX (R.Zc c c') (Hb.tls n r u) (Hb.tls n r u') :=
  hN.2 n r _ u u' h fun _ ⟨_, _, _, hz⟩ => hz.elim id (hW _)

section
variable {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
  {af : AFunc} {fa : FnAsm} {fb : FnBin}

set_option maxHeartbeats 4000000 in
/-- **Two activations of a compiled function locked from the entries to the return**
(`backend_twoRunLEF` and `RL.retAgreeX_rets`): the lock along the body and `RetAgreeX` at the
return, from entries agreeing by `EntryAgree` and on `x29`. -/
theorem backend_twoRunLER (hsub : InSubset p f) (hc : Compiled f k vc vcp rf af fa fb)
    (hone : InstCallsOne f) (htc : TryCallsOne f)
    {XI : ExtSemI} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64} {args : List Clif.Val} {cs : Clif.State}
    (hX : ∀ s n, ReachN env p cs s n →
      XCallsOk (env.only (Clif.Invoked env p s)) (f.externs.map (·.2))
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n) ∧
      XCallsIndOk (env.only (Clif.Invoked env p s)) (indSigs f)
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n))
    (hNI : ∀ s n, ReachN env p cs s n → XNI F syms (f.externs.map (·.2)) (indSigs f) c
      (CallLg (env.only (Clif.Invoked env p s)) (f.externs.map (·.2)) (indSigs f)) (XI.at n))
    (hTls : ∀ n, XTls F (XI.at n))
    (hsym : ∀ n b, syms n = some b → XI.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {w₀ w₀' : Arm.ArmState} {D : BitVec 64 → Prop} (ρ₀ : Nat → CV) (hce : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hrel' : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem
      w₀')
    (hargs : ArgsAtEntry F f.sig args w₀)
    (hsw : SameWorld (fun b => F b ∨ D b) w₀ w₀')
    (hreg : ∀ r v, (ArgLoc.reg r, v) ∈ (locsOf f.sig).zip args → regVal w₀' r = regVal w₀ r)
    (hstk : ∀ off v, (ArgLoc.stack off, v) ∈ (locsOf f.sig).zip args → ∀ k < v.ty.bytes,
      w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
        w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k))
    (htr : TrapsExplicit env p cs) (fuel : Nat)
    {lm : Std.HashMap Lbl Nat} (hlm : labelOffsets fa.lines = .ok lm) {body : List Line}
    {psF : PState} (hpsF : blocksLinesE ⟨fa.k, af.slotBase⟩ af af.blocks.toList {} = .ok (body, psF))
    {H : ArmHooks} {G G' : BitVec 64 → Prop}
    {base ra ra' : BitVec 64} {Kp Kp' : Nat} {cc cc' : BitVec 64} {P P' : Nat → BitVec 64 → BitVec 8}
    {Rr Rr' : Nat → Arm.ArmState} {s t0 : Arm.ArmState}
    (he : ActEntryPR vcp rf af fa fb K F G XI H base ra Kp cc P Rr s w₀)
    (he' : ActEntryPR vcp rf af fa fb K F G' XI H base ra' Kp' cc' P' Rr' t0 w₀')
    {R : RL} (hR : R = actRL vcp rf af fa fb lm base s XI H psF K G (GotV vcp))
    (hcov : FormsCovered R.ctx R.vc)
    (hx30 : fa.x30Free lm = true)
    (hcall : ∀ n n' c c' i u u', ({ R with X := XI.at n } : RL).InSeg (OkDiff F c c') c i u →
      ({ R with s0 := t0, G := G', X := XI.at n' } : RL).InSeg (OkDiff F c c') c' i u' →
      ({ R with X := XI.at n } : RL).GoodX u →
      ({ R with s0 := t0, G := G', X := XI.at n' } : RL).GoodX u' →
      StEqOutX (R.Zc c c') u u' →
      ((∃ m, ({ R with X := XI.at n } : RL).AtLine u (.bl m)) ∨
        ∃ r, ({ R with X := XI.at n } : RL).AtLine u (.blr r)) →
      ∀ d, StEqOutX (R.Zc c c') (H.call d u) (H.call d u'))
    (htls : ∀ n n' c c' i u u', ({ R with X := XI.at n } : RL).InSeg (OkDiff F c c') c i u →
      ({ R with s0 := t0, G := G', X := XI.at n' } : RL).InSeg (OkDiff F c c') c' i u' →
      ({ R with X := XI.at n } : RL).GoodX u →
      ({ R with s0 := t0, G := G', X := XI.at n' } : RL).GoodX u' →
      StEqOutX (R.Zc c c') u u' →
      (∃ a b c, ({ R with X := XI.at n } : RL).AtLine u (.ldrTlsDescLo12 a b c)) →
      ∀ m r, StEqOutX (R.Zc c c') (H.tls m r u) (H.tls m r u'))
    (hag : EntryAgree (frameDrop af + K) s t0)
    (hx29 : Arm.r (.GPR 29#5) s = Arm.r (.GPR 29#5) t0) :
    ∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
    ∃ N,
      (∀ i < N, ∃ c c', StEqOutX (R.Zc c c')
        (iterN ({ R with X := XI.at 0 } : RL).step ((prologueLines R.af.saves R.af.frameSize).length + i) R.s0)
        (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step
          ((prologueLines R.af.saves R.af.frameSize).length + i) t0)) ∧
      Arm.r .PC (iterN ({ R with X := XI.at 0 } : RL).step
        ((prologueLines R.af.saves R.af.frameSize).length + N + R.retLen) R.s0) = ra ∧
      Arm.r .PC (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step
        ((prologueLines R.af.saves R.af.frameSize).length + N + R.retLen) t0) = ra' ∧
      RetAgreeX (frameDrop af + K) (spv s)
        (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step
          ((prologueLines R.af.saves R.af.frameSize).length + N + R.retLen) t0)
        (iterN ({ R with X := XI.at 0 } : RL).step
          ((prologueLines R.af.saves R.af.frameSize).length + N + R.retLen) R.s0) := by
  intro vals cm hrun
  obtain ⟨N, e, e', -, hlk, ⟨⟨W, hqA, -⟩, -, -, hLB⟩, -, hpc, hpc', hre, -⟩ :=
    backend_twoRunLEF hsub hc hone htc hX hNI hTls hsym hslot ρ₀ hce hrel hrel' hargs hsw hreg hstk
      htr fuel hlm hpsF he he' hR hcov hx30 hcall htls hag hx29 vals cm hrun
  refine ⟨N, hlk, hpc, hpc', ?_⟩
  have hs : ∀ (g : Arm.ArmState → Arm.ArmState) (x : Arm.ArmState),
      iterN g ((prologueLines R.af.saves R.af.frameSize).length + N + R.retLen) x =
        iterN g R.retLen (iterN g ((prologueLines R.af.saves R.af.frameSize).length + N) x) :=
    fun g x => iterN_add ..
  rw [hs, hs]
  subst hR
  have hF := he.hF
  subst hF
  obtain ⟨-, -, -, -, hk⟩ := emitFunc_ok hc.emit
  subst hk
  obtain ⟨ckc, ins, hck⟩ := checked_of_checkAlloc hc.check
  obtain ⟨a0, hat, hle⟩ := hck.at
  have hW0 : ({ actRL vcp rf af fa fb lm base s XI H psF K G (GotV vcp) with X := XI.at 0 } :
      RL).Wf :=
    ⟨⟨ckc, ins, a0, hat, entryOk_of_le hle⟩, hc.alloc, hc.emit, hc.layout, hlm,
      by show 4 * fb.words.size ≤ 2 ^ 64; have := he.abi.fits; omega, he.stack, ⟨body, hpsF⟩,
      he.abi.program, he.gfree⟩
  exact RL.retAgreeX_rets hW0 he.abi hx30 (QWA.qaX hqA hW0 he.abi) hre hLB.symm

end

end E2E
