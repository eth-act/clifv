import FV.E2E.BackendTwoRunLF
import FV.E2E.LinkArmDetX

/-!
# The return agreement from the machine lock (SEM1 #537, `docs/plans/uninit.md` §5.9)

At the joint invariant at the `rets` item (`backend_twoRunLF`/`LEF`: the JR configurations are at a
`rets`, `RL.RetsAt`) the two states are locked (`StEqOutX (Zc d d')`). The epilogue keeps the lock
(the `sp` adjustment reads nothing and names no `x30`; the frame-record reload reads the saved fp
word, a frame byte, which `Zc` excludes), and the `ret` gives `RetAgreeX`: the bytes below the
entry `sp` that `RetAgreeX` compares are frame bytes but the saved-LR word, or the callees' dead
stack, all outside `Zc`.

* `RL.notZc_ret` (the compared bytes are outside `Zc`);
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

set_option maxHeartbeats 1000000 in
/-- **The return agreement from the lock at the `rets` item** (module doc): from states locked at
`Zc d d'`, the first (`u`) at `Q` of a `rets` configuration, the two runs return after `retLen`
steps in `RetAgreeX (frameDrop + K) (spv s0)`. -/
theorem RL.retAgreeX_rets {R : RL} (hR : R.Wf) {ra : BitVec 64} (hent : AbiCall R.fb R.base ra R.s0)
    (hx30 : R.fa.x30Free R.lm = true) {u u' : Arm.ArmState} {e : MConf CV Arm.ArmState}
    (hq : Q R u e) (hre : R.RetsAt e) {d d' : MConf CV Arm.ArmState}
    (hl : StEqOutX (R.Zc d d') u' u) :
    RetAgreeX (frameDrop R.af + R.K) (spv R.s0) (iterN R.step R.retLen u')
      (iterN R.step R.retLen u) := by
  obtain ⟨b, k, allocs, its, m, w, vb, us, rfl, hvb, hi⟩ := hre
  obtain ⟨n3, hn3, hgx, -⟩ := ret_machineNA (Y := fun _ => True) hR hent hq hvb hi
  subst hn3
  have hframe := lowerRFunc_frame hR.alloc
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
  have hdropA : R.L.drop j0 = spAdjLines false R.af.frameSize ++
      (Line.ins (.ldp Reg.fp Reg.lr (.spPostIndexed 16)) none ::
        .ins .ret none :: (relaxLines R.far (ftList (ls2 ++ nxtOf R.af b)) ++ T)) := by
    rw [hdrop']; simp
  have hdrop0 : frameDrop R.af = R.af.frameSize + 16 := by simp [frameDrop, hframe]
  have hslot : spOf u + BitVec.ofNat 64 R.af.frameSize = spv R.s0 - 16#64 := by
    rw [hst.sp, RL.spB, hdrop0, BitVec.ofNat_add]; bv_omega
  have hal : (spOf u + BitVec.ofNat 64 R.af.frameSize).toNat % 16 = 0 := by
    have h16 : 16 ≤ (spv R.s0).toNat := by have := hst0.1; omega
    rw [hslot, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simpa using h16)]
    have := hent.spAligned
    simp; omega
  obtain ⟨s1, hsteps, -, -, -, -, -⟩ := epilogue_ok (R.envOf j0) hs u hal
  -- the lines and the pcs of the epilogue's states
  have hat : ∀ q ln, (spAdjLines false R.af.frameSize ++
      [Line.ins (.ldp Reg.fp Reg.lr (.spPostIndexed 16)) none])[q]? = some ln →
      R.fa.lines.toList[j0 + q]? = some ln := by
    intro q ln hq'
    have := congrArg (·[q]?) hdrop'
    simp only [List.getElem?_drop, RL.L] at this
    rw [this, List.getElem?_append_left (List.getElem?_eq_some_iff.1 hq').1]
    exact hq'
  have hins : ∀ ln ∈ spAdjLines false R.af.frameSize ++
      [Line.ins (.ldp Reg.fp Reg.lr (.spPostIndexed 16)) none],
      ∃ x, ln = .ins x none ∧ x.hooked = false := fun ln h => by
    rcases List.mem_append.1 h with h | h
    · obtain ⟨x, e, hh, -⟩ := spAdjLines_ins false _ ln h; exact ⟨x, e, hh⟩
    · simp only [List.mem_singleton] at h; exact ⟨_, h, rfl⟩
  have hhook : ∀ i t, Line.ins i t ∈ spAdjLines false R.af.frameSize ++
      [Line.ins (.ldp Reg.fp Reg.lr (.spPostIndexed 16)) none] → i.hooked = false := fun i t h => by
    obtain ⟨x, e, hh⟩ := hins _ h; cases e; exact hh
  have hpcs := iterN_execLines_pc (X := R.X) (H := R.H) hR.layout hR.lm hR.fit _ j0 u s1 hat hhook
    hst.prog (by rw [hpc]; rfl) hst.err (stepsOk_interOk hsteps hst.err) hsteps.exec
  -- `sp` at the frame-record reload
  obtain ⟨s2, h2s, hsp2, -, -⟩ := spAdj_ok (R.envOf j0) false hs u
  simp only [Bool.false_eq_true, ite_false] at hsp2
  have hinsA : ∀ ln ∈ spAdjLines false R.af.frameSize, ∃ x, ln = .ins x none ∧ x.hooked = false :=
    fun ln h => let ⟨x, e, hh, _⟩ := spAdjLines_ins false _ ln h; ⟨x, e, hh⟩
  have hit2 : iterN R.step (spAdjLines false R.af.frameSize).length u = s2 :=
    (iterN_steps hR hdropA hinsA hst.prog hpc hst.err h2s).1
  have hlen : R.retLen = (spAdjLines false R.af.frameSize ++
      [Line.ins (.ldp Reg.fp Reg.lr (.spPostIndexed 16)) none]).length + 1 := by
    simp [RL.retLen]
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
  have H : ∀ i ≤ (spAdjLines false R.af.frameSize ++
      [Line.ins (.ldp Reg.fp Reg.lr (.spPostIndexed 16)) none]).length,
      StEqOutX (R.Zc d d') (iterN R.step i u') (iterN R.step i u) := by
    intro i hi
    induction i with
    | zero => exact hl
    | succ i ih =>
      have hi' : i < (spAdjLines false R.af.frameSize ++
          [Line.ins (.ldp Reg.fp Reg.lr (.spPostIndexed 16)) none]).length := by omega
      have hlk := ih (by omega)
      obtain ⟨ln, hln⟩ : ∃ ln, (spAdjLines false R.af.frameSize ++
          [Line.ins (.ldp Reg.fp Reg.lr (.spPostIndexed 16)) none])[i]? = some ln :=
        ⟨_, List.getElem?_eq_getElem hi'⟩
      obtain ⟨x, rfl, hhx⟩ := hins _ (List.mem_of_getElem? hln)
      have hg := (hgx i (by rw [hlen]; omega)).1.1
      have ht : OnLine R.fa R.fb R.lm R.base (iterN R.step i u) x :=
        ⟨hR.layout, hR.lm, hR.fit, hg.prog, hg.err, ⟨j0 + i, none, hat i _ hln, hpcs i (by omega)⟩⟩
      have e1 : iterN R.step (i + 1) u' = R.step (iterN R.step i u') := by rw [iterN_add]; rfl
      have e2 : iterN R.step (i + 1) u = R.step (iterN R.step i u) := by rw [iterN_add]; rfl
      rw [e1, e2]
      rcases Nat.lt_or_ge i (spAdjLines false R.af.frameSize).length with hia | hia
      · have hmem : Line.ins x none ∈ spAdjLines false R.af.frameSize := by
          rw [List.getElem?_append_left hia] at hln
          exact List.mem_of_getElem? hln
        exact stEqOutX_line_free (X := R.X) (H := R.H) ht hx30
          (spAdjLines_x30 false _ x none hmem) hlk
          (by
            apply readsAvoid_stepiEvs
            intro a ha ev hev hdir k' hk
            obtain ⟨j', a', ha', hd⟩ := ht.decodeAt
            rw [hd, Option.some.injEq] at ha
            subst ha
            have hcov := (ExecBytes.instEvs_cover hev).1 hdir
            rw [Insn.memReads_nil (spAdjLines_noLoads false _ x none hmem) ha'] at hcov
            cases hcov)
          (fun _ _ hb => by obtain ⟨_, _, _, rfl⟩ := hb; simp [Insn.hooked] at hhx)
      · obtain rfl : i = (spAdjLines false R.af.frameSize).length := by simp at hi'; omega
        rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at hln
        simp only [List.getElem?_cons_zero, Option.some.injEq, Line.ins.injEq] at hln
        obtain ⟨rfl, -⟩ := hln
        refine stEqOutX_line_ldpFR (X := R.X) (H := R.H) ht hlk fun q hq' => ?_
        have hsp : Arm.read_gpr 64 31 (iterN R.step (spAdjLines false R.af.frameSize).length u) =
            spv R.s0 - 16#64 := by
          rw [hit2]
          show spOf s2 = _
          rw [hsp2, hslot]
        rw [hsp]
        exact hfpw q hq'
  -- the `ret`
  have hlk := H _ (Nat.le_refl _)
  have hg := (hgx (spAdjLines false R.af.frameSize ++
      [Line.ins (.ldp Reg.fp Reg.lr (.spPostIndexed 16)) none]).length (by rw [hlen]; omega)).1.1
  have hj : R.fa.lines.toList[j0 + (spAdjLines false R.af.frameSize ++
      [Line.ins (.ldp Reg.fp Reg.lr (.spPostIndexed 16)) none]).length]? =
      some (Line.ins .ret none) := by
    have := congrArg (·[(spAdjLines false R.af.frameSize ++
      [Line.ins (.ldp Reg.fp Reg.lr (.spPostIndexed 16)) none]).length]?) hdrop'
    simpa [List.getElem?_drop, RL.L] using this
  have ht : OnLine R.fa R.fb R.lm R.base (iterN R.step (spAdjLines false R.af.frameSize ++
      [Line.ins (.ldp Reg.fp Reg.lr (.spPostIndexed 16)) none]).length u) .ret :=
    ⟨hR.layout, hR.lm, hR.fit, hg.prog, hg.err, ⟨_, none, hj, hpcs _ (Nat.le_refl _)⟩⟩
  have e1 : iterN R.step R.retLen u' = R.step (iterN R.step (spAdjLines false R.af.frameSize ++
      [Line.ins (.ldp Reg.fp Reg.lr (.spPostIndexed 16)) none]).length u') := by
    rw [hlen, iterN_add]; rfl
  have e2 : iterN R.step R.retLen u = R.step (iterN R.step (spAdjLines false R.af.frameSize ++
      [Line.ins (.ldp Reg.fp Reg.lr (.spPostIndexed 16)) none]).length u) := by
    rw [hlen, iterN_add]; rfl
  rw [e1, e2]
  exact retAgreeX_of_ret (X := R.X) (H := R.H) ht hlk fun a ha h8 => RL.notZc_ret hR d d' ha h8

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
        (iterN ({ R with X := XI.at 0 } : RL).step ((prologueLines R.af.frameSize).length + i) R.s0)
        (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step
          ((prologueLines R.af.frameSize).length + i) t0)) ∧
      Arm.r .PC (iterN ({ R with X := XI.at 0 } : RL).step
        ((prologueLines R.af.frameSize).length + N + R.retLen) R.s0) = ra ∧
      Arm.r .PC (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step
        ((prologueLines R.af.frameSize).length + N + R.retLen) t0) = ra' ∧
      RetAgreeX (frameDrop af + K) (spv s)
        (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step
          ((prologueLines R.af.frameSize).length + N + R.retLen) t0)
        (iterN ({ R with X := XI.at 0 } : RL).step
          ((prologueLines R.af.frameSize).length + N + R.retLen) R.s0) := by
  intro vals cm hrun
  obtain ⟨N, e, e', -, hlk, ⟨⟨W, hqA, -⟩, -, -, -, -, hLB⟩, -, hpc, hpc', hre, -⟩ :=
    backend_twoRunLEF hsub hc hone htc hX hNI hTls hsym hslot ρ₀ hce hrel hrel' hargs hsw hreg hstk
      htr fuel hlm hpsF he he' hR hcov hx30 hcall htls hag hx29 vals cm hrun
  refine ⟨N, hlk, hpc, hpc', ?_⟩
  have hs : ∀ (g : Arm.ArmState → Arm.ArmState) (x : Arm.ArmState),
      iterN g ((prologueLines R.af.frameSize).length + N + R.retLen) x =
        iterN g R.retLen (iterN g ((prologueLines R.af.frameSize).length + N) x) :=
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
  exact RL.retAgreeX_rets hW0 he.abi hx30 (QW.withX (X := XI.at 0) hqA).q hre hLB.symm

end

end E2E
