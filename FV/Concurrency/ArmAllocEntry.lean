import FV.Concurrency.ArmAllocBranch
import FV.Concurrency.CallCompose

/-!
# Layer 4b from the ABI entry: the prologue (T2h, #311)

Layer 4b's run-level theorems (`arm_alloc_refines_br`, …) start at the allocated code's entry
configuration, i.e. after the prologue. Here the precise Arm run starts at the **ABI entry**
`R.s0` (`AbiCall`: the pc at the function's first word, an aligned `sp`):

* `stp_fplr_evs`: the prologue's `stp x29, x30, [sp, #-16]!` has one plain write at `sp - 16`
  and is no exclusive;
* `q_init_lines`: `RegLevelFrame.q_init` with the prologue's lines exposed (`LinesAt`) and the
  number of its steps (`prologueLines`' length): `Q ∧ AInv` at the entry configuration after
  them;
* `prologue_evs`: every step of the prologue accesses only the fp/lr slot (in the frame `R.F`),
  with a plain write, and is no store exclusive; `prun_prologue`: a precise run under `OkPriv`
  through (a prefix of) the prologue is the single-core run, its events private plain writes;
* `refines_privW`: an Arm segment of private writes without load exclusive refines the empty
  source;
* **`arm_alloc_refines_entry`**: every precise run from the ABI entry under `OkPriv` realizes a
  run of the allocated code from its entry configuration (any `BodyEntryW` world `w₀`), with
  `arm_alloc_refines_br`'s conclusion: the prologue's write is private (`PrivA`), the rest by
  `arm_alloc_refines_br`, composed by `CallCompose.Refines.app`.
-/

namespace Concurrency.ArmAllocThread

open Arm ArmFoot ArmThread ArmInstFoot VCodeThread Backend Backend.Proof AllocThread ThreadRefine
  E2E Code VCodeEvents

/-! ## The prologue's `stp` -/

/-- **The prologue's `stp x29, x30, [sp, #-16]!`**: one plain write at `sp - 16`, no
exclusive. -/
theorem stp_fplr_evs (env : Env) (s : ArmState) (hal : CheckSPAlignment s) :
    ∃ a, (Insn.stp Reg.fp Reg.lr (.spPreIndexed (-16))).toArmInst env = .ok a ∧ isExcl a = false ∧
      ∀ e ∈ instEvs a s, e.addr = spOf s - 16#64 ∧ e.k = .plainW := by
  refine ⟨_, by simp [csimp_rules, Reg.fp, Reg.lr, pure, Except.pure]; rfl, rfl, ?_⟩
  have hal' := spAligned hal
  intro e he
  simp [instEvs, pairEvs, LDST.reg_pair_constrain_unpredictable, hal, Arm.BitVec.lsb] at he
  subst he
  refine ⟨?_, rfl⟩
  simp only [read_gpr, spOf]
  bv_omega

/-! ## After the prologue -/

/-- **`q_init` with the prologue's lines**: from the ABI entry, the prologue's lines run
(`LinesAt` at line 1) to the state after them, where `Q ∧ AInv` hold at the entry configuration
of the allocated code (store = the machine's locations, world = any body-entry world `w₀`). -/
theorem q_init_lines {R : RL} (hR : R.Wf) {ra : BitVec 64} (hent : AbiCall R.fb R.base ra R.s0)
    {w₀ : ArmState} (hbe : BodyEntryW R.F R.vc.EntryArg R.af R.s0 w₀) :
    LinesAt R 1 (prologueLines R.af.frameSize) R.s0
      (iterN R.step (prologueLines R.af.frameSize).length R.s0) ∧
    Q R (iterN R.step (prologueLines R.af.frameSize).length R.s0)
      (MConf.init R.rf (locVal R.fr (iterN R.step (prologueLines R.af.frameSize).length R.s0)) w₀) ∧
    AInv R (MConf.init R.rf (locVal R.fr (iterN R.step (prologueLines R.af.frameSize).length R.s0))
      w₀) := by
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
  obtain ⟨hiter, hpc', -, -⟩ := iterN_steps hR hdrop
    (fun ln h => by obtain ⟨x, e, hh, -⟩ := prologueLines_ins _ ln h; exact ⟨x, e, hh⟩)
    hent.program hpc1 hent.err hsteps
  obtain ⟨herr', hprog'⟩ := hsteps.err
  have hlat : LinesAt R 1 (prologueLines R.af.frameSize) R.s0 s' :=
    ⟨lines_at hdrop, fun x t h => by
      obtain ⟨x', e, hh, -⟩ := prologueLines_ins _ _ h; cases e; exact hh,
      hent.program, by rw [hpc1]; rfl, hent.err, stepsOk_interOk hsteps hent.err, hsteps.exec⟩
  rw [hiter]
  refine ⟨hlat, ?_⟩
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
  refine ⟨?_, ?_⟩
  · have hitems : R.rf.blocks[0]! = items := by simp [getElem!_def, hit]
    simp only [MConf.init, hitems]
    refine ⟨1 + (prologueLines R.af.frameSize).length, vb, items, [], code, ls, ps1, ps2, T, hvb,
      hit, rfl, itemsChecked_block hR hvb hit, hcode, hls, htr, ?_, hpc', ?_⟩
    · rw [← List.drop_drop, hdrop, List.drop_left]
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

/-! ## The prologue's events -/

theorem kinds_prologue_tail (n : Nat) :
    kinds (Line.ins (.mov true Reg.fp .sp) none :: spAdjLines true n) = [] := by
  have h := kinds_prologueLines n
  rw [prologueLines_eq, show [Line.ins (.stp Reg.fp Reg.lr (.spPreIndexed (-16))) none,
      Line.ins (.mov true Reg.fp .sp) none] ++ spAdjLines true n =
      [Line.ins (.stp Reg.fp Reg.lr (.spPreIndexed (-16))) none] ++
        (Line.ins (.mov true Reg.fp .sp) none :: spAdjLines true n) from rfl, kinds_append,
    show kinds [Line.ins (.stp Reg.fp Reg.lr (.spPreIndexed (-16))) none] = [.plainW] from rfl] at h
  simpa using h

/-- **The prologue's steps**: each accesses only the fp/lr slot (in `R.F`) with a plain write, and
none is a store exclusive. -/
theorem prologue_evs {R : RL} (hR : R.Wf) {ra : BitVec 64} (hent : AbiCall R.fb R.base ra R.s0)
    {s' : ArmState} (hlat : LinesAt R 1 (prologueLines R.af.frameSize) R.s0 s') :
    ∀ i < (prologueLines R.af.frameSize).length,
      (∀ e ∈ stepEvs (iterN R.step i R.s0), R.F e.addr ∧ e.k = .plainW) ∧
        NoStx (iterN R.step i R.s0) := by
  intro i hi
  have hstep := step_execLines (X := R.X) (H := R.H) hR.layout hR.lm hR.fit hlat.at_ hlat.hook
    hlat.prog hlat.pc hlat.err hlat.inter hlat.run i hi
  obtain ⟨x, t, a, hli, ha, hdec, hev, -⟩ := hstep
  have hns : isExcl a = false → NoStx (iterN R.step i R.s0) := fun hx rel rs rn hc => by
    rw [show R.step = ArmStepX R.X R.H R.fa from rfl, cls_of_decode hdec] at hc
    exact clsOf_ne_stx hx rel rs rn hc
  rw [show R.step = ArmStepX R.X R.H R.fa from rfl, hev]
  rw [prologueLines_eq] at hli
  cases i with
  | zero =>
    simp only [List.cons_append, List.getElem?_cons_zero, Option.some.injEq, Line.ins.injEq] at hli
    obtain ⟨rfl, -⟩ := hli
    have hal : CheckSPAlignment R.s0 := (checkSP_iff _).2 hent.spAligned
    obtain ⟨a', ha', hx, hevs⟩ := stp_fplr_evs ⟨lineOffset R.fa.lines.toList (1 + 0), (R.lm[·]?)⟩
      R.s0 hal
    rw [ha] at ha'
    cases ha'
    refine ⟨fun e he => ?_, hns hx⟩
    obtain ⟨hadd, hk⟩ := hevs e he
    refine ⟨?_, hk⟩
    rw [hadd]
    have := RL.FK_F (fplr_inF hR (lowerRFunc_frame hR.alloc) 0 (by omega))
    simpa [spOf, spv] using this
  | succ i =>
    have hmem : Line.ins x t ∈ Line.ins (.mov true Reg.fp .sp) none :: spAdjLines true R.af.frameSize := by
      simp only [List.cons_append, List.getElem?_cons_succ] at hli
      exact List.mem_of_getElem? hli
    have hk := kinds_mem_none (kinds_prologue_tail _) hmem
    rw [instEvs_none ha hk]
    exact ⟨fun e he => absurd he List.not_mem_nil, hns (isExcl_none ha hk)⟩

/-- **A precise run through (a prefix of) the prologue** under `OkPriv` is the single-core run;
its events are private plain writes. -/
theorem prun_prologue {R : RL} (hR : R.Wf) {ra : BitVec 64} (hent : AbiCall R.fb R.base ra R.s0)
    {s' : ArmState} (hlat : LinesAt R 1 (prologueLines R.af.frameSize) R.s0 s') {mon : Mon}
    {L : List Lab} {t1 : ArmState × Mon} (hr : PRun Policy.arm R.step (OkPriv R) (R.s0, mon) L t1)
    (hL : L.length ≤ (prologueLines R.af.frameSize).length) :
    t1.1 = iterN R.step L.length R.s0 ∧ PrivW (PrivA R) (evTr L) ∧
      ∀ p y, evAt (evTr L) p = some y → y.k = .plainW := by
  have hpe := prologue_evs hR hent hlat
  obtain ⟨h1, h2⟩ := prun_priv hr fun i hi =>
    ⟨fun e he => (hpe i (by omega)).1 e he |>.1, (hpe i (by omega)).2⟩
  have hk : ∀ p y, evAt (evTr L) p = some y → R.F y.addr ∧ y.k = .plainW := by
    intro p y hy
    rw [h2] at hy
    obtain ⟨j, k⟩ := p
    simp only [evAt] at hy
    cases hj : (segEvs R.step L.length R.s0)[j]? with
    | none => rw [hj] at hy; cases hy
    | some x =>
      rw [hj] at hy
      simp only [Option.bind_some] at hy
      obtain ⟨i, hi, rfl⟩ := mem_segEvs (List.mem_of_getElem? hj)
      exact (hpe i (by omega)).1 y (List.mem_of_getElem? hy)
  exact ⟨h1, fun p y hy _ => privA_addr.2 (hk p y hy).1, fun p y hy => (hk p y hy).2⟩

/-- **A segment of private writes without load exclusive refines the empty source.** -/
theorem refines_privW {K : Type} {MK : K → AKind → Prop} {Priv : Nat → Prop} {T : List (List Ev)}
    (h : PrivW Priv T) :
    Refines MK Priv (MonPair T) ([] : List (List (Prog.Ev K ClifThread.BVal))) (PrepThread.conv T)
      id where
  ev p x hx := by rw [evAt_nil] at hx; cases hx
  mono p _ hp := by rw [evAt_nil] at hp; cases hp
  shared p x hx := by rw [evAt_nil] at hx; cases hx
  priv p y hy hW _ := by
    rw [evAt_conv] at hy
    cases hT : evAt T p with
    | none => rw [hT] at hy; cases hy
    | some z =>
      rw [hT] at hy
      simp only [Option.map_some, Option.some.injEq] at hy
      subst hy
      exact h p z hT (by simpa [ProgE2E.convEv] using hW)
  len j hj := absurd hj (Nat.not_lt_zero _)
  pair j hj := absurd hj (Nat.not_lt_zero _)
  pair_inv p _ hp := by rw [evAt_nil] at hp; cases hp

/-! ## From the ABI entry -/

/-- **Layer 4b from the ABI entry** (module doc): every precise run under `OkPriv` from the ABI
entry realizes, on a prefix, a run of the allocated code from its entry configuration
(`MConf.init` with the body-entry world `w₀`), with `Refines` (equal kinds, the addresses outside
the world private, the atomic updates monitor pairs), up to the allocated code's return, trap or
undefined behaviour (`Done`), for functions in `MemScopeB`. -/
theorem arm_alloc_refines_entry {R : RL} (hR : R.Wf) (hsc : MemScopeB R) {ra : BitVec 64}
    (hent : AbiCall R.fb R.base ra R.s0) {w₀ : ArmState}
    (hbe : BodyEntryW R.F R.vc.EntryArg R.af R.s0 w₀) {mon : Mon} {ls : List Lab}
    {t' : ArmState × Mon} (hr : PRun Policy.arm R.step (OkPriv R) (R.s0, mon) ls t') :
    ∃ m₀ n trS cE ψ, n ≤ ls.length ∧
      MTRun R.vc R.rf R.sem ckeep (cEvs R.F R.ctx) (MConf.init R.rf m₀ w₀) trS cE ∧
      Refines (· = ·) (PrivA R) (MonPair (evTr (ls.take n))) (PrepThread.conv trS)
        (PrepThread.conv (evTr (ls.take n))) ψ ∧ (n = ls.length ∨ Done R cE) := by
  obtain ⟨hlat, hq, hA⟩ := q_init_lines hR hent hbe
  have hpp : ∀ {mon : Mon} {L : List Lab} {t1 : ArmState × Mon},
      PRun Policy.arm R.step (OkPriv R) (R.s0, mon) L t1 →
      L.length ≤ (prologueLines R.af.frameSize).length →
      t1.1 = iterN R.step L.length R.s0 ∧ PrivW (PrivA R) (evTr L) ∧
        ∀ p y, evAt (evTr L) p = some y → y.k = .plainW := fun h hL => prun_prologue hR hent hlat h hL
  generalize hP : (prologueLines R.af.frameSize).length = P at hq hA hpp
  by_cases hle : ls.length ≤ P
  · -- the run ends inside the prologue: private writes only
    obtain ⟨-, hpw, -⟩ := hpp hr hle
    refine ⟨locVal R.fr (iterN R.step P R.s0), ls.length, [], _, id, Nat.le_refl _, .nil, ?_, .inl rfl⟩
    rw [List.take_length]
    exact refines_privW hpw
  · obtain ⟨v, hv, hrest⟩ := CallCompose.take_prun hr P
    have hPl : (ls.take P).length = P := by simp; omega
    obtain ⟨hv1, hpw, hpk⟩ := hpp hv (by omega)
    rw [hPl] at hv1
    obtain ⟨v1, vm⟩ := v
    simp only at hv1
    subst hv1
    obtain ⟨n2, trS, cE, ψ2, hn2, hM, href, hend⟩ := arm_alloc_refines_br hR hsc hq hA hrest
    refine ⟨_, P + n2, trS, cE, CallCompose.appMap 0 (evTr (ls.take P)).length id ψ2,
      by simp at hn2; omega, hM, ?_, ?_⟩
    · have e : evTr (ls.take (P + n2)) = evTr (ls.take P) ++ evTr ((ls.drop P).take n2) := by
        rw [List.take_add, evTr_append]
      rw [e]
      have := CallCompose.Refines.app (refines_privW (MK := (· = ·)) hpw) href
        (.inr fun a x hx hk => by rw [hpk a x hx] at hk; cases hk)
      simpa using this
    · rcases hend with h | h
      · left; simp at h; omega
      · exact .inr h

end Concurrency.ArmAllocThread
