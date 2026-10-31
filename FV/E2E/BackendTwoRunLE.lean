import FV.E2E.BackendTwoRunL
import FV.E2E.LinkArmProphDetE

/-!
# The machine lock from the entries (SEM1 #537, `docs/plans/uninit.md` §5.9, machine lock)

`backend_twoRunL`'s premise `hpro` (the lock after both prologues) from the two ABI entries:
entries agreeing on the masked registers but `x30`/pc and on the `frameDrop + K` bytes below `sp`
(`EntryAgree`), and on `x29` (#705: the prologue saves it in the frame record, which the lock
keeps equal), with body-entry worlds the same outside `F ∪ D`, are locked at `Zc` of the initial
configurations; the prologue keeps the lock (it reads nothing, writes `x29`/`sp` and the pushed
callee-saved registers from equal values, and the record, whose saved-LR word is in `Zc`).

* `mem_eq_of_read_mem_bytes`, `RL.jtByte_mem_eq`, `RL.jtByte_codeAddr`, `RL.lrWord_Zc`;
* `stEqOutX_entryZ`, `pushLines_x30`, `prologue_exempt`, `stEqOutX_prologueZ`;
* **`backend_twoRunLE`**.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- Two states reading equal `n` bytes at `a` hold equal bytes there. -/
theorem mem_eq_of_read_mem_bytes {n : Nat} {a : BitVec 64} {s t : Arm.ArmState}
    (h : Arm.read_mem_bytes n a s = Arm.read_mem_bytes n a t) (hn : n ≤ 2 ^ 64) {i : Nat}
    (hi : i < n) : s.mem (a + BitVec.ofNat 64 i) = t.mem (a + BitVec.ofNat 64 i) := by
  rw [Arm.Memory.State.read_mem_bytes_eq_mem_read_bytes,
    Arm.Memory.State.read_mem_bytes_eq_mem_read_bytes] at h
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  have := congrArg (fun v => v.getLsbD (i * 8 + b)) h
  simp only [Arm.Memory.getLsbD_read_bytes hn] at this
  simpa [show i * 8 + b < n * 8 by omega, show (i * 8 + b) / 8 = i by omega,
    show (i * 8 + b) % 8 = b by omega] using this

/-- **The jump-table bytes are equal in two states holding the code words.** -/
theorem RL.jtByte_mem_eq {R : RL} (hR : R.Wf) {s t : Arm.ArmState}
    (hs : ∀ k w, R.fb.words[k]? = some w →
      Arm.read_mem_bytes 4 (R.base + BitVec.ofNat 64 (4 * k)) s = w)
    (ht : ∀ k w, R.fb.words[k]? = some w →
      Arm.read_mem_bytes 4 (R.base + BitVec.ofNat 64 (4 * k)) t = w)
    {a : BitVec 64} (h : R.JTByte a) : s.mem a = t.mem a := by
  obtain ⟨j, tg, bs, hj, i, hi, rfl⟩ := h
  obtain ⟨hal, w, -, hw⟩ := FnAsm.layout_word hR.layout hR.lm (j := j) hj rfl
  have e1 := hs _ w hw
  have e2 := ht _ w hw
  have hpc : R.pcOf j = R.base + BitVec.ofNat 64 (4 * (lineOffset R.fa.lines.toList j / 4)) := by
    simp only [RL.pcOf, RL.L, Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hal)]
  rw [← hpc] at e1 e2
  exact mem_eq_of_read_mem_bytes (e1.trans e2.symm) (by decide) hi

/-- **A jump-table byte is a code address** of a state holding the program. -/
theorem RL.jtByte_codeAddr {R : RL} (hR : R.Wf) {s : Arm.ArmState}
    (hp : s.program = R.fb.program R.base) {a : BitVec 64} (h : R.JTByte a) : CodeAddr s a := by
  obtain ⟨j, tg, bs, hj, i, hi, rfl⟩ := h
  obtain ⟨hal, w, -, hw⟩ := FnAsm.layout_word hR.layout hR.lm (j := j) hj rfl
  have hpc : R.pcOf j = R.base + BitVec.ofNat 64 (4 * (lineOffset R.fa.lines.toList j / 4)) := by
    simp only [RL.pcOf, RL.L, Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hal)]
  rw [hpc]
  exact codeAddr_word hp hw hi

/-- **The frame record's saved-LR word is in the lock set.** -/
theorem RL.lrWord_Zc {R : RL} (hR : R.Wf) (c c' : MConf CV Arm.ArmState) {k : Nat} (hk8 : 8 ≤ k)
    (hk : k < 16) : R.Zc c c' (spv R.s0 - 16#64 + BitVec.ofNat 64 k) := by
  have hframe := lowerRFunc_frame hR.alloc
  have hst0 := hR.stack.frame
  have hd : frameDrop R.af = R.af.frameSize + 16 := by simp [frameDrop, hframe]
  have hlt := (spv R.s0).isLt
  have hsp := hst0.1
  have hk64 : (spv R.s0 - 16#64 + BitVec.ofNat 64 k).toNat = (spv R.s0).toNat - 16 + k := by
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := k) (by omega)]
    omega
  have htop : spv R.s0 - 16#64 + BitVec.ofNat 64 k =
      R.topB + BitVec.ofNat 64 (clobberBytes R.af.saves + k) := by
    rw [RL.topB, RL.topN, BitVec.ofNat_add, BitVec.ofNat_add]; bv_omega
  refine ⟨?_, ?_, ?_, .inl (RL.FK_F (htop ▸ fplr_inF hR hframe _ (by simp only [RL.topN]; omega)))⟩
  · rintro ⟨o, ho, ho8, he⟩
    have hB := (spBody_toNat hR.stack).1
    have he' := congrArg BitVec.toNat he
    rw [hk64, BitVec.toNat_add, BitVec.toNat_ofNat, RL.spB, hB] at he'
    rw [Nat.mod_eq_of_lt (a := o) (by omega), Nat.mod_eq_of_lt (by omega)] at he'
    rcases ho8 with h | h
    · omega
    · cases h
  · intro hj
    have hc := RL.jtByte_codeAddr hR hR.prog0 hj
    have h2 := hst0.2 _ hc
    have : spv R.s0 - 16#64 + BitVec.ofNat 64 k - (spv R.s0 - BitVec.ofNat 64 (R.af.frameSize + 16)) =
        BitVec.ofNat 64 (R.af.frameSize + k) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt (a := R.af.frameSize + 16) (by omega),
        Nat.mod_eq_of_lt (a := R.af.frameSize + k) (by omega)]
      omega
    rw [this, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h2
    omega
  · rintro ⟨h1, -⟩
    have hB := (spBody_toNat hR.stack).1
    rw [hk64, RL.spB, hB] at h1
    omega

/-- **The lock at the two entries**: equal masked registers but `x30`/pc and equal bytes below
`sp` (`EntryAgree`), equal `x29`, body-entry worlds the same outside `F ∪ D`; the lock set's
world difference contains the worlds' (`hW`). -/
theorem stEqOutX_entryZ {R : RL} (hR : R.Wf) {t0 : Arm.ArmState} {ra ra' : BitVec 64}
    (hent : AbiCall R.fb R.base ra R.s0) (hent' : AbiCall R.fb R.base ra' t0)
    {A A' : Reg → Prop} {F' D : BitVec 64 → Prop} {w₀ w₀' : Arm.ArmState}
    (hbe : BodyEntryW R.F A R.af R.s0 w₀) (hbe' : BodyEntryW F' A' R.af t0 w₀')
    (hF' : ∀ a, F' a → R.F a) (hsw : SameWorld (fun b => R.F b ∨ D b) w₀ w₀')
    (hag : EntryAgree (frameDrop R.af + R.K) R.s0 t0)
    (hx29 : Arm.r (.GPR 29#5) R.s0 = Arm.r (.GPR 29#5) t0)
    {c c' : MConf CV Arm.ArmState} (hW : ∀ a, w₀.mem a ≠ w₀'.mem a → MConf.WDiff c c' a) :
    StEqOutX (R.Zc c c') R.s0 t0 := by
  refine ⟨fun f hf => ?_, hent.program.trans hent'.program.symm, fun a ha => ?_⟩
  · by_cases hm : Masked f
    · by_cases hpc : f = .PC
      · subst hpc; rw [hent.pc, hent'.pc]
      · exact hag.1 f hm hpc hf
    · by_cases h29 : f = .GPR 29#5
      · subst h29; exact hx29
      · by_cases h31 : f = .GPR 31#5
        · subst h31
          have e3 : spv w₀ = spv w₀' := hsw.1 _ (by simp [Masked])
          have e : spv R.s0 - BitVec.ofNat 64 (frameDrop R.af) =
              spv t0 - BitVec.ofNat 64 (frameDrop R.af) := hbe.sp.symm.trans (e3.trans hbe'.sp)
          have := congrArg (· + BitVec.ofNat 64 (frameDrop R.af)) e
          simpa [spv] using this
        · rw [← hbe.other f hm h29 h31, hsw.1 f hm, hbe'.other f hm h29 h31]
  · by_cases hfr : R.FrameRd false a
    · obtain ⟨o, ho, -, rfl⟩ := hfr
      apply hag.2
      obtain ⟨hB, hK⟩ := spBody_toNat hR.stack
      have hlt := (spv R.s0).isLt
      have e : (R.spB + BitVec.ofNat 64 o).toNat = (spv R.s0).toNat - frameDrop R.af + o := by
        rw [BitVec.toNat_add, RL.spB, hB, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega),
          Nat.mod_eq_of_lt (by omega)]
      simp only [StackBelow, e]
      omega
    · by_cases hjt : R.JTByte a
      · exact RL.jtByte_mem_eq hR hent.code hent'.code hjt
      · by_cases hds : StackBelow R.K R.spB a
        · apply hag.2
          obtain ⟨hB, hK⟩ := spBody_toNat hR.stack
          obtain ⟨h1, h2⟩ := hds
          rw [RL.spB, hB] at h1 h2
          exact ⟨by omega, by omega⟩
        · by_cases hpr : probeHit R.af (spv R.s0) a = true
          · -- a byte the stack probes zero: in the frame or the dead stack below it
            apply hag.2
            have hst := hR.stack
            have hf : R.af.frame = true := by
              simp only [probeHit, Bool.and_eq_true] at hpr; exact hpr.1
            have hd : frameDrop R.af = R.af.frameSize + 16 := by simp [frameDrop, hf]
            have hb := probeHit_below (by rw [hd]; exact hst.probe.1) hpr
            have h2 := hst.2
            unfold StackBelow at hb ⊢
            omega
          have hn : ¬ (R.F a ∨ MConf.WDiff c c' a) := fun h => ha ⟨hfr, hjt, hds, h⟩
          have hF : ¬ R.F a := fun h => hn (.inl h)
          have hsp : spv t0 = spv R.s0 := by
            have e3 : spv w₀ = spv w₀' := hsw.1 _ (by simp [Masked])
            have e : spv R.s0 - BitVec.ofNat 64 (frameDrop R.af) =
                spv t0 - BitVec.ofNat 64 (frameDrop R.af) := hbe.sp.symm.trans (e3.trans hbe'.sp)
            have := congrArg (· + BitVec.ofNat 64 (frameDrop R.af)) e
            simpa using this.symm
          have hpr' : probeHit R.af (spv t0) a = false := by
            rw [hsp]; simpa using hpr
          rw [← probeMem_of_not (by simpa using hpr), ← probeMem_of_not hpr', ← hbe.mem a hF,
            ← hbe'.mem a (fun h => hF (hF' a h))]
          exact Classical.byContradiction fun h => hn (.inr (hW a h))

theorem spAdjLines_x30 (sub : Bool) (size : Nat) :
    ∀ x t, Line.ins x t ∈ spAdjLines sub size → x.x30Exempt = false := by
  intro x t hln
  unfold spAdjLines at hln
  split at hln
  · simp at hln
  · split at hln
    · simp only [List.mem_singleton, Line.ins.injEq] at hln
      obtain ⟨rfl, -⟩ := hln; cases sub <;> simp [Insn.x30Exempt]
    · rw [List.mem_append, loadConst64_eq] at hln
      rcases hln with hln | hln
      · simp only [List.mem_cons] at hln
        rcases hln with h | hln
        · simp only [Line.ins.injEq] at h; obtain ⟨rfl, -⟩ := h; simp [Insn.x30Exempt]
        · obtain ⟨c, i, h⟩ := movkLines_mem hln
          simp only [Line.ins.injEq] at h; obtain ⟨rfl, -⟩ := h; simp [Insn.x30Exempt]
      · simp only [List.mem_singleton, Line.ins.injEq] at hln
        obtain ⟨rfl, -⟩ := hln; cases sub <;> simp [Insn.x30Exempt]

/-- The pushes of registers the pushes handle (no fp/lr) name no `x30`-exempt instruction. -/
theorem pushLines_x30 {int : Bool} {rs : List Reg} (hrs : ∀ r ∈ rs, PushReg int r) :
    ∀ x t, Line.ins x t ∈ pushLines int rs → x.x30Exempt = false := by
  intro x t hln
  rw [pushLines_eq, List.mem_append] at hln
  rcases hln with hln | hln
  · split at hln
    · simp only [List.mem_singleton, Line.ins.injEq] at hln
      obtain ⟨rfl, -⟩ := hln
      cases int <;> simp [Insn.x30Exempt]
    · simp at hln
  · obtain ⟨p, hp, e⟩ := List.mem_map.1 hln
    have hp1 := hrs _ ((pairsOf_mem rs).1 p (List.mem_reverse.1 hp)).1
    have hne : p.1 ≠ Reg.fp := by
      intro e1; rw [e1] at hp1; simp [PushReg, Reg.fp] at hp1
    simp only [pushLine2, Line.ins.injEq] at e
    obtain ⟨rfl, -⟩ := e
    cases int <;> simp [Insn.x30Exempt, hne]

/-- **The only `x30`-exempt line of the prologue is its first, the frame-record store.** -/
theorem prologue_exempt {saves : List Reg} (hsv : SavesOk saves) {size i : Nat} {calls : Bool}
    {x : Insn} {t : Option Clif.TrapCode}
    (h : (prologueLines saves size calls)[i]? = some (.ins x t)) (hx : x.x30Exempt = true) :
    i = 0 ∧ x = .stp .fp .lr (.spPreIndexed (-16)) := by
  rw [prologueLines_eq] at h
  match i, h with
  | 0, h =>
    simp only [List.cons_append, List.getElem?_cons_zero, Option.some.injEq, Line.ins.injEq] at h
    exact ⟨rfl, h.1.symm⟩
  | 1, h =>
    simp only [List.cons_append, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
      Line.ins.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp [Insn.x30Exempt] at hx
  | i + 2, h =>
    simp only [List.cons_append, List.getElem?_cons_succ, List.nil_append] at h
    have hm := List.mem_of_getElem? h
    simp only [List.mem_append] at hm
    have : x.x30Exempt = false := by
      rcases hm with hm | hm | hm | hm
      · rcases probeLines_mem hm with e | e | ⟨_, e⟩ <;>
          (simp only [Line.ins.injEq] at e; obtain ⟨rfl, -⟩ := e; simp [Insn.x30Exempt])
      · exact pushLines_x30 hsv.int x t hm
      · exact pushLines_x30 hsv.float x t hm
      · exact spAdjLines_x30 true _ x t hm
    rw [hx] at this; cases this

/-- `stpAddr` of the frame-record store is `sp - 16`. -/
theorem stpAddr_fr (s : Arm.ArmState) : stpAddr 0x7e s = spv s - 16#64 := by
  have h : BitVec.signExtend 64 (126 : BitVec 7) <<< 3 = -16#64 := by decide
  simp only [stpAddr, spv, Arm.read_gpr, BitVec.setWidth_eq]
  rw [h, BitVec.sub_eq_add_neg]
  rfl

/-- **The prologue keeps a lock at every step** whose set contains the frame record's saved-LR
word: it reads nothing and names `x30` only in the record store. -/
theorem stEqOutX_prologueZ_le {R : RL} (hR : R.Wf) {ra : BitVec 64}
    (hent : AbiCall R.fb R.base ra R.s0) (hx30 : R.fa.x30Free R.lm = true)
    {Z : BitVec 64 → Prop}
    (hLR : ∀ k, 8 ≤ k → k < 16 → Z (spv R.s0 - 16#64 + BitVec.ofNat 64 k)) {t : Arm.ArmState}
    (h : StEqOutX Z t R.s0) :
    ∀ i ≤ (prologueLines R.af.saves R.af.frameSize R.af.isCaller).length,
      StEqOutX Z (iterN R.step i t) (iterN R.step i R.s0) := by
  obtain ⟨-, hfs, -, hsv, -, hcb, -, -, -⟩ := RL.frame_facts hR
  have hst0 := hR.stack.frame
  have hs : R.af.frameSize < 2 ^ 64 := by have := hst0.1; have := (spv R.s0).isLt; omega
  obtain ⟨vb, items, code, ls, ps1, ps2, T, -, -, -, -, -, hj0, hdrop⟩ := entry_block hR
  obtain ⟨s', hsteps, -, -, -, -, -, -⟩ :=
    prologue_ok (calls := R.af.isCaller) (R.envOf 1) hs hsv (by rw [hfs]; exact hcb) R.s0 hent.spAligned
  have hpc1 : Arm.r .PC R.s0 = R.pcOf 1 := by
    rw [hent.pc]
    simp only [RL.pcOf, RL.L] at hj0 ⊢
    rw [lineOffset_succ _ _ _ hj0]
    simp [lineOffset, Line.size]
  have hat : ∀ k ln, (prologueLines R.af.saves R.af.frameSize R.af.isCaller)[k]? = some ln →
      R.fa.lines.toList[1 + k]? = some ln := by
    intro k ln hk
    have := congrArg (·[k]?) hdrop
    simp only [List.getElem?_drop, RL.L] at this
    rw [this, List.getElem?_append_left (List.getElem?_eq_some_iff.1 hk).1]
    exact hk
  have hhook : ∀ i t, Line.ins i t ∈ prologueLines R.af.saves R.af.frameSize R.af.isCaller → i.hooked = false :=
    fun i t hm => by
      obtain ⟨x, e, hh, -⟩ := prologueLines_ins _ _ _ hm; cases e; exact hh
  have hinter := stepsOk_interOk hsteps hent.err
  have hpcs := iterN_execLines_pc (X := R.X) (H := R.H) hR.layout hR.lm hR.fit _ 1 R.s0 s' hat hhook
    hent.program (by rw [hpc1]; rfl) hent.err hinter hsteps.exec
  have hgx := (iterN_steps hR hdrop (fun ln h => by
      obtain ⟨x, e, hh, -⟩ := prologueLines_ins _ _ ln h; exact ⟨x, e, hh⟩)
    hent.program hpc1 hent.err hsteps).2.2.2 (prologueLines_tail _ _)
    (.inl (by rw [hent.pc]; exact RL.not_postCall_base hR hent.fits))
    (linesReads_noLoads (prologueLines_noLoads _ _))
  intro i hi
  induction i with
  | zero => exact h
  | succ i ih =>
    have hi' : i < (prologueLines R.af.saves R.af.frameSize R.af.isCaller).length := by omega
    have hl := ih (by omega)
    obtain ⟨ln, hln⟩ : ∃ ln, (prologueLines R.af.saves R.af.frameSize R.af.isCaller)[i]? = some ln :=
      ⟨_, List.getElem?_eq_getElem hi'⟩
    obtain ⟨x, rfl, hhx, -⟩ := prologueLines_ins _ _ _ (List.mem_of_getElem? hln)
    have hj := hat i _ hln
    have hg := hgx i hi'
    have ht : OnLine R.fa R.fb R.lm R.base (iterN R.step i R.s0) x :=
      ⟨hR.layout, hR.lm, hR.fit, hg.prog, hg.err, ⟨1 + i, none, hj, hpcs i (by omega)⟩⟩
    have hex : x.x30Exempt = true → i = 0 ∧ x = .stp .fp .lr (.spPreIndexed (-16)) :=
      prologue_exempt hsv hln
    have hstep := stEqOutX_line (X := R.X) (H := R.H) ht hx30
      (prologueLines_tail _ _ x none (List.mem_of_getElem? hln))
      (fun e => by subst e; have := (hex rfl).2; cases this) hl
      (fun _ => by
        apply readsAvoid_stepiEvs
        intro a ha ev hev hdir k hk
        obtain ⟨j', a', ha', hd⟩ := ht.decodeAt
        rw [hd, Option.some.injEq] at ha
        subst ha
        have hcov := (ExecBytes.instEvs_cover hev).1 hdir
        rw [Insn.memReads_nil (prologueLines_noLoads _ _ x none (List.mem_of_getElem? hln)) ha'] at hcov
        cases hcov)
      (fun e => by subst e; have := (hex (by decide)).2; cases this)
      (fun hb => by
        rcases hb with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp [Insn.hooked] at hhx)
      (fun _ _ hb => by obtain ⟨_, _, _, rfl⟩ := hb; simp [Insn.hooked] at hhx)
    have e1 : iterN R.step (i + 1) t = R.step (iterN R.step i t) := by rw [iterN_add]; rfl
    have e2 : iterN R.step (i + 1) R.s0 = R.step (iterN R.step i R.s0) := by rw [iterN_add]; rfl
    rw [e1, e2]
    refine hstep.mono fun a ha => ?_
    rcases ha with ha | ⟨e, k, hk8, hk16, rfl⟩
    · exact ha
    · obtain ⟨rfl, -⟩ := hex (by rw [e]; decide)
      rw [stpAddr_fr]
      exact hLR k hk8 hk16

/-- **The prologue keeps a lock** whose set contains the frame record's saved-LR word: it reads
nothing and names `x30` only in the record store. -/
theorem stEqOutX_prologueZ {R : RL} (hR : R.Wf) {ra : BitVec 64}
    (hent : AbiCall R.fb R.base ra R.s0) (hx30 : R.fa.x30Free R.lm = true)
    {Z : BitVec 64 → Prop}
    (hLR : ∀ k, 8 ≤ k → k < 16 → Z (spv R.s0 - 16#64 + BitVec.ofNat 64 k)) {t : Arm.ArmState}
    (h : StEqOutX Z t R.s0) :
    StEqOutX Z (iterN R.step (prologueLines R.af.saves R.af.frameSize R.af.isCaller).length t)
      (iterN R.step (prologueLines R.af.saves R.af.frameSize R.af.isCaller).length R.s0) :=
  stEqOutX_prologueZ_le hR hent hx30 hLR h _ (Nat.le_refl _)

section
variable {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
  {af : AFunc} {fa : FnAsm} {fb : FnBin}

set_option maxHeartbeats 4000000 in
/-- **`backend_twoRunL` from the entries** (module doc): `hpro` from `EntryAgree` of the two ABI
entries and their equal `x29` (#705). -/
theorem backend_twoRunLE (hsub : InSubset p f) (hc : Compiled f k vc vcp rf af fa fb)
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
    (hfr : ∀ n Ok c i u x, ({ R with X := XI.at n } : RL).InSeg Ok c i u →
      ({ R with X := XI.at n } : RL).AtLine u x → x.x30Exempt = true → x.tlsTail = false →
      (∃ m, x = .bl m) ∨ ∃ r, x = .blr r)
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
    ∃ N e e',
      (∀ i < (prologueLines R.af.saves R.af.frameSize R.af.isCaller).length,
        ({ R with X := XI.at 0 } : RL).GoodXNY (fun _ => True)
          (iterN ({ R with X := XI.at 0 } : RL).step i R.s0) ∧
        ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).GoodXNY (fun _ => True)
          (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step i t0)) ∧
      (∀ i < N, ∃ c c', StEqOutX (R.Zc c c')
        (iterN ({ R with X := XI.at 0 } : RL).step ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + i) R.s0)
        (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step
          ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + i) t0)) ∧
      JR R ({ R with s0 := t0, G := G' } : RL) (KJL R XI t0 G' F)
        (fun d d' u u' => StEqOutX (R.Zc d d') u u')
        (iterN ({ R with X := XI.at 0 } : RL).step ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + N) R.s0) e
        (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step
          ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + N) t0) e' ∧
      (∀ i < R.retLen,
        ({ R with X := XI.at 0 } : RL).GoodXNY (fun _ => True)
          (iterN ({ R with X := XI.at 0 } : RL).step
            ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + N + i) R.s0) ∧
        ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).GoodXNY (fun _ => True)
          (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step
            ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + N + i) t0)) ∧
      Arm.r .PC (iterN ({ R with X := XI.at 0 } : RL).step
        ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + N + R.retLen) R.s0) = ra ∧
      Arm.r .PC (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step
        ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + N + R.retLen) t0) = ra' ∧
      R.RetsAt e ∧ R.RetsAt e' := by

  have hpro : StEqOutX
      (R.Zc (MConf.init R.rf (locVal R.fr (iterN ({ R with X := XI.at 0 } : RL).step
          (prologueLines R.af.saves R.af.frameSize R.af.isCaller).length R.s0)) w₀)
        (MConf.init R.rf (locVal R.fr (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step
          (prologueLines R.af.saves R.af.frameSize R.af.isCaller).length t0)) w₀'))
      (iterN ({ R with X := XI.at 0 } : RL).step (prologueLines R.af.saves R.af.frameSize R.af.isCaller).length R.s0)
      (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step
        (prologueLines R.af.saves R.af.frameSize R.af.isCaller).length t0) := by
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
    exact (stEqOutX_prologueZ hW0 he.abi hx30 (fun k h8 h16 => RL.lrWord_Zc hW0 _ _ h8 h16)
      (stEqOutX_entryZ hW0 he.abi he'.abi he.body he'.body (fun _ h => h) hsw hag hx29
        (fun _ h => by exact h)).symm).symm
  exact backend_twoRunL hsub hc hone htc hX hNI hTls hsym hslot ρ₀ hce hrel hrel' hargs hsw hreg
    hstk htr fuel hlm hpsF he he' hR hcov hx30 hfr hcall htls hpro

end

end E2E
