import FV.Concurrency.ArmAllocLS
import FV.Concurrency.CallCompose
import FV.Concurrency.FrameEvs
import FV.E2E.RegLevelFrameW

/-!
# Layer 4b from the ABI entry: the prologue (T2h, #311)

Layer 4b's run-level theorems (`arm_alloc_refines_ls`, …) start at the allocated code's entry
configuration, i.e. after the prologue. Here the precise Arm run starts at the **ABI entry**
`R.s0` (`AbiCall`: the pc at the function's first word, an aligned `sp`):

* `q_init_lines`: `RegLevelFrame.q_init` with the prologue's run exposed (`ProRun` from line 1)
  and the number of its steps (`prologueSteps`): `Q ∧ AInv` at the entry configuration after
  them;
* `prologue_evs`: every step of the prologue (Cranelift's: fp/lr's `stp`, `mov x29, sp`, the
  stack probes, the pushes of the saved registers, the `sp` adjustment) accesses only fp/lr, the
  clobber area and the probed bytes (in the frame `R.F`, `FrameEvs.prologue_evsIn`; the probed
  bytes by the hypothesis `ProbeF`, #581), with plain writes, and is no store exclusive;
  `prun_prologue`: a precise run under `OkPriv` through (a prefix of) the prologue is the
  single-core run, its events private plain writes;
* `refines_privW`: an Arm segment of private writes without load exclusive refines the empty
  source; `prologue_linesAt`, `arm_alloc_refines_entryQ` (from any configuration `Q`-related to
  the state after the prologue);
* **`arm_alloc_refines_entry`**: every precise run from the ABI entry under `OkPriv` realizes a
  run of the allocated code from its entry configuration (any `BodyEntryW` world `w₀`), with
  `arm_alloc_refines_ls`'s conclusion: the prologue's writes are private (`PrivA`), the rest by
  `arm_alloc_refines_ls`, composed by `CallCompose.Refines.app`.
-/

namespace Concurrency.ArmAllocThread

open Arm ArmFoot ArmThread ArmInstFoot VCodeThread Backend Backend.Proof AllocThread ThreadRefine
  E2E Code VCodeEvents

/-! ## After the prologue -/

/-- **`q_init` with the prologue's run**: from the ABI entry, the prologue runs (`ProRun` at
line 1, `prologueSteps` machine steps) to the state after it, where `Q ∧ AInv` hold at the entry
configuration of the allocated code (store = the machine's locations, world = any body-entry
world `w₀`). (#581: the former first conjunct, `LinesAt` (a straight-line run of the prologue's
lines, `prologueLines`' length steps), became false with Cranelift's stack-probe loop, whose
`b.gt` jumps back; the run is `ProRun`, its steps `prologueSteps`, both as before without the
loop.) -/
theorem q_init_lines {R : RL} (hR : R.Wf) {ra : BitVec 64} (hent : AbiCall R.fb R.base ra R.s0)
    {w₀ : ArmState} (hbe : BodyEntryW R.F R.vc.EntryArg R.af R.s0 w₀) :
    ProRun (R.envOf 1) R.af.saves R.af.frameSize R.af.isCaller R.s0
      (iterN R.step (prologueSteps R.af.saves R.af.frameSize R.af.isCaller) R.s0) ∧
    Q R (iterN R.step (prologueSteps R.af.saves R.af.frameSize R.af.isCaller) R.s0)
      (MConf.init R.rf (locVal R.fr
        (iterN R.step (prologueSteps R.af.saves R.af.frameSize R.af.isCaller) R.s0)) w₀) ∧
    AInv R (MConf.init R.rf (locVal R.fr
      (iterN R.step (prologueSteps R.af.saves R.af.frameSize R.af.isCaller) R.s0)) w₀) := by
  obtain ⟨hframe, hfs, -, hsv, -, hcb, -, -, hdrop0⟩ := RL.frame_facts hR
  have hst0 := hR.stack.frame
  have hsp0 := (spv R.s0).isLt
  have hs : R.af.frameSize < 2 ^ 64 := by have := hst0.1; omega
  obtain ⟨vb, items, code, ps1, pl, X, psm, ps2, x, hvb, hit, hcode, hX, hT, htr, hpl0, hj0,
    hdrop, hx, hsc⟩ := entry_block hR
  subst hpl0
  obtain ⟨s', hsteps, hsp', hfp', ho', hfl', hm', -, -⟩ :=
    prologue_ok (calls := R.af.isCaller) (R.envOf 1) hs hsv (by rw [hfs]; exact hcb) R.s0 hent.spAligned
  have hpc1 : Arm.r .PC R.s0 = R.pcOf 1 := by
    rw [hent.pc]
    simp only [RL.pcOf, RL.L] at hj0 ⊢
    rw [lineOffset_succ _ _ _ hj0]
    simp [lineOffset, Line.size]
  obtain ⟨hiter, hpc', -, -, -⟩ := iterN_proRun hR hdrop hent.program hpc1 hent.err hsteps
  obtain ⟨herr', hprog'⟩ := hsteps.err
  have hsP : R.sP = s' := hiter
  rw [hiter]
  refine ⟨hsteps, ?_⟩
  have hspB : spOf s' = R.spB := by
    rw [hsp', RL.spB, hdrop0, ← hfs]; exact sp_sub16 _ _
  have htopB : R.topB.toNat = (spv R.s0).toNat - R.topN := by
    simp only [RL.topB, RL.topN]
    have := hst0.1
    rw [BitVec.toNat_sub_of_le] <;>
      simp only [BitVec.le_def, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show 16 + clobberBytes R.af.saves < 2 ^ 64 by omega)]
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
  have hfield : ∀ f, f ≠ .PC → f ≠ .GPR 29#5 → f ≠ .GPR 31#5 → f ≠ .GPR 16#5 → f ≠ .GPR 17#5 →
      (∀ fl, f ≠ .FLAG fl) → Arm.r f s' = Arm.r f R.s0 := ho'
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
  refine ⟨?_, ?_⟩
  · have hitems : R.rf.blocks[0]! = items := by simp [getElem!_def, hit]
    simp only [MConf.init, hitems]
    refine .inl ⟨1 + (prologueLines R.af.saves R.af.frameSize R.af.isCaller).length, vb, items, [], code, X,
      ps1, psm, ps2, x, hvb, hit, rfl, itemsChecked_block hR hvb hit, hcode, hX, hT, htr, ?_, hpc',
      ?_, hx, hsc⟩
    · rw [← List.drop_drop (i := (prologueLines R.af.saves R.af.frameSize R.af.isCaller).length) (j := 1),
        hdrop, List.drop_left' (by simp)]
    · refine ⟨fun l _ _ => rfl, ⟨fun f hf => ?_, hmemF, ?_⟩, by rw [herr', hent.err],
        by rw [hprog', hent.program], hspB, ?_, fun _ => ?_, code_keep hR.prog0 hent.code hcode',
        hgk, fun _ => hfp'⟩
      · by_cases hfl : ∃ fl, f = .FLAG fl
        · obtain ⟨fl, rfl⟩ := hfl
          rw [hfl' fl, hbe.other _ hf (by simp) (by simp)]
          simp [probeR, probeFlag, hframe]
        have hfl : ∀ fl, f ≠ .FLAG fl := fun fl e => hfl ⟨fl, e⟩
        by_cases h29 : f = .GPR 29#5
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
        have h17 : f ≠ .GPR 17#5 := by rintro rfl; exact hf (by simp [Masked])
        have hpc : f ≠ .PC := by rintro rfl; exact hf trivial
        rw [hfield f hpc h29 h31 h16 h17 hfl, hbe.other f hf h29 h31, probeR_of_ne hfl]
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
        (hne 16 (by omega) (by omega)) (hne 17 (by omega) (by omega)) (by simp)]
    | v n =>
      simp only [regVal]
      rw [hfield _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)]
    | _ => simp [Reg.isArgReg] at hr

/-! ## The prologue's events -/

/-- **The stack probes write outside the world** (#581): every byte the prologue's inline stack
probes zero (`probeHit`, the `stur wzr` stores 4096 bytes and more below fp/lr) is in `R.F`.
Cranelift's probes store into the new frame, possibly into CLIF stack slots, which the world
model treats as shared; this hypothesis excludes that case. It holds for every function whose
probed stack is below 4 KiB (`ProbeF.of_count`, `ProbeF.of_small`: no probes). -/
def ProbeF (R : RL) : Prop := ∀ a, probeHit R.af (spv R.s0) a = true → R.F a

/-- Without probes, `ProbeF` holds. -/
theorem ProbeF.of_count {R : RL} (h : probeCount (probeTotal R.af.frameSize R.af.isCaller) = 0) :
    ProbeF R := fun a ha => by simp [probeHit, probeHitN, probeHitB, h] at ha

/-- A frame below 4 KiB (with its callees' 16-byte setup area) gets no probes: `ProbeF` holds. -/
theorem ProbeF.of_small {R : RL} (h : R.af.frameSize + 16 < 4096) : ProbeF R := by
  have ht : probeTotal R.af.frameSize R.af.isCaller < 4096 := by unfold probeTotal; split <;> omega
  exact ProbeF.of_count (by simp [probeCount, Nat.div_eq_of_lt ht])

/-- **The prologue's states** (#581): the prologue's run from the ABI entry (`ProRun`) is its
`prologueSteps` machine steps, and every state before its last step is at an (unhooked)
instruction line `1 + k` of the prologue, with the program and no error. These are the facts the
straight-line `LinesAt` gave, which Cranelift's stack-probe loop (its `b.gt` jumps back) does not
make. -/
theorem prologue_states {R : RL} (hR : R.Wf) {ra : BitVec 64} (hent : AbiCall R.fb R.base ra R.s0)
    {s' : ArmState} (hpr : ProRun (R.envOf 1) R.af.saves R.af.frameSize R.af.isCaller R.s0 s') :
    iterN R.step (prologueSteps R.af.saves R.af.frameSize R.af.isCaller) R.s0 = s' ∧
    ∀ i < prologueSteps R.af.saves R.af.frameSize R.af.isCaller, ∃ k x,
      k < (prologueLines R.af.saves R.af.frameSize R.af.isCaller).length ∧
      R.fa.lines.toList[1 + k]? = some (.ins x none) ∧
      Line.ins x none ∈ prologueLines R.af.saves R.af.frameSize R.af.isCaller ∧ x.hooked = false ∧
      (iterN R.step i R.s0).program = R.fb.program R.base ∧
      Arm.r .PC (iterN R.step i R.s0) = R.pcOf (1 + k) ∧ Arm.r .ERR (iterN R.step i R.s0) = .None := by
  obtain ⟨vb, items, code, ps1, pl, Xe, psm, ps2, xe, -, -, -, -, -, -, hpl0, hj0, hdrop, -, -⟩ :=
    entry_block hR
  subst hpl0
  have hpc1 : Arm.r .PC R.s0 = R.pcOf 1 := by
    rw [hent.pc]
    simp only [RL.pcOf, RL.L] at hj0 ⊢
    rw [lineOffset_succ _ _ _ hj0]
    simp [lineOffset, Line.size]
  obtain ⟨hiter, -, -, hgx, hline⟩ := iterN_proRun hR hdrop hent.program hpc1 hent.err hpr
  have hgx' := hgx (.inl (by rw [hent.pc]; exact RL.not_postCall_base hR hent.fits))
  refine ⟨hiter, fun i hi => ?_⟩
  obtain ⟨k, hk, hpck, -⟩ := hline i hi
  have hgi := hgx' i hi
  obtain ⟨x, hx, hxh, -⟩ :=
    prologueLines_ins (calls := R.af.isCaller) R.af.saves R.af.frameSize _ (List.getElem_mem hk)
  have hj : R.fa.lines.toList[1 + k]? = some (.ins x none) := by
    have := congrArg (·[k]?) hdrop
    simp only [List.getElem?_drop, RL.L] at this
    rw [this, List.getElem?_append_left hk, List.getElem?_eq_getElem hk, hx]
  exact ⟨k, x, hk, hj, hx ▸ List.getElem_mem hk, hxh, hgi.prog, hpck, hgi.err⟩

/-- **The prologue keeps the program** (#581: `CallSeg.linesAt_program` for the prologue's run,
`ProRun`). -/
theorem prologue_program {R : RL} (hR : R.Wf) {ra : BitVec 64} (hent : AbiCall R.fb R.base ra R.s0)
    {s' : ArmState} (hpr : ProRun (R.envOf 1) R.af.saves R.af.frameSize R.af.isCaller R.s0 s') :
    ∀ i ≤ prologueSteps R.af.saves R.af.frameSize R.af.isCaller,
      (iterN R.step i R.s0).program = R.fb.program R.base := by
  intro i hi
  obtain ⟨hit, hst⟩ := prologue_states hR hent hpr
  rcases Nat.lt_or_ge i (prologueSteps R.af.saves R.af.frameSize R.af.isCaller) with h | h
  · obtain ⟨-, -, -, -, -, -, hp, -⟩ := hst i h
    exact hp
  · obtain rfl : i = prologueSteps R.af.saves R.af.frameSize R.af.isCaller := by omega
    rw [hit, hpr.err.2, hent.program]

/-- **The prologue's steps**: each accesses only fp/lr, the clobber area and the bytes of the
stack probes (in `R.F`) with plain writes, and none is a store exclusive. (#581: `hpf`, the probed
bytes in `R.F`, is new: without it the statement is false, as Cranelift's stack probes may store
into CLIF stack slots, which are not in `R.F`. The prologue's run is `ProRun` and its steps
`prologueSteps`, not a straight-line run (`LinesAt`) of `prologueLines`' length steps, which
Cranelift's stack-probe loop does not make.) -/
theorem prologue_evs {R : RL} (hR : R.Wf) {ra : BitVec 64} (hent : AbiCall R.fb R.base ra R.s0)
    (hpf : ProbeF R) {s' : ArmState}
    (hpr : ProRun (R.envOf 1) R.af.saves R.af.frameSize R.af.isCaller R.s0 s') :
    ∀ i < prologueSteps R.af.saves R.af.frameSize R.af.isCaller,
      (∀ e ∈ stepEvs (iterN R.step i R.s0), R.F e.addr ∧ e.k = .plainW) ∧
        NoStx (iterN R.step i R.s0) := by
  obtain ⟨hframe, -, -, hsv, -, -, -, -, -⟩ := RL.frame_facts hR
  obtain ⟨vb, items, code, ps1, pl, Xe, psm, ps2, xe, -, -, -, -, -, -, hpl0, hj0, hdrop, -, -⟩ :=
    entry_block hR
  subst hpl0
  have hpc1 : Arm.r .PC R.s0 = R.pcOf 1 := by
    rw [hent.pc]
    simp only [RL.pcOf, RL.L] at hj0 ⊢
    rw [lineOffset_succ _ _ _ hj0]
    simp [lineOffset, Line.size]
  have hwr := iterN_proRunWP hR hsv hdrop hent.program hpc1 hent.err hent.spAligned hpr (P := R.F)
    (fun k hk => by
      have := RL.FK_F (fplr_inF hR hframe k (by simpa [RL.topN] using hk))
      simpa [RL.topB, RL.topN, spOf, spv] using this)
    (fun a hp => hpf a (by simpa [probeHit, hframe, spOf, spv] using hp))
  have hplain : ∀ k ∈ kinds (prologueLines R.af.saves R.af.frameSize R.af.isCaller),
      k = .plainR ∨ k = .plainW := by
    intro k hk
    rw [kinds_prologueLines] at hk
    simp only [List.mem_cons, List.mem_replicate] at hk
    rcases hk with rfl | ⟨-, rfl⟩ <;> exact .inr rfl
  intro i hi
  obtain ⟨k, x, -, hj, hmem, hxh, hprog, hpck, herr⟩ := (prologue_states hR hent hpr).2 i hi
  obtain ⟨a, ha, -, hev, hdec⟩ := stepEvs_line (X := R.X) (H := R.H) hR.layout hR.lm hR.fit hj hxh
    hprog (by rw [hpck]; rfl) herr
  refine ⟨fun e he => ?_, fun rel rs rn hc => ?_⟩
  · rw [hev] at he
    have hkx : insnKind x = some e.k := by
      have hmk := (instEvs_kinds ha _).subset (List.mem_map_of_mem (f := (·.k)) he)
      cases h : insnKind x with
      | none => rw [h] at hmk; cases hmk
      | some k' => rw [h] at hmk; simp only [Option.toList_some, List.mem_singleton] at hmk; rw [hmk]
    have hkind : e.k = .plainW := by
      have hin : e.k ∈ kinds (prologueLines R.af.saves R.af.frameSize R.af.isCaller) :=
        List.mem_filterMap.2 ⟨_, hmem, by simp [lineKind, hkx]⟩
      rw [kinds_prologueLines] at hin
      simp only [List.mem_cons, List.mem_replicate] at hin
      rcases hin with h | ⟨-, h⟩ <;> exact h
    have hw := evs_memWrites ha (by rw [hkx, hkind]) _ e he
    have := hwr i hi (1 + k) x none hj hpck hxh _ a ha _ hw 0 (Backend.Proof.memWrites_pos a _ _ hw)
    exact ⟨by simpa using this, hkind⟩
  · rw [cls_of_decode hdec] at hc
    exact clsOf_ne_stx (noExcl_of_kinds hplain hmem ha) rel rs rn hc

/-- **A precise run through (a prefix of) the prologue** under `OkPriv` is the single-core run;
its events are private plain writes. (#581: `hpf` (`ProbeF`) is new: the stack probes' writes are
private only when the probed bytes are in `R.F`; the prologue's run is `ProRun`, its steps
`prologueSteps`, as in `prologue_evs`.) -/
theorem prun_prologue {R : RL} (hR : R.Wf) {ra : BitVec 64} (hent : AbiCall R.fb R.base ra R.s0)
    (hpf : ProbeF R)
    {s' : ArmState} (hlat : ProRun (R.envOf 1) R.af.saves R.af.frameSize R.af.isCaller R.s0 s')
    {mon : Mon} {L : List Lab} {t1 : ArmState × Mon}
    (hr : PRun Policy.arm R.step (OkPriv R) (R.s0, mon) L t1)
    (hL : L.length ≤ prologueSteps R.af.saves R.af.frameSize R.af.isCaller) :
    t1.1 = iterN R.step L.length R.s0 ∧ PrivW (PrivA R) (evTr L) ∧
      ∀ p y, evAt (evTr L) p = some y → y.k = .plainW := by
  have hpe := prologue_evs hR hent hpf hlat
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
  exact ⟨h1, fun p y hy _ => ⟨privA_addr.2 (hk p y hy).1, by rw [(hk p y hy).2]; decide⟩,
    fun p y hy => (hk p y hy).2⟩

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
      exact (h p z hT (by simpa [ProgE2E.convEv] using hW)).1
  len j hj := absurd hj (Nat.not_lt_zero _)
  pair j hj := absurd hj (Nat.not_lt_zero _)
  pair_inv p _ hp := by rw [evAt_nil] at hp; cases hp

/-! ## From the ABI entry -/

/-- **The prologue's run from the ABI entry** (`q_init_lines` without the body world). (#581:
the former statement, a straight-line run (`LinesAt`) of `prologueLines`' length steps, became
false with Cranelift's stack-probe loop; the run is `ProRun`, its steps `prologueSteps`.) -/
theorem prologue_linesAt {R : RL} (hR : R.Wf) {ra : BitVec 64} (hent : AbiCall R.fb R.base ra R.s0) :
    ProRun (R.envOf 1) R.af.saves R.af.frameSize R.af.isCaller R.s0
      (iterN R.step (prologueSteps R.af.saves R.af.frameSize R.af.isCaller) R.s0) := by
  obtain ⟨-, hfs, -, hsv, -, hcb, -, -, -⟩ := RL.frame_facts hR
  have hst0 := hR.stack.frame
  have hs : R.af.frameSize < 2 ^ 64 := by have := hst0.1; omega
  obtain ⟨vb, items, code, ps1, pl, X, psm, ps2, x, hvb, hit, hcode, hX, hT, htr, hpl0, hj0,
    hdrop, hx, hsc⟩ := entry_block hR
  subst hpl0
  obtain ⟨s', hsteps, -⟩ :=
    prologue_ok (calls := R.af.isCaller) (R.envOf 1) hs hsv (by rw [hfs]; exact hcb) R.s0 hent.spAligned
  have hpc1 : Arm.r .PC R.s0 = R.pcOf 1 := by
    rw [hent.pc]
    simp only [RL.pcOf, RL.L] at hj0 ⊢
    rw [lineOffset_succ _ _ _ hj0]
    simp [lineOffset, Line.size]
  obtain ⟨hiter, -⟩ := iterN_proRun hR hdrop hent.program hpc1 hent.err hsteps
  rw [hiter]
  exact hsteps

/-- **Layer 4b from the ABI entry, from any configuration `Q`-related to the state after the
prologue** (`arm_alloc_refines_entry` with `Q ∧ AInv` given). (#581: `hpf` (`ProbeF`) is new:
the prologue's stack probes refine no CLIF step only when the probed bytes are private; the
state after the prologue is after `prologueSteps` steps, which Cranelift's stack-probe loop
makes more than `prologueLines`' length.) -/
theorem arm_alloc_refines_entryQ {R : RL} (hR : R.Wf) (hsc : MemScopeLS R) {ra : BitVec 64}
    (hent : AbiCall R.fb R.base ra R.s0) (hpf : ProbeF R) {c : MConf CV ArmState}
    (hq : Q R (iterN R.step (prologueSteps R.af.saves R.af.frameSize R.af.isCaller) R.s0) c)
    (hA : AInv R c) {mon : Mon} {ls : List Lab}
    {t' : ArmState × Mon} (hr : PRun Policy.arm R.step (OkPriv R) (R.s0, mon) ls t') :
    ∃ n trS cE ψ, n ≤ ls.length ∧ MTRun R.vc R.rf R.sem ckeep (cEvs R.F R.ctx) c trS cE ∧
      Refines (· = ·) (PrivA R) (MonPair (evTr (ls.take n))) (PrepThread.conv trS)
        (PrepThread.conv (evTr (ls.take n))) ψ ∧ (n = ls.length ∨ Done R cE) := by
  have hlat := prologue_linesAt hR hent
  have hpp : ∀ {mon : Mon} {L : List Lab} {t1 : ArmState × Mon},
      PRun Policy.arm R.step (OkPriv R) (R.s0, mon) L t1 →
      L.length ≤ prologueSteps R.af.saves R.af.frameSize R.af.isCaller →
      t1.1 = iterN R.step L.length R.s0 ∧ PrivW (PrivA R) (evTr L) ∧
        ∀ p y, evAt (evTr L) p = some y → y.k = .plainW := fun h hL => prun_prologue hR hent hpf hlat h hL
  generalize hP : prologueSteps R.af.saves R.af.frameSize R.af.isCaller = P at hq hpp
  by_cases hle : ls.length ≤ P
  · -- the run ends inside the prologue: private writes only
    obtain ⟨-, hpw, -⟩ := hpp hr hle
    refine ⟨ls.length, [], _, id, Nat.le_refl _, .nil, ?_, .inl rfl⟩
    rw [List.take_length]
    exact refines_privW hpw
  · obtain ⟨v, hv, hrest⟩ := CallCompose.take_prun hr P
    have hPl : (ls.take P).length = P := by simp; omega
    obtain ⟨hv1, hpw, hpk⟩ := hpp hv (by omega)
    rw [hPl] at hv1
    obtain ⟨v1, vm⟩ := v
    simp only at hv1
    subst hv1
    obtain ⟨n2, trS, cE, ψ2, hn2, hM, href, hend⟩ := arm_alloc_refines_ls hR hsc hq hA hrest
    refine ⟨P + n2, trS, cE, CallCompose.appMap 0 (evTr (ls.take P)).length id ψ2,
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

/-- **Layer 4b from the ABI entry** (module doc): every precise run under `OkPriv` from the ABI
entry realizes, on a prefix, a run of the allocated code from its entry configuration
(`MConf.init` with the body-entry world `w₀`), with `Refines` (equal kinds, the addresses outside
the world private, the atomic updates monitor pairs), up to the allocated code's return, trap or
undefined behaviour (`Done`), for functions in `MemScopeLS` (event-free forms, `fence`, `ldar`,
`stlr`, LL/SC loops, block-ending branches, plain loads/stores). (#581: `hpf` (`ProbeF`) is new:
the prologue's stack probes refine no CLIF step only when the probed bytes are private.) -/
theorem arm_alloc_refines_entry {R : RL} (hR : R.Wf) (hsc : MemScopeLS R) {ra : BitVec 64}
    (hent : AbiCall R.fb R.base ra R.s0) (hpf : ProbeF R) {w₀ : ArmState}
    (hbe : BodyEntryW R.F R.vc.EntryArg R.af R.s0 w₀) {mon : Mon} {ls : List Lab}
    {t' : ArmState × Mon} (hr : PRun Policy.arm R.step (OkPriv R) (R.s0, mon) ls t') :
    ∃ m₀ n trS cE ψ, n ≤ ls.length ∧
      MTRun R.vc R.rf R.sem ckeep (cEvs R.F R.ctx) (MConf.init R.rf m₀ w₀) trS cE ∧
      Refines (· = ·) (PrivA R) (MonPair (evTr (ls.take n))) (PrepThread.conv trS)
        (PrepThread.conv (evTr (ls.take n))) ψ ∧ (n = ls.length ∨ Done R cE) := by
  obtain ⟨-, hq, hA⟩ := q_init_lines hR hent hbe
  exact ⟨_, arm_alloc_refines_entryQ hR hsc hent hpf hq hA hr⟩

end Concurrency.ArmAllocThread
