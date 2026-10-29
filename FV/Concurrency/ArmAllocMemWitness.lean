import FV.Concurrency.ArmAllocFwd
import FV.Concurrency.ArmAllocWitness

/-!
# Non-vacuity of layer 4b for the memory scope (T2h, #311)

* `mem_premises`: the compiled `args; fence; rets` (`RF`: a hand-written VCode `vcF` and
  allocation `rfF` without moves, lowered, emitted and laid out by the compiler, loaded as
  `ArmAllocWitness.act` loads it; the `dmb ish` is its line 3, after the prologue's `stp`/`mov`)
  meets the premises of `arm_alloc_refines_mem`: `R.Wf`, `MemScope` (and not `NoEvScope`: the
  `fence` is a memory form), no moves, and `Q ∧ AInv` at `MConf.init` after the prologue
  (`Backend.Proof.q_init`). (`spillAlloc`'s allocations of compiled CLIF functions have moves:
  the saves of x19–x28 at the entry.)
* `dmb_run`: from there, the Arm's precise one-step run through the `dmb ish` has the barrier
  event (`exists_prun_line`, `line_of_q`); `dmb_refines`: `arm_alloc_refines_mem` on it;
* `ldar_w`, `stlr_w`: `ldar_form`/`stlr_form` at a covered `loadAcquire`/`storeRelease`
  (`OneEvForm`);
* `ctlIndep_ldar`: `ctlIndep_excl` at the encoded `ldar x1, [x0]`.
-/

namespace Concurrency.ArmAllocThread.MemWitness

open Arm ArmFoot ArmThread Backend Backend.Proof VCodeThread Witness

/-- `args; fence; rets`. -/
def vcF : VCode :=
  { name := "f", blocks := #[{ label := 0, insts := #[.args [], .fence, .rets []] }], classes := #[],
    slotBytes := 0, outgoing := 0, rulesFired := #[] }

def rfF : RFunc := { blocks := #[#[.op 0 #[], .op 1 #[], .op 2 #[]]], spillSlots := 0, saved := [] }

abbrev RF : RL := act vcF rfF

theorem oneF : oneLabel RF.fa.lines.toList = true := by decide +kernel

theorem wfF : RF.Wf := by
  have hfb := fb_eq oneF
  refine wf_of (VCodeThread.Witness.ok_of_isOkB () (by decide +kernel)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ ?_ ?_ (by decide +kernel) ?_ (by decide +kernel)
  · rw [layout_eq (labelOffsets_one oneF)]; decide +kernel
  · rw [labelOffsets_one oneF]; rfl
  · rw [hfb]; decide +kernel
  · rw [hfb]; decide +kernel

theorem szF : 4 * RF.fb.words.size ≤ 0x10000 := by rw [fb_eq oneF]; decide +kernel

theorem codeF : ∀ k < RF.fb.words.size,
    Arm.read_mem_bytes 4 (0x10000#64 + BitVec.ofNat 64 (4 * k)) RF.s0 = RF.fb.words[k]! := by
  have hfb := fb_eq oneF
  have hs0 : RF.s0 = entry (fbK vcF rfF) 0x10000#64 := by
    show entry RF.fb _ = _; rw [hfb]
  rw [hs0, hfb]
  decide +kernel

theorem entryArgF : ∀ r, RF.vc.EntryArg r → r.isArgReg = true := by
  intro r ⟨vb, ds, h1, h2, v, hv⟩
  simp only [RF, act, vcF] at h1
  cases h1
  simp at h2
  subst h2
  simp at hv

/-- **`Q ∧ AInv` at the allocated code's entry configuration** after the prologue
(`Backend.Proof.q_init`), with the body-entry world `E2E.bodyOf`. -/
theorem qF : ∃ n, Q RF (iterN RF.step n RF.s0)
      (MConf.init RF.rf (locVal RF.fr (iterN RF.step n RF.s0)) (E2E.bodyOf RF.af RF.s0)) ∧
    AInv RF (MConf.init RF.rf (locVal RF.fr (iterN RF.step n RF.s0)) (E2E.bodyOf RF.af RF.s0)) := by
  obtain ⟨n, -, hq, hA, -⟩ := q_init wfF (abi_of szF codeF)
    ((E2E.Binary.bodyEntry_bodyOf RF.af RF.s0).w RF.F entryArgF)
  exact ⟨n, hq, hA⟩

theorem scopeF : MemScope RF := by
  intro b vb k i hb hi
  rcases b with _ | b
  · simp only [RF, act, vcF] at hb
    cases hb
    rcases k with _ | _ | _ | k
    · simp at hi; subst hi; exact .inl (.inr (.inl ⟨_, rfl⟩))
    · simp at hi; subst hi; exact .inr (.inl rfl)
    · simp at hi; subst hi; exact .inl (.inr (.inr (.inl ⟨_, rfl⟩)))
    · simp at hi
  · simp [RF, act, vcF] at hb

/-- The `fence` is outside `NoEvScope` (it has the barrier kind). -/
theorem not_noEvF : ¬ NoEvScope RF := by
  intro h
  rcases h 0 _ 1 .fence rfl rfl with ⟨-, -, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> cases h

theorem noMovesF : NoMoves RF := by
  intro b items hb src dst hm
  rcases b with _ | b
  · simp only [RF, act, rfF] at hb
    cases hb
    simp at hm
  · simp [RF, act, rfF] at hb

/-- **Non-vacuity of `arm_alloc_refines_mem`**: the compiled `args; fence; rets` (`RF`) satisfies
its premises — `R.Wf`, the memory scope (beyond `NoEvScope`), no moves, and `Q ∧ AInv` at
`MConf.init` after the prologue; the theorem then applies to every precise Arm run from there. -/
theorem mem_premises : RF.Wf ∧ MemScope RF ∧ ¬ NoEvScope RF ∧ NoMoves RF ∧
    ∃ n, Q RF (iterN RF.step n RF.s0)
      (MConf.init RF.rf (locVal RF.fr (iterN RF.step n RF.s0)) (E2E.bodyOf RF.af RF.s0)) ∧
    AInv RF (MConf.init RF.rf (locVal RF.fr (iterN RF.step n RF.s0)) (E2E.bodyOf RF.af RF.s0)) ∧
    ∀ (mon : Mon) (ls : List Lab) (t' : ArmState × Mon),
      PRun Policy.arm RF.step (fun _ _ => True) (iterN RF.step n RF.s0, mon) ls t' →
      ∃ k trS cE ψ, k ≤ ls.length ∧ AllocThread.MTRun RF.vc RF.rf RF.sem ckeep (cEvs RF.F RF.ctx)
        (MConf.init RF.rf (locVal RF.fr (iterN RF.step n RF.s0)) (E2E.bodyOf RF.af RF.s0)) trS cE ∧
        ThreadRefine.Refines (· = ·) (PrivA RF) (MonPair (evTr (ls.take k))) (PrepThread.conv trS)
          (PrepThread.conv (evTr (ls.take k))) ψ ∧ (k = ls.length ∨ Done RF cE) := by
  obtain ⟨n, hq, hA⟩ := qF
  exact ⟨wfF, scopeF, not_noEvF, noMovesF, n, hq, hA, fun _ _ _ hr =>
    arm_alloc_refines_mem wfF scopeF noMovesF hq hA hr⟩

/-! ## A precise run with the barrier event -/

/-- The lines of the body's code: `dmb ish`, then the epilogue. -/
def LF : List Line :=
  [.ins .dmbish none, .ins (.ldp (.x 29) (.x 30) (.spPostIndexed 16)) none, .ins .ret none]

/-- The code `[fence, epilogue]`. -/
def codeOk : Except String (List AInst) → Bool
  | .ok [.inst .fence, .epilogueRet] => true
  | _ => false

theorem codeOk_eq {e : Except String (List AInst)} (h : codeOk e = true) :
    e = .ok [.inst .fence, .epilogueRet] := by
  unfold codeOk at h
  split at h
  · rfl
  · cases h

/-- At the entry configuration, the Arm is at the `dmb ish` line. -/
theorem line_of_q {s : ArmState} {m₀ : Loc → CV} {w₀ : ArmState}
    (hq : Q RF s (MConf.init RF.rf m₀ w₀)) :
    ∃ j, RF.fa.lines.toList[j]? = some (.ins .dmbish none) ∧ Arm.r .PC s = RF.pcOf j ∧
      StRel RF s m₀ w₀ := by
  have hq' : Q RF s (.run ⟨0, (RF.rf.blocks[0]!).toList, m₀, w₀⟩) := hq
  refine q_head wfF hq' rfl (fun _ h => by cases h) ?_
  intro vb code hvb hcode ps ls ps' hl
  simp only [RF, act, vcF] at hvb
  cases hvb
  have hc : codeOk (itemsCode RF.fr vcF.blocks[0] RF.rf.blocks[0]!.toList) = true := by native_decide
  obtain rfl : code = [.inst .fence, .epilogueRet] :=
    Except.ok.inj ((hcode.symm.trans (codeOk_eq hc)))
  exact codeLinesE_head_fence hl

/-- **Non-vacuity of `exists_prun_line`, a precise run with a memory event**: from the
`Q`-related state after the prologue, for every monitor, the Arm's one-step precise run through
the `dmb ish` has the barrier event `dmbEv` (whatever the environment's memory). -/
theorem dmb_run : ∃ n, Q RF (iterN RF.step n RF.s0)
      (MConf.init RF.rf (locVal RF.fr (iterN RF.step n RF.s0)) (E2E.bodyOf RF.af RF.s0)) ∧
    ∀ mon : Mon, ∃ t',
      PRun Policy.arm RF.step (fun _ _ => True) (iterN RF.step n RF.s0, mon)
        [⟨[ArmInstFoot.dmbEv], false⟩] t' := by
  obtain ⟨n, hq, -⟩ := qF
  refine ⟨n, hq, fun mon => ?_⟩
  obtain ⟨j, hj, hpc, hst⟩ := line_of_q hq
  obtain ⟨a, t', ha, hev, hr⟩ := exists_prun_line wfF hj rfl hst.prog hpc hst.err
    (fun a ha rel rs rn h => by rw [(dmbish_inst ha ArmState.default).2] at h; cases h) mon RF.s0.mem
  rw [hev, (dmbish_inst ha _).1] at hr
  exact ⟨t', hr⟩

/-- **`arm_alloc_refines_mem` on a run with a memory event**: the one-step run through the
`dmb ish` is realized by a run of the allocated code with `Refines`. -/
theorem dmb_refines : ∃ n, ∀ mon : Mon, ∃ t' k trS cE ψ,
    PRun Policy.arm RF.step (fun _ _ => True) (iterN RF.step n RF.s0, mon)
      [⟨[ArmInstFoot.dmbEv], false⟩] t' ∧ k ≤ 1 ∧
    AllocThread.MTRun RF.vc RF.rf RF.sem ckeep (cEvs RF.F RF.ctx)
      (MConf.init RF.rf (locVal RF.fr (iterN RF.step n RF.s0)) (E2E.bodyOf RF.af RF.s0)) trS cE ∧
    ThreadRefine.Refines (· = ·) (PrivA RF)
      (MonPair (evTr (([⟨[ArmInstFoot.dmbEv], false⟩] : List Lab).take k))) (PrepThread.conv trS)
      (PrepThread.conv (evTr (([⟨[ArmInstFoot.dmbEv], false⟩] : List Lab).take k))) ψ ∧
    (k = 1 ∨ Done RF cE) := by
  obtain ⟨n, hq, hA⟩ := qF
  obtain ⟨n', hq', hr⟩ := dmb_run
  refine ⟨n', fun mon => ?_⟩
  obtain ⟨t', hr⟩ := hr mon
  have hA' : AInv RF (MConf.init RF.rf (locVal RF.fr (iterN RF.step n' RF.s0))
      (E2E.bodyOf RF.af RF.s0)) := fun hb ⟨a, ha⟩ r hr => by
    simp [RF, act, vcF, VCode.EntryArg] at hr
  obtain ⟨k, trS, cE, ψ, hk, hm, href, hend⟩ := arm_alloc_refines_mem wfF scopeF noMovesF hq' hA' hr
  exact ⟨t', k, trS, cE, ψ, hr, hk, hm, href, hend⟩

/-! ## The one-event forms -/

def flW : Clif.MemFlags := default

/-- **Non-vacuity of `ldar_form`**: a covered `ldar` (`i64`, vregs). -/
theorem ldar_w (F : BitVec 64 → Prop) (ctx : FnCtx) :
    OneEvForm F ctx (.loadAcquire (.int 64) (.vreg 1 .int) (.vreg 0 .int) flW) :=
  ldar_form (by simp [FormOk, AtomTy])

/-- **Non-vacuity of `stlr_form`**: a covered `stlr` (`i32`, vregs). -/
theorem stlr_w (F : BitVec 64 → Prop) (ctx : FnCtx) :
    OneEvForm F ctx (.storeRelease (.int 32) (.vreg 1 .int) (.vreg 0 .int) flW) :=
  stlr_form (by simp [FormOk, AtomTy])

/-- **Non-vacuity of `ctlIndep_excl`**: the encoded canonical `ldar x1, [x0]`. -/
theorem ctlIndep_ldar : ∃ a, (Insn.ldar 64 (.x 1) (.x 0)).toArmInst env0 = .ok a ∧ CtlIndep a :=
  ⟨_, rfl, ctlIndep_excl _⟩

end Concurrency.ArmAllocThread.MemWitness
