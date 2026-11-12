import FV.Concurrency.CallResumeLayers
import FV.Concurrency.CallRetsEnd

/-!
# The caller's resume premises from the callee's preservation facts (#473, step (1))

`CallResumeL.resume_layers` asks the state `y` after the callee's return to hold every live
location of the caller outside the call's clobbers. The call's result registers (`info.defs`)
are not clobbers, so for a call with results that premise would ask the callee to leave its
result registers unchanged. Here:

* `mstep_callR`, **`resume_layersR`**: `mstep_call`/`resume_layers` with the preservation premise
  only for locations that no late def of the call writes (the results are written by the call's
  step);
* **`hpresR_of_callee`**: that premise from what a returning callee gives (`RetEnd`): the
  callee-saved registers up to `ckeep`, `sp`, and the memory of the caller's frame and kept
  addresses `RA.FK`; every def register of the call is the location of a late def operand
  (`checkStatic`'s fixed-register check);
* `hkeep_of_callee`: the clobbered callee-saved registers (the high halves of v8–v15) up to `ckeep`.
-/

namespace Concurrency.CallRetResume

open Arm ArmThread Backend Backend.Proof Backend.Proof.Driver VCodeThread PrepThread AllocThread
  ArmAllocThread E2E IselResume CallResumeL CallRetsEnd

/-- The (operand, location) pairs of a call item's defs. -/
def defPairs (ops : Array Operand) (allocs : Array Loc) : List (Operand × Loc) :=
  (ops.zip allocs).toList.filter (·.1.isDef)

/-- **The allocated code's `call` step after the callee's return, results written by the step**
(`mstep_call` with the preservation premise only off the late def locations). -/
theorem mstep_callR {R : RL} {s y : ArmState} {b k : Nat} {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : ArmState}
    (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩)) {vb : VBlock} {info : CallInfo}
    (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some (.call info))
    (hk : k + 1 < vb.insts.size) {ops : Array Operand} (hops : (MInst.call info).operands = .ok ops)
    (hsz : allocs.size = ops.size)
    (hpres : ∀ l, ValidLoc l → Live R.rf l → (∀ c ∈ (MInst.call info).clobbers, l ≠ .reg c) →
      (∀ q ∈ defPairs ops allocs, q.1.isLate = true → q.2 ≠ l) →
      locVal R.fr y l = locVal R.fr s l)
    (hkeep : ∀ c ∈ (MInst.call info).clobbers, c ∈ calleeSaved →
      ckeep c (regVal y c) = ckeep c (regVal s c))
    (X : ExtSem) (y' : ArmState) :
    ∃ m', MStep R.vc (csem R.F R.ctx
        (xcallX X ((defPairs ops allocs).map fun p => locVal R.fr y p.2) y'))
        ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) (.run ⟨b, its, m', y'⟩) ∧
      ∀ l, ValidLoc l → Live R.rf l → m' l = locVal R.fr y l := by
  classical
  have hst := q_stRel hq
  let D := defPairs ops allocs
  let outs := D.map fun p => locVal R.fr y p.2
  let early := (D.zip outs).filter (·.1.1.isEarly)
  let late := (D.zip outs).filter (·.1.1.isLate)
  let clob := (MInst.call info).clobbers
  let m1 := writeM m early
  let m2 : Loc → CV := fun l => if ∃ c ∈ clob, l = .reg c then locVal R.fr y l else m1 l
  have hzipE : D.zip outs = D.map fun q => (q, locVal R.fr y q.2) := by
    simp only [outs]
    clear hpres
    induction D with
    | nil => rfl
    | cons q D ih => simp [ih]
  have hzip : ∀ p ∈ D.zip outs, p.2 = locVal R.fr y p.1.2 := by
    intro p hp
    rw [hzipE] at hp
    obtain ⟨q, -, rfl⟩ := List.mem_map.mp hp
    rfl
  have hearly : ∀ p ∈ early, p.2 = locVal R.fr y p.1.2 :=
    fun p hp => hzip p ((List.mem_filter.mp hp).1)
  have hlate : ∀ p ∈ late, p.2 = locVal R.fr y p.1.2 :=
    fun p hp => hzip p ((List.mem_filter.mp hp).1)
  have hm1 := writeM_fun (locVal R.fr y) early m hearly
  have hm' := writeM_fun (locVal R.fr y) late m2 hlate
  have hD : D.length ≤ info.defs.length := by
    have := congrArg List.length (pairs_fst hsz.symm Operand.isDef)
    rw [List.length_map] at this
    simp only [D, defPairs]; rw [this]; exact CallResumeL.call_defs_le hops
  refine ⟨writeM m2 late, ?_, fun l hv hlive => ?_⟩
  · refine MStep.op hvb hi hops hsz ?_ (by simp [outs, D, defPairs]) (HavocOuts.refl _ _ _)
      ⟨?_, ?_⟩ (.next hk)
    · have hO : outs.length ≤ info.defs.length := by simp only [outs, List.length_map]; exact hD
      simp only [csem, xcallX, Option.map_some]
      congr 2
      exact List.take_of_length_le hO
    · intro l hl
      simp only [m2]
      rw [if_neg (fun ⟨c, hc, he⟩ => hl c hc he)]; rfl
    · intro c hc hcs
      simp only [m2]
      rw [if_pos ⟨c, hc, rfl⟩]
      show ckeep c (regVal y c) = ckeep c (writeM m early (.reg c))
      rw [hm1]
      split
      · rfl
      · rw [hst.store (.reg c) (fun r e => by cases e; exact calleeSaved_allocatable c hcs) trivial]
        exact hkeep c hc hcs
  · rw [hm']
    split
    · rfl
    · rename_i hnl
      have hnl' : ∀ q ∈ D, q.1.isLate = true → q.2 ≠ l := by
        intro q hq hlq he
        apply hnl
        refine List.any_eq_true.mpr ⟨(q, locVal R.fr y q.2), ?_, by simp [he]⟩
        refine List.mem_filter.mpr ⟨?_, hlq⟩
        rw [hzipE]
        exact List.mem_map_of_mem hq
      simp only [m2]
      split
      · rfl
      · rename_i hnc
        show writeM m early l = _
        rw [hm1]
        split
        · rfl
        · rw [hst.store l hv hlive]
          exact (hpres l hv hlive (fun c hc he => hnc ⟨c, hc, he⟩) hnl').symm

/-- **Layers 3, 4a and 4b after a call's return, results written by the call**
(`resume_layers` with `mstep_callR`). -/
theorem resume_layersR {R : RL} (hR : R.Wf) {vc : VCode} {L : Nat → Prop}
    {ss ss' : Array (Array Nat)} (H3 : PrepFacts vc R.vc L ss ss')
    {ev : MInst → List CV → ArmState → List Ev} {c : CheckCtx} {ins : Array (Option AState)}
    {a0 : AState} {r₀ : Reg → CV} (hc : CheckedAt R.vc R.rf c ins a0)
    {x y : ArmState} {b k : Nat} {allocs : Array Loc} {its : List RItem} {m : Loc → CV}
    {w : ArmState} {ρ : Nat → CV} {src : VConf CV ArmState}
    (hP : PMatch vc R.vc R.sem ev L ss' src (.run ⟨b, k, ρ, w⟩))
    (hA : MatchRun c ins ckeep r₀ ⟨b, .op k allocs :: its, m, w⟩ ⟨b, k, ρ, w⟩)
    (hq : Q R x (.run ⟨b, .op k allocs :: its, m, w⟩)) {vb : VBlock} {info : CallInfo}
    (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some (.call info))
    (hk : k + 1 < vb.insts.size) {ops : Array Operand} (hops : (MInst.call info).operands = .ok ops)
    (hsz : allocs.size = ops.size)
    (hpres : ∀ l, ValidLoc l → Live R.rf l → (∀ c ∈ (MInst.call info).clobbers, l ≠ .reg c) →
      (∀ q ∈ defPairs ops allocs, q.1.isLate = true → q.2 ≠ l) →
      locVal R.fr y l = locVal R.fr x l)
    (hkeep : ∀ c ∈ (MInst.call info).clobbers, c ∈ calleeSaved →
      ckeep c (regVal y c) = ckeep c (regVal x c))
    (hpc : Arm.r .PC y = Arm.r .PC x + 4#64) (herr : Arm.r .ERR y = .None)
    (hsp : spOf y = spOf x) (hmem : ∀ a, R.FK a → y.mem a = x.mem a)
    (hprog : y.program = x.program) (hfp : xreg 29 y = xreg 29 x) (X : ExtSem) :
    ∃ b0 m' ρ', src = .run ⟨b0, k, ρ, w⟩ ∧
      VStep vc (csem R.F R.ctx (xcallX X
        ((defPairs ops allocs).map fun p => locVal R.fr y p.2) y))
        (.run ⟨b0, k, ρ, w⟩) (.run ⟨b0, k + 1, ρ', y⟩) ∧
      PMatch vc R.vc R.sem ev L ss' (.run ⟨b0, k + 1, ρ', y⟩) (.run ⟨b, k + 1, ρ', y⟩) ∧
      MatchRun c ins ckeep r₀ ⟨b, its, m', y⟩ ⟨b, k + 1, ρ', y⟩ ∧
      Q R y (.run ⟨b, its, m', y⟩) := by
  obtain ⟨m', hms, hst'⟩ := mstep_callR hq hvb hi hk hops hsz hpres hkeep X y
  obtain ⟨ρ', hv4, hA'⟩ := alloc_call_vstep hc hA hvb hi (fun u w0 r h => by
    simp only [csem, xcallX, Option.map_some, Option.some.injEq] at h
    subst h; rfl) hms
  obtain ⟨b0, rfl, hLb, hσ⟩ := pmatch_call hP hvb hi
  exact ⟨b0, m', ρ', rfl, prep_vstep_next H3 (driverSem_csem _ _ _).toDriverSemG hLb hσ hv4,
    .blk hLb hσ, hA', CallSeg.resumeQW hR hq hvb hi hpc herr hsp hmem hprog hfp hst'
      (SameWorld.refl _ _)⟩

/-! ## The premises from the callee's preservation facts -/

/-- Every allocatable register is an AAPCS64 call clobber or one of x19–x28. -/
theorem allocatable_cases : ∀ r ∈ aarch64Env.allocatable,
    r ∈ defaultAapcsClobbers ∨ r ∈ (List.range 10).map (fun i => Reg.x (19 + i)) := by
  decide

theorem allocatable_cases' {r : Reg} (h : r.allocatable = true) :
    r ∈ defaultAapcsClobbers ∨ ∃ i < 10, r = .x (19 + i) := by
  have hm : r ∈ aarch64Env.allocatable := by
    simpa [Reg.allocatable, List.contains_iff_mem] using h
  rcases allocatable_cases r hm with h | h
  · exact .inl h
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h
    exact .inr ⟨i, List.mem_range.mp hi, rfl⟩

theorem slotBytes_cases (l : Loc) : slotBytes l = 8 ∨ slotBytes l = 16 := by
  unfold slotBytes; split <;> simp

/-- A frame location's value is kept when `sp` and the frame's memory are. -/
theorem frame_congr {R : RL} (hR : R.Wf) {x y : ArmState} {m : Loc → CV} {w : ArmState}
    (hst : StRel R x m w) (hsp : spOf y = spOf x) (hmem : ∀ a, R.FK a → y.mem a = x.mem a)
    {l : Loc} (hl : ∀ r, l ≠ .reg r) (hlive : Live R.rf l) : locVal R.fr y l = locVal R.fr x l := by
  have hsx : spOf x = R.spB := hst.sp
  have key : ∀ off, R.fr.offset l = .ok off → ∀ n, n ≤ slotBytes l →
      Arm.read_mem_bytes n (spOf y + BitVec.ofNat 64 off) y =
        Arm.read_mem_bytes n (spOf x + BitVec.ofNat 64 off) x := by
    intro off hoff n hn
    have hin := (RL.frameOkK hR).inF l off hlive hoff
    rw [hsp]
    refine read_mem_bytes_congr n _ fun k hk => ?_
    rw [hsx]
    exact hmem _ (hin k (by omega))
  have h816 := slotBytes_cases l
  cases l with
  | reg r => exact absurd rfl (hl r)
  | stack k cl =>
    simp only [locVal]
    split
    · rename_i off hoff
      split
      · rename_i h8; rw [key off hoff 8 (by omega)]
      · rename_i h8; rw [key off hoff 16 (by omega)]
    · rfl
  | save r =>
    simp only [locVal]
    split
    · rename_i off hoff
      split
      · rename_i h8; rw [key off hoff 8 (by omega)]
      · rename_i h8; rw [key off hoff 16 (by omega)]
    · rfl

/-- **The caller's preservation premise of `resume_layersR` from the callee's facts** (module
doc): `y` holds the callee-saved registers of `x` up to `ckeep`, `x`'s `sp`, and `x`'s memory at
the caller's frame and kept addresses; every def register of the call is the location of a late
def operand. -/
theorem hpresR_of_callee {R : RL} (hR : R.Wf) {x y : ArmState} {m : Loc → CV} {w : ArmState}
    (hst : StRel R x m w) {info : CallInfo} {ops : Array Operand} {allocs : Array Loc}
    (hdef : ∀ d ∈ info.defs, ∃ q ∈ defPairs ops allocs, q.1.isLate = true ∧ q.2 = .reg d.1)
    (hcs : ∀ r ∈ calleeSaved, ckeep r (regVal y r) = ckeep r (regVal x r))
    (hsp : spOf y = spOf x) (hmem : ∀ a, R.FK a → y.mem a = x.mem a) :
    ∀ l, ValidLoc l → Live R.rf l → (∀ c ∈ (MInst.call info).clobbers, l ≠ .reg c) →
      (∀ q ∈ defPairs ops allocs, q.1.isLate = true → q.2 ≠ l) →
      locVal R.fr y l = locVal R.fr x l := by
  intro l hv hlive hcl hnd
  cases l with
  | reg r =>
    have hal := hv r rfl
    rcases allocatable_cases' hal with hc | ⟨i, hi, rfl⟩
    · -- a clobber register that the call does not clobber is one of its results
      exfalso
      by_cases hd : info.defs.any (·.1 == r) = true
      · obtain ⟨d, hd, hdr⟩ := List.any_eq_true.mp hd
        have hdr : d.1 = r := by simpa using hdr
        obtain ⟨q, hq, hlq, hq2⟩ := hdef d hd
        exact hnd q hq hlq (by rw [hq2, hdr])
      · exact hcl r (List.mem_filter.mpr ⟨hc, by rw [Bool.not_eq_true']; exact Bool.eq_false_iff.mpr hd⟩) rfl
    · have hmem' : Reg.x (19 + i) ∈ calleeSaved := by
        simp only [calleeSaved, List.mem_append, List.mem_map, List.mem_range]
        exact .inl ⟨i, hi, rfl⟩
      simpa [ckeep, locVal] using hcs _ hmem'
  | stack k cl => exact frame_congr hR hst hsp hmem (fun _ e => nomatch e) hlive
  | save r => exact frame_congr hR hst hsp hmem (fun _ e => nomatch e) hlive

/-- **The clobbered callee-saved registers up to `ckeep`** (the second premise of
`resume_layersR`) from the callee's facts. -/
theorem hkeep_of_callee {x y : ArmState} {info : CallInfo}
    (hcs : ∀ r ∈ calleeSaved, ckeep r (regVal y r) = ckeep r (regVal x r)) :
    ∀ c ∈ (MInst.call info).clobbers, c ∈ calleeSaved →
      ckeep c (regVal y c) = ckeep c (regVal x c) :=
  fun c _ h => hcs c h


/-- **The caller's resume premises from a callee's `RetEnd`** (step (1)): the callee `RB`
returning (`RetEnd`, its own machine `RB.step` for `n` steps from its pause `xr`) to the caller
paused at its `call` in `x`, where the callee's entry values `r₀` of the callee-saved registers
are `x`'s (up to `ckeep`), the callee entered with `x`'s `sp` and the return address after the
`bl`, and the callee's run up to its pause kept the caller's `RA.FK` memory: the state `y` after
its `ret` satisfies the premises of `resume_layersR` other than the program (which the linked
machine restores) and the error flag. -/
theorem resume_premises_of_retEnd {RA RB : RL} (hRA : RA.Wf) {env : Clif.Env}
    {p : Clif.Program} {MR : MemRelT} {slots : List (Clif.SlotId × Nat)} {r₀ : Reg → CV}
    {xr : ArmState} {s' : Clif.State} {ra : BitVec 64}
    (hret : RetEnd RB ra env p MR slots r₀ xr s')
    {x : ArmState} {m : Loc → CV} {w : ArmState} (hst : StRel RA x m w)
    (hr₀ : ∀ r ∈ calleeSaved, ckeep r (r₀ r) = ckeep r (regVal x r))
    (hra : ra = Arm.r .PC x + 4#64) (hsp0 : spv RB.s0 = spOf x) (hfp0 : xreg 29 RB.s0 = xreg 29 x)
    (hmr : ∀ a, RA.FK a → xr.mem a = x.mem a)
    {info : CallInfo} {ops : Array Operand} {allocs : Array Loc}
    (hdef : ∀ d ∈ info.defs, ∃ q ∈ defPairs ops allocs, q.1.isLate = true ∧ q.2 = .reg d.1) :
    ∃ n, Arm.r .PC (iterN RB.step n xr) = Arm.r .PC x + 4#64 ∧
      Arm.r .ERR (iterN RB.step n xr) = .None ∧
      spOf (iterN RB.step n xr) = spOf x ∧
      (∀ a, RA.FK a → (iterN RB.step n xr).mem a = x.mem a) ∧
      (∀ l, ValidLoc l → Live RA.rf l → (∀ c ∈ (MInst.call info).clobbers, l ≠ .reg c) →
        (∀ q ∈ defPairs ops allocs, q.1.isLate = true → q.2 ≠ l) →
        locVal RA.fr (iterN RB.step n xr) l = locVal RA.fr x l) ∧
      (∀ c ∈ (MInst.call info).clobbers, c ∈ calleeSaved →
        ckeep c (regVal (iterN RB.step n xr) c) = ckeep c (regVal x c)) ∧
      xreg 29 (iterN RB.step n xr) = xreg 29 x := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, n, -, -, -, -, -, -, -, -, -, hpc, herr, hsp, hmem,
    ⟨-, hx29⟩, hcs, -⟩ := hret
  have hcs' : ∀ r ∈ calleeSaved, ckeep r (regVal (iterN RB.step n xr) r) = ckeep r (regVal x r) :=
    fun r hr => (hcs r hr).trans (hr₀ r hr)
  have hsp' : spOf (iterN RB.step n xr) = spOf x := hsp.trans hsp0
  have hmem' : ∀ a, RA.FK a → (iterN RB.step n xr).mem a = x.mem a := fun a ha => by
    rw [hmem]; exact hmr a ha
  exact ⟨n, hpc.trans hra, herr, hsp', hmem', hpresR_of_callee hRA hst hdef hcs' hsp' hmem',
    hkeep_of_callee hcs', hx29.trans hfp0⟩

end Concurrency.CallRetResume
