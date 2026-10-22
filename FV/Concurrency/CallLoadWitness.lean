import FV.Concurrency.CallLoadData

/-!
# A compiled caller calling the compiled `atomic_load` (T2h, #311, calls)

On the caller `RC` (`CallLoadData`) and the compiled `atomic_load`:

* `wfRC`, `abiRC`: the caller's activation is well formed and entered at its ABI entry;
* `prefixC`: from the ABI entry the single-core path through the prologue, the saves, the entry
  `args` and the spill moves to the `bl ld` line, every step private, no store exclusive, on the
  caller's program (`moves_privA`, `prologue_evs`); `x0` there is the argument `0`;
-/

namespace Concurrency.CallSeg.WitnessC

open Arm ArmFoot ArmThread Prog ClifThread ProgE2E Backend Backend.Proof Backend.Proof.Driver
  VCodeThread PrepThread AllocThread ThreadRefine ArmAllocThread E2E ArmInstFoot Code
  RealizeCompiled RealizeCompiled.Witness RealizeCompiled.WitnessL CallThread
open ArmAllocThread.Witness (act entryAt codeMem)

/-! ## The caller's activation -/

/-- **`R.Wf` of an activation of compiled code laid out by `act`**, with any base, entry state,
hooks and kept addresses (the pipeline's facts as checks). -/
theorem wf_gen {vc : VCode} {rf : RFunc} {base : BitVec 64} {s0 : ArmState} {H : ArmHooks}
    {G : BitVec 64 → Prop} (hc : checkAlloc vc rf = .ok ())
    (ha : (lowerRFunc vc rf).toBool = true) (he : (emitFunc 0 (act vc rf).af).toBool = true)
    (hk : (act vc rf).fa.k = 0) (hl : (act vc rf).fa.layout.toBool = true)
    (hm : (labelOffsets (act vc rf).fa.lines).toBool = true)
    (hfit : 4 * (act vc rf).fb.words.size ≤ 2 ^ 64)
    (hps : (blocksLinesE (act vc rf).ctx (act vc rf).af (act vc rf).af.blocks.toList {}).toBool =
      true)
    (hst : StackAvail 0 (act vc rf).af s0) (hp : s0.program = (act vc rf).fb.program base)
    (hg : ∀ a, G a → ¬ StackBelow (frameDrop (act vc rf).af + 0) (E2E.spv s0) a) :
    ({ act vc rf with base := base, s0 := s0, H := H, G := G } : RL).Wf where
  check := allocChecked_of_checkAlloc hc
  alloc := ArmAllocThread.Witness.ok_getD ha
  emit := by
    rw [show ({ act vc rf with base := base, s0 := s0, H := H, G := G } : RL).fa.k = 0 from hk]
    exact ArmAllocThread.Witness.ok_getD he
  layout := ArmAllocThread.Witness.ok_getD hl
  lm := ArmAllocThread.Witness.ok_getD hm
  fit := hfit
  stack := hst
  psF := ArmAllocThread.Witness.ok_snd hps
  prog0 := hp
  gfree := hg

theorem spv_RC : E2E.spv RC.s0 = 0x7000#64 := spC.1

theorem program_RC : RC.s0.program = RC.fb.program RC.base := by
  show (setMem memC _).program = _
  rw [setMem_program, ArmAllocThread.Witness.entryAt_program]
  rfl

theorem gL_ge {a : BitVec 64} (h : GL a) : 0x20000 ≤ a.toNat ∧ a.toNat < 0x30000 := by
  have hs := spC.2.2.2.1
  unfold GL at h
  have : 4 * (act vcpL rfL).fb.words.size ≤ 0x10000 := by omega
  generalize (act vcpL rfL).fb.words.size = n at this h
  bv_omega

/-- A code address of a program `wordsAt base 0 ws` with at most `0x4000` words. -/
theorem codeAddr_words {s : ArmState} {base a : BitVec 64} {fb : FnBin}
    (hp : s.program = fb.program base) (h : CodeAddr s a) :
    ∃ j < fb.words.size, (a - (base + BitVec.ofNat 64 (4 * j))).toNat < 4 := by
  obtain ⟨p, hp', hd⟩ := h
  rw [hp] at hp'
  obtain ⟨j, hj, he⟩ := ArmAllocThread.Witness.wordsAt_addr hp'
  simp only [Nat.zero_add] at he
  exact ⟨j, by simpa using hj, by rw [← he]; exact hd⟩

theorem stackRC : StackAvail 0 (act vcpC rfC).af RC.s0 := by
  have hs := spC
  refine ⟨?_, fun a ha => ?_⟩
  · rw [spv_RC]; show (act vcpC rfC).af.frameSize + 16 + 0 ≤ _
    have : (act vcpC rfC).af.frameSize = 224 := hs.2.2.2.2.2.2.2.1
    simp only [BitVec.toNat_ofNat]; omega
  · obtain ⟨j, hj, hd⟩ := codeAddr_words program_RC ha
    rw [spv_RC]
    have : (act vcpC rfC).af.frameSize = 224 := hs.2.2.2.2.2.2.2.1
    show (act vcpC rfC).af.frameSize + 16 + 0 ≤ _
    rw [this]
    have hj' : j < 0x4000 := by have := hs.2.2.2.2.1; omega
    rw [show RC.base = 0x30000#64 from rfl] at hd
    generalize j = J at hj' hd
    bv_omega

theorem wfRC : RC.Wf := by
  obtain ⟨-, h1, h2, h3, h4, h5, h6, -, -, h9⟩ := factsC
  refine wf_gen allocC h1 h2 h3 h4 h5 h6 h9 stackRC program_RC fun a hG ⟨h1, _⟩ => ?_
  have := gL_ge hG
  rw [show E2E.spv sC0 = 0x7000#64 from spv_RC] at h1
  simp only [BitVec.toNat_ofNat] at h1
  omega

theorem abiRC : AbiCall RC.fb RC.base 0x4000#64 RC.s0 where
  program := program_RC
  code k w hk := by
    obtain ⟨hlt, rfl⟩ := Array.getElem?_eq_some_iff.mp hk
    rw [show RC.base = 0x30000#64 from rfl, codeRC k hlt]
    simp [hlt]
  pc := by
    show Arm.r .PC (setMem memC _) = _
    rw [show RC.base = 0x30000#64 from rfl]
    simp [ArmFoot.r_setMem, ArmAllocThread.Witness.entryAt, Arm.r_of_w_same]
  err := by
    show Arm.r .ERR (setMem memC _) = _
    simp only [ArmAllocThread.Witness.entryAt, ArmFoot.r_setMem,
      Arm.r_of_w_different (show StateField.ERR ≠ .PC by simp),
      Arm.r_of_w_different (show StateField.ERR ≠ .GPR 31#5 by simp),
      Arm.r_of_w_different (show StateField.ERR ≠ .GPR 30#5 by simp)]
    simp [set_program, ArmState.default, Arm.r, read_base_error]
  lr := by
    show Arm.r (.GPR 30#5) (setMem memC _) = _
    simp [ArmAllocThread.Witness.entryAt, ArmFoot.r_setMem, Arm.r_of_w_different,
      Arm.r_of_w_same]
  spAligned := by rw [spv_RC]; decide
  fits := by
    have := spC.2.2.2.2.1
    rw [show RC.base = 0x30000#64 from rfl]
    simp only [BitVec.toNat_ofNat]; omega

/-- The caller's body-entry world. -/
abbrev w₀C : ArmState := E2E.bodyOf RC.af RC.s0

theorem bodyRC : BodyEntryW RC.F RC.vc.EntryArg RC.af RC.s0 w₀C :=
  (E2E.Binary.bodyEntry_bodyOf RC.af RC.s0).w RC.F entryArgRC

theorem vb0C : RC.vc.blocks[0]? = some vcpC.blocks[0]! := by
  show vcpC.blocks[0]? = _
  rw [Array.getElem?_eq_getElem checksRunC.2.2.2]
  simp [getElem!_def, Array.getElem?_eq_getElem checksRunC.2.2.2]

theorem argsC0 : (vcpC.blocks[0]!).insts[0]? = some (.args [(.vreg 0 .int, .x 0)]) ∧
    (vcpC.blocks[0]!).insts.size = 3 := by
  have h := checksRunC.2.2.1
  unfold argsBC at h
  rw [show vcpC.blocks[0]? = some vcpC.blocks[0]! from vb0C] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, h2⟩
  revert h1
  generalize (vcpC.blocks[0]!).insts[0]? = oi
  intro h1
  split at h1
  · rfl
  · cases h1

/-- The lines of code starting with a direct call start with its `bl`. -/
theorem codeLinesE_head_call {ctx : FnCtx} {af : AFunc} {n : String} {u d : List (Reg × Reg)}
    {rest : List AInst} {ps ps' : Backend.PState} {ls : List Line}
    (h : codeLinesE ctx af (.inst (.call ⟨.sym n, u, d⟩) :: rest) ps = .ok (ls, ps')) :
    ls.head? = some (.ins (.bl n) none) := by
  simp only [codeLinesE, ainstLines, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i r hr
    have e : (MInst.call ⟨.sym n, u, d⟩).lines ctx ps = .ok ([.ins (.bl n) none], ps) := rfl
    rw [e] at hr
    cases hr
    split at h
    · cases h
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      rfl

theorem head_blC : ∀ vb code, RC.vc.blocks[0]? = some vb → itemsCode RC.fr vb restC = .ok code →
    ∀ ps ls ps', codeLinesE RC.ctx RC.af code ps = .ok (ls, ps') →
      ls.head? = some (.ins (.bl "ld") none) := by
  intro vb code hvb hc ps ls ps' hl
  rw [vb0C] at hvb
  obtain rfl := (Option.some.inj hvb).symm
  have h := checksRunC.2.1
  simp only [headBlB, hc] at h
  split at h
  · rename_i u d rest e
    cases e
    exact codeLinesE_head_call hl
  · cases h

/-- The entry `args` as a step of the caller's allocated code. -/
theorem args_stepC (its : List RItem) (m : Loc → CV) (w : ArmState) :
    ∃ m', MStep RC.vc RC.sem ckeep RC.rf (.run ⟨0, .op 0 #[.reg (.x 0)] :: its, m, w⟩)
      (.run ⟨0, its, m', w⟩) ∧ m' (.reg (.x 0)) = regVal w (.x 0) := by
  obtain ⟨hi, hsz⟩ := argsC0
  refine ⟨_, MStep.op vb0C hi (operands_args [(0, .x 0)]) rfl rfl
    (by simp [argOps, Operand.isDef]) (HavocOuts.refl _ _ _)
    ⟨fun _ _ => rfl, fun c hc => by cases hc⟩ (MNext.next (by rw [hsz]; decide)), ?_⟩
  simp [Proof.writeM, argOps, Operand.isDef, Operand.isLate, Operand.isEarly, Backend.Proof.upd]

/-! ## The caller's path to the `bl` -/

/-- **The caller's single-core path from its ABI entry to the `bl ld` line** (module doc). -/
theorem prefixC : ∃ (n0 j : Nat) (m : Loc → CV),
    (∀ i < n0, ((∀ e ∈ stepEvs (iterN RC.step i RC.s0), RC.F e.addr) ∧
      NoStx (iterN RC.step i RC.s0)) ∧ (iterN RC.step i RC.s0).program = RC.fb.program RC.base) ∧
    RC.fa.lines.toList[j]? = some (.ins (.bl "ld") none) ∧
    Arm.r .PC (iterN RC.step n0 RC.s0) = RC.pcOf j ∧ StRel RC (iterN RC.step n0 RC.s0) m w₀C ∧
    regVal (iterN RC.step n0 RC.s0) (.x 0) = 0 := by
  obtain ⟨hlat, hq, hA⟩ := q_init_lines wfRC abiRC bodyRC
  have hpe := prologue_evs wfRC abiRC hlat
  have hpr0 := linesAt_program wfRC hlat
  generalize hn0 : (prologueLines RC.af.frameSize).length = n0 at hpe hpr0 hq hA
  have hq0 := hq
  have hA0 := hA
  have e0 := checksRunC.1
  simp only [MConf.init] at hq0 hA0
  rw [show RC.rf = rfC from rfl, e0] at hq0 hA0
  obtain ⟨n1, hq1, hA1, hp1⟩ := moves_privA wfRC savesL _ _ _ hq0 hA0
  obtain ⟨m', hst, hm'⟩ := args_stepC (spillL.map (fun p => RItem.move p.1 p.2) ++ restC) _ w₀C
  have hq2 := realizes_args wfRC hq1 hA1 vb0C argsC0.1 hst
  have hA2 := Backend.Proof.aInv_step wfRC hq1 hA1 hst
  obtain ⟨n2, hq3, -, hp2⟩ := moves_privA wfRC spillL restC _ m' hq2 hA2
  obtain ⟨j, hj, hpc, hstr⟩ := q_head hq3 rfl head_blC
  rw [← iterN_add, ← iterN_add, ← Nat.add_assoc] at hpc hstr
  rw [← iterN_add] at hp2
  refine ⟨n0 + n1 + n2, j, _, fun i hi => ?_, hj, hpc, hstr, ?_⟩
  · by_cases h0 : i < n0
    · exact ⟨⟨fun e he => (hpe i h0).1 e he |>.1, (hpe i h0).2⟩, hpr0 i (by omega)⟩
    by_cases h1 : i < n0 + n1
    · have := hp1 (i - n0) (by omega)
      rw [← iterN_add, show n0 + (i - n0) = i by omega] at this
      exact this
    · have := hp2 (i - (n0 + n1)) (by omega)
      rw [← iterN_add, show n0 + n1 + (i - (n0 + n1)) = i by omega] at this
      exact this
  · have hx0 : movesM spillL m' (.reg (.x 0)) = regVal w₀C (.x 0) := by
      simp [movesM, spillL, Backend.Proof.upd, hm']
    have hs3 := hstr.store (.reg (.x 0)) (fun r h => by cases h; rfl) trivial
    rw [hx0, E2E.regVal_bodyOf _ _ (by decide), x0C] at hs3
    exact hs3.symm

end Concurrency.CallSeg.WitnessC
