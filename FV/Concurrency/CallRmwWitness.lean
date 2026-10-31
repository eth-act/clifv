import FV.Concurrency.CallRmwData
import FV.Concurrency.CallLoadWitness
import FV.Concurrency.CallLLSCEntry
import FV.Concurrency.CallXClosedWitness

/-!
# A compiled caller calling the compiled `atomic_rmw` (T2h, #311, calls)

On the caller `RC` (`CallRmwData`) and the compiled `atomic_rmw`:

* `wfRC`, `abiRC`: the caller's activation is well formed and entered at its ABI entry;
* `prefixC`: from the ABI entry the single-core path through the prologue, the saves, the entry
  `args` and the spill moves to the `bl rmw` line, every step private, no store exclusive, on the
  caller's program (`moves_privA`, `prologue_evs`); `x0` and `x1` there are the arguments `0`;
* `prun_privF_mon` (`CallSeg`): a precise run along a private single-core path without load
  exclusive keeps the monitor, so the monitor at the caller's `bl` is `none`
  (`noLdxC`: no word of the caller's program is a load exclusive);
* the callee's part: `RLx`, its `Wf`/`AbiCall`/`Compiled` from the callee entered at the `bl`
  (`enterR`), `scopeX` from the LL/SC loops (`scopeLR`), `funRealX` from `funReal_calleeX` with
  the monitor open (`ldxAcq_of_words` on the callee's words);
* the CLIF call step `stepC` (the two arguments) and `cstepC`;
* the linked thread `MC` and **`funReal_call`** (`link_compose`), then **`realizes_call`**.
-/

namespace Concurrency.CallSeg.WitnessCR

open Arm ArmFoot ArmThread Prog ClifThread ProgE2E Backend Backend.Proof Backend.Proof.Driver
  VCodeThread PrepThread AllocThread ThreadRefine ArmAllocThread E2E ArmInstFoot Code
  RealizeCompiled RealizeCompiled.Witness RealizeCompiled.WitnessR RealizeCompiled.WitnessL
  CallThread
open ArmAllocThread.Witness (act entryAt codeMem)

/-! ## The caller's activation -/

theorem spv_RC : E2E.spv RC.s0 = 0x7000#64 := spC.1

theorem program_RC : RC.s0.program = RC.fb.program RC.base := by
  show (setMem memC _).program = _
  rw [setMem_program, ArmAllocThread.Witness.entryAt_program]
  rfl

theorem gR_ge {a : BitVec 64} (h : GL a) : 0x20000 ≤ a.toNat ∧ a.toNat < 0x30000 := by
  have hs := spC.2.2.2.1
  unfold GL at h
  have : 4 * (act vcpR rfR).fb.words.size ≤ 0x10000 := by omega
  generalize (act vcpR rfR).fb.words.size = n at this h
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
  refine ⟨⟨?_, fun a ha => ?_⟩, ?_⟩
  · rw [spv_RC]; show (act vcpC rfC).af.frameSize + 16 + 0 ≤ _
    have : (act vcpC rfC).af.frameSize = 176 := hs.2.2.2.2.2.2.2.1
    simp only [BitVec.toNat_ofNat]; omega
  · obtain ⟨j, hj, hd⟩ := codeAddr_words program_RC ha
    rw [spv_RC]
    have : (act vcpC rfC).af.frameSize = 176 := hs.2.2.2.2.2.2.2.1
    show (act vcpC rfC).af.frameSize + 16 + 0 ≤ _
    rw [this]
    have hj' : j < 0x4000 := by have := hs.2.2.2.2.1; omega
    rw [show RC.base = 0x30000#64 from rfl] at hd
    generalize j = J at hj' hd
    bv_omega
  · have : (act vcpC rfC).af.frameSize = 176 := hs.2.2.2.2.2.2.2.1
    exact ArmAllocThread.Witness.probeBelow_le_small (by omega)

theorem wfRC : RC.Wf := by
  obtain ⟨-, h1, h2, h3, h4, h5, h6, -, -, h9⟩ := factsC
  refine WitnessC.wf_gen allocC h1 h2 h3 h4 h5 h6 h9 stackRC program_RC fun a hG ⟨h1, _⟩ => ?_
  have := gR_ge hG
  rw [show E2E.spv sC0 = 0x7000#64 from spv_RC] at h1
  simp only [BitVec.toNat_ofNat] at h1
  omega

/-- The caller's frame gets no stack probes (#581). -/
theorem probeF_RC : ProbeF RC :=
  ProbeF.of_small (show (act vcpC rfC).af.frameSize + 16 < 4096 by
    have : (act vcpC rfC).af.frameSize = 176 := spC.2.2.2.2.2.2.2.1
    omega)

/-- The callee's (`atomic_rmw`'s) frame gets no stack probes (#581). -/
theorem probeF_R {R : RL} (h : R.af = (act vcpR rfR).af) : ProbeF R :=
  ProbeF.of_small (by
    rw [h]
    have : (act vcpR rfR).af.frameSize = 192 := spC.2.2.2.2.2.2.2.2
    omega)

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

theorem argsC0 : (vcpC.blocks[0]!).insts[0]? =
      some (.args [(.vreg 0 .int, .x 0), (.vreg 1 .int, .x 1)]) ∧
    (vcpC.blocks[0]!).insts.size = 3 := by
  have h := checksRunC.2.2.1
  unfold argsBC at h
  rw [show vcpC.blocks[0]? = some vcpC.blocks[0]! from vb0C] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨h1, h3⟩ := h
  refine ⟨?_, h3⟩
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
      ls.head? = some (.ins (.bl "rmw") none) := by
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
    ∃ m', MStep RC.vc RC.sem ckeep RC.rf (.run ⟨0, .op 0 #[.reg (.x 0), .reg (.x 1)] :: its, m, w⟩)
      (.run ⟨0, its, m', w⟩) ∧ m' (.reg (.x 0)) = regVal w (.x 0) ∧
      m' (.reg (.x 1)) = regVal w (.x 1) := by
  obtain ⟨hi, hsz⟩ := argsC0
  refine ⟨_, MStep.op vb0C hi (operands_args [(0, .x 0), (1, .x 1)]) rfl rfl
    (by simp [argOps, Operand.isDef]) (HavocOuts.refl _ _ _)
    ⟨fun _ _ => rfl, fun c hc => by cases hc⟩ (MNext.next (by rw [hsz]; decide)), ?_, ?_⟩
  all_goals simp [Proof.writeM, argOps, Operand.isDef, Operand.isLate, Operand.isEarly,
    Backend.Proof.upd]

/-! ## The caller's path to the `bl` -/

/-- **The caller's single-core path from its ABI entry to the `bl rmw` line** (module doc). -/
theorem prefixC : ∃ (n0 j : Nat) (m : Loc → CV),
    (∀ i < n0, ((∀ e ∈ stepEvs (iterN RC.step i RC.s0), RC.F e.addr) ∧
      NoStx (iterN RC.step i RC.s0)) ∧ (iterN RC.step i RC.s0).program = RC.fb.program RC.base) ∧
    RC.fa.lines.toList[j]? = some (.ins (.bl "rmw") none) ∧
    Arm.r .PC (iterN RC.step n0 RC.s0) = RC.pcOf j ∧ StRel RC (iterN RC.step n0 RC.s0) m w₀C ∧
    regVal (iterN RC.step n0 RC.s0) (.x 0) = 0 ∧
    regVal (iterN RC.step n0 RC.s0) (.x 1) = 0 := by
  obtain ⟨hlat, hq, hA⟩ := q_init_lines wfRC abiRC bodyRC
  have hpe := prologue_evs wfRC abiRC probeF_RC hlat
  have hpr0 := linesAt_program wfRC hlat
  generalize hn0 : (prologueLines RC.af.saves RC.af.frameSize RC.af.isCaller).length = n0 at hpe hpr0 hq hA
  have hq0 := hq
  have hA0 := hA
  have e0 := checksRunC.1
  simp only [MConf.init] at hq0 hA0
  rw [show RC.rf = rfC from rfl, e0] at hq0 hA0
  obtain ⟨n1, hq1, hA1, hp1⟩ := moves_privA wfRC savesL _ _ _ hq0 hA0 (by simp [savesL, Loc.isSave])
  obtain ⟨m', hst, hm0, hm1⟩ := args_stepC (spillL.map (fun p => RItem.move p.1 p.2) ++ restC)
    _ w₀C
  have hq2 := realizes_args wfRC hq1 hA1 vb0C argsC0.1 hst
  have hA2 := Backend.Proof.aInv_step wfRC hq1 hA1 hst
  obtain ⟨n2, hq3, -, hp2⟩ := moves_privA wfRC spillL restC _ m' hq2 hA2 (by simp [spillL, Loc.isSave])
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
      simp [movesM, spillL, Backend.Proof.upd, hm0]
    have hx1 : movesM spillL m' (.reg (.x 1)) = regVal w₀C (.x 1) := by
      simp [movesM, spillL, Backend.Proof.upd, hm1]
    have hs3 := hstr.store (.reg (.x 0)) (fun r h => by cases h; rfl) trivial
    have hs4 := hstr.store (.reg (.x 1)) (fun r h => by cases h; rfl) trivial
    rw [hx0, E2E.regVal_bodyOf _ _ (by decide), x0C.1] at hs3
    rw [hx1, E2E.regVal_bodyOf _ _ (by decide), x0C.2] at hs4
    exact ⟨hs3.symm, hs4.symm⟩

end Concurrency.CallSeg.WitnessCR

namespace Concurrency.CallSeg

open Arm ArmFoot ArmThread Prog ClifThread ProgE2E Backend Backend.Proof Backend.Proof.Driver
  VCodeThread PrepThread AllocThread ThreadRefine ArmAllocThread E2E ArmInstFoot Code
  RealizeCompiled RealizeCompiled.Witness RealizeCompiled.WitnessR RealizeCompiled.WitnessL
  CallThread
/-! ## The monitor at the `bl` -/

/-- **A precise run along a private single-core path with no load exclusive from an open
monitor stays with the open monitor** (`prun_privF` with the monitor; a `clrex` also gives
`none`). -/
theorem prun_privF_mon {R : RL} {f : ArmState → ArmState} :
    ∀ {L : List Lab} {s : ArmState} {mon : Mon} {t' : ArmState × Mon},
    PRun Policy.arm f (OkPriv R) (s, mon) L t' →
    (∀ i < L.length, (∀ e ∈ stepEvs (iterN R.step i s), R.F e.addr) ∧
      NoStx (iterN R.step i s) ∧ f (iterN R.step i s) = R.step (iterN R.step i s)) →
    (∀ i < L.length, ∀ a rn sz, cls (iterN R.step i s) ≠ .ldx a rn sz) →
    mon = none → t'.2 = none
  | [], _, _, _, .nil, _, _, hmon => hmon
  | l :: L, s, mon, t', .cons (t1 := t1) hs hp ho hr, hf, hldx, hmon0 => by
    obtain ⟨hpv, hns, hstep⟩ := hf 0 (by simp)
    simp only [iterN] at hpv hns hstep
    obtain ⟨s1, mon1⟩ := t1
    have hmon : mon1 = monAfter (cls s) s mon := by
      cases hs with
      | exec _ _ _ _ => rfl
      | xfail hc _ _ _ => rw [hc]; rfl
    have hxf : l.xfail = false := by
      cases hs with
      | exec => rfl
      | xfail hc => exact absurd hc (hns _ _ _)
    have hag : Agrees l.evs s.mem := by
      intro e he hRd
      rcases hp with h' | ⟨M, hM⟩
      · rw [hxf] at h'; cases h'
      · have he' := he
        rw [hM, ArmPrecise.stepEvs_setMem] at he'
        obtain ⟨e0, he0, -, ha, -⟩ := mem_reread he'
        exact ho e he hRd (privA_addr.2 (ha ▸ hpv e0 he0))
    obtain ⟨h1, -, -⟩ := tstep_own hs hp hag hxf
    simp only at h1
    rw [hstep] at h1
    subst h1
    cases hcl : cls s with
    | ldx a rn sz => exact absurd hcl (hldx 0 (by simp) a rn sz)
    | _ =>
      have hm1 : mon1 = none := by
        rw [hmon, hmon0, hcl]
        rfl
      exact prun_privF_mon hr
        (fun i hi => by
          obtain ⟨hpv', hns', hstep'⟩ := hf (i + 1) (by simp; omega)
          simp only [iterN] at hpv' hns' hstep'
          exact ⟨hpv', hns', hstep'⟩)
        (fun i hi a rn sz => by
          have := hldx (i + 1) (by simp; omega)
          simp only [iterN] at this
          exact this a rn sz)
        hm1

end Concurrency.CallSeg

namespace Concurrency.CallSeg.WitnessCR

open ArmAllocThread.Witness (act entryAt codeMem)
open Arm ArmFoot ArmThread Prog ClifThread ProgE2E Backend Backend.Proof Backend.Proof.Driver
  VCodeThread PrepThread AllocThread ThreadRefine ArmAllocThread E2E ArmInstFoot Code
  RealizeCompiled RealizeCompiled.Witness RealizeCompiled.WitnessR RealizeCompiled.WitnessL
  CallThread
/-! ## The word check for the caller -/

/-- A word that does not decode to a load exclusive. -/
def wordNoLdxB (w : BitVec 32) : Bool :=
  match decode_raw_inst w with
  | some (.LDST (.Reg_exclusive i)) => !(decide (i.ord ≠ 1#1) && decide (i.L = 1#1))
  | _ => true

theorem noLdx_wordsC : (RC.fb.program RC.base).all (fun q => wordNoLdxB q.2) = true := by
  native_decide

/-- **No state of the caller's program is at a load exclusive.** -/
theorem noLdxC (s : ArmState) (hs : s.program = RC.fb.program RC.base) (a : Bool)
    (rn : BitVec 5) (sz : BitVec 2) : cls s ≠ .ldx a rn sz := by
  intro hc
  unfold cls at hc
  cases hd : decodeAt s with
  | none => rw [hd] at hc; cases hc
  | some ai =>
    rw [hd] at hc
    have hw : ∃ w, fetch_inst (r .PC s) s = some w ∧ decode_raw_inst w = some ai := by
      unfold decodeAt at hd
      split at hd
      · exact ⟨_, by assumption, hd⟩
      · cases hd
    obtain ⟨w, hf, hdw⟩ := hw
    rw [fetch_inst_from_program, hs] at hf
    obtain ⟨a', hmem⟩ := CallThread.Witness.find?_mem hf
    have hok := List.all_eq_true.mp noLdx_wordsC _ hmem
    simp only [wordNoLdxB, hdw] at hok
    cases ai with
    | LDST i =>
      cases i with
      | Reg_exclusive i =>
        simp only at hc
        split at hc
        · split at hc <;> cases hc
        · rename_i hord
          split at hc
          · rename_i hL
            simp only [Cls.ldx.injEq] at hc
            obtain ⟨rfl, rfl, -⟩ := hc
            simp only [hord, hL, ne_eq, not_false_eq_true, decide_true, Bool.and_self,
              Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at hok
            exact absurd hok (by decide)
          · cases hc
      | _ => cases hc
    | BR i =>
      cases i <;> simp only at hc
      all_goals (try split at hc) <;> (try split at hc) <;> cases hc
    | _ => cases hc

/-! ## The callee's activation after the `bl` -/

/-- **The compiled `atomic_rmw` entered by the caller's `bl` from `s`**: the hook's state
`enterR s`, the caller's addresses (`RC.F`: its frame, its code, the callee's code) kept. -/
def RLx (s : ArmState) : RL :=
  { act vcpR rfR with base := 0x20000#64, s0 := enterR s, G := RC.F }

theorem pR_eq : RAR.s0.program = pR := ArmAllocThread.Witness.entryAt_program _ _ _

theorem enterR_program (s : ArmState) : (enterR s).program = pR := by
  simp only [enterR, w_program]; rfl

theorem RLx_program (s : ArmState) : (RLx s).s0.program = pR := enterR_program s

theorem r_enterR {f : StateField} (h1 : f ≠ .PC) (h2 : f ≠ .GPR 30#5) (s : ArmState) :
    Arm.r f (enterR s) = Arm.r f s := by
  unfold enterR
  rw [Arm.r_of_w_different h1, Arm.r_of_w_different h2, E2E.r_set_program]

theorem mem_enterR (s : ArmState) : (enterR s).mem = s.mem := by
  unfold enterR; rw [w_mem, w_mem]; rfl

theorem regVal_enterR0 (s : ArmState) : regVal (enterR s) (.x 0) = regVal s (.x 0) := by
  simp only [regVal]
  rw [r_enterR (by decide) (by decide)]

theorem regVal_enterR1 (s : ArmState) : regVal (enterR s) (.x 1) = regVal s (.x 1) := by
  simp only [regVal]
  rw [r_enterR (by decide) (by decide)]

section bl
variable {s : ArmState} {m : Loc → CV}

theorem spv_enterR (hS : StRel RC s m w₀C) : E2E.spv (enterR s) = 0x6F40#64 := by
  unfold E2E.spv
  rw [r_enterR (by simp) (by simp)]
  have := hS.sp
  unfold spOf at this
  rw [this]
  show E2E.spv RC.s0 - BitVec.ofNat 64 (frameDrop RC.af) = _
  rw [spv_RC, spC.2.1]; rfl

/-- The caller's frame, code and the callee's code are above the caller's body `sp`. -/
theorem rcF_ge {a : BitVec 64} (h : RC.F a) : 0x6F40 ≤ a.toNat := by
  have hs := spC
  have e : E2E.spv RC.s0 - BitVec.ofNat 64 (frameDrop RC.af) = 0x6F40#64 := by
    rw [spv_RC, hs.2.1]; rfl
  have hK : RC.K = 0 := rfl
  have hsz := hs.2.2.2.2.2.1
  have hfs := hs.2.2.2.2.2.2.2.1
  unfold RL.F frameWG frameW frameF StackBelow at h
  rw [e, hK, hs.2.1, hfs] at h
  rcases h with ((⟨h1, h2⟩ | ⟨h1, h2⟩ | hc) | ⟨h1, h2⟩) | hG
  · generalize RC.fr.size = n at hsz h2
    bv_omega
  · bv_omega
  · obtain ⟨j, hj, hd⟩ := codeAddr_words program_RC hc
    rw [show RC.base = 0x30000#64 from rfl] at hd
    have : j < 0x4000 := by have := hs.2.2.2.2.1; omega
    generalize j = J at this hd
    bv_omega
  · simp only [BitVec.toNat_ofNat] at h1 h2; omega
  · have := gR_ge hG; omega

theorem stackX (hS : StRel RC s m w₀C) : StackAvail 0 (act vcpR rfR).af (enterR s) := by
  have hs := spC
  have hfs : (act vcpR rfR).af.frameSize = 192 := hs.2.2.2.2.2.2.2.2
  refine ⟨⟨?_, fun a ha => ?_⟩, ArmAllocThread.Witness.probeBelow_le_small (by omega)⟩
  · rw [spv_enterR hS, hfs]; decide
  · obtain ⟨j, hj, hd⟩ := codeAddr_words (enterR_program s) ha
    rw [spv_enterR hS, hfs]
    have : j < 0x4000 := by have := hs.2.2.2.1; omega
    generalize j = J at this hd
    bv_omega

theorem wfX (hS : StRel RC s m w₀C) : (RLx s).Wf := by
  obtain ⟨h1, h2, h3, h4, h5, h6, -, -, h9⟩ := factsR
  refine WitnessC.wf_gen allocR h1 h2 h3 h4 h5 h6 h9 (stackX hS) (enterR_program s)
    fun a hG ⟨ha, _⟩ => ?_
  have := rcF_ge hG
  rw [spv_enterR hS] at ha
  simp only [BitVec.toNat_ofNat] at ha
  omega

theorem abiX (hS : StRel RC s m w₀C) :
    AbiCall (RLx s).fb (RLx s).base (Arm.r .PC s + 4#64) (RLx s).s0 where
  program := enterR_program s
  code k w hk := by
    have hk' : (act vcpR rfR).fb.words[k]? = some w := hk
    have hR : Arm.read_mem_bytes 4 (0x20000#64 + BitVec.ofNat 64 (4 * k)) RAR.s0 = w :=
      Concurrency.CallThread.Witness.abiRR.code k w hk'
    obtain ⟨hlt, -⟩ := Array.getElem?_eq_some_iff.mp hk'
    show Arm.read_mem_bytes 4 (0x20000#64 + _) (enterR s) = _
    rw [← hR]
    apply read_mem_bytes_congr
    intro i hi
    have hG : GL (0x20000#64 + BitVec.ofNat 64 (4 * k) + BitVec.ofNat 64 i) := by
      unfold GL
      have : (act vcpR rfR).fb.words.size ≤ 0x4000 := spC.2.2.2.1
      generalize (act vcpR rfR).fb.words.size = n at this hlt
      bv_omega
    rw [mem_enterR, hS.gkeep _ hG]
    show memC _ = _
    rw [memC, if_pos hG]
  pc := by show Arm.r .PC (enterR s) = _; unfold enterR; rw [Arm.r_of_w_same]; rfl
  err := by show Arm.r .ERR (enterR s) = _; rw [r_enterR (by simp) (by simp)]; exact hS.err
  lr := by
    show Arm.r (.GPR (BitVec.ofNat 5 30)) (enterR s) = _
    unfold enterR
    rw [Arm.r_of_w_different (by simp)]
    exact Arm.r_of_w_same
  spAligned := by rw [show E2E.spv (RLx s).s0 = _ from spv_enterR hS]; decide
  fits := by
    have := spC.2.2.2.1
    show (0x20000#64 : BitVec 64).toNat + 4 * (act vcpR rfR).fb.words.size ≤ _
    simp only [BitVec.toNat_ofNat]; omega

theorem entryArgX (s : ArmState) : ∀ r, (RLx s).vc.EntryArg r → r.isArgReg = true := by
  rintro r ⟨vb, ds, h1, h2, v, hv⟩
  have h := entryArgsR
  simp only [entryArgsB, show vcpR = (RLx s).vc from rfl, h1, h2, List.all_eq_true] at h
  exact h _ hv

/-- The callee's body-entry world. -/
abbrev w₀X (s : ArmState) : ArmState := E2E.bodyOf (RLx s).af (RLx s).s0

theorem bodyX (s : ArmState) :
    BodyEntryW (RLx s).F (RLx s).vc.EntryArg (RLx s).af (RLx s).s0 (w₀X s) :=
  (E2E.Binary.bodyEntry_bodyOf (RLx s).af (RLx s).s0).w (RLx s).F (entryArgX s)

/-- The callee's memory scope (with LL/SC loops), from `scopeLR`. -/
theorem scopeX (s : ArmState) : MemScopeL (RLx s) := by
  have h : (RLx s).vc.blocks.all (·.insts.all (formRB (RLx s).ctx)) = true := scopeLR
  intro b vb k i hb hi
  obtain ⟨hb', rfl⟩ := Array.getElem?_eq_some_iff.mp hb
  obtain ⟨hk', rfl⟩ := Array.getElem?_eq_some_iff.mp hi
  have h1 := (Array.all_eq_true.mp h) b hb'
  have h2 := (Array.all_eq_true.mp h1) k hk'
  revert h2
  generalize (RLx s).vc.blocks[b].insts[k] = i
  intro h2
  cases i with
  | fence => exact .inl (.inr (.inl rfl))
  | args ds => exact .inl (.inl (.inr (.inl ⟨ds, rfl⟩)))
  | rets us => exact .inl (.inl (.inr (.inr (.inl ⟨us, rfl⟩))))
  | loadAcquire ty rt rn fl => exact .inl (.inr (.inr (.inl ⟨ty, rt, rn, fl, rfl, h2⟩)))
  | atomicRmwLoop => exact .inr (.inl ⟨_, _, _, _, _, _, _, _, rfl⟩)
  | _ => simp [formRB] at h2

/-- The callee's addresses are above its body `sp`. -/
theorem xF_ge (hS : StRel RC s m w₀C) {a : BitVec 64} (h : (RLx s).F a) :
    0x6E70 ≤ a.toNat := by
  have hs := spC
  have e : E2E.spv (enterR s) - BitVec.ofNat 64 (frameDrop (act vcpR rfR).af) = 0x6E70#64 := by
    rw [spv_enterR hS, hs.2.2.1]; rfl
  have hsz : (act vcpR rfR).fr.size ≤ 192 := hs.2.2.2.2.2.2.1
  have hfs : (act vcpR rfR).af.frameSize = 192 := hs.2.2.2.2.2.2.2.2
  change frameWG 0 (act vcpR rfR).fr.intBase (act vcpR rfR).fr.size (act vcpR rfR).af RC.F
    (enterR s) a at h
  unfold frameWG frameW frameF StackBelow at h
  rw [e, hs.2.2.1, hfs] at h
  rcases h with ((⟨h1, h2⟩ | ⟨h1, h2⟩ | hc) | ⟨h1, h2⟩) | hG
  · generalize (act vcpR rfR).fr.size = n at hsz h2
    bv_omega
  · bv_omega
  · obtain ⟨j, hj, hd⟩ := codeAddr_words (enterR_program s) hc
    have : j < 0x4000 := by have := hs.2.2.2.1; omega
    generalize j = J at this hd
    bv_omega
  · simp only [BitVec.toNat_ofNat] at h1 h2; omega
  · have := rcF_ge hG; omega

theorem errW₀X (hS : StRel RC s m w₀C) : Arm.r .ERR (w₀X s) = .None := by
  rw [E2E.r_bodyOf _ _ (by simp) (by simp)]
  show Arm.r .ERR (enterR s) = _
  rw [r_enterR (by simp) (by simp)]
  exact hS.err

/-- The memory relation's parameters of the callee (as `ΓR`). -/
def ΓX (s : ArmState) : E2E.Rel := ⟨(RLx s).F, fun _ => none, (RLx s).ctx.slotBase, 0⟩

theorem relX (hS : StRel RC s m w₀C) : E2E.RelW (ΓX s) fR (E2E.spv (w₀X s)) [] memL (w₀X s) := by
  refine ⟨⟨⟨fun a b _ hb => by simp [memL] at hb, fun a n hv => ?_, rfl⟩,
      fun id b h => by simp at h, E2E.outRel_zero _ _ _⟩, rfl, errW₀X hS⟩
  simp only [Clif.Mem.valid, memL, List.any_cons, List.any_nil, Bool.or_false,
    Clif.Alloc.contains] at hv
  have hv' : a + n ≤ 8 := by
    revert hv; simp only [Bool.and_eq_true, decide_eq_true_eq]; omega
  refine ⟨by omega, fun k hk hF => ?_⟩
  have := xF_ge hS hF
  simp only [BitVec.toNat_ofNat] at this
  omega

theorem argsAtX (hx0 : regVal s (.x 0) = 0) (hx1 : regVal s (.x 1) = 0) :
    ArgsAtEntry (RLx s).F fR.sig argsR (w₀X s) := by
  intro loc v h
  rw [locsR] at h
  simp only [argsR, List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.mem_singleton,
    Prod.mk.injEq, List.not_mem_nil, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · show VHolds _ _
    rw [VHolds, E2E.regVal_bodyOf _ _ (by decide)]
    rw [show (RLx s).s0 = enterR s from rfl, regVal_enterR0, hx0]
    rfl
  · show VHolds _ _
    rw [VHolds, E2E.regVal_bodyOf _ _ (by decide)]
    rw [show (RLx s).s0 = enterR s from rfl, regVal_enterR1, hx1]
    rfl

theorem alignX (hS : StRel RC s m w₀C) : (E2E.spv (w₀X s)).toNat % 16 = 0 := by
  rw [(bodyX s).sp]
  show (E2E.spv (enterR s) - BitVec.ofNat 64 (frameDrop (act vcpR rfR).af)).toNat % 16 = 0
  rw [spv_enterR hS, spC.2.2.1]; decide

/-- **`CompiledLS` for the callee entered from the caller's `bl`** (as `compiled_ofR`). -/
theorem compiled_ofX (hS : StRel RC s m w₀C) (hx0 : regVal s (.x 0) = 0)
    (hx1 : regVal s (.x 1) = 0) {s' : ArmState}
    (hq : Q (RLx s) s' (MConf.init (RLx s).rf (locVal (RLx s).fr s') (w₀X s)))
    (hA : AInv (RLx s) (MConf.init (RLx s).rf (locVal (RLx s).fr s') (w₀X s)))
    (env : Clif.Env) (p : Clif.Program) : CompiledLS env p (RLx s) csR s' := by
  obtain ⟨hlow, hthr, hext, hind, hv, -, hout, hprep, -⟩ := checksR
  obtain ⟨ctx, st0, R, gn, bl, A, H, hbl⟩ := driverHyp_of (Γ := ΓX s) (fctx := (RLx s).ctx)
    (X := (RLx s).X) (c := E2E.spv (w₀X s)) (env := env) (p := p) hlow hthr
    (List.isEmpty_iff.mp hext) (List.isEmpty_iff.mp hind) hv cfgR hout rfl (fun _ _ h => by cases h)
  obtain ⟨-, -, hpar, hsig, hlocs, -, hc, -⟩ := shapeR
  exact {
    wf := wfX hS
    scope := memScopeLS_of_memScopeB (memScopeB_of_memScopeL (scopeX s))
    gv := rfl
    front := ⟨fR, vcR, ctx, st0, R, gn, bl, A, _, [], (ΓX s).slotOff, (ΓX s).syms, B0R, argsR, _,
      w₀X s, H, hbl, E2E.memRelOk_relW (ΓX s) fR _, IselRefines.Witness.relW_wf (alignX hS),
      VCodeThread.Witness.X0_tls,
      memRefines_csem (RLx s).F (RLx s).ctx _ rfl (fun _ _ h => by cases h),
      E2E.mrStable_relW (ΓX s) fR _,
      (fun off h => by
        have := List.all_eq_true.mp hlocs _ h
        simp at this),
      hprep, allocR, b0R, rfl, rfl, rfl, rfl, rfl, regsR_eq, hpar, hsig, relX hS,
      argsAtX hx0 hx1, hq, hA⟩ }

/-- **Every premise of `CompiledE`** for the callee entered from the caller's `bl`. -/
theorem compiledEX (hS : StRel RC s m w₀C) (hx0 : regVal s (.x 0) = 0)
    (hx1 : regVal s (.x 1) = 0) (env : Clif.Env) (p : Clif.Program) :
    CompiledE env p (RLx s) csR := by
  obtain ⟨-, hq, hA⟩ := q_init_lines (wfX hS) (abiX hS) (bodyX s)
  exact ⟨wfX hS, memScopeLS_of_memScopeB (memScopeB_of_memScopeL (scopeX s)), rfl, ⟨_, abiX hS⟩,
    (compiled_ofX hS hx0 hx1 hq hA env p).front, probeF_R rfl⟩

theorem step_programX (s s' : ArmState) : ((RLx s).step s').program = s'.program :=
  CallThread.Witness.armStepX_program (fun _ _ => rfl) (fun _ _ _ => rfl) s'

/-- **The callee's contract**, entered from the caller's `bl` with the open monitor
(`funReal_calleeX`; every load exclusive of its program acquires, `wordLdxR`). -/
theorem funRealX (hS : StRel RC s m w₀C) (hx0 : regVal s (.x 0) = 0)
    (hx1 : regVal s (.x 1) = 0) (env : Clif.Env) (p : Clif.Program)
    (ext : List (Clif.Frame × List Clif.ValueId)) {M : ArmState → ArmState}
    (hM : ∀ s', s'.program = (RLx s).s0.program → M s' = (RLx s).step s') :
    CallCompose.FunReal env p (PrivA (RLx s)) M (OkPriv (RLx s)) (fun _ _ _ _ => False)
      (CalleeEnd env p (RLx s) ext) (enterR s, none) (.run (ClifLift.pushC ext csR)) :=
  funReal_calleeX (compiledEX hS hx0 hx1 env p) ext hM
    (fun s' h => (step_programX s s').trans h)
    (fun s' _ h => armStepX_err (fun _ _ h => h) (fun _ _ _ h => h) s' h)
    (fun s' h => WitnessX.ldxAcq_of_words Concurrency.CallThread.Witness.wordLdxR s'
      (by rw [h, RLx_program s]; exact pR_eq.symm))

end bl

/-! ## The CLIF call -/

theorem preC : (do
    let ext ← Clif.Res.ofOption s!"unknown function reference fn{(0 : Clif.FnRef)}"
      (csC.frame.func.extern? 0)
    let vals ← csC.frame.getMany [0, 1]
    Clif.checkTys s!"arguments of call to %{ext.name}" vals (Clif.AbiParam.tys ext.sig.params)
    pure (ext, vals) : Clif.Res (Clif.ExtFunc × List Clif.Val)) = .ok (extF, argsR) := by
  have h := preB_eq
  unfold preB at h
  revert h
  generalize (do
    let ext ← Clif.Res.ofOption s!"unknown function reference fn{(0 : Clif.FnRef)}"
      (csC.frame.func.extern? 0)
    let vals ← csC.frame.getMany [0, 1]
    Clif.checkTys s!"arguments of call to %{ext.name}" vals (Clif.AbiParam.tys ext.sig.params)
    pure (ext, vals) : Clif.Res (Clif.ExtFunc × List Clif.Val)) = r
  cases r <;> simp

/-- **The CLIF call step on any bytes**: the caller enters `%rmw` with the arguments `0`, `1`. -/
theorem stepC (env : Clif.Env) (B : Bytes) :
    Clif.step env pCR (withBytes csC B) = .next (withBytes (ClifLift.pushC extC csR) B) := by
  obtain ⟨hb, hf, hsig, hent, h1, h2, hsl⟩ := clifC
  rw [Clif.step_call env pCR _ [] [2] 0 [0, 1] hb]
  unfold Clif.stepCall
  simp only [show (withBytes csC B).frame = csC.frame from rfl]
  rw [preC]
  simp only [Clif.StepResult.ofRes_ok, hf, hsig, ite_true]
  rw [WitnessC.enterFunc_of' hent h1 h2 regsR_eq]
  simp only [Clif.StepResult.ofRes_ok]
  have hs : Clif.enterSlots fR (withBytes csC B).mem = ([], (withBytes csC B).mem) := by
    unfold Clif.enterSlots
    show Clif.bumpSlots fR.slots _ = _
    rw [hsl]; rfl
  rw [hs]
  rfl

/-- **The CLIF call step** (no events). -/
theorem cstepC (env : Clif.Env) :
    CStep env pCR (.run csC) [] (.run (ClifLift.pushC extC csR)) := by
  refine ⟨⟨?_, fun _ h => nomatch h⟩, ⟨csC.mem.bytes, trivial⟩, fun B _ =>
    ⟨.run (withBytes (ClifLift.pushC extC csR) B), by rw [stepC]; rfl, rfl⟩⟩
  show [] ∈ evShape csC
  unfold evShape
  rw [show csC.frame.body = B0C.body from rfl, clifC.1]
  simp

/-! ## The linked thread -/

/-- The length of the caller's path to its `bl` (`prefixC`). -/
noncomputable def n0C : Nat := Classical.choose prefixC

/-- The caller's state at its `bl`. -/
noncomputable def sBC : ArmState := iterN RC.step n0C RC.s0

/-- **The callee's activation in the linked thread** (entered by the caller's `bl`). -/
noncomputable def RLB : RL := RLx sBC

/-- The callee's machine. -/
noncomputable def stepR : ArmState → ArmState :=
  ArmStepX (act vcpR rfR).X (act vcpR rfR).H (act vcpR rfR).fa

open Classical in
/-- **The linked machine**: the callee's on the states holding its program, the caller's (whose
`bl rmw` hook enters the callee) otherwise. -/
noncomputable def MC (s : ArmState) : ArmState := if s.program = pR then stepR s else RC.step s

/-- **The end condition of the linked thread**: the realized Arm prefix ends with a prefix at
the callee's end (`CalleeEnd`: the callee's allocated code driven to its end, or its CLIF
activation stopped or returning). -/
def EndC (env : Clif.Env) (P : List Lab) (d : TState) : Prop :=
  ∃ A B, P = A ++ B ∧ CalleeEnd env pCR RLB extC B d

/-- **The compiled caller calling the compiled `atomic_rmw`, as a thread** (`link_compose`):
every precise run of the linked machine from the caller's ABI entry (open monitor), reading the
thread's own bytes at the callee's private addresses (which contain the caller's), realizes on a
prefix a run of the CLIF program `pCR` from the caller's entry state: the whole run, or ending
where the callee's compiled code reaches its end or its CLIF activation stops or returns. The
caller's part up to the `bl` is the single-core path through private steps (`prun_privF`), whose
monitor stays open (`prun_privF_mon`, `noLdxC`); the `bl` and the CLIF `call` have no events; the
callee's events are matched by its own refinement (`funRealX`). -/
theorem funReal_call (env : Clif.Env) :
    CallCompose.FunReal env pCR (PrivA RLB) MC (OkPriv RLB) (fun _ _ _ _ => False) (EndC env)
      (RC.s0, none) (.run csC) := by
  have hspec := Classical.choose_spec prefixC
  rw [show Classical.choose prefixC = n0C from rfl] at hspec
  obtain ⟨j, m, hpath, hj, hpc, hstr, hx0, hx1⟩ := hspec
  have hsub : ∀ a, PrivA RC a → PrivA RLB a := fun a h => Or.inr h
  have hM : ∀ s', s'.program = pR → MC s' = (RLx sBC).step s' := fun s' h => by
    simp only [MC, h, ite_true]; rfl
  refine CallCompose.link_compose (G := Bool) (Ext := fun g => g = true)
    (Ent := fun g u c => match g with
      | true => u.1 = RLB.s0 ∧ u.2 = none ∧ c = .run (ClifLift.pushC extC csR)
      | false => u = (RC.s0, none) ∧ c = .run csC)
    (Ret := fun _ _ _ _ _ => False) (E := EndC env)
    (Inv := fun g u c x d => g = false ∧ x = u ∧ d = c ∧ u = (RC.s0, none) ∧ c = .run csC)
    (fun A B d ⟨A', B', h, hc⟩ => ⟨A ++ A', B', by rw [h, List.append_assoc], hc⟩)
    (fun g u c hg he => ?_) (fun g hg => ?_) (fun h u c hh he => ?_) false (RC.s0, none) (.run csC)
    ⟨rfl, rfl⟩
  · cases g
    · exact ⟨rfl, rfl, rfl, he.1, he.2⟩
    · exact absurd rfl hg
  · -- the caller's segment: its path to the `bl`, then the call
    rintro u c x d ⟨-, rfl, rfl, rfl, rfl⟩ ls t' hr
    have hagree : ∀ i < n0C, MC (iterN RC.step i RC.s0) = RC.step (iterN RC.step i RC.s0) := by
      intro i hi
      simp only [MC]
      rw [if_neg (by rw [(hpath i hi).2]; exact progC_ne)]
    have hmono : ∀ {L : List Lab} {v : ArmState × Mon},
        PRun Policy.arm MC (OkPriv RLB) (RC.s0, none) L v →
        PRun Policy.arm MC (OkPriv RC) (RC.s0, none) L v :=
      fun h => PRun.mono (fun _ _ h e he hd hp => h e he hd (hsub _ hp)) h
    have hldx : ∀ i < n0C, ∀ a rn sz, cls (iterN RC.step i RC.s0) ≠ .ldx a rn sz :=
      fun i hi a rn sz => noLdxC _ ((hpath i hi).2) a rn sz
    have hW : PrivW (PrivA RLB) (segEvs RC.step n0C RC.s0) := fun p y hy hd =>
      (fun h => ⟨hsub _ h.1, h.2⟩) (privW_segEvs (fun i hi => (hpath i hi).1.1)
        (fun i hi => stepEvs_noRelXW (hpath i hi).1.2) p y hy hd)
    by_cases hlen : ls.length ≤ n0C
    · obtain ⟨-, hev, hk⟩ := prun_privF (hmono hr) fun i hi =>
        ⟨(hpath i (by omega)).1.1, (hpath i (by omega)).1.2, hagree i (by omega)⟩
      refine ⟨ls.length, .run csC, ⟨Nat.le_refl _, [], id, .nil, ?_, ?_⟩, .inl rfl⟩
      · rw [List.take_length]; exact WitnessC.xClosed_labs fun l hl => (hk l hl).2
      · rw [List.take_length, hev]
        exact refines_nilS (fun x hx => absurd hx List.not_mem_nil) fun p y hy hd =>
          (fun h => ⟨hsub _ h.1, h.2⟩) (privW_segEvs (fun i hi => (hpath i (by omega)).1.1)
            (fun i hi => stepEvs_noRelXW (hpath i (by omega)).1.2) p y hy hd)
    · -- the path to the `bl`, then the `bl` step
      obtain ⟨v, hv, hrest⟩ := CallCompose.take_prun hr n0C
      have hlt : (ls.take n0C).length = n0C := by simp; omega
      obtain ⟨hv1, hev, hk⟩ := prun_privF (hmono hv) fun i hi =>
        ⟨(hpath i (by omega)).1.1, (hpath i (by omega)).1.2, hagree i (by omega)⟩
      rw [hlt] at hev
      have hv2 := prun_privF_mon (hmono hv)
        (fun i hi => ⟨(hpath i (by omega)).1.1, (hpath i (by omega)).1.2,
          hagree i (by omega)⟩)
        (fun i hi a rn sz => hldx i (by omega) a rn sz) rfl
      rw [hlt] at hv1
      obtain ⟨l, rest, hdrop⟩ : ∃ l rest, ls.drop n0C = l :: rest := by
        cases h : ls.drop n0C with
        | nil => simp at h; omega
        | cons l rest => exact ⟨l, rest, rfl⟩
      rw [hdrop] at hrest
      obtain ⟨v1, v2⟩ := v
      simp only at hv1 hv2
      subst hv1
      subst hv2
      cases hrest with
      | cons hs hp ho _ =>
        obtain ⟨hst, hse, hcls⟩ := step_bl wfRC hj hstr.prog hpc
        obtain ⟨rfl, ht1⟩ := tstep_plain_nil hs hp hse hcls
        have hMC : MC (iterN RC.step n0C RC.s0) = enterR sBC := by
          simp only [MC]
          rw [if_neg (by rw [hstr.prog]; exact progC_ne), hst]
          show (if some "rmw" = some "rmw" then enterR (iterN RC.step n0C RC.s0)
            else iterN RC.step n0C RC.s0) = _
          rw [if_pos rfl]; rfl
        rw [hMC] at ht1
        subst ht1
        have htake : ls.take (n0C + 1) = ls.take n0C ++ [⟨[], false⟩] := by
          rw [List.take_add, hdrop]; rfl
        have hev1 : evTr (ls.take (n0C + 1)) = segEvs RC.step n0C RC.s0 ++ [[]] := by
          rw [htake, evTr_append, hev]; rfl
        refine ⟨n0C + 1, .run (ClifLift.pushC extC csR), ⟨by omega, [[]], id,
          .cons (cstepC env) .nil, ?_, ?_⟩,
          .inr (.inr (.inr ⟨by omega, (enterR sBC, none), true, ?_, ⟨rfl, rfl, rfl⟩,
          fun _ _ h => h.elim⟩))⟩
        · rw [htake]
          refine WitnessC.xClosed_labs fun l' hl' => ?_
          rcases List.mem_append.mp hl' with hl' | hl'
          · exact (hk l' hl').2
          · simp only [List.mem_singleton] at hl'
            subst hl'
            intro e he
            exact absurd he List.not_mem_nil
        · rw [hev1]
          exact refines_nilS (fun x hx => by simp at hx; exact hx)
            (WitnessC.privW_snoc_nil hW)
        · rw [htake]
          exact PRun.append hv (.cons hs hp ho .nil)
  · subst hh
    obtain ⟨⟨u1, u2⟩, rfl⟩ : ∃ v : ArmState × Mon, v = u := ⟨u, rfl⟩
    obtain ⟨hu1, hu2, rfl⟩ := he
    simp only at hu1
    subst hu1
    subst hu2
    intro ls t' hr
    obtain ⟨k, c', hR, hend⟩ := funRealX hstr hx0 hx1 env pCR extC
      (fun s' h => hM s' (by rw [h]; exact RLx_program sBC)) ls t' hr
    refine ⟨k, c', hR, ?_⟩
    rcases hend with h | h | h
    · exact .inl h
    · exact .inr (.inl ⟨[], _, rfl, h⟩)
    · exact .inr (.inr h)

/-- **The thread through the call realizes the CLIF program** (`realizes_linked` with the
caller's thread contract `funReal_call`): every execution of the realized prefix of a precise run
of the linked machine from the caller's ABI entry (as `realizes_linked`'s premises) is realized
by a CLIF thread of `pCR` from the caller's entry state. -/
theorem realizes_call (env : Clif.Env) {ls : List Lab} {t' : CallCompose.AT}
    (hr : PRun Policy.arm MC (OkPriv RLB) (RC.s0, none) ls t') :
    ∃ k : Nat → Nat, (∀ i < 1, k i ≤ ls.length) ∧
      ∀ (PA : Traces ProgE2E.AState AKind BVal) (locsA locsC : List (Nat × Nat)) (MA0 MC0 : Bytes)
        (rfA coA rmwA : Rel PEv), PA.n = 1 →
        (∀ i < 1, PA.tr i = conv (evTr (ls.take (k i)))) →
        (PA.exec locsA rfA coA rmwA).Wf →
        (∀ i < 1, ∀ a b, rmwA (.thr i a.1 a.2) (.thr i b.1 b.2) ↔
          MonPair (evTr (ls.take (k i))) a b) →
        locsC <+: locsA →
        (∀ q (h : q < locsA.length), locsC.length ≤ q → ∃ j, j < 1 ∧ PrivA RLB (locsA[q]).1) →
        (∀ q (h : q < locsC.length),
          bytesI.get MA0 (locsC[q]).1 (locsC[q]).2 = bytesI.get MC0 (locsC[q]).1 (locsC[q]).2) →
        (∀ i < 1, ∀ j < 1, j ≠ i → ∀ q x, evAt (PA.tr i) q = some x → x.dir ≠ .F →
          ¬ PrivA RLB x.loc) →
        ∃ (PC : Traces TState SKind BVal) (φ : PEv → PEv), PC.n = 1 ∧
          (∀ i < 1, PC.st i 0 = .run csC) ∧ PC.Runs (CStep env pCR) ∧
          Realizes PA locsA MA0 rfA coA rmwA PC locsC MC0 φ (fun _ _ _ => True) :=
  CallCompose.realizes_linked (Priv := fun _ => PrivA RLB) (M := fun _ => MC)
    (ok := fun _ => OkPriv RLB) (cs := fun _ => .run csC) (sA := fun _ => (RC.s0, none))
    (fun _ _ ls t' hr => by
      obtain ⟨k, c', hR, -⟩ := funReal_call env ls t' hr
      exact ⟨k, c', hR⟩)
    (ls := fun _ => ls) (t' := fun _ => t') (fun _ _ => hr)

end Concurrency.CallSeg.WitnessCR