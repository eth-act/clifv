import FV.Concurrency.CallLoadWitness
import FV.Concurrency.CallResume

/-!
# The compiled caller's whole run through the compiled `atomic_load` and back (T2j follow-up, #473)

`CallLoadWitness.funReal_call` realizes the caller's run up to where the callee's compiled code
or CLIF activation ends. Here the run continues: the callee returns and the caller resumes and
returns too, and every precise run of the linked thread is realized entirely or up to where the
CLIF thread stops (`funReal_callFull`, `realizes_call_full`), through `CallCompose.link_compose`
with a return (`Ret`) of the callee:

* `MC2`, the linked machine: the callee's step on its program, except at its `ret` line
  (`IsRetL`), where the step also switches back to the caller's program (the return to the
  caller); the caller's step otherwise;
* the callee's run (`calleePath`, `mstep_ldar`, `funReal_ld`): the single-core path through its
  prologue, saves, `args` and spill moves (private, at lines other than `ret`), the `ldar` (its one
  event, read through `oneEv_op1`, the source step existing by layers 2–4a's progress), the moves
  and restores, the epilogue (`rets_privP`), the `ret`; on the CLIF side the `atomic_load` reading
  the `ldar`'s bytes (`cstep_ld`) and the return to the caller (`cstep_ret_pop`);
* the caller resumed (`resumeQ`: `Q` at the item after its call, from what the callee keeps), its
  moves, restores and epilogue, and the CLIF `return`.

Checks by `native_decide` (witness only).
-/

namespace Concurrency.CallSeg.WitnessC

open Arm ArmFoot ArmThread Prog ClifThread ProgE2E Backend Backend.Proof Backend.Proof.Driver
  VCodeThread PrepThread AllocThread ThreadRefine ArmAllocThread E2E ArmInstFoot Code
  RealizeCompiled RealizeCompiled.Witness RealizeCompiled.WitnessL CallThread
open ArmAllocThread.Witness (act entryAt codeMem)

/-! ## Checks -/

/-- The moves after the `ldar` (`r = x1`) or the `call` (`r = x0`): the result to its slot, the
restores of the callee-saved registers, the result back to x0. -/
def postMv (r : Reg) : List (Loc × Loc) :=
  (.reg r, .stack 1 .int) :: (savesL.map (fun p => (p.2, p.1)) ++ [(.stack 1 .int, .reg (.x 0))])

/-- The lines of a move have no `ret` (as a check). -/
def moveNoRetB (R : RL) (p : Loc × Loc) : Bool :=
  match R.fr.moveInsts p.1 p.2 with
  | .ok code => match codeLinesE R.ctx R.af code {} with
    | .ok (ls1, _) => ls1.all (fun ln => match ln with | .ins .ret _ => false | _ => true)
    | .error _ => true
  | .error _ => true

theorem moves_noRet {R : RL} {mvs : List (Loc × Loc)} (h : mvs.all (moveNoRetB R) = true) :
    ∀ p ∈ mvs, ∀ code ls1, R.fr.moveInsts p.1 p.2 = .ok code →
      codeLinesE R.ctx R.af code {} = .ok (ls1, {}) → NoRet ls1 := by
  intro p hp code ls1 hc hl x t hx hxr
  subst hxr
  have h := (List.all_eq_true.mp h) p hp
  simp only [moveNoRetB, hc, hl, List.all_eq_true] at h
  have := h _ hx
  simp at this

/-- The `ldar` and the `rets` of the callee, the `rets` of the caller (as a check). -/
def instsLB : Bool :=
  (match (vcpL.blocks[0]!).insts[1]? with
    | some (MInst.loadAcquire (.int 64) (.vreg 2 .int) (.vreg 0 .int) fl) =>
      FormOk (act vcpL rfL).ctx (.loadAcquire (.int 64) (.vreg 2 .int) (.vreg 0 .int) fl)
    | _ => false) &&
  (match (vcpL.blocks[0]!).insts[2]? with
    | some (MInst.rets [(.vreg 2 .int, .x 0)]) => true
    | _ => false) &&
  (match (vcpC.blocks[0]!).insts[2]? with
    | some (MInst.rets [(.vreg 2 .int, .x 0)]) => true
    | _ => false)

theorem checksPost :
    rest2L = .op 1 #[.reg (.x 0), .reg (.x 1)] ::
      ((postMv (.x 1)).map (fun p => RItem.move p.1 p.2) ++ [.op 2 #[.reg (.x 0)]]) ∧
    restC = .op 1 #[.reg (.x 0), .reg (.x 0)] ::
      ((postMv (.x 0)).map (fun p => RItem.move p.1 p.2) ++ [.op 2 #[.reg (.x 0)]]) ∧
    (savesL ++ spillL ++ postMv (.x 1)).all (moveNoRetB (act vcpL rfL)) = true ∧
    instsLB = true ∧ 3 = (vcpC.blocks[0]!).insts.size := by
  native_decide

theorem instL1 : ∃ fl, (vcpL.blocks[0]!).insts[1]? =
      some (.loadAcquire (.int 64) (.vreg 2 .int) (.vreg 0 .int) fl) ∧
    FormOk (act vcpL rfL).ctx (.loadAcquire (.int 64) (.vreg 2 .int) (.vreg 0 .int) fl) = true := by
  have h := checksPost.2.2.2.1
  simp only [instsLB, Bool.and_eq_true] at h
  obtain ⟨⟨h1, -⟩, -⟩ := h
  revert h1
  generalize (vcpL.blocks[0]!).insts[1]? = oi
  intro h1
  split at h1
  · exact ⟨_, rfl, h1⟩
  · cases h1

theorem instL2 : (vcpL.blocks[0]!).insts[2]? = some (.rets [(.vreg 2 .int, .x 0)]) := by
  have h := checksPost.2.2.2.1
  simp only [instsLB, Bool.and_eq_true] at h
  obtain ⟨⟨-, h2⟩, -⟩ := h
  revert h2
  generalize (vcpL.blocks[0]!).insts[2]? = oi
  intro h2
  split at h2
  · rfl
  · cases h2

theorem instC2 : (vcpC.blocks[0]!).insts[2]? = some (.rets [(.vreg 2 .int, .x 0)]) := by
  have h := checksPost.2.2.2.1
  simp only [instsLB, Bool.and_eq_true] at h
  obtain ⟨-, h3⟩ := h
  revert h3
  generalize (vcpC.blocks[0]!).insts[2]? = oi
  intro h3
  split at h3
  · rfl
  · cases h3

/-! ## The callee's path to its `ldar` -/

section callee
variable {s : ArmState} {m : Loc → CV}

/-- The entry `args` as a step of the callee's allocated code (as `WitnessL.args_step`). -/
theorem args_stepX (its : List RItem) (m' : Loc → CV) (w : ArmState) :
    ∃ m'', MStep (RLx s).vc (RLx s).sem ckeep (RLx s).rf (.run ⟨0, .op 0 #[.reg (.x 0)] :: its, m', w⟩)
      (.run ⟨0, its, m'', w⟩) ∧ m'' (.reg (.x 0)) = regVal w (.x 0) := by
  obtain ⟨hi, hsz⟩ := argsL0
  refine ⟨_, MStep.op vb0L hi (operands_args [(0, .x 0)]) rfl rfl
    (by simp [argOps, Operand.isDef]) (HavocOuts.refl _ _ _)
    ⟨fun _ _ => rfl, fun c hc => by cases hc⟩ (MNext.next (by rw [hsz]; decide)), ?_⟩
  simp [Proof.writeM, argOps, Operand.isDef, Operand.isLate, Operand.isEarly, Backend.Proof.upd]

theorem coveredX (hS : StRel RC s m w₀C) (hx0 : regVal s (.x 0) = 0) :
    ThreadProgress.CoveredCode (RLx s) :=
  ThreadProgress.coveredCode_of_ls (compiledEX hS hx0 default default).scope

/-- **The callee's path from its ABI entry to its `ldar`** (module doc): the prologue, the saves,
the entry `args` and the spill moves, every step private, no store exclusive, on the callee's
program, at a line other than `ret`; `Q ∧ AInv` at the `ldar`'s configuration, reached by an
event-free run of the allocated code from its entry configuration; its address x0 is `0`. -/
theorem calleePath (hS : StRel RC s m w₀C) (hx0 : regVal s (.x 0) = 0) :
    ∃ (n0 : Nat) (mL : Loc → CV) (trM : List (List Ev)),
      (∀ i < n0, ((∀ e ∈ stepEvs (iterN (RLx s).step i (RLx s).s0), (RLx s).F e.addr) ∧
        NoStx (iterN (RLx s).step i (RLx s).s0)) ∧
        (iterN (RLx s).step i (RLx s).s0).program = (RLx s).fb.program (RLx s).base ∧
        AtNonRet (RLx s) (iterN (RLx s).step i (RLx s).s0)) ∧
      Q (RLx s) (iterN (RLx s).step n0 (RLx s).s0) (.run ⟨0, rest2L, mL, w₀X s⟩) ∧
      AInv (RLx s) (.run ⟨0, rest2L, mL, w₀X s⟩) ∧
      SRun (SrcStep (RLx s)) (MConf.init (RLx s).rf (locVal (RLx s).fr
        (iterN (RLx s).step (prologueLines (RLx s).af.frameSize).length (RLx s).s0)) (w₀X s))
        trM (.run ⟨0, rest2L, mL, w₀X s⟩) ∧
      (∀ x ∈ trM, x = []) ∧ mL (.reg (.x 0)) = 0 := by
  have hR := wfX hS
  obtain ⟨hlat, hq, hA⟩ := q_init_lines hR (abiX hS) (bodyX s)
  have hpe := prologue_evs hR (abiX hS) hlat
  have hpr0 := linesAt_program hR hlat
  have hnr0 := linesAt_nonRet hR hlat (noRet_prologue _)
  generalize hP : (prologueLines (RLx s).af.frameSize).length = n0 at hpe hpr0 hnr0 hq hA ⊢
  have hq0 := hq
  have hA0 := hA
  simp only [MConf.init] at hq0 hA0
  rw [show (RLx s).rf = rfL from rfl, checksRunL.1] at hq0 hA0
  have hnr := moves_noRet (R := RLx s) checksPost.2.2.1
  obtain ⟨n1, hq1, hA1, hp1⟩ := moves_privP hR savesL _ _ _ hq0 hA0
    fun p hp => hnr p (by simp [hp])
  obtain ⟨m', hst, hm'⟩ := args_stepX (s := s) (spillL.map (fun p => RItem.move p.1 p.2) ++ rest2L) _
    (w₀X s)
  have hq2 := realizes_args hR hq1 hA1 vb0L argsL0.1 hst
  have hA2 := Backend.Proof.aInv_step hR hq1 hA1 hst
  obtain ⟨n2, hq3, hA3, hp2⟩ := moves_privP hR spillL rest2L _ m' hq2 hA2
    fun p hp => hnr p (by simp [hp])
  have hsa := srcStep_of_mstep_nil (coveredX hS hx0) VCodeThread.Witness.X0_tls hq1
    (fun vb i hvb hi => by
      have h0 : (RLx s).vc.blocks[0]? = some vcpL.blocks[0]! := vb0L
      rw [h0] at hvb; cases hvb; rw [argsL0.1] at hi; cases hi; rfl) hst
  rw [← iterN_add, ← iterN_add, ← Nat.add_assoc] at hq3
  have e0 : MConf.init (RLx s).rf (locVal (RLx s).fr (iterN (RLx s).step n0 (RLx s).s0)) (w₀X s) =
      .run ⟨0, savesL.map (fun p => RItem.move p.1 p.2) ++ (.op 0 #[.reg (.x 0)] ::
        (spillL.map (fun p => RItem.move p.1 p.2) ++ rest2L)),
        locVal (RLx s).fr (iterN (RLx s).step n0 (RLx s).s0), w₀X s⟩ := by
    simp only [MConf.init]; rw [show (RLx s).rf = rfL from rfl, checksRunL.1]
  refine ⟨n0 + n1 + n2, _, _, fun i hi => ?_, hq3, hA3,
    e0 ▸ SRun.append' (srun_moves savesL _ _) (.cons hsa (srun_moves spillL rest2L m')),
    fun x hx => ?_, ?_⟩
  · by_cases h0 : i < n0
    · exact ⟨⟨fun e he => (hpe i h0).1 e he |>.1, (hpe i h0).2⟩, hpr0 i (by omega), hnr0 i (by omega)⟩
    by_cases h1 : i < n0 + n1
    · have := hp1 (i - n0) (by omega)
      rw [← iterN_add, show n0 + (i - n0) = i by omega] at this
      exact this
    · have := hp2 (i - (n0 + n1)) (by omega)
      rw [← iterN_add, ← iterN_add, show n0 + (n1 + (i - (n0 + n1))) = i by omega] at this
      exact this
  · simp only [List.mem_append, List.mem_map, List.mem_cons] at hx
    rcases hx with ⟨_, _, rfl⟩ | rfl | ⟨_, _, rfl⟩ <;> rfl
  · have hx0' : movesM spillL m' (.reg (.x 0)) = regVal (w₀X s) (.x 0) := by
      simp [movesM, spillL, Backend.Proof.upd, hm']
    rw [hx0', E2E.regVal_bodyOf _ _ (by decide)]
    show regVal (enterL s) (.x 0) = 0
    rw [regVal_enterL, hx0]

end callee

/-! ## The CLIF side: the callee's load and return, the caller's return -/

/-- The CLIF facts of the two functions (as checks). -/
theorem clifF : csL.frame.term = .ret [1] ∧ Clif.AbiParam.tys fL.sig.returns = [.i64] ∧
    csL.frame.slots = [] ∧ csL.frame.func = fL ∧ csL.callers = [] ∧
    csC.frame.term = .ret [1] ∧ Clif.AbiParam.tys fC.sig.returns = [.i64] ∧
    csC.frame.slots = [] ∧ csC.frame.func = fC ∧
    csL.frame.body.length = 1 ∧ (csL.frame.body.head?.map (·.results)) = some [1] := by
  native_decide

/-- **The CLIF state of a frame ready to return its `v1`** (its body done, `return v1`, no slots,
of function `f`). -/
def RetReady (f : Clif.Function) (s : Clif.State) : Prop :=
  s.frame.body = [] ∧ s.frame.term = .ret [1] ∧ s.frame.slots = [] ∧ s.frame.func = f ∧
    ∃ v : BitVec 64, s.frame.regs 1 = some ⟨.i64, v⟩

theorem free_bytes (c : Clif.Mem) (bases : List Nat) : (c.free bases).bytes = c.bytes := by
  have := ClifCStepTerm.withB_free c c.bytes bases
  rw [show ClifCStep.withB c c.bytes = c from rfl] at this
  rw [this]

theorem leave_bytes (c : Clif.Mem) : c.leave.bytes = c.bytes := by
  have := ClifCStepTerm.withB_leave c c.bytes
  rw [show ClifCStep.withB c c.bytes = c from rfl] at this
  rw [this]

/-- **The caller's `return v1`** (its callers none): a step without events to `.ret`. -/
theorem cstep_retC (env : Clif.Env) {d : Clif.State} (hd : RetReady fC d) (hc : d.callers = []) :
    ∃ vals, CStep env pCL (.run d) [] (.ret vals) := by
  obtain ⟨hb, hT, hsl, hf, v, hv⟩ := hd
  have hret := clifF.2.2.2.2.2.2.1
  refine ⟨[⟨.i64, v⟩], ClifCStepTerm.cstep_term hb hc (by rw [hT]; intro _ _ h; cases h)
    (by rw [hT]; rfl) ?_⟩
  rw [Clif.step_term env pCL _ hb, hT]
  simp [Clif.stepTerm, Clif.Frame.getMany, Clif.Frame.get, hv, Clif.returnValues, Clif.checkTys,
    Clif.Res.check, hf, hret, hc, hsl, res, free_bytes, leave_bytes]

/-- **The callee's `atomic_load` on any bytes there**: a step to a frame ready to return. -/
theorem stepLd (env : Clif.Env) (B : Bytes) (hB : ∀ j < 8, (B (0 + j)).isSome) :
    ∃ s1, Clif.step env pCL (withBytes csL B) = .next s1 ∧ RetReady fL s1 ∧ s1.callers = [] := by
  obtain ⟨st, rest, hb, hi⟩ := bodyL
  obtain ⟨hT, -, hsl, hf, hcl, -, -, -, -, hlen, hres⟩ := clifF
  have hrest : rest = [] := by rw [hb] at hlen; simpa using hlen
  subst hrest
  have hres1 : st.results = [1] := by rw [hb] at hres; simpa using hres
  have hb' : (withBytes csL B).frame.body = [st] := hb
  have hc : ∀ fn args, st.inst ≠ .call fn args := fun _ _ h => by rw [hi] at h; cases h
  have hci : ∀ sig callee args, st.inst ≠ .callIndirect sig callee args :=
    fun _ _ _ h => by rw [hi] at h; cases h
  obtain ⟨old0, hold0⟩ : ∃ old0, (withBytes csL (fun _ => some 0)).mem.load {} 0 8 64 = .ok old0 := by
    have h : (match (withBytes csL (fun _ => some 0)).mem.load {} 0 8 64 with
      | .ok _ => true | _ => false) = true := by native_decide
    revert h
    cases (withBytes csL (fun _ => some 0)).mem.load {} 0 8 64 with
    | ok v => intro _; exact ⟨v, rfl⟩
    | _ => intro h; cases h
  obtain ⟨-, -, hall⟩ := IselClif.load_ok (by rfl) hold0
  obtain ⟨old, hold⟩ := hall (withBytes csL B).mem rfl hB
  rw [Clif.step_inst env pCL _ st [] hb' hc hci, hi]
  simp only [Clif.evalInst, Clif.Frame.get, show (withBytes csL B).frame = csL.frame from rfl, regL0,
    Clif.Res.ofOption_some, Clif.Res.ok_bind]
  have hold' : (withBytes csL B).mem.load {} 0 8 Clif.Ty.i64.width = .ok old := hold
  rw [show Clif.effAddr ⟨.i64, 0⟩ 0 = 0 from rfl, show Clif.Ty.i64.bytes = 8 from rfl, hold']
  simp only [Clif.Res.check, show (0 % 8 == 0) = true from rfl, ite_true, Clif.Res.ok_bind,
    pure, Clif.StepResult.ofRes_ok, Clif.continueWith, hres1, Clif.Regs.setMany]
  refine ⟨_, rfl, ⟨rfl, hT, hsl, hf, old, ?_⟩, hcl⟩
  simp

/-- **The callee's load and return to the caller** (`ClifLift`): on the bytes `bv` read, the
`atomic_load` step with its one read, then the return into the caller, which is ready to return. -/
theorem cstep_ld (env : Clif.Env) (bv : BVal) (hl : bv.length = 8) (hs : ∀ x ∈ bv, x.isSome) :
    ∃ s1 d, CStep env pCL (.run (ClifLift.pushC extC csL)) [⟨.scR, .R, 0, 8, bv⟩]
        (.run (ClifLift.pushC extC s1)) ∧
      CStep env pCL (.run (ClifLift.pushC extC s1)) [] (.run d) ∧ RetReady fC d ∧ d.callers = [] := by
  obtain ⟨st, rest, hb, hi⟩ := bodyL
  have hB : ∀ j < 8, (putB (fun _ => none) 0 8 bv (0 + j)).isSome := by
    intro j hj
    simp only [putB, Nat.zero_add, Nat.zero_le, true_and, hj, ite_true, Nat.sub_zero]
    have : bv[j]? = some bv[j] := List.getElem?_eq_getElem (by omega)
    rw [List.getD_eq_getElem?_getD, this]
    exact hs _ (List.getElem_mem _)
  obtain ⟨s1, hst, ⟨hb1, hT1, hsl1, hf1, v, hv⟩, hcl1⟩ := stepLd env _ hB
  have hstep : Clif.step env pCL (withBytes (ClifLift.pushC extC csL) (putB (fun _ => none) 0 8 bv)) =
      .next (ClifLift.pushC extC s1) := by
    rw [ClifLift.withBytes_pushC, ClifLift.step_pushC, hst]; rfl
  have hc1 := ClifCStep.cstep_atomicLoad (env := env) (p := pCL) (s := withBytes (ClifLift.pushC extC csL)
    (putB (fun _ => none) 0 8 bv)) hb hi regL0 hstep
  have hget : getB (putB (fun _ => none) 0 8 bv) 0 8 = bv := by
    have := bytesI.get_put_same (fun _ => none) 0 8 bv hl
    exact this
  rw [show (withBytes (ClifLift.pushC extC csL) (putB (fun _ => none) 0 8 bv)).mem.bytes =
    putB (fun _ => none) 0 8 bv from rfl, show Clif.effAddr ⟨.i64, 0⟩ 0 = 0 from rfl,
    show Clif.Ty.i64.bytes = 8 from rfl, hget] at hc1
  have hret := clifF.2.1
  obtain ⟨regs, hregs⟩ : ∃ regs, ({ csC.frame with body := [] } : Clif.Frame).regs.setMany [1]
      [⟨.i64, v⟩] = some regs := ⟨_, rfl⟩
  have hc2 := ClifCStepTerm.cstep_ret_pop (env := env) (p := pCL) (s := ClifLift.pushC extC s1)
    hb1 hT1 (vals := [⟨.i64, v⟩]) (by
      simp only [Clif.Frame.getMany, Clif.Frame.get, show (ClifLift.pushC extC s1).frame = s1.frame
        from rfl, hv, Clif.Res.ofOption_some, Clif.Res.ok_bind]; rfl)
    (u := ()) (by
      show Clif.checkTys _ _ _ = _
      rw [show (ClifLift.pushC extC s1).frame = s1.frame from rfl, hf1, hret]
      simp [Clif.checkTys, Clif.Res.check])
    (show s1.callers ++ extC = _ from by rw [hcl1]; rfl) hregs
  refine ⟨s1, _, hc1, hc2, ⟨rfl, clifF.2.2.2.2.2.1, clifF.2.2.2.2.2.2.2.1, clifF.2.2.2.2.2.2.2.2.1,
    v, ?_⟩, rfl⟩
  rw [← Option.some_inj.mpr rfl] at hregs
  simp only [Clif.Regs.setMany, Option.some.injEq] at hregs
  subst hregs
  simp

end Concurrency.CallSeg.WitnessC
