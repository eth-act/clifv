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

/-- The caller's moves after its call have no `ret` (as a check). -/
theorem postMvC_noRet : (postMv (.x 0)).all (moveNoRetB (act vcpC rfC)) = true := by
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
        (iterN (RLx s).step (prologueLines (RLx s).af.saves (RLx s).af.frameSize (RLx s).af.isCaller).length (RLx s).s0)) (w₀X s))
        trM (.run ⟨0, rest2L, mL, w₀X s⟩) ∧
      (∀ x ∈ trM, x = []) ∧ mL (.reg (.x 0)) = 0 := by
  have hR := wfX hS
  obtain ⟨hlat, hq, hA⟩ := q_init_lines hR (abiX hS) (bodyX s)
  have hpe := prologue_evs hR (abiX hS) (probeF_L rfl) hlat
  have hpr0 := linesAt_program hR hlat
  have hnr0 := linesAt_nonRet hR hlat (noRet_prologue _ _ _)
  generalize hP : (prologueLines (RLx s).af.saves (RLx s).af.frameSize (RLx s).af.isCaller).length = n0 at hpe hpr0 hnr0 hq hA ⊢
  have hq0 := hq
  have hA0 := hA
  simp only [MConf.init] at hq0 hA0
  rw [show (RLx s).rf = rfL from rfl, checksRunL.1] at hq0 hA0
  have hnr := moves_noRet (R := RLx s) checksPost.2.2.1
  obtain ⟨n1, hq1, hA1, hp1⟩ := moves_privP hR savesL _ _ _ hq0 hA0
    (fun p hp => hnr p (by simp [hp])) (by simp [savesL, Loc.isSave])
  obtain ⟨m', hst, hm'⟩ := args_stepX (s := s) (spillL.map (fun p => RItem.move p.1 p.2) ++ rest2L) _
    (w₀X s)
  have hq2 := realizes_args hR hq1 hA1 vb0L argsL0.1 hst
  have hA2 := Backend.Proof.aInv_step hR hq1 hA1 hst
  obtain ⟨n2, hq3, hA3, hp2⟩ := moves_privP hR spillL rest2L _ m' hq2 hA2
    (fun p hp => hnr p (by simp [hp])) (by simp [spillL, Loc.isSave])
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

/-! ## Realized segments -/

theorem Realized.of_take {env : Clif.Env} {p : Clif.Program} {Priv : Nat → Prop} {ls : List Lab}
    {k : Nat} {c c' : TState} (h : CallCompose.Realized env p Priv (ls.take k) k c c')
    (hk : k ≤ ls.length) : CallCompose.Realized env p Priv ls k c c' := by
  obtain ⟨-, trS, ψ, hr, hx, hf⟩ := h
  rw [List.take_take, Nat.min_self] at hx hf
  exact ⟨hk, trS, ψ, hr, hx, hf⟩

/-- **A private segment of the single-core path realizes event-free CLIF steps.** -/
theorem realized_privSeg {R : RL} {env : Clif.Env} {p : Clif.Program} {L : List Lab}
    {s0 : ArmState} {c c' : TState} (hev : evTr L = segEvs R.step L.length s0)
    (hpv : ∀ i < L.length, ∀ e ∈ stepEvs (iterN R.step i s0), R.F e.addr)
    (hk : ∀ l ∈ L, ∀ e ∈ l.evs, e.k ≠ .relXW) {trS : List (List (Prog.Ev SKind BVal))}
    (hS : ∀ x ∈ trS, x = []) (hrun : ClifCStepTerm.CRun env p c trS c') :
    CallCompose.Realized env p (PrivA R) L L.length c c' := by
  refine ⟨Nat.le_refl _, trS, id, hrun, ?_, ?_⟩
  · rw [List.take_length]; exact xClosed_labs hk
  · rw [List.take_length]
    exact refines_nilS hS (privW_labs (fun p y hy _ => by rw [hev] at hy; exact privA_segEvs hpv hy) hk)

/-- **The `ldar`'s step realizes the CLIF load**: its one `acqR` event, read as the load's
bytes. -/
theorem realized_ld {R : RL} {env : Clif.Env} {p : Clif.Program} {la : Lab} {L : List Lab}
    {e : Ev} (he : la.evs = [e]) (hk : e.k = .acqR) (hnp : ¬ PrivA R e.addr.toNat) {c c1 : TState}
    (hs : CStep env p c [⟨.scR, .R, e.addr.toNat, e.n, bytesOf e.n e.val⟩] c1) :
    CallCompose.Realized env p (PrivA R) (la :: L) 1 c c1 := by
  have htr : evTr ((la :: L).take 1) = [[e]] := by simp [evTr, he]
  refine ⟨by simp, _, id, .cons hs .nil, ?_, ?_⟩
  · exact xClosed_labs fun l hl e' he' => by
      simp at hl; subst hl; rw [he] at he'; simp at he'; subst he'; rw [hk]; decide
  · rw [htr]
    have hat : ∀ q x, evAt [[(⟨.scR, .R, e.addr.toNat, e.n, bytesOf e.n e.val⟩ :
        Prog.Ev SKind BVal)]] q = some x → q = (0, 0) ∧ x = ⟨.scR, .R, e.addr.toNat, e.n,
          bytesOf e.n e.val⟩ := by
      rintro ⟨j, kk⟩ x hx
      rcases j with _ | j
      · rcases kk with _ | kk
        · simp [evAt] at hx; exact ⟨rfl, hx.symm⟩
        · simp [evAt] at hx
      · simp [evAt] at hx
    have hatT : ∀ q y, evAt (conv [[e]]) q = some y → q = (0, 0) ∧ y = convEv e := by
      rintro ⟨j, kk⟩ y hy
      rcases j with _ | j
      · rcases kk with _ | kk
        · simp [evAt, conv] at hy; exact ⟨rfl, hy.symm⟩
        · simp [evAt, conv] at hy
      · simp [evAt, conv] at hy
    exact {
      ev := fun q x hx => by
        obtain ⟨rfl, rfl⟩ := hat q x hx
        refine ⟨convEv e, by simp [evAt, conv], ?_, ?_, rfl, rfl, rfl⟩
        · show Maps .scR e.k; rw [hk]; exact .inl rfl
        · show e.k.dir = .R; rw [hk]; rfl
      mono := fun q q' hq hq' hlt => by
        obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hq
        obtain ⟨x', hx'⟩ := Option.isSome_iff_exists.mp hq'
        obtain ⟨rfl, -⟩ := hat q x hx
        obtain ⟨rfl, -⟩ := hat q' x' hx'
        exact absurd hlt (Lt.irrefl _)
      shared := fun q x hx _ => by obtain ⟨-, rfl⟩ := hat q x hx; exact hnp
      priv := fun q y hy hW _ => by
        obtain ⟨-, rfl⟩ := hatT q y hy
        simp [convEv, hk, AKind.dir] at hW
      len := fun j hj => by simp at hj; subst hj; simp
      pair := fun j hj h2 => by simp at hj; subst hj; simp at h2
      pair_inv := fun q q' hq _ hpr => by
        obtain ⟨⟨x, hx, hxk⟩, -⟩ := hpr
        obtain ⟨x0, hx0⟩ := Option.isSome_iff_exists.mp hq
        obtain ⟨rfl, -⟩ := hat q x0 hx0
        simp [evAt] at hx
        subst hx
        rw [hk] at hxk
        cases hxk }

/-! ## The linked machine with the return -/

/-- The caller's program. -/
abbrev pC0 : Arm.Program := RC.fb.program RC.base

/-- **A state at the callee's `ret` line.** -/
def IsRetL (x : ArmState) : Prop :=
  ∃ j t, (act vcpL rfL).fa.lines.toList[j]? = some (.ins .ret t) ∧
    Arm.r .PC x = 0x20000#64 + BitVec.ofNat 64 (lineOffset (act vcpL rfL).fa.lines.toList j)

open Classical in
/-- **The linked machine with the return** (module doc): at the callee's `ret` line, its step
goes back to the caller's program. -/
noncomputable def MC2 (x : ArmState) : ArmState :=
  if x.program = pL then (if IsRetL x then set_program (stepL x) pC0 else stepL x) else RC.step x

theorem mc2_caller {x : ArmState} (hx : x.program = pC0) : MC2 x = RC.step x := by
  have : ¬ x.program = pL := by rw [hx]; exact progC_ne
  simp only [MC2, this, ite_false]

theorem mc2_ret {x : ArmState} (hx : x.program = pL) (hr : IsRetL x) :
    MC2 x = set_program (stepL x) pC0 := by
  simp only [MC2, hx, ite_true, hr]

/-- **The caller's state after the callee returned** (as the caller resumes): at the return
address, no error, its `sp`, its addresses as at the call, its program, its x29 (the callee's
epilogue restores it; the caller's `StRel.fp` needs it). -/
def PostA (s y : ArmState) : Prop :=
  Arm.r .PC y = Arm.r .PC s + 4#64 ∧ Arm.r .ERR y = .None ∧ E2E.spv y = E2E.spv s ∧
    (∀ a, RC.F a → y.mem a = s.mem a) ∧ y.program = pC0 ∧ E2E.xreg 29 y = E2E.xreg 29 s

/-- **The callee's return** (`Ret` of `link_compose`): the caller's Arm state after it, the
caller's CLIF state ready to return. -/
def RetL (s : ArmState) (_u : CallCompose.AT) (_c : TState) (v : CallCompose.AT) (d : TState) :
    Prop :=
  PostA s v.1 ∧ ∃ sd, d = .run sd ∧ RetReady fC sd ∧ sd.callers = []

theorem srcStep_next {R : RL} {b k : Nat} {allocs : Array Loc} {its : List RItem}
    {m : Loc → CV} {w : ArmState} {evs : List Ev} {c' : MConf CV ArmState}
    (hf : ∀ vb i, R.vc.blocks[b]? = some vb → vb.insts[k]? = some i → i.isCtl = false)
    (h : SrcStep R (OpC b k allocs its m w) evs c') : ∃ m' w', c' = .run ⟨b, its, m', w'⟩ := by
  cases h with
  | op hvb hi hops hevs hfoot hst =>
    cases hst with
    | op hvb' hi' hops' hsz hsem hlen hho hcl hn =>
      rw [hvb] at hvb'; cases hvb'; rw [hi] at hi'; cases hi'
      obtain rfl := csem_ctl (hf _ _ hvb hi) (R.sem_csem hsem)
      cases hn with
      | next _ => exact ⟨_, _, rfl⟩

section callee2
variable {s : ArmState} {m : Loc → CV}

theorem mc2_callee (hS : StRel RC s m w₀C) {x : ArmState} (hx : x.program = pL)
    (hn : AtNonRet (RLx s) x) (M : Memory) : MC2 (setMem M x) = (RLx s).step (setMem M x) := by
  have hnr : ¬ IsRetL (setMem M x) := by
    rintro ⟨j, t, hj, hpc⟩
    obtain ⟨j', x', t', hj', hx', -, hpc'⟩ := hn
    rw [ArmFoot.r_setMem] at hpc
    have := RL.pcOf_inj (R := RLx s) (wfX hS) hj hj' (hpc.symm.trans hpc')
    subst this
    have hj2 : (RLx s).fa.lines.toList[j]? = some (.ins .ret t) := hj
    rw [hj2] at hj'; cases hj'; exact hx' rfl
  have hp : (setMem M x).program = pL := by rw [setMem_program]; exact hx
  simp only [MC2, hp, ite_true, hnr, ite_false]; rfl

/-- **The `ldar`'s configuration has a step of the allocated code** (layers 2–4a's progress,
`isel_alloc_refinesP`, on the event-free run from the entry: the CLIF thread at `csL` has not
stepped, since its step has an event, and does not stop there). -/
theorem mstep_ldar (hS : StRel RC s m w₀C) (hx0 : regVal s (.x 0) = 0) (env : Clif.Env)
    {mL : Loc → CV} {trM : List (List Ev)}
    (hrun : SRun (SrcStep (RLx s)) (MConf.init (RLx s).rf (locVal (RLx s).fr
        (iterN (RLx s).step (prologueLines (RLx s).af.saves (RLx s).af.frameSize (RLx s).af.isCaller).length (RLx s).s0)) (w₀X s))
        trM (.run ⟨0, rest2L, mL, w₀X s⟩))
    (hnil : ∀ x ∈ trM, x = []) :
    ∃ c', MStep (RLx s).vc (RLx s).sem ckeep (RLx s).rf (.run ⟨0, rest2L, mL, w₀X s⟩) c' := by
  obtain ⟨hlow, hthr, hext, hind, hv, -, hout, hprep, -⟩ := checksL
  obtain ⟨ctx, st0, R, gn, bl, A, H, hbl⟩ := driverHyp_of (Γ := ΓX s) (fctx := (RLx s).ctx)
    (X := (RLx s).X) (c := E2E.spv (w₀X s)) (env := env) (p := pCL) hlow hthr
    (List.isEmpty_iff.mp hext) (List.isEmpty_iff.mp hind) hv cfgL hout rfl (fun _ _ h => by cases h)
  obtain ⟨-, -, hpar, hsig, hlocs, -, -, -⟩ := shapeL
  have hsem : (RLx s).sem = csem (RLx s).F (RLx s).ctx (RLx s).X :=
    ThreadCompose.csemV_none _ _ _
  have hM := mtrun_of_srun hrun
  rw [hsem] at hM
  obtain ⟨mI, trS, t, ψ, -, hcr, href, hend⟩ := ThreadCompose.isel_alloc_refinesP (cs := csL) H hbl
    (E2E.memRelOk_relW (ΓX s) fL _) (IselRefines.Witness.relW_wf (alignX hS))
    VCodeThread.Witness.X0_tls (memRefines_csem (RLx s).F (RLx s).ctx _ rfl (fun _ _ h => by cases h))
    (E2E.mrStable_relW (ΓX s) fL _)
    (fun off h => by have := List.all_eq_true.mp hlocs _ h; simp at this) hprep allocL b0L
    rfl rfl rfl rfl rfl regsL_eq hpar hsig (fun _ => 0) (relX hS) (argsAtX hx0) hM
  rcases hend with ⟨-, cM', hst⟩ | hstop
  · exact ⟨cM', by rw [hsem]; exact hst⟩
  · exfalso
    cases hcr with
    | nil => exact notStop_csL env pCL hstop
    | @cons _ _ _ x _ hs1 _ =>
      have hm := hs1.1.1
      rw [shapeL1, List.mem_singleton] at hm
      obtain ⟨e, rfl⟩ : ∃ e, x = [e] := by
        rcases x with _ | ⟨e, _ | ⟨e', r⟩⟩ <;> simp at hm
        exact ⟨e, rfl⟩
      obtain ⟨y, hy, -⟩ := href.ev (0, 0) e (by simp [evAt])
      rw [CallSeg.evAt_nilS (fun x hx => by
        simp only [PrepThread.conv, List.mem_map] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        rw [hnil y (List.mem_of_mem_take hy)]; rfl)] at hy
      cases hy

/-- **The callee after its `ldar`**: the moves, the restores and the return, every step private,
no store exclusive, on its program, at a line other than `ret` but the last, which is at the
`ret`; after it the caller's state as it resumes (`PostA`). From `QA` (the restores emit no
code: they continue a return tail, `moves_privQA`). -/
theorem calleePost (hS : StRel RC s m w₀C) {x : ArmState} {m2 : Loc → CV} {w2 : ArmState}
    (hqa : QA (RLx s) x (.run ⟨0, (postMv (.x 1)).map (fun p => RItem.move p.1 p.2) ++
      [.op 2 #[.reg (.x 0)]], m2, w2⟩)) :
    ∃ nP, 0 < nP ∧
      (∀ i < nP, ((∀ e ∈ stepEvs (iterN (RLx s).step i x), (RLx s).F e.addr) ∧
        NoStx (iterN (RLx s).step i x)) ∧ (iterN (RLx s).step i x).program = pL) ∧
      (∀ i, i + 1 < nP → AtNonRet (RLx s) (iterN (RLx s).step i x)) ∧
      IsRetL (iterN (RLx s).step (nP - 1) x) ∧
      PostA s (set_program (iterN (RLx s).step nP x) pC0) := by
  have hR := wfX hS
  obtain ⟨n1, hqa1, hp1⟩ := moves_privQA hR (postMv (.x 1)) [.op 2 #[.reg (.x 0)]] x m2 hqa
    (fun p hp => moves_noRet (R := RLx s) checksPost.2.2.1 p (by simp [hp]))
  obtain ⟨mt1, hq1⟩ := qa_q hqa1
  have hvb : (RLx s).vc.blocks[0]? = some vcpL.blocks[0]! := vb0L
  obtain ⟨n2, hp2, hpc2, herr2, hsp2, hmem2, hprog2, hx29, hnr2, hn2, j, t, hj, hpcj⟩ :=
    rets_privP hR (abiX hS) hq1 hvb instL2
  have hstr := q_stRel hq1
  have hshift : ∀ i, iterN (RLx s).step i (iterN (RLx s).step n1 x) =
      iterN (RLx s).step (n1 + i) x := fun i => (iterN_add _ _ _ _).symm
  refine ⟨n1 + n2, by omega, fun i hi => ?_, fun i hi => ?_, ?_, ?_⟩
  · by_cases h : i < n1
    · exact ⟨(hp1 i h).1, (hp1 i h).2.1⟩
    · have := hp2 (i - n1) (by omega)
      rw [hshift, show n1 + (i - n1) = i by omega] at this
      exact ⟨this.1, this.2.1⟩
  · by_cases h : i < n1
    · exact (hp1 i h).2.2
    · have := hnr2 (i - n1) (by omega)
      rw [hshift, show n1 + (i - n1) = i by omega] at this
      exact this
  · rw [show n1 + n2 - 1 = n1 + (n2 - 1) by omega, ← hshift]
    exact ⟨j, t, hj, hpcj⟩
  · rw [← hshift]
    refine ⟨?_, ?_, ?_, fun a ha => ?_, rfl, ?_⟩
    · rw [E2E.r_set_program, hpc2]
    · rw [E2E.r_set_program, herr2]
    · show Arm.r (.GPR 31#5) (set_program _ _) = Arm.r (.GPR 31#5) s
      rw [E2E.r_set_program]
      show E2E.spv _ = _
      rw [hsp2]
      show Arm.r (.GPR 31#5) (enterL s) = _
      rw [r_enterL (by simp) (by simp)]
    · rw [E2E.mem_set_program, hmem2, hstr.gkeep a ha]
      show (enterL s).mem a = _
      rw [mem_enterL]
    · show Arm.r (.GPR 29#5) (set_program _ _) = Arm.r (.GPR 29#5) s
      rw [E2E.r_set_program]
      show E2E.xreg 29 _ = _
      rw [hx29]
      show Arm.r (.GPR 29#5) (enterL s) = _
      rw [r_enterL (by simp) (by simp)]

/-- **A step of private events realizes an event-free CLIF step.** -/
theorem realized_privStep {R : RL} {env : Clif.Env} {p : Clif.Program} {l : Lab} {L : List Lab}
    {c c' : TState} (hpv : ∀ e ∈ l.evs, R.F e.addr) (hk : ∀ e ∈ l.evs, e.k ≠ .relXW)
    (hs : CStep env p c [] c') : CallCompose.Realized env p (PrivA R) (l :: L) 1 c c' := by
  have htr : evTr ((l :: L).take 1) = [l.evs] := by simp [evTr]
  refine ⟨by simp, [[]], id, .cons hs .nil, ?_, ?_⟩
  · exact xClosed_labs fun l' hl' e he => by simp at hl'; subst hl'; exact hk e he
  · rw [htr]
    exact refines_nilS (by simp) fun q y hy _ => by
      obtain ⟨x, hx, hyx⟩ := mem_of_evAt hy
      simp only [List.mem_singleton] at hx; subst hx
      exact ⟨privA_addr.2 (hpv y hyx), hk y hyx⟩

/-- **The callee's contract with its return** (module doc): every precise run of the linked
machine from the callee's ABI entry (after the caller's `bl` from `s`) realizes, through the
CLIF `atomic_load` reading the `ldar`'s bytes, a prefix that is the whole run or ends at the
callee's return (`RetL`: the caller's Arm state resumable, its CLIF state ready to return). -/
theorem funReal_ld (env : Clif.Env) (hS : StRel RC s m w₀C) (hx0 : regVal s (.x 0) = 0)
    (mon : Mon) :
    CallCompose.FunReal env pCL (PrivA (RLx s)) MC2 (OkPriv (RLx s)) (RetL s) (fun _ _ => False)
      (enterL s, mon) (.run (ClifLift.pushC extC csL)) := by
  intro ls t' hr
  have hR := wfX hS
  obtain ⟨n0, mL, trM, hpath, hqa, hAa, hrun, hnil, hmL0⟩ := calleePath hS hx0
  have hagA : ∀ i < n0, MC2 (iterN (RLx s).step i (RLx s).s0) =
      (RLx s).step (iterN (RLx s).step i (RLx s).s0) := fun i hi => by
    have h := mc2_callee hS (hpath i hi).2.1 (hpath i hi).2.2 (iterN (RLx s).step i (RLx s).s0).mem
    rwa [setMem_self] at h
  by_cases hlen : ls.length ≤ n0
  · obtain ⟨-, hev, hk⟩ := prun_privF hr fun i hi =>
      ⟨(hpath i (by omega)).1.1, (hpath i (by omega)).1.2, hagA i (by omega)⟩
    exact ⟨ls.length, _, realized_privSeg hev (fun i hi => (hpath i (by omega)).1.1)
      (fun l hl => (hk l hl).2) (trS := []) (by simp) .nil, .inl rfl⟩
  obtain ⟨va, hva, hrest⟩ := CallCompose.take_prun hr n0
  have hlt : (ls.take n0).length = n0 := by simp; omega
  obtain ⟨hva1, hevA, hkA⟩ := prun_privF hva fun i hi =>
    ⟨(hpath i (by omega)).1.1, (hpath i (by omega)).1.2, hagA i (by omega)⟩
  have hRA0 := realized_privSeg (env := env) (p := pCL) (c := .run (ClifLift.pushC extC csL)) hevA
    (fun i hi => (hpath i (by omega)).1.1) (fun l hl => (hkA l hl).2) (trS := []) (by simp) .nil
  rw [hlt] at hva1 hRA0
  have hRA := Realized.of_take hRA0 (by omega)
  obtain ⟨la, ls2, hdrop⟩ : ∃ la ls2, ls.drop n0 = la :: ls2 := by
    cases h : ls.drop n0 with
    | nil => simp at h; omega
    | cons la ls2 => exact ⟨la, ls2, rfl⟩
  rw [hdrop] at hrest
  obtain ⟨va1, va2⟩ := va
  simp only at hva1
  subst hva1
  -- the `ldar`
  obtain ⟨jl, hjl, hpcl, hstrl⟩ := q_head hqa rfl head_ldarL
  have hnra : AtNonRet (RLx s) (iterN (RLx s).step n0 (RLx s).s0) :=
    ⟨jl, .ldar 64 (.x 1) (.x 0), some .heapOob, hjl, (fun h => by cases h), rfl, hpcl⟩
  cases hrest with
  | @cons _ ta _ _ _ hsa hpa hoa hr2 =>
  have hsaR := tstep_transfer (fun M => mc2_callee hS hstrl.prog hnra M) hsa
  obtain ⟨hnsa, -⟩ := ldar_evs_line hR hjl rfl hstrl.prog hpcl hstrl.err (p := 1) (q := 0)
    (by omega) (by omega) (fun _ => rfl) (iterN (RLx s).step n0 (RLx s).s0).mem
  have hxa : la.xfail = false := by
    cases hsa with
    | exec => rfl
    | xfail hc => exact absurd hc (hnsa _ _ _)
  obtain ⟨M, hM⟩ : ∃ M, la.evs = stepEvs (setMem M (iterN (RLx s).step n0 (RLx s).s0)) := by
    rcases hpa with h | h
    · rw [hxa] at h; cases h
    · exact h
  obtain ⟨-, e, hse, hek, hen, hea⟩ := ldar_evs_line hR hjl rfl hstrl.prog hpcl hstrl.err (p := 1)
    (q := 0) (by omega) (by omega) (fun _ => rfl) M
  rw [hse] at hM
  have hs3 := hstrl.store (.reg (.x 0)) (fun r h => by cases h; rfl) trivial
  have hea0 : e.addr = 0 := hea.trans (regVal_x0 hs3 hmL0)
  have hnp : ¬ PrivA (RLx s) e.addr.toNat := by
    rw [hea0]
    intro h
    have := xF_ge hS (privA_addr.1 h)
    simp at this
  -- its source step and the related states after it
  obtain ⟨cM, hms⟩ := mstep_ldar hS hx0 env hrun hnil
  obtain ⟨evs0, hsrc⟩ := srcStep_of_mstep_eq (coveredX hS hx0) VCodeThread.Witness.X0_tls hqa hms
  obtain ⟨fl, hil, hfo⟩ := instL1
  have hform : ∀ vb i, (RLx s).vc.blocks[0]? = some vb → vb.insts[1]? = some i →
      OneEvForm (RLx s).F (RLx s).ctx i := by
    intro vb i hvb hi
    have h0 : (RLx s).vc.blocks[0]? = some vcpL.blocks[0]! := vb0L
    rw [h0] at hvb; cases hvb; rw [hil] at hi; cases hi
    exact ldar_form hfo
  rw [checksPost.1] at hqa hAa hsrc
  obtain ⟨c', t1, φ, hsc, hp1, ht1, hqa1, -⟩ := oneEv_op1 hR hqa hAa hsrc hform
    (.cons hsaR hpa trivial .nil)
  obtain rfl := PRun.det hp1 (.cons hsaR hpa trivial .nil)
  obtain ⟨m2, w2, rfl⟩ := srcStep_next (fun vb i hvb hi => (hform vb i hvb hi).ctl) hsc
  obtain ⟨nP, hnP, hpP, hnrP, hretP, hpostP⟩ := calleePost hS hqa1
  -- the CLIF load and return
  obtain ⟨s1, d, hcl1, hcl2, hdr, hdc⟩ := cstep_ld env (bytesOf e.n e.val) (by simp [bytesOf, hen])
    (fun x hx => by simp only [bytesOf, List.mem_map] at hx; obtain ⟨_, _, rfl⟩ := hx; rfl)
  have hev : (⟨.scR, .R, e.addr.toNat, e.n, bytesOf e.n e.val⟩ : Prog.Ev SKind BVal) =
      ⟨.scR, .R, 0, 8, bytesOf e.n e.val⟩ := by
    simp only [Prog.Ev.mk.injEq, true_and, hea0, hen]; simp
  have hRL := realized_ld (L := ls2) (R := RLx s) hM hek hnp (hev ▸ hcl1)
  have hRAL := hRA.trans (by rw [hdrop]; exact hRL)
  -- the run after the `ldar`
  have hagP : ∀ i, i + 1 < nP → MC2 (iterN (RLx s).step i t1.1) = (RLx s).step (iterN (RLx s).step i t1.1) :=
    fun i hi => by
      have h := mc2_callee hS (hpP i (by omega)).2 (hnrP i hi) (iterN (RLx s).step i t1.1).mem
      rwa [setMem_self] at h
  have hdrop1 : ls.drop (n0 + 1) = ls2 := by rw [← List.drop_drop, hdrop]; rfl
  by_cases hlen2 : ls2.length < nP
  · obtain ⟨-, hev2, hk2⟩ := prun_privF hr2 fun i hi =>
      ⟨(hpP i (by omega)).1.1, (hpP i (by omega)).1.2, hagP i (by omega)⟩
    have hR2 := realized_privSeg (env := env) (p := pCL) (c := .run (ClifLift.pushC extC s1)) hev2
      (fun i hi => (hpP i (by omega)).1.1) (fun l hl => (hk2 l hl).2) (trS := []) (by simp) .nil
    refine ⟨n0 + 1 + ls2.length, _, hRAL.trans (by rw [hdrop1]; exact hR2), .inl ?_⟩
    have := congrArg List.length hdrop
    simp at this; omega
  obtain ⟨v3, hv3, hrest3⟩ := CallCompose.take_prun hr2 (nP - 1)
  have hlt3 : (ls2.take (nP - 1)).length = nP - 1 := by simp; omega
  obtain ⟨hv31, hev3, hk3⟩ := prun_privF hv3 fun i hi =>
    ⟨(hpP i (by omega)).1.1, (hpP i (by omega)).1.2, hagP i (by omega)⟩
  have hR30 := realized_privSeg (env := env) (p := pCL) (c := .run (ClifLift.pushC extC s1)) hev3
    (fun i hi => (hpP i (by omega)).1.1) (fun l hl => (hk3 l hl).2) (trS := []) (by simp) .nil
  rw [hlt3] at hv31 hR30
  have hR3 := Realized.of_take hR30 (by omega)
  obtain ⟨lr, ls3, hdrop3⟩ : ∃ lr ls3, ls2.drop (nP - 1) = lr :: ls3 := by
    cases h : ls2.drop (nP - 1) with
    | nil => simp at h; omega
    | cons lr ls3 => exact ⟨lr, ls3, rfl⟩
  rw [hdrop3] at hrest3
  obtain ⟨v31, v32⟩ := v3
  simp only at hv31
  subst hv31
  cases hrest3 with
  | @cons _ tr _ _ _ hsr hpr hor _ =>
  obtain ⟨htr1, hlr, -, hkr⟩ := tstep_priv1 hsr hpr hor (hpP (nP - 1) (by omega)).1.1
    (hpP (nP - 1) (by omega)).1.2
  have hRr : CallCompose.Realized env pCL (PrivA (RLx s)) (lr :: ls3) 1
      (.run (ClifLift.pushC extC s1)) (.run d) :=
    realized_privStep (fun e he => by rw [hlr] at he; exact (hpP (nP - 1) (by omega)).1.1 e he)
      hkr hcl2
  have hR3r := hR3.trans (by rw [hdrop3]; exact hRr)
  rw [show nP - 1 + 1 = nP by omega] at hR3r
  refine ⟨n0 + 1 + nP, .run d, hRAL.trans (by rw [hdrop1]; exact hR3r), .inr (.inr ⟨tr, ?_, ?_,
    d, rfl, hdr, hdc⟩)⟩
  · have e1 : ls.take (n0 + 1 + nP) = ls.take n0 ++ (la :: (ls2.take (nP - 1) ++ [lr])) := by
      have h2 : ls2.take nP = ls2.take (nP - 1) ++ [lr] := by
        rw [show nP = (nP - 1) + 1 by omega, List.take_add, hdrop3]; simp
      rw [List.take_add, hdrop1, h2, List.take_add, hdrop]; simp
    rw [e1]
    exact hva.append (.cons hsa hpa hoa (hv3.append (.cons hsr hpr hor .nil)))
  · rw [htr1, mc2_ret (hpP (nP - 1) (by omega)).2 hretP]
    have : stepL (iterN (RLx s).step (nP - 1) t1.1) = iterN (RLx s).step nP t1.1 := by
      rw [show nP = (nP - 1) + 1 by omega, iterN_one_succ]; rfl
    rw [this]
    exact hpostP

end callee2

end Concurrency.CallSeg.WitnessC
