import FV.Concurrency.CallLoadFull
import FV.Concurrency.CallResumeQ

/-!
# The compiled caller's whole run through the compiled `atomic_load` (T2j follow-up, #473)

`CallLoadFull.funReal_ld` gives the compiled `atomic_load`'s contract up to its return into the
caller (`RetL`). Here the caller resumes and returns too: every precise run of the linked machine
`MC2` from the caller's ABI entry is realized entirely or up to where the CLIF thread has returned
(`funReal_callFull`, `realizes_call_full`), through `CallCompose.link_compose` with the callee's
return (`Ret true = RetL`):

* `resumeQ` (generic): `Q` at the item after a call, from `Q` at the call and the caller's state
  after the callee returned (pc after the `bl`, no error, `sp` kept, its frame/code/kept addresses
  untouched, its program);
* `prefixCQ`: the caller's path to its `bl` with `Q` there (`prefixC` with the relation);
* `callerPost`: the caller's moves, restores, epilogue and `ret` after the return, every step
  private, no store exclusive, on its program;
* the CLIF side: the call (`cstepC`), the callee's load and return (`funReal_ld`), the caller's
  `return` (`cstep_retC`).

Checks by `native_decide` (witness only).
-/

namespace Concurrency.CallSeg

open Arm ArmFoot ArmThread Prog ClifThread ProgE2E Backend Backend.Proof VCodeThread PrepThread
  AllocThread ThreadRefine ArmAllocThread E2E ArmInstFoot CallThread

/-- **A private segment of the single-core path of `R` realizes event-free CLIF steps** for a
larger private set (`realized_privSeg` with `PrivA R ⊆ Priv`). -/
theorem realized_privSegS {R : RL} {Priv : Nat → Prop} (hsub : ∀ a, PrivA R a → Priv a)
    {env : Clif.Env} {p : Clif.Program} {L : List Lab} {s0 : ArmState} {c c' : TState}
    (hev : evTr L = segEvs R.step L.length s0)
    (hpv : ∀ i < L.length, ∀ e ∈ stepEvs (iterN R.step i s0), R.F e.addr)
    (hk : ∀ l ∈ L, ∀ e ∈ l.evs, e.k ≠ .relXW) {trS : List (List (Prog.Ev SKind BVal))}
    (hS : ∀ x ∈ trS, x = []) (hrun : ClifCStepTerm.CRun env p c trS c') :
    CallCompose.Realized env p Priv L L.length c c' := by
  refine ⟨Nat.le_refl _, trS, id, hrun, ?_, ?_⟩
  · rw [List.take_length]; exact WitnessC.xClosed_labs hk
  · rw [List.take_length]
    exact refines_nilS hS
      (privW_labs (fun q y hy _ => by rw [hev] at hy; exact hsub _ (privA_segEvs hpv hy)) hk)

end Concurrency.CallSeg

namespace Concurrency.CallSeg.WitnessC

open Arm ArmFoot ArmThread Prog ClifThread ProgE2E Backend Backend.Proof Backend.Proof.Driver
  VCodeThread PrepThread AllocThread ThreadRefine ArmAllocThread E2E ArmInstFoot Code
  RealizeCompiled RealizeCompiled.Witness RealizeCompiled.WitnessL CallThread
open ArmAllocThread.Witness (act entryAt codeMem)

/-! ## Checks -/

/-- The caller's item 1 is a call (as a check). -/
def callB : Bool :=
  match (vcpC.blocks[0]!).insts[1]? with
  | some (MInst.call _) => true
  | _ => false

theorem callC1 : ∃ info, (vcpC.blocks[0]!).insts[1]? = some (.call info) := by
  have h : callB = true := by native_decide
  unfold callB at h
  revert h
  generalize (vcpC.blocks[0]!).insts[1]? = oi
  intro h
  split at h
  · exact ⟨_, rfl⟩
  · cases h

/-! ## The caller's path to the `bl`, with `Q` -/

/-- **The caller's path to its `bl` with the simulation relation there** (`prefixC`). -/
theorem prefixCQ : ∃ (n0 : Nat) (m : Loc → CV),
    (∀ i < n0, ((∀ e ∈ stepEvs (iterN RC.step i RC.s0), RC.F e.addr) ∧
      NoStx (iterN RC.step i RC.s0)) ∧ (iterN RC.step i RC.s0).program = RC.fb.program RC.base) ∧
    Q RC (iterN RC.step n0 RC.s0) (.run ⟨0, restC, m, w₀C⟩) ∧
    regVal (iterN RC.step n0 RC.s0) (.x 0) = 0 := by
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
  obtain ⟨m', hst, hm'⟩ := args_stepC (spillL.map (fun p => RItem.move p.1 p.2) ++ restC) _ w₀C
  have hq2 := realizes_args wfRC hq1 hA1 vb0C argsC0.1 hst
  have hA2 := Backend.Proof.aInv_step wfRC hq1 hA1 hst
  obtain ⟨n2, hq3, -, hp2⟩ := moves_privA wfRC spillL restC _ m' hq2 hA2 (by simp [spillL, Loc.isSave])
  have hstr := q_stRel hq3
  rw [← iterN_add, ← iterN_add, ← Nat.add_assoc] at hq3 hstr
  rw [← iterN_add] at hp2
  refine ⟨n0 + n1 + n2, _, fun i hi => ?_, hq3, ?_⟩
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

/-- The length of the caller's path to its `bl` (`prefixCQ`). -/
noncomputable def n0F : Nat := Classical.choose prefixCQ

/-- The caller's state at its `bl` (`prefixCQ`). -/
noncomputable def sBF : ArmState := iterN RC.step n0F RC.s0

/-- **The callee's activation in the thread of `funReal_callFull`** (entered by the caller's
`bl` at `sBF`). -/
noncomputable def RLF : RL := RLx sBF

theorem prefixF : ∃ m : Loc → CV,
    (∀ i < n0F, ((∀ e ∈ stepEvs (iterN RC.step i RC.s0), RC.F e.addr) ∧
      NoStx (iterN RC.step i RC.s0)) ∧ (iterN RC.step i RC.s0).program = RC.fb.program RC.base) ∧
    Q RC sBF (.run ⟨0, restC, m, w₀C⟩) ∧ regVal sBF (.x 0) = 0 :=
  Classical.choose_spec prefixCQ

/-! ## The caller after the callee returned -/

/-- **The caller after the callee's return** (module doc): from a state as the callee returns
(`PostA`), its moves (the result to its slot, the restores, the result back to x0), its epilogue
and `ret`: every step private, no store exclusive, on its program. -/
theorem callerPost {y : ArmState} (hy : PostA sBF y) :
    ∃ nP, ∀ i < nP, ((∀ e ∈ stepEvs (iterN RC.step i y), RC.F e.addr) ∧
      NoStx (iterN RC.step i y)) ∧ (iterN RC.step i y).program = pC0 := by
  obtain ⟨m, -, hq, -⟩ := prefixF
  obtain ⟨hpc, herr, hsp, hmem, hprog, hfp⟩ := hy
  obtain ⟨info, hinfo⟩ := callC1
  have hstr := q_stRel hq
  rw [checksPost.2.1] at hq
  have hq1 := resumeQ wfRC hq vb0C hinfo hpc herr hsp hmem (hprog.trans hstr.prog.symm) hfp
  have hA1 : AInv RC (.run ⟨0, (postMv (.x 0)).map (fun p => RItem.move p.1 p.2) ++
      [.op 2 #[.reg (.x 0)]], locVal RC.fr y, y⟩) := by
    intro _ ⟨a, ha⟩
    simp [postMv, savesL] at ha
  obtain ⟨n1, hqa2, hp1⟩ := moves_privQA wfRC (postMv (.x 0)) _ _ _ (.inl ⟨hq1, hA1⟩)
    (moves_noRet (R := RC) postMvC_noRet)
  obtain ⟨mt2, hq2⟩ := qa_q hqa2
  obtain ⟨n2, hp2, -⟩ := rets_privP wfRC abiRC hq2 vb0C instC2
  refine ⟨n1 + n2, fun i hi => ?_⟩
  by_cases h : i < n1
  · exact ⟨(hp1 i h).1, (hp1 i h).2.1⟩
  · have := hp2 (i - n1) (by omega)
    rw [← iterN_add, show n1 + (i - n1) = i by omega] at this
    exact ⟨this.1, this.2.1⟩

/-! ## The whole run -/

/-- **The end condition of the whole run**: the CLIF thread has returned. -/
def Returned (_P : List Lab) (d : TState) : Prop := ∃ v, d = .ret v

/-- **The compiled caller calling the compiled `atomic_load`, its whole run** (module doc): every
precise run of the linked machine with the return (`MC2`) from the caller's ABI entry (open
monitor), reading the thread's own bytes at the private addresses, realizes on a prefix a run of
the CLIF program `pCL` from the caller's entry state: the whole run, or up to where the CLIF thread
has returned (after the callee's `atomic_load` and return, the caller's `return`). -/
theorem funReal_callFull (env : Clif.Env) :
    CallCompose.FunReal env pCL (PrivA RLF) MC2 (OkPriv RLF) (fun _ _ _ _ => False) Returned
      (RC.s0, none) (.run csC) := by
  obtain ⟨m, hpath, hqB, hx0⟩ := prefixF
  have hstr := q_stRel hqB
  obtain ⟨j, hj, hpc, -⟩ := q_head hqB rfl head_blC
  have hsub : ∀ a, PrivA RC a → PrivA RLF a := fun a h => Or.inr h
  have hmono : ∀ {x : ArmState × Mon} {L : List Lab} {v : ArmState × Mon},
      PRun Policy.arm MC2 (OkPriv RLF) x L v → PRun Policy.arm MC2 (OkPriv RC) x L v :=
    fun h => PRun.mono (fun _ _ h e he hd hp => h e he hd (hsub _ hp)) h
  have hagC : ∀ x : ArmState, x.program = RC.fb.program RC.base → MC2 x = RC.step x :=
    fun x hx => mc2_caller hx
  refine CallCompose.link_compose (G := Bool) (Ext := fun g => g = true)
    (Ent := fun g u c => match g with
      | true => u.1 = enterL sBF ∧ c = .run (ClifLift.pushC extC csL)
      | false => u = (RC.s0, none) ∧ c = .run csC)
    (Ret := fun g => match g with
      | true => RetL sBF
      | false => fun _ _ _ _ => False) (E := Returned)
    (Inv := fun _ _ _ x d => (x = (RC.s0, none) ∧ d = .run csC) ∨
      (PostA sBF x.1 ∧ ∃ sd, d = .run sd ∧ RetReady fC sd ∧ sd.callers = []))
    (fun _ _ _ h => h) (fun g u c hg he => ?_) (fun g hg => ?_) (fun h u c hh he => ?_) false
    (RC.s0, none) (.run csC) ⟨rfl, rfl⟩
  · cases g
    · exact .inl he
    · exact absurd rfl hg
  · cases g
    case true => exact absurd rfl hg
    rintro u c x d (⟨rfl, rfl⟩ | ⟨hpost, sd, rfl, hsd, hsc⟩) ls t' hr
    · -- the caller's path to the `bl`, then the call
      have hagree : ∀ i < n0F, MC2 (iterN RC.step i RC.s0) = RC.step (iterN RC.step i RC.s0) :=
        fun i hi => hagC _ (hpath i hi).2
      by_cases hlen : ls.length ≤ n0F
      · obtain ⟨-, hev, hk⟩ := prun_privF (hmono hr) fun i hi =>
          ⟨(hpath i (by omega)).1.1, (hpath i (by omega)).1.2, hagree i (by omega)⟩
        exact ⟨ls.length, _, realized_privSegS hsub hev (fun i hi => (hpath i (by omega)).1.1)
          (fun l hl => (hk l hl).2) (trS := []) (by simp) .nil, .inl rfl⟩
      obtain ⟨v, hv, hrest⟩ := CallCompose.take_prun hr n0F
      have hlt : (ls.take n0F).length = n0F := by simp; omega
      obtain ⟨hv1, hev, hk⟩ := prun_privF (hmono hv) fun i hi =>
        ⟨(hpath i (by omega)).1.1, (hpath i (by omega)).1.2, hagree i (by omega)⟩
      rw [hlt] at hv1 hev
      obtain ⟨l, rest, hdrop⟩ : ∃ l rest, ls.drop n0F = l :: rest := by
        cases h : ls.drop n0F with
        | nil => simp at h; omega
        | cons l rest => exact ⟨l, rest, rfl⟩
      rw [hdrop] at hrest
      obtain ⟨v1, v2⟩ := v
      simp only at hv1
      subst hv1
      cases hrest with
      | cons hs hp ho _ =>
        obtain ⟨hst, hse, hcls⟩ := step_bl wfRC hj hstr.prog hpc
        obtain ⟨rfl, ht1⟩ := tstep_plain_nil hs hp hse hcls
        have hMC : MC2 (iterN RC.step n0F RC.s0) = enterL sBF := by
          rw [show iterN RC.step n0F RC.s0 = sBF from rfl, hagC _ hstr.prog, hst]
          show (if some "ld" = some "ld" then enterL sBF else sBF) = _
          simp
        rw [hMC] at ht1
        subst ht1
        have hW : PrivW (PrivA RLF) (segEvs RC.step n0F RC.s0) := fun p y hy hd =>
          (fun h => ⟨hsub _ h.1, h.2⟩) (privW_segEvs (fun i hi => (hpath i hi).1.1)
            (fun i hi => stepEvs_noRelXW (hpath i hi).1.2) p y hy hd)
        have htake : ls.take (n0F + 1) = ls.take n0F ++ [⟨[], false⟩] := by
          rw [List.take_add, hdrop]; rfl
        have hev1 : evTr (ls.take (n0F + 1)) = segEvs RC.step n0F RC.s0 ++ [[]] := by
          rw [htake, evTr_append, hev]; rfl
        refine ⟨n0F + 1, .run (ClifLift.pushC extC csL), ⟨by omega, [[]], id,
          .cons (cstepC env) .nil, ?_, ?_⟩, .inr (.inr (.inr ⟨by omega, (enterL sBF, v2), true, ?_,
          ⟨rfl, rfl⟩, fun z d'' h => .inr ⟨h.1, h.2⟩⟩))⟩
        · rw [htake]
          refine xClosed_labs fun l' hl' => ?_
          rcases List.mem_append.mp hl' with hl' | hl'
          · exact (hk l' hl').2
          · simp only [List.mem_singleton] at hl'
            subst hl'
            intro e he
            exact absurd he List.not_mem_nil
        · rw [hev1]
          exact refines_nilS (fun x hx => by simp at hx; exact hx) (privW_snoc_nil hW)
        · rw [htake]
          exact PRun.append hv (.cons hs hp ho .nil)
    · -- the caller resumed: its moves, epilogue and `ret`, then its CLIF `return`
      obtain ⟨x1, x2⟩ := x
      obtain ⟨nP, hpP⟩ := callerPost hpost
      have hagP : ∀ i < nP, MC2 (iterN RC.step i x1) = RC.step (iterN RC.step i x1) :=
        fun i hi => hagC _ (hpP i hi).2
      by_cases hlen : ls.length ≤ nP
      · obtain ⟨-, hev, hk⟩ := prun_privF (hmono hr) fun i hi =>
          ⟨(hpP i (by omega)).1.1, (hpP i (by omega)).1.2, hagP i (by omega)⟩
        exact ⟨ls.length, _, realized_privSegS hsub hev (fun i hi => (hpP i (by omega)).1.1)
          (fun l hl => (hk l hl).2) (trS := []) (by simp) .nil, .inl rfl⟩
      obtain ⟨v, hv, -⟩ := CallCompose.take_prun hr nP
      have hlt : (ls.take nP).length = nP := by simp; omega
      obtain ⟨-, hev, hk⟩ := prun_privF (hmono hv) fun i hi =>
        ⟨(hpP i (by omega)).1.1, (hpP i (by omega)).1.2, hagP i (by omega)⟩
      obtain ⟨vals, hret⟩ := cstep_retC env hsd hsc
      have hR := realized_privSegS (env := env) (p := pCL) hsub hev
        (fun i hi => (hpP i (by rw [hlt] at hi; exact hi)).1.1) (fun l hl => (hk l hl).2)
        (trS := [[]]) (by simp) (.cons hret .nil)
      rw [hlt] at hR
      exact ⟨nP, _, Realized.of_take hR (by omega), .inr (.inl ⟨vals, rfl⟩)⟩
  · subst hh
    obtain ⟨⟨u1, u2⟩, rfl⟩ : ∃ v : ArmState × Mon, v = u := ⟨u, rfl⟩
    obtain ⟨hu, rfl⟩ := he
    simp only at hu
    subst hu
    intro ls t' hr
    obtain ⟨k, c', hR, hend⟩ := funReal_ld env hstr hx0 u2 ls t' hr
    exact ⟨k, c', hR, hend.imp_right (Or.imp_left False.elim)⟩

/-- **The thread through the call and back realizes the CLIF program** (`realizes_linked` with
`funReal_callFull`): every execution of the realized prefix of a precise run of the linked machine
with the return from the caller's ABI entry (as `realizes_linked`'s premises) is realized by a
CLIF thread of `pCL` from the caller's entry state. -/
theorem realizes_call_full (env : Clif.Env) {ls : List Lab} {t' : CallCompose.AT}
    (hr : PRun Policy.arm MC2 (OkPriv RLF) (RC.s0, none) ls t') :
    ∃ k : Nat → Nat, (∀ i < 1, k i ≤ ls.length) ∧
      ∀ (PA : Traces ProgE2E.AState AKind BVal) (locsA locsC : List (Nat × Nat)) (MA0 MC0 : Bytes)
        (rfA coA rmwA : Rel PEv), PA.n = 1 →
        (∀ i < 1, PA.tr i = conv (evTr (ls.take (k i)))) →
        (PA.exec locsA rfA coA rmwA).Wf →
        (∀ i < 1, ∀ a b, rmwA (.thr i a.1 a.2) (.thr i b.1 b.2) ↔
          MonPair (evTr (ls.take (k i))) a b) →
        locsC <+: locsA →
        (∀ q (h : q < locsA.length), locsC.length ≤ q → ∃ j, j < 1 ∧ PrivA RLF (locsA[q]).1) →
        (∀ q (h : q < locsC.length),
          bytesI.get MA0 (locsC[q]).1 (locsC[q]).2 = bytesI.get MC0 (locsC[q]).1 (locsC[q]).2) →
        (∀ i < 1, ∀ j < 1, j ≠ i → ∀ q x, evAt (PA.tr i) q = some x → x.dir ≠ .F →
          ¬ PrivA RLF x.loc) →
        ∃ (PC : Traces TState SKind BVal) (φ : PEv → PEv), PC.n = 1 ∧
          (∀ i < 1, PC.st i 0 = .run csC) ∧ PC.Runs (CStep env pCL) ∧
          Realizes PA locsA MA0 rfA coA rmwA PC locsC MC0 φ (fun _ _ _ => True) :=
  CallCompose.realizes_linked (Priv := fun _ => PrivA RLF) (M := fun _ => MC2)
    (ok := fun _ => OkPriv RLF) (cs := fun _ => .run csC) (sA := fun _ => (RC.s0, none))
    (fun _ _ ls t' hr => by
      obtain ⟨k, c', hR, -⟩ := funReal_callFull env ls t' hr
      exact ⟨k, c', hR⟩)
    (ls := fun _ => ls) (t' := fun _ => t') (fun _ _ => hr)

end Concurrency.CallSeg.WitnessC
