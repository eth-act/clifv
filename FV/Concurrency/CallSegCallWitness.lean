import FV.Concurrency.CallSegCall
import FV.Concurrency.CallEntryLinkWitness
import FV.Concurrency.CallRetLinkWitness
import FV.Concurrency.FrameDisjWitness
import FV.Concurrency.CallRetPremisesWitness

/-!
# Witnesses for `CallSegCall` (#473)

On the link of the compiled caller and the compiled `atomic_load` (`LinkedMachine.Witness.link2`),
the caller with a callee budget of `0x100` bytes (`RA2`):

* `codeIn_RA2`: `CodeIn` (the caller's own code; `atomic_load`'s in its kept addresses `GL`);
* `stack_ld`, `nested_ld`, `gfree_ld`: at the caller's `bl ld` (`sBF`), `atomic_load` entered
  with a budget of `0x10` bytes (`stackAvail_callee`, `nested_callee`, `gfree_callee`);
* `budget_two`: `budget_call` with `Dcap = 2`;
* `call_endK_fC`: `call_endK` for the caller's call, every premise holding but the paused
  configuration's relations and the CLIF state at the call;
* `retEnd_n_ld`: `retEnd_n` for every activation of `atomic_load` entered by the caller's `bl`;
* `resume_ret_fC`: `resume_ret` for the caller (`RC`, as `CallResumeAll.Witness.resume_all_fC`)
  resumed after every such activation of `atomic_load`, every static premise discharged.

Checks by `native_decide` (witness only).
-/

namespace Concurrency.CallSegCall.Witness

open Arm ArmThread ClifThread Backend Backend.Proof Backend.Proof.Driver VCodeThread PrepThread
  AllocThread ArmAllocThread IselThread ThreadRefine E2E IselCall IselCallRet CallRetsEnd
  LinkedMachine LinkedMachine.Link LinkedMachine.Witness CallSeg.WitnessC CallEntry.Witness
  CallResumeL.Witness RealizeCompiled.WitnessL FrameDisj FrameDisj.Witness CallArgsL2 CallArgsAt
  CallArgsEntry CallResumeChecks
open ArmAllocThread.Witness (act)

/-- The caller in the link with a callee budget of `0x100` bytes. -/
abbrev RA2 : RL := link2.act callerF sC0 0x100 GL

theorem wf_RA2 : RA2.Wf :=
  ⟨wfRCK.check, wfRCK.alloc, wfRCK.emit, wfRCK.layout, wfRCK.lm, wfRCK.fit, wfRCK.stack,
    wfRCK.psF, wfRCK.prog0, wfRCK.gfree⟩

/-- **The linked code is kept by the caller.** -/
theorem codeIn_RA2 : CodeIn link2 RA2 := by
  intro n FB hB
  simp only [link2, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hB
  rcases hB with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine .inr fun k wd hk => ?_
    have hk' : (act vcpL rfL).fb.words[k]? = some wd := hk
    obtain ⟨hlt, -⟩ := Array.getElem?_eq_some_iff.mp hk'
    have hG : ∀ i < 4, GL (0x20000#64 + BitVec.ofNat 64 (4 * k) + BitVec.ofNat 64 i) :=
      fun i hi => by
        unfold GL
        have : (act vcpL rfL).fb.words.size ≤ 0x4000 := spC.2.2.2.1
        generalize (act vcpL rfL).fb.words.size = n at this hlt
        bv_omega
    refine ⟨hG, ?_⟩
    have hR : Arm.read_mem_bytes 4 (0x20000#64 + BitVec.ofNat 64 (4 * k)) RAL.s0 = wd :=
      abiRL.code k wd hk'
    show Arm.read_mem_bytes 4 (0x20000#64 + BitVec.ofNat 64 (4 * k)) sC0 = wd
    rw [← hR]
    refine read_mem_bytes_congr 4 _ fun i hi => ?_
    show memC _ = _
    simp only [memC, hG i hi, ↓reduceIte]
  · exact .inl ⟨rfl, rfl⟩

theorem F_RA2 : ∀ a, RC.F a → RA2.F a := fun a h => by
  unfold RL.F frameWG frameW at h ⊢
  rcases h with (h | ⟨h1, h2⟩) | h
  · exact .inl (.inl h)
  · exact .inl (.inr ⟨h1, by
      show (spv RC.s0 - BitVec.ofNat 64 (frameDrop RC.af)).toNat ≤ a.toNat + 0x100
      have : (spv RC.s0 - BitVec.ofNat 64 (frameDrop RC.af)).toNat ≤ a.toNat + 0 := h2
      omega⟩)
  · exact .inr h

/-- The caller at its `bl ld` (`sBF`), related as the caller with the larger budget. -/
theorem strel_sBF : ∃ m, StRel RA2 sBF m w₀C := by
  obtain ⟨m, -, hq, -⟩ := prefixF
  have hS := q_stRel hq
  refine ⟨m, ⟨hS.store, SameWorld.mono F_RA2 hS.world, hS.err, hS.prog, hS.sp, hS.align,
    fun hf => ?_, hS.code, hS.gkeep, hS.fp⟩⟩
  show Arm.read_mem_bytes RC.topN RC.topB sBF = Arm.read_mem_bytes RC.topN RC.topB RA2.sP
  rw [show RA2.sP = RC.sP from RL.sP_hooks wfRC abiRC link2.H]
  exact hS.fplr hf

theorem mem_ld : ("ld", ldF) ∈ link2.fns := by simp [link2]

theorem budget_ld : ldF.af.frameSize + 16 + 0x10 ≤ RA2.K := by
  have : (act vcpL rfL).af.frameSize = 160 := spC.2.2.2.2.2.2.2.2
  show (act vcpL rfL).af.frameSize + 16 + 0x10 ≤ 0x100
  omega

/-- `atomic_load`'s frame gets no stack probes (#581). -/
theorem probe_ld : probeBelow ldF.af ≤ 0x10 := by
  have : (act vcpL rfL).af.frameSize = 160 := spC.2.2.2.2.2.2.2.2
  exact ArmAllocThread.Witness.probeBelow_le_small (show (act vcpL rfL).af.frameSize + 16 < 4096 by omega)

/-- **Non-vacuity of `stackAvail_callee`.** -/
theorem stack_ld : StackAvail 0x10 ldF.af (enter ldF sBF) := by
  obtain ⟨m, hS⟩ := strel_sBF
  exact stackAvail_callee wf_RA2 hS codeIn_RA2 mem_ld budget_ld probe_ld

/-- **Non-vacuity of `nested_callee`.** -/
theorem nested_ld : Nested RA2 (link2.act ldF (enter ldF sBF) 0x10 RA2.FK) := by
  obtain ⟨m, hS⟩ := strel_sBF
  exact nested_callee hS (by have := frameDrop_le ldF.af; have := budget_ld; omega)

/-- **Non-vacuity of `gfree_callee`.** -/
theorem gfree_ld : ∀ a, RA2.FK a → ¬ StackBelow (frameDrop ldF.af + 0x10) (spv (enter ldF sBF)) a := by
  obtain ⟨m, hS⟩ := strel_sBF
  exact gfree_callee wf_RA2 hS codeIn_RA2 mem_ld budget_ld

/-- **Non-vacuity of `budget_call`.** -/
theorem budget_two : 240 ≤ 512 ∧ (2 - (0 + 1)) * 256 ≤ 512 - 240 :=
  budget_call (Dcap := 2) (d := 0) (M := 256) (K := 512) (N := 240) (by decide) (by decide)
    (by decide)

/-- The memory relation's parameters of the caller with the larger budget. -/
def ΓC2 : E2E.Rel := ⟨RA2.F, fun _ => none, RA2.ctx.slotBase, 0⟩

/-- **Non-vacuity of `call_endK`**: the caller's call of `atomic_load`, every premise holding
but the paused configuration's relations and the CLIF state at the call. -/
theorem call_endK_fC {env : Clif.Env} (henv : env.extern "ld" = none) (c : BitVec 64) :
    ∃ (ctx : Ctx) (st0 : LState) (R : Reg → Reg) (gn : Nat → Nat) (bl : List BLow)
      (A : Nat → Nat → List Clif.ValueId) (Lp : Nat → Prop) (ss' : Array (Array Nat))
      (cc : CheckCtx) (ins : Array (Option AState)),
      DriverHypT fC vcC ctx st0 R gn bl A (csem RA2.F RA2.ctx RA2.X) (RelW ΓC2 fC c) env pCL ∧
      ∀ {r₀ : Reg → CV} {x : ArmState} {s' : Clif.State} {vV' vP' : VState CV ArmState}
        {cM' : MState CV ArmState} {slots : List (Clif.SlotId × Nat)} {stm : Clif.Stmt}
        {rest : List Clif.Stmt} {fn : Clif.FnRef} {args : List Clif.ValueId}
        {vals : List Clif.Val},
        Q RA2 x (.run cM') → Pause RA2 (.run cM') →
        Match fC ctx R gn bl A (RelW ΓC2 fC c) slots s' vV' →
        PMatch vcC RA2.vc (csem RA2.F RA2.ctx RA2.X) (cEvs RA2.F RA2.ctx) Lp ss' (.run vV')
          (.run vP') →
        MatchRun cc ins ckeep r₀ cM' vP' →
        s'.frame.body = stm :: rest → stm.inst = .call fn args →
        s'.frame.func.extern? fn = some extF → s'.frame.getMany args = .ok vals →
        vals.map (·.ty) = Clif.AbiParam.tys extF.sig.params →
        link2.M x = enter ldF x ∧ (link2.act ldF (enter ldF x) 0x10 RA2.FK).Wf ∧
          ArgsAtEntry (link2.act ldF (enter ldF x) 0x10 RA2.FK).F fL.sig vals
            (bodyOf ldF.af (enter ldF x)) ∧
          CodeIn link2 (link2.act ldF (enter ldF x) 0x10 RA2.FK) ∧
          Nested RA2 (link2.act ldF (enter ldF x) 0x10 RA2.FK) := by
  obtain ⟨hlow, hthr, -, hnames, hind, hv, hnt, -, hout0, -, hexts⟩ := IselCall.Witness.checksFC
  have hext : ∀ e ∈ fC.externs, env.extern e.2.name = none := by
    intro e he
    have : e.2.name ∈ fC.externs.map (·.2.name) := List.mem_map_of_mem he
    rw [hnames, List.mem_singleton] at this
    rw [this]; exact henv
  obtain ⟨ctx, st0, R, gn, bl, A, H, hchk, -, hcu⟩ := IselResume.driverHypT_ofA (Γ := ΓC2)
    (fctx := RA2.ctx) (X := VCodeThread.Witness.X0) (c := c) (env := env) (p := pCL) hlow hthr
    CallResumeAll.Witness.arity_fC.1 CallArgsEntry.Witness.useRegs_fC hext
    (List.isEmpty_iff.mp hind) hv hnt IselCall.Witness.cfgFC hout0 rfl (fun _ _ h => by cases h)
  obtain ⟨Lp, ss, ss', H3, -⟩ := CallLayers.prep_init (vc := vcC) (vcp := RA2.vc) prepC
  obtain ⟨cc, ins, a0, hat0, -⟩ := CallLayers.alloc_init (vc := RA2.vc) (rf := RA2.rf) allocC ckeep
  refine ⟨ctx, st0, R, gn, bl, A, Lp, ss', cc, ins, H, fun hq hP hm2 hm3 hm4 hbody hcl hext' hvals
    htys => ?_⟩
  have hB : (extF.name, ldF) ∈ link2.fns := by rw [name_extF]; exact mem_ld
  obtain ⟨h1, -, -, h4, -, -, -, -, -, -, h11, h12, h13⟩ := call_endK ok2 (nA := "f") (FA := callerF)
    (by simp [link2]) (s0 := sC0) (K := 0x100) (G := GL) wf_RA2 codeIn_RA2 H hchk
    CallArgsL2.Witness.resLen_fC hcu hlow (List.isEmpty_iff.mp hind) hv hnt hout0 rfl
    (fun _ _ h => by cases h) (fun _ _ _ => rfl) H3 hat0 Concurrency.CallArgsAt.Witness.usesV_fC
    CallResumeAll.Witness.defs_fC.1 hq hP hm2 hm3 hm4 hbody hcl hext'
    (fun e he _ => by rw [hexts, List.mem_singleton] at he; rw [he]) hvals htys hB static_ld
    budget_ld probe_ld sig_fL
  exact ⟨h1, h4, h11, h12, h13⟩

/-- **Non-vacuity of `retEnd_n`**: every activation of `atomic_load` entered by the caller's `bl`
at a `rets` pause with its contract. -/
theorem retEnd_n_ld {s0 : ArmState} {env : Clif.Env} {p : Clif.Program} {MR : MemRelT}
    {slots : List (Clif.SlotId × Nat)} {r₀ : Reg → CV} {x : ArmState} {s' : Clif.State}
    (hRB : (link2.act ldF s0 0 RC.F).Wf) (hent : AbiCall ldF.fb ldF.base (RC.pcOf 15 + 4#64) s0)
    (hret : RetEnd (link2.act ldF s0 0 RC.F) (RC.pcOf 15 + 4#64) env p MR slots r₀ x s') :
    ∃ n, 0 < n ∧ ∃ b k allocs its m w vb us ops ρ vals cm,
      QA (link2.act ldF s0 0 RC.F) x (.run ⟨b, .op k allocs :: its, m, w⟩) ∧
      ldF.vc.blocks[b]? = some vb ∧ vb.insts[k]? = some (.rets us) ∧
      (MInst.rets us).operands = .ok ops ∧ Clif.step env p s' = .done vals cm ∧
      PrefixHold vals (vuses ops ρ) ∧ MR slots s'.mem w ∧
      cm = (s'.mem.free (slots.map (·.2))).leave ∧
      (iterN (link2.act ldF s0 0 RC.F).step n x).mem = x.mem ∧
      ∀ (j : Nat) (v q : Reg) (y : CV), us[j]? = some (v, q) → (vuses ops ρ)[j]? = some y →
        regVal (iterN (link2.act ldF s0 0 RC.F).step n x) q = y := by
  obtain ⟨n, hn, hRC, -, -⟩ := ret_end ok2 (nB := "ld") mem_ld hRB hent ra_out (nA := "f")
    (by simp [link2]) ra_in hret
  exact ⟨n, hn, retEnd_n hRB hent ra_out hret hRC.1 hRC.2.1⟩

/-- `atomic_load`'s `rets` read `x0` (as a check). -/
def retsB : Bool :=
  vcpL.blocks.all fun vb => vb.insts.all fun i => match i with
    | .rets us => us.map (·.2) == [.x 0]
    | _ => true

theorem retsB_eq : retsB = true := by native_decide

theorem rets_ld {b : Nat} {vb : VBlock} {us : List (Reg × Reg)} (hb : vcpL.blocks[b]? = some vb)
    (hk : ∃ k : Nat, vb.insts[k]? = some (MInst.rets us)) : us.map (·.2) = [.x 0] := by
  obtain ⟨k, hk⟩ := hk
  have h := retsB_eq
  simp only [retsB, Array.all_eq_true] at h
  obtain ⟨hb1, rfl⟩ := Array.getElem?_eq_some_iff.mp hb
  obtain ⟨hk1, e⟩ := Array.getElem?_eq_some_iff.mp hk
  have h2 := h b hb1 k hk1
  rw [e] at h2
  simpa using h2

/-- **Non-vacuity of `resume_ret`**: the caller of `atomic_load` resumed after every activation
of `atomic_load` entered by its `bl`, every static premise discharged; the pause, the callee's
entry and return contract and the valid memory stay premises. -/
theorem resume_ret_fC {env : Clif.Env} (henv : env.extern "ld" = none) (c : BitVec 64) :
    ∃ (ctx : Ctx) (st0 : LState) (R : Reg → Reg) (gn : Nat → Nat) (bl : List BLow)
      (A : Nat → Nat → List Clif.ValueId) (Lp : Nat → Prop) (ss' : Array (Array Nat))
      (cc : CheckCtx) (ins : Array (Option AState)),
      DriverHypT fC vcC ctx st0 R gn bl A (csem RC.F RC.ctx RC.X) (RelW ΓC fC c) env pCL ∧
      ∀ {s0B : ArmState} {r₀ : Reg → CV} {x : ArmState} {s' : Clif.State}
        {vV' vP' : VState CV ArmState} {cM' : MState CV ArmState}
        {slots : List (Clif.SlotId × Nat)} {r₀B : Reg → CV} {ΓB : E2E.Rel} {fB : Clif.Function}
        {cB : BitVec 64} {slotsB : List (Clif.SlotId × Nat)} {xB : ArmState} {sR : Clif.State}
        {n : Nat} {rvals : List Clif.Val} {cmR : Clif.Mem} {d : Nat} {sRet : Clif.State}
        {stm : Clif.Stmt} {rest : List Clif.Stmt} {fn : Clif.FnRef} {args : List Clif.ValueId}
        {vals : List Clif.Val} {regs' : Clif.Regs},
        Q RC x (.run cM') → AInv RC (.run cM') → Pause RC (.run cM') → AtCallS s' →
        Match fC ctx R gn bl A (RelW ΓC fC c) slots s' vV' →
        PMatch vcC RC.vc (csem RC.F RC.ctx RC.X) (cEvs RC.F RC.ctx) Lp ss' (.run vV') (.run vP') →
        MatchRun cc ins ckeep r₀ cM' vP' →
        (link2.act ldF s0B 0 RC.F).Wf → AbiCall ldF.fb ldF.base (RC.pcOf 15 + 4#64) s0B →
        (∀ f, f ≠ .PC → f ≠ .GPR 30#5 → Arm.r f s0B = Arm.r f x) →
        xreg 30 s0B = Arm.r .PC x + 4#64 → (∀ a, RC.FK a → s0B.mem a = x.mem a) →
        (∀ r ∈ calleeSaved, ckeep r (r₀B r) = ckeep r
          (locVal (link2.act ldF s0B 0 RC.F).fr (iterN (link2.act ldF s0B 0 RC.F).step
            (prologueLines ldF.af.saves ldF.af.frameSize ldF.af.isCaller).length s0B) (.reg r))) →
        RetEnd (link2.act ldF s0B 0 RC.F) (RC.pcOf 15 + 4#64) env pCL (RelW ΓB fB cB) slotsB r₀B
          xB sR →
        ΓB.F = (link2.act ldF s0B 0 RC.F).F → ΓB.syms = ΓC.syms →
        RetC (link2.act ldF s0B 0 RC.F) (RC.pcOf 15 + 4#64) r₀B
          (iterN (link2.act ldF s0B 0 RC.F).step n xB) →
        Clif.step env pCL sR = .done rvals cmR →
        CallValid.AllocInvD s'.mem d sRet → sRet.callers.length = d → sRet.mem = cmR →
        s'.frame.body = stm :: rest → stm.inst = .call fn args →
        s'.frame.func.extern? fn = some extF → s'.frame.getMany args = .ok vals →
        vals.map (·.ty) = Clif.AbiParam.tys extF.sig.params →
        rvals.map (·.ty) = Clif.AbiParam.tys extF.sig.returns →
        s'.frame.regs.setMany stm.results rvals = some regs' →
        ∃ vV'' vP'' cM'',
          Match fC ctx R gn bl A (RelW ΓC fC c) slots { s' with
              frame := { s'.frame with regs := regs', body := rest }, mem := cmR } vV'' ∧
          PMatch vcC RC.vc (csem RC.F RC.ctx RC.X) (cEvs RC.F RC.ctx) Lp ss' (.run vV'')
            (.run vP'') ∧
          MatchRun cc ins ckeep r₀ cM'' vP'' ∧
          Q RC (set_program (iterN (link2.act ldF s0B 0 RC.F).step n xB) (RC.fb.program RC.base))
            (.run cM'') ∧ AInv RC (.run cM'') := by
  obtain ⟨ctx, st0, R, gn, bl, A, H, hchk, har, -⟩ := driverA_fC henv c
  obtain ⟨Lp, ss, ss', H3, -⟩ := CallLayers.prep_init (vc := vcC) (vcp := RC.vc) prepC
  obtain ⟨cc, ins, a0, hat0, -⟩ := CallLayers.alloc_init (vc := RC.vc) (rf := RC.rf) allocC ckeep
  obtain ⟨hlow, -, -, -, hind, hv, hnt, -, hout0, -, hexts⟩ := IselCall.Witness.checksFC
  refine ⟨ctx, st0, R, gn, bl, A, Lp, ss', cc, ins, H, fun hq hA hP hat hm2 hm3 hm4 hRB hent hfx
    hlr hm0 hr₀B hret hΓB hsyms hy hdone hD hd hmR hbody hcl hext hvals htys hrty hregs => ?_⟩
  exact resume_ret wfRC hRB rfl (fun _ _ _ => rfl) H hchk har hlow (List.isEmpty_iff.mp hind) hv
    hnt hout0 rfl rfl (fun _ _ h => by cases h) H3 hat0 CallResumeAll.Witness.defs_fC.1 hq hA hP
    hat hm2 hm3 hm4 hent ra_out hfx hlr hm0 (fun a h => h.elim (fun h => .inl (.inl h)) .inr) hr₀B
    (fun b vb us hb hk => by rw [rets_ld hb hk]; exact CallResumeAll.Witness.defs_fC.2) hret hΓB
    hsyms hy hdone hD hd hmR hbody hcl hext
    (fun e he _ => by rw [hexts, List.mem_singleton] at he; rw [he]) hvals htys hrty hregs

end Concurrency.CallSegCall.Witness
