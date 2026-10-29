import FV.Concurrency.ThreadCompose
import FV.Concurrency.ArmAllocLS

/-!
# The realized prefix covers the whole run (T2j, #473)

`ThreadCompose.arm_isel_refines` realizes a prefix of a thread's Arm run that is the whole run,
or ends where the CLIF thread stops, or ends where the allocated code is `Done` — returned,
trapped, or **without a step**. The last case could end the prefix early. This file excludes it:

* `ItemSim.withRel`, `arm_alloc_refinesQ`, **`arm_alloc_refines_lsQ`**: layer 4b ends at a
  `Done` configuration that is still related to an Arm state (`RelQ`): the per-item obligation
  stops only at related configurations;
* `CoveredCode` (every instruction of the activation is `SegFoot.Covered`: not a call, a control
  form or a covered straight-line form), `coveredCode_of_ls` (the scope `MemScopeLS` is covered);
* **`srcStep_of_mstep`** (the allocated code's progress, as a thread): at a configuration related
  to an Arm state, a step of the allocated code (`MStep`) is a thread step (`SrcStep`) with the
  instruction's precise footprint on the world (`ifoot_csem`; the world is error-free and aligned
  by `StRel`, and the footprint's reads come before its writes, so they read the world);
* **`arm_isel_refines_full`**: all layers composed with layers 2–4a's progress
  (`ThreadCompose.isel_alloc_refinesP`: where the realized prefix is the allocated code's whole
  run, the allocated code has a step): the realized prefix is the whole Arm run, or the CLIF
  thread stops (`IselThread.Stop`: it has no step — returned, trapped, undefined behaviour — or is
  at an `atomic_cas` on read-only data).
-/

namespace Concurrency.ThreadProgress

open Arm ArmThread Prog ClifThread Backend Backend.Proof Backend.Proof.Driver VCodeThread
  PrepThread AllocThread IselCheck CorrRefine ClifCStepTerm IselThread ThreadRefine
  ArmAllocThread ThreadCompose

/-! ## Layer 4b, ending at a related configuration -/

/-- **The per-item obligation stops only at related configurations.** -/
theorem ItemSim.withRel {P : Policy} {f : ArmState → ArmState} {ok : ArmState → Lab → Prop}
    {C : Type} {S : C → List Ev → C → Prop} {Rel : ArmState × Mon → C → Prop} {Term : C → Prop}
    {μ : C → Nat} {Priv : Nat → Prop} (h : ItemSim P f ok S Rel Term μ Priv) :
    ItemSim P f ok S Rel (fun c => Term c ∧ ∃ t, Rel t c) μ Priv := by
  intro t c hR ls t' hr
  rcases h t c hR ls t' hr with h1 | h2
  · exact .inl ⟨h1, t, hR⟩
  · exact .inr h2

/-- **Layer 4b, ending at a related configuration** (`refines_of_itemSim` with
`ItemSim.withRel`), for any scope whose per-item obligation holds. The obligation is on ranked
configurations (`ArmAllocBranch.RConf`: the statement before #553 took one with a measure of the
configuration only, which no scope with branches meets under `MachBuffer`'s layout). -/
theorem arm_alloc_refinesQ {R : RL}
    (hsim : ItemSim Policy.arm R.step (OkPriv R) (SrcStepR R) (RelQR R) (DoneR R) (μR R) (PrivA R))
    {s : ArmState} {mon : Mon} {c : MConf CV ArmState} (hq : Q R s c) (hA : AInv R c)
    {ls : List Lab} {t' : ArmState × Mon} (hr : PRun Policy.arm R.step (OkPriv R) (s, mon) ls t') :
    ∃ n trS cE ψ, n ≤ ls.length ∧ MTRun R.vc R.rf R.sem ckeep (cEvs R.F R.ctx) c trS cE ∧
      Refines (· = ·) (PrivA R) (MonPair (evTr (ls.take n))) (PrepThread.conv trS)
        (PrepThread.conv (evTr (ls.take n))) ψ ∧
      (n = ls.length ∨ (Done R cE ∧ ∃ t, RelQ R t cE)) := by
  obtain ⟨r, hrel⟩ := RelQR.of (t := (s, mon)) hq hA
  obtain ⟨n, trS, cE, ψ, hn, hs, href, hend⟩ :=
    refines_of_itemSim (ItemSim.withRel hsim) hr hrel
  exact ⟨n, trS, cE.1, ψ, hn, mtrun_of_srun (SRun.fst hs), href,
    hend.imp_right fun ⟨hD, t, h1, _⟩ => ⟨hD, t, h1⟩⟩

/-- **`arm_alloc_refines_ls` ending at a related configuration.** -/
theorem arm_alloc_refines_lsQ {R : RL} (hR : R.Wf) (hsc : MemScopeLS R)
    {s : ArmState} {mon : Mon} {c : MConf CV ArmState} (hq : Q R s c) (hA : AInv R c)
    {ls : List Lab} {t' : ArmState × Mon} (hr : PRun Policy.arm R.step (OkPriv R) (s, mon) ls t') :
    ∃ n trS cE ψ, n ≤ ls.length ∧ MTRun R.vc R.rf R.sem ckeep (cEvs R.F R.ctx) c trS cE ∧
      Refines (· = ·) (PrivA R) (MonPair (evTr (ls.take n))) (PrepThread.conv trS)
        (PrepThread.conv (evTr (ls.take n))) ψ ∧
      (n = ls.length ∨ (Done R cE ∧ ∃ t, RelQ R t cE)) :=
  arm_alloc_refinesQ (itemSim_ls hR hsc) hq hA hr

/-! ## Covered code -/

/-- **Every instruction of the activation's code is covered** (`SegFoot.Covered`). -/
def CoveredCode (R : RL) : Prop :=
  ∀ (b : Nat) (vb : VBlock) (k : Nat) (i : MInst), R.vc.blocks[b]? = some vb →
    vb.insts[k]? = some i → SegFoot.Covered R.ctx i

theorem covered_of_formOk {ctx : FnCtx} {i : MInst} (h : FormOk ctx i = true) :
    SegFoot.Covered ctx i := by
  refine ⟨fun info e => ?_, fun info ti e => ?_, .inr h⟩ <;> subst e <;> simp [FormOk] at h

theorem covered_of_memFormL {ctx : FnCtx} {i : MInst} (h : MemFormL ctx i) :
    SegFoot.Covered ctx i := by
  rcases h with ((⟨-, hfo, -⟩ | ⟨ds, rfl⟩ | ⟨us, rfl⟩ | ⟨c, rfl⟩) | rfl | ⟨ty, rt, rn, fl, rfl, hfo⟩ |
      ⟨ty, rt, rn, fl, rfl, hfo⟩) | ⟨ty, op, fl, ra, ro, rd, r1, r2, rfl⟩ |
      ⟨ty, fl, ra, re, rx, rd, r1, rfl⟩
  · exact covered_of_formOk hfo
  · exact ⟨fun _ e => (nomatch e), fun _ _ e => (nomatch e), .inl rfl⟩
  · exact ⟨fun _ e => (nomatch e), fun _ _ e => (nomatch e), .inl rfl⟩
  · exact ⟨fun _ e => (nomatch e), fun _ _ e => (nomatch e), .inl rfl⟩
  · exact covered_of_formOk rfl
  · exact covered_of_formOk hfo
  · exact covered_of_formOk hfo
  · exact ⟨fun _ e => (nomatch e), fun _ _ e => (nomatch e), .inl rfl⟩
  · exact ⟨fun _ e => (nomatch e), fun _ _ e => (nomatch e), .inl rfl⟩

theorem covered_of_brForm {ctx : FnCtx} {i : MInst} (h : BrForm i) : SegFoot.Covered ctx i := by
  rcases h with ⟨l, rfl⟩ | ⟨t, e, kk, rfl⟩ | ⟨kd, t, e, rn, bit, rfl⟩ <;>
    exact ⟨fun _ e => (nomatch e), fun _ _ e => (nomatch e), .inl rfl⟩

/-- **The scope with plain loads/stores is covered.** -/
theorem coveredCode_of_ls {R : RL} (h : MemScopeLS R) : CoveredCode R := fun b vb k i hb hi =>
  (h b vb k i hb hi).elim covered_of_memFormL fun h => h.elim covered_of_brForm fun h =>
    covered_of_formOk h.1

/-! ## The allocated code's progress -/

/-- At most one memory kind, off the LL/SC loops. -/
theorem akinds_le_one {i : MInst}
    (hr : ∀ ty op fl a b c d e, i ≠ .atomicRmwLoop ty op fl a b c d e)
    (hc : ∀ ty fl a b c d e, i ≠ .atomicCasLoop ty fl a b c d e) : (Code.akinds i).length ≤ 1 := by
  cases i
  all_goals first
    | exact absurd rfl (hr _ _ _ _ _ _ _ _)
    | exact absurd rfl (hc _ _ _ _ _ _ _)
    | simp [Code.akinds]

/-- **A covered instruction's footprint reads the world** (its reads come first). -/
theorem agrees_cEvs {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {i : MInst} {u : List CV}
    {w : ArmState} {r : List CV × ArmState × Ctl} (he : Arm.r .ERR w = .None)
    (hf : IFoot (csem F ctx X) i u w (cEvs F ctx i u w)) (hs : csem F ctx X i u w = some r) :
    Agrees (cEvs F ctx i u w) w.mem := by
  by_cases hl : (∃ ty op fl a b c d e, i = .atomicRmwLoop ty op fl a b c d e) ∨
      (∃ ty fl a b c d e, i = .atomicCasLoop ty fl a b c d e)
  · rcases hl with ⟨ty, op, fl, a, b, c, d, e, rfl⟩ | ⟨ty, fl, a, b, c, d, e, rfl⟩
    · rcases u with _ | ⟨u1, _ | ⟨u2, _ | ⟨u3, t⟩⟩⟩
      · simp [csem] at hs
      · simp [csem] at hs
      · obtain ⟨wr, hev, hk, -, -⟩ := IselMemAux.cEvs_rmw_shape he hs
        rw [hev]
        intro x hx hR
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · rfl
        · rw [hk] at hR; cases hR
      · simp [csem] at hs
    · rcases u with _ | ⟨u1, _ | ⟨u2, _ | ⟨u3, _ | ⟨u4, t⟩⟩⟩⟩
      · simp [csem] at hs
      · simp [csem] at hs
      · simp [csem] at hs
      · rcases IselMemAux.cEvs_cas_shape he hs with ⟨hev, -⟩ | ⟨wr, hev, hk, -, -, -⟩
        · rw [hev]
          intro x hx _
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          subst hx; rfl
        · rw [hev]
          intro x hx hR
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl
          · rfl
          · rw [hk] at hR; cases hR
      · simp [csem] at hs
  · simp only [not_or, not_exists] at hl
    refine (sagrees_iff ?_ w.mem).mp hf.1
    have h1 := (VCodeEvents.cEvs_kinds F ctx i u w).length_le
    rw [List.length_map] at h1
    exact Nat.le_trans h1 (akinds_le_one (fun ty op fl a b c d e h => hl.1 ty op fl a b c d e h)
      (fun ty fl a b c d e h => hl.2 ty fl a b c d e h))

/-- **The allocated code's progress, as a thread** (module doc): at a configuration related to an
Arm state, every step of covered allocated code is a thread step, with the instruction's precise
footprint on the world. -/
theorem srcStep_of_mstep {R : RL} (hcov : CoveredCode R) (hX : TlsMemFree R.X) {s : ArmState}
    {c c' : MConf CV ArmState} (hq : Q R s c) (hs : MStep R.vc R.sem ckeep R.rf c c') :
    ∃ evs c'', SrcStep R c evs c'' := by
  cases hs with
  | move => exact ⟨[], _, .move⟩
  | @op b k allocs its m w vb i ops outs outs' w' ctl m2 c' hvb hi hops hsz hsem hlen hho hclob
      hnext =>
    obtain ⟨hnc, hnt, hcv⟩ := hcov b vb k i hvb hi
    have hstr := q_stRel hq
    have herrw : Arm.r .ERR w = .None := by
      rw [← hstr.world.1 .ERR (by simp [Masked]), hstr.err]
    have halw : CheckSPAlignment w :=
      align_of_sp (show Arm.r (.GPR 31#5) w = Arm.r (.GPR 31#5) s from
        (hstr.world.1 (.GPR 31#5) (by simp [Masked])).symm) hstr.align
    obtain ⟨regs, -, hsz', -, huses⟩ := q_regs hq hvb hi hops
    have hst : i.isCtl = false →
        csemWF R.ctx i (itemUses ops allocs m) = true ∧ CheckSPAlignment w := by
      intro hctl
      have hfo : FormOk R.ctx i = true := by
        rcases hcv with h | h
        · rw [hctl] at h; cases h
        · exact h
      refine ⟨?_, halw⟩
      rw [huses]
      simp [csemWF, hfo, hops, useVals_length ops regs hsz']
    have hfoot := ifoot_csem (F := R.F) (ctx := R.ctx) (uses := itemUses ops allocs m) hX herrw
      hnc hnt hst
    have hsemC : csem R.F R.ctx R.X i (itemUses ops allocs m) w = some (outs, w', ctl) := by
      rw [← R.sem_eq hnc hnt]; exact hsem
    have hp := patch_of_agrees (agrees_cEvs herrw hfoot hsemC)
    refine ⟨cEvs R.F R.ctx i (itemUses ops allocs m) w, c', .op hvb hi hops ?_ ?_ ?_⟩
    · rw [hp]
    · rw [hp]
      unfold IFoot at hfoot ⊢
      simp only [R.sem_eq hnc hnt]
      exact hfoot
    · rw [hp]
      exact .op hvb hi hops hsz hsem hlen hho hclob hnext

/-- **The allocated code's progress in a return tail**: the item is a move (a thread step
without events) or the tail's `rets`, whose footprint needs no fact of the store. -/
theorem srcStep_of_retTail {R : RL} (hX : TlsMemFree R.X) {s : ArmState}
    {c c' : MConf CV ArmState} (hrt : RetTail R s c)
    (hs : MStep R.vc R.sem ckeep R.rf c c') : ∃ evs c'', SrcStep R c evs c'' := by
  cases hs with
  | move => exact ⟨[], _, .move⟩
  | @op b k allocs its m w vb i ops outs outs' w' ctl m2 c' hvb hi hops hsz hsem hlen hho hclob
      hnext =>
    simp only [RetTail] at hrt
    obtain ⟨mt, D, hq, -, vb', pend, k', a', rest, us, hvb', he, hk', htl⟩ := hrt
    obtain rfl : i = .rets us := by
      rcases pend with _ | ⟨it, pend⟩
      · simp only [List.nil_append, List.cons.injEq, RItem.op.injEq] at he
        obtain ⟨⟨rfl, -⟩, -⟩ := he
        rw [hvb] at hvb'; cases hvb'; rw [hi] at hk'; cases hk'; rfl
      · simp only [List.cons_append, List.cons.injEq] at he
        obtain ⟨rfl, -⟩ := he
        simp [retTailOk, RItem.restoreReg, RItem.avoids] at htl
    have hnc : ∀ info, MInst.rets us ≠ .call info := fun _ h => by cases h
    have hnt : ∀ info ti, MInst.rets us ≠ .tryCall info ti := fun _ _ h => by cases h
    have hstr := q_stRel hq
    have herrw : Arm.r .ERR w = .None := by
      rw [← hstr.world.1 .ERR (by simp [Masked]), hstr.err]
    have hst : (MInst.rets us).isCtl = false →
        csemWF R.ctx (.rets us) (itemUses ops allocs m) = true ∧ CheckSPAlignment w :=
      fun h => by simp [MInst.isCtl] at h
    have hfoot := ifoot_csem (F := R.F) (ctx := R.ctx) (uses := itemUses ops allocs m) hX herrw
      hnc hnt hst
    have hsemC : csem R.F R.ctx R.X (.rets us) (itemUses ops allocs m) w = some (outs, w', ctl) := by
      rw [← R.sem_eq hnc hnt]; exact hsem
    have hp := patch_of_agrees (agrees_cEvs herrw hfoot hsemC)
    refine ⟨cEvs R.F R.ctx (.rets us) (itemUses ops allocs m) w, c', .op hvb hi hops ?_ ?_ ?_⟩
    · rw [hp]
    · rw [hp]
      unfold IFoot at hfoot ⊢
      simp only [R.sem_eq hnc hnt]
      exact hfoot
    · rw [hp]
      exact .op hvb hi hops hsz hsem hlen hho hclob hnext

/-- **`srcStep_of_mstep` at a `RelQ`-related configuration** (`srcStep_of_retTail` in a return
tail). -/
theorem srcStep_of_mstepQA {R : RL} (hcov : CoveredCode R) (hX : TlsMemFree R.X)
    {t : ArmState × Mon} {c c' : MConf CV ArmState} (hqa : RelQ R t c)
    (hs : MStep R.vc R.sem ckeep R.rf c c') : ∃ evs c'', SrcStep R c evs c'' := by
  rcases hqa with ⟨hq, -⟩ | hrt
  · exact srcStep_of_mstep hcov hX hq hs
  · exact srcStep_of_retTail hX hrt hs

/-! ## All layers -/

/-- **All layers composed, the realized prefix the whole run or ending where the CLIF thread
stops, all of layer 4b's prefix where it has returned** (T2j follow-up; `isel_alloc_refinesR`) (module doc): layer 4b's refinement ending at a related configuration (`hA`, `hend`,
`arm_alloc_refinesQ`'s form) and layers 2–4a with progress (`isel_alloc_refinesP`); at a related
`Done` configuration after which layers 2–4a give a step of the allocated code, that step is a
thread step (`srcStep_of_mstep`), which `Done` excludes. -/
theorem arm_isel_refines_fullR {RA : RL} (hgv : RA.gv = fun _ _ => False) (hcov : CoveredCode RA)
    {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
    {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId} {MR : MemRelT}
    {env : Clif.Env} {p : Clif.Program} {slots : List (Clif.SlotId × Nat)} {sb : Nat}
    {syms : String → Option Nat}
    (H : DriverHyp f vc ctx st0 R gn bl A (csem RA.F RA.ctx RA.X) MR env p)
    (hchk : threadCheckBl f bl = true) (hMR : MemRelOk RA.F sb syms f MR)
    (hMRw : ∀ sl cm w, MR sl cm w → Arm.r .ERR w = .None ∧ Arm.CheckSPAlignment w)
    (hX : TlsMemFree RA.X) (hMem : MemRefines RA.F sb syms (csem RA.F RA.ctx RA.X))
    (hMRs : MRStable RA.F MR) (hreg : ∀ off, ArgLoc.stack off ∉ locsOf f.sig)
    (hprep : prepCheck vc RA.vc = true) (halloc : checkAlloc RA.vc RA.rf = .ok ())
    {cs : Clif.State} {B0 : Clif.Block} (hB0 : f.blocks[0]? = some B0)
    (hcall : cs.callers = []) (hfunc : cs.frame.func = f) (hslots : cs.frame.slots = slots)
    (hbody : cs.frame.body = B0.body) (hterm : cs.frame.term = B0.term) {args : List Clif.Val}
    (hregs : Clif.Regs.empty.setMany (B0.params.map (·.1)) args = some cs.frame.regs)
    (hty : args.map (·.ty) = B0.params.map (·.2))
    (hsig : args.map (·.ty) = f.sig.params.map (·.ty))
    {m₀ : Loc → CV} {w₀ : Arm.ArmState} (hmr : MR slots cs.mem w₀)
    (hargs : ArgsAtEntry RA.F f.sig args w₀)
    {ok : ArmState → Lab → Prop} {s : ArmState × Mon} {ls : List Lab} {s' : ArmState × Mon}
    (hP : PRun Policy.arm RA.step ok s ls s') {nA : Nat} {trM : List (List Ev)}
    {cE : MConf CV ArmState} {ψA : Nat × Nat → Nat × Nat}
    (hM : MTRun RA.vc RA.rf RA.sem ckeep (cEvs RA.F RA.ctx) (MConf.init RA.rf m₀ w₀) trM cE)
    (hA : Refines (· = ·) (PrivA RA) (MonPair (evTr (ls.take nA))) (conv trM)
      (conv (evTr (ls.take nA))) ψA)
    (hend : nA = ls.length ∨ (Done RA cE ∧ ∃ t, RelQ RA t cE)) (hnA : nA ≤ ls.length) :
    ∃ k trS t ψ, k ≤ nA ∧ CRun env p (.run cs) trS t ∧
      Refines Maps (PrivA RA) (MonPair (evTr (ls.take nA))) trS (conv (evTr (ls.take k))) ψ ∧
      (k = ls.length ∨ Stop env p t) ∧ ∀ v, t = .ret v → k = nA := by
  have hsem : RA.sem = csem RA.F RA.ctx RA.X := by
    show csemV RA.gv RA.F RA.ctx RA.X = _
    rw [hgv, csemV_none]
  rw [hsem] at hM
  obtain ⟨m, trS, t, ψ, hm, hrun, href, hendm, hretm⟩ :=
    isel_alloc_refinesR H hchk hMR hMRw hX hMem hMRs hreg hprep halloc hB0 hcall hfunc hslots
      hbody hterm hregs hty hsig (fun _ => 0) hmr hargs hM
  have h1 : ∀ j (hj : j < (conv (evTr (ls.take nA))).length),
      (conv (evTr (ls.take nA)))[j].length ≤ 1 := by
    intro j hj
    have hl := prun_len hP j (by simp [conv, evTr] at hj ⊢; omega)
    simp only [conv, evTr, List.getElem_map, List.length_map, List.getElem_take] at hl ⊢
    exact hl
  obtain ⟨k, hk, hAk, hkfull⟩ := Refines.take hA h1 m
  have hlenA : (conv (evTr (ls.take nA))).length = nA := by
    simp [conv, evTr]; omega
  have htk : (conv (evTr (ls.take nA))).take k = conv (evTr (ls.take k)) := by
    simp only [conv, evTr, ← List.map_take, List.take_take]
    rw [Nat.min_eq_left (by omega)]
  rw [htk] at hAk
  have hm' : (conv trM).take m = conv (trM.take m) := by simp [conv, List.map_take]
  rw [hm'] at hAk
  have href2 := Refines.congr (Refines.trans href hAk) (MK' := Maps) (P' := PrivA RA)
    (fun a c ⟨b, h1, h2⟩ => h2 ▸ h1) (fun l => ⟨fun h => by rcases h with h | h; exact h.elim; exact h,
      fun h => .inr h⟩)
  refine ⟨k, trS, t, _, by omega, hrun, href2, ?_, fun v hv => ?_⟩
  rotate_left
  · have hk' := hkfull (by simp [conv, hretm v hv])
    rw [hlenA] at hk'
    exact hk'
  rcases hendm with ⟨h, cE', hmst⟩ | h
  · have hk' := hkfull (by simp [conv, h])
    rw [hlenA] at hk'
    rcases hend with h' | ⟨hD, t0, hq0⟩
    · exact .inl (hk'.trans h')
    · exfalso
      rw [← hsem] at hmst
      obtain ⟨evs, c'', hs⟩ := srcStep_of_mstepQA hcov hX hq0 hmst
      rcases hD with ⟨vals, m', w', rfl⟩ | ⟨w', rfl⟩ | hD
      · cases hmst
      · cases hmst
      · exact hD evs c'' hs
  · exact .inr h

/-- **All layers composed, the realized prefix the whole run or ending where the CLIF thread
stops** (module doc): layer 4b's refinement ending at a related configuration (`hA`, `hend`,
`arm_alloc_refinesQ`'s form) and layers 2–4a with progress (`isel_alloc_refinesP`); at a related
`Done` configuration after which layers 2–4a give a step of the allocated code, that step is a
thread step (`srcStep_of_mstep`), which `Done` excludes. -/
theorem arm_isel_refines_full {RA : RL} (hgv : RA.gv = fun _ _ => False) (hcov : CoveredCode RA)
    {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
    {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId} {MR : MemRelT}
    {env : Clif.Env} {p : Clif.Program} {slots : List (Clif.SlotId × Nat)} {sb : Nat}
    {syms : String → Option Nat}
    (H : DriverHyp f vc ctx st0 R gn bl A (csem RA.F RA.ctx RA.X) MR env p)
    (hchk : threadCheckBl f bl = true) (hMR : MemRelOk RA.F sb syms f MR)
    (hMRw : ∀ sl cm w, MR sl cm w → Arm.r .ERR w = .None ∧ Arm.CheckSPAlignment w)
    (hX : TlsMemFree RA.X) (hMem : MemRefines RA.F sb syms (csem RA.F RA.ctx RA.X))
    (hMRs : MRStable RA.F MR) (hreg : ∀ off, ArgLoc.stack off ∉ locsOf f.sig)
    (hprep : prepCheck vc RA.vc = true) (halloc : checkAlloc RA.vc RA.rf = .ok ())
    {cs : Clif.State} {B0 : Clif.Block} (hB0 : f.blocks[0]? = some B0)
    (hcall : cs.callers = []) (hfunc : cs.frame.func = f) (hslots : cs.frame.slots = slots)
    (hbody : cs.frame.body = B0.body) (hterm : cs.frame.term = B0.term) {args : List Clif.Val}
    (hregs : Clif.Regs.empty.setMany (B0.params.map (·.1)) args = some cs.frame.regs)
    (hty : args.map (·.ty) = B0.params.map (·.2))
    (hsig : args.map (·.ty) = f.sig.params.map (·.ty))
    {m₀ : Loc → CV} {w₀ : Arm.ArmState} (hmr : MR slots cs.mem w₀)
    (hargs : ArgsAtEntry RA.F f.sig args w₀)
    {ok : ArmState → Lab → Prop} {s : ArmState × Mon} {ls : List Lab} {s' : ArmState × Mon}
    (hP : PRun Policy.arm RA.step ok s ls s') {nA : Nat} {trM : List (List Ev)}
    {cE : MConf CV ArmState} {ψA : Nat × Nat → Nat × Nat}
    (hM : MTRun RA.vc RA.rf RA.sem ckeep (cEvs RA.F RA.ctx) (MConf.init RA.rf m₀ w₀) trM cE)
    (hA : Refines (· = ·) (PrivA RA) (MonPair (evTr (ls.take nA))) (conv trM)
      (conv (evTr (ls.take nA))) ψA)
    (hend : nA = ls.length ∨ (Done RA cE ∧ ∃ t, RelQ RA t cE)) (hnA : nA ≤ ls.length) :
    ∃ k trS t ψ, k ≤ nA ∧ CRun env p (.run cs) trS t ∧
      Refines Maps (PrivA RA) (MonPair (evTr (ls.take nA))) trS (conv (evTr (ls.take k))) ψ ∧
      (k = ls.length ∨ Stop env p t) := by
  obtain ⟨k, trS, t, ψ, hk, hrun, href, hend', -⟩ := arm_isel_refines_fullR hgv hcov H hchk hMR hMRw hX hMem hMRs hreg hprep halloc hB0 hcall hfunc hslots hbody
    hterm hregs hty hsig hmr hargs hP hM hA hend hnA
  exact ⟨k, trS, t, ψ, hk, hrun, href, hend'⟩

end Concurrency.ThreadProgress
