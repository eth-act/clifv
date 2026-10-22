import FV.Concurrency.IselSeg
import FV.Concurrency.CorrRefine
import FV.Concurrency.ClifCStepTerm
import FV.Concurrency.Mapping

/-!
# CLIF → VCode with interference: the induction (T2h, #311, layer 2e)

A VCode thread run (`PrepThread.VTRun` under `csem` and its footprint `cEvs`) from a
configuration matched to a CLIF state (`LowerSim.Match`) is realized by a CLIF thread run
(`ClifCStepTerm.CRun`): their traces correspond step by step (`CorrRefine.Corr Maps`) on the whole
VCode trace or on a prefix after which the CLIF thread has no step (`Done`: returned, trapped,
undefined behaviour).

* `SimRes`: that conclusion; `SegRes`: one segment's (a statement's or a terminator's) part of
  it — the whole result, or a CLIF run to a matched state with progress (VCode steps, or a
  shorter body);
* **`simRes_of_seg`**: segment results compose (induction on the trace and the body);
* `pure_seg`: the segment of a pure statement (no events on either side); `term_seg`: a
  terminator (branches through `IselStep.term_matchN`; a return or a trap ends the CLIF
  thread).
-/

namespace Concurrency.IselThread

open Arm ArmThread Prog ClifThread Backend Backend.Proof Backend.Proof.Driver VCodeThread
  PrepThread SegRun IselStep IselCheck IselSeg CorrRefine ClifCStepTerm Code

/-! ## Results -/

/-- The CLIF thread is at an `atomic_cas` on read-only data (outside layer 2's scope: its store
would be stuck exactly when the comparison succeeds). -/
def CasRO (t : TState) : Prop :=
  ∃ s stm rest ty fl pp ex x a n, t = .run s ∧ s.frame.body = stm :: rest ∧
    stm.inst = .atomicCas ty fl pp ex x ∧ IselClif.access s.frame stm.inst = some (a, n) ∧
    s.mem.readonlyAt a n = true

/-- Where a realized prefix may end: the CLIF thread has no step, or is at an `atomic_cas` on
read-only data. -/
def Stop (env : Clif.Env) (p : Clif.Program) (t : TState) : Prop := Done env p t ∨ CasRO t

/-- **The VCode trace `tr` from a match with `s` is realized** (module doc). -/
def SimRes (env : Clif.Env) (p : Clif.Program) (s : Clif.State) (tr : List (List Ev)) : Prop :=
  ∃ n trS t, n ≤ tr.length ∧ CRun env p (.run s) trS t ∧ Corr Maps trS (conv (tr.take n)) ∧
    (n = tr.length ∨ Stop env p t)

/-- **One segment's result** (module doc). -/
def SegRes (env : Clif.Env) (p : Clif.Program) (vc : VCode) (sem : ISem CV ArmState)
    (ev : MInst → List CV → ArmState → List Ev)
    (Mt : Clif.State → VState CV ArmState → Prop) (s : Clif.State) (tr : List (List Ev))
    (cT : VConf CV ArmState) : Prop :=
  SimRes env p s tr ∨
  ∃ n trS s' vs', n ≤ tr.length ∧ CRun env p (.run s) trS (.run s') ∧
    Corr Maps trS (conv (tr.take n)) ∧ Mt s' vs' ∧ VTRun vc sem ev (.run vs') (tr.drop n) cT ∧
    (0 < n ∨ s'.frame.body.length < s.frame.body.length)

theorem conv_append (a b : List (List Ev)) : conv (a ++ b) = conv a ++ conv b :=
  List.map_append

/-- **Segment results compose.** -/
theorem simRes_of_seg {env : Clif.Env} {p : Clif.Program} {vc : VCode}
    {sem : ISem CV ArmState} {ev : MInst → List CV → ArmState → List Ev}
    {Mt : Clif.State → VState CV ArmState → Prop}
    (hseg : ∀ s c tr cT, Mt s c → VTRun vc sem ev (.run c) tr cT → SegRes env p vc sem ev Mt s tr cT)
    (s : Clif.State) (c : VState CV ArmState) (tr : List (List Ev)) (cT : VConf CV ArmState)
    (hm : Mt s c) (hr : VTRun vc sem ev (.run c) tr cT) : SimRes env p s tr := by
  rcases hseg s c tr cT hm hr with h | ⟨n, trS, s', vs', hn, hrun, hcorr, hm', hr', hprog⟩
  · exact h
  · obtain ⟨n', trS', t', hn', hrun', hcorr', hend⟩ := simRes_of_seg hseg s' vs' (tr.drop n) cT hm' hr'
    refine ⟨n + n', trS ++ trS', t', ?_, hrun.append hrun', ?_, ?_⟩
    · simp at hn'; omega
    · rw [List.take_add, conv_append]
      exact hcorr.append hcorr'
    · rcases hend with h | h
      · left; simp at h; omega
      · exact .inr h
termination_by (tr.length, s.frame.body.length)
decreasing_by
  rcases hprog with h | h
  · exact Prod.Lex.left _ _ (by simp; omega)
  · by_cases h0 : n = 0
    · subst h0; simp only [List.drop_zero]; exact Prod.Lex.right _ h
    · exact Prod.Lex.left _ _ (by simp; omega)

/-! ## Statements and terminators without events -/

theorem corr_nil_tgts {trT : List (List Ev)} (h : ∀ e ∈ trT, e = []) :
    Corr Maps ([] : List (List (Prog.Ev SKind BVal))) (conv trT) :=
  Corr.tgts fun x hx => by
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    rw [h e he]; rfl

theorem corr_src_tgts {trT : List (List Ev)} (h : ∀ e ∈ trT, e = []) :
    Corr Maps [([] : List (Prog.Ev SKind BVal))] (conv trT) :=
  .src (corr_nil_tgts h)

theorem take_all_nil {tr : List (List Ev)} {n : Nat} (h : ∀ e ∈ tr, e = []) :
    ∀ e ∈ tr.take n, e = [] := fun e he => h e (List.mem_of_mem_take he)

theorem memInsts_extraOf (results : List Nat) (rss : List (List Reg)) :
    SegShape.memInsts (extraOf results rss) = [] := by
  unfold SegShape.memInsts extraOf
  rw [List.filter_eq_nil_iff]
  intro i hi
  obtain ⟨⟨r, rs⟩, -, h⟩ := List.mem_filterMap.mp hi
  simp only at h
  split at h
  · cases h
  · cases h; simp [akinds]
  · cases h

/-- The instructions of a statement's code with a memory kind are its `memInsts`, renamed. -/
theorem seg_mem {f : Clif.Function} {R : Reg → Reg} {bl : List BLow} {b j : Nat}
    {B : Clif.Block} {stm : Clif.Stmt} {L : BLow} {sl : SLow} (hB : f.blocks[b]? = some B)
    (hL : bl[b]? = some L) (hs : B.body[j]? = some stm) (hsl : L.sl[j]? = some sl)
    {i : MInst} (hi : i ∈ seg f R bl b j) (hk : akinds i ≠ []) :
    i ∈ (SegShape.memInsts sl.st'.emitted.toList).map (·.mapRegs R) := by
  rw [seg_eq hB hL hs hsl] at hi
  obtain ⟨i0, hi0, rfl⟩ := List.mem_map.mp hi
  rw [SegShape.akinds_mapRegs] at hk
  refine List.mem_map.mpr ⟨i0, ?_, rfl⟩
  rcases List.mem_append.mp hi0 with h | h
  · exact List.mem_filter.mpr ⟨h, by simpa using hk⟩
  · have : i0 ∈ SegShape.memInsts (extraOf stm.results sl.rss) :=
      List.mem_filter.mpr ⟨h, by simpa using hk⟩
    rw [memInsts_extraOf] at this; cases this

theorem body_of_step_pure {env : Clif.Env} {p : Clif.Program} {s s' : Clif.State}
    {stm : Clif.Stmt} {rest : List Clif.Stmt} (hb : s.frame.body = stm :: rest)
    (hp : pureInst stm.inst = true) (hs : Clif.step env p s = .next s') :
    s'.frame.body = rest := by
  rw [step_stmt env p s stm rest hb (fun fn args h => by rw [h] at hp; simp [pureInst] at hp)
    (fun sig callee args h => by rw [h] at hp; simp [pureInst] at hp)] at hs
  cases hO : instOutcome env p s.frame s.mem stm.inst with
  | ok r =>
    rw [hO] at hs
    simp only [Clif.StepResult.ofRes, Clif.continueWith] at hs
    split at hs
    · cases hs; rfl
    · cases hs
  | trap c => rw [hO] at hs; cases hs
  | stuck m => rw [hO] at hs; cases hs

theorem res_none_of {r : Clif.StepResult} (h1 : ∀ s', r ≠ .next s') (h2 : ∀ v m, r ≠ .done v m) :
    res r = none := by
  cases r with
  | next s' => exact absurd rfl (h1 s')
  | done v m => exact absurd rfl (h2 v m)
  | _ => rfl

section
variable {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
  {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId}
  {F : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem} {MR : MemRelT} {env : Clif.Env}
  {p : Clif.Program} {slots : List (Clif.SlotId × Nat)}

/-- **The segment of a pure statement**: no events on either side. -/
theorem pure_seg (H : DriverHyp f vc ctx st0 R gn bl A (csem F fc X) MR env p)
    (hchk : threadCheckBl f bl = true) {s : Clif.State} {b k : Nat} {ρ : Nat → CV} {w : ArmState}
    (hm : Match f ctx R gn bl A MR slots s ⟨b, k, ρ, w⟩)
    {stm : Clif.Stmt} {rest : List Clif.Stmt} (hbody : s.frame.body = stm :: rest)
    (hp : pureInst stm.inst = true) {tr : List (List Ev)} {cT : VConf CV ArmState}
    (hr : VTRun vc (csem F fc X) (cEvs F fc) (.run ⟨b, k, ρ, w⟩) tr cT) :
    SegRes env p vc (csem F fc X) (cEvs F fc) (Match f ctx R gn bl A MR slots) s tr cT := by
  have hind : ∀ sig callee args, stm.inst = .callIndirect sig callee args → ∀ cv,
      s.frame.get callee = .ok cv → ∀ g ∈ p.funcs, s.mem.symbols g.name ≠ some cv.toNat :=
    fun sig callee args h => by rw [h] at hp; simp [pureInst] at hp
  have hext : ∀ fn args, stm.inst = .call fn args → ∀ e, s.frame.func.extern? fn = some e →
      p.func? e.name = none := fun fn args h => by rw [h] at hp; simp [pureInst] at hp
  cases hs : Clif.step env p s with
  | next s' =>
    obtain ⟨B, j, ρ', w', hB, hstm, hk, hstar, -, hM⟩ := stmt_matchN H hm hbody hind hs
    obtain ⟨L, hL⟩ := H.blow hB
    obtain ⟨vb, hvb, hsllen, -, -, -, -, -, hcode, htne, -⟩ := H.shape.blk b B L hB hL
    have hjlt : j < B.body.length := (List.getElem?_eq_some_iff.mp hstm).1
    obtain ⟨sl, hsl⟩ : ∃ sl, L.sl[j]? = some sl :=
      ⟨L.sl[j]'(by omega), List.getElem?_eq_getElem _⟩
    have hsegat := (seg_at hcode htne hjlt).1
    have hok := stmtOk_of hchk hB hstm hL hsl
    have hmi : SegShape.memInsts sl.st'.emitted.toList = [] := by
      simp only [stmtOkB, Bool.and_eq_true] at hok
      have h2 := hok.1.1.2
      unfold SegShape.segShape at h2
      have he : SegShape.expect stm.inst = none := by
        cases h : stm.inst <;> rw [h] at hp <;> simp [pureInst] at hp <;> rfl
      rw [he] at h2
      simpa using h2
    have hP : ∀ c : VConf CV ArmState, InSeg b k (seg f R bl b j).length c → NoMemAt vc c := by
      rintro c ⟨i', hi', ρx, wx, rfl⟩ b2 k2 ρ2 w2 he vb2 ins hb2 hins
      cases he
      rw [hvb] at hb2; cases hb2
      rw [hk, hsegat i' hi'] at hins; cases hins
      refine Classical.byContradiction fun hne => ?_
      have := seg_mem hB hL hstm hsl (List.getElem_mem _) hne
      rw [hmi] at this; cases this
    rcases vtrun_follow (hstar.mono hP) hr with ⟨pre, rest', htr, hl, hpe, h1, h2⟩ | ⟨hl, hpe⟩
    · refine .inr ⟨(seg f R bl b j).length, [[]], s', _, by rw [htr]; simp [hl], .cons
        (cstep_pure hbody hp hs) .nil, ?_, hM, ?_, .inr ?_⟩
      · rw [htr, List.take_left' hl]; exact corr_src_tgts hpe
      · rw [htr, List.drop_left' hl]; exact h2
      · rw [body_of_step_pure hbody hp hs, hbody]; simp
    · exact .inl ⟨tr.length, [], .run s, Nat.le_refl _, .nil,
        (by rw [List.take_length]; exact corr_nil_tgts hpe), .inl rfl⟩
  | done v0 m0 => exact absurd hs (stmt_not_done hbody hext hind)
  | trapped c =>
    refine .inl ⟨0, [], .run s, Nat.zero_le _, .nil, .nil, .inr (.inl ?_)⟩
    refine done_of_step (evShape_pure hbody hp) (by rw [hs]; rfl)
  | stuck m =>
    refine .inl ⟨0, [], .run s, Nat.zero_le _, .nil, .nil, .inr (.inl ?_)⟩
    refine done_of_step (evShape_pure hbody hp) (by rw [hs]; rfl)

/-- **The segment of a terminator**: a branch reaches the successor's match without events; a
return or a trap ends the CLIF thread. -/
theorem term_seg (H : DriverHyp f vc ctx st0 R gn bl A (csem F fc X) MR env p)
    (hchk : threadCheckBl f bl = true) {s : Clif.State} {b k : Nat} {ρ : Nat → CV} {w : ArmState}
    (hm : Match f ctx R gn bl A MR slots s ⟨b, k, ρ, w⟩) (hbody : s.frame.body = [])
    {tr : List (List Ev)} {cT : VConf CV ArmState}
    (hr : VTRun vc (csem F fc X) (cEvs F fc) (.run ⟨b, k, ρ, w⟩) tr cT) :
    SegRes env p vc (csem F fc X) (cEvs F fc) (Match f ctx R gn bl A MR slots) s tr cT := by
  obtain ⟨hcall, hfunc, hslots, -, B, j, hB, hterm, -, -, -, -, -⟩ := id hm
  obtain ⟨L, hL⟩ := H.blow hB
  have htk := termOk_of hchk hB hL
  simp only [termOkB, Bool.and_eq_true, Bool.not_eq_true'] at htk
  obtain ⟨⟨hnt, hnrc⟩, hall⟩ := htk
  have hnt' : s.frame.term.isTry = false := by rw [hterm]; exact hnt
  have hnoRC : ∀ fn args, s.frame.term ≠ .returnCall fn args := by
    intro fn args h; rw [hterm] at h; rw [h] at hnrc; cases hnrc
  have htk' : ∀ L', bl[b]? = some L' → ∀ i ∈ L'.tst'.emitted.toList, akinds i = [] := by
    intro L' hL' i hi
    rw [hL] at hL'; cases hL'
    have := List.all_eq_true.mp hall i hi
    simpa using this
  cases hs : Clif.step env p s with
  | next s' =>
    obtain ⟨n, vs', hstar, hn0, hM⟩ := term_matchN H hm hbody hnt' htk' hs
    have hc : CStep env p (.run s) [] (.run s') := by
      refine cstep_term hbody hcall hnoRC hnt' ?_
      rw [Clif.step_term env p s hbody] at hs
      have hne : dests s.frame.term ≠ [] := by
        intro hd
        cases hT : s.frame.term with
        | ret xs => rw [hT] at hs; exact (stepTerm_ret (env := env) (p := p) hcall).1 s' hs
        | trap c => rw [hT] at hs; simp [Clif.stepTerm] at hs
        | returnCall fn args => exact hnoRC fn args hT
        | tryCall _ _ _ => rw [hT] at hnt'; cases hnt'
        | tryCallIndirect _ _ _ => rw [hT] at hnt'; cases hnt'
        | jump bc => rw [hT] at hd; simp [dests] at hd
        | brif c t e => rw [hT] at hd; simp [dests] at hd
        | brTable x d tbl => rw [hT] at hd; simp [dests] at hd
      obtain ⟨-, -, fr2, -, -, -, rfl⟩ := stepTerm_branch hne hs
      rw [Clif.step_term env p s hbody, hs]; rfl
    rcases vtrun_follow hstar hr with ⟨pre, rest', htr, hl, hpe, h1, h2⟩ | ⟨hl, hpe⟩
    · refine .inr ⟨n, [[]], s', vs', by rw [htr]; simp [hl], .cons hc .nil, ?_, hM, ?_, .inl hn0⟩
      · rw [htr, List.take_left' hl]; exact corr_src_tgts hpe
      · rw [htr, List.drop_left' hl]; exact h2
    · exact .inl ⟨tr.length, [], .run s, Nat.le_refl _, .nil,
        (by rw [List.take_length]; exact corr_nil_tgts hpe), .inl rfl⟩
  | done vals cm =>
    have hc : CStep env p (.run s) [] (.ret vals) := by
      refine cstep_term hbody hcall hnoRC hnt' ?_
      rw [hs]
      have hcm : cm.bytes = s.mem.bytes := by
        rw [Clif.step_term env p s hbody] at hs
        cases hT : s.frame.term with
        | ret xs =>
          rw [hT] at hs
          obtain ⟨-, rfl⟩ := (stepTerm_ret (env := env) (p := p) hcall).2.2 vals cm hs
          unfold Clif.Mem.leave
          cases (s.mem.free (s.frame.slots.map (·.2))).place <;> rfl
        | jump bc =>
          rw [hT] at hs
          exact absurd hs ((stepTerm_branch_ne (s := s) (env := env) (p := p)
            (by simp [dests] : dests (Clif.Terminator.jump bc) ≠ [])).1 vals cm)
        | brif c t e =>
          rw [hT] at hs
          exact absurd hs ((stepTerm_branch_ne (s := s) (env := env) (p := p)
            (by simp [dests] : dests (Clif.Terminator.brif c t e) ≠ [])).1 vals cm)
        | brTable x d tbl =>
          rw [hT] at hs
          exact absurd hs ((stepTerm_branch_ne (s := s) (env := env) (p := p)
            (by simp [dests] : dests (Clif.Terminator.brTable x d tbl) ≠ [])).1 vals cm)
        | trap c => rw [hT] at hs; simp [Clif.stepTerm] at hs
        | returnCall fn args => exact absurd hT (hnoRC fn args)
        | tryCall _ _ _ => rw [hT] at hnt'; cases hnt'
        | tryCallIndirect _ _ _ => rw [hT] at hnt'; cases hnt'
      simp [res, hcm]
    refine .inl ⟨0, [[]], .ret vals, Nat.zero_le _, .cons hc .nil, .src .nil, .inr (.inl ?_)⟩
    rintro ⟨evs, t', h⟩
    exact h
  | trapped c =>
    refine .inl ⟨0, [], .run s, Nat.zero_le _, .nil, .nil, .inr (.inl ?_)⟩
    refine done_of_step (evShape_term hbody) (by rw [hs]; rfl)
  | stuck m =>
    refine .inl ⟨0, [], .run s, Nat.zero_le _, .nil, .nil, .inr (.inl ?_)⟩
    refine done_of_step (evShape_term hbody) (by rw [hs]; rfl)

end

end Concurrency.IselThread
