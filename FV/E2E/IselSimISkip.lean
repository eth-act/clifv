import FV.E2E.IselSimICleanup
import FV.Backend.Proof.LowerSimSkip
import FV.Backend.Proof.CleanupStageFacts

/-!
# The counted CLIF → VCode simulation for the kept code (#552, SEM1)

`sim_runG` (`FV/E2E/IselSimITry.lean`) for `vcK`, the lowering `vc` with the unused statements
skipped (`SkipHyp`, `FV/Backend/Proof/LowerSimSkip.lean`), as `sim_run_abiK` is `sim_run_abi` for
`vcK`: each step of `vc` runs in a zone whose positions are kept (`starP_deletes`), a skipped
statement's step is no step of `vcK` (`stmt_stepK`).

* the counted steps of the kept code: `stmt_stepG_noCallK`, `stmt_stepG_callK`, `term_stepGK`,
  `term_step_tryGK`;
* **`sim_runGK`**;
* **`iselSim_relWI_cleanup_stage`**: `iselSim_relWI_cleanup` for `skipStage f vc`, the code the
  production cleanup stage prunes and prepares.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

theorem skippable_not_callLike {i : Clif.Inst} (h : skippable i = true) (hc : i.isCallLike = true) :
    False := by
  cases i <;> simp_all [skippable, Clif.Inst.isCallLike]

/-- Corresponding configurations stay corresponding with a counter. -/
theorem corrC_counted {W : Type} {mask : Nat → List Bool} {G : Nat → Prop} {vs vsK : VState CV W}
    (n : Nat) (h : CorrC mask G (.run vs) (.run vsK)) :
    CorrC mask G (.run ⟨vs.b, vs.k, vs.ρ, (vs.w, n)⟩) (.run ⟨vsK.b, vsK.k, vsK.ρ, (vsK.w, n)⟩) := by
  obtain ⟨hb, hk, hw, hρ⟩ := h
  exact ⟨hb, hk, by simp only; rw [hw], hρ⟩

section
variable {f : Clif.Function} {vc vcK : VCode} {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
  {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId} {W : Type}
  {env : Clif.Env} {p : Clif.Program} {slots : List (Clif.SlotId × Nat)}
  {drop : Nat → Nat → Bool} {sem semB : Nat → ISem CV W} {MRW : MemRelTW W}

/-- `termZone_kept` for a zone of any world. -/
theorem termZone_keptW {W' : Type} {sw : ISem CV W} {MR : MemRelTW W}
    (hK : SkipHyp f vc R bl drop vcK) (H : DriverHyp f vc ctx st0 R gn bl A sw MR env p)
    {b : Nat} {B : Clif.Block} (hB : f.blocks[b]? = some B) :
    ∀ b' k ρ (w : W'), TermZone vc b (pos f R bl b B.body.length) (.run ⟨b', k, ρ, w⟩) →
      ∀ vb i, vc.blocks[b']? = some vb → vb.insts[k]? = some i →
        (skipMask f R bl vc drop b')[k]? = some true := by
  intro b' k ρ w hz vb i hvb hi
  rcases hz with ⟨k', ρ', w', he, hle⟩ | ⟨e, ρ', w', vb', l, he, hvb', hins⟩
  · simp only [VConf.run.injEq, VState.mk.injEq] at he
    obtain ⟨rfl, rfl, -, -⟩ := he
    obtain ⟨L, hL⟩ := H.blow hB
    obtain ⟨vb0, hvb0, -, -, -, -, -, -, hcode, -, -⟩ := H.shape.blk b' B L hB hL
    rw [hvb] at hvb0; cases hvb0
    have hlt : k < vb.insts.size := (Array.getElem?_eq_some_iff.mp hi).1
    have hsz : vb.insts.size = pos f R bl b' B.body.length + (tseg R bl b').length :=
      (tseg_at hcode).2
    have := skipMask_tseg (vc := vc) (R := R) (bl := bl) (drop := drop)
      (t := k - pos f R bl b' B.body.length) hB
      (by omega)
    rwa [Nat.add_sub_cancel' hle] at this
  · simp only [VConf.run.injEq, VState.mk.injEq] at he
    obtain ⟨rfl, rfl, -, -⟩ := he
    rw [hvb] at hvb'; cases hvb'
    have hD := hK.deletes
    have hlen := hD.len b' vb hvb
    rcases hD.last b' vb hvb with h0 | hl
    · rw [hins] at h0; cases h0
    · rw [hins] at hlen
      simp only [List.size_toArray, List.length_cons, List.length_nil] at hlen
      rw [List.getLast?_eq_getElem?, hlen] at hl
      exact hl

variable (hK : SkipHyp f vc R bl drop vcK)
include hK

/-- **A statement without an extern call of the kept code, counted** (`stmt_stepG_noCall`). -/
theorem stmt_stepG_noCallK (hB : ProbeOf semB sem) {n : Nat}
    (Hb : DriverHyp f vc ctx st0 R gn bl A (semB n) MRW (env.only fun _ _ _ => False) p)
    {s : Clif.State} {b k : Nat} {ρ : Nat → CV} {w : W}
    (hm : MatchK f ctx R gn bl A MRW slots (skipMask f R bl vc drop)
      (DeadDef vc (skipMask f R bl vc drop)) s ⟨b, k, ρ, w⟩)
    {stm : Clif.Stmt} {rest : List Clif.Stmt} (hbody : s.frame.body = stm :: rest)
    (hnc : stm.inst.isCallLike = false)
    (hind : ∀ sig callee args, stm.inst = .callIndirect sig callee args → ∀ cv,
      s.frame.get callee = .ok cv → ∀ g ∈ p.funcs, s.mem.symbols g.name ≠ some cv.toNat) :
    (∀ s', Clif.step env p s = .next s' →
      ∃ b' k' ρ' w', Star (VStep vcK (ISem.counted sem)) (.run ⟨b, k, ρ, (w, n)⟩)
        (.run ⟨b', k', ρ', (w', n)⟩) ∧
        MatchK f ctx R gn bl A MRW slots (skipMask f R bl vc drop)
          (DeadDef vc (skipMask f R bl vc drop)) s' ⟨b', k', ρ', w'⟩) ∧
    (∀ c, Clif.step env p s = .trapped c → explicitTrapInst stm.inst = true →
      VTrapFrom vcK (ISem.counted sem) ⟨b, k, ρ, (w, n)⟩ c) := by
  have hstep : Clif.step (env.only fun _ _ _ => False) p s = Clif.step env p s :=
    step_none_of_callNum (by simp [callNum, hbody, hnc]) (fun _ _ h => by rw [hbody] at h; cases h)
  obtain ⟨S1, S2⟩ := stmt_stepK hK Hb hm hbody hind
  have hp := counted_probe_proj hB n
  refine ⟨fun s' hs => ?_, fun c hs hexp => vTrapFrom_mapW hp (S2 c (hstep.trans hs) hexp)⟩
  obtain ⟨⟨b', k', ρ', w'⟩, hstar, hM⟩ := S1 s' (hstep.trans hs)
  exact ⟨b', k', ρ', w', vstar_mapW hp hstar, hM⟩

/-- **A `call`/`call_indirect` statement of the kept code, counted** (`stmt_stepG_call`; a call
is never skipped). -/
theorem stmt_stepG_callK (hni : NoncallIndep sem) {n : Nat} {s : Clif.State}
    (Hs : DriverHyp f vc ctx st0 R gn bl A (sem n) MRW (env.only (Clif.Invoked env p s)) p)
    (hseg : ∀ b B j stm, f.blocks[b]? = some B → B.body[j]? = some stm →
      stm.inst.isCallLike = true → callsI (seg f R bl b j) = 1)
    {b k : Nat} {ρ : Nat → CV} {w : W}
    (hm : MatchK f ctx R gn bl A MRW slots (skipMask f R bl vc drop)
      (DeadDef vc (skipMask f R bl vc drop)) s ⟨b, k, ρ, w⟩)
    {stm : Clif.Stmt} {rest : List Clif.Stmt} (hbody : s.frame.body = stm :: rest)
    (hcl : stm.inst.isCallLike = true)
    (hind : ∀ sig callee args, stm.inst = .callIndirect sig callee args → ∀ cv,
      s.frame.get callee = .ok cv → ∀ g ∈ p.funcs, s.mem.symbols g.name ≠ some cv.toNat) :
    (∀ s', Clif.step env p s = .next s' →
      ∃ b' k' ρ' w', Star (VStep vcK (ISem.counted sem)) (.run ⟨b, k, ρ, (w, n)⟩)
        (.run ⟨b', k', ρ', (w', n + 1)⟩) ∧
        MatchK f ctx R gn bl A MRW slots (skipMask f R bl vc drop)
          (DeadDef vc (skipMask f R bl vc drop)) s' ⟨b', k', ρ', w'⟩) ∧
    (∀ c, Clif.step env p s = .trapped c → explicitTrapInst stm.inst = true →
      VTrapFrom vcK (ISem.counted sem) ⟨b, k, ρ, (w, n)⟩ c) := by
  have hD := hK.deletes
  have hstep : Clif.step (env.only (Clif.Invoked env p s)) p s = Clif.step env p s :=
    Clif.step_only fun _ _ _ h => h
  obtain ⟨⟨b0, k0, ρ0, w0⟩, hC, hM⟩ := hm
  have hCn := corrC_counted n hC
  obtain ⟨B, j, hB, -, hjlt, hstm, rfl, hnext, htrap⟩ := stmt_run Hs hM hbody hind
  obtain ⟨L, hL⟩ := Hs.blow hB
  obtain ⟨vb, hvb, -, -, -, -, -, -, hcode, htne, -⟩ := Hs.shape.blk b0 B L hB hL
  obtain ⟨hsegat, hlt⟩ := seg_at hcode htne hjlt
  have h1 := hseg b0 B j stm hB hstm hcl
  have hle : callsI (seg f R bl b0 j) ≤ 1 := by omega
  have hdrop : drop b0 j = false := by
    cases hd : drop b0 j
    · rfl
    · exact (skippable_not_callLike (hK.skip b0 j B stm hd hB hstm) hcl).elim
  have hP : ∀ (b' k' : Nat) (ρ' : Nat → CV) (w' : W × Nat),
      AtSeg (V := CV) b0 (pos f R bl b0 j) (seg f R bl b0 j).length
      (.run ⟨b', k', ρ', w'⟩) → ∀ vb' i, vc.blocks[b']? = some vb' →
        vb'.insts[k']? = some i → (skipMask f R bl vc drop b')[k']? = some true := by
    rintro b' k' ρ' w' ⟨t, ht, ρ'', w'', he⟩ vb' i - -
    simp only [VConf.run.injEq, VState.mk.injEq] at he
    obtain ⟨rfl, rfl, -, -⟩ := he
    rw [skipMask_seg hB hjlt ht, hdrop]; rfl
  refine ⟨fun s' hs => ?_, fun c hs hexp => ?_⟩
  · obtain ⟨ρ', w', hsr, hM'⟩ := hnext s' (hstep.trans hs)
    have hsrI : seqRun (ISem.counted sem) (seg f R bl b0 j) ρ0 (w0, n) =
        some (.fall ρ' (w', n + 1)) := by
      rw [seqRun_counted_le1 hni hle ρ0 w0 n, hsr]
      simp [SeqEnd.liftW, h1]
    rw [pos_succ] at hlt hM'
    have hstar := seqRun_fall_starP (vc := vc) hvb hsegat hlt hsrI
    obtain ⟨cK, hsK, hCK⟩ := starP_deletes hD hP hstar _ hCn
    cases cK with
    | run vsK' =>
      obtain ⟨b', k', ρK, wK, nK⟩ := vsK'
      obtain ⟨hb', hk', hw', hρ'⟩ := hCK
      simp only [Prod.mk.injEq] at hb' hk' hw' hρ'
      obtain ⟨rfl, rfl⟩ := hw'
      exact ⟨b', k', ρK, wK, hsK, ⟨b0, _, ρ', wK⟩, ⟨hb', hk', rfl, hρ'⟩, hM'⟩
    | ret _ _ => exact absurd hCK id
    | halt _ => exact absurd hCK id
  · obtain ⟨k', i, ops, ρ₁, w₁, outs, w₂, hsr, htc⟩ := htrap c (hstep.trans hs) hexp
    have hsrI := seqRun_counted_le1 hni hle ρ0 w0 n
    rw [hsr] at hsrI
    obtain ⟨hstar, hk', hi, hops, hsem, -, -⟩ := seqRun_stop_starP (vc := vc) hvb hsegat hsrI
    exact VTrapFromP.deletes hD hP
      ⟨b0, _, ρ₁, _, vb, i, ops, outs, _, hstar, ⟨k', hk', ρ₁, _, rfl⟩, hvb, hi, hops, hsem, htc⟩
      hCn

/-- **A terminator other than `try_call` of the kept code, counted** (`term_stepG`). -/
theorem term_stepGK (hB : ProbeOf semB sem) {n : Nat}
    (Hb : DriverHyp f vc ctx st0 R gn bl A (semB n) MRW (env.only fun _ _ _ => False) p)
    {s : Clif.State} {b k : Nat} {ρ : Nat → CV} {w : W}
    (hm : MatchK f ctx R gn bl A MRW slots (skipMask f R bl vc drop)
      (DeadDef vc (skipMask f R bl vc drop)) s ⟨b, k, ρ, w⟩) (hbody : s.frame.body = [])
    (hnt : s.frame.term.isTry = false) :
    (∀ s', Clif.step env p s = .next s' →
      ∃ b' k' ρ' w', Star (VStep vcK (ISem.counted sem)) (.run ⟨b, k, ρ, (w, n)⟩)
        (.run ⟨b', k', ρ', (w', n)⟩) ∧
        MatchK f ctx R gn bl A MRW slots (skipMask f R bl vc drop)
          (DeadDef vc (skipMask f R bl vc drop)) s' ⟨b', k', ρ', w'⟩) ∧
    (∀ vals cm, Clif.step env p s = .done vals cm →
      ∃ us outs w' sv, VRetFrom vcK (ISem.counted sem) ⟨b, k, ρ, (w, n)⟩ us outs (w', n) ∧
        us.map (·.2) = (List.range us.length).map Reg.x ∧ us.length = outs.length ∧
        s.frame.getMany (sretRet f) = .ok sv ∧ AllHold (vals ++ sv) outs ∧
        MRW slots s.mem w' ∧ cm = (s.mem.free (slots.map (·.2))).leave) ∧
    (∀ c, Clif.step env p s = .trapped c →
      VTrapFrom vcK (ISem.counted sem) ⟨b, k, ρ, (w, n)⟩ c) := by
  have hnr : ∀ fn args, s.frame.body = [] → s.frame.term ≠ .returnCall fn args := by
    intro fn args _ h
    obtain ⟨_, -, -, -, -, -, B, j, hB, hterm, -⟩ := hm
    exact Hb.noTail B (List.mem_of_getElem? hB) fn args (hterm.symm.trans h)
  have hstep : Clif.step (env.only fun _ _ _ => False) p s = Clif.step env p s :=
    step_none_of_callNum (by simp [callNum, hbody, hnt]) hnr
  obtain ⟨T1, T2, T3⟩ := term_step_abiK hK Hb hm hbody hnt
  have hp := counted_probe_proj hB n
  refine ⟨fun s' hs => ?_, fun vals cm hs => ?_,
    fun c hs => vTrapFrom_mapW hp (T3 c (hstep.trans hs))⟩
  · obtain ⟨⟨b', k', ρ', w'⟩, hstar, hM⟩ := T1 s' (hstep.trans hs)
    exact ⟨b', k', ρ', w', vstar_mapW hp hstar, hM⟩
  · obtain ⟨us, outs, w', sv, hret, h1, h2, h3, h4, h5, h6⟩ := T2 vals cm (hstep.trans hs)
    exact ⟨us, outs, w', sv, vRetFrom_mapW hp hret, h1, h2, h3, h4, h5, h6⟩

/-- **`try_call`/`try_call_indirect` step of the kept code, counted** (`term_step_tryG`). -/
theorem term_step_tryGK (hni : NoncallIndep sem) {n : Nat}
    (H : DriverHyp f vc ctx st0 R gn bl A (sem n) MRW env p) (htc : TryCallsOne f)
    {s : Clif.State} {b k : Nat} {ρ : Nat → CV} {w : W}
    (hm : MatchK f ctx R gn bl A MRW slots (skipMask f R bl vc drop)
      (DeadDef vc (skipMask f R bl vc drop)) s ⟨b, k, ρ, w⟩) (hbody : s.frame.body = [])
    {et : Clif.ExnTable} (hT : IsTryWith s.frame.term et)
    (hind : ∀ callee args, s.frame.term = .tryCallIndirect callee args et → ∀ cv,
      s.frame.get callee = .ok cv → ∀ g ∈ p.funcs, s.mem.symbols g.name ≠ some cv.toNat) :
    (∀ vals cm, Clif.step env p s ≠ .done vals cm) ∧
    ∀ s', Clif.step env p s = .next s' →
      (s'.frame.body = [] ∧ ∃ bc, s'.frame.term = .jump bc) ∧
      (∀ c, Clif.step env p s' ≠ .trapped c) ∧ (∀ vals cm, Clif.step env p s' ≠ .done vals cm) ∧
      ∀ s'', Clif.step env p s' = .next s'' →
        ∃ b' k' ρ' w', Star (VStep vcK (ISem.counted sem)) (.run ⟨b, k, ρ, (w, n)⟩)
          (.run ⟨b', k', ρ', (w', n + 1)⟩) ∧
          MatchK f ctx R gn bl A MRW slots (skipMask f R bl vc drop)
            (DeadDef vc (skipMask f R bl vc drop)) s'' ⟨b', k', ρ', w'⟩ := by
  have hD := hK.deletes
  obtain ⟨⟨b0, k0, ρ0, w0⟩, hC, hM⟩ := hm
  have hCn := corrC_counted n hC
  obtain ⟨B, j, hB, hj, hbd, hk⟩ : ∃ B j, f.blocks[b0]? = some B ∧ j ≤ B.body.length ∧
      s.frame.body = B.body.drop j ∧ k0 = pos f R bl b0 j :=
    let ⟨_, _, _, _, B, j, hB, _, hj, hbd, hk, _⟩ := hM; ⟨B, j, hB, hj, hbd, hk⟩
  have hjn : j = B.body.length := by
    rw [hbd] at hbody
    have := List.drop_eq_nil_iff.mp hbody
    omega
  subst hjn
  subst hk
  have hP := termZone_keptW (W' := W × Nat) hK H hB
  obtain ⟨T1, T2⟩ := term_step_tryGP hni H htc hM hbody hT hind
  refine ⟨T1, fun s' hs => ?_⟩
  obtain ⟨N0, N1, N2, N3⟩ := T2 s' hs
  refine ⟨N0, N1, N2, fun s'' hs' => ?_⟩
  obtain ⟨b', k', ρ', w', hstar, hM'⟩ := N3 s'' hs'
  obtain ⟨cK, hsK, hCK⟩ := starP_deletes hD hP hstar _ hCn
  cases cK with
  | run vsK' =>
    obtain ⟨bK, kK, ρK, wK, nK⟩ := vsK'
    obtain ⟨hb', hk', hw', hρ'⟩ := hCK
    simp only [Prod.mk.injEq] at hb' hk' hw' hρ'
    obtain ⟨rfl, rfl⟩ := hw'
    exact ⟨bK, kK, ρK, wK, hsK, ⟨b', k', ρ', wK⟩, ⟨hb', hk', rfl, hρ'⟩, hM'⟩
  | ret _ _ => exact absurd hCK id
  | halt _ => exact absurd hCK id

/-- **Whole runs of the kept code, counted, for a family** (`sim_runG` for `vcK`). -/
theorem sim_runGK (hni : NoncallIndep sem) (hPr : ProbeOf semB sem) {cs : Clif.State}
    (hP : RunPrem env p f cs)
    (Hb : ∀ n, DriverHyp f vc ctx st0 R gn bl A (semB n) MRW (env.only fun _ _ _ => False) p)
    (Hs : ∀ s n, ReachN env p cs s n → DriverHyp f vc ctx st0 R gn bl A (sem n) MRW
      (env.only (Clif.Invoked env p s)) p)
    (hseg : ∀ b B j stm, f.blocks[b]? = some B → B.body[j]? = some stm →
      stm.inst.isCallLike = true → callsI (seg f R bl b j) = 1)
    (htc : TryCallsOne f) :
    ∀ fuel s n b k ρ w, ReachN env p cs s n →
      MatchK f ctx R gn bl A MRW slots (skipMask f R bl vc drop)
        (DeadDef vc (skipMask f R bl vc drop)) s ⟨b, k, ρ, w⟩ →
        RunOkAbi vcK (ISem.counted sem) (fun sl cm w => MRW sl cm w.1) slots (fun _ => True)
          ⟨b, k, ρ, (w, n)⟩
          (Clif.runLoop env p fuel s) := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | _ fuel ih =>
  intro s n b k ρ w hr hm
  cases fuel with
  | zero => trivial
  | succ m =>
    rw [Clif.runLoop_succ]
    obtain ⟨vsF, -, hMF⟩ := id hm
    have hfunc : s.frame.func = f := hMF.2.1
    cases hbody : s.frame.body with
    | nil =>
      cases hty : s.frame.term.isTry with
      | false =>
        obtain ⟨T1, T2, T3⟩ := term_stepGK hK hPr (Hb n) hm hbody hty
        have hc0 : callNum s = 0 := by simp [callNum, hbody, hty]
        cases hs : Clif.step env p s with
        | next s' =>
          obtain ⟨b', k', ρ', w', hstar, hm'⟩ := T1 s' hs
          have h := ih m (by omega) s' (n + callNum s) b' k' ρ' w' (hr.snoc hs) hm'
          rw [hc0, Nat.add_zero] at h
          exact RunOkAbi.prefix hstar h
        | done vals cm =>
          obtain ⟨us, outs, w', sv, hret, h1, h2, hsv, h3, h4, h5⟩ := T2 vals cm hs
          exact ⟨us, outs, (w', n), s.mem, sv, hret, h1, h2, trivial, h3, h4, h5⟩
        | trapped c => exact T3 c hs
        | stuck => trivial
      | true =>
        obtain ⟨B, j, hB, hterm, -⟩ := hMF.2.2.2.2
        have hBmem : B ∈ f.blocks := List.mem_of_getElem? hB
        obtain ⟨et, hT⟩ : ∃ et, IsTryWith s.frame.term et := by
          cases ht : s.frame.term with
          | tryCall fn args et => exact ⟨et, .inl ⟨fn, args, rfl⟩⟩
          | tryCallIndirect c args et => exact ⟨et, .inr ⟨c, args, rfl⟩⟩
          | _ => rw [ht] at hty; cases hty
        have hind : ∀ callee args, s.frame.term = .tryCallIndirect callee args et → ∀ cv,
            s.frame.get callee = .ok cv → ∀ g ∈ p.funcs, s.mem.symbols g.name ≠ some cv.toNat :=
          fun callee args ht => hP.tryIndirect s callee args et hr.reach hbody ht
            ⟨B, hBmem, hterm.symm.trans ht⟩
        obtain ⟨Tnd, Tnx⟩ := term_step_tryGK hK hni (Hs s n hr) htc hm hbody hT hind
        have hst : Clif.step (env.only (Clif.Invoked env p s)) p s = Clif.step env p s :=
          Clif.step_only fun _ _ _ h => h
        have hc1 : callNum s = 1 := by simp [callNum, hbody, hty]
        cases hs : Clif.step env p s with
        | next s' =>
          obtain ⟨⟨hb', bc, ht'⟩, N1, N2, N3⟩ := Tnx s' (hst.trans hs)
          have hst' : Clif.step (env.only (Clif.Invoked env p s)) p s' = Clif.step env p s' := by
            apply Clif.step_only
            intro _ _ _ ⟨_, hI⟩
            simp [hb', ht'] at hI
          have hc0 : callNum s' = 0 := by simp [callNum, hb', ht', Clif.Terminator.isTry]
          cases m with
          | zero => trivial
          | succ m' =>
            show RunOkAbi vcK (ISem.counted sem) (fun sl cm w => MRW sl cm w.1) slots
              (fun _ => True) _ (Clif.runLoop env p (m' + 1) s')
            rw [Clif.runLoop_succ]
            cases hs' : Clif.step env p s' with
            | next s'' =>
              obtain ⟨b', k', ρ', w', hstar, hm'⟩ := N3 s'' (hst'.trans hs')
              have h := ih m' (by omega) s'' (n + callNum s + callNum s') b' k' ρ' w'
                ((hr.snoc hs).snoc hs') hm'
              rw [hc1, hc0, Nat.add_zero] at h
              exact RunOkAbi.prefix hstar h
            | done vals cm => exact absurd (hst'.trans hs') (N2 vals cm)
            | trapped c => exact absurd (hst'.trans hs') (N1 c)
            | stuck => trivial
        | done vals cm => exact absurd (hst.trans hs) (Tnd vals cm)
        | trapped c =>
          rcases hT with ⟨fn, args, hT⟩ | ⟨callee, args, hT⟩
          · exact absurd (hterm.symm.trans hT)
              (hP.tryCall s c fn args et hr.reach hs hbody hT B hBmem)
          · exact absurd (hterm.symm.trans hT)
              (hP.tryCallInd s c callee args et hr.reach hs hbody hT B hBmem)
        | stuck => trivial
    | cons st rest =>
      obtain ⟨-, -, -, -, B, j, hB, -, -, hbd, -⟩ := id hMF
      have hst : st ∈ B.body := by
        rw [hbd] at hbody
        exact List.mem_of_mem_drop (hbody ▸ List.mem_cons_self)
      have hBmem : B ∈ f.blocks := List.mem_of_getElem? hB
      have hext : ∀ fn args, st.inst = .call fn args → ∀ e, s.frame.func.extern? fn = some e →
          p.func? e.name = none := by
        intro fn args hi e he
        exact (Hb n).ext B hBmem st hst fn args hi e (hfunc ▸ he)
      have hind : ∀ sig callee args, st.inst = .callIndirect sig callee args → ∀ cv,
          s.frame.get callee = .ok cv → ∀ g ∈ p.funcs, s.mem.symbols g.name ≠ some cv.toNat :=
        fun sig callee args hi => hP.indirect s st rest sig callee args hr.reach hbody hi
          ⟨B, hBmem, hst⟩
      cases hcl : st.inst.isCallLike with
      | false =>
        obtain ⟨S1, S2⟩ := stmt_stepG_noCallK hK hPr (Hb n) hm hbody hcl hind
        have hc0 : callNum s = 0 := by simp [callNum, hbody, hcl]
        cases hs : Clif.step env p s with
        | next s' =>
          obtain ⟨b', k', ρ', w', hstar, hm'⟩ := S1 s' hs
          have h := ih m (by omega) s' (n + callNum s) b' k' ρ' w' (hr.snoc hs) hm'
          rw [hc0, Nat.add_zero] at h
          exact RunOkAbi.prefix hstar h
        | done vals cm => exact absurd hs (stmt_not_done hbody hext hind)
        | trapped c => exact S2 c hs (hP.stmt s c st rest hr.reach hs hbody)
        | stuck => trivial
      | true =>
        obtain ⟨S1, S2⟩ := stmt_stepG_callK hK hni (Hs s n hr) hseg hm hbody hcl hind
        have hc1 : callNum s = 1 := by simp [callNum, hbody, hcl]
        cases hs : Clif.step env p s with
        | next s' =>
          obtain ⟨b', k', ρ', w', hstar, hm'⟩ := S1 s' hs
          have h := ih m (by omega) s' (n + callNum s) b' k' ρ' w' (hr.snoc hs) hm'
          rw [hc1] at h
          exact RunOkAbi.prefix hstar h
        | done vals cm => exact absurd hs (stmt_not_done hbody hext hind)
        | trapped c => exact S2 c hs (hP.stmt s c st rest hr.reach hs hbody)
        | stuck => trivial

end

/-- **`iselSim_relWI_cleanup` for the code after the skip of unused instructions**
(`skipStage f vc`, which the cleanup stage prunes and prepares). -/
theorem iselSim_relWI_cleanup_stage {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledCleanup f k vc vcp rf af fa fb)
    (hone : InstCallsOne f) (htc : TryCallsOne f)
    {XI : ExtSemI} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    {F : BitVec 64 → Prop} {c : BitVec 64} {args : List Clif.Val} {cs : Clif.State}
    (hX : ∀ s n, ReachN env p cs s n →
      XCallsOk (env.only (Clif.Invoked env p s)) (f.externs.map (·.2))
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n) ∧
      XCallsIndOk (env.only (Clif.Invoked env p s)) (indSigs f)
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n))
    (hsym : ∀ n b, syms n = some b → XI.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {w₀ : Arm.ArmState} (ρ₀ : Nat → CV)
    (hce : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀) (htr : TrapsExplicit env p cs) (fuel : Nat) :
    (∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ us outs w, VRetFrom (skipStage f vc) (valueSemI F ⟨fa.k, af.slotBase⟩ XI)
          ⟨0, 0, ρ₀, (w₀, 0)⟩ us outs w ∧
        us.map (·.2) = (List.range us.length).map Reg.x ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w.1) ∧
    (∀ c', Clif.runLoop env p fuel cs = .trapped c' →
      VTrapFrom (skipStage f vc) (valueSemI F ⟨fa.k, af.slotBase⟩ XI) ⟨0, 0, ρ₀, (w₀, 0)⟩ c') := by
  obtain ⟨ctx, st0, R, gn, bl, A, hshape, hcert, hbr, hsk⟩ := skipStage_spec hc.lowerOk
  rcases hsk with heq | hK
  · rw [heq]
    exact iselSim_relWI_cleanup hsub hc hone htc hX hsym hslot ρ₀ hce hrel hargs htr fuel
  let Γ : Rel := ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩
  have Hb : ∀ n, DriverHyp f vc ctx st0 R gn bl A
      (valueSem F ⟨fa.k, af.slotBase⟩ (XI.at n).noCall)
      (RelW Γ f c) (env.only fun _ _ _ => False) p := fun n =>
    driverHyp_relW_cleanup hsub hc hshape hcert hbr (xCallsOk_none _ _ _ _)
      (xCallsIndOk_none _ _ _ _) hsym hslot
  have Hs : ∀ s n, ReachN env p cs s n → DriverHyp f vc ctx st0 R gn bl A
      (valueSem F ⟨fa.k, af.slotBase⟩ (XI.at n)) (RelW Γ f c) (env.only (Clif.Invoked env p s)) p :=
    fun s n hr => driverHyp_relW_cleanup hsub hc hshape hcert hbr (hX s n hr).1 (hX s n hr).2
      hsym hslot
  have hseg : ∀ b B j stm, f.blocks[b]? = some B → B.body[j]? = some stm →
      stm.inst.isCallLike = true → callsI (seg f R bl b j) = 1 :=
    fun _ _ _ _ hB hstm hcl => segCalls_of (Hb 0) hone hB hstm hcl
  obtain ⟨B0, hent, hbody, hterm, hty, hregs⟩ := hce.entry
  have hB0 : f.blocks[0]? = some B0 := by
    simpa [Clif.Function.entry?, List.head?_eq_getElem?] using hent
  have hP : RunPrem env p f cs := by
    have hf := hce.func
    exact ⟨htr.stmt, fun s c fn args et hr hs hb hT B hB => htr.tryCall s c fn args et hr hs hb hT B
        (hf ▸ hB),
      fun s c callee args et hr hs hb hT B hB =>
        htr.tryCallInd s c callee args et hr hs hb hT B (hf ▸ hB),
      fun s st rest sig callee args hr hb hi ⟨B, hB, hst⟩ =>
        htr.indirect s st rest sig callee args hr hb hi ⟨B, hf ▸ hB, hst⟩,
      fun s callee args et hr hb hT ⟨B, hB, e⟩ =>
        htr.tryIndirect s callee args et hr hb hT ⟨B, hf ▸ hB, e⟩⟩
  have hPr := probeOf_valueSem F ⟨fa.k, af.slotBase⟩ XI
  obtain ⟨k0, ρ₁, w₁, hstar, hm⟩ := entry_stepP (Hb 0)
    (driverSem_valueSem F ⟨fa.k, af.slotBase⟩ (XI.at 0).noCall)
    (memRefines_valueSem _ _ (XI.at 0).noCall hslot hsym) (mrStable_relW Γ f c) hB0 hce.callers
    hce.func rfl hbody hterm hregs hty.symm hce.sig (ρ₀ := ρ₀) hrel hargs
  obtain ⟨⟨b1, k1, ρ1, w1⟩, hsK, hmK⟩ := entry_matchK hK hB0 hbody hstar hm
  have hrun := RunOkAbi.runOk (RunOkAbi.prefix
    (vstar_mapW (counted_probe_proj hPr 0) hsK)
    (sim_runGK hK (noncallIndep_valueSem F ⟨fa.k, af.slotBase⟩ XI) hPr hP Hb Hs hseg htc fuel
      cs 0 b1 k1 ρ1 w1 .refl hmK))
  refine ⟨fun vals cm h => ?_, fun c' h => ?_⟩
  · rw [h] at hrun
    obtain ⟨us, outs, w, cm0, hret, h1, h2, h3, h4, h5⟩ := hrun
    exact ⟨us, outs, w, hret, h1, h2, h3, h5 ▸ memRel_leave (memRel_free h4.1.1 _)⟩
  · rw [h] at hrun
    exact hrun

end E2E
