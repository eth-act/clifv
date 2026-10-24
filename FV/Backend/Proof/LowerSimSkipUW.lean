import FV.Backend.Proof.LowerSimSkipU
import FV.Backend.Proof.LowerSimUW

/-!
# The driver simulation with unwinding on worlds `W` of the kept code (`skipDead`)

`sim_runXW` (`FV/Backend/Proof/LowerSimUW.lean`) for `vcK`, the VCode without the unused
statements: `LowerSimSkipU.lean`'s argument on worlds `W` (the pairs of worlds of the
non-interference proofs): `VUnwFromWP.deletes`, `stmt_step_raiseWK`, `term_step_try_exnWK`,
`sim_runXWK`.
-/

namespace Backend.Proof.Driver
open Backend Backend.Proof

/-- **A raising run moves to the kept code.** -/
theorem VUnwFromWP.deletes {W : Type} {vc vcK : VCode} {mask : Nat → List Bool}
    {G : Nat → Prop} {sem : ISem CV W} {rz : RaiseFn W} (hD : Deletes vc vcK mask G)
    {P : VConf CV W → Prop}
    (hP : ∀ b k ρ w, P (.run ⟨b, k, ρ, w⟩) → ∀ vb i, vc.blocks[b]? = some vb →
      vb.insts[k]? = some i → (mask b)[k]? = some true)
    {vs vsK : VState CV W} {obj : BitVec 64} {w' : W}
    (h : VUnwFromWP P vc sem rz vs obj w')
    (hC : CorrC mask G (.run vs) (.run vsK)) : VUnwFromW vcK sem rz vsK obj w' := by
  obtain ⟨b, k, ρ, w, vb, info, ops, outs, hs, hp, hvb, hi, hops, hra, hsem, hlen⟩ := h
  obtain ⟨cK, hsK, hCK⟩ := starP_deletes hD hP hs _ hC
  cases cK with
  | run vsK' =>
    obtain ⟨b', k', ρK, wK⟩ := vsK'
    obtain ⟨hb, hk, hw, hρ⟩ := hCK
    simp only at hb hk hw hρ
    subst b' k' wK
    have hmk := hP b k ρ w hp vb _ hvb hi
    obtain ⟨vbK, hvbK, hins, -, -⟩ := hD.blk b vb hvb
    have hiK : vbK.insts[kidx (mask b) k]? = some (.call info) := by
      rw [← Array.getElem?_toList, hins,
        maskKeep_getElem? (by rw [hD.len b vb hvb]; simp) hmk, Array.getElem?_toList]
      exact hi
    have hvu := vuses_congr_of hops (fun u hu => hρ u (hD.uses b vb k _ hvb hi hmk u hu))
    exact ⟨b, _, ρK, w, vbK, info, ops, outs, hsK, hvbK, hiK, hops, by rw [← hvu]; exact hra,
      by rw [← hvu]; exact hsem, hlen⟩
  | ret _ _ => exact absurd hCK id
  | halt _ => exact absurd hCK id

section
variable {f : Clif.Function} {vc vcK : VCode} {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
  {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId} {W : Type}
  {sem : ISem CV W} {MR : MemRelTW W} {env : Clif.XEnv} {p : Clif.Program}
  {slots : List (Clif.SlotId × Nat)} {rz : RaiseFn W} {out : Nat} {drop : Nat → Nat → Bool}

/-- **A raising statement of the kept code** (`stmt_step_raise` for `vcK`). -/
theorem stmt_step_raiseWK (H : DriverHyp f vc ctx st0 R gn bl A sem MR env.toEnv p)
    (HU : UnwShape f vc ctx R gn bl A) (HR : RaiseHypW f sem rz MR env p out)
    (hK : SkipHyp f vc R bl drop vcK) {s : Clif.State} {vsK : VState CV W}
    (hm : MatchK f ctx R gn bl A MR slots (skipMask f R bl vc drop)
      (DeadDef vc (skipMask f R bl vc drop)) s vsK)
    {stm : Clif.Stmt} {rest : List Clif.Stmt} (hbody : s.frame.body = stm :: rest)
    {e : Clif.Exn} {mm : Clif.Mem} (hr : instRaise env p s.frame s.mem stm.inst = some (e, mm)) :
    ∃ obj w', VUnwFromW vcK sem rz vsK obj w' ∧ E2E.ExnRel e obj ∧ MR slots mm w' := by
  have hD := hK.deletes
  obtain ⟨⟨b, k, ρ, w⟩, hC, hM⟩ := hm
  obtain ⟨B, j, hB, hstm, rfl, obj, w', hu, hex, hmr⟩ := stmt_step_raiseWP H HU HR hM hbody hr
  have hjlt : j < B.body.length := (List.getElem?_eq_some_iff.mp hstm).1
  have hdrop : drop b j = false := by
    cases hd : drop b j
    · rfl
    · have hsk := hK.skip b j B stm hd hB hstm
      rw [instRaise_skippable hsk] at hr
      cases hr
  refine ⟨obj, w', VUnwFromWP.deletes hD (fun b' k' ρ' w' hz vb i _ _ => ?_) hu hC, hex, hmr⟩
  obtain ⟨t, ht, ρ'', w'', he⟩ := hz
  simp only [VConf.run.injEq, VState.mk.injEq] at he
  obtain ⟨rfl, rfl, -, -⟩ := he
  rw [skipMask_seg hB hjlt ht, hdrop]; rfl

/-- **A raising `try_call` of the kept code** (`term_step_try_exn` for `vcK`). -/
theorem term_step_try_exnWK (H : DriverHyp f vc ctx st0 R gn bl A sem MR env.toEnv p)
    (HU : UnwShape f vc ctx R gn bl A) (HR : RaiseHypW f sem rz MR env p out)
    (hK : SkipHyp f vc R bl drop vcK) {xs : Clif.XState} {vsK : VState CV W}
    (hm : MatchK f ctx R gn bl A MR slots (skipMask f R bl vc drop)
      (DeadDef vc (skipMask f R bl vc drop)) xs.s vsK) (hbody : xs.s.frame.body = [])
    {et : Clif.ExnTable} (hT : IsTryWith xs.s.frame.term et)
    {e : Clif.Exn} {mm : Clif.Mem} (hr : Clif.raiseAt? env p xs.s = some (e, mm)) :
    ∃ xs1, Clif.stepX env p xs = .next xs1 ∧
      (∀ c, Clif.stepX env p xs1 ≠ .trapped c) ∧ (∀ vals cm, Clif.stepX env p xs1 ≠ .done vals cm) ∧
      (∀ e' cm, Clif.stepX env p xs1 ≠ .unwound e' cm) ∧
      ∀ xs2, Clif.stepX env p xs1 = .next xs2 →
        ∃ vsK', Star (VStep vcK sem) (.run vsK) (.run vsK') ∧
          MatchK f ctx R gn bl A MR slots (skipMask f R bl vc drop)
            (DeadDef vc (skipMask f R bl vc drop)) xs2.s vsK' := by
  have hD := hK.deletes
  obtain ⟨⟨b, k, ρ, w⟩, hC, hM⟩ := hm
  obtain ⟨B, j, hB, hj, hbd, hk⟩ : ∃ B j, f.blocks[b]? = some B ∧ j ≤ B.body.length ∧
      xs.s.frame.body = B.body.drop j ∧ k = pos f R bl b j :=
    let ⟨_, _, _, _, B, j, hB, _, hj, hbd, hk, _⟩ := hM; ⟨B, j, hB, hj, hbd, hk⟩
  have hjn : j = B.body.length := by
    rw [hbd] at hbody
    have := List.drop_eq_nil_iff.mp hbody
    omega
  subst hjn
  subst hk
  have hP := termZone_kept hK H (W := W) hB
  obtain ⟨xs1, h1, h2, h3, h4, h5⟩ := term_step_try_exnWP H HU HR hM hbody hT hr
  refine ⟨xs1, h1, h2, h3, h4, fun xs2 h => ?_⟩
  obtain ⟨vs', hstar, hM'⟩ := h5 xs2 h
  obtain ⟨cK, hsK, hCK⟩ := starP_deletes hD hP hstar _ hC
  cases cK with
  | run vsK' => exact ⟨vsK', hsK, _, hCK, hM'⟩
  | ret _ _ => exact absurd hCK id
  | halt _ => exact absurd hCK id

/-- **Whole runs with unwinding of the kept code** (`sim_runX` for `vcK`). -/
theorem sim_runXWK (H : DriverHyp f vc ctx st0 R gn bl A sem MR env.toEnv p)
    (HU : UnwShape f vc ctx R gn bl A) (HR : RaiseHypW f sem rz MR env p out)
    (hK : SkipHyp f vc R bl drop vcK)
    {cs : Clif.State} (hcf : cs.frame.func = f) (htr : E2E.TrapsExplicitX env p cs) :
    ∀ fuel (xs : Clif.XState) (vs : VState CV W), E2E.ReachX env p cs.toX xs →
      MatchK f ctx R gn bl A MR slots (skipMask f R bl vc drop)
        (DeadDef vc (skipMask f R bl vc drop)) xs.s vs →
      RunOkUW vcK sem rz MR slots vs (Clif.runLoopX env p fuel xs) := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | _ fuel ih =>
  intro xs vs hr hm
  cases fuel with
  | zero => trivial
  | succ n =>
    obtain ⟨vsF, -, hMF⟩ := id hm
    have hfunc : xs.s.frame.func = f := hMF.2.1
    have hcallers : xs.s.callers = [] := hMF.1
    have hslots : xs.s.frame.slots = slots := hMF.2.2.1
    have hnext : ∀ s', Clif.step env.toEnv p xs.s = .next s' →
        (∃ vs', Star (VStep vcK sem) (.run vs) (.run vs') ∧
          MatchK f ctx R gn bl A MR slots (skipMask f R bl vc drop)
            (DeadDef vc (skipMask f R bl vc drop)) s' vs') →
        RunOkUW vcK sem rz MR slots vs (Clif.runLoopX env p (n + 1) xs) := by
      intro s' hs ⟨vs', hstar, hm'⟩
      obtain ⟨t, hx⟩ := stepX_next_of hs
      rw [runLoopX_next hx]
      exact RunOkUW.prefix hstar (ih n (by omega) _ vs' (hr.snoc hx) hm')
    cases hbody : xs.s.frame.body with
    | cons st rest =>
      obtain ⟨-, -, -, -, B, j, hB, -, -, hbd, -⟩ := id hMF
      have hst : st ∈ B.body := by
        rw [hbd] at hbody
        exact List.mem_of_mem_drop (hbody ▸ List.mem_cons_self)
      have hBmem : B ∈ f.blocks := List.mem_of_getElem? hB
      have hext : ∀ fn args, st.inst = .call fn args → ∀ e, xs.s.frame.func.extern? fn = some e →
          p.func? e.name = none := by
        intro fn args hi e he
        exact H.ext B hBmem st hst fn args hi e (hfunc ▸ he)
      have hind : ∀ sig callee args, st.inst = .callIndirect sig callee args → ∀ cv,
          xs.s.frame.get callee = .ok cv → ∀ g ∈ p.funcs, xs.s.mem.symbols g.name ≠ some cv.toNat :=
        fun sig callee args hi => htr.indirect xs st rest sig callee args hr hbody hi
          ⟨B, hcf ▸ hBmem, hst⟩
      obtain ⟨S1, S2⟩ := stmt_stepK hK H hm hbody hind
      cases hs : Clif.step env.toEnv p xs.s with
      | next s' => exact hnext s' hs (S1 s' hs)
      | done vals cm => exact absurd hs (stmt_not_done hbody hext hind)
      | trapped c =>
        rw [runLoopX_trapped (stepX_trapped_of hs)]
        exact S2 c hs (htr.stmt xs c st rest hr hs hbody)
      | stuck msg =>
        cases hra : instRaise env p xs.s.frame xs.s.mem st.inst with
        | none =>
          rw [runLoopX_stuck (stepX_stuck_of hs (by rw [raiseAt_stmt hbody, hra]))]
          trivial
        | some em =>
          obtain ⟨e, mm⟩ := em
          obtain ⟨obj, w', hu, hex, hmr⟩ := stmt_step_raiseWK H HU HR hK hm hbody hra
          have hx : Clif.stepX env p xs =
              .unwound e ((mm.free (xs.s.frame.slots.map (·.2))).leave) := by
            have hpend : Clif.pendingOf xs.s = none := by
              unfold Clif.pendingOf; rw [hbody]
            simp only [Clif.stepX, raiseAt_stmt hbody, hra, Clif.raiseIn, hpend, Option.bind_none,
              hcallers, Clif.unwindFrom]
          rw [runLoopX_unwound hx]
          exact ⟨obj, w', mm, hu, hex, hmr, by rw [hslots]⟩
    | nil =>
      obtain ⟨B, j, hB, hterm, -⟩ := hMF.2.2.2.2
      have hBmem : B ∈ f.blocks := List.mem_of_getElem? hB
      cases hty : xs.s.frame.term.isTry with
      | false =>
        obtain ⟨T1, T2, T3⟩ := term_step_abiK hK H hm hbody hty
        cases hs : Clif.step env.toEnv p xs.s with
        | next s' => exact hnext s' hs (T1 s' hs)
        | done vals cm =>
          rw [runLoopX_done (stepX_done_of hs)]
          obtain ⟨us, outs, w', sv, hret, h1, h2, -, h4, h5, h6⟩ := T2 vals cm hs
          exact ⟨us, outs, w', xs.s.mem, hret, h1, h2, AllHold.prefix_append h4, h5, h6⟩
        | trapped c =>
          rw [runLoopX_trapped (stepX_trapped_of hs)]
          exact T3 c hs
        | stuck msg =>
          have hra : Clif.raiseAt? env p xs.s = none := raiseAt_term_none hbody hty
            (fun fn args ht => H.noTail B hBmem fn args (hterm.symm.trans ht))
          rw [runLoopX_stuck (stepX_stuck_of hs hra)]
          trivial
      | true =>
        obtain ⟨et, hT⟩ : ∃ et, IsTryWith xs.s.frame.term et := by
          cases ht : xs.s.frame.term with
          | tryCall fn args et => exact ⟨et, .inl ⟨fn, args, rfl⟩⟩
          | tryCallIndirect c args et => exact ⟨et, .inr ⟨c, args, rfl⟩⟩
          | _ => rw [ht] at hty; cases hty
        have hind : ∀ callee args, xs.s.frame.term = .tryCallIndirect callee args et → ∀ cv,
            xs.s.frame.get callee = .ok cv → ∀ g ∈ p.funcs,
              xs.s.mem.symbols g.name ≠ some cv.toNat :=
          fun callee args ht => htr.tryIndirect xs callee args et hr hbody ht
            ⟨B, hcf ▸ hBmem, hterm.symm.trans ht⟩
        obtain ⟨Tnd, Tnx⟩ := term_step_tryK hK H hm hbody hT hind
        cases hs : Clif.step env.toEnv p xs.s with
        | next s' =>
          obtain ⟨N1, N2, N3⟩ := Tnx s' hs
          obtain ⟨t, hx⟩ := stepX_next_of hs
          rw [runLoopX_next hx]
          cases n with
          | zero => trivial
          | succ m =>
            have hr' := hr.snoc hx
            cases hs' : Clif.step env.toEnv p s' with
            | next s'' =>
              obtain ⟨vs', hstar, hm'⟩ := N3 s'' hs'
              obtain ⟨t', hx'⟩ := stepX_next_of (xs := ⟨s', t⟩) hs'
              rw [runLoopX_next hx']
              exact RunOkUW.prefix hstar (ih m (by omega) _ vs' (hr'.snoc hx') hm')
            | done vals cm => exact absurd hs' (N2 vals cm)
            | trapped c => exact absurd hs' (N1 c)
            | stuck msg =>
              cases hra' : Clif.raiseAt? env p s' with
              | none =>
                rw [runLoopX_stuck (stepX_stuck_of (xs := ⟨s', t⟩) hs' hra')]
                trivial
              | some em =>
                exfalso
                revert hra'
                rcases hT with ⟨fn, args, hT⟩ | ⟨callee, args, hT⟩
                · obtain ⟨-, hnx⟩ := stepTry_spec (env := env.toEnv) (p := p) (args := args)
                    (et := et) (fun e he => H.tryExt B hBmem fn args et (hterm.symm.trans hT) e
                      (hfunc ▸ he))
                  have hs2 : Clif.stepTerm env.toEnv p xs.s (.tryCall fn args et) = .next s' := by
                    rw [← hT, ← Clif.step_term _ _ _ hbody]; exact hs
                  obtain ⟨-, -, -, -, -, -, -, -, -, rfl⟩ := hnx s' hs2
                  simp [Clif.raiseAt?, tryNext]
                · obtain ⟨-, hnx⟩ := stepTryInd_spec (env := env.toEnv) (p := p) (args := args)
                    (et := et) (hind callee args hT)
                  have hs2 : Clif.stepTerm env.toEnv p xs.s (.tryCallIndirect callee args et) =
                      .next s' := by
                    rw [← hT, ← Clif.step_term _ _ _ hbody]; exact hs
                  obtain ⟨-, -, -, -, -, -, -, -, -, rfl⟩ := hnx s' hs2
                  simp [Clif.raiseAt?, tryNext]
        | done vals cm => exact absurd hs (Tnd vals cm)
        | trapped c =>
          rcases hT with ⟨fn, args, hT⟩ | ⟨callee, args, hT⟩
          · exact absurd (hterm.symm.trans hT)
              (htr.tryCall xs c fn args et hr hs hbody hT B (hcf ▸ hBmem))
          · exact absurd (hterm.symm.trans hT)
              (htr.tryCallInd xs c callee args et hr hs hbody hT B (hcf ▸ hBmem))
        | stuck msg =>
          cases hra : Clif.raiseAt? env p xs.s with
          | none =>
            rw [runLoopX_stuck (stepX_stuck_of hs hra)]
            trivial
          | some em =>
            obtain ⟨e, mm⟩ := em
            obtain ⟨xs1, hx1, hX1, hX2, hX3, hnx1⟩ :=
              term_step_try_exnWK H HU HR hK hm hbody hT hra
            rw [runLoopX_next hx1]
            cases n with
            | zero => trivial
            | succ m =>
              have hr' := hr.snoc hx1
              cases hs1 : Clif.stepX env p xs1 with
              | next xs2 =>
                obtain ⟨vs', hstar, hm'⟩ := hnx1 xs2 hs1
                rw [runLoopX_next hs1]
                exact RunOkUW.prefix hstar (ih m (by omega) _ vs' (hr'.snoc hs1) hm')
              | done vals cm => exact absurd hs1 (hX2 vals cm)
              | unwound e' cm => exact absurd hs1 (hX3 e' cm)
              | trapped c => exact absurd hs1 (hX1 c)
              | stuck msg =>
                rw [runLoopX_stuck hs1]
                trivial

end

end Backend.Proof.Driver
