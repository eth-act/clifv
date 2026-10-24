import FV.E2E.TrapCallTryStop
import FV.Backend.Proof.LowerSimSkipU

/-!
# A trapping run of the kept code, stopped at the trapping step (`skipDead`)

`driver_trapStop` (`FV/E2E/TrapCallTryStop.lean`) for `vcK`, the VCode without the unused
statements (`SkipHyp`): the raising `tryCall` is in its terminator's code, which the deletion
keeps (`term_step_try_stopK`); the other steps are the kept code's (`stmt_stepK`,
`stmt_step_raiseK`, `term_step_abiK`, `term_step_tryK`).
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof E2E

/-- **A run to a raising `tryCall` moves to the kept code.** -/
theorem VTryRaiseFromP.deletes {vc vcK : VCode} {mask : Nat → List Bool} {G : Nat → Prop}
    {sem : Sem} {XR : XRaise} (hD : Deletes vc vcK mask G)
    {P : VConf CV Arm.ArmState → Prop}
    (hP : ∀ b k ρ w, P (.run ⟨b, k, ρ, w⟩) → ∀ vb i, vc.blocks[b]? = some vb →
      vb.insts[k]? = some i → (mask b)[k]? = some true)
    {vs vsK : VState CV Arm.ArmState} (h : VTryRaiseFromP P vc sem XR vs)
    (hC : CorrC mask G (.run vs) (.run vsK)) : VTryRaiseFrom vcK sem XR vsK := by
  obtain ⟨b, k, ρ, w, vb, info, ti, ops, obj, w', hs, hp, hvb, hi, hops, hra⟩ := h
  obtain ⟨cK, hsK, hCK⟩ := starP_deletes hD hP hs _ hC
  cases cK with
  | run vsK' =>
    obtain ⟨b', k', ρK, wK⟩ := vsK'
    obtain ⟨hb, hk, hw, hρ⟩ := hCK
    simp only at hb hk hw hρ
    subst b' k' wK
    have hmk := hP b k ρ w hp vb _ hvb hi
    obtain ⟨vbK, hvbK, hins, -, -⟩ := hD.blk b vb hvb
    have hiK : vbK.insts[kidx (mask b) k]? = some (.tryCall info ti) := by
      rw [← Array.getElem?_toList, hins,
        maskKeep_getElem? (by rw [hD.len b vb hvb]; simp) hmk, Array.getElem?_toList]
      exact hi
    have hvu := vuses_congr_of hops (fun u hu => hρ u (hD.uses b vb k _ hvb hi hmk u hu))
    exact ⟨b, _, ρK, w, vbK, info, ti, ops, obj, w', hsK, hvbK, hiK, hops,
      by rw [← hvu]; exact hra⟩
  | ret _ _ => exact absurd hCK id
  | halt _ => exact absurd hCK id

section
variable {f : Clif.Function} {vc vcK : VCode} {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
  {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId} {sem : Sem}
  {MR : MemRelT} {env : Clif.XEnv} {p : Clif.Program} {slots : List (Clif.SlotId × Nat)}
  {F : BitVec 64 → Prop} {X : ExtSem} {XR : XRaise} {sb : Nat} {syms : String → Option Nat}
  {out : Nat} {drop : Nat → Nat → Bool}

/-- **A raising `try_call` of the kept code, up to its call** (`term_step_try_stop` for
`vcK`). -/
theorem term_step_try_stopK (H : DriverHyp f vc ctx st0 R gn bl A sem MR env.toEnv p)
    (HU : UnwShape f vc ctx R gn bl A) (HR : RaiseHyp f sem MR env F X XR sb syms out)
    (hK : SkipHyp f vc R bl drop vcK) {s : Clif.State} {vsK : VState CV Arm.ArmState}
    (hm : MatchK f ctx R gn bl A MR slots (skipMask f R bl vc drop)
      (DeadDef vc (skipMask f R bl vc drop)) s vsK) (hbody : s.frame.body = [])
    {et : Clif.ExnTable} (hT : IsTryWith s.frame.term et)
    {e : Clif.Exn} {mm : Clif.Mem} (hr : Clif.raiseAt? env p s = some (e, mm)) :
    VTryRaiseFrom vcK sem XR vsK := by
  have hD := hK.deletes
  obtain ⟨⟨b, k, ρ, w⟩, hC, hM⟩ := hm
  obtain ⟨B, j, hB, hj, hbd, hk⟩ : ∃ B j, f.blocks[b]? = some B ∧ j ≤ B.body.length ∧
      s.frame.body = B.body.drop j ∧ k = pos f R bl b j :=
    let ⟨_, _, _, _, B, j, hB, _, hj, hbd, hk, _⟩ := hM; ⟨B, j, hB, hj, hbd, hk⟩
  have hjn : j = B.body.length := by
    rw [hbd] at hbody
    have := List.drop_eq_nil_iff.mp hbody
    omega
  subst hjn
  subst hk
  exact VTryRaiseFromP.deletes hD (termZone_kept hK H (W := Arm.ArmState) hB)
    (term_step_try_stopP H HU HR hM hbody hT hr) hC

/-- **The simulation of a trapping run of the kept code, stopped at the trapping step**
(`sim_trapStop` for `vcK`). -/
theorem sim_trapStopK {env0 : Clif.Env} {c : Clif.TrapCode} (hp : p.funcs = [])
    (H : DriverHyp f vc ctx st0 R gn bl A sem MR (trapEnv env0 c).toEnv p)
    (HU : UnwShape f vc ctx R gn bl A)
    (HR : RaiseHyp f sem MR (trapEnv env0 c) F X XR sb syms out)
    (hK : SkipHyp f vc R bl drop vcK)
    {cs : Clif.State} (hcf : cs.frame.func = f) (htr : TrapsExplicitCT env0 p cs) :
    ∀ (fuel : Nat) (s : Clif.State) (vs : VState CV Arm.ArmState), Reach env0 p cs s →
      MatchK f ctx R gn bl A MR slots (skipMask f R bl vc drop)
        (DeadDef vc (skipMask f R bl vc drop)) s vs → Clif.runLoop env0 p fuel s = .trapped c →
      VTrapFrom vcK sem vs c ∨ (∃ obj w', VUnwFrom vcK sem XR vs obj w') ∨
        VTryRaiseFrom vcK sem XR vs := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | _ fuel ih =>
  intro s vs hr hm hrun
  cases fuel with
  | zero => simp [Clif.runLoop] at hrun
  | succ n =>
  obtain ⟨vsF, -, hMF⟩ := id hm
  rw [Clif.runLoop_succ] at hrun
  have hrel := step_trapRel env0 c hp s
  have hnx : ∀ s', Clif.step env0 p s = .next s' →
      Clif.step (trapEnv env0 c).toEnv p s = .next s' := by
    intro s' hs
    rcases hrel with e | ⟨e, -⟩
    · rw [e, hs]
    · rw [hs] at e; cases e
  have hcont : ∀ s', Clif.step env0 p s = .next s' → Clif.runLoop env0 p n s' = .trapped c →
      (∃ vs', Star (VStep vcK sem) (.run vs) (.run vs') ∧
        MatchK f ctx R gn bl A MR slots (skipMask f R bl vc drop)
          (DeadDef vc (skipMask f R bl vc drop)) s' vs') →
      VTrapFrom vcK sem vs c ∨ (∃ obj w', VUnwFrom vcK sem XR vs obj w') ∨
        VTryRaiseFrom vcK sem XR vs := by
    intro s' hs hrun' ⟨vs', hstar, hm'⟩
    rcases ih n (by omega) s' vs' (hr.snoc hs) hm' hrun' with h | ⟨o, w', h⟩ | h
    · exact .inl (VTrapFrom.prefix hstar h)
    · exact .inr (.inl ⟨o, w', VUnwFrom.prefix hstar h⟩)
    · exact .inr (.inr (VTryRaiseFrom.prefix hstar h))
  cases hbody : s.frame.body with
  | cons st rest =>
    obtain ⟨-, -, -, -, B, j, hB, -, -, hbd, -⟩ := id hMF
    have hst : st ∈ B.body := by
      rw [hbd] at hbody
      exact List.mem_of_mem_drop (hbody ▸ List.mem_cons_self)
    have hBmem : B ∈ f.blocks := List.mem_of_getElem? hB
    have hind : ∀ sig callee args, st.inst = .callIndirect sig callee args → ∀ cv,
        s.frame.get callee = .ok cv → ∀ g ∈ p.funcs, s.mem.symbols g.name ≠ some cv.toNat :=
      fun sig callee args hi => htr.indirect s st rest sig callee args hr hbody hi
        ⟨B, hcf ▸ hBmem, hst⟩
    obtain ⟨S1, S2⟩ := stmt_stepK hK H hm hbody hind
    cases hs : Clif.step env0 p s with
    | next s' =>
      rw [hs] at hrun
      exact hcont s' hs hrun (S1 s' (hnx s' hs))
    | trapped c' =>
      rw [hs] at hrun
      cases hrun
      rcases hrel with e | ⟨-, m, e⟩
      · rw [hs] at e
        rcases htr.stmt s c st rest hr hs hbody with hx | hx
        · exact .inl (S2 c e hx)
        · exact absurd e (step_call_trap_stuck env0 c hp hbody hx hs)
      · have hra := raiseAt_of_trapRel env0 c hp (fun h => by rw [hbody] at h; cases h) hs e
        rw [raiseAt_stmt hbody] at hra
        obtain ⟨obj, w', hu, -, -⟩ := stmt_step_raiseK H HU HR hK hm hbody hra
        exact .inr (.inl ⟨obj, w', hu⟩)
    | done vals cm => rw [hs] at hrun; cases hrun
    | stuck msg => rw [hs] at hrun; cases hrun
  | nil =>
    obtain ⟨B, j, hB, hterm, -⟩ := hMF.2.2.2.2
    have hBmem : B ∈ f.blocks := List.mem_of_getElem? hB
    cases hty : s.frame.term.isTry with
    | false =>
      obtain ⟨T1, -, T3⟩ := term_step_abiK hK H hm hbody hty
      cases hs : Clif.step env0 p s with
      | next s' =>
        rw [hs] at hrun
        exact hcont s' hs hrun (T1 s' (hnx s' hs))
      | trapped c' =>
        rw [hs] at hrun
        cases hrun
        rcases hrel with e | ⟨-, m, e⟩
        · rw [hs] at e
          exact .inl (T3 c e)
        · have hra := raiseAt_of_trapRel env0 c hp (fun _ => hty) hs e
          rw [raiseAt_term_none hbody hty
            (fun fn args ht => H.noTail B hBmem fn args (hterm.symm.trans ht))] at hra
          cases hra
      | done vals cm => rw [hs] at hrun; cases hrun
      | stuck msg => rw [hs] at hrun; cases hrun
    | true =>
      obtain ⟨et, hT⟩ : ∃ et, IsTryWith s.frame.term et := by
        cases ht : s.frame.term with
        | tryCall fn args et => exact ⟨et, .inl ⟨fn, args, rfl⟩⟩
        | tryCallIndirect c args et => exact ⟨et, .inr ⟨c, args, rfl⟩⟩
        | _ => rw [ht] at hty; cases hty
      have hind : ∀ callee args, s.frame.term = .tryCallIndirect callee args et → ∀ cv,
          s.frame.get callee = .ok cv → ∀ g ∈ p.funcs,
            s.mem.symbols g.name ≠ some cv.toNat :=
        fun callee args ht => htr.tryIndirect s callee args et hr hbody ht
          ⟨B, hcf ▸ hBmem, hterm.symm.trans ht⟩
      obtain ⟨-, Tnx⟩ := term_step_tryK hK H hm hbody hT hind
      cases hs : Clif.step env0 p s with
      | next s' =>
        rw [hs] at hrun
        obtain ⟨-, -, N3⟩ := Tnx s' (hnx s' hs)
        have hs' : ∃ regs bc cm, s' = tryNext s regs bc cm := by
          rw [Clif.step_term _ _ _ hbody] at hs
          rcases hT with ⟨fn, args, ht⟩ | ⟨callee, args, ht⟩
          · rw [ht] at hs
            obtain ⟨-, hnx'⟩ := stepTry_spec (env := env0) (p := p) (args := args) (et := et)
              (fun e he => H.tryExt B hBmem fn args et (hterm.symm.trans ht) e
                (hMF.2.1 ▸ he))
            obtain ⟨-, bc, -, cm, regs, -, -, -, -, rfl⟩ := hnx' s' hs
            exact ⟨regs, bc, cm, rfl⟩
          · rw [ht] at hs
            obtain ⟨-, hnx'⟩ := stepTryInd_spec (env := env0) (p := p) (args := args) (et := et)
              (hind callee args ht)
            obtain ⟨-, bc, -, cm, regs, -, -, -, -, rfl⟩ := hnx' s' hs
            exact ⟨regs, bc, cm, rfl⟩
        obtain ⟨regs, bc, cm, rfl⟩ := hs'
        cases n with
        | zero => simp [Clif.runLoop] at hrun
        | succ m =>
          dsimp only at hrun
          rw [Clif.runLoop_succ] at hrun
          have hrel' := step_trapRel env0 c hp (tryNext s regs bc cm)
          cases hs2 : Clif.step env0 p (tryNext s regs bc cm) with
          | next s'' =>
            rw [hs2] at hrun
            have hs2' : Clif.step (trapEnv env0 c).toEnv p (tryNext s regs bc cm) = .next s'' := by
              rcases hrel' with e | ⟨e, -⟩
              · rw [e, hs2]
              · rw [hs2] at e; cases e
            obtain ⟨vs', hstar, hm'⟩ := N3 s'' hs2'
            rcases ih m (by omega) s'' vs' ((hr.snoc hs).snoc hs2) hm' hrun with h | ⟨o, w', h⟩ | h
            · exact .inl (VTrapFrom.prefix hstar h)
            · exact .inr (.inl ⟨o, w', VUnwFrom.prefix hstar h⟩)
            · exact .inr (.inr (VTryRaiseFrom.prefix hstar h))
          | trapped c' => exact absurd hs2 (step_tryNext_ne_trapped c')
          | done vals cm' => rw [hs2] at hrun; cases hrun
          | stuck msg => rw [hs2] at hrun; cases hrun
      | trapped c' =>
        rw [hs] at hrun
        cases hrun
        rcases hrel with e | ⟨-, m, e⟩
        · rw [hs] at e
          exact absurd e (step_try_trap_stuck env0 c hp hbody hT hs)
        · exact .inr (.inr (term_step_try_stopK H HU HR hK hm hbody hT
            (raiseAt_of_trapRel_try env0 c hp hbody hT hs)))
      | done vals cm => rw [hs] at hrun; cases hrun
      | stuck msg => rw [hs] at hrun; cases hrun

/-- **`sim_trapStopK` from the entry** (`driver_trapStop` for `vcK`). -/
theorem driver_trapStop_skip {env0 : Clif.Env} {c : Clif.TrapCode} (hp : p.funcs = [])
    (H : DriverHyp f vc ctx st0 R gn bl A sem MR (trapEnv env0 c).toEnv p)
    (HU : UnwShape f vc ctx R gn bl A)
    (HR : RaiseHyp f sem MR (trapEnv env0 c) F X XR sb syms out)
    (hK : SkipHyp f vc R bl drop vcK) (hds : DriverSem sem)
    {cs : Clif.State} {B0 : Clif.Block} (hB0 : f.blocks[0]? = some B0)
    (hcall : cs.callers = []) (hfunc : cs.frame.func = f) (hslots : cs.frame.slots = slots)
    (hbody : cs.frame.body = B0.body) (hterm : cs.frame.term = B0.term) {args : List Clif.Val}
    (hregs : Clif.Regs.empty.setMany (B0.params.map (·.1)) args = some cs.frame.regs)
    (hty : args.map (·.ty) = B0.params.map (·.2))
    (hsig : args.map (·.ty) = f.sig.params.map (·.ty))
    {ρ₀ : Nat → CV} {w₀ : Arm.ArmState} (hmr : MR slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀) (htr : TrapsExplicitCT env0 p cs) {fuel : Nat}
    (hrun : Clif.runLoop env0 p fuel cs = .trapped c) :
    VTraps vcK sem ρ₀ w₀ c ∨ (∃ obj w', VUnwinds vcK sem XR ρ₀ w₀ obj w') ∨
      VTryRaiseFrom vcK sem XR ⟨0, 0, ρ₀, w₀⟩ := by
  obtain ⟨k, ρ₁, w₁, hstar, hm⟩ := entry_stepP H hds HR.mem HR.mrs hB0 hcall hfunc hslots hbody
    hterm hregs hty hsig hmr hargs (ρ₀ := ρ₀)
  obtain ⟨vsK, hsK, hmK⟩ := entry_matchK hK hB0 hbody hstar hm
  rcases sim_trapStopK hp H HU HR hK hfunc htr fuel cs _ (.refl _) hmK hrun with
    h | ⟨o, w', h⟩ | h
  · exact .inl (VTrapFrom.prefix hsK h)
  · exact .inr (.inl ⟨o, w', VUnwFrom.prefix hsK h⟩)
  · exact .inr (.inr (VTryRaiseFrom.prefix hsK h))

/-- **`driver_trapStop` for `vc` or its kept code.** -/
theorem driver_trapStop_stage {env0 : Clif.Env} {c : Clif.TrapCode} (hp : p.funcs = [])
    (H : DriverHyp f vc ctx st0 R gn bl A sem MR (trapEnv env0 c).toEnv p)
    (HU : UnwShape f vc ctx R gn bl A)
    (HR : RaiseHyp f sem MR (trapEnv env0 c) F X XR sb syms out)
    (hsk : vcK = vc ∨ SkipHyp f vc R bl drop vcK) (hds : DriverSem sem)
    {cs : Clif.State} {B0 : Clif.Block} (hB0 : f.blocks[0]? = some B0)
    (hcall : cs.callers = []) (hfunc : cs.frame.func = f) (hslots : cs.frame.slots = slots)
    (hbody : cs.frame.body = B0.body) (hterm : cs.frame.term = B0.term) {args : List Clif.Val}
    (hregs : Clif.Regs.empty.setMany (B0.params.map (·.1)) args = some cs.frame.regs)
    (hty : args.map (·.ty) = B0.params.map (·.2))
    (hsig : args.map (·.ty) = f.sig.params.map (·.ty))
    {ρ₀ : Nat → CV} {w₀ : Arm.ArmState} (hmr : MR slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀) (htr : TrapsExplicitCT env0 p cs) {fuel : Nat}
    (hrun : Clif.runLoop env0 p fuel cs = .trapped c) :
    VTraps vcK sem ρ₀ w₀ c ∨ (∃ obj w', VUnwinds vcK sem XR ρ₀ w₀ obj w') ∨
      VTryRaiseFrom vcK sem XR ⟨0, 0, ρ₀, w₀⟩ := by
  rcases hsk with rfl | hK
  · exact driver_trapStop hp H HU HR hds hB0 hcall hfunc hslots hbody hterm hregs hty hsig hmr
      hargs htr hrun
  · exact driver_trapStop_skip hp H HU HR hK hds hB0 hcall hfunc hslots hbody hterm hregs hty
      hsig hmr hargs htr hrun

end

end Backend.Proof.Driver
