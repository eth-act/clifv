import FV.Backend.Proof.LowerSimU

/-!
# The driver simulation with unwinding, with the ABI return values (S7)

`sim_runX`/`driver_correctU` (`LowerSimU.lean`) with the `return` step of `term_step_abi`: a
return also returns the frame's `sretRet f` values (`abiTerm`), all held by the VCode return's
use values (`RunOkUAbi`; `sim_run_abi`/`driver_correct_abi`'s counterparts). The values satisfy
`Q` when `Q` holds of them in every state reachable with unwinding (`hQ`; `sret_reachX`).
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof

section
variable {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
  {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId} {sem : Sem}
  {MR : MemRelT} {env : Clif.XEnv} {p : Clif.Program} {slots : List (Clif.SlotId × Nat)}
  {F : BitVec 64 → Prop} {X : ExtSem} {XR : XRaise} {sb : Nat} {syms : String → Option Nat}
  {out : Nat}

/-- `RunOkU` with the ABI return values: a return also returns `sv` (the frame's `sretRet f`
values at the `return`, which satisfy `Q`), all the use values held (`AllHold`). -/
def RunOkUAbi (vc : VCode) (sem : Sem) (XR : XRaise) (MR : MemRelT)
    (slots : List (Clif.SlotId × Nat)) (Q : List Clif.Val → Prop) (vs : VState CV Arm.ArmState) :
    Clif.XOutcome → Prop
  | .returned vals cm => ∃ us outs w cm0 sv, VRetFrom vc sem vs us outs w ∧
      RetPins vals us ∧ us.length = outs.length ∧
      Q sv ∧ AllHold (vals ++ sv) outs ∧ MR slots cm0 w ∧ cm = (cm0.free (slots.map (·.2))).leave
  | .trapped c => VTrapFrom vc sem vs c
  | .unwound e cm => ∃ obj w cm0, E2E.VUnwFrom vc sem XR vs obj w ∧ E2E.ExnRel e obj ∧
      MR slots cm0 w ∧ cm = (cm0.free (slots.map (·.2))).leave
  | .stuck _ | .outOfFuel => True

theorem RunOkUAbi.prefix {Q : List Clif.Val → Prop} {vs vs' : VState CV Arm.ArmState}
    {o : Clif.XOutcome} (h : Star (VStep vc sem) (.run vs) (.run vs'))
    (h' : RunOkUAbi vc sem XR MR slots Q vs' o) : RunOkUAbi vc sem XR MR slots Q vs o := by
  cases o with
  | returned vals cm =>
    obtain ⟨us, outs, w, cm0, sv, hr, h1⟩ := h'
    exact ⟨us, outs, w, cm0, sv, VRetFrom.prefix h hr, h1⟩
  | trapped c => exact VTrapFrom.prefix h h'
  | unwound e cm =>
    obtain ⟨obj, w, cm0, hu, h1⟩ := h'
    exact ⟨obj, w, cm0, E2E.VUnwFrom.prefix h hu, h1⟩
  | _ => trivial

/-- `RunOkUAbi` gives `RunOkU` (the CLIF return values are a prefix of the held ones). -/
theorem RunOkUAbi.runOkU {Q : List Clif.Val → Prop} {vs : VState CV Arm.ArmState}
    {o : Clif.XOutcome} (h : RunOkUAbi vc sem XR MR slots Q vs o) :
    RunOkU vc sem XR MR slots vs o := by
  cases o with
  | returned vals cm =>
    obtain ⟨us, outs, w, cm0, sv, hr, h1, h2, -, h4, h5, h6⟩ := h
    exact ⟨us, outs, w, cm0, hr, h1, h2, AllHold.prefix_append h4, h5, h6⟩
  | trapped c => exact h
  | unwound e cm => exact h
  | _ => trivial

/-- **Whole runs with unwinding, with the ABI return values**: `sim_runX`, and a return also
returns the frame's `sretRet f` values, which satisfy `Q` when `Q` holds of them in every state
reachable with unwinding (`hQ`). -/
theorem sim_runX_abi (H : DriverHyp f vc ctx st0 R gn bl A sem MR env.toEnv p)
    (HU : UnwShape f vc ctx R gn bl A) (HR : RaiseHyp f sem MR env F X XR sb syms out)
    {cs : Clif.State} (hcf : cs.frame.func = f) (htr : E2E.TrapsExplicitX env p cs)
    {Q : List Clif.Val → Prop}
    (hQ : ∀ xs sv, E2E.ReachX env p cs.toX xs → xs.s.frame.getMany (sretRet f) = .ok sv → Q sv) :
    ∀ fuel (xs : Clif.XState) (vs : VState CV Arm.ArmState), E2E.ReachX env p cs.toX xs →
      Match f ctx R gn bl A MR slots xs.s vs →
      RunOkUAbi vc sem XR MR slots Q vs (Clif.runLoopX env p fuel xs) := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | _ fuel ih =>
  intro xs vs hr hm
  cases fuel with
  | zero => trivial
  | succ n =>
    obtain ⟨b, k, ρ, w⟩ := vs
    have hfunc : xs.s.frame.func = f := hm.2.1
    have hcallers : xs.s.callers = [] := hm.1
    have hslots : xs.s.frame.slots = slots := hm.2.2.1
    -- the CLIF step continues: the old simulation (its trap/indirect premises from `htr`)
    have hnext : ∀ s', Clif.step env.toEnv p xs.s = .next s' →
        (∃ vs', Star (VStep vc sem) (.run ⟨b, k, ρ, w⟩) (.run vs') ∧
          Match f ctx R gn bl A MR slots s' vs') →
        RunOkUAbi vc sem XR MR slots Q ⟨b, k, ρ, w⟩ (Clif.runLoopX env p (n + 1) xs) := by
      intro s' hs ⟨vs', hstar, hm'⟩
      obtain ⟨t, hx⟩ := stepX_next_of hs
      rw [runLoopX_next hx]
      exact RunOkUAbi.prefix hstar (ih n (by omega) _ vs' (hr.snoc hx) hm')
    cases hbody : xs.s.frame.body with
    | cons st rest =>
      obtain ⟨-, -, -, -, B, j, hB, -, -, hbd, -⟩ := id hm
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
      obtain ⟨S1, S2⟩ := stmt_step H hm hbody hind
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
          obtain ⟨obj, w', hu, hex, hmr⟩ := stmt_step_raise H HU HR hm hbody hra
          have hx : Clif.stepX env p xs =
              .unwound e ((mm.free (xs.s.frame.slots.map (·.2))).leave) := by
            have hpend : Clif.pendingOf xs.s = none := by
              unfold Clif.pendingOf; rw [hbody]
            simp only [Clif.stepX, raiseAt_stmt hbody, hra, Clif.raiseIn, hpend, Option.bind_none,
              hcallers, Clif.unwindFrom]
          rw [runLoopX_unwound hx]
          exact ⟨obj, w', mm, hu, hex, hmr, by rw [hslots]⟩
    | nil =>
      obtain ⟨B, j, hB, hterm, -⟩ := hm.2.2.2.2
      have hBmem : B ∈ f.blocks := List.mem_of_getElem? hB
      cases hty : xs.s.frame.term.isTry with
      | false =>
        obtain ⟨T1, T2, T3⟩ := term_step_abi H hm hbody hty
        cases hs : Clif.step env.toEnv p xs.s with
        | next s' => exact hnext s' hs (T1 s' hs)
        | done vals cm =>
          rw [runLoopX_done (stepX_done_of hs)]
          obtain ⟨us, outs, w', sv, hret, h1, h2, hsv, h3, h4, h5⟩ := T2 vals cm hs
          exact ⟨us, outs, w', xs.s.mem, sv, hret, h1, h2, hQ xs sv hr hsv, h3, h4, h5⟩
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
        obtain ⟨Tnd, Tnx⟩ := term_step_try H hm hbody hT hind
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
              exact RunOkUAbi.prefix hstar (ih m (by omega) _ vs' (hr'.snoc hx') hm')
            | done vals cm => exact absurd hs' (N2 vals cm)
            | trapped c => exact absurd hs' (N1 c)
            | stuck msg =>
              cases hra' : Clif.raiseAt? env p s' with
              | none =>
                rw [runLoopX_stuck (stepX_stuck_of (xs := ⟨s', t⟩) hs' hra')]
                trivial
              | some em =>
                -- `s'` is at the pending `jump` of the `try_call`: it never raises
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
            obtain ⟨xs1, hx1, hX1, hX2, hX3, hnx1⟩ := term_step_try_exn H HU HR hm hbody hT hra
            rw [runLoopX_next hx1]
            cases n with
            | zero => trivial
            | succ m =>
              have hr' := hr.snoc hx1
              cases hs1 : Clif.stepX env p xs1 with
              | next xs2 =>
                obtain ⟨vs', hstar, hm'⟩ := hnx1 xs2 hs1
                rw [runLoopX_next hs1]
                exact RunOkUAbi.prefix hstar (ih m (by omega) _ vs' (hr'.snoc hs1) hm')
              | done vals cm => exact absurd hs1 (hX2 vals cm)
              | unwound e' cm => exact absurd hs1 (hX3 e' cm)
              | trapped c => exact absurd hs1 (hX1 c)
              | stuck msg =>
                rw [runLoopX_stuck hs1]
                trivial

/-- **The driver lemma with unwinding, with the ABI return values**: `driver_correctU`, and a
return also returns the frame's `sretRet f` values, which satisfy `Q` when `Q` holds of them in
every state reachable with unwinding from the entry (`hQ`). -/
theorem driver_correctU_abi (H : DriverHyp f vc ctx st0 R gn bl A sem MR env.toEnv p)
    (HU : UnwShape f vc ctx R gn bl A) (HR : RaiseHyp f sem MR env F X XR sb syms out)
    (hds : DriverSem sem)
    {cs : Clif.State} {B0 : Clif.Block} (hB0 : f.blocks[0]? = some B0)
    (hcall : cs.callers = []) (hfunc : cs.frame.func = f) (hslots : cs.frame.slots = slots)
    (hbody : cs.frame.body = B0.body) (hterm : cs.frame.term = B0.term) {args : List Clif.Val}
    (hregs : Clif.Regs.empty.setMany (B0.params.map (·.1)) args = some cs.frame.regs)
    (hty : args.map (·.ty) = B0.params.map (·.2))
    (hsig : args.map (·.ty) = f.sig.params.map (·.ty))
    {ρ₀ : Nat → CV} {w₀ : Arm.ArmState} (hmr : MR slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : E2E.TrapsExplicitX env p cs) {Q : List Clif.Val → Prop}
    (hQ : ∀ xs sv, E2E.ReachX env p cs.toX xs → xs.s.frame.getMany (sretRet f) = .ok sv → Q sv)
    (fuel : Nat) :
    RunOkUAbi vc sem XR MR slots Q ⟨0, 0, ρ₀, w₀⟩ (Clif.runLoopX env p fuel cs.toX) := by
  obtain ⟨k, ρ₁, w₁, hstar, hm⟩ := entry_step H hds HR.mem HR.mrs hB0 hcall hfunc hslots hbody
    hterm hregs hty hsig hmr hargs (ρ₀ := ρ₀)
  exact RunOkUAbi.prefix hstar (sim_runX_abi H HU HR hfunc htr hQ fuel cs.toX _ (.refl _) hm)

end

end Backend.Proof.Driver
