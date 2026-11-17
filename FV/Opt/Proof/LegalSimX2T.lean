import FV.Opt.Proof.LegalSimX2
import FV.Opt.Proof.LegalSimSW
import FV.Opt.LegalExnT

/-!
# The refinement theorems of `Opt.Legal.checkW` with unwinding on `indTB` (#1076)

`check_refinesX`/`check_refinesX2` (`FV/Opt/Proof/LegalSimX.lean`, `LegalSimX2.lean`) are about
`check`'s domain (`indOldB`): no `try_call_indirect`. `checkW_refinesXT`/`checkW_refinesX2T`: the
same refinement with unwinding for a legalisation accepted by the validator `lean-backend` runs
(`checkW`), the handler-edge check with `try_call_indirect` (`exnOkT`), on a function whose
indirect calls have `i128`-free call-site signatures (`indTB`; Rust's `Box<dyn Any>::downcast`
compares two `TypeId`s with `load.i128` and calls the vtable's `type_id` with a
`try_call_indirect`).

* A `try_call_indirect` whose callee returns: `S.sim_tryInd` (`FV/Opt/Proof/LegalSimSW.lean`).
* A `try_call_indirect` whose callee unwinds (`sim_tryInd_raise2`): on `indTB` the call-site
  signature has no `i128`, so the target's call has the same signature and the same argument
  values, resolving to the same extern (`EnvOkX2T.indXT`), which unwinds with the same exception;
  the tables are related (`exnOkT`), and `raise_sim` (stated once for both callee forms) follows
  the handlers.
* `EnvOkX2T`: `EnvOkX2` and the clause `indX` also at `try_call_indirect` sites (`indXT`).
  `EnvOkX.twoT` (one environment), `EnvOkX2.toT` (on `indOldB` the new clause is vacuous).
-/

namespace Opt.Legal.X

open Clif Opt Opt.Legalize128 Opt.Legal

/-! ## The environments' contracts -/

/-- **`EnvOkX2` with indirect calls of `try_call_indirect` sites**: at each `try_call_indirect`
of `f` (call-site signature `d`), an extern that unwinds in `E` at an address unwinds alike in
`E'`. -/
structure EnvOkX2T (E E' : XEnv) (C : Ctx) (p p' : Program) : Prop extends EnvOkX2 E E' C p p' where
  indXT : ∀ B ∈ C.f.blocks, ∀ c args et d, B.term = .tryCallIndirect c args et →
    C.f.sigDecls.lookup et.sig = some d →
    ∀ mem a vals r, externAtRaise E p mem d a vals = some r → externAtRaise E' p' mem d a vals = some r

/-- One environment: `EnvOkX` is `EnvOkX2T` with `E' = E`. -/
theorem EnvOkX.twoT {env : XEnv} {C : Ctx} {p p' : Program} (hE : EnvOkX env C p p') :
    EnvOkX2T env env C p p' where
  toEnvOkX2 := hE.two
  indXT B hB c args et _ ht _ _ _ _ _ hr :=
    externAtRaise_prefix (hE.base.ind ⟨et.sig, .inr ⟨B, hB, c, args, et, ht, rfl⟩⟩).2 hr

/-- On `check`'s domain (`indOldB`: no `try_call_indirect`), `EnvOkX2` is `EnvOkX2T`. -/
theorem EnvOkX2.toT {E E' : XEnv} {C : Ctx} {p p' : Program} (hE : EnvOkX2 E E' C p p')
    (hold : indOldB C.f = true) : EnvOkX2T E E' C p p' where
  toEnvOkX2 := hE
  indXT B hB c args et _ ht := by
    simp only [indOldB, List.all_eq_true, Bool.and_eq_true] at hold
    have := (hold B hB).2
    rw [ht] at this
    cases this

/-! ## A `try_call_indirect` whose callee unwinds -/

theorem tryCallIndRaise_inv {env : XEnv} {p : Program} {m : Mem} {fr : Frame} {c : ValueId}
    {args : List ValueId} {et : ExnTable} {r : Exn × Mem}
    (h : tryCallIndRaise env p m fr c args et = some r) :
    callIndRaise env p m fr et.sig c args = some r := by
  unfold tryCallIndRaise at h
  split at h
  · exact h
  · cases h

/-- An indirect call that unwinds runs an extern of the environment that unwinds. -/
theorem externAtRaise_inv {env : XEnv} {p : Program} {mem : Mem} {d : Signature} {a : Nat}
    {vals : List Val} {x : Exn} {m1 : Mem} (h : externAtRaise env p mem d a vals = some (x, m1)) :
    ∃ name g, env.extern name = some g ∧ g vals mem = .unwound x m1 := by
  unfold externAtRaise at h
  cases hn : (env.names ++ p.externNames).find? (fun n => mem.symbols n == some a) with
  | none => rw [hn] at h; cases h
  | some name =>
    rw [hn] at h
    simp only at h
    cases hg : env.extern name with
    | none => rw [hg] at h; cases h
    | some g =>
      rw [hg] at h
      simp only at h
      split at h
      · cases hgo : g vals mem with
        | unwound e m' =>
          rw [hgo] at h
          cases h
          exact ⟨name, g, hg, hgo⟩
        | returned _ _ => rw [hgo] at h; cases h
        | trapped _ => rw [hgo] at h; cases h
        | stuck _ => rw [hgo] at h; cases h
        | outOfFuel => rw [hgo] at h; cases h
      · cases h

/-- `indTB`: a `try_call_indirect`'s call-site signature has no `i128`. -/
theorem indTB_term_sig {f : Function} (hT : indTB f = true) {B : Block} (hB : B ∈ f.blocks)
    {c : ValueId} {args : List ValueId} {et : ExnTable} (ht : B.term = .tryCallIndirect c args et)
    {d : Signature} (hd : f.sigDecls.lookup et.sig = some d) : sig128 d = false :=
  Bool.eq_false_iff.2 fun h =>
    S.indTB_not_ind128 hT ⟨et.sig, d, .inr ⟨B, hB, c, args, et, ht, rfl⟩, hd, h⟩

/-- **An indirect call whose extern unwinds**, on `indTB` (`sim_callInd_raise2` without
`indOldB`): the target runs the same statement on the same values, which resolves to the same
extern. -/
theorem sim_callInd_raise2T {C : Ctx} (hG : Good C) (hT : indTB C.f = true) {E E' : XEnv}
    {p p' : Program}
    (hE : EnvOkX2T E E' C p p') {fr fr' : Frame} {m : Mem} (hR : FRel C fr fr') {st : Stmt}
    {rest : List Stmt} (hb : fr.body = st :: rest) {sig : Nat} {callee : ValueId}
    {args : List ValueId} (hi : st.inst = .callIndirect sig callee args) {x : Exn} {m1 : Mem}
    (hr : callIndRaise E p m fr sig callee args = some (x, m1)) :
    stepX E p ⟨⟨fr, [], m⟩, []⟩ = .unwound x (leftMem fr m1) ∧
      stepX E' p' ⟨⟨fr', [], m⟩, []⟩ = .unwound x (leftMem fr m1) := by
  constructor
  · simp [stepX, raiseAt?, hb, hi, hr, raiseIn, pendingOf, unwindFrom, leftMem]
  have hcode0 := hR.code
  rw [hb] at hcode0
  obtain ⟨pl, hpl, hseg, -⟩ := code_cons hcode0
  rcases planOf_callIndirect_eq hpl hi with rfl | ⟨d, args', rg, rs, rfl⟩
  rotate_left
  · exact (S.frel_not_callInd128T hR hT hb hpl).elim
  obtain ⟨hs, hdecl⟩ := segOk_callInd hseg
  have hbody := take_drop_eq (l := fr'.body) (n := 1) rfl
  simp only [Plan.len] at hs
  rw [hs, List.singleton_append] at hbody
  obtain ⟨ts2, hb'⟩ : ∃ ts2, fr'.body = st :: ts2 := ⟨_, hbody⟩
  obtain ⟨B, hB, hst⟩ := frel_stmt hR hb
  obtain ⟨sig0, callee0, args0, d0, hi0, -, -, hplain⟩ := planOf_callInd hpl
  rw [hi] at hi0
  cases hi0
  have hreg : ∀ y ∈ callee :: args, fr'.regs y = fr.regs y := fun y hy => by
    have hlt : y < C.T0 := ops_lt hG hB hst (by rw [hi]; simpa [instOps] using hy)
    have hpl' := hplain y (List.mem_append_left _ hy)
    exact hR.peq y hlt (by simpa [Ctx.plain] using hpl')
  obtain ⟨declared, cv, cv64, vals, hd, hc, h64, hv, hf, hx⟩ := callIndRaise_inv hr
  have hex : ∃ B ∈ C.f.blocks, ∃ st ∈ B.body, ∃ sig callee args,
      st.inst = .callIndirect sig callee args := ⟨B, hB, st, hst, sig, callee, args, hi⟩
  have hnames := (hE.base.ind (S.indSite_of_stmt hex)).1
  have hdf : C.f.sigDecls.lookup sig = some declared := by rw [← hR.func]; exact hd
  have hd' : fr'.func.sigDecls.lookup sig = some declared := by
    rw [hR.func', hdecl sig callee args hi, ← hR.func]; exact hd
  have hc' : fr'.get callee = .ok cv := by
    simp only [Frame.get, hreg callee (List.mem_cons_self ..)]; exact hc
  have hv' : fr'.getMany args = .ok vals :=
    (getMany_congr fun y hy => hreg y (List.mem_cons_of_mem _ hy)).trans hv
  have hf' := find?_names hnames (fun n => m.symbols n == some cv64.toNat) hf
  have hr' : callIndRaise E' p' m fr' sig callee args = some (x, m1) := by
    simp only [callIndRaise, hd', hc', h64, hv', Res.ofOption, bind, Res.bind, pure]
    simp only [hf']
    exact hE.indX hex B hB st hst sig callee args declared hi hdf m _ vals _ hx
  simp [stepX, raiseAt?, hb', hi, hr', raiseIn, pendingOf, unwindFrom, leftMem, hR.slots]

/-- **A `try_call_indirect` whose callee unwinds** (on `indTB`, the handler edges checked by
`exnOkT`): the target's call (the same call-site signature, the same argument values) resolves
to the same extern, which unwinds with the same exception; the tables catch it at related
handlers or not at all (`raise_sim`). -/
theorem sim_tryInd_raise2 {C : Ctx} (hG : Good C) (hx : exnOkT C.f C.g C.cert = true)
    (hT : indTB C.f = true) {E E' : XEnv} {p p' : Program} (hE : EnvOkX2T E E' C p p')
    {fr fr' : Frame} {m : Mem} (hR : FRel C fr fr') (hIC : InCode C.g fr') (hb : fr.body = [])
    {c : ValueId} {args : List ValueId} {et : ExnTable} (ht : fr.term = .tryCallIndirect c args et)
    {x : Exn} {m1 : Mem} (hr : tryCallIndRaise E p m fr c args et = some (x, m1)) :
    (stepX E p ⟨⟨fr, [], m⟩, []⟩ = .unwound x (leftMem fr m1) ∧
      stepX E' p' ⟨⟨fr', [], m⟩, []⟩ = .unwound x (leftMem fr m1)) ∨
    (∃ msg, stepX E p ⟨⟨fr, [], m⟩, []⟩ = .stuck msg) ∨
    ∃ fr1 fr1', stepX E p ⟨⟨fr, [], m⟩, []⟩ = .next ⟨⟨fr1, [], m1⟩, []⟩ ∧
      stepX E' p' ⟨⟨fr', [], m⟩, []⟩ = .next ⟨⟨fr1', [], m1⟩, []⟩ ∧
      ((∃ msg, stepX E p ⟨⟨fr1, [], m1⟩, []⟩ = .stuck msg) ∨
        ∃ fr2 fr2', stepX E p ⟨⟨fr1, [], m1⟩, []⟩ = .next ⟨⟨fr2, [], m1⟩, []⟩ ∧
          stepX E' p' ⟨⟨fr1', [], m1⟩, []⟩ = .next ⟨⟨fr2', [], m1⟩, []⟩ ∧
          FRel C fr2 fr2' ∧ InCode C.g fr2') := by
  obtain ⟨B0, hB0, -, hterm⟩ := hR.blk
  have hlt : ∀ y ∈ termOps (.tryCallIndirect c args et), y < C.T0 := fun y hy =>
    term_ops_lt hG hB0 (by rw [← hterm, ht]; exact hy)
  have hltc : c < C.T0 := hlt c (by simp [termOps])
  have hlta : ∀ y ∈ args, y < C.T0 := fun y hy => hlt y (by simp [termOps, hy])
  have hltv : ∀ y ∈ et.vals, y < C.T0 := fun y hy => hlt y (by simp [termOps, hy])
  have hcode := hR.code
  rw [hb, ht] at hcode
  simp only [codeOk] at hcode
  cases ht' : fr'.term
  all_goals first | (rw [ht'] at hcode; simp [termOk] at hcode; done) | skip
  rename_i c' args' et'
  rw [ht'] at hcode
  have hcode0 := hcode
  obtain ⟨hts, hcc, hpc, hsig, -, -, hT0f, hT0g, hzg, hcg, d, B, d', gs, rg, hd, -, hs', hgs, -,
    hdg, hexp, hexpT⟩ := termOk_tryCallInd hcode
  subst c'
  -- the handler tables are related
  have hitems : itemsOk C et.items et'.items = true := by
    obtain ⟨-, hpos⟩ := hIC
    rcases hpos with ⟨B0', hB0', hterm'⟩ | ⟨-, bc, hj⟩
    · rw [hts] at hcode0
      exact exnOkT_itemsInd hx hB0 hB0' (hterm ▸ ht) (hterm' ▸ ht') hcode0
    · rw [ht'] at hj; cases hj
  -- the call-site signature has no `i128`: the same signature and argument values
  have hB0t : B0.term = .tryCallIndirect c args et := by rw [← hterm]; exact ht
  have h128 : sig128 d = false := indTB_term_sig hT hB0 hB0t hd
  have hdd : d' = d := by
    rw [Complete.sigExp_plain h128] at hs'
    exact (Option.some.inj hs').symm
  obtain ⟨gs0, hgs0, hGs⟩ := groups_plain (sig128_params h128)
  rw [hgs] at hgs0
  have hgg : gs0 = gs := (Option.some.inj hgs0).symm
  rw [hgg] at hGs
  -- the source's callee
  obtain ⟨declared, cv, cv64, vals, hdl, hc, h64, hv, hf, hxr⟩ :=
    callIndRaise_inv (tryCallIndRaise_inv hr)
  have hdecl : declared = d := by
    rw [hR.func, hd] at hdl
    exact (Option.some.inj hdl).symm
  rw [hdecl] at hxr
  obtain ⟨vals', hv', hexp'⟩ := expandArgs_holds hR.vrel hR.zero hexp hlta (getMany_holds hv)
  have hvv : vals' = vals := expRel_val hGs (sig128_params h128) hexp'
  -- the target's `try_call_indirect` raises
  have hdt : fr'.func.sigDecls.lookup et'.sig = some d := by
    rw [hR.func', hsig, hdg, hdd]
  have hc' : fr'.get c = .ok cv := by
    simp only [Frame.get, hR.peq c hltc (plain_iff.1 hpc)]; exact hc
  have hv'' : fr'.getMany args' = .ok vals := by rw [← hvv]; exact holds_getMany hv'
  have hname : IndSite C.f et.sig := .inr ⟨B0, hB0, c, args, et, hB0t, rfl⟩
  have hnames := (hE.base.ind ⟨et.sig, hname⟩).1
  have hf' := find?_names hnames (fun n => m.symbols n == some cv64.toNat) hf
  have hxr' := hE.indXT B0 hB0 c args et d hB0t hd m _ vals _ hxr
  have hbc2 := tryNormal_of_noExn (base := fr'.func.freshValue) (expandTry_noExn hexpT)
  have hr' : tryCallIndRaise E' p' m fr' c args' et' = some (x, m1) := by
    simp only [tryCallIndRaise, hdt, hbc2, Res.ofOption, bind, Res.bind, pure]
    simp only [callIndRaise, hdt, hc', h64, hv'', Res.ofOption, bind, Res.bind, pure]
    simp only [hf']
    exact hxr'
  have hpend : pendingOf ⟨fr, [], m⟩ = some et := by simp [pendingOf, hb, ht]
  have hpend' : pendingOf ⟨fr', [], m⟩ = some et' := by simp [pendingOf, hts, ht']
  have hstep : stepX E p ⟨⟨fr, [], m⟩, []⟩ = raiseIn ⟨⟨fr, [], m⟩, []⟩ x m1 := by
    simp [stepX, raiseAt?, hb, ht, hr]
  have hstep' : stepX E' p' ⟨⟨fr', [], m⟩, []⟩ = raiseIn ⟨⟨fr', [], m⟩, []⟩ x m1 := by
    simp [stepX, raiseAt?, hts, ht', hr']
  rw [hstep, hstep']
  obtain ⟨name, g, hg, hgo⟩ := externAtRaise_inv hxr
  exact raise_sim hG hR hpend hpend' hitems hltv hT0f hT0g hzg hcg
    (hE.arity name g hg vals m x m1 hgo)

/-! ## Runs -/

theorem memBounded_raiseInd2 {E : XEnv} (hK : EnvKeepsBoundedX E) {p : Program} {m : Mem}
    {fr : Frame} {c : ValueId} {args : List ValueId} {et : ExnTable} {x : Exn} {m1 : Mem}
    (h : tryCallIndRaise E p m fr c args et = some (x, m1)) (hM : MemBounded m) : MemBounded m1 := by
  obtain ⟨_, _, _, vals, _, _, _, _, _, hx⟩ := callIndRaise_inv (tryCallIndRaise_inv h)
  obtain ⟨name, g, hg, hgo⟩ := externAtRaise_inv hx
  exact hK name g hg vals m x m1 hgo hM

/-- **Runs with unwinding, two environments, on `indTB`** (`sim_runX2` with
`try_call_indirect`). -/
theorem sim_runX2T {C : Ctx} (hG : Good C) (hx : exnOkT C.f C.g C.cert = true)
    (hT128 : indTB C.f = true) {E E' : XEnv}
    {p p' : Program} (hE : EnvOkX2T E E' C p p') :
    ∀ (n : Nat) (fr fr' : Frame) (m : Mem), FRel C fr fr' → InCode C.g fr' → MemBounded m →
      NoMemTrapX E p ⟨fr, [], m⟩ → NoIndInternalX E p C.f ⟨fr, [], m⟩ →
      XSimOut C E' p' fr' m (runLoopX E p n ⟨⟨fr, [], m⟩, []⟩) := by
  have hnr : ∀ B ∈ C.g.blocks, ∀ fn args, B.term ≠ .returnCall fn args :=
    fun B hB => exnOk_noReturnCall (exnOkT_exnOk hx) hB
  have hE2 := hE.base
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro fr fr' m hR hIC hM hT hI
  cases n with
  | zero => trivial
  | succ n =>
  have ihn : ∀ fr1 fr1' m1, FRel C fr1 fr1' → InCode C.g fr1' → MemBounded m1 →
      stepX E p ⟨⟨fr, [], m⟩, []⟩ = .next ⟨⟨fr1, [], m1⟩, []⟩ →
      XSimOut C E' p' fr1' m1 (runLoopX E p n ⟨⟨fr1, [], m1⟩, []⟩) :=
    fun fr1 fr1' m1 hR1 hIC1 hM1 hs => ih n (by omega) fr1 fr1' m1 hR1 hIC1 hM1 (hT.next hs) (hI.next hs)
  cases hra : raiseAt? E p ⟨fr, [], m⟩ with
  | none =>
    have hst : stepX E p ⟨⟨fr, [], m⟩, []⟩ =
        liftStep ⟨⟨fr, [], m⟩, []⟩ (step E.toEnv p ⟨fr, [], m⟩) := by
      simp [stepX, hra]
    have hT0 := hT _ (.refl _)
    have hI0 := hI _ (.refl _)
    by_cases htc : fr.body = [] ∧ ((∃ fn args et, fr.term = .tryCall fn args et) ∨
        ∃ c args et, fr.term = .tryCallIndirect c args et)
    · obtain ⟨hb, hform⟩ := htc
      -- the call of either form of `try_call`, then its pending jump
      have hSS : S.SimStep C E.toEnv E'.toEnv p p' fr' m (step E.toEnv p ⟨fr, [], m⟩) ∧
          ∀ s1, step E.toEnv p ⟨fr, [], m⟩ = .next s1 → s1.callers = [] →
            s1.frame.body = [] ∧ ∃ bc, s1.frame.term = .jump bc := by
        rcases hform with ⟨fn, args, et, ht⟩ | ⟨c, args, et, ht⟩
        · refine ⟨S.sim_try hG hE2 hR hM hb ht, fun s1 hs1 hcl => ?_⟩
          rw [step_term _ _ _ hb] at hs1
          simp only [ht] at hs1
          exact (stepTryCall_next hs1 hcl).2
        · refine ⟨S.sim_tryInd hG hE2 hR hM hb ht hI0, fun s1 hs1 hcl => ?_⟩
          rw [step_term _ _ _ hb] at hs1
          simp only [ht] at hs1
          exact (stepTryCallIndirect_next hs1 hcl).2
      obtain ⟨hSS, hshape⟩ := hSS
      rcases hSS with hS | ⟨s1, hs1, hcl, hM1, fr1', hT1, hS2⟩
      · exact xsim_of_simOut2 hnr hst hS hIC ihn
      · obtain ⟨sf, scl, sm⟩ := s1
        simp only at hcl hM1 hT1 hS2
        subst hcl
        have hst1 : stepX E p ⟨⟨fr, [], m⟩, []⟩ = .next ⟨⟨sf, [], sm⟩, []⟩ := by
          rw [hst, hs1]; simp [liftStep]
        rw [runLoopX_next hst1]
        obtain ⟨k, hk⟩ := tstep_runLoopX hT1
        refine XSimOut.pre hk ?_
        -- the pending jump
        obtain ⟨hb1, bc, hj1⟩ := hshape _ hs1 rfl
        cases n with
        | zero => trivial
        | succ n =>
        have hst2 : stepX E p ⟨⟨sf, [], sm⟩, []⟩ =
            liftStep ⟨⟨sf, [], sm⟩, []⟩ (step E.toEnv p ⟨sf, [], sm⟩) := by
          simp [stepX, raiseAt_jump (env := E) (p := p) (m := sm) hb1 hj1]
        exact xsim_of_simOut2 hnr hst2 hS2 (tstep_inCode hnr hT1 hIC)
          fun fr2 fr2' m2 hR2 hIC2 hM2 hs2 => ih n (by omega) fr2 fr2' m2 hR2 hIC2 hM2
            ((hT.next hst1).next hs2) ((hI.next hst1).next hs2)
    · exact xsim_of_simOut2 hnr hst
        (S.step_sim_outT hG hE2 hT128 hR hM hT0 hI0
          (fun hb fn args et h => htc ⟨hb, .inl ⟨fn, args, et, h⟩⟩)
          (fun hb c args et h => htc ⟨hb, .inr ⟨c, args, et, h⟩⟩))
        hIC ihn
  | some r =>
    obtain ⟨x, m1⟩ := r
    cases hb : fr.body with
    | cons st rest =>
      have hra' := hra
      simp only [raiseAt?, hb] at hra'
      split at hra'
      · rename_i fn args hi
        obtain ⟨h1, h2⟩ := sim_call_raise2 hG hE.toEnvOkX2 hR hb hi hra'
        rw [runLoopX_unwound h1]
        exact ⟨1, runLoopX_unwound h2 0⟩
      · rename_i sig callee args hi
        obtain ⟨h1, h2⟩ := sim_callInd_raise2T hG hT128 hE hR hb hi hra'
        rw [runLoopX_unwound h1]
        exact ⟨1, runLoopX_unwound h2 0⟩
      · cases hra'
    | nil =>
      have hra' := hra
      simp only [raiseAt?, hb] at hra'
      have hcode := hR.code
      rw [hb] at hcode
      simp only [codeOk] at hcode
      split at hra'
      · rename_i fn args ht
        rw [ht] at hcode
        cases ht' : fr'.term <;> rw [ht'] at hcode <;> simp [termOk] at hcode
      · rename_i fn args et ht
        have hM1 := memBounded_raise2 hE.keepX (tryCallRaise_inv hra') hM
        rcases sim_try_raise2 hG (exnOkT_exnOk hx) hE.toEnvOkX2 hR hIC hb ht hra' with
          ⟨h1, h2⟩ | ⟨msg, h1⟩ | ⟨fr1, fr1', h1, h2, h3⟩
        · rw [runLoopX_unwound h1]
          exact ⟨1, runLoopX_unwound h2 0⟩
        · rw [runLoopX_stuck h1]; trivial
        · rw [runLoopX_next h1]
          refine XSimOut.pre (k := 1) (fun q => runLoopX_next h2 q) ?_
          cases n with
          | zero => trivial
          | succ n =>
          rcases h3 with ⟨msg, h3⟩ | ⟨fr2, fr2', h3, h4, hR2, hIC2⟩
          · rw [runLoopX_stuck h3]; trivial
          · rw [runLoopX_next h3]
            refine XSimOut.pre (k := 1) (fun q => runLoopX_next h4 q) ?_
            exact ih n (by omega) fr2 fr2' m1 hR2 hIC2 hM1 ((hT.next h1).next h3)
              ((hI.next h1).next h3)
      · rename_i callee args et ht
        have hM1 := memBounded_raiseInd2 hE.keepX hra' hM
        rcases sim_tryInd_raise2 hG hx hT128 hE hR hIC hb ht hra' with
          ⟨h1, h2⟩ | ⟨msg, h1⟩ | ⟨fr1, fr1', h1, h2, h3⟩
        · rw [runLoopX_unwound h1]
          exact ⟨1, runLoopX_unwound h2 0⟩
        · rw [runLoopX_stuck h1]; trivial
        · rw [runLoopX_next h1]
          refine XSimOut.pre (k := 1) (fun q => runLoopX_next h2 q) ?_
          cases n with
          | zero => trivial
          | succ n =>
          rcases h3 with ⟨msg, h3⟩ | ⟨fr2, fr2', h3, h4, hR2, hIC2⟩
          · rw [runLoopX_stuck h3]; trivial
          · rw [runLoopX_next h3]
            refine XSimOut.pre (k := 1) (fun q => runLoopX_next h4 q) ?_
            exact ih n (by omega) fr2 fr2' m1 hR2 hIC2 hM1 ((hT.next h1).next h3)
              ((hI.next h1).next h3)
      · cases hra'

/-- **The refinement theorem of `Opt.Legal.checkW` with unwinding, two environments, on
`indTB`** (`check_refinesX2` for the validator `lean-backend` runs, `try_call_indirect`
included): for a legalisation `g` of `f` accepted by `checkW` and by the handler-edge check
`exnOkT`, `f`'s indirect calls at `i128`-free call-site signatures (`indTB`), from entry states
of `f` on `args` and of `g` on `args'` (the arguments expanded by the ABI groups of `f`'s
parameters; same slots and memory), whenever the run of `f` with unwinding under `E` returns
within `fuel` steps, the run of `g` with unwinding under `E'` returns the values expanded by the
ABI groups of `f`'s returns with the same memory; whenever it traps, `g`'s traps with the same
code; whenever an exception leaves `f`, the same exception leaves `g` with the same memory.
Premises: `EnvOkX2T`, valid ranges below `2^64`, no load/store trap and no indirect call of a
function of `p` in the source run with unwinding. -/
theorem checkW_refinesX2T {C : Ctx} (hc : checkW C.f C.g C.cert = true)
    (hx : exnOkT C.f C.g C.cert = true) (hT128 : indTB C.f = true)
    {E E' : XEnv} {p p' : Program} (hE : EnvOkX2T E E' C p p') {b b' : Block}
    (hb : C.f.entry? = some b) (hb' : C.g.entry? = some b') {args args' : List Val}
    {fr0 fr0' : Frame} {m : Mem}
    (h1 : fr0.func = C.f) (h2 : fr0.body = b.body) (h3 : fr0.term = b.term)
    (h4 : b.params.map (·.2) = args.map (·.ty))
    (h5 : Regs.empty.setMany (b.params.map (·.1)) args = some fr0.regs)
    (h1' : fr0'.func = C.g) (h2' : fr0'.body = b'.body) (h3' : fr0'.term = b'.term)
    (h5' : Regs.empty.setMany (b'.params.map (·.1)) args' = some fr0'.regs)
    (hsl : fr0'.slots = fr0.slots)
    (hexp : ExpRel ((groups C.f.sig.params).getD []) args args')
    (hM : MemBounded m) (hT : NoMemTrapX E p ⟨fr0, [], m⟩)
    (hI : NoIndInternalX E p C.f ⟨fr0, [], m⟩) (fuel : Nat) :
    (∀ vals m1, runLoopX E p fuel ⟨⟨fr0, [], m⟩, []⟩ = .returned vals m1 →
      ∃ vals', ExpRel ((groups C.f.sig.returns).getD []) vals vals' ∧
        ∃ k, runLoopX E' p' k ⟨⟨fr0', [], m⟩, []⟩ = .returned vals' m1) ∧
    (∀ c, runLoopX E p fuel ⟨⟨fr0, [], m⟩, []⟩ = .trapped c →
      ∃ k, runLoopX E' p' k ⟨⟨fr0', [], m⟩, []⟩ = .trapped c) ∧
    (∀ e m1, runLoopX E p fuel ⟨⟨fr0, [], m⟩, []⟩ = .unwound e m1 →
      ∃ k, runLoopX E' p' k ⟨⟨fr0', [], m⟩, []⟩ = .unwound e m1) := by
  have hG : Good C := checkW_good hc
  obtain ⟨b0, bs, b0', bs', hf, hg, -, hok, -⟩ := hG.blocks
  simp only [Function.entry?, hf, List.head?_cons, Option.some.injEq] at hb
  simp only [Function.entry?, hg, List.head?_cons, Option.some.injEq] at hb'
  subst hb hb'
  have hBmem : b0 ∈ C.f.blocks := by rw [hf]; exact List.mem_cons_self ..
  simp only [blockOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, ite_true] at hok
  obtain ⟨⟨-, hnd'⟩, hok⟩ := hok
  split at hok
  · rename_i gs z rest hgs hbody'
    simp only [Bool.and_eq_true, beq_iff_eq] at hok
    obtain ⟨⟨hep, rfl⟩, hcode⟩ := hok
    simp only [hgs, Option.getD_some] at hexp
    obtain ⟨hty', hbind, hcov⟩ := entry_bind hep hexp h4.symm
    have hnd := params_nodup hG.defs hBmem
    have H0 := holds_setMany hnd h5
    have H0' := holds_setMany hnd' h5'
    -- the target's first step: the pad zero
    have hz : lstep fr0' m = .next { fr0' with regs := fr0'.regs.set C.zero zeroVal, body := rest } m := by
      have hb0 : fr0'.body = C.zeroStmt :: rest := by rw [h2', hbody']
      rw [lstep_eval (m1 := m) (vals := [zeroVal]) hb0 (fun _ _ h => by cases h) rfl rfl]
    have hzT : S.TStep E'.toEnv p' fr0' m
        { fr0' with regs := fr0'.regs.set C.zero zeroVal, body := rest } m :=
      S.TStep.of_lstar (.single hz)
    -- parameters of the target that are values of `f` are the source parameters
    have hpar : ∀ v, v < C.T0 → v ∉ b0.params.map (·.1) → v ∉ b0'.params.map (·.1) := by
      intro v hv hvn hv'
      rcases hcov v hv' with hf' | ⟨u, hu, hvu⟩
      · have := (fresh_spec hf').1; vomega
      · cases hpu : C.pair u with
        | none =>
          simp only [img, hpu, List.mem_singleton] at hvu
          exact hvn (hvu ▸ hu)
        | some ab =>
          obtain ⟨a, b⟩ := ab
          obtain ⟨ha, hb, -⟩ := hG.pair_facts hpu
          simp only [img, hpu, List.mem_cons, List.mem_nil_iff, or_false] at hvu
          rcases hvu with rfl | rfl <;> vomega
    have hR : FRel C fr0 { fr0' with regs := fr0'.regs.set C.zero zeroVal, body := rest } := by
      refine ⟨⟨h1, h1', hsl, ?_, ?_, ?_, by simp⟩, ⟨b0, hBmem, by rw [h2]; exact List.suffix_refl _, h3⟩, ?_⟩
      · intro v x hv hx
        have hvp : v ∈ b0.params.map (·.1) := by
          refine Classical.byContradiction fun hn => ?_
          rw [setMany_other h5 hn] at hx; cases hx
        refine (hbind H0 H0' hnd v hvp x hx).congr fun w hw => ?_
        simp only
        rw [Regs.set_other _ _ fun h => zero_not_img hG hv (by rw [← h]; exact hw)]
      · intro v hv hp
        simp only
        have hvz : v ≠ C.zero := fun h => by have := hG.zero_ge; vomega
        rw [Regs.set_other _ _ hvz]
        by_cases hvp : v ∈ b0.params.map (·.1)
        · obtain ⟨x, hx⟩ := holds_mem H0 v hvp
          have := hbind H0 H0' hnd v hvp x hx
          rw [RelV.plain hp] at this
          rw [this, hx]
        · rw [setMany_other h5 hvp, setMany_other h5' (hpar v hv hvp)]
      · exact srcInv_enter hG.defs hBmem (fun _ _ h => by cases h) h4.symm h5
      · simp only
        rw [h2, h3, h3']
        exact hcode
    have hIC : InCode C.g { fr0' with regs := fr0'.regs.set C.zero zeroVal, body := rest } := by
      refine ⟨h1', .inl ⟨b0', ?_, h3'⟩⟩
      rw [hg]; exact List.mem_cons_self ..
    have hS := sim_runX2T hG hx hT128 hE fuel fr0 _ m hR hIC hM hT hI
    obtain ⟨k0, hk0⟩ := tstep_runLoopX (env := E') hzT
    have hS' := XSimOut.pre hk0 hS
    refine ⟨fun vals m1 h => ?_, fun c h => ?_, fun e m1 h => ?_⟩
    · rw [h] at hS'; exact hS'
    · rw [h] at hS'; exact hS'
    · rw [h] at hS'; exact hS'
  · cases hok

/-- **The refinement theorem of `Opt.Legal.checkW` with unwinding on `indTB`** (one environment:
`checkW_refinesX2T` with `EnvOkX.twoT`; `check_refinesX` for the validator `lean-backend` runs,
`try_call_indirect` included). -/
theorem checkW_refinesXT {C : Ctx} (hc : checkW C.f C.g C.cert = true)
    (hx : exnOkT C.f C.g C.cert = true) (hT128 : indTB C.f = true)
    {env : XEnv} {p p' : Program} (hE : EnvOkX env C p p') {b b' : Block}
    (hb : C.f.entry? = some b) (hb' : C.g.entry? = some b') {args args' : List Val}
    {fr0 fr0' : Frame} {m : Mem}
    (h1 : fr0.func = C.f) (h2 : fr0.body = b.body) (h3 : fr0.term = b.term)
    (h4 : b.params.map (·.2) = args.map (·.ty))
    (h5 : Regs.empty.setMany (b.params.map (·.1)) args = some fr0.regs)
    (h1' : fr0'.func = C.g) (h2' : fr0'.body = b'.body) (h3' : fr0'.term = b'.term)
    (h5' : Regs.empty.setMany (b'.params.map (·.1)) args' = some fr0'.regs)
    (hsl : fr0'.slots = fr0.slots)
    (hexp : ExpRel ((groups C.f.sig.params).getD []) args args')
    (hM : MemBounded m) (hT : NoMemTrapX env p ⟨fr0, [], m⟩)
    (hI : NoIndInternalX env p C.f ⟨fr0, [], m⟩) (fuel : Nat) :
    (∀ vals m1, runLoopX env p fuel ⟨⟨fr0, [], m⟩, []⟩ = .returned vals m1 →
      ∃ vals', ExpRel ((groups C.f.sig.returns).getD []) vals vals' ∧
        ∃ k, runLoopX env p' k ⟨⟨fr0', [], m⟩, []⟩ = .returned vals' m1) ∧
    (∀ c, runLoopX env p fuel ⟨⟨fr0, [], m⟩, []⟩ = .trapped c →
      ∃ k, runLoopX env p' k ⟨⟨fr0', [], m⟩, []⟩ = .trapped c) ∧
    (∀ e m1, runLoopX env p fuel ⟨⟨fr0, [], m⟩, []⟩ = .unwound e m1 →
      ∃ k, runLoopX env p' k ⟨⟨fr0', [], m⟩, []⟩ = .unwound e m1) :=
  checkW_refinesX2T hc hx hT128 hE.twoT hb hb' h1 h2 h3 h4 h5 h1' h2' h3' h5' hsl hexp hM hT hI fuel

end Opt.Legal.X
