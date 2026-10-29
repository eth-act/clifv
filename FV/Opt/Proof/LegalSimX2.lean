module

public import FV.Opt.Proof.LegalSimX

@[expose] public section

/-!
# The refinement theorem of `Opt.Legal.check` with unwinding, two environments (S10f, #233)

`check_refinesX2`: `Opt.Legal.X.check_refinesX` with a source environment `E` (the run of `f`)
and a target environment `E'` (the run of `g`), as `Opt.Legal.check_refines2` is
`check_refines`'s: the whole-program refinement of the legalised program
(`E2E.LegalProgram.legalProg_refinesX`) runs each activation of a function of the source program
under the environment of the source program's functions, and its legalisation under the
legalised program's.

`EnvOkX2 E E'`: `EnvOk2` of `E.toEnv`/`E'.toEnv` (the steps where no callee unwinds), and for the
unwinding externs: each extern `f` declares that unwinds in `E` on some arguments unwinds in `E'`
on the arguments expanded by its ABI groups with the same exception and memory
(`ExtRaiseRel`), each indirect call site's signature raises alike, `E`'s externs leave
memories below `2^64` when they unwind (`EnvKeepsBoundedX`), and carry the two payload words
(`ExnArityOk E`). The proofs are `FV/Opt/Proof/LegalSimX.lean`'s with the target's steps under
`E'`.
-/

namespace Opt.Legal.X

open Clif Opt Opt.Legalize128 Opt.Legal

/-! ## The environments' contracts -/

/-- The extern `name` (declared with `sig`) unwinds in `E'` on the arguments expanded by the ABI
groups of `sig` where it unwinds in `E`, with the same exception and memory. -/
def ExtRaiseRel (E E' : XEnv) (name : String) (sig : Signature) : Prop :=
  ∀ h, E.extern name = some h → ∃ h', E'.extern name = some h' ∧
    ∀ gs, groups sig.params = some gs → ∀ vals vals' m, vals.map (·.ty) = AbiParam.tys sig.params →
      ExpRel gs vals vals' → ∀ e m', h vals m = .unwound e m' → h' vals' m = .unwound e m'

/-- An extern that unwinds leaves valid ranges below `2^64`. -/
def EnvKeepsBoundedX (E : XEnv) : Prop :=
  ∀ name h, E.extern name = some h → ∀ vals m e m', h vals m = .unwound e m' →
    MemBounded m → MemBounded m'

theorem EnvKeepsAllocsX.bounded {E : XEnv} (h : EnvKeepsAllocsX E) : EnvKeepsBoundedX E :=
  fun name g hg vals m e m' hu hM => memBounded_of_allocs (h name g hg vals m e m' hu) hM

/-- **The environments' side of the refinement with unwinding, source environment `E`, target
environment `E'`.** -/
structure EnvOkX2 (E E' : XEnv) (C : Ctx) (p p' : Program) : Prop where
  base : EnvOk2 E.toEnv E'.toEnv C p p'
  extX : ∀ fn e, C.f.extern? fn = some e → ExtRaiseRel E E' e.name e.sig
  keepX : EnvKeepsBoundedX E
  arity : ExnArityOk E
  indX : (∃ B ∈ C.f.blocks, ∃ st ∈ B.body, ∃ sig callee args,
      st.inst = .callIndirect sig callee args) →
    ∀ B ∈ C.f.blocks, ∀ st ∈ B.body, ∀ sig callee args d,
      st.inst = .callIndirect sig callee args → C.f.sigDecls.lookup sig = some d →
      ∀ mem a vals r, externAtRaise E p mem d a vals = some r → externAtRaise E' p' mem d a vals = some r

/-- One environment: `EnvOkX` is `EnvOkX2` with `E' = E`. -/
theorem EnvOkX.two {env : XEnv} {C : Ctx} {p p' : Program} (hE : EnvOkX env C p p') :
    EnvOkX2 env env C p p' where
  base := hE.base.two
  extX _ _ _ := fun h hh => ⟨h, hh, fun gs hgs vals vals' m hty hexp e m' hu =>
    hE.extX _ h hh _ gs hgs vals vals' m hty hexp e m' hu⟩
  keepX := hE.keepX.bounded
  arity := hE.arity
  indX h _ _ _ _ _ _ _ _ _ _ _ _ _ _ hr :=
    externAtRaise_prefix (hE.base.ind (S.indSite_of_stmt h)).2 hr

/-! ## Raising callees -/

theorem sim_call_raise2 {C : Ctx} (hG : Good C) {E E' : XEnv} {p p' : Program}
    (hE : EnvOkX2 E E' C p p') {fr fr' : Frame} {m : Mem} (hR : FRel C fr fr') {st : Stmt}
    {rest : List Stmt} (hb : fr.body = st :: rest) {fn : FnRef} {args : List ValueId}
    (hi : st.inst = .call fn args) {x : Exn} {m1 : Mem}
    (hr : callRaise E p m fr fn args = some (x, m1)) :
    stepX E p ⟨⟨fr, [], m⟩, []⟩ = .unwound x (leftMem fr m1) ∧
      stepX E' p' ⟨⟨fr', [], m⟩, []⟩ = .unwound x (leftMem fr m1) := by
  constructor
  · simp [stepX, raiseAt?, hb, hi, hr, raiseIn, pendingOf, unwindFrom, leftMem]
  obtain ⟨ext, vals, g, hx, hv, ht, hp, hg, hgo⟩ := callRaise_inv hr
  have hcode0 := hR.code
  rw [hb] at hcode0
  obtain ⟨pl, hpl, hseg, -⟩ := code_cons hcode0
  obtain ⟨e, args', rg, rs, rfl⟩ := planOf_of_call hpl hi
  obtain ⟨args0, gs, hi0, -, hfe, hgs, -, hexp⟩ := planOf_call hpl
  rw [hi] at hi0
  obtain ⟨-, rfl⟩ : fn = fn ∧ args = args0 := by cases hi0; exact ⟨rfl, rfl⟩
  obtain ⟨rs', hs, -, -, s', hs', hfn⟩ := segOk_call hseg
  have hbody := take_drop_eq (l := fr'.body) (n := 1) rfl
  simp only [Plan.len] at hs
  rw [hs] at hbody
  rw [hR.func] at hx
  rw [hfe] at hx
  cases hx
  obtain ⟨B, hB, hst⟩ := frel_stmt hR hb
  have hlt : ∀ y ∈ args, y < C.T0 := fun y hy => ops_lt hG hB hst (by rw [hi]; exact hy)
  obtain ⟨vals', hv', hexp'⟩ := expandArgs_holds hR.vrel hR.zero hexp hlt (getMany_holds hv)
  obtain ⟨gs0, rg0, hgs0, -, hpar', -⟩ := sigExp_spec hs'
  rw [hgs] at hgs0; cases hgs0
  have ht' : vals'.map (·.ty) = AbiParam.tys s'.params := by
    rw [hpar', AbiParam.tys, ← expRel_tys (groups_spec hgs) hexp' ht]
  have hfe' : fr'.func.extern? fn = some { ext with sig := s' } := by rw [hR.func']; exact hfn
  obtain ⟨g', hg', hrel⟩ := hE.extX fn ext hfe g hg
  have hr' : callRaise E' p' m fr' fn args' = some (x, m1) :=
    callRaise_of hfe' (holds_getMany hv') ht' (hE.base.tgt fn _ hfn) hg'
      (hrel gs hgs vals vals' m ht hexp' x m1 hgo)
  simp only [List.singleton_append] at hbody
  obtain ⟨ts2, hb'⟩ : ∃ ts2, fr'.body = { results := rs', inst := .call fn args' } :: ts2 :=
    ⟨_, hbody⟩
  simp [stepX, raiseAt?, hb', hr', raiseIn, pendingOf, unwindFrom, leftMem, hR.slots]

theorem sim_callInd_raise2 {C : Ctx} (hG : Good C) (hold : indOldB C.f = true) {E E' : XEnv}
    {p p' : Program}
    (hE : EnvOkX2 E E' C p p') {fr fr' : Frame} {m : Mem} (hR : FRel C fr fr') {st : Stmt}
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
  · exact (S.frel_not_callInd128 hR hold hb hpl).elim
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

theorem sim_try_raise2 {C : Ctx} (hG : Good C) (hx : exnOk C.f C.g C.cert = true) {E E' : XEnv}
    {p p' : Program} (hE : EnvOkX2 E E' C p p') {fr fr' : Frame} {m : Mem} (hR : FRel C fr fr')
    (hIC : InCode C.g fr') (hb : fr.body = []) {fn : FnRef} {args : List ValueId} {et : ExnTable}
    (ht : fr.term = .tryCall fn args et) {x : Exn} {m1 : Mem}
    (hr : tryCallRaise E p m fr fn args et = some (x, m1)) :
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
  have hlt : ∀ y ∈ args ++ et.vals, y < C.T0 := fun y hy =>
    term_ops_lt hG hB0 (by rw [← hterm, ht]; exact hy)
  have hcode := hR.code
  rw [hb, ht] at hcode
  simp only [codeOk] at hcode
  cases ht' : fr'.term
  all_goals first | (rw [ht'] at hcode; simp [termOk] at hcode; done) | skip
  rename_i fn' args' et'
  rw [ht'] at hcode
  have hcode0 := hcode
  obtain ⟨hts, hfnn, hsig, hblk, hne, hT0f, hT0g, hzg, hcg, e, d', B, s', gs, rg, he, hd', hB,
    hs', hgs, hrg, hfn', htyp, htyr, hexp, hexpT⟩ := termOk_tryCall hcode
  rw [hfnn] at ht' hcode hcode0
  -- the handler tables are related
  have hitems : itemsOk C et.items et'.items = true := by
    obtain ⟨-, hpos⟩ := hIC
    rcases hpos with ⟨B0', hB0', hterm'⟩ | ⟨-, bc, hj⟩
    · rw [hts] at hcode0
      exact exnOk_items hx hB0 hB0' (hterm ▸ ht) (hterm' ▸ ht') hcode0
    · rw [ht'] at hj; cases hj
  -- the source's callee
  have hrc := tryCallRaise_inv hr
  obtain ⟨ext, vals, g, hxe, hv, hty, hp, hg, hgo⟩ := callRaise_inv hrc
  rw [hR.func, he] at hxe
  cases hxe
  obtain ⟨gs0, rg0, hgs0, hrg0, hpar', hret'⟩ := sigExp_spec hs'
  rw [hgs] at hgs0; cases hgs0
  obtain ⟨vals', hv', hexp'⟩ := expandArgs_holds hR.vrel hR.zero hexp
    (fun y hy => hlt y (List.mem_append_left _ hy)) (getMany_holds hv)
  have hty' : vals'.map (·.ty) = AbiParam.tys s'.params := by
    rw [hpar', AbiParam.tys, ← expRel_tys (groups_spec hgs) hexp' hty]
  have hfe' : fr'.func.extern? fn = some { e with sig := s' } := by rw [hR.func']; exact hfn'
  obtain ⟨g', hg', hrel⟩ := hE.extX fn e he g hg
  have hrc' : callRaise E' p' m fr' fn args' = some (x, m1) :=
    callRaise_of hfe' (holds_getMany hv') hty' (hE.base.tgt fn _ hfn') hg'
      (hrel gs hgs vals vals' m hty hexp' x m1 hgo)
  -- the target's `try_call` raises
  have hd2 : fr'.func.sigDecls.lookup et'.sig = some d' := by rw [hR.func', hsig]; exact hd'
  have hbc2 := tryNormal_of_noExn (base := fr'.func.freshValue) (expandTry_noExn hexpT)
  have hr' : tryCallRaise E' p' m fr' fn args' et' = some (x, m1) := by
    simp only [tryCallRaise, hfe', hd2, hbc2, htyp, htyr, Res.ofOption, bind, Res.bind, Res.check,
      beq_self_eq_true, Bool.and_self, ite_true, pure]
    exact hrc'
  have hpend : pendingOf ⟨fr, [], m⟩ = some et := by simp [pendingOf, hb, ht]
  have hpend' : pendingOf ⟨fr', [], m⟩ = some et' := by simp [pendingOf, hts, ht']
  have hstep : stepX E p ⟨⟨fr, [], m⟩, []⟩ = raiseIn ⟨⟨fr, [], m⟩, []⟩ x m1 := by
    simp [stepX, raiseAt?, hb, ht, hr]
  have hstep' : stepX E' p' ⟨⟨fr', [], m⟩, []⟩ = raiseIn ⟨⟨fr', [], m⟩, []⟩ x m1 := by
    simp [stepX, raiseAt?, hts, ht', hr']
  rw [hstep, hstep']
  rcases catch?_rel (e := x) hitems with ⟨hn, hn'⟩ | ⟨d, d'', hc, hc', hdo⟩
  · -- nothing catches: both frames are left
    refine .inl ⟨?_, ?_⟩
    · simp [raiseIn, hpend, catchIn, hn, unwindFrom, leftMem]
    · simp [raiseIn, hpend', catchIn, hn', unwindFrom, leftMem, hR.slots]
  -- related handlers
  simp only [destOk, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hdo
  obtain ⟨⟨hblkd, hned⟩, hdo⟩ := hdo
  split at hdo
  · rename_i Bh hBh
    simp only [beq_iff_eq] at hdo
    cases hth : tryHandler d fr.func.freshValue with
    | trap c => exact absurd hth (tryHandler_ne_trap _ _ c)
    | stuck msg =>
      refine .inr (.inl ⟨msg, ?_⟩)
      simp [raiseIn, hpend, catchIn, hc, hth, bind, Res.bind, XStepResult.ofRes]
    | ok bc =>
    have hbcE := tryHandler_inv hth
    have hth' := tryHandler_of_noRet (base := fr'.func.freshValue) (expandExn_noRet hdo)
    generalize hbc'e : ({ block := d''.block, args := d''.args.map (exnId fr'.func.freshValue) } :
      BlockCall) = bc' at hth'
    have hpay := hE.arity e.name g hg vals m x m1 hgo
    obtain ⟨ρ1, hs⟩ := setMany_of_len fr.regs
      (rs := (List.range x.payload.length).map (fr.func.freshValue + ·)) (vs := x.payload)
      (by simp)
    obtain ⟨ρ1', hs'⟩ := setMany_of_len fr'.regs
      (rs := (List.range x.payload.length).map (fr'.func.freshValue + ·)) (vs := x.payload)
      (by simp)
    have hfv : fr.func.freshValue = C.f.freshValue := by rw [hR.func]
    have hfv' : fr'.func.freshValue = C.g.freshValue := by rw [hR.func']
    refine .inr (.inr ⟨{ fr with regs := ρ1, body := [], term := .jump bc },
      { fr' with regs := ρ1', body := [], term := .jump bc' }, ?_, ?_, ?_⟩)
    · simp [raiseIn, hpend, catchIn, hc, hth, hs, bind, Res.bind, Res.ofOption, pure,
        XStepResult.ofRes]
    · simp [raiseIn, hpend', catchIn, hc', hth', hs', bind, Res.bind, Res.ofOption, pure,
        XStepResult.ofRes]
    -- the pending jumps
    have hCR := crel_bind hG hR.toCRel hs hs'
      (fun v hv => by have := (mem_range_map hv).1; rw [hfv] at this; omega)
      (fun w hw => fresh_of_ge (base' := C.g.freshValue) hT0g hzg hcg
        (by have := (mem_range_map hw).1; rw [hfv'] at this; exact this))
      [] (.jump bc) [] (.jump bc')
    have hsrc : stepX E p ⟨⟨{ fr with regs := ρ1, body := [], term := .jump bc }, [], m1⟩, []⟩ =
        liftStep ⟨⟨{ fr with regs := ρ1, body := [], term := .jump bc }, [], m1⟩, []⟩
          (StepResult.ofRes (enterBlock { fr with regs := ρ1, body := [], term := .jump bc } bc)
            fun fr2 => .next ⟨fr2, [], m1⟩) := by
      simp only [stepX, raiseAt_jump (env := E) (p := p) (m := m1)
        (fr := { fr with regs := ρ1, body := [], term := .jump bc }) rfl rfl]
      rw [step_term _ _ _ rfl]
      rfl
    have htgt : stepX E' p' ⟨⟨{ fr' with regs := ρ1', body := [], term := .jump bc' }, [], m1⟩, []⟩ =
        liftStep ⟨⟨{ fr' with regs := ρ1', body := [], term := .jump bc' }, [], m1⟩, []⟩
          (StepResult.ofRes (enterBlock { fr' with regs := ρ1', body := [], term := .jump bc' } bc')
            fun fr2 => .next ⟨fr2, [], m1⟩) := by
      simp only [stepX, raiseAt_jump (env := E') (p := p') (m := m1)
        (fr := { fr' with regs := ρ1', body := [], term := .jump bc' }) rfl rfl]
      rw [step_term _ _ _ rfl]
      rfl
    rw [hsrc, htgt]
    cases hen : enterBlock { fr with regs := ρ1, body := [], term := .jump bc } bc with
    | trap c => exact absurd hen (enterBlock_not_trap _ _ c)
    | stuck msg => exact .inl ⟨msg, by simp [liftStep]⟩
    | ok fr2 =>
    obtain ⟨fr2', hen', hR2⟩ := enter_sim_vals hG hCR (bc' := bc')
      (by rw [← hbc'e, hbcE]; exact hblkd) (by rw [hbcE]; exact hned)
      (fun B1 vals1 hB1 hv1 => by
        rw [← hbc'e]
        rw [hbcE] at hB1 hv1
        rw [hBh] at hB1
        cases hB1
        exact expandExn_holds hR.vrel hpay
          (base := fr.func.freshValue) (base' := fr'.func.freshValue)
          (fun v hv => setMany_other hs fun hm => by
            have := (mem_range_map hm).1; rw [hfv] at this
            exact absurd hv (Nat.not_lt.mpr (Nat.le_trans hT0f this)))
          (fun i hi => setMany_get hs (range_map_nodup _ _) (getElem?_range_map hi))
          (fun a ha => setMany_other hs' fun hm => absurd ha (Nat.not_lt.mpr (mem_range_map hm).1))
          (fun j hj => setMany_get hs' (range_map_nodup _ _) (getElem?_range_map hj))
          (fun v a b hp => by
            obtain ⟨ha, hb⟩ := mem_comps hp
            rw [hfv']; exact ⟨hcg a ha, hcg b hb⟩)
          (by rw [hfv']; exact hT0g) hdo
          (fun v hv => hlt v (List.mem_append_right _ (catch?_vals hc v hv))) hv1) hen
    refine .inr ⟨fr2, fr2', by simp [liftStep], by simp [hen', liftStep], hR2, ?_⟩
    obtain ⟨h1, B2, hB2, h2⟩ := enterBlock_next hen'
    refine ⟨h1.trans hR.func', .inl ⟨B2, ?_, h2⟩⟩
    rw [hR.func'] at hB2
    exact hB2
  · cases hdo

/-! ## Runs -/

/-- `xsim_of_simOut` with the target's steps under `E'`. -/
theorem xsim_of_simOut2 {C : Ctx} (hnr : ∀ B ∈ C.g.blocks, ∀ fn args, B.term ≠ .returnCall fn args)
    {E E' : XEnv} {p p' : Program} {fr fr' : Frame} {m : Mem} {n : Nat}
    (hst : stepX E p ⟨⟨fr, [], m⟩, []⟩ = liftStep ⟨⟨fr, [], m⟩, []⟩ (step E.toEnv p ⟨fr, [], m⟩))
    (hS : S.SimOut C E'.toEnv p' fr' m (step E.toEnv p ⟨fr, [], m⟩)) (hIC : InCode C.g fr')
    (ih : ∀ fr1 fr1' m1, FRel C fr1 fr1' → InCode C.g fr1' → MemBounded m1 →
      stepX E p ⟨⟨fr, [], m⟩, []⟩ = .next ⟨⟨fr1, [], m1⟩, []⟩ →
      XSimOut C E' p' fr1' m1 (runLoopX E p n ⟨⟨fr1, [], m1⟩, []⟩)) :
    XSimOut C E' p' fr' m (runLoopX E p (n + 1) ⟨⟨fr, [], m⟩, []⟩) := by
  cases hr : step E.toEnv p ⟨fr, [], m⟩ with
  | next s1 =>
    rw [hr] at hS hst
    obtain ⟨sf, scl, sm⟩ := s1
    obtain ⟨hcl, hM1, fr1', hR1, hT1⟩ := hS
    simp only at hcl hM1 hR1 hT1
    subst hcl
    have hst' : stepX E p ⟨⟨fr, [], m⟩, []⟩ = .next ⟨⟨sf, [], sm⟩, []⟩ := by
      rw [hst]; simp [liftStep]
    rw [runLoopX_next hst']
    obtain ⟨k, hk⟩ := tstep_runLoopX hT1
    exact XSimOut.pre hk (ih sf fr1' sm hR1 (tstep_inCode hnr hT1 hIC) hM1 hst')
  | done vals m1 =>
    rw [hr] at hS hst
    obtain ⟨vals', hv, k, hk⟩ := hS
    have : runLoopX E p (n + 1) ⟨⟨fr, [], m⟩, []⟩ = .returned vals m1 := by
      rw [Clif.runLoopX, hst]; rfl
    rw [this]
    exact ⟨vals', hv, k, runLoopX_of_returned k ⟨⟨fr', [], m⟩, []⟩ hk⟩
  | trapped c =>
    rw [hr] at hS hst
    obtain ⟨k, hk⟩ := hS
    have : runLoopX E p (n + 1) ⟨⟨fr, [], m⟩, []⟩ = .trapped c := by
      rw [Clif.runLoopX, hst]; rfl
    rw [this]
    exact ⟨k, runLoopX_of_trapped k ⟨⟨fr', [], m⟩, []⟩ hk⟩
  | stuck msg =>
    rw [hr] at hst
    have : runLoopX E p (n + 1) ⟨⟨fr, [], m⟩, []⟩ = .stuck msg := by
      rw [Clif.runLoopX, hst]; rfl
    rw [this]
    trivial

theorem memBounded_raise2 {E : XEnv} (hK : EnvKeepsBoundedX E) {p : Program} {m : Mem}
    {fr : Frame} {fn : FnRef} {args : List ValueId} {x : Exn} {m1 : Mem}
    (h : callRaise E p m fr fn args = some (x, m1)) (hM : MemBounded m) : MemBounded m1 := by
  obtain ⟨ext, vals, g, -, -, -, -, hg, hgo⟩ := callRaise_inv h
  exact hK _ g hg vals m x m1 hgo hM

/-- **Runs with unwinding, two environments** (`sim_runX`). -/
theorem sim_runX2 {C : Ctx} (hG : Good C) (hx : exnOk C.f C.g C.cert = true)
    (hold : indOldB C.f = true) {E E' : XEnv}
    {p p' : Program} (hE : EnvOkX2 E E' C p p') :
    ∀ (n : Nat) (fr fr' : Frame) (m : Mem), FRel C fr fr' → InCode C.g fr' → MemBounded m →
      NoMemTrapX E p ⟨fr, [], m⟩ → NoIndInternalX E p C.f ⟨fr, [], m⟩ →
      XSimOut C E' p' fr' m (runLoopX E p n ⟨⟨fr, [], m⟩, []⟩) := by
  have hnr : ∀ B ∈ C.g.blocks, ∀ fn args, B.term ≠ .returnCall fn args :=
    fun B hB => exnOk_noReturnCall hx hB
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
    by_cases htc : fr.body = [] ∧ ∃ fn args et, fr.term = .tryCall fn args et
    · obtain ⟨hb, fn, args, et, ht⟩ := htc
      rcases S.sim_try hG hE2 hR hM hb ht with hS | ⟨s1, hs1, hcl, hM1, fr1', hT1, hS2⟩
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
        have hshape : sf.body = [] ∧ ∃ bc, sf.term = .jump bc := by
          rw [step_term _ _ _ hb] at hs1
          simp only [ht] at hs1
          exact (stepTryCall_next hs1 rfl).2
        obtain ⟨hb1, bc, hj1⟩ := hshape
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
        (S.step_sim_out hG hE2 hold hR hM hT0 hI0 fun hb fn args et h => htc ⟨hb, fn, args, et, h⟩)
        hIC ihn
  | some r =>
    obtain ⟨x, m1⟩ := r
    cases hb : fr.body with
    | cons st rest =>
      have hra' := hra
      simp only [raiseAt?, hb] at hra'
      split at hra'
      · rename_i fn args hi
        obtain ⟨h1, h2⟩ := sim_call_raise2 hG hE hR hb hi hra'
        rw [runLoopX_unwound h1]
        exact ⟨1, runLoopX_unwound h2 0⟩
      · rename_i sig callee args hi
        obtain ⟨h1, h2⟩ := sim_callInd_raise2 hG hold hE hR hb hi hra'
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
        rcases sim_try_raise2 hG hx hE hR hIC hb ht hra' with ⟨h1, h2⟩ | ⟨msg, h1⟩ |
          ⟨fr1, fr1', h1, h2, h3⟩
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
        exact (S.frel_not_tryInd hR hold callee args et ht).elim
      · cases hra'

/-- **The refinement theorem of `Opt.Legal.check` with unwinding, two environments**
(`check_refinesX` with the source run under `E` and the target run under `E'`). -/
theorem check_refinesX2 {C : Ctx} (hc : check C.f C.g C.cert = true)
    (hx : exnOk C.f C.g C.cert = true)
    {E E' : XEnv} {p p' : Program} (hE : EnvOkX2 E E' C p p') {b b' : Block}
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
  have hG : Good C := check_good hc
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
    have hS := sim_runX2 hG hx (indOldB_of_check hc) hE fuel fr0 _ m hR hIC hM hT hI
    obtain ⟨k0, hk0⟩ := tstep_runLoopX (env := E') hzT
    have hS' := XSimOut.pre hk0 hS
    refine ⟨fun vals m1 h => ?_, fun c h => ?_, fun e m1 h => ?_⟩
    · rw [h] at hS'; exact hS'
    · rw [h] at hS'; exact hS'
    · rw [h] at hS'; exact hS'
  · cases hok

end Opt.Legal.X
