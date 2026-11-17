import FV.Opt.Proof.LegalSimS
import FV.Opt.Legalize128PreT

/-!
# The stepwise simulation of a `try_call_indirect` (#1076)

`FV/Opt/Proof/LegalSimS.lean` repeats `LegalSim.lean`'s simulation lemmas with the stepwise
target relation `TStep` on the domain of `check` (`indOldB`: no `try_call_indirect`, no
`call_indirect` with an `i128` signature), which the refinement theorems with unwinding
(`LegalSimX.lean`, `LegalSimX2.lean`) build on. This file adds, in the same way (the proof is
`LegalSim.lean`'s, unchanged), the step of a `try_call_indirect` (`sim_tryInd`), and the
source step outside the two `try_call` forms on functions whose indirect calls have
`i128`-free call-site signatures (`Opt.Legalize128.indTB`; `step_sim_outT`).
-/

namespace Opt.Legal.S

open Clif Opt Opt.Legalize128 Opt.Legal

/-- `indTB`: no indirect call site has an `i128` call-site signature. -/
theorem indTB_not_ind128 {f : Function} (h : indTB f = true) : ¬ Ind128 f := by
  rintro ⟨sig, d, hs, hd, h128⟩
  simp only [indTB, List.all_eq_true, Bool.and_eq_true] at h
  rcases hs with ⟨B, hB, st, hst, callee, args, hi⟩ | ⟨B, hB, c, args, et, ht, rfl⟩
  · have := (h B hB).1 st hst
    simp [hi, hd, h128] at this
  · have := (h B hB).2
    simp [ht, hd, h128] at this

/-- The domain of `check` has `i128`-free indirect call sites. -/
theorem indTB_of_indOldB {f : Function} (h : indOldB f = true) : indTB f = true := by
  simp only [indOldB, indTB, List.all_eq_true, Bool.and_eq_true] at h ⊢
  intro b hb
  obtain ⟨h1, h2⟩ := h b hb
  refine ⟨h1, ?_⟩
  split
  · rename_i c args et he
    simp [he] at h2
  · rfl

/-- On `indTB`, no statement of `f` has the plan `callInd128`. -/
theorem frel_not_callInd128T {C : Ctx} {fr fr' : Frame} (hR : FRel C fr fr')
    (hT : indTB C.f = true) {st : Stmt} {rest : List Stmt} (hb : fr.body = st :: rest)
    {sig : Nat} {d : Signature} {callee : ValueId} {args : List ValueId}
    {rg : List (List SlotEl)} {rs : List ValueId}
    (hpl : planOf C st = some (.callInd128 sig d callee args rg rs)) : False := by
  obtain ⟨args0, -, hi, -, hd, h128, -⟩ := planOf_callInd128 hpl
  obtain ⟨B, hB, hst⟩ := frel_stmt hR hb
  exact indTB_not_ind128 hT ⟨sig, d, .inl ⟨B, hB, st, hst, callee, args0, hi⟩, hd, h128⟩

/-- **A `try_call_indirect`** (two source steps: the indirect call, then the jump to the
normal-return successor): the target's `try_call_indirect` calls the same address with the
arguments expanded by the groups of the call-site signature (`CallIndRel2`), its results at
fresh values; after the jumps, the frames are related again. -/
theorem sim_tryInd {C : Ctx} (hG : Good C) {env env' : Env} {p p' : Program}
    (hE : EnvOk2 env env' C p p')
    {fr fr' : Frame} {m : Mem} (hR : FRel C fr fr') (hM : MemBounded m) (hb : fr.body = [])
    {c : ValueId} {args : List ValueId} {et : ExnTable} (ht : fr.term = .tryCallIndirect c args et)
    (hI : IndExt env p C.f ⟨fr, [], m⟩) :
    SimStep C env env' p p' fr' m (step env p ⟨fr, [], m⟩) := by
  obtain ⟨B0, hB0, -, hterm⟩ := hR.blk
  have hlt : ∀ x ∈ termOps (.tryCallIndirect c args et), x < C.T0 := fun x hx =>
    term_ops_lt hG hB0 (by rw [← hterm, ht]; exact hx)
  have hltc : c < C.T0 := hlt c (by simp [termOps])
  have hlta : ∀ x ∈ args, x < C.T0 := fun x hx => hlt x (by simp [termOps, hx])
  have hltv : ∀ x ∈ et.vals, x < C.T0 := fun x hx => hlt x (by simp [termOps, hx])
  have hcode := hR.code
  rw [hb, ht] at hcode
  simp only [codeOk] at hcode
  cases ht' : fr'.term
  all_goals first | (rw [ht'] at hcode; simp [termOk] at hcode; done) | skip
  rename_i c' args' et'
  rw [ht'] at hcode
  obtain ⟨hts, hcc, hpc, hsig, hblk, hne, hT0f, hT0g, hzg, hcg, d, B, d', gs, rg, hd, hB, hs',
    hgs, hrg, hdg, hexp, hexpT⟩ := termOk_tryCallInd hcode
  subst c'
  obtain ⟨gs0, rg0, hgs0, hrg0, -, hret'⟩ := sigExp_spec hs'
  rw [hgs] at hgs0
  cases hgs0
  rw [hrg] at hrg0
  cases hrg0
  have hdf : fr.func.sigDecls.lookup et.sig = some d := by rw [hR.func]; exact hd
  have hdt : fr'.func.sigDecls.lookup et'.sig = some d' := by rw [hR.func', hsig]; exact hdg
  rw [step_term env p _ hb, ht]
  simp only [stepTerm]
  cases hbc : tryNormal et fr.func.freshValue with
  | trap c0 => exact absurd hbc (tryNormal_ne_trap _ _ c0)
  | stuck msg =>
    exact .inl (by simp [SimOut, stepTryCallIndirect, hdf, hbc, Res.ofOption, bind, Res.bind])
  | ok bc =>
  have hsrcT : stepTryCallIndirect env p ⟨fr, [], m⟩ c args et =
      stepCallIndirect env p ⟨{ fr with body := [], term := .jump bc }, [], m⟩ []
        ((List.range d.returns.length).map (fr.func.freshValue + ·)) et.sig c args := by
    simp only [stepTryCallIndirect, hdf, hbc, Res.ofOption, bind, Res.bind, pure,
      StepResult.ofRes_ok]
  rw [hsrcT]
  have hbcE := tryNormal_eq hbc
  cases hc : fr.get c with
  | trap c0 => exact absurd hc (get_ne_trap fr c c0)
  | stuck msg =>
    have hcJ : ({ fr with body := [], term := .jump bc } : Frame).get c = .stuck msg := hc
    exact .inl (by simp [SimOut, stepCallIndirect, hdf, hcJ, Res.ofOption, bind, Res.bind,
      StepResult.ofRes])
  | ok cv =>
  have hcJ : ({ fr with body := [], term := .jump bc } : Frame).get c = .ok cv := hc
  cases hcv : cv.as? .i64 with
  | none =>
    exact .inl (by simp [SimOut, stepCallIndirect, hdf, hcJ, hcv, Res.ofOption, bind, Res.bind,
      StepResult.ofRes])
  | some b =>
  cases hga : fr.getMany args with
  | trap c0 => exact absurd hga (getMany_ne_trap fr args c0)
  | stuck msg =>
    have hgaJ : ({ fr with body := [], term := .jump bc } : Frame).getMany args = .stuck msg :=
      (getMany_congr (fr := fr) (fr' := { fr with body := [], term := .jump bc })
        fun _ _ => rfl).trans hga
    exact .inl (by simp [SimOut, stepCallIndirect, hdf, hcJ, hcv, hgaJ, Res.ofOption, bind,
      Res.bind, StepResult.ofRes])
  | ok vals =>
  have hgaJ : ({ fr with body := [], term := .jump bc } : Frame).getMany args = .ok vals :=
    (getMany_congr (fr := fr) (fr' := { fr with body := [], term := .jump bc })
      fun _ _ => rfl).trans hga
  have hnf := hI.2 c args et cv hb ht ⟨B0, hB0, by rw [← hterm]; exact ht⟩ hc
  rw [← as_i64_toNat hcv] at hnf
  rw [stepCallIndirect_ext (fr := { fr with body := [], term := .jump bc }) (cs := []) (m := m)
    hdf hcJ hcv hgaJ hnf]
  obtain ⟨vals', hv', hexp'⟩ := expandArgs_holds hR.vrel hR.zero hexp hlta (getMany_holds hga)
  -- the target's `try_call_indirect`
  have hnoexn := expandTry_noExn hexpT
  have hbc2 := tryNormal_of_noExn (base := fr'.func.freshValue) hnoexn
  generalize hbc'e : (⟨et'.normal.block, et'.normal.args.map (argId fr'.func.freshValue)⟩ :
    BlockCall) = bc' at hbc2
  have htT : stepTryCallIndirect env' p' ⟨fr', [], m⟩ c args' et' =
      stepCallIndirect env' p' ⟨{ fr' with body := [], term := .jump bc' }, [], m⟩ []
        ((List.range d'.returns.length).map (fr'.func.freshValue + ·)) et'.sig c args' := by
    simp only [stepTryCallIndirect, hdt, hbc2, Res.ofOption, bind, Res.bind, pure,
      StepResult.ofRes_ok]
  have hget' : fr'.get c = fr.get c := by
    simp only [Frame.get, hR.peq c hltc (plain_iff.1 hpc)]
  have hgaJ2 : ({ fr' with body := [], term := .jump bc' } : Frame).getMany args' = .ok vals' :=
    (getMany_congr (fr := fr') (fr' := { fr' with body := [], term := .jump bc' })
      fun _ _ => rfl).trans (holds_getMany hv')
  have hname : IndSite C.f et.sig := .inr ⟨B0, hB0, c, args, et, by rw [← hterm]; exact ht, rfl⟩
  obtain ⟨hfn, hrelI⟩ := hE.ind ⟨et.sig, hname⟩
  have hrel := hrelI et.sig d hname hd d' gs rg hs' hgs hrg m b.toNat
  have htgt := stepCallIndirect_ext (env := env') (p := p')
    (fr := { fr' with body := [], term := .jump bc' }) (cs := []) (m := m) (rest := [])
    (results := (List.range d'.returns.length).map (fr'.func.freshValue + ·)) hdt
    (show fr'.get c = .ok cv by rw [hget']; exact hc) hcv hgaJ2 (nf_names hfn hnf)
  have hT1 : ∀ r, step env' p' ⟨fr', [], m⟩ = r ↔ stepCallIndirect env' p'
      ⟨{ fr' with body := [], term := .jump bc' }, [], m⟩ []
      ((List.range d'.returns.length).map (fr'.func.freshValue + ·)) et'.sig c args' = r := by
    intro r
    rw [step_term env' p' _ hts, ht']
    simp only [stepTerm]
    rw [htT]
  rw [hsig] at htgt hT1
  cases hx : callExternAt env p m d b.toNat vals with
  | stuck msg => exact .inl trivial
  | trap c0 =>
    obtain ⟨-, -, -, -, -, hty, -⟩ := callExternAt_trap_full hx
    refine .inl ⟨1, ?_⟩
    rw [runLoop_succ, (hT1 (.trapped c0)).2 (by rw [htgt, (hrel vals vals' hty hexp').2 c0 hx]; rfl)]
  | ok r =>
  obtain ⟨rv, m'⟩ := r
  obtain ⟨name, h, -, henv, -, hty, hout, hrt⟩ := callExternAt_ok_full hx
  obtain ⟨rv', hx', hexr⟩ := (hrel vals vals' hty hexp').1 rv m' hx
  have hrt' : rv'.map (·.ty) = AbiParam.tys d'.returns := by
    rw [hret', AbiParam.tys, ← expRel_tys (groups_spec hrg) hexr hrt]
  simp only [StepResult.ofRes_ok, continueWith]
  have hnrv : rv.length = d.returns.length := by
    have := congrArg List.length hrt; simpa [AbiParam.tys] using this
  have hnrv' : rv'.length = d'.returns.length := by
    have := congrArg List.length hrt'; simpa [AbiParam.tys] using this
  cases hs : fr.regs.setMany ((List.range d.returns.length).map (fr.func.freshValue + ·)) rv with
  | none => exact .inl trivial
  | some ρ1 =>
  obtain ⟨ρ1', hs1'⟩ := setMany_of_len fr'.regs
    (rs := (List.range d'.returns.length).map (fr'.func.freshValue + ·)) (vs := rv')
    (by simp [hnrv'])
  have hfv : fr.func.freshValue = C.f.freshValue := by rw [hR.func]
  have hfv' : fr'.func.freshValue = C.g.freshValue := by rw [hR.func']
  have hstepT : step env' p' ⟨fr', [], m⟩ =
      .next ⟨{ fr' with regs := ρ1', body := [], term := .jump bc' }, [], m'⟩ := by
    refine (hT1 _).2 ?_
    rw [htgt, hx']
    simp only [StepResult.ofRes_ok, continueWith, hs1']
  have hM1 : MemBounded m' := hE.keep name h henv vals m rv m' hout hM
  refine .inr ⟨_, rfl, rfl, hM1, _, TStep.of_step hstepT, ?_⟩
  -- the jumps
  have hCR := crel_bind hG hR.toCRel hs hs1'
    (fun v hv => by have := (mem_range_map hv).1; rw [hfv] at this; omega)
    (fun w hw => fresh_of_ge (base' := C.g.freshValue) hT0g hzg hcg
      (by have := (mem_range_map hw).1; rw [hfv'] at this; exact this))
    [] (.jump bc) [] (.jump bc')
  simp only
  rw [step_term env p _ rfl]
  simp only [stepTerm]
  cases hen : enterBlock { fr with regs := ρ1, body := [], term := .jump bc } bc with
  | trap c0 => exact absurd hen (enterBlock_not_trap _ _ c0)
  | stuck msg => trivial
  | ok fr2 =>
  simp only [StepResult.ofRes_ok]
  obtain ⟨fr2', hen', hR2⟩ := enter_sim_vals hG hCR (bc' := bc') (by rw [← hbc'e, hbcE]; exact hblk)
    (by rw [hbcE]; exact hne) (fun B1 vals1 hB1 hv1 => by
      rw [← hbc'e]
      rw [hbcE] at hB1 hv1
      rw [hB] at hB1
      cases hB1
      refine expandTry_holds hR.vrel hexr (base := fr.func.freshValue)
        (base' := fr'.func.freshValue)
        (fun v hv => setMany_other hs fun hm => by
          have := (mem_range_map hm).1; rw [hfv] at this
          exact absurd hv (Nat.not_lt.mpr (Nat.le_trans hT0f this)))
        (fun i hi => setMany_get hs (range_map_nodup _ _) (getElem?_range_map (hnrv ▸ hi)))
        (fun a ha => setMany_other hs1' fun hm => absurd ha (Nat.not_lt.mpr (mem_range_map hm).1))
        (fun j hj => setMany_get hs1' (range_map_nodup _ _) (getElem?_range_map (hnrv' ▸ hj)))
        (fun v a b hp => by
          obtain ⟨ha, hb⟩ := mem_comps hp
          rw [hfv']; exact ⟨hcg a ha, hcg b hb⟩)
        (by rw [hfv']; exact hT0g) hexpT
        (fun v hv => hltv v (List.mem_append_left _ (val_mem_vals hv))) hv1) hen
  refine ⟨rfl, hM1, fr2', hR2, TStep.of_step ?_⟩
  rw [step_term env' p' _ rfl]
  simp only [stepTerm, hen', StepResult.ofRes_ok]

/-- **One source step that is neither form of `try_call`**, matched by the target
(`step_sim_out` on `indTB` instead of `indOldB`). -/
theorem step_sim_outT {C : Ctx} (hG : Good C) {env env' : Env} {p p' : Program}
    (hE : EnvOk2 env env' C p p') (hT128 : indTB C.f = true)
    {fr fr' : Frame} {m : Mem} (hR : FRel C fr fr') (hM : MemBounded m)
    (hT : MemTrapFree env p ⟨fr, [], m⟩) (hI : IndExt env p C.f ⟨fr, [], m⟩)
    (hnt : fr.body = [] → ∀ fn args et, fr.term ≠ .tryCall fn args et)
    (hnti : fr.body = [] → ∀ c args et, fr.term ≠ .tryCallIndirect c args et) :
    SimOut C env' p' fr' m (step env p ⟨fr, [], m⟩) := by
  cases hb : fr.body with
  | nil =>
    exact sim_term hG hR hM hb (fun fn args et h => hnt hb fn args et h)
      (fun c args et h => hnti hb c args et h)
  | cons st rest =>
    have hcode0 := hR.code
    rw [hb] at hcode0
    obtain ⟨pl, hpl, hseg, hcode⟩ := code_cons hcode0
    have hbody := take_drop_eq (l := fr'.body) (n := pl.len) rfl
    have hT' : ∀ c, step env p ⟨fr, [], m⟩ = .trapped c →
        (∀ op t fl a o, st.inst ≠ .load op t fl a o) ∧
          (∀ op t fl x a o, st.inst ≠ .store op t fl x a o) := fun c h => hT c st rest h hb
    cases pl with
    | same =>
      rw [segOk_same hseg] at hbody
      exact sim_same hG hR hM hb hpl hbody hcode
    | pure pat ins outs =>
      exact sim_pure hG hR hM hb hpl hseg hbody hcode
    | load rl rh q fl off =>
      obtain ⟨hs, hrl, hrq⟩ := segOk_load hseg
      rw [hs] at hbody
      exact sim_load hG hR hM hb hpl hbody hrl hrq hcode fun c h => by
        obtain ⟨hi, -, -, -⟩ := planOf_load hpl
        exact (hT' c h).1 _ _ _ _ _ hi
    | store xl xh q fl off =>
      rw [segOk_store hseg] at hbody
      exact sim_store hG hR hM hb hpl hbody hcode fun c h => by
        obtain ⟨⟨x, hi, -⟩, -, -, -⟩ := planOf_store hpl
        exact (hT' c h).2 _ _ _ _ _ _ hi
    | div op xl xh yl yh rl rh =>
      obtain ⟨fn, hs, hrl, hfn⟩ := segOk_div hseg
      rw [hs] at hbody
      exact sim_div hG hE.helper hE.tgt hR hM hb hpl hbody hrl hfn hcode
    | call fn e args rg rs =>
      obtain ⟨rs', hs, hrets, hnd', s', hs', hfn⟩ := segOk_call hseg
      rw [hs] at hbody
      exact sim_call hG hE.ext hE.keep hE.src hE.tgt hR hM hb hpl hbody hrets hnd' hs' hfn hcode
    | trap lo hi nz code =>
      obtain ⟨segA, c, hs, hc, hpo⟩ := segOk_trap hseg
      rw [hs, List.append_assoc] at hbody
      exact sim_trap hG hR hM hb hpl hpo hc hbody hcode
    | callInd =>
      obtain ⟨hs, hdecl⟩ := segOk_callInd hseg
      rw [hs] at hbody
      exact sim_callInd hG hE hR hM hb hpl hbody hdecl hcode hI
    | callInd128 sig d callee args rg rs => exact (frel_not_callInd128T hR hT128 hb hpl).elim

end Opt.Legal.S
