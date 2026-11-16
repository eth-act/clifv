import FVTest.Backend.FloatCtlRulesT
import FV.Backend.Proof.IselCovTFamCover

/-!
Witnesses for the premise `hca : CallArgsInt ctx` (the arguments of the context's `call`s are in
integer positions) that S11g (#1015) added to `CtxT.ofExterns` and `CovT.famCover_ofG`. Until
S11g `CtxInvT` gave it (`intArgs` listed a `call`'s arguments); since `intArgs` no longer lists
them, both statements are false without it.

`fMis` passes an `f64` value to an extern declared with an `i64` parameter (a CLIF verifier
error; neither statement assumes the verifier's typing of a `call`'s arguments). `buildCtx`
accepts it and its context satisfies `CtxInvT` (`ctxOkT`), the typed scope (`InstScopeT`),
integer externs and every other premise of `famCover_ofG`, but

* its `call` argument `v0` is not in an integer position (`not_callArgsInt_fMis`), so it is not a
  `CtxT`: `CtxT.ofExterns` without `hca` is false (`ctxT_ofExterns_needs_callArgs`);
* its `call` belongs to no instruction family (family 13 takes integer arguments,
  `not_famCover_fMis`): `famCover_ofG` without `hca` is false (`famCover_ofG_needs_callArgs`).

The same context over `fInt` (the same function with an `i64` argument, in `Compile.functionET`)
passes `ctxOkT` and the scope check, so the witness helper `FloatCtlRulesT.ctxT_of` without its
new `buildCtx` premise is false too (`ctxT_of_needs_buildCtx`).

`lake build FVTest.Backend.CallArgsIntW`.
-/

open Backend Backend.Proof Backend.Proof.Driver Backend.Proof.CovT

namespace CallArgsIntW

open FloatCtlT FloatCtlRulesT

/-- An `f64` passed to an `i64` parameter. -/
def fMis : Clif.Function := fnOfText
  "function %m(f64) -> i64 {
    fn0 = %g(i64) -> i64
block0(v0: f64):
    v1 = call fn0(v0)
    return v1
}
"

/-- `fMis`'s context. -/
abbrev ctxM : Ctx := (ctxStOf fMis).1

#guard (buildCtx fMis).toBool
#guard ctxM.insts[0]?.bind (·.clif) == some (Clif.Inst.call 0 [0])
#guard ctxM.valueType? 0 == some (.float 64)
#guard ctxOkT fMis ctxM && scopeOkB ctxM
#guard fMis.externs.all (Compile.sigE ·.2.sig)
#guard dominatedB fMis && Compile.storeTypedB fMis && Compile.selectTypedB fMis
#guard fMis.blocks.all fun B => B.body.all fun s => Compile.instET s.inst

theorem buildCtx_fMis : ∃ ranges st0, buildCtx fMis = .ok (ctxM, ranges, st0) := by
  have h : (buildCtx fMis).toBool = true := by native_decide
  revert h
  unfold ctxM ctxStOf
  cases buildCtx fMis with
  | error e => intro h; cases h
  | ok r =>
    intro _
    obtain ⟨ctx, ranges, st⟩ := r
    exact ⟨ranges, st, rfl⟩

theorem ctxInvT_fMis : CtxInvT fMis ctxM := ctxOkT_sound (by native_decide)

theorem instScopeT_fMis : InstScopeT ctxM := instScopeT_of (by native_decide)

theorem insts0_fMis : (ctxM.insts[0]?).isSome = true := by native_decide

theorem clif0_fMis : (ctxM.insts[0]?.get insts0_fMis).clif = some (.call 0 [0]) := by
  native_decide

theorem valueType0_fMis : ctxM.valueType? 0 = some (.float 64) := by native_decide

/-- **`fMis`'s `call` argument `v0` (an `f64`) is not in an integer position.** -/
theorem not_callArgsInt_fMis : ¬ CallArgsInt ctxM := by
  intro h
  have := h 0 _ 0 [0] (Option.some_get insts0_fMis).symm clif0_fMis 0 (by simp) (.float 64)
    valueType0_fMis
  simp [eCTys] at this

/-- **`CtxT.ofExterns` without `hca` is false.** -/
theorem ctxT_ofExterns_needs_callArgs :
    ¬ ∀ (f : Clif.Function) (ctx : Ctx), CtxInvT f ctx → InstScopeT ctx →
      f.externs.all (Compile.sigE ·.2.sig) = true → CtxT f ctx := fun H =>
  not_callArgsInt_fMis (H fMis ctxM ctxInvT_fMis instScopeT_fMis (by native_decide)).callArgs

/-- `fMis` with an `i64` argument: in the typed scope (`Compile.functionET`). -/
def fInt : Clif.Function := fnOfText
  "function %m(i64) -> i64 {
    fn0 = %g(i64) -> i64
block0(v0: i64):
    v1 = call fn0(v0)
    return v1
}
"

/-- `fMis`'s context over `fInt`: `ctxOkT` and the scope check accept it (they do not tie the
context's value types to `fInt`'s definitions), and its `call` argument is an `f64`. -/
abbrev ctxI : Ctx := { ctxM with func := fInt }

#guard ctxOkT fInt ctxI && scopeOkB ctxI && Compile.functionET fInt

theorem not_callArgsInt_ctxI : ¬ CallArgsInt ctxI := fun h =>
  not_callArgsInt_fMis fun ii info fn args hi hc => h ii info fn args hi hc

/-- **`FloatCtlRulesT.ctxT_of` without its `buildCtx` premise is false** (S11g: it concluded
`CtxT` from `ctxOkT`, `scopeOkB` and `Compile.functionET` for any context). -/
theorem ctxT_of_needs_buildCtx :
    ¬ ∀ (f : Clif.Function) (ctx : Ctx), ctxOkT f ctx = true → scopeOkB ctx = true →
      Compile.functionET f = true → CtxT f ctx := fun H =>
  not_callArgsInt_ctxI
    (H fInt ctxI (by native_decide) (by native_decide) (by native_decide)).callArgs

/-- **`fMis`'s `call` belongs to no instruction family.** -/
theorem not_famCover_fMis : ¬ FamCover ctxM := by
  intro h
  have hd : (ctxM.insts[0]?.get insts0_fMis).data =
      .data 152 6 [.data 151 8 [], .values [0], .op (.funcRef 0)] :=
    eq_of_beq (by native_decide)
  obtain ⟨i, F, hF, -, -, -, hg⟩ := h 0 _ _ (Option.some_get insts0_fMis).symm clif0_fMis
  rw [hd] at hg
  have hmem := List.mem_of_getElem? hF
  simp only [famTab, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals
    subst h
    simp (config := { decide := true }) [idata, opAlts, γP, γLP, γAnyP, ValIn, ValsIn,
      valueType0_fMis, eCTys] at hg

/-- **`famCover_ofG` without `hca` is false.** -/
theorem famCover_ofG_needs_callArgs :
    ¬ ∀ (f : Clif.Function) (ctx : Ctx) (ranges : Array (Nat × Nat)) (st0 : LState),
      CtxInvT f ctx → f.externs.all (Compile.sigE ·.2.sig) = true →
      (∀ B ∈ f.blocks, ∀ s ∈ B.body,
        Compile.instET s.inst = true ∨ ∃ op ty args, s.inst = .float op ty args) →
      (∀ (j : Nat) info op ty args, ctx.insts[j]? = some info →
        info.clif = some (.float op ty args) →
        ∃ (i : Nat) (F : Fam), famTab[i]? = some F ∧ FamOk ctx F info) →
      dominatedB f = true → Compile.storeTypedB f = true → Compile.selectTypedB f = true →
      buildCtx f = .ok (ctx, ranges, st0) → FamCover ctx := by
  intro H
  obtain ⟨ranges, st0, hb⟩ := buildCtx_fMis
  refine not_famCover_fMis (H fMis ctxM ranges st0 ctxInvT_fMis (by native_decide) ?_ ?_
    (by native_decide) (by native_decide) (by native_decide) hb)
  · intro B hB s hs
    left
    have h : fMis.blocks.all (fun B => B.body.all fun s => Compile.instET s.inst) = true := by
      native_decide
    exact List.all_eq_true.mp (List.all_eq_true.mp h B hB) s hs
  · intro j info op ty args hj hc
    exfalso
    have h : ctxM.insts.toList.all (fun info => !(info.clif matches some (.float ..))) = true := by
      native_decide
    have hm : info ∈ ctxM.insts.toList := by
      rw [Array.mem_toList_iff]; exact Array.mem_of_getElem? hj
    have := List.all_eq_true.mp h info hm
    rw [hc] at this
    simp at this

end CallArgsIntW
