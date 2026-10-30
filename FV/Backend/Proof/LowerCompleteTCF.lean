import FV.Backend.Proof.LowerCompleteT
import FV.Backend.Proof.DriverCheckCF
import FV.Backend.Proof.TryRegsC

/-!
# Completeness of the float lowering validator (S11f, #35)

`lowerCheckTCF_complete`: on input in `Dominated` and the float scope `LowerScopeTF`,
`lowerCheckTCF` (the validator `Backend.lowerCheckFor` runs on functions with the proven float
operations) accepts every output of `lowerFunction`. The conjuncts are `lowerCheck_partsTF`'s with
`instScopeOkF` (`instScopeOkF_complete`); the validator's run over the typed `try_call` helpers
(`lowBlocksC`) is the model run `lowBlocks` (`lowBlocksC_of_lowBlocks`: whenever the integer
helpers succeed, the typed ones give the same result, `exnTableOpndC_of`, `tryCallDataC_of`,
`tryRegsOfC_eq`).
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof

/-- A terminator the model lowering `lowTerm` lowers is lowered the same way by `lowTermC`. -/
theorem lowTermC_of_lowTerm {f : Clif.Function} {tcall : TermCallF} {ycall : TryCallF} {ti : Nat}
    {t : Clif.Terminator} {tst : LState} {nl : Nat}
    {r : V × List Label × Option TryLow × LState × Nat}
    (h : lowTerm f tcall ycall ti t tst nl = some r) : lowTermC f tcall ycall ti t tst nl = some r := by
  cases t with
  | tryCall fn args et =>
    simp only [lowTerm] at h
    simp only [lowTermC]
    cases hd : tryCallData f (.tryCall fn args et) with
    | error => rw [hd] at h; cases h
    | ok data =>
      cases he : exnTableOpnd f et with
      | error => rw [hd, he] at h; cases h
      | ok p =>
        obtain ⟨sig, items⟩ := p
        rw [hd, he] at h
        rw [tryCallDataC_of hd, exnTableOpndC_of he]
        cases htg : tryTargets f et.dests nl with
        | none => rw [htg] at h; cases h
        | some p =>
          obtain ⟨targets, nl'⟩ := p
          rw [htg] at h
          simp only at h ⊢
          rw [tryRegsOfC_eq (sigRets_classes_int (sigIntB_iff.mp (exnTableOpnd_int he)).2)]
          exact h
  | tryCallIndirect callee args et =>
    simp only [lowTerm] at h
    simp only [lowTermC]
    cases hd : tryCallData f (.tryCallIndirect callee args et) with
    | error => rw [hd] at h; cases h
    | ok data =>
      cases he : exnTableOpnd f et with
      | error => rw [hd, he] at h; cases h
      | ok p =>
        obtain ⟨sig, items⟩ := p
        rw [hd, he] at h
        rw [tryCallDataC_of hd, exnTableOpndC_of he]
        cases htg : tryTargets f et.dests nl with
        | none => rw [htg] at h; cases h
        | some p =>
          obtain ⟨targets, nl'⟩ := p
          rw [htg] at h
          simp only at h ⊢
          rw [tryRegsOfC_eq (sigRets_classes_int (sigIntB_iff.mp (exnTableOpnd_int he)).2)]
          exact h
  | _ => exact h

/-- **The validator's lowering run is the model run** (`lowBlocksC` over `lowTermC` is
`lowBlocks` whenever `lowBlocks` succeeds). -/
theorem lowBlocksC_of_lowBlocks {f : Clif.Function} {call : StmtCall} {tcall : TermCallF}
    {ycall : TryCallF} :
    ∀ {Bs : List Clif.Block} {start : Nat} {st : LState} {nl : Nat} {bl : List BLow},
      lowBlocks f call tcall ycall start Bs st nl = some bl →
      lowBlocksC f call tcall ycall start Bs st nl = some bl
  | [], _, _, _, _, h => h
  | B :: Bs, start, st, nl, bl, h => by
    unfold lowBlocks at h
    unfold lowBlocksC
    split at h
    · cases h
    · rename_i sls stE hs
      rw [hs]
      simp only at h ⊢
      split at h
      · rename_i data targets tl tst' nl' ht
        rw [lowTermC_of_lowTerm ht]
        simp only
        obtain ⟨bl', hbl', rfl⟩ := Option.map_eq_some_iff.mp h
        rw [lowBlocksC_of_lowBlocks hbl']
        rfl
      · cases h

theorem shapeOkTF_eq_S {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState}
    {gn : Nat → Nat} {bl : List BLow} :
    shapeOkTF f vc ctx st0 gn bl = shapeOkTS (instScopeOkF ctx) f vc ctx st0 gn bl := rfl

/-- **Completeness of the float lowering validator.** On input satisfying `Dominated` and the
float scope `LowerScopeTF`, `lowerCheckTCF` accepts `lowerFunction`'s output. -/
theorem lowerCheckTCF_complete {f : Clif.Function} {vc : VCode} (hd : Dominated f)
    (hs : LowerScopeTF f) (h : lowerFunction f = .ok vc) : lowerCheckTCF f vc = true := by
  obtain ⟨ctx, ranges, st0, bl, hb, hl, hok⟩ := lowerCheck_partsTF hd hs h
    (sc := instScopeOkF) fun _ _ _ hb => instScopeOkF_complete ((ctxSpec_of hb).instScopeTF hs.subsetTF)
  unfold lowerCheckTCF
  rw [hb]; simp only; rw [lowBlocksC_of_lowBlocks hl]
  exact hok

end Backend.Proof.Driver
