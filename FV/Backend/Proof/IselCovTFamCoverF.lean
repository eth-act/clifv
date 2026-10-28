import FV.Backend.Proof.IselCovTFamCover
import FV.Backend.Proof.LowerLoopCtxTF
import FV.Compile.SubsetTFArgs

/-!
# Form coverage over float-capable contexts: the float scope's families

`famCover_ofF`: in `buildCtx`'s context of a function of the float scope (`LowerScopeTF`) whose
float positions are float-defined (`Compile.floatArgsTyped`), every statement belongs to an
instruction family of `famTab` (`FamCover`): the statements of the typed scope as in
`famCover_of` (`famCover_ofG`), the S11f float operations to families 31-35 (`famFloat_of`):
their float operands have float types (`floatArgsTyped`, dominance), the operand of an
`fcvt_from_*` is an integer (`opsTypedTF`). `termFam_ofF`, `callRes_intF`: `termFam_of`,
`callRes_int` on the float scope.
-/

namespace Backend.Proof.CovT

open Backend Backend.Proof Backend.Proof.Driver Isle Isle.Aarch64

set_option maxRecDepth 20000

/-- An enum value of type `t` whose variant index is in `ks` is described by the alternatives. -/
theorem γ_enumAlts {ctx : Ctx} {t : TypeId} {name : String} {ks : List Nat}
    (h : ks.any (fun k => variantIdx t name == some k) = true) :
    γP ctx noInst (.alts (ks.map fun k => .data t k [])) (mkVariant t name) := by
  obtain ⟨k, hk, he⟩ := List.any_eq_true.mp h
  have he : variantIdx t name = some k := by simpa using he
  unfold mkVariant
  rw [he]
  show γAnyP ctx noInst (ks.map fun k => AT.data t k []) (.data t k [])
  rw [γAnyP_iff]
  exact ⟨.data t k [], List.mem_map.mpr ⟨k, hk, rfl⟩, ⟨[], rfl, trivial⟩⟩

/-- `FamOk`'s result conjuncts for a single result of type `ty` in `ts`. -/
theorem resIn1 {info : IInfo} {ty : Clif.Ty} (hres : info.resTys = [CTy.ofClif ty])
    {F : Fam} (hr : CTy.ofClif ty ∈ F.res) (ha : CTy.ofClif ty ∈ F.all) :
    (∀ t ∈ info.resTys, t ∈ F.res ∧ t ∈ F.all) ∧ info.resTys.head?.getD .invalid ∈ F.res := by
  rw [hres]
  refine ⟨fun t ht => ?_, by simpa using hr⟩
  simp at ht; subst ht; exact ⟨hr, ha⟩

set_option maxHeartbeats 4000000 in
/-- **Every float operation of a float-scope function belongs to a float family** (31-35). -/
theorem famFloat_of {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {st0 : LState}
    (hs : LowerScopeTF f) (hfa : Compile.floatArgsTyped f = true) (hdom : dominatedB f = true)
    (hb : buildCtx f = .ok (ctx, ranges, st0)) :
    ∀ (j : Nat) info op ty args, ctx.insts[j]? = some info →
      info.clif = some (.float op ty args) →
      ∃ (i : Nat) (F : Fam), famTab[i]? = some F ∧ FamOk ctx F info := by
  intro j info op ty args hj hc
  have sp := ctxSpec_of hb
  have hctx : CtxInvT f ctx := ctxInvT_ofF hs hb
  have hd := dominated_of hdom
  obtain ⟨B, hB, s, hsB, -, hcs⟩ := sp.inst_of hj hc
  have hdata := hctx.data j info _ hj hc
  obtain ⟨tys, htys, hres, hlen0⟩ := hctx.resTys j info _ hj hc
  have hlen : info.results.length = info.resTys.length := by rw [hres, hlen0]; simp
  have hrv := (sp.facts.types hd.ssa).1 j info hj
  have hint := sp.intOpsF_of hs.subsetTF j info _ hj hc
  have htyped : ∀ y ∈ args, (ctx.valueType? y).isSome := by
    intro y hy
    obtain ⟨bi, hbi, e⟩ := List.getElem_of_mem hB
    obtain ⟨jj, hjj, e'⟩ := List.getElem_of_mem hsB
    have hB' : f.blocks[bi]? = some B := by rw [List.getElem?_eq_getElem hbi, e]
    have hs' : B.body[jj]? = some s := by rw [List.getElem?_eq_getElem hjj, e']
    have hy' : y ∈ instArgs s.inst := by rw [← hcs]; simpa [instArgs] using hy
    exact Prg.typed_of_def sp (availOf_defs ((hd.uses ctx ranges st0 hb bi B hB').1 jj s hs' y hy'))
  have hfl : ∀ y ∈ Compile.floatArgs (.float op ty args), y ∈ args → ValIn ctx y fCTys := by
    intro y hy hya
    refine valIn_F (htyped y hya) (fun t ht => ?_) (hctx.valTyM y)
    have hF := hfa
    simp only [Compile.floatArgsTyped, List.all_eq_true] at hF
    rw [hcs] at hy
    exact sp.class_of_argClassOk (hF B hB s hsB y hy) (by decide) t ht
  rcases args with _ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩
  · simp [instData, throw, throwThe, MonadExceptOf.throw] at hdata
  · -- one operand: arithmetic/rounding or a conversion
    simp only [instData] at hdata
    split at hdata
    · rename_i n hn
      split at hdata
      · rename_i hty
        simp only [pure, Except.pure, Except.ok.injEq] at hdata
        have hx := hfl x (by simp [Compile.floatArgs, hn]) (by simp)
        have hres1 : info.resTys = [CTy.ofClif ty] := by
          have : tys = [ty] := by
            cases op <;> simp only [Backend.fUnaryOpcode, reduceCtorEq] at hn <;>
              simp only [Clif.Inst.resultTypes, Option.some.injEq] at htys <;> exact htys.symm
          rw [hres, this]; rfl
        have hfty : ty.isFloat = true := by
          cases op <;> simp_all [Backend.fTyOk, Backend.fUnaryOpcode] <;> (subst hty; rfl)
        obtain ⟨hR1, hR2⟩ := resIn1 hres1 (F := famTab[32])
          (by simpa [famTab] using ofClif_fCTys hfty) (by simpa [famTab] using ofClif_fCTys hfty)
        refine ⟨32, _, rfl, famOk_of hrv hlen hR1 hR2 ?_⟩
        rw [← hdata]
        refine γ_idata (by decide) ⟨γ_opAlts ?_, γ_val hx, trivial⟩
        cases op <;> simp_all [Backend.fUnaryOpcode] <;> (subst hn; decide)
      · cases hdata
    · rename_i hnu
      split at hdata
      · rename_i n hn
        split at hdata
        · rename_i hty
          simp only [pure, Except.pure, Except.ok.injEq] at hdata
          cases op <;> simp only [Backend.fCvtOpcode, reduceCtorEq] at hn
          all_goals (
            simp only [Option.some.injEq] at hn
            subst hn
            simp only [Clif.Inst.resultTypes, Option.some.injEq] at htys
            subst htys
            simp only [List.map_cons, List.map_nil] at hres)
          all_goals first
            -- `fcvt_from_uint`, `fcvt_from_sint`: an integer operand, a float result
            | (have hfty : ty.isFloat = true := by simpa [Backend.fCvtTyOk] using hty
               have hx := valIn_E (hint x (by simp [Compile.intOperandsF]))
               obtain ⟨hR1, hR2⟩ := resIn1 hres (F := famTab[33])
                 (by simpa [famTab] using ofClif_fCTys hfty) (by simpa [famTab] using ofClif_fCTys hfty)
               exact ⟨33, _, rfl, famOk_of hrv hlen hR1 hR2
                 (by rw [← hdata]; exact γ_idata (by decide) ⟨γ_opAlts (by decide), γ_val hx, trivial⟩)⟩)
            -- `fcvt_to_uint_sat`, `fcvt_to_sint_sat`: a float operand, an `i32`/`i64` result
            | (have hx := hfl x (by simp [Compile.floatArgs, Backend.fBinaryOpcode,
                 Backend.fUnaryOpcode, Compile.floatOperands]) (by simp)
               have hI : CTy.ofClif ty ∈ [CTy.int 32, CTy.int 64] := by
                 simp [Backend.fCvtTyOk] at hty
                 rcases hty with rfl | rfl <;> simp [CTy.ofClif]
               obtain ⟨hR1, hR2⟩ := resIn1 hres (F := famTab[34]) (by simpa [famTab] using hI)
                 (by simpa [famTab] using hI)
               exact ⟨34, _, rfl, famOk_of hrv hlen hR1 hR2
                 (by rw [← hdata]; exact γ_idata (by decide) ⟨γ_opAlts (by decide), γ_val hx, trivial⟩)⟩)
        · cases hdata
      · cases hdata
  · -- two operands: arithmetic or `fcmp`
    simp only [instData] at hdata
    split at hdata
    · rename_i n hn
      split at hdata
      · rename_i hty
        simp only [pure, Except.pure, Except.ok.injEq] at hdata
        have hfa' : ∀ w ∈ [x, y], w ∈ Compile.floatArgs (.float op ty [x, y]) := by
          intro w hw; simp [Compile.floatArgs, hn, hw]
        have hxy := γ_vals2 (ctx := ctx) (hfl x (hfa' x (by simp)) (by simp))
          (hfl y (hfa' y (by simp)) (by simp))
        have hres1 : info.resTys = [CTy.ofClif ty] := by
          have : tys = [ty] := by
            cases op <;> simp only [Backend.fBinaryOpcode, reduceCtorEq] at hn <;>
              simp only [Clif.Inst.resultTypes, Option.some.injEq] at htys <;> exact htys.symm
          rw [hres, this]; rfl
        have hfty : ty.isFloat = true := by
          cases op <;> simp_all [Backend.fTyOk, Backend.fBinaryOpcode]
        obtain ⟨hR1, hR2⟩ := resIn1 hres1 (F := famTab[31])
          (by simpa [famTab] using ofClif_fCTys hfty) (by simpa [famTab] using ofClif_fCTys hfty)
        refine ⟨31, _, rfl, famOk_of hrv hlen hR1 hR2 ?_⟩
        rw [← hdata]
        refine γ_idata (by decide) ⟨γ_opAlts ?_, hxy, trivial⟩
        cases op <;> simp_all [Backend.fBinaryOpcode] <;> (subst hn; decide)
      · cases hdata
    · rename_i hnb
      split at hdata
      · rename_i cc
        split at hdata
        · rename_i hok
          simp only [Bool.and_eq_true] at hok
          simp only [pure, Except.pure, Except.ok.injEq] at hdata
          simp only [Clif.Inst.resultTypes, Option.some.injEq] at htys
          subst htys
          simp only [List.map_cons, List.map_nil] at hres
          have hfa' : ∀ w ∈ [x, y], w ∈ Compile.floatArgs (.float (.fcmp cc) ty [x, y]) := by
            intro w hw; simp [Compile.floatArgs, Backend.fBinaryOpcode, Backend.fUnaryOpcode,
              Compile.floatOperands, hw]
          have hxy := γ_vals2 (ctx := ctx) (hfl x (hfa' x (by simp)) (by simp))
            (hfl y (hfa' y (by simp)) (by simp))
          obtain ⟨hR1, hR2⟩ := resIn1 (ty := .i8) hres (F := famTab[35]) (by simp [famTab, CTy.ofClif])
            (by simp [famTab, CTy.ofClif])
          refine ⟨35, _, rfl, famOk_of hrv hlen hR1 hR2 ?_⟩
          rw [← hdata]
          refine γ_idata (by decide) ⟨γ_opAlts (by decide), hxy, γ_enumAlts ?_, trivial⟩
          have h2 := hok.2
          cases cc <;> simp [Backend.fccOk] at h2 <;> decide
        · cases hdata
      · cases hdata
  · simp [instData, throw, throwThe, MonadExceptOf.throw] at hdata

/-- **Every statement of a float-scope function belongs to an instruction family.** -/
theorem famCover_ofF {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {st0 : LState}
    (hs : LowerScopeTF f) (hfa : Compile.floatArgsTyped f = true) (hdom : dominatedB f = true)
    (hst : Compile.storeTypedB f = true) (hsel : Compile.selectTypedB f = true)
    (hb : buildCtx f = .ok (ctx, ranges, st0)) : FamCover ctx := by
  refine famCover_ofG (ctxInvT_ofF hs hb) hs.externsE (fun B hB s hsB => ?_)
    (famFloat_of hs hfa hdom hb) hdom hst hsel hb
  have h := (functionETF_parts hs.subsetTF).2.2.1 B hB
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  have hi := h.1.2 s hsB
  cases hsi : s.inst with
  | float op ty args => exact .inr ⟨op, ty, args, rfl⟩
  | _ =>
    rw [hsi] at hi
    left
    simpa [Compile.instETF, Compile.instETA, Compile.fArithET, Compile.fCvtET, Compile.fCmpET]
      using hi

/-- **A terminator of a float-scope function belongs to a terminator family.** -/
theorem termFam_ofF {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {st0 : LState}
    (hs : LowerScopeTF f) (hb : buildCtx f = .ok (ctx, ranges, st0))
    {B : Clif.Block} (hB : B ∈ f.blocks) {data : V}
    (hd : termData (abiTerm f B.term) = .ok data ∨ tryCallData f B.term = .ok data) :
    ∃ (i : Nat) (F : Fam), famTab[i]? = some F ∧ FamOk ctx F ⟨data, [], [], none⟩ := by
  have sp := ctxSpec_of hb
  refine termFam_ofG (ctxInvT_ofF hs hb) (fun x hx => ?_) hd
  refine valIn_E fun t ht => ?_
  have hO := (functionETF_parts hs.subsetTF).2.2.2.1
  simp only [Compile.opsTypedTF, Bool.and_eq_true, List.all_eq_true] at hO
  have h2 := (hO B hB).2 x hx
  exact sp.eCTys_of_not_floatDef ht (by simpa using h2)

/-- **The results of a `call`/`call_indirect` of a float-scope function are of class `int`.** -/
theorem callRes_intF {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {st0 : LState}
    (hs : LowerScopeTF f) (hdom : dominatedB f = true) (hb : buildCtx f = .ok (ctx, ranges, st0))
    {j : Nat} {info : IInfo} {c : Clif.Inst} (hj : ctx.insts[j]? = some info)
    (hc : info.clif = some c) (hcall : Cov.CallInst c) :
    ∀ x ∈ info.results, valClassOf ctx x = .int :=
  callRes_intG (ctxInvT_ofF hs hb) hs.externsE hdom hb hj hc hcall

end Backend.Proof.CovT
