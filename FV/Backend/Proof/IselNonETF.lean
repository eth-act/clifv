import FV.Backend.Proof.IselNonETI
import FV.Backend.Proof.LowerContractTF

/-!
# The integer roots never match a non-E instruction with the proven float operations (S11f)

`IselNonETI`'s checker over the instructions of `Compile.instETF`: besides the float movement,
a non-E instruction may be an S11f float arithmetic or rounding instruction (a float result, an
opcode of `arithOps`) or a conversion (`fcvt_to_*_sat`: an integer result, `cvtIOps`;
`fcvt_from_*`: a float result, `cvtFOps`). `rootNEF` evaluates a root pattern against them
(`nonE_splitF`), with `failsArgsTG p opsTF floatOpsF` for the fields (look-through instructions
of `InstScopeTF`, `inst_splitF_calls`). `nonEOkF` also exempts the conversion roots
(`floatCvtRootRule`, `LowerRulesCorrectCvtT`).

* `nonEOkF_program` (one kernel decision), `nonE_splitF`, `rootNEF_sound`;
* `nonEUnmatchableTF_program : NonEUnmatchableTF program`.

`nonEUnmatchableT_program` and its checker are unchanged.
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-- Opcodes of the non-E instructions of `instETF` with an integer or no result. -/
def neIOpsF : List Nat := neIOps ++ cvtIOps

/-- Opcodes of the non-E instructions of `instETF` with a float result (`select` only when
`sel = false`). -/
def neFOpsF (sel : Bool) : List Nat := neFOps sel ++ arithOps ++ cvtFOps

section
variable (p : Program)

mutual
/-- **Root checker**: the root pattern `q` matches no non-E instruction of a context with the
proven float operations. -/
def rootNEF (sel : Bool) : Pattern → Bool
  | .bind _ _ q => rootNEF sel q
  | .and _ qs => rootNEFAny sel qs
  | .term _ t args =>
    match termOf p t with
    | .error _ => true
    | .ok term =>
      match term.kind with
      | .decl flags _ (some (.external _ _)) =>
        if flags.isMulti then true else
        term.id == TId.inst_data_value &&
          failsArgsTG p opsTF floatOpsF [.tys (.invalid :: eCTys), .data neIOpsF] args &&
          failsArgsTG p opsTF floatOpsF [.tys fTys, .data (neFOpsF sel)] args
      | _ => false
  | _ => false

/-- Some conjunct is refuted. -/
def rootNEFAny (sel : Bool) : List Pattern → Bool
  | [] => false
  | q :: qs => rootNEF sel q || rootNEFAny sel qs
end

/-- A closure root of `lower` that is not a float root (movement, memory, arithmetic,
conversion) nor an integer `store` root is refuted on the non-E instructions. -/
def nonEOkF (r : Rule) : Bool :=
  !closureRootIds.contains r.id || floatMoveRootRule r || floatMemRootRule r ||
    floatArithRootRule r || floatCvtRootRule r || intStoreRoot r ||
    match r.args with
    | [q] => rootNEF p (r.id == 971) q
    | _ => false

end

set_option maxRecDepth 100000 in
/-- Checked over the exported rule list. -/
theorem nonEOkF_program : (program.rulesOf TId.lower).all (nonEOkF program) = true := by
  rw [show TId.lower = 686 from rfl, data_program.r686]
  decide +kernel

/-! ## The non-E instructions -/

theorem aNames_neF (sel : Bool) : aNamePairs.all (fun pr =>
    match variantIdx 152 pr.1, variantIdx 151 pr.2 with
    | some _, some ko => (neFOpsF sel).contains ko
    | _, _ => false) = true := by
  cases sel <;> decide +kernel

theorem cvtFNames_neF (sel : Bool) : [("Unary", "FcvtFromUint"), ("Unary", "FcvtFromSint")].all
    (fun pr => match variantIdx 152 pr.1, variantIdx 151 pr.2 with
    | some _, some ko => (neFOpsF sel).contains ko
    | _, _ => false) = true := by
  cases sel <;> decide +kernel

theorem cvtINames_neI : [("Unary", "FcvtToUintSat"), ("Unary", "FcvtToSintSat")].all
    (fun pr => match variantIdx 152 pr.1, variantIdx 151 pr.2 with
    | some _, some ko => neIOpsF.contains ko
    | _, _ => false) = true := by
  decide +kernel

/-- **A non-E instruction of the scope with the proven float operations**: an integer or no
result with an opcode of `neIOpsF`, or a float result with one of `neFOpsF sel`. -/
theorem nonE_splitF {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx) {j : Nat}
    {info : IInfo} {c : Clif.Inst} (hi : ctx.insts[j]? = some info) (hc : info.clif = some c)
    (hd : instData f c = .ok info.data) (hTF : Compile.instETF c = true)
    (hE : Compile.instE c = false) {sel : Bool} (hsel : sel = true → ¬ FloatSelect c) :
    (info.resTys.head?.getD .invalid ∈ (.invalid :: eCTys) ∧
        (AVT.data neIOpsF).HoldsS Compile.instETF f ctx info.data) ∨
      (info.resTys.head?.getD .invalid ∈ fTys ∧
        (AVT.data (neFOpsF sel)).HoldsS Compile.instETF f ctx info.data) := by
  have hT := hTF
  simp only [Compile.instETF, Compile.instETA, Bool.or_eq_true] at hT
  rcases hT with (hT | hA) | hV
  · rcases nonE_split hctx hi hc hd hT hE hsel with ⟨h1, c', hT', hc', kf, ko, fs, he, hko⟩ |
      ⟨h1, c', hT', hc', kf, ko, fs, he, hko⟩
    · exact .inl ⟨h1, c', Compile.instETF_of_instET hT', hc', kf, ko, fs, he,
        List.mem_append_left _ hko⟩
    · exact .inr ⟨h1, c', Compile.instETF_of_instET hT', hc', kf, ko, fs, he,
        List.mem_append_left _ (List.mem_append_left _ hko)⟩
  · cases c with
    | float op ty args =>
      rcases instData_names hd with ⟨rest, hd'⟩ | ⟨ty', imm, he, -⟩
      · refine .inr ⟨fArith_resTy hctx hA hi hc, _, hTF, hd, data_of_names hd' ?_ (aNames_neF sel)⟩
        rcases fArithET_op hA with ho | ho <;>
          cases op <;> simp [fBinaryOpcode, fUnaryOpcode] at ho <;>
          simp [instNames, fFmt, fOpc, aNamePairs]
      · cases he
    | _ => simp [Compile.fArithET] at hA
  · obtain ⟨op, ty, x, rfl, (⟨hop, hty⟩ | ⟨hop, hty⟩)⟩ := fCvtET_cases hV
    · rcases instData_names hd with ⟨rest, hd'⟩ | ⟨ty', imm, he, -⟩
      · refine .inr ⟨?_, _, hTF, hd, data_of_names hd' ?_ (cvtFNames_neF sel)⟩
        · rw [float_resTy hctx (fun cc e => by rcases hop with rfl | rfl <;> cases e) hi hc]
          revert hty; cases ty <;> simp [fTys, CTy.ofClif, Clif.Ty.isFloat]
        · rcases hop with rfl | rfl <;> simp [instNames, fFmt, fOpc]
      · cases he
    · rcases instData_names hd with ⟨rest, hd'⟩ | ⟨ty', imm, he, -⟩
      · refine .inl ⟨?_, _, hTF, hd, data_of_names hd' ?_ cvtINames_neI⟩
        · rw [float_resTy hctx (fun cc e => by rcases hop with rfl | rfl <;> cases e) hi hc]
          rcases hty with rfl | rfl <;> simp [eCTys, CTy.ofClif]
        · rcases hop with rfl | rfl <;> simp [instNames, fFmt, fOpc]
      · cases he

/-! ## Soundness -/

section
variable {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx) (hsc : InstScopeTF ctx)
  (hx : CallsE f ctx) {ii : Nat} {info : IInfo} {sel : Bool}
  (hsp : (info.resTys.head?.getD .invalid ∈ (.invalid :: eCTys) ∧
        (AVT.data neIOpsF).HoldsS Compile.instETF f ctx info.data) ∨
      (info.resTys.head?.getD .invalid ∈ fTys ∧
        (AVT.data (neFOpsF sel)).HoldsS Compile.instETF f ctx info.data))
  (hi : ctx.insts[ii]? = some info)
include hctx hsc hx hsp hi

mutual
theorem rootNEF_sound : ∀ (q : Pattern) (st : LState) (env env' : Interp.Env V),
    rootNEF program sel q = true →
    matchPat program (sem ctx) st q (.inst ii) env = .ok (some env') → False
  | .bind ty x q, st, env, env', hf, hm => by
    rw [rootNEF.eq_1] at hf
    exact rootNEF_sound q st _ env' hf (matchPat_bind_inv hm).2
  | .and ty qs, st, env, env', hf, hm => by
    rw [rootNEF.eq_2] at hf
    rw [matchPat.eq_7] at hm
    exact rootNEFAny_sound qs st env env' hf hm
  | .term ty t args, st, env, env', hf, hm => by
    rw [rootNEF.eq_3] at hf
    cases ht : termOf program t with
    | error e => exact matchPat_termOf_error ht hm
    | ok term =>
      rw [ht] at hf
      simp only at hf
      cases hk : term.kind with
      | decl flags c ex =>
        rw [hk] at hf
        cases ex with
        | none => simp at hf
        | some ex =>
          cases ex with
          | internal form => simp at hf
          | external fn inf =>
            simp only at hf
            cases hmu : flags.isMulti
            · rw [hmu] at hf
              simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at hf
              obtain ⟨⟨hid, hf1⟩, hf2⟩ := hf
              obtain ⟨fs, hx', hma⟩ := matchPat_extract_inv ht hk hmu hm
              rw [sem_extract] at hx'
              obtain ⟨info', hi', rfl⟩ := ext_idv_inv hid hx'
              rw [hi] at hi'
              cases hi'
              rcases hsp with ⟨h1, h2⟩ | ⟨h1, h2⟩
              · exact failsArgsTG_sound hctx (inst_splitF_calls hctx hsc hx) args _
                  [.ty (info.resTys.head?.getD .invalid), info.data] st env env' hf1
                  ⟨⟨_, h1, rfl⟩, h2, trivial⟩ hma
              · exact failsArgsTG_sound hctx (inst_splitF_calls hctx hsc hx) args _
                  [.ty (info.resTys.head?.getD .invalid), info.data] st env env' hf2
                  ⟨⟨_, h1, rfl⟩, h2, trivial⟩ hma
            · exact matchPat_multi ht hk hmu hm
      | _ => rw [hk] at hf; simp at hf
  | .var .., _, _, _, hf, _ => by simp [rootNEF] at hf
  | .constBool .., _, _, _, hf, _ => by simp [rootNEF] at hf
  | .constInt .., _, _, _, hf, _ => by simp [rootNEF] at hf
  | .constPrim .., _, _, _, hf, _ => by simp [rootNEF] at hf
  | .wildcard .., _, _, _, hf, _ => by simp [rootNEF] at hf

theorem rootNEFAny_sound : ∀ (qs : List Pattern) (st : LState) (env env' : Interp.Env V),
    rootNEFAny program sel qs = true →
    matchAll program (sem ctx) st qs (.inst ii) env = .ok (some env') → False
  | [], _, _, _, hf, _ => by simp [rootNEFAny] at hf
  | q :: qs, st, env, env', hf, hm => by
    rw [rootNEFAny.eq_2, Bool.or_eq_true] at hf
    obtain ⟨e1, h1, h2⟩ := matchAll_cons_inv_ex hm
    rcases hf with hf | hf
    · exact rootNEF_sound q st env e1 hf h1
    · exact rootNEFAny_sound qs st e1 env' hf h2
end

end

/-! ## The theorem -/

/-- **The integer roots never match the non-E instructions of a typed context with the proven
float operations.** -/
theorem nonEUnmatchableTF_program : NonEUnmatchableTF program := by
  intro r hr hroot hfm hmm hfa hfc f ctx hctx ii info inst hi hc hE hsel hst cfg m st tr env' s1
    _ hmatch
  have hok := List.all_eq_true.mp nonEOkF_program r hr
  rw [closureRoot_eq] at hroot
  simp only [nonEOkF, hroot, hfm, hmm, hfa, hfc, Bool.not_true, Bool.false_or] at hok
  cases his : intStoreRoot r
  · rw [his, Bool.false_or] at hok
    cases m with
    | zero => rw [matchRule.eq_1] at hmatch; cases hmatch
    | succ m =>
      obtain ⟨env0, ha, -⟩ := matchRule_some_inv hmatch
      split at hok
      · rename_i q hargs
        rw [hargs] at ha
        obtain ⟨e1, h1, -⟩ := matchArgs_cons_inv ha
        have hd := hctx.inv.data ii info inst hi hc
        have hsp := nonE_splitF hctx.inv hi hc hd (hctx.scope ii info inst hi hc) hE
          (sel := r.id == 971) (fun h => hsel (beq_iff_eq.mp h))
        exact rootNEF_sound hctx.inv hctx.scope hctx.calls hsp hi q _ _ _ hok h1
      · cases hok
  · exact intStore_nonE hr his hctx hi hc hE hst hmatch

end Backend.Proof
