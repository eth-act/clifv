import FV.Backend.Proof.IselNonETF
import FV.Backend.Proof.LowerContractTS

/-!
# Exclusion and non-E unmatchability with the literal pool (#1002 part 2)

The scope `Compile.instETFL` admits an `f64const` of any bits (`InstScopeTFL`). Its instruction
data is an `f64const`'s whatever its bits (`instData_f64const_eq`), with a float result
(`f64const_resTy`), and its opcode is in `floatOpsFC`/`neFOpsF`, so the exclusion and non-E
checkers' kernel decisions (`exclOkTFC_program`, `nonEOkFC_program`) cover it as they cover an
`f64const` without literal pool:

* `inst_splitFCL1`, `inst_splitFCL`, `lower_nonroot_nomatchTFCL`: `inst_splitFC1`,
  `inst_splitFC`, `lower_nonroot_nomatchTFC` over `InstScopeTFL`;
* `nonE_splitFL`, `rootNEFCL_sound`: `nonE_splitF`, `rootNEFC_sound` over `Compile.instETFL`;
* `intStore_nonES`, `nonEUnmatchableTFS_program`: `intStore_nonEW` and `nonEUnmatchableTFW_program`
  over `CtxTS S` for every scope `S` inside `InstScopeTFL`.

The theorems over `InstScopeTF` and `CtxTW` are unchanged.
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-- The data of an `f64const`, whatever its bits: the `UnaryIeee64`/`F64const` variant. -/
theorem instData_f64const_eq {f : Clif.Function} {imm : BitVec 64} {d : V}
    (h : instData f (.iconst .f64 imm) = .ok d) :
    d = .data 152 34 [.data 151 60 [], .int imm.toNat] := by
  simp [instData, eTy, pure, Except.pure, instDataV_UnaryIeee64, opcodeV_F64const] at h
  first | exact h.symm | exact h

/-- **An `f64const` of a float-capable context**, whatever its bits: a float result (`f64`). -/
theorem f64const_resTy {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx) {j : Nat}
    {info : IInfo} {imm : BitVec 64} (hi : ctx.insts[j]? = some info)
    (hc : info.clif = some (.iconst .f64 imm)) :
    info.resTys.head?.getD .invalid ∈ fTys := by
  obtain ⟨tys, htys, hres, -⟩ := hctx.resTys j info _ hi hc
  have : tys = [.f64] := by simpa [Clif.Inst.resultTypes] using htys.symm
  subst this
  rw [hres]
  decide

/-- An instruction of `Compile.instETFL` outside `Compile.instETF` is an `f64const`. -/
theorem f64const_of_instETFL {c : Clif.Inst} (hL : Compile.instETFL c = true)
    (hF : Compile.instETF c = false) : ∃ imm : BitVec 64, c = .iconst .f64 imm := by
  have h : Compile.f64ConstET c = true := by simpa [Compile.instETFL, hF] using hL
  cases c with
  | iconst ty imm =>
    simp only [Compile.f64ConstET, beq_iff_eq] at h
    subst h
    exact ⟨imm, rfl⟩
  | _ => simp [Compile.f64ConstET] at h

/-- **One instruction of a context with the proven float operations, float calls and the literal
pool**: `inst_splitFC1` over `Compile.instETFL`. -/
theorem inst_splitFCL1 {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx) {j : Nat}
    {info : IInfo} {c : Clif.Inst} (hTF : Compile.instETFL c = true)
    (hi : ctx.insts[j]? = some info) (hc : info.clif = some c) (hd : instData f c = .ok info.data) :
    (info.resTys.head?.getD .invalid ∈ (.invalid :: eCTys) ∧
        (AVT.data opsTF).HoldsS Compile.instETFL f ctx info.data) ∨
      (info.resTys.head?.getD .invalid ∈ fTys ∧
        (AVT.data floatOpsFC).HoldsS Compile.instETFL f ctx info.data) := by
  cases hF : Compile.instETF c
  · obtain ⟨imm, rfl⟩ := f64const_of_instETFL hTF hF
    exact .inr ⟨f64const_resTy hctx hi hc, _, hTF, hd, 34, 60, _, instData_f64const_eq hd,
      by decide⟩
  · rcases inst_splitFC1 hctx hF hi hc hd with ⟨h1, c', hS, hd', rest⟩ | ⟨h1, c', hS, hd', rest⟩
    · exact .inl ⟨h1, c', Compile.instETFL_of_instETF hS, hd', rest⟩
    · exact .inr ⟨h1, c', Compile.instETFL_of_instETF hS, hd', rest⟩

/-- **An instruction of a context with the literal pool**: `InstSplit` at `opsTF`/`floatOpsFC`
over `Compile.instETFL`. -/
theorem inst_splitFCL {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx)
    (hsc : InstScopeTFL ctx) : InstSplit Compile.instETFL f ctx opsTF floatOpsFC :=
  fun hi hc hd => inst_splitFCL1 hctx (hsc _ _ _ hi hc) hi hc hd

/-- **The root rules of `lower` outside the closure never match an instruction of a
float-capable context with the proven float operations and the literal pool** (instructions in
`InstScopeTFL`, `call`s of any typed signature): `lower_nonroot_nomatchTFC` over
`InstScopeTFL`. -/
theorem lower_nonroot_nomatchTFCL {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx)
    (hsc : InstScopeTFL ctx) {ii : Nat}
    {info : IInfo} {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
    {r : Rule} (hr : r ∈ program.rulesOf TId.lower) (hroot : closureRootIds.contains r.id = false) :
    ∀ cfg m s0 env s1, (matchRule program (sem ctx) cfg m r [.inst ii]).run s0 ≠ .ok (some env, s1) := by
  intro cfg m s0 env' s1 hmatch
  have hok := List.all_eq_true.mp exclOkTFC_program r hr
  simp only [exclOkTFC, hroot, Bool.false_or] at hok
  cases h952 : r.id == 952
  · rw [h952, Bool.false_or] at hok
    cases m with
    | zero => rw [matchRule.eq_1] at hmatch; cases hmatch
    | succ m =>
      obtain ⟨env0, ha, -⟩ := matchRule_some_inv hmatch
      split at hok
      · rename_i q hargs
        rw [hargs] at ha
        obtain ⟨e1, h1, -⟩ := matchArgs_cons_inv ha
        exact failsTG_sound hctx (inst_splitFCL hctx hsc) q .inst _ _ _ _ hok
          ⟨ii, info, inst, rfl, hi, hc, hctx.data ii info inst hi hc⟩ h1
      · cases hok
  · have hsub : r ∈ (program.rulesOf TId.lower).filter (·.id == 952) :=
      List.mem_filter.2 ⟨hr, h952⟩
    rw [lower_rule952_filter, List.mem_singleton] at hsub
    subst hsub
    exact rule_lower_2179_nomatchT hctx hi hc hmatch

/-- **A non-E instruction of the scope with the proven float operations and the literal pool**
(`nonE_splitF` over `Compile.instETFL`). -/
theorem nonE_splitFL {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx) {j : Nat}
    {info : IInfo} {c : Clif.Inst} (hi : ctx.insts[j]? = some info) (hc : info.clif = some c)
    (hd : instData f c = .ok info.data) (hTF : Compile.instETFL c = true)
    (hE : Compile.instE c = false) {sel : Bool} (hsel : sel = true → ¬ FloatSelect c) :
    (info.resTys.head?.getD .invalid ∈ (.invalid :: eCTys) ∧
        (AVT.data neIOpsF).HoldsS Compile.instETFL f ctx info.data) ∨
      (info.resTys.head?.getD .invalid ∈ fTys ∧
        (AVT.data (neFOpsF sel)).HoldsS Compile.instETFL f ctx info.data) := by
  cases hF : Compile.instETF c
  · obtain ⟨imm, rfl⟩ := f64const_of_instETFL hTF hF
    exact .inr ⟨f64const_resTy hctx hi hc, _, hTF, hd, 34, 60, _, instData_f64const_eq hd,
      by cases sel <;> decide⟩
  · rcases nonE_splitF hctx hi hc hd hF hE hsel with ⟨h1, c', hS, hd', rest⟩ |
      ⟨h1, c', hS, hd', rest⟩
    · exact .inl ⟨h1, c', Compile.instETFL_of_instETF hS, hd', rest⟩
    · exact .inr ⟨h1, c', Compile.instETFL_of_instETF hS, hd', rest⟩

section
variable {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx) (hsc : InstScopeTFL ctx)
  {ii : Nat} {info : IInfo} {sel : Bool}
  (hsp : (info.resTys.head?.getD .invalid ∈ (.invalid :: eCTys) ∧
        (AVT.data neIOpsF).HoldsS Compile.instETFL f ctx info.data) ∨
      (info.resTys.head?.getD .invalid ∈ fTys ∧
        (AVT.data (neFOpsF sel)).HoldsS Compile.instETFL f ctx info.data))
  (hi : ctx.insts[ii]? = some info)
include hctx hsc hsp hi

mutual
/-- `rootNEFC_sound` over `InstScopeTFL`. -/
theorem rootNEFCL_sound : ∀ (q : Pattern) (st : LState) (env env' : Interp.Env V),
    rootNEFC program sel q = true →
    matchPat program (sem ctx) st q (.inst ii) env = .ok (some env') → False
  | .bind ty x q, st, env, env', hf, hm => by
    rw [rootNEFC.eq_1] at hf
    exact rootNEFCL_sound q st _ env' hf (matchPat_bind_inv hm).2
  | .and ty qs, st, env, env', hf, hm => by
    rw [rootNEFC.eq_2] at hf
    rw [matchPat.eq_7] at hm
    exact rootNEFCLAny_sound qs st env env' hf hm
  | .term ty t args, st, env, env', hf, hm => by
    rw [rootNEFC.eq_3] at hf
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
              · exact failsArgsTG_sound hctx (inst_splitFCL hctx hsc) args _
                  [.ty (info.resTys.head?.getD .invalid), info.data] st env env' hf1
                  ⟨⟨_, h1, rfl⟩, h2, trivial⟩ hma
              · exact failsArgsTG_sound hctx (inst_splitFCL hctx hsc) args _
                  [.ty (info.resTys.head?.getD .invalid), info.data] st env env' hf2
                  ⟨⟨_, h1, rfl⟩, h2, trivial⟩ hma
            · exact matchPat_multi ht hk hmu hm
      | _ => rw [hk] at hf; simp at hf
  | .var .., _, _, _, hf, _ => by simp [rootNEFC] at hf
  | .constBool .., _, _, _, hf, _ => by simp [rootNEFC] at hf
  | .constInt .., _, _, _, hf, _ => by simp [rootNEFC] at hf
  | .constPrim .., _, _, _, hf, _ => by simp [rootNEFC] at hf
  | .wildcard .., _, _, _, hf, _ => by simp [rootNEFC] at hf

theorem rootNEFCLAny_sound : ∀ (qs : List Pattern) (st : LState) (env env' : Interp.Env V),
    rootNEFCAny program sel qs = true →
    matchAll program (sem ctx) st qs (.inst ii) env = .ok (some env') → False
  | [], _, _, _, hf, _ => by simp [rootNEFCAny] at hf
  | q :: qs, st, env, env', hf, hm => by
    rw [rootNEFCAny.eq_2, Bool.or_eq_true] at hf
    obtain ⟨e1, h1, h2⟩ := matchAll_cons_inv_ex hm
    rcases hf with hf | hf
    · exact rootNEFCL_sound q st env e1 hf h1
    · exact rootNEFCLAny_sound qs st e1 env' hf h2
end

end

/-- **An integer `store` root never matches a non-E instruction of a context over a scope inside
`InstScopeTFL`** whose float stores store float values (`intStore_nonEW` over `CtxTS S`). -/
theorem intStore_nonES {S : InstScope} (hS : ∀ ctx, S.P ctx → InstScopeTFL ctx) {r : Rule}
    (hr : r ∈ program.rulesOf TId.lower) (hs : intStoreRoot r = true)
    {f : Clif.Function} {ctx : Ctx} (hctx : CtxTS S f ctx) {ii : Nat} {info : IInfo}
    {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
    (hE : Compile.instE inst = false) (hst : StoreTyped ctx inst) {cfg : Config} {m : Nat}
    {st : LState} {tr : Array RuleId} {env' : Interp.Env V} {s1 : LState × Array RuleId}
    (hmatch : (matchRule program (sem ctx) cfg m r [.inst ii]).run (st, tr) = .ok (some env', s1)) :
    False := by
  have hsub : r ∈ (program.rulesOf TId.lower).filter intStoreRoot := List.mem_filter.2 ⟨hr, hs⟩
  rw [lower_intStoreRoot_filter] at hsub
  have hT := hS ctx hctx.scope ii info inst hi hc
  have hd := hctx.inv.data ii info inst hi hc
  cases m with
  | zero => rw [matchRule.eq_1] at hmatch; cases hmatch
  | succ m =>
  have hp := data_program
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hsub
  rcases hsub with rfl | rfl | rfl | rfl <;>
  · mem_inv hp [] at hmatch
    have hw := ‹ctx.insts[ii]? = some _›
    rw [hi, Option.some.injEq] at hw
    subst hw
    have hdd : V.data 152 22 _ = _ := ‹V.data 152 22 _ = _›
    obtain ⟨op, ty, fl, x, q, off, rfl, -, rfl, -, -, -, -⟩ :=
      inv_store_root (hd.trans (congrArg Except.ok hdd.symm))
    simp only [ext_value_array_2_iff, List.cons.injEq, and_true] at *
    isel_destruct; subst_vars
    obtain ⟨t, hvt, ht⟩ := (ext_value_type_iff _ _ _ _).mp ‹externExtract ctx T.value_type (.value x) _ = _›
    simp only [List.cons.injEq, V.ty.injEq, and_true] at ht
    subst ht
    have hf : ty.isFloat = true := by
      revert hT hE; cases ty <;> cases op <;>
        simp [Compile.instETFL, Compile.f64ConstET, Compile.instETF, Compile.instETA,
          Compile.fArithET, Compile.fCvtET, Compile.fCmpET,
          Compile.instET, Compile.instE, Compile.tyE, Clif.Ty.isFloat]
    have := hst _ _ _ _ _ _ rfl hf _ hvt
    simp [fTys] at this

/-- **The integer roots never match the non-E instructions of a context over a scope inside
`InstScopeTFL`** (`nonEUnmatchableTFW_program` over `CtxTS S`: an `f64const` from the literal
pool among the instructions, `nonE_splitFL`, `rootNEFCL_sound`). -/
theorem nonEUnmatchableTFS_program {S : InstScope} (hS : ∀ ctx, S.P ctx → InstScopeTFL ctx) :
    NonEUnmatchableTFS S program := by
  intro r hr hroot hfm hmm hfa hfc hfcmp f ctx hctx ii info inst hi hc hE hsel hst cfg m st tr
    env' s1 _ hmatch
  have hok := List.all_eq_true.mp nonEOkFC_program r hr
  rw [closureRoot_eq] at hroot
  simp only [nonEOkFC, hroot, hfm, hmm, hfa, hfc, hfcmp, Bool.not_true, Bool.false_or] at hok
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
        have hsc := hS ctx hctx.scope
        have hsp := nonE_splitFL hctx.inv hi hc hd (hsc ii info inst hi hc) hE
          (sel := r.id == 971) (fun h => hsel (beq_iff_eq.mp h))
        exact rootNEFCL_sound hctx.inv hsc hsp hi q _ _ _ hok h1
      · cases hok
  · exact intStore_nonES hS hr his hctx hi hc hE hst hmatch

end Backend.Proof
