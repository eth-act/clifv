import FV.Backend.Proof.IselPoolTFL
import FV.Backend.Proof.IselCopysignFamily
import FV.Backend.Proof.IselFmaFamily

/-!
# Exclusion and non-E unmatchability with `fcopysign` and `fma` (#35)

The scope `Compile.instETFLO` admits `fcopysign` and `fma` at `f32`/`f64` (`InstScopeTFLO`) besides
`Compile.instETFL`. Their instruction data has the opcode `Fcopysign`/`Fma` (`instData_copysignFma`)
and a float result (`copysignFma_resTy`). The exclusion and non-E checkers over the float-result
opcodes with these two (`floatOpsFCO`, `neFOpsFO`) are new kernel decisions (`exclOkTFCO_program`,
`nonEOkFCO_program`); the non-E checker also exempts the `fcopysign` and `fma` roots
(`copysignRootRule`, `fmaRootRule`: their families `LowerRulesCorrectCS`, `LowerRulesCorrectFM`).

* `inst_splitFCLO1`, `inst_splitFCLO`, `lower_nonroot_nomatchTFCLO`: `inst_splitFCL1`,
  `inst_splitFCL`, `lower_nonroot_nomatchTFCL` over `InstScopeTFLO`;
* `nonE_splitFLO`, `rootNEFCLO_sound`: `nonE_splitFL`, `rootNEFCL_sound` over `Compile.instETFLO`;
* `NonEUnmatchableTFSO S`: `NonEUnmatchableTFS S` for the closure roots outside the `fcopysign`
  and `fma` families; `intStore_nonESO`, `nonEUnmatchableTFSO_program` for every scope `S` inside
  `InstScopeTFLO`.

The theorems over `InstScopeTFL` (`IselPoolTFL.lean`) are unchanged.
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-- The opcodes of `fcopysign` and `fma` (float results). -/
def copysignFmaOps : List Nat := [VIdx.Opcode.Fcopysign, VIdx.Opcode.Fma]

/-- The float-result opcodes with the float calls, `fcopysign` and `fma`. -/
def floatOpsFCO : List Nat := floatOpsFC ++ copysignFmaOps

section
variable (p : Program)

/-- `exclOkTFC` over `floatOpsFCO`: a root rule of `lower` is in the closure, is
`rule_lower_2179`, or cannot match an instruction of a float-capable context whose instructions
are in `Compile.instETFLO`. -/
def exclOkTFCO (r : Rule) : Bool :=
  closureRootIds.contains r.id || r.id == 952 ||
    match r.args with
    | [q] => failsTG p opsTF floatOpsFCO .inst q
    | _ => false

end

set_option maxRecDepth 100000 in
/-- Every root rule of `lower` is a closure root, `rule_lower_2179`, or cannot match an
instruction of a float-capable context with the proven float operations, float calls,
`fcopysign` and `fma` (checked). -/
theorem exclOkTFCO_program : (program.rulesOf TId.lower).all (exclOkTFCO program) = true := by
  rw [show TId.lower = 686 from rfl, data_program.r686]
  decide +kernel

set_option maxRecDepth 20000 in
theorem copysignFmaNames_idx : [("Binary", "Fcopysign"), ("Ternary", "Fma")].all (fun pr =>
    match variantIdx 152 pr.1, variantIdx 151 pr.2 with
    | some _, some ko => copysignFmaOps.contains ko
    | _, _ => false) = true := by
  decide +kernel

/-- An instruction of `Compile.instETFLO` outside `Compile.instETFL` is an `fcopysign` or an
`fma` at `f32`/`f64`. -/
theorem copysignFma_of_instETFLO {c : Clif.Inst} (hO : Compile.instETFLO c = true)
    (hL : Compile.instETFL c = false) :
    ∃ op ty args, c = .float op ty args ∧ (op = .fcopysign ∨ op = .fma) ∧
      ty.isArithFloat = true := by
  simp only [Compile.instETFLO, hL, Bool.false_or, Bool.or_eq_true] at hO
  rcases hO with h | h
  · unfold Compile.fCopysignET at h
    split at h
    · exact ⟨_, _, _, rfl, .inl rfl, h⟩
    · cases h
  · unfold Compile.fFmaET at h
    split at h
    · exact ⟨_, _, _, rfl, .inr rfl, h⟩
    · cases h

set_option maxRecDepth 20000 in
/-- The data of an `fcopysign` or an `fma`: the opcode `Fcopysign`/`Fma` (`copysignFmaOps`). -/
theorem instData_copysignFma {f : Clif.Function} {op : Clif.FOp} {ty : Clif.Ty}
    {args : List Clif.ValueId} (hop : op = .fcopysign ∨ op = .fma) {d : V}
    (h : instData f (.float op ty args) = .ok d) :
    ∃ kf ko fs, d = .data 152 kf (.data 151 ko [] :: fs) ∧ ko ∈ copysignFmaOps := by
  rcases instData_names h with ⟨rest, hd⟩ | ⟨ty', imm, he, -⟩
  · refine data_of_names hd ?_ copysignFmaNames_idx
    rcases hop with rfl | rfl <;> simp [instNames, fFmt, fOpc]
  · cases he

/-- **An `fcopysign` or an `fma` of a float-capable context** at `f32`/`f64`: a float result. -/
theorem copysignFma_resTy {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx) {j : Nat}
    {info : IInfo} {op : Clif.FOp} {ty : Clif.Ty} {args : List Clif.ValueId}
    (hop : op = .fcopysign ∨ op = .fma) (hty : ty.isArithFloat = true)
    (hi : ctx.insts[j]? = some info) (hc : info.clif = some (.float op ty args)) :
    info.resTys.head?.getD .invalid ∈ fTys := by
  obtain ⟨tys, htys, hres, -⟩ := hctx.resTys j info _ hi hc
  have : tys = [ty] := by
    rcases hop with rfl | rfl <;> simpa [Clif.Inst.resultTypes] using htys.symm
  subst this
  rw [hres]
  cases ty <;> simp_all [fTys, CTy.ofClif]

/-- **One instruction of a context with the proven float operations, float calls, the literal
pool, `fcopysign` and `fma`**: `inst_splitFCL1` over `Compile.instETFLO`. -/
theorem inst_splitFCLO1 {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx) {j : Nat}
    {info : IInfo} {c : Clif.Inst} (hTF : Compile.instETFLO c = true)
    (hi : ctx.insts[j]? = some info) (hc : info.clif = some c) (hd : instData f c = .ok info.data) :
    (info.resTys.head?.getD .invalid ∈ (.invalid :: eCTys) ∧
        (AVT.data opsTF).HoldsS Compile.instETFLO f ctx info.data) ∨
      (info.resTys.head?.getD .invalid ∈ fTys ∧
        (AVT.data floatOpsFCO).HoldsS Compile.instETFLO f ctx info.data) := by
  cases hL : Compile.instETFL c
  · obtain ⟨op, ty, args, rfl, hop, hty⟩ := copysignFma_of_instETFLO hTF hL
    obtain ⟨kf, ko, fs, he, hko⟩ := instData_copysignFma hop hd
    exact .inr ⟨copysignFma_resTy hctx hop hty hi hc, _, hTF, hd, kf, ko, fs, he,
      List.mem_append_right _ hko⟩
  · rcases inst_splitFCL1 hctx hL hi hc hd with ⟨h1, c', hS, hd', kf, ko, fs, he, hko⟩ |
      ⟨h1, c', hS, hd', kf, ko, fs, he, hko⟩
    · exact .inl ⟨h1, c', Compile.instETFLO_of_instETFL hS, hd', kf, ko, fs, he, hko⟩
    · exact .inr ⟨h1, c', Compile.instETFLO_of_instETFL hS, hd', kf, ko, fs, he,
        List.mem_append_left _ hko⟩

/-- **An instruction of a context with `fcopysign` and `fma`**: `InstSplit` at
`opsTF`/`floatOpsFCO` over `Compile.instETFLO`. -/
theorem inst_splitFCLO {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx)
    (hsc : InstScopeTFLO ctx) : InstSplit Compile.instETFLO f ctx opsTF floatOpsFCO :=
  fun hi hc hd => inst_splitFCLO1 hctx (hsc _ _ _ hi hc) hi hc hd

/-- **The root rules of `lower` outside the closure never match an instruction of a
float-capable context with the proven float operations, the literal pool, `fcopysign` and
`fma`** (instructions in `InstScopeTFLO`, `call`s of any typed signature):
`lower_nonroot_nomatchTFCL` over `InstScopeTFLO`. -/
theorem lower_nonroot_nomatchTFCLO {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx)
    (hsc : InstScopeTFLO ctx) {ii : Nat}
    {info : IInfo} {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
    {r : Rule} (hr : r ∈ program.rulesOf TId.lower) (hroot : closureRootIds.contains r.id = false) :
    ∀ cfg m s0 env s1, (matchRule program (sem ctx) cfg m r [.inst ii]).run s0 ≠ .ok (some env, s1) := by
  intro cfg m s0 env' s1 hmatch
  have hok := List.all_eq_true.mp exclOkTFCO_program r hr
  simp only [exclOkTFCO, hroot, Bool.false_or] at hok
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
        exact failsTG_sound hctx (inst_splitFCLO hctx hsc) q .inst _ _ _ _ hok
          ⟨ii, info, inst, rfl, hi, hc, hctx.data ii info inst hi hc⟩ h1
      · cases hok
  · have hsub : r ∈ (program.rulesOf TId.lower).filter (·.id == 952) :=
      List.mem_filter.2 ⟨hr, h952⟩
    rw [lower_rule952_filter, List.mem_singleton] at hsub
    subst hsub
    exact rule_lower_2179_nomatchT hctx hi hc hmatch

/-! ## Non-E unmatchability -/

/-- Opcodes of the non-E instructions of `instETFLO` with a float result (`select` only when
`sel = false`): `neFOpsF` with `fcopysign` and `fma`. -/
def neFOpsFO (sel : Bool) : List Nat := neFOpsF sel ++ copysignFmaOps

/-- **A non-E instruction of the scope with `fcopysign` and `fma`** (`nonE_splitFL` over
`Compile.instETFLO`). -/
theorem nonE_splitFLO {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx) {j : Nat}
    {info : IInfo} {c : Clif.Inst} (hi : ctx.insts[j]? = some info) (hc : info.clif = some c)
    (hd : instData f c = .ok info.data) (hTF : Compile.instETFLO c = true)
    (hE : Compile.instE c = false) {sel : Bool} (hsel : sel = true → ¬ FloatSelect c) :
    (info.resTys.head?.getD .invalid ∈ (.invalid :: eCTys) ∧
        (AVT.data neIOpsF).HoldsS Compile.instETFLO f ctx info.data) ∨
      (info.resTys.head?.getD .invalid ∈ fTys ∧
        (AVT.data (neFOpsFO sel)).HoldsS Compile.instETFLO f ctx info.data) := by
  cases hL : Compile.instETFL c
  · obtain ⟨op, ty, args, rfl, hop, hty⟩ := copysignFma_of_instETFLO hTF hL
    obtain ⟨kf, ko, fs, he, hko⟩ := instData_copysignFma hop hd
    exact .inr ⟨copysignFma_resTy hctx hop hty hi hc, _, hTF, hd, kf, ko, fs, he,
      List.mem_append_right _ hko⟩
  · rcases nonE_splitFL hctx hi hc hd hL hE hsel with ⟨h1, c', hS, hd', kf, ko, fs, he, hko⟩ |
      ⟨h1, c', hS, hd', kf, ko, fs, he, hko⟩
    · exact .inl ⟨h1, c', Compile.instETFLO_of_instETFL hS, hd', kf, ko, fs, he, hko⟩
    · exact .inr ⟨h1, c', Compile.instETFLO_of_instETFL hS, hd', kf, ko, fs, he,
        List.mem_append_left _ hko⟩

section
variable (p : Program)

mutual
/-- **Root checker with `fcopysign` and `fma`**: `rootNEFC` with the fields over `floatOpsFCO`
and the float-result opcodes `neFOpsFO`. -/
def rootNEFCO (sel : Bool) : Pattern → Bool
  | .bind _ _ q => rootNEFCO sel q
  | .and _ qs => rootNEFCOAny sel qs
  | .term _ t args =>
    match termOf p t with
    | .error _ => true
    | .ok term =>
      match term.kind with
      | .decl flags _ (some (.external _ _)) =>
        if flags.isMulti then true else
        term.id == TId.inst_data_value &&
          failsArgsTG p opsTF floatOpsFCO [.tys (.invalid :: eCTys), .data neIOpsF] args &&
          failsArgsTG p opsTF floatOpsFCO [.tys fTys, .data (neFOpsFO sel)] args
      | _ => false
  | _ => false

/-- Some conjunct is refuted. -/
def rootNEFCOAny (sel : Bool) : List Pattern → Bool
  | [] => false
  | q :: qs => rootNEFCO sel q || rootNEFCOAny sel qs
end

/-- `nonEOkFC` with `rootNEFCO`, the `fcopysign` and `fma` roots exempt. -/
def nonEOkFCO (r : Rule) : Bool :=
  !closureRootIds.contains r.id || floatMoveRootRule r || floatMemRootRule r ||
    floatArithRootRule r || floatCvtRootRule r || floatCmpRootRule r || copysignRootRule r ||
    fmaRootRule r || intStoreRoot r ||
    match r.args with
    | [q] => rootNEFCO p (r.id == 971) q
    | _ => false

end

set_option maxRecDepth 100000 in
/-- Checked over the exported rule list. -/
theorem nonEOkFCO_program : (program.rulesOf TId.lower).all (nonEOkFCO program) = true := by
  rw [show TId.lower = 686 from rfl, data_program.r686]
  decide +kernel

section
variable {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx) (hsc : InstScopeTFLO ctx)
  {ii : Nat} {info : IInfo} {sel : Bool}
  (hsp : (info.resTys.head?.getD .invalid ∈ (.invalid :: eCTys) ∧
        (AVT.data neIOpsF).HoldsS Compile.instETFLO f ctx info.data) ∨
      (info.resTys.head?.getD .invalid ∈ fTys ∧
        (AVT.data (neFOpsFO sel)).HoldsS Compile.instETFLO f ctx info.data))
  (hi : ctx.insts[ii]? = some info)
include hctx hsc hsp hi

mutual
/-- `rootNEFCL_sound` over `InstScopeTFLO` (`rootNEFCO`). -/
theorem rootNEFCLO_sound : ∀ (q : Pattern) (st : LState) (env env' : Interp.Env V),
    rootNEFCO program sel q = true →
    matchPat program (sem ctx) st q (.inst ii) env = .ok (some env') → False
  | .bind ty x q, st, env, env', hf, hm => by
    rw [rootNEFCO.eq_1] at hf
    exact rootNEFCLO_sound q st _ env' hf (matchPat_bind_inv hm).2
  | .and ty qs, st, env, env', hf, hm => by
    rw [rootNEFCO.eq_2] at hf
    rw [matchPat.eq_7] at hm
    exact rootNEFCLOAny_sound qs st env env' hf hm
  | .term ty t args, st, env, env', hf, hm => by
    rw [rootNEFCO.eq_3] at hf
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
              · exact failsArgsTG_sound hctx (inst_splitFCLO hctx hsc) args _
                  [.ty (info.resTys.head?.getD .invalid), info.data] st env env' hf1
                  ⟨⟨_, h1, rfl⟩, h2, trivial⟩ hma
              · exact failsArgsTG_sound hctx (inst_splitFCLO hctx hsc) args _
                  [.ty (info.resTys.head?.getD .invalid), info.data] st env env' hf2
                  ⟨⟨_, h1, rfl⟩, h2, trivial⟩ hma
            · exact matchPat_multi ht hk hmu hm
      | _ => rw [hk] at hf; simp at hf
  | .var .., _, _, _, hf, _ => by simp [rootNEFCO] at hf
  | .constBool .., _, _, _, hf, _ => by simp [rootNEFCO] at hf
  | .constInt .., _, _, _, hf, _ => by simp [rootNEFCO] at hf
  | .constPrim .., _, _, _, hf, _ => by simp [rootNEFCO] at hf
  | .wildcard .., _, _, _, hf, _ => by simp [rootNEFCO] at hf

theorem rootNEFCLOAny_sound : ∀ (qs : List Pattern) (st : LState) (env env' : Interp.Env V),
    rootNEFCOAny program sel qs = true →
    matchAll program (sem ctx) st qs (.inst ii) env = .ok (some env') → False
  | [], _, _, _, hf, _ => by simp [rootNEFCOAny] at hf
  | q :: qs, st, env, env', hf, hm => by
    rw [rootNEFCOAny.eq_2, Bool.or_eq_true] at hf
    obtain ⟨e1, h1, h2⟩ := matchAll_cons_inv_ex hm
    rcases hf with hf | hf
    · exact rootNEFCLO_sound q st env e1 hf h1
    · exact rootNEFCLOAny_sound qs st e1 env' hf h2
end

end

/-- **The integer roots never match the non-E instructions of a context over the scope `S`**
other than through the float families, the `fcopysign` roots and the `fma` roots
(`NonEUnmatchableTFS` for the closure roots outside `copysignRootRule` and `fmaRootRule`, #35). -/
def NonEUnmatchableTFSO (S : InstScope) (p : Program) : Prop :=
  ∀ r ∈ p.rulesOf TId.lower, closureRoot r = true → floatMoveRootRule r = false →
    floatMemRootRule r = false → floatArithRootRule r = false → floatCvtRootRule r = false →
    floatCmpRootRule r = false → copysignRootRule r = false → fmaRootRule r = false →
  ∀ (f : Clif.Function) (ctx : Ctx), CtxTS S f ctx →
  ∀ (ii : Nat) (info : IInfo) (inst : Clif.Inst), ctx.insts[ii]? = some info →
    info.clif = some inst → Compile.instE inst = false → (r.id = 971 → ¬ FloatSelect inst) →
    StoreTyped ctx inst →
  ∀ (cfg : Config) (m : Nat) (st : LState) (tr : Array RuleId) (env' : Interp.Env V)
    (s1 : LState × Array RuleId),
    (∀ pre post, p.rulesOf TId.lower = pre ++ r :: post → ∀ r' ∈ pre, ∃ m', 1000 ≤ m' ∧
      ∃ s', (matchRule p (sem ctx) cfg m' r' [.inst ii]).run (st, tr) = .ok (none, s')) →
    (matchRule p (sem ctx) cfg m r [.inst ii]).run (st, tr) ≠ .ok (some env', s1)

/-- **An integer `store` root never matches a non-E instruction of a context over a scope inside
`InstScopeTFLO`** whose float stores store float values (`intStore_nonES` over
`InstScopeTFLO`). -/
theorem intStore_nonESO {S : InstScope} (hS : ∀ ctx, S.P ctx → InstScopeTFLO ctx) {r : Rule}
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
        simp [Compile.instETFLO, Compile.fCopysignET, Compile.fFmaET, Compile.instETFL,
          Compile.f64ConstET, Compile.instETF, Compile.instETA,
          Compile.fArithET, Compile.fCvtET, Compile.fCmpET,
          Compile.instET, Compile.instE, Compile.tyE, Clif.Ty.isFloat]
    have := hst _ _ _ _ _ _ rfl hf _ hvt
    simp [fTys] at this

/-- **The integer roots never match the non-E instructions of a context over a scope inside
`InstScopeTFLO`** outside the float, `fcopysign` and `fma` families (`nonEUnmatchableTFS_program`
over `InstScopeTFLO`: `nonE_splitFLO`, `rootNEFCLO_sound`). -/
theorem nonEUnmatchableTFSO_program {S : InstScope} (hS : ∀ ctx, S.P ctx → InstScopeTFLO ctx) :
    NonEUnmatchableTFSO S program := by
  intro r hr hroot hfm hmm hfa hfc hfcmp hcs hfma f ctx hctx ii info inst hi hc hE hsel hst cfg m
    st tr env' s1 _ hmatch
  have hok := List.all_eq_true.mp nonEOkFCO_program r hr
  rw [closureRoot_eq] at hroot
  simp only [nonEOkFCO, hroot, hfm, hmm, hfa, hfc, hfcmp, hcs, hfma, Bool.not_true,
    Bool.false_or] at hok
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
        have hsp := nonE_splitFLO hctx.inv hi hc hd (hsc ii info inst hi hc) hE
          (sel := r.id == 971) (fun h => hsel (beq_iff_eq.mp h))
        exact rootNEFCLO_sound hctx.inv hsc hsp hi q _ _ _ hok h1
      · cases hok
  · exact intStore_nonESO hS hr his hctx hi hc hE hst hmatch

end Backend.Proof
