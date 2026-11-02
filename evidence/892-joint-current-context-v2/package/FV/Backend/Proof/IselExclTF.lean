import FV.Backend.Proof.IselExclT
import FV.Backend.Proof.InstScopeTF
import FV.Backend.Proof.IselFloatCmpEmit
import FV.Backend.Proof.IselCtlTry

/-!
# Excluded root rules with the proven float operations (S11f, #35)

`IselExclT`'s typed exclusion checker over the instructions of `Compile.instETF`: the typed
movement scope, the S11f float arithmetic and rounding (`floatOpsA`), the conversions of
S11f-cvt and the scalar comparisons. A conversion to an integer (`fcvt_to_{u,s}int_sat` at
`i32`/`i64`) has an integer result and an opcode of `cvtIOps`; a conversion from an integer
(`fcvt_from_{u,s}int` at `f32`/`f64`) a float result and an opcode of `cvtFOps`; an `fcmp` an `i8`
result and the opcode of `cmpOps`.

* `exclOkTF_program`: every root rule of `lower` is a closure root, the vector `fcmp` root
  `rule_lower_2179` (id 952), or passes `failsTG p opsTF floatOpsF` (one kernel decision over
  the exported rule list);
* `rule_lower_2179_nomatchT`: the vector `fcmp` root matches nothing in a float-capable context
  (its operand's type is scalar, `CtxInvT.valTyM`, so `ty_vector_float` fails);
* `inst_splitF1_calls`, `inst_splitF_calls`: the instructions of a context in `InstScopeTF` split
  as `InstSplit Compile.instETF f ctx opsTF floatOpsF`;
* `lower_nonroot_nomatchTF_calls`: a root rule outside the closure matches no instruction of a
  float-capable context whose instructions are in `InstScopeTF`.

`lower_nonroot_nomatchT`/`lower_nonroot_nomatchTA` and their checkers are unchanged.
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

/-- The opcodes of the conversions to an integer (integer results). -/
def cvtIOps : List Nat := [VIdx.Opcode.FcvtToUintSat, VIdx.Opcode.FcvtToSintSat]

/-- The opcodes of the conversions from an integer (float results). -/
def cvtFOps : List Nat := [VIdx.Opcode.FcvtFromUint, VIdx.Opcode.FcvtFromSint]

/-- The opcode of the scalar comparisons (`fcmp`: an `i8` result). -/
def cmpOps : List Nat := [VIdx.Opcode.Fcmp]

/-- The integer-result opcodes with the conversions and the comparisons. -/
def opsTF : List Nat := opsT ++ (cvtIOps ++ cmpOps)

/-- The float-result opcodes with the float arithmetic and the conversions. -/
def floatOpsF : List Nat := floatOpsA ++ cvtFOps

section
variable (p : Program)

/-- A root rule of `lower` is in the closure, is the vector `fcmp` root `rule_lower_2179` (id
952: its `ty_vector_float` condition fails, `rule_lower_2179_nomatchT`), or cannot match an
instruction of a float-capable context whose instructions are in `Compile.instETF`
(`InstScopeTF`). -/
def exclOkTF (r : Rule) : Bool :=
  closureRootIds.contains r.id || r.id == 952 ||
    match r.args with
    | [q] => failsTG p opsTF floatOpsF .inst q
    | _ => false

end

set_option maxRecDepth 100000 in
/-- Every root rule of `lower` is a closure root, `rule_lower_2179`, or cannot match an
instruction of a float-capable context with the proven float operations (checked). -/
theorem exclOkTF_program : (program.rulesOf TId.lower).all (exclOkTF program) = true := by
  rw [show TId.lower = 686 from rfl, data_program.r686]
  decide +kernel

/-! ## The conversions -/

set_option maxRecDepth 20000 in
theorem cvtINames_idx : [("Unary", "FcvtToUintSat"), ("Unary", "FcvtToSintSat")].all (fun pr =>
    match variantIdx 152 pr.1, variantIdx 151 pr.2 with
    | some _, some ko => opsTF.contains ko
    | _, _ => false) = true := by
  decide +kernel

set_option maxRecDepth 20000 in
theorem cvtFNames_idx : [("Unary", "FcvtFromUint"), ("Unary", "FcvtFromSint")].all (fun pr =>
    match variantIdx 152 pr.1, variantIdx 151 pr.2 with
    | some _, some ko => floatOpsF.contains ko
    | _, _ => false) = true := by
  decide +kernel

/-- **An admitted conversion**: `fcvt_from_*` at a float type, or `fcvt_to_*_sat` at `i32`/`i64`,
with one operand. -/
theorem fCvtET_cases {c : Clif.Inst} (h : Compile.fCvtET c = true) :
    ∃ op ty x, c = .float op ty [x] ∧
      (((op = .fcvtFromUint ∨ op = .fcvtFromSint) ∧ ty.isFloat = true) ∨
       ((op = .fcvtToUintSat ∨ op = .fcvtToSintSat) ∧ (ty = .i32 ∨ ty = .i64))) := by
  cases c with
  | float op ty args =>
    cases args with
    | nil => simp [Compile.fCvtET] at h
    | cons x rest =>
      cases rest with
      | cons => simp [Compile.fCvtET] at h
      | nil =>
        refine ⟨op, ty, x, rfl, ?_⟩
        simp only [Compile.fCvtET, Bool.and_eq_true] at h
        cases op <;> simp_all [fCvtOpcode, fCvtTyOk]
  | _ => simp [Compile.fCvtET] at h

set_option maxRecDepth 20000 in
/-- The data of a conversion to an integer: an integer-result opcode (`opsTF`). -/
theorem instData_cvtTo {f : Clif.Function} {op : Clif.FOp} {ty : Clif.Ty} {x : Nat} {d : V}
    (hop : op = .fcvtToUintSat ∨ op = .fcvtToSintSat) (h : instData f (.float op ty [x]) = .ok d) :
    ∃ kf ko fs, d = .data 152 kf (.data 151 ko [] :: fs) ∧ ko ∈ opsTF := by
  rcases instData_names h with ⟨rest, hd⟩ | ⟨ty', imm, he, -⟩
  · refine data_of_names hd ?_ cvtINames_idx
    rcases hop with rfl | rfl <;> simp [instNames, fFmt, fOpc]
  · cases he

set_option maxRecDepth 20000 in
/-- The data of a conversion from an integer: a float-result opcode (`floatOpsF`). -/
theorem instData_cvtFrom {f : Clif.Function} {op : Clif.FOp} {ty : Clif.Ty} {x : Nat} {d : V}
    (hop : op = .fcvtFromUint ∨ op = .fcvtFromSint) (h : instData f (.float op ty [x]) = .ok d) :
    ∃ kf ko fs, d = .data 152 kf (.data 151 ko [] :: fs) ∧ ko ∈ floatOpsF := by
  rcases instData_names h with ⟨rest, hd⟩ | ⟨ty', imm, he, -⟩
  · refine data_of_names hd ?_ cvtFNames_idx
    rcases hop with rfl | rfl <;> simp [instNames, fFmt, fOpc]
  · cases he

/-! ## The scalar comparisons -/

set_option maxRecDepth 20000 in
theorem cmpNames_idx : [("FloatCompare", "Fcmp")].all (fun pr =>
    match variantIdx 152 pr.1, variantIdx 151 pr.2 with
    | some _, some ko => opsTF.contains ko
    | _, _ => false) = true := by
  decide +kernel

/-- **An admitted comparison**: `fcmp` of two operands at a float type. -/
theorem fCmpET_cases {c : Clif.Inst} (h : Compile.fCmpET c = true) :
    ∃ cc ty x y, c = .float (.fcmp cc) ty [x, y] ∧ ty.isFloat = true := by
  cases c with
  | float op ty args =>
    cases op with
    | fcmp cc =>
      match args, h with
      | [x, y], h =>
        simp only [Compile.fCmpET, Bool.and_eq_true] at h
        exact ⟨cc, ty, x, y, rfl, h.1⟩
      | [], h => simp [Compile.fCmpET] at h
      | [_], h => simp [Compile.fCmpET] at h
      | _ :: _ :: _ :: _, h => simp [Compile.fCmpET] at h
    | _ => simp [Compile.fCmpET] at h
  | _ => simp [Compile.fCmpET] at h

set_option maxRecDepth 20000 in
/-- The data of a comparison: an integer-result opcode (`opsTF`). -/
theorem instData_cmp {f : Clif.Function} {cc : Clif.FloatCC} {ty : Clif.Ty} {x y : Nat} {d : V}
    (h : instData f (.float (.fcmp cc) ty [x, y]) = .ok d) :
    ∃ kf ko fs, d = .data 152 kf (.data 151 ko [] :: fs) ∧ ko ∈ opsTF := by
  rcases instData_names h with ⟨rest, hd⟩ | ⟨ty', imm, he, -⟩
  · exact data_of_names hd (by simp [instNames, fFmt, fOpc]) cmpNames_idx
  · cases he

/-- The result type of an `fcmp` is `i8`. -/
theorem fcmp_resTy {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx) {j : Nat}
    {info : IInfo} {cc : Clif.FloatCC} {ty : Clif.Ty} {args : List Nat}
    (hi : ctx.insts[j]? = some info) (hc : info.clif = some (.float (.fcmp cc) ty args)) :
    info.resTys.head?.getD .invalid = .int 8 := by
  obtain ⟨tys, htys, hres, -⟩ := hctx.resTys j info _ hi hc
  have : tys = [.i8] := by simpa [Clif.Inst.resultTypes] using htys.symm
  subst this
  rw [hres]
  rfl

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- **The vector `fcmp` root never matches in a float-capable context** (`rule_lower_2179`,
`lower.isle:2179`, id 952): it matches an `fcmp` whose first operand has the type `in_ty`
(`value_type`), a scalar type of the context (`CtxInvT.valTyM`), so its condition
`ty_vector_float in_ty` fails. -/
theorem rule_lower_2179_nomatchT {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx)
    {ii : Nat} {info : IInfo} {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info)
    (hc : info.clif = some inst) {cfg : Config} {m : Nat} {s : LState × Array RuleId}
    {env' : Interp.Env V} {s1 : LState × Array RuleId} :
    (matchRule program (sem ctx) cfg m rule_lower_2179 [.inst ii]).run s ≠ .ok (some env', s1) := by
  intro hmatch
  have hp := data_program
  have hdat := hctx.data ii info inst hi hc
  cases m with
  | zero => rw [matchRule.eq_1] at hmatch; cases hmatch
  | succ m =>
  isel_inv' hp [] at hmatch
  rename_i w5 w4 w3 w2 w1 h1 h2 hil _ _ _ _ _ info' hi' hd
  rw [hi, Option.some.injEq] at hi'
  subst hi'
  rw [← hd] at hdat
  obtain ⟨cc, ty, x, y, rfl, -, -, hd2⟩ := instData_fcmp_inv hdat
  simp only [List.cons.injEq, and_true] at hd2
  obtain ⟨rfl, rfl⟩ := hd2
  rw [ext_value_array_2_iff] at h1
  simp only [List.cons.injEq, and_true] at h1
  obtain ⟨rfl, rfl⟩ := h1
  obtain ⟨t, hvt, ht⟩ := (ext_value_type_iff _ _ _ _).mp h2
  simp only [List.cons.injEq, and_true] at ht
  subst ht
  have hm := hctx.valTyM x t hvt
  cases m with
  | zero => rw [matchIfLets.eq_1] at hil; cases hil
  | succ m =>
  rw [matchIfLets_cons_iff] at hil
  obtain ⟨v, s2, he, -⟩ := hil
  have ht130 : Interp.termOf program 130 = pure T.«ty_vector_float» := rfl
  cases m with
  | zero => rw [evalExpr.eq_1] at he; cases he
  | succ m =>
  isel_inv_all [ht130] at he
  rename_i as s3 hargs happ
  cases m with
  | zero => rw [evalArgs.eq_def] at hargs; simp_all
  | succ m =>
  isel_inv_all [ht130] at hargs happ
  rename_i a0 s4 hv as' hnil
  rw [show termOf program 130 = .ok T.«ty_vector_float» from rfl] at happ
  obtain ⟨-, st', hct, -⟩ := happ
  cases m with
  | zero => rw [evalExpr.eq_1] at hv; cases hv
  | succ m =>
  isel_inv_all [] at hv hnil
  simp only [mCTys, eCTys, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with (rfl | rfl | rfl | rfl) | (rfl | rfl) <;> cases hct

set_option maxRecDepth 100000 in
/-- The root rule of `lower` with id 952 is `rule_lower_2179`. -/
theorem lower_rule952_filter : (program.rulesOf TId.lower).filter (·.id == 952) =
    [rule_lower_2179] := by
  rw [program_rulesOf_686]
  rfl

/-- **One instruction of a context with the proven float operations** (the callees of the
context's `call`s with integer signatures): an integer (or no) result with an opcode of
`opsTF` (an `fcmp`'s `i8` among them), or a float result with an opcode of `floatOpsF`. -/
theorem inst_splitF1_calls {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx)
    (hx : CallsE f ctx) {j : Nat} {info : IInfo} {c : Clif.Inst}
    (hTF : Compile.instETF c = true) (hi : ctx.insts[j]? = some info) (hc : info.clif = some c)
    (hd : instData f c = .ok info.data) :
    (info.resTys.head?.getD .invalid ∈ (.invalid :: eCTys) ∧
        (AVT.data opsTF).HoldsS Compile.instETF f ctx info.data) ∨
      (info.resTys.head?.getD .invalid ∈ fTys ∧
        (AVT.data floatOpsF).HoldsS Compile.instETF f ctx info.data) := by
  have hT := hTF
  simp only [Compile.instETF, Compile.instETA, Bool.or_eq_true] at hT
  rcases hT with ((hT | hA) | hV) | hC
  · rcases inst_split1_calls hctx hx hT hi hc hd with ⟨h1, c', hT', hc', kf, ko, fs, he, hko⟩ |
      ⟨h1, c', hT', hc', kf, ko, fs, he, hko⟩
    · exact .inl ⟨h1, c', Compile.instETF_of_instET hT', hc', kf, ko, fs, he,
        List.mem_append_left _ hko⟩
    · exact .inr ⟨h1, c', Compile.instETF_of_instET hT', hc', kf, ko, fs, he,
        List.mem_append_left _ (List.mem_append_left _ hko)⟩
  · obtain ⟨kf, ko, fs, he, hko⟩ := instData_shapeA hA hd
    exact .inr ⟨fArith_resTy hctx hA hi hc, c, hTF, hd, kf, ko, fs, he,
      List.mem_append_left _ hko⟩
  · obtain ⟨op, ty, x, rfl, (⟨hop, hty⟩ | ⟨hop, hty⟩)⟩ := fCvtET_cases hV
    · obtain ⟨kf, ko, fs, he, hko⟩ := instData_cvtFrom hop hd
      refine .inr ⟨?_, _, hTF, hd, kf, ko, fs, he, hko⟩
      rw [float_resTy hctx (fun cc e => by rcases hop with rfl | rfl <;> cases e) hi hc]
      revert hty; cases ty <;> simp [fTys, CTy.ofClif, Clif.Ty.isFloat]
    · obtain ⟨kf, ko, fs, he, hko⟩ := instData_cvtTo hop hd
      refine .inl ⟨?_, _, hTF, hd, kf, ko, fs, he, hko⟩
      rw [float_resTy hctx (fun cc e => by rcases hop with rfl | rfl <;> cases e) hi hc]
      rcases hty with rfl | rfl <;> simp [eCTys, CTy.ofClif]
  · obtain ⟨cc, ty, x, y, rfl, -⟩ := fCmpET_cases hC
    obtain ⟨kf, ko, fs, he, hko⟩ := instData_cmp hd
    refine .inl ⟨?_, _, hTF, hd, kf, ko, fs, he, hko⟩
    rw [fcmp_resTy hctx hi hc]
    simp [eCTys]

/-- **An instruction of a context with the proven float operations**: `InstSplit` at
`opsTF`/`floatOpsF`. -/
theorem inst_splitF_calls {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx)
    (hsc : InstScopeTF ctx) (hx : CallsE f ctx) :
    InstSplit Compile.instETF f ctx opsTF floatOpsF :=
  fun hi hc hd => inst_splitF1_calls hctx hx (hsc _ _ _ hi hc) hi hc hd

/-- **The root rules of `lower` outside the closure never match an instruction of a
float-capable context with the proven float operations** (instructions in `InstScopeTF`, the
callees of its `call`s with integer signatures): `rule_lower_2179` by
`rule_lower_2179_nomatchT`, the others by the checker. -/
theorem lower_nonroot_nomatchTF_calls {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx)
    (hsc : InstScopeTF ctx) (hx : CallsE f ctx) {ii : Nat}
    {info : IInfo} {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
    {r : Rule} (hr : r ∈ program.rulesOf TId.lower) (hroot : closureRootIds.contains r.id = false) :
    ∀ cfg m s0 env s1, (matchRule program (sem ctx) cfg m r [.inst ii]).run s0 ≠ .ok (some env, s1) := by
  intro cfg m s0 env' s1 hmatch
  have hok := List.all_eq_true.mp exclOkTF_program r hr
  simp only [exclOkTF, hroot, Bool.false_or] at hok
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
        exact failsTG_sound hctx (inst_splitF_calls hctx hsc hx) q .inst _ _ _ _ hok
          ⟨ii, info, inst, rfl, hi, hc, hctx.data ii info inst hi hc⟩ h1
      · cases hok
  · have hsub : r ∈ (program.rulesOf TId.lower).filter (·.id == 952) :=
      List.mem_filter.2 ⟨hr, h952⟩
    rw [lower_rule952_filter, List.mem_singleton] at hsub
    subst hsub
    exact rule_lower_2179_nomatchT hctx hi hc hmatch

end Backend.Proof
