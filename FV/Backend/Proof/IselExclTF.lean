import FV.Backend.Proof.IselExclT
import FV.Backend.Proof.InstScopeTF

/-!
# Excluded root rules with the proven float operations (S11f, #35)

`IselExclT`'s typed exclusion checker over the instructions of `Compile.instETF`: the typed
movement scope, the S11f float arithmetic and rounding (`floatOpsA`) and the conversions of
S11f-cvt. A conversion to an integer (`fcvt_to_{u,s}int_sat` at `i32`/`i64`) has an integer
result and an opcode of `cvtIOps`; a conversion from an integer (`fcvt_from_{u,s}int` at
`f32`/`f64`) a float result and an opcode of `cvtFOps`.

* `exclOkTF_program`: every root rule of `lower` is a closure root or passes
  `failsTG p opsTF floatOpsF` (one kernel decision over the exported rule list);
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

/-- The integer-result opcodes with the conversions. -/
def opsTF : List Nat := opsT ++ cvtIOps

/-- The float-result opcodes with the float arithmetic and the conversions. -/
def floatOpsF : List Nat := floatOpsA ++ cvtFOps

section
variable (p : Program)

/-- A root rule of `lower` is in the closure or cannot match an instruction of a float-capable
context whose instructions are in `Compile.instETF` (`InstScopeTF`). -/
def exclOkTF (r : Rule) : Bool :=
  closureRootIds.contains r.id ||
    match r.args with
    | [q] => failsTG p opsTF floatOpsF .inst q
    | _ => false

end

set_option maxRecDepth 100000 in
/-- Every root rule of `lower` is a closure root or cannot match an instruction of a
float-capable context with the proven float operations (checked). -/
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

/-- The result type of a non-`fcmp` float operation is its controlling type. -/
theorem float_resTy {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx) {j : Nat}
    {info : IInfo} {op : Clif.FOp} {ty : Clif.Ty} {args : List Nat}
    (hop : ∀ cc, op ≠ .fcmp cc) (hi : ctx.insts[j]? = some info)
    (hc : info.clif = some (.float op ty args)) :
    info.resTys.head?.getD .invalid = CTy.ofClif ty := by
  obtain ⟨tys, htys, hres, -⟩ := hctx.resTys j info _ hi hc
  have : tys = [ty] := by
    cases op
    case fcmp cc => exact absurd rfl (hop cc)
    all_goals simpa [Clif.Inst.resultTypes] using htys.symm
  subst this
  rw [hres]
  rfl

/-- **One instruction of a context with the proven float operations** (the callees of the
context's `call`s with integer signatures): an integer (or no) result with an opcode of
`opsTF`, or a float result with an opcode of `floatOpsF`. -/
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
  rcases hT with (hT | hA) | hV
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

/-- **An instruction of a context with the proven float operations**: `InstSplit` at
`opsTF`/`floatOpsF`. -/
theorem inst_splitF_calls {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx)
    (hsc : InstScopeTF ctx) (hx : CallsE f ctx) :
    InstSplit Compile.instETF f ctx opsTF floatOpsF :=
  fun hi hc hd => inst_splitF1_calls hctx hx (hsc _ _ _ hi hc) hi hc hd

/-- **The root rules of `lower` outside the closure never match an instruction of a
float-capable context with the proven float operations** (instructions in `InstScopeTF`, the
callees of its `call`s with integer signatures). -/
theorem lower_nonroot_nomatchTF_calls {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx)
    (hsc : InstScopeTF ctx) (hx : CallsE f ctx) {ii : Nat}
    {info : IInfo} {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
    {r : Rule} (hr : r ∈ program.rulesOf TId.lower) (hroot : closureRootIds.contains r.id = false) :
    ∀ cfg m s0 env s1, (matchRule program (sem ctx) cfg m r [.inst ii]).run s0 ≠ .ok (some env, s1) := by
  intro cfg m s0 env' s1 hmatch
  have hok := List.all_eq_true.mp exclOkTF_program r hr
  simp only [exclOkTF, hroot, Bool.false_or] at hok
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

end Backend.Proof
