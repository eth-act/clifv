import FV.Backend.Proof.IselMemRoots
import FV.Backend.Proof.LowerContractT

/-!
# The integer roots never match a non-E instruction of a typed context (S11e5 Stage C, slice 7)

The typed movement scope (`Compile.instET`) adds to subset E the float constants, `load`/`store`
of a float, `select` of floats and `bitcast`. On such an instruction (`instE = false`) the first
matching closure root of `lower` must be a float root (or the float arm of `select`, 971): the
integer roots never match it. A root pattern is `(inst_data_value ty data)` (possibly under an
`and`); the checker `rootNE` evaluates it against the result type and data of a non-E instruction
(`nonE_split`: an integer or no result with opcode `store`/`bitcast`, or a float result with a
float-movement opcode, `select` excluded at the `select` root) with `failsArgsTG` for the fields
(whose look-through instructions are any of the typed scope's, `inst_split`).

The integer `store` roots (`rule_lower_2705`/`2709`/`2713`/`2717`) dispatch on the stored value's
`value_type`, not on the store's type: on a float `store` they are excluded by the CLIF
verifier's store typing (`StoreTyped`, `LowerContractT.lean`: the stored value of a float
store has a float type; decided per function by `Compile.storeTypedB`).
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-- Opcodes of the non-E typed-scope instructions with an integer or no result. -/
def neIOps : List Nat := [VIdx.Opcode.Store, VIdx.Opcode.Bitcast]

/-- Opcodes of the non-E typed-scope instructions with a float result (`select` only when
`sel = false`). -/
def neFOps (sel : Bool) : List Nat :=
  [VIdx.Opcode.F32const, VIdx.Opcode.F64const, VIdx.Opcode.Load, VIdx.Opcode.Bitcast] ++
    (if sel then [] else [VIdx.Opcode.Select])

section
variable (p : Program)

mutual
/-- **Root checker**: the root pattern `q` matches no non-E instruction of a typed context. -/
def rootNE (sel : Bool) : Pattern → Bool
  | .bind _ _ q => rootNE sel q
  | .and _ qs => rootNEAny sel qs
  | .term _ t args =>
    match termOf p t with
    | .error _ => true
    | .ok term =>
      match term.kind with
      | .decl flags _ (some (.external _ _)) =>
        if flags.isMulti then true else
        term.id == TId.inst_data_value &&
          failsArgsTG p opsT floatOps [.tys (.invalid :: eCTys), .data neIOps] args &&
          failsArgsTG p opsT floatOps [.tys fTys, .data (neFOps sel)] args
      | _ => false
  | _ => false

/-- Some conjunct is refuted. -/
def rootNEAny (sel : Bool) : List Pattern → Bool
  | [] => false
  | q :: qs => rootNE sel q || rootNEAny sel qs
end

/-- The integer `store` roots (`value_type`-dispatched; `StoreTyped`). -/
def intStoreRoot (r : Rule) : Bool := r.id == 1064 || r.id == 1065 || r.id == 1066 || r.id == 1067

/-- A closure root of `lower` that is not a float root nor an integer `store` root is refuted
on the non-E instructions. -/
def nonEOk (r : Rule) : Bool :=
  !closureRootIds.contains r.id || floatMoveRootRule r || floatMemRootRule r ||
    floatArithRootRule r || intStoreRoot r ||
    match r.args with
    | [q] => rootNE p (r.id == 971) q
    | _ => false

end

set_option maxRecDepth 100000 in
/-- Checked over the exported rule list. -/
theorem nonEOk_program : (program.rulesOf TId.lower).all (nonEOk program) = true := by
  rw [show TId.lower = 686 from rfl, data_program.r686]
  decide +kernel

/-! ## The non-E instructions -/

set_option maxRecDepth 20000 in
theorem neNames_load (sel : Bool) : [("Load", "Load")].all (fun pr =>
    match variantIdx 152 pr.1, variantIdx 151 pr.2 with
    | some _, some ko => (neFOps sel).contains ko
    | _, _ => false) = true := by
  cases sel <;> decide +kernel

set_option maxRecDepth 20000 in
theorem neNames_bitcastF (sel : Bool) : [("LoadNoOffset", "Bitcast")].all (fun pr =>
    match variantIdx 152 pr.1, variantIdx 151 pr.2 with
    | some _, some ko => (neFOps sel).contains ko
    | _, _ => false) = true := by
  cases sel <;> decide +kernel

set_option maxRecDepth 20000 in
theorem neNames_select : [("Ternary", "Select")].all (fun pr =>
    match variantIdx 152 pr.1, variantIdx 151 pr.2 with
    | some _, some ko => (neFOps false).contains ko
    | _, _ => false) = true := by
  decide +kernel

set_option maxRecDepth 20000 in
theorem neNames_int : [("Store", "Store"), ("LoadNoOffset", "Bitcast")].all (fun pr =>
    match variantIdx 152 pr.1, variantIdx 151 pr.2 with
    | some _, some ko => neIOps.contains ko
    | _, _ => false) = true := by
  decide +kernel

/-- **A non-E instruction of the typed scope**: an integer or no result with opcode `store`/
`bitcast`, or a float result with a float-movement opcode (not `select` when `sel`). -/
theorem nonE_split {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx) {j : Nat} {info : IInfo}
    {c : Clif.Inst} (hi : ctx.insts[j]? = some info) (hc : info.clif = some c)
    (hd : instData f c = .ok info.data) (hT : Compile.instET c = true)
    (hE : Compile.instE c = false) {sel : Bool} (hsel : sel = true → ¬ FloatSelect c) :
    (info.resTys.head?.getD .invalid ∈ (.invalid :: eCTys) ∧
        (AVT.data neIOps).HoldsS Compile.instET f ctx info.data) ∨
      (info.resTys.head?.getD .invalid ∈ fTys ∧
        (AVT.data (neFOps sel)).HoldsS Compile.instET f ctx info.data) := by
  obtain ⟨tys, hty, hres, -⟩ := hctx.resTys j info c hi hc
  rw [hres]
  have hnm := instData_names hd
  cases c
  case iconst ty imm =>
    have hf : ty.isFloat = true := by
      revert hT hE; cases ty <;> simp [Compile.instET, Compile.instE, Compile.tyE, Clif.Ty.isFloat]
    simp only [Clif.Inst.resultTypes, Option.some.injEq] at hty
    subst hty
    right
    refine ⟨by cases ty <;> simp_all [fTys, CTy.ofClif, Clif.Ty.isFloat], .iconst ty imm, hT, hd, ?_⟩
    obtain ⟨rest, h | h⟩ := instData_iconst_float hf hd
    · exact ⟨_, _, _, h, by cases sel <;> decide⟩
    · exact ⟨_, _, _, h, by cases sel <;> decide⟩
  case load op ty fl q off =>
    have hf : ty.isFloat = true ∧ op = .load := by
      revert hT hE; cases ty <;> cases op <;>
        simp [Compile.instET, Compile.instE, Compile.tyE, Clif.Ty.isFloat]
    obtain ⟨hf, rfl⟩ := hf
    simp only [Clif.Inst.resultTypes, Option.some.injEq] at hty
    subst hty
    right
    refine ⟨by cases ty <;> simp_all [fTys, CTy.ofClif, Clif.Ty.isFloat], _, hT, hd, ?_⟩
    rcases hnm with ⟨rest, h⟩ | ⟨_, _, h, -⟩
    · exact data_of_names h (by simp [instNames, loadOpcode]) (neNames_load sel)
    · cases h
  case store op ty fl x q off =>
    have hop : op = .store := by
      revert hT hE; cases ty <;> cases op <;>
        simp [Compile.instET, Compile.instE, Compile.tyE, Clif.Ty.isFloat]
    subst hop
    simp only [Clif.Inst.resultTypes, Option.some.injEq] at hty
    subst hty
    left
    refine ⟨by simp, _, hT, hd, ?_⟩
    rcases hnm with ⟨rest, h⟩ | ⟨_, _, h, -⟩
    · exact data_of_names h (by simp [instNames, storeOpcode]) neNames_int
    · cases h
  case select ty cnd x y =>
    have hf : ty.isFloat = true := by
      revert hT hE; cases ty <;> simp [Compile.instET, Compile.instE, Compile.tyE, Compile.tyM,
        Clif.Ty.isFloat]
    cases sel
    · simp only [Clif.Inst.resultTypes, Option.some.injEq] at hty
      subst hty
      right
      refine ⟨by cases ty <;> simp_all [fTys, CTy.ofClif, Clif.Ty.isFloat], _, hT, hd, ?_⟩
      rcases hnm with ⟨rest, h⟩ | ⟨_, _, h, -⟩
      · exact data_of_names h (by simp [instNames]) neNames_select
      · cases h
    · exact absurd ⟨ty, cnd, x, y, rfl, hf⟩ (hsel rfl)
  case bitcast ty fl x =>
    simp only [Clif.Inst.resultTypes, Option.some.injEq] at hty
    subst hty
    have hdata := fun (L : List (String × String)) (hm : instNames (.bitcast ty fl x) ∈ L) ops hL =>
      match hnm with
      | .inl ⟨rest, h⟩ => data_of_names (ops := ops) h hm hL
      | .inr ⟨_, _, h, _⟩ => by cases h
    cases hfl : ty.isFloat
    · left
      refine ⟨?_, _, hT, hd, hdata [("Store", "Store"), ("LoadNoOffset", "Bitcast")]
        (by simp [instNames]) neIOps neNames_int⟩
      revert hT hfl
      cases ty <;> simp [Compile.instET, Compile.tyM, Compile.tyE, Clif.Ty.isFloat, CTy.ofClif, eCTys]
    · right
      refine ⟨by cases ty <;> simp_all [fTys, CTy.ofClif, Clif.Ty.isFloat], _, hT, hd,
        hdata [("LoadNoOffset", "Bitcast")] (by simp [instNames]) (neFOps sel) (neNames_bitcastF sel)⟩
  all_goals exact absurd hT (by simp_all [Compile.instET])

/-! ## Soundness -/

section
variable {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx) (hsc : InstScopeT ctx)
  (hx : CallsE f ctx) {ii : Nat} {info : IInfo} {sel : Bool}
  (hsp : (info.resTys.head?.getD .invalid ∈ (.invalid :: eCTys) ∧
        (AVT.data neIOps).HoldsS Compile.instET f ctx info.data) ∨
      (info.resTys.head?.getD .invalid ∈ fTys ∧
        (AVT.data (neFOps sel)).HoldsS Compile.instET f ctx info.data))
  (hi : ctx.insts[ii]? = some info)
include hctx hsc hx hsp hi

mutual
theorem rootNE_sound : ∀ (q : Pattern) (st : LState) (env env' : Interp.Env V),
    rootNE program sel q = true →
    matchPat program (sem ctx) st q (.inst ii) env = .ok (some env') → False
  | .bind ty x q, st, env, env', hf, hm => by
    rw [rootNE.eq_1] at hf
    exact rootNE_sound q st _ env' hf (matchPat_bind_inv hm).2
  | .and ty qs, st, env, env', hf, hm => by
    rw [rootNE.eq_2] at hf
    rw [matchPat.eq_7] at hm
    exact rootNEAny_sound qs st env env' hf hm
  | .term ty t args, st, env, env', hf, hm => by
    rw [rootNE.eq_3] at hf
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
              · exact failsArgsT_sound_calls hctx hsc hx args _ [.ty (info.resTys.head?.getD .invalid),
                  info.data] st env env' hf1 ⟨⟨_, h1, rfl⟩, h2, trivial⟩ hma
              · exact failsArgsT_sound_calls hctx hsc hx args _ [.ty (info.resTys.head?.getD .invalid),
                  info.data] st env env' hf2 ⟨⟨_, h1, rfl⟩, h2, trivial⟩ hma
            · exact matchPat_multi ht hk hmu hm
      | _ => rw [hk] at hf; simp at hf
  | .var .., _, _, _, hf, _ => by simp [rootNE] at hf
  | .constBool .., _, _, _, hf, _ => by simp [rootNE] at hf
  | .constInt .., _, _, _, hf, _ => by simp [rootNE] at hf
  | .constPrim .., _, _, _, hf, _ => by simp [rootNE] at hf
  | .wildcard .., _, _, _, hf, _ => by simp [rootNE] at hf

theorem rootNEAny_sound : ∀ (qs : List Pattern) (st : LState) (env env' : Interp.Env V),
    rootNEAny program sel qs = true →
    matchAll program (sem ctx) st qs (.inst ii) env = .ok (some env') → False
  | [], _, _, _, hf, _ => by simp [rootNEAny] at hf
  | q :: qs, st, env, env', hf, hm => by
    rw [rootNEAny.eq_2, Bool.or_eq_true] at hf
    obtain ⟨e1, h1, h2⟩ := matchAll_cons_inv_ex hm
    rcases hf with hf | hf
    · exact rootNE_sound q st env e1 hf h1
    · exact rootNEAny_sound qs st e1 env' hf h2
end

end


/-! ## The integer `store` roots -/

/-- The integer `store` roots of `lower`, in order. -/
theorem lower_intStoreRoot_filter : (program.rulesOf TId.lower).filter intStoreRoot =
    [rule_lower_2705, rule_lower_2709, rule_lower_2713, rule_lower_2717] := by
  rw [program_rulesOf_686]
  rfl

/-- **An integer `store` root never matches a non-E instruction of a typed context** whose float
stores store float values (`StoreTyped`): it matches a `store` whose stored value has an integer
type, and a non-E `store` is a float store. -/
theorem intStore_nonE {r : Rule} (hr : r ∈ program.rulesOf TId.lower) (hs : intStoreRoot r = true)
    {f : Clif.Function} {ctx : Ctx} (hctx : CtxT f ctx) {ii : Nat} {info : IInfo}
    {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
    (hE : Compile.instE inst = false) (hst : StoreTyped ctx inst) {cfg : Config} {m : Nat}
    {st : LState} {tr : Array RuleId} {env' : Interp.Env V} {s1 : LState × Array RuleId}
    (hmatch : (matchRule program (sem ctx) cfg m r [.inst ii]).run (st, tr) = .ok (some env', s1)) :
    False := by
  have hsub : r ∈ (program.rulesOf TId.lower).filter intStoreRoot := List.mem_filter.2 ⟨hr, hs⟩
  rw [lower_intStoreRoot_filter] at hsub
  have hT := hctx.scope ii info inst hi hc
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
        simp [Compile.instETF, Compile.instETA, Compile.fArithET, Compile.fCvtET, Compile.fCmpET,
          Compile.instET, Compile.instE, Compile.tyE, Clif.Ty.isFloat]
    have := hst _ _ _ _ _ _ rfl hf _ hvt
    simp [fTys] at this

/-! ## The theorem -/

/-- **The integer roots never match the non-E instructions of a typed context.** -/
theorem nonEUnmatchableT_program : NonEUnmatchableT program := by
  intro r hr hroot hfm hmm hfa f ctx hctx hsc ii info inst hi hc hE hsel hst cfg m st tr env' s1 _
    hmatch
  have hok := List.all_eq_true.mp nonEOk_program r hr
  rw [closureRoot_eq] at hroot
  simp only [nonEOk, hroot, hfm, hmm, hfa, Bool.not_true, Bool.false_or] at hok
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
        have hsp := nonE_split hctx.inv hi hc hd (hsc ii info inst hi hc) hE
          (sel := r.id == 971) (fun h => hsel (beq_iff_eq.mp h))
        exact rootNE_sound hctx.inv hsc hctx.calls hsp hi q _ _ _ hok h1
      · cases hok
  · exact intStore_nonE hr his hctx hi hc hE hst hmatch


end Backend.Proof
