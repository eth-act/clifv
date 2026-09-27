import FV.Backend.Proof.IselCmpInv
import FV.Backend.Proof.IselCmpRun
import FV.Backend.Proof.IselFamily

/-!
# The backend side of inverse evaluation (flags/select/div family)

`iff` forms of the extern helpers (`externExtract`/`externCtor`) the family's rules use, the
embedding's equality (`V.beq` is lawful), and the `isel_inv` tactic: `simp only` with the
generic inverse lemmas (`IselCmpInv`), the data facts and these, at a hypothesis "this
match/evaluation returned `some`". Calls of internal constructors stay as `ApplyInternal`
hypotheses for the callee's contract.
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

section Sem
variable (ctx : Ctx)

theorem sem_eq (a b : V) : (sem ctx).eq a b = (a == b) := rfl

theorem sem_unData_iff (ty : TypeId) (v : V) (k : Nat) (fs : List V) :
    (sem ctx).unData ty v = some (k, fs) ↔ v = .data ty k fs := by
  cases v <;> simp [sem]

end Sem

/-! ## Extern extractors -/

section Extract
variable (ctx : Ctx) (st : LState)

theorem ext_fits_in_16_iff (ty : CTy) (fs : List V) :
    externExtract ctx T.fits_in_16 (.ty ty) st = .ok fs ↔ ty.bits ≤ 16 ∧ fs = [.ty ty] := by
  have : externExtract ctx T.fits_in_16 (.ty ty) st =
    if decide (ty.bits ≤ 16) = true then .ok [.ty ty] else .fail := rfl
  rw [this]; clear this; split <;> simp_all [eq_comm] <;> omega
theorem ext_fits_in_32_iff (ty : CTy) (fs : List V) :
    externExtract ctx T.fits_in_32 (.ty ty) st = .ok fs ↔ ty.bits ≤ 32 ∧ fs = [.ty ty] := by
  have : externExtract ctx T.fits_in_32 (.ty ty) st =
    if decide (ty.bits ≤ 32) = true then .ok [.ty ty] else .fail := rfl
  rw [this]; clear this; split <;> simp_all [eq_comm] <;> omega
theorem ext_fits_in_64_iff (ty : CTy) (fs : List V) :
    externExtract ctx T.fits_in_64 (.ty ty) st = .ok fs ↔ ty.bits ≤ 64 ∧ fs = [.ty ty] := by
  have : externExtract ctx T.fits_in_64 (.ty ty) st =
    if decide (ty.bits ≤ 64) = true then .ok [.ty ty] else .fail := rfl
  rw [this]; clear this; split <;> simp_all [eq_comm] <;> omega
theorem ext_ty_32_or_64_iff (ty : CTy) (fs : List V) :
    externExtract ctx T.ty_32_or_64 (.ty ty) st = .ok fs ↔
      (ty.bits == 32 || ty.bits == 64) = true ∧ fs = [.ty ty] := by
  have : externExtract ctx T.ty_32_or_64 (.ty ty) st =
    if (ty.bits == 32 || ty.bits == 64) = true then .ok [.ty ty] else .fail := rfl
  rw [this]; clear this
  split
  · rename_i h; simp only [h, ExtResult.ok.injEq, true_and]; exact eq_comm
  · rename_i h; simp only [h, reduceCtorEq, false_iff, not_and, Bool.false_eq_true]; intro h'; exact h'.elim
theorem ext_ty_int_iff (ty : CTy) (fs : List V) :
    externExtract ctx T.ty_int (.ty ty) st = .ok fs ↔ ty.isInt = true ∧ fs = [.ty ty] := by
  have : externExtract ctx T.ty_int (.ty ty) st =
    if ty.isInt = true then .ok [.ty ty] else .fail := rfl
  rw [this]; clear this
  split
  · rename_i h; simp only [h, ExtResult.ok.injEq, true_and]; exact eq_comm
  · rename_i h; simp only [h, reduceCtorEq, false_iff, not_and, Bool.false_eq_true]; intro h'; exact h'.elim
theorem ext_ty_scalar_float_iff (ty : CTy) (fs : List V) :
    externExtract ctx T.ty_scalar_float (.ty ty) st = .ok fs ↔ ty.isFloat = true ∧ fs = [.ty ty] := by
  have : externExtract ctx T.ty_scalar_float (.ty ty) st =
    if ty.isFloat = true then .ok [.ty ty] else .fail := rfl
  rw [this]; clear this
  split
  · rename_i h; simp only [h, ExtResult.ok.injEq, true_and]; exact eq_comm
  · rename_i h; simp only [h, reduceCtorEq, false_iff, not_and, Bool.false_eq_true]; intro h'; exact h'.elim
theorem ext_ty_vec128_iff (ty : CTy) (fs : List V) :
    externExtract ctx T.ty_vec128 (.ty ty) st = .ok fs ↔
      (ty.isVector && ty.bits == 128) = true ∧ fs = [.ty ty] := by
  have : externExtract ctx T.ty_vec128 (.ty ty) st =
    if (ty.isVector && ty.bits == 128) = true then .ok [.ty ty] else .fail := rfl
  rw [this]; clear this
  split
  · rename_i h; simp only [h, ExtResult.ok.injEq, true_and]; exact eq_comm
  · rename_i h; simp only [h, reduceCtorEq, false_iff, not_and, Bool.false_eq_true]; intro h'; exact h'.elim

theorem ext_fits_in_32' (ty : CTy) :
    externExtract ctx T.fits_in_32 (.ty ty) st = if decide (ty.bits ≤ 32) = true then .ok [.ty ty] else .fail := rfl
theorem ext_fits_in_16' (ty : CTy) :
    externExtract ctx T.fits_in_16 (.ty ty) st = if decide (ty.bits ≤ 16) = true then .ok [.ty ty] else .fail := rfl
theorem ext_fits_in_64' (ty : CTy) :
    externExtract ctx T.fits_in_64 (.ty ty) st = if decide (ty.bits ≤ 64) = true then .ok [.ty ty] else .fail := rfl
theorem ext_ty_32_or_64' (ty : CTy) :
    externExtract ctx T.ty_32_or_64 (.ty ty) st =
      if (ty.bits == 32 || ty.bits == 64) = true then .ok [.ty ty] else .fail := rfl

theorem ext_def_inst_iff (v : Nat) (fs : List V) :
    externExtract ctx T.def_inst (.value v) st = .ok fs ↔ ∃ i, ctx.defInst? v = some i ∧ fs = [.inst i] := by
  rw [ext_def_inst]
  cases ctx.defInst? v <;> simp [eq_comm]

theorem ext_inst_data_value_iff (i : Nat) (fs : List V) :
    externExtract ctx T.inst_data_value (.inst i) st = .ok fs ↔
      ∃ info, ctx.insts[i]? = some info ∧ fs = [.ty (info.resTys.head?.getD .invalid), info.data] := by
  have : externExtract ctx T.inst_data_value (.inst i) st = match ctx.insts[i]? with
    | some info => .ok [.ty (info.resTys.head?.getD .invalid), info.data]
    | none => .unmodeled s!"inst {i}" := rfl
  rw [this]
  cases ctx.insts[i]? <;> simp [eq_comm]

theorem ext_value_type_iff (v : Nat) (fs : List V) :
    externExtract ctx T.value_type (.value v) st = .ok fs ↔ ∃ t, ctx.valueType? v = some t ∧ fs = [.ty t] := by
  have : externExtract ctx T.value_type (.value v) st = match ctx.valueType? v with
    | some ty => .ok [.ty ty]
    | none => .unmodeled s!"value_type of unknown v{v}" := rfl
  rw [this]
  cases ctx.valueType? v <;> simp [eq_comm]

theorem ext_u64_from_imm64_iff (i : Int) (fs : List V) :
    externExtract ctx T.u64_from_imm64 (.int i) st = .ok fs ↔ fs = [.int (u64 i)] := by
  rw [ext_u64_from_imm64]; simp [eq_comm]

theorem ext_imm12_from_u64_iff (i : Int) (fs : List V) :
    externExtract ctx T.imm12_from_u64 (.int i) st = .ok fs ↔
      ∃ imm, Imm12.ofNat? (u64 i) = some imm ∧ fs = [.op (.imm12 imm)] := by
  rw [ext_imm12_from_u64]
  cases Imm12.ofNat? (u64 i) <;> simp [eq_comm]

theorem ext_value_array_2_iff (a b : Nat) (fs : List V) :
    externExtract ctx T.value_array_2 (.values [a, b]) st = .ok fs ↔ fs = [.value a, .value b] := by
  rw [ext_value_array_2]; simp [eq_comm]

theorem ext_is_second_result_iff (v : Nat) (fs : List V) :
    externExtract ctx T.is_second_result (.value v) st = .ok fs ↔
      ∃ i info, ctx.defInst? v = some i ∧ ctx.insts[i]? = some info ∧ info.results[1]? = some v ∧
        fs = [.value v] := by
  have : externExtract ctx T.is_second_result (.value v) st =
      match ctx.defInst? v >>= (ctx.insts[·]?) with
      | some info => if info.results[1]? == some v then .ok [.value v] else .fail
      | none => .fail := rfl
  rw [this]
  cases hd : ctx.defInst? v with
  | none => simp
  | some i =>
    cases hi : ctx.insts[i]? with
    | none => simp [hi]
    | some info =>
      simp only [Option.bind_eq_bind, Option.bind_some, hi]
      by_cases hr : info.results[1]? = some v
      · simp [hr, eq_comm, hd, hi]
      · simp [hr, hd, hi]

theorem ext_maybe_uextend_iff (v : Nat) (fs : List V) :
    externExtract ctx T.maybe_uextend (.value v) st = .ok fs ↔
      (∃ ty x, ctx.defClif? v = some (.extend .uextend ty x) ∧ fs = [.value x]) ∨
      ((∀ ty x, ctx.defClif? v ≠ some (.extend .uextend ty x)) ∧ fs = [.value v]) := by
  have : externExtract ctx T.maybe_uextend (.value v) st = match ctx.defClif? v with
    | some (.extend .uextend _ x) => .ok [.value x]
    | _ => .ok [.value v] := rfl
  rw [this]
  split
  · rename_i ty' x' hx
    simp only [ExtResult.ok.injEq, hx, Option.some.injEq, Clif.Inst.extend.injEq, true_and]
    constructor
    · intro h; exact .inl ⟨ty', x', ⟨rfl, rfl⟩, h.symm⟩
    · rintro (⟨ty, x, ⟨rfl, rfl⟩, h⟩ | ⟨h1, _⟩)
      · exact h.symm
      · exact absurd rfl (h1 ty' x')
  · rename_i hne
    simp only [ExtResult.ok.injEq]
    constructor
    · intro h; exact .inr ⟨fun ty x hx => hne ty x hx, h.symm⟩
    · rintro (⟨ty, x, hx, _⟩ | ⟨_, h⟩)
      · exact absurd hx (hne ty x)
      · exact h.symm

end Extract

/-! ## Extern constructors -/

section Ctor
variable (ctx : Ctx) (st : LState)

theorem ctor_put_in_reg_iff (x : Nat) (v : V) (st' : LState) :
    externCtor ctx T.put_in_reg [.value x] st = .ok (v, st') ↔
      ∃ r, ctx.valueReg? x = some r ∧ v = .reg r ∧ st' = st := by
  have : externCtor ctx T.put_in_reg [.value x] st = match ctx.valueReg? x with
      | some r => .ok (.reg r, st)
      | none => .unmodeled s!"put_in_reg v{x}" := rfl
  rw [this]
  cases ctx.valueReg? x <;> simp [eq_comm]

theorem ctor_ty_bits' (t : CTy) (v : V) (st' : LState) :
    externCtor ctx T.ty_bits [.ty t] st = .ok (v, st') ↔ v = .int t.bits ∧ st' = st := by
  have : externCtor ctx T.ty_bits [.ty t] st = .ok (.int t.bits, st) := rfl
  rw [this]; simp [eq_comm]

theorem ctor_emit_iff (i : V) (v : V) (st' : LState) :
    externCtor ctx T.emit [i] st = .ok (v, st') ↔
      ∃ m, MInst.ofV i = some m ∧ v = .op .unit ∧ st' = st.emit m := by
  have : externCtor ctx T.emit [i] st = match MInst.ofV i with
      | some m => .ok (.op .unit, st.emit m)
      | none => .unmodeled s!"emit of {((i.variant?).map (·.2.1)).getD "?"}" := rfl
  rw [this]
  cases MInst.ofV i <;> simp [eq_comm]

theorem ctor_temp_writable_reg_i64' (v : V) (st' : LState) :
    externCtor ctx T.temp_writable_reg [.ty (.int 64)] st = .ok (v, st') ↔
      v = .reg (st.fresh .int).1 ∧ st' = (st.fresh .int).2 := by
  rw [ctor_temp_writable_reg_i64]; simp [eq_comm]

theorem ctor_writable_reg_to_reg' (r v : V) (st' : LState) :
    externCtor ctx T.writable_reg_to_reg [r] st = .ok (v, st') ↔ v = r ∧ st' = st := by
  rw [ctor_writable_reg_to_reg]; simp [eq_comm]

theorem ctor_value_reg' (r : Reg) (v : V) (st' : LState) :
    externCtor ctx T.value_reg [.reg r] st = .ok (v, st') ↔ v = .regs [r] ∧ st' = st := by
  rw [ctor_value_reg]; simp [eq_comm]

theorem ctor_output' (rs : List Reg) (v : V) (st' : LState) :
    externCtor ctx T.output [.regs rs] st = .ok (v, st') ↔ v = .regsVec [rs] ∧ st' = st := by
  rw [ctor_output]; simp [eq_comm]

theorem ctor_value_regs_get_iff (rs : List Reg) (i : Int) (v : V) (st' : LState) :
    externCtor ctx T.value_regs_get [.regs rs, .int i] st = .ok (v, st') ↔
      ∃ r, rs[i.toNat]? = some r ∧ v = .reg r ∧ st' = st := by
  have : externCtor ctx T.value_regs_get [.regs rs, .int i] st = match rs[i.toNat]? with
    | some r => .ok (.reg r, st)
    | none => .unmodeled "value_regs_get index" := rfl
  rw [this]
  cases rs[i.toNat]? <;> simp [eq_comm]

theorem ctor_zero_reg' (v : V) (st' : LState) :
    externCtor ctx T.zero_reg [] st = .ok (v, st') ↔ v = .reg .xzr ∧ st' = st := by
  have : externCtor ctx T.zero_reg [] st = .ok (.reg .xzr, st) := rfl
  rw [this]; simp [eq_comm]

theorem ctor_writable_zero_reg' (v : V) (st' : LState) :
    externCtor ctx T.writable_zero_reg [] st = .ok (v, st') ↔ v = .reg .xzr ∧ st' = st := by
  rw [ctor_writable_zero_reg]; simp [eq_comm]

theorem ctor_invert_cond_iff (c : V) (v : V) (st' : LState) :
    externCtor ctx T.invert_cond [c] st = .ok (v, st') ↔
      ∃ cd, c.cond? = some cd ∧ v = .data tyCond cd.invert.idx [] ∧ st' = st := by
  have : externCtor ctx T.invert_cond [c] st = match c.cond? with
    | some c => .ok (.data tyCond c.invert.idx [], st)
    | none => .unmodeled "invert_cond" := rfl
  rw [this]
  cases c.cond? <;> simp [eq_comm]

theorem ctor_cond_code_iff (c : V) (v : V) (st' : LState) :
    externCtor ctx T.cond_code [c] st = .ok (v, st') ↔
      ∃ cd, (c.intcc? >>= condOfIntCC) = some cd ∧ v = .data tyCond cd.idx [] ∧ st' = st := by
  have : externCtor ctx T.cond_code [c] st = match c.intcc? >>= condOfIntCC with
    | some c => .ok (.data tyCond c.idx [], st)
    | none => .unmodeled "cond_code" := rfl
  rw [this]
  cases c.intcc? >>= condOfIntCC <;> simp [eq_comm]

end Ctor

/-! ## Decoding enum values -/

theorem cond_ofIdx_idx (c : Cond) : Cond.ofIdx? c.idx = some c := by cases c <;> rfl

theorem V.cond?_data (k : Nat) : (V.data tyCond k []).cond? = Cond.ofIdx? k := rfl

end Backend.Proof

open Lean Elab Tactic Meta in
/-- Split every hypothesis that is a conjunction or an existential (and, with `ors`, a
disjunction, into one goal per case), repeatedly. -/
partial def iselDestructGoal (ors : Bool) (goal : MVarId) : MetaM (List MVarId) := goal.withContext do
  for ldecl in (← getLCtx) do
    if ldecl.isImplementationDetail then continue
    let ty ← whnfR (← instantiateMVars ldecl.type)
    if ty.isAppOfArity ``And 2 || ty.isAppOfArity ``Exists 2 || (ors && ty.isAppOfArity ``Or 2) then
      let subgoals ← goal.cases ldecl.fvarId
      let mut out := []
      for sg in subgoals do
        out := out ++ (← iselDestructGoal ors sg.mvarId)
      return out
  return [goal]

open Lean Elab Tactic Meta in
/-- Split every conjunction/existential hypothesis. -/
elab "isel_destruct" : tactic => do
  replaceMainGoal (← iselDestructGoal false (← getMainGoal))

open Lean Elab Tactic Meta in
/-- Split every conjunction/existential/disjunction hypothesis (one goal per case). -/
elab "isel_cases" : tactic => do
  replaceMainGoal (← iselDestructGoal true (← getMainGoal))

/-- Case split on the committed rule of `rulesOf t = pre ++ r :: post` (a concrete list),
substituting `pre` and `r`. -/
macro "isel_rule_cases " h:ident : tactic => `(tactic| (
  simp only [List.append_eq_cons_iff, List.cons_eq_append_iff, List.nil_eq_append_iff,
    List.cons.injEq, exists_eq_left, exists_and_left, reduceCtorEq, false_and, and_false, or_false,
    exists_false, List.nil_append, and_true] at $h:ident
  isel_cases <;> subst_vars))

/-- `isel_inv [lemmas] at h₁ … hₙ`: rewrite hypotheses "this match/evaluation returned `some`"
into the facts they imply (inverse evaluation), split them and substitute, to a fixpoint.
Pass the data facts (`*` after `cases hp`) and the rules' definitions as `lemmas`. -/
syntax "isel_inv" ("[" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|> Lean.Parser.Tactic.simpLemma),* "]")? " at " (ppSpace colGt ident)+ : tactic

/-- The inverse-evaluation simp set (without the caller's data facts). -/
syntax "isel_inv_simp" ("[" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|> Lean.Parser.Tactic.simpLemma),* "]")? (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| isel_inv_simp [$ts,*] $[$loc]?) => `(tactic| simp only [Isle.Interp.matchRule_iff, Isle.Interp.matchArgs_nil_iff,
        Isle.Interp.matchArgs_cons_iff, Isle.Interp.matchPat_bind_iff,
        Isle.Interp.matchPat_wildcard_iff, Isle.Interp.matchPat_var_iff,
        Isle.Interp.matchPat_constBool_iff, Isle.Interp.matchPat_constInt_iff,
        Isle.Interp.matchPat_constPrim_iff, Isle.Interp.matchPat_term_iff, Isle.Interp.MatchTerm,
        Isle.Interp.matchIfLets_nil_iff, Isle.Interp.matchIfLets_cons_iff,
        Isle.Interp.evalExpr_var_iff, Isle.Interp.evalExpr_constBool_iff,
        Isle.Interp.evalExpr_constInt_iff, Isle.Interp.evalExpr_constPrim_iff,
        Isle.Interp.evalExpr_let_iff, Isle.Interp.evalExpr_term_iff, Isle.Interp.evalArgs_nil_iff,
        Isle.Interp.evalArgs_cons_iff, Isle.Interp.evalBinds_nil_iff,
        Isle.Interp.evalBinds_cons_iff, Isle.Interp.applyTerm_iff, Isle.Interp.ApplySpec,
        isel_data, isel_monad, Backend.Proof.sem_eq, Backend.Proof.sem_unData_iff, beq_iff_eq,
        Backend.Proof.ext_fits_in_16_iff, Backend.Proof.ext_fits_in_32_iff,
        Backend.Proof.ext_fits_in_64_iff, Backend.Proof.ext_ty_32_or_64_iff,
        Backend.Proof.ext_ty_int_iff, Backend.Proof.ext_ty_scalar_float_iff,
        Backend.Proof.ext_ty_vec128_iff, Backend.Proof.ext_def_inst_iff,
        Backend.Proof.ext_inst_data_value_iff, Backend.Proof.ext_value_type_iff,
        Backend.Proof.ext_u64_from_imm64_iff, Backend.Proof.ext_imm12_from_u64_iff,
        Backend.Proof.ext_value_array_2_iff, Backend.Proof.ext_is_second_result_iff,
        Backend.Proof.ext_maybe_uextend_iff, Backend.Proof.ctor_put_in_reg_iff,
        Backend.Proof.ctor_emit_iff, Backend.Proof.ctor_ty_bits', Backend.Proof.ctor_temp_writable_reg_i64',
        Backend.Proof.ctor_writable_reg_to_reg', Backend.Proof.ctor_value_reg',
        Backend.Proof.ctor_output', Backend.Proof.ctor_value_regs_get_iff,
        Backend.Proof.ctor_zero_reg', Backend.Proof.ctor_writable_zero_reg',
        Backend.Proof.ctor_invert_cond_iff, Backend.Proof.ctor_cond_code_iff,
        exists_and_left, exists_and_right, exists_eq_left, exists_eq_right, exists_eq_left',
        exists_eq_right', exists_const, and_true, true_and, and_self, Prod.mk.injEq,
        Option.some.injEq, Backend.V.data.injEq, Backend.V.reg.injEq, Backend.V.value.injEq,
        Backend.V.int.injEq, Backend.V.ty.injEq, Backend.V.inst.injEq, List.cons.injEq,
        Except.ok.injEq, Isle.ExtResult.ok.injEq, reduceCtorEq, false_and, and_false, exists_false,
        List.getElem?_cons_zero, List.getElem?_cons_succ, $ts,*] $[$loc]?)
macro_rules
  | `(tactic| isel_inv at $hs*) => `(tactic| isel_inv [] at $hs*)
  | `(tactic| isel_inv [$ts,*] at $hs*) => `(tactic| (isel_inv_simp [$ts,*] at $hs* <;> isel_destruct <;> subst_vars <;>
      repeat (isel_inv_simp [] at * <;> isel_destruct <;> subst_vars)))
