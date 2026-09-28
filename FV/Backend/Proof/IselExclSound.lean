import FV.Backend.Proof.IselExclData

/-!
# Excluded root rules: soundness of the abstract pattern checker

`fails_sound`: if `fails p a q`, then `q` matches no value that `a` describes (`AV.Holds`) in
any context with `CtxInv`.
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

theorem holdsAll_exact (fs : List V) {f : Clif.Function} {ctx : Ctx} :
    AV.HoldsAll f ctx (fs.map .exact) fs := by
  induction fs with
  | nil => trivial
  | cons v fs ih => exact ⟨rfl, ih⟩

section
variable {p : Program} {f : Clif.Function} {ctx : Ctx}

theorem matchPat_termOf_error {st : LState} {ty : TypeId} {t : TermId} {args : List Pattern}
    {v : V} {env env' : Interp.Env V} {e : Err} (ht : termOf p t = .error e)
    (h : matchPat p (sem ctx) st (.term ty t args) v env = .ok (some env')) : False := by
  rw [matchPat.eq_8, ht] at h; cases h

theorem matchPat_multi {st : LState} {ty : TypeId} {t : TermId} {args : List Pattern}
    {v : V} {env env' : Interp.Env V} {term : Term} {flags : TermFlags} {c : Option Ctor}
    {fn : String} {inf : Bool} (ht : termOf p t = .ok term)
    (hk : term.kind = .decl flags c (some (.external fn inf))) (hm : flags.isMulti = true)
    (h : matchPat p (sem ctx) st (.term ty t args) v env = .ok (some env')) : False := by
  rw [matchPat.eq_8, ht] at h
  simp only [M.except_ok_bind, hk, hm, ↓reduceIte] at h
  cases h

theorem matchAll_cons_inv_ex {st : LState} {q : Pattern} {qs : List Pattern} {v : V}
    {env env' : Interp.Env V}
    (h : matchAll p (sem ctx) st (q :: qs) v env = .ok (some env')) :
    ∃ e1, matchPat p (sem ctx) st q v env = .ok (some e1) ∧
      matchAll p (sem ctx) st qs v e1 = .ok (some env') := by
  rw [matchAll.eq_2] at h
  cases hq : matchPat p (sem ctx) st q v env with
  | error e => rw [hq] at h; cases h
  | ok o =>
    rw [hq] at h
    cases o with
    | none => cases h
    | some e1 => exact ⟨e1, rfl, h⟩

theorem prim_sem_ex (ty : TypeId) (n : String) : (sem ctx).prim ty n = primTy ty n := rfl

theorem eq_sem_ex (a b : V) : (sem ctx).eq a b = (a == b) := rfl

variable (hctx : CtxInv f ctx)
include hctx

/-- The result types of a context instruction are `invalid` or `i8..i64`. -/
theorem head_resTy_ex {j : Nat} {info : IInfo} (hi : ctx.insts[j]? = some info) :
    info.resTys.head?.getD .invalid ∈ (.invalid :: eCTys) := by
  cases h : info.resTys with
  | nil => exact List.mem_cons_self
  | cons t ts =>
    exact List.mem_cons_of_mem _ (hctx.resTysE j info hi t (by rw [h]; exact List.mem_cons_self))

-- `failsAny_sound`/`failsArgs_sound` use `hctx` only through `fails_sound`
set_option linter.unusedSectionVars false

mutual
/-- **Soundness of the checker**: `fails p a q` means `q` matches no value `a` describes. -/
theorem fails_sound : ∀ (q : Pattern) (a : AV) (v : V) (st : LState) (env env' : Interp.Env V),
    fails p a q = true → a.Holds f ctx v →
    matchPat p (sem ctx) st q v env = .ok (some env') → False
  | .bind ty x q, a, v, st, env, env', hf, ha, hm => by
    rw [fails.eq_1] at hf
    exact fails_sound q a v st _ env' hf ha (matchPat_bind_inv hm).2
  | .and ty qs, a, v, st, env, env', hf, ha, hm => by
    rw [fails.eq_2] at hf
    rw [matchPat.eq_7] at hm
    exact failsAny_sound qs a v st env env' hf ha hm
  | .constPrim ty n, a, v, st, env, env', hf, ha, hm => by
    rw [matchPat.eq_5, prim_sem_ex] at hm
    rw [fails.eq_3] at hf
    cases hp : primTy ty n with
    | none => rw [hp] at hm; cases hm
    | some c =>
      rw [hp] at hm hf
      simp only [pure, Except.pure, eq_sem_ex] at hm
      have hne : (v == c) = false := by
        cases a with
        | tys ts =>
          obtain ⟨t, ht, rfl⟩ := ha
          simpa using List.all_eq_true.mp hf t ht
        | exact w => cases ha; simpa using hf
        | _ => simp at hf
      simp [hne] at hm
  | .term ty t args, a, v, st, env, env', hf, ha, hm => by
    rw [fails.eq_def] at hf
    try dsimp only at hf
    cases ht : termOf p t with
    | error e => exact matchPat_termOf_error ht hm
    | ok term =>
      rw [ht] at hf
      simp only at hf
      cases hk : term.kind with
      | struct => rw [hk] at hf; simp at hf
      | enumVariant k =>
        rw [hk] at hf
        obtain ⟨fs, hu, hma⟩ := matchPat_enum_inv ht hk hm
        cases a with
        | data =>
          obtain ⟨c, hEc, hc⟩ := ha
          obtain ⟨kf, ko, fs0, rfl, hko⟩ := instData_shape hEc hc
          simp only [sem, beq_iff_eq] at hu
          split at hu
          · rename_i hty
            subst hty
            obtain ⟨rfl, rfl⟩ := Option.some.inj hu
            simp only at hf
            split at hf
            · rename_i ty2 oT rest
              obtain ⟨e1, hm1, hm2⟩ := matchArgs_cons_inv hma
              cases hot : termOf p oT with
              | error e => exact matchPat_termOf_error hot hm1
              | ok oterm =>
                rw [hot] at hf
                simp only at hf
                cases hok : oterm.kind with
                | enumVariant ko' =>
                  rw [hok] at hf
                  obtain ⟨fs1, hu1, -⟩ := matchPat_enum_inv hot hok hm1
                  simp only [sem, beq_iff_eq] at hu1
                  split at hu1
                  · obtain ⟨rfl, -⟩ := Option.some.inj hu1
                    try dsimp only at hf
                    rw [List.contains_iff_mem.mpr hko, Bool.not_true, Bool.false_or] at hf
                    cases hsh : opShape ko with
                    | none => rw [hsh] at hf; cases hf
                    | some sh =>
                      rw [hsh] at hf
                      exact failsArgs_sound rest sh fs0 st e1 env' hf (instData_fields hc hsh) hm2
                  · cases hu1
                | _ => rw [hok] at hf; simp at hf
            · cases hf
          · cases hu
        | exact w =>
          cases ha
          try dsimp only at hf
          cases v with
          | data ty' k' fs' =>
            simp only [sem, beq_iff_eq] at hu
            split at hu
            · rename_i hty
              obtain ⟨rfl, rfl⟩ := Option.some.inj hu
              simp only [hty, beq_self_eq_true, Bool.not_true, Bool.false_or] at hf
              exact failsArgs_sound args _ _ st env env' hf (holdsAll_exact _) hma
            · cases hu
          | _ => simp at hf
        | _ => simp at hf
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
              simp only [Bool.false_eq_true, ↓reduceIte] at hf
              obtain ⟨fs, hx, hma⟩ := matchPat_extract_inv ht hk hmu hm
              rw [sem_extract] at hx
              cases a with
              | inst =>
                obtain ⟨j, info, c, rfl, hi, hc, hd⟩ := ha
                try dsimp only at hf
                split at hf
                · rename_i hid
                  obtain ⟨info', hi', rfl⟩ := ext_idv_inv (beq_iff_eq.mp hid) hx
                  rw [hi] at hi'
                  cases hi'
                  exact failsArgs_sound args _ [.ty (info.resTys.head?.getD .invalid), info.data] st env env' hf
                    ⟨⟨_, head_resTy_ex hctx hi, rfl⟩, ⟨c, hctx.instE j info c hi hc, hd⟩, trivial⟩ hma
                · rw [ext_flagOff hf] at hx; cases hx
              | value =>
                obtain ⟨x, rfl⟩ := ha
                try dsimp only at hf
                split at hf
                · rename_i hid
                  obtain ⟨i, hdi, rfl⟩ := ext_def_inst_inv (beq_iff_eq.mp hid) hx
                  obtain ⟨info, hi, -⟩ := hctx.defInst x i hdi
                  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp (hctx.defClif x i info hdi hi)
                  exact failsArgs_sound args _ [.inst i] st env env' hf
                    ⟨⟨i, info, c, rfl, hi, hc, hctx.data i info c hi hc⟩, trivial⟩ hma
                · split at hf
                  · rename_i _ hid
                    obtain ⟨t, hvt, rfl⟩ := ext_value_type_inv (beq_iff_eq.mp hid) hx
                    exact failsArgs_sound args _ [.ty t] st env env' hf
                      ⟨⟨t, hctx.valTyE x t hvt, rfl⟩, trivial⟩ hma
                  · cases hf
              | values n =>
                obtain ⟨xs, rfl, hn⟩ := ha
                try dsimp only at hf
                split at hf
                · rename_i hid
                  simp only [Bool.and_eq_true, beq_iff_eq] at hid
                  obtain ⟨hid, rfl⟩ := hid
                  match xs, hn with
                  | [x, y], _ =>
                    rw [ext_value_array_2_ex hid] at hx
                    cases hx
                    exact failsArgs_sound args _ [.value x, .value y] st env env' hf
                      ⟨⟨x, rfl⟩, ⟨y, rfl⟩, trivial⟩ hma
                · cases hf
              | tys ts =>
                obtain ⟨t0, ht0, rfl⟩ := ha
                try dsimp only at hf
                have h0 := List.all_eq_true.mp hf t0 ht0
                cases hte : tyExtract term.id t0 with
                | none => rw [hte] at h0; cases h0
                | some r =>
                  rw [tyExtract_sound hte] at hx
                  subst hx
                  rw [hte] at h0
                  exact failsArgs_sound args _ _ st env env' h0 (holdsAll_exact _) hma
              | exact w =>
                cases ha
                try dsimp only at hf
                cases v with
                | ty t0 =>
                  try dsimp only at hf
                  cases hte : tyExtract term.id t0 with
                  | none => rw [hte] at hf; cases hf
                  | some r =>
                    rw [tyExtract_sound hte] at hx
                    subst hx
                    rw [hte] at hf
                    exact failsArgs_sound args _ _ st env env' hf (holdsAll_exact _) hma
                | _ => simp at hf
              | _ => simp at hf
            · exact matchPat_multi ht hk hmu hm
  | .var .., _, _, _, _, _, hf, _, _ => by simp [fails] at hf
  | .constBool .., _, _, _, _, _, hf, _, _ => by simp [fails] at hf
  | .constInt .., _, _, _, _, _, hf, _, _ => by simp [fails] at hf
  | .wildcard .., _, _, _, _, _, hf, _, _ => by simp [fails] at hf

theorem failsAny_sound : ∀ (qs : List Pattern) (a : AV) (v : V) (st : LState)
    (env env' : Interp.Env V), failsAny p a qs = true → a.Holds f ctx v →
    matchAll p (sem ctx) st qs v env = .ok (some env') → False
  | [], _, _, _, _, _, hf, _, _ => by simp [failsAny] at hf
  | q :: qs, a, v, st, env, env', hf, ha, hm => by
    rw [failsAny.eq_2, Bool.or_eq_true] at hf
    obtain ⟨e1, h1, h2⟩ := matchAll_cons_inv_ex hm
    rcases hf with hf | hf
    · exact fails_sound q a v st env e1 hf ha h1
    · exact failsAny_sound qs a v st e1 env' hf ha h2

theorem failsArgs_sound : ∀ (qs : List Pattern) (as : List AV) (vs : List V) (st : LState)
    (env env' : Interp.Env V), failsArgs p as qs = true → AV.HoldsAll f ctx as vs →
    matchArgs p (sem ctx) st qs vs env = .ok (some env') → False
  | [], _, _, _, _, _, hf, _, _ => by cases ‹List AV› <;> simp [failsArgs] at hf
  | q :: qs, [], _, _, _, _, hf, _, _ => by simp [failsArgs] at hf
  | q :: qs, a :: as, vs, st, env, env', hf, hav, hm => by
    rw [failsArgs.eq_1, Bool.or_eq_true] at hf
    match vs, hav with
    | v :: vs, ⟨ha, hrest⟩ =>
      obtain ⟨e1, h1, h2⟩ := matchArgs_cons_inv hm
      rcases hf with hf | hf
      · exact fails_sound q a _ st env e1 hf ha h1
      · exact failsArgs_sound qs as _ st e1 env' hf hrest h2
end

end

end Backend.Proof
